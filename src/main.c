#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/constants.h"
#include "../include/types.h"
#include "../include/getters.h"
#include "../include/printers.h"
#include "../include/setters.h"
#include "../include/payment.h"
#include "../include/deposit.h"
#include "../include/close.h"

#include "../include/cbmc_helper.h"
// #include "../include/mock_cbmc_helper.h"

// Type for the contract template
typedef struct {
    int amountAda;
    int amountDollar;
    int adaTimeout;
    int dollarTimeout;
} ContractTemplate;

int main() {
    // Define the tokens for internal accounts
    // int initialAda_AdaHolder_Internal = constr_non_det_int(0,0);
    // int initialDollar_AdaHolder_Internal = constr_non_det_int(0,0);
    // int initialAda_DollarHolder_Internal = constr_non_det_int(0,0);
    // int initialDollar_DollarHolder_Internal = constr_non_det_int(0,0);
    
    int initialAda_AdaHolder_Internal = 0;
    int initialDollar_AdaHolder_Internal = 0;
    int initialAda_DollarHolder_Internal = 0;
    int initialDollar_DollarHolder_Internal = 0;
    
    Token adaAdaProviderInternal = {.currency = ADA, .amount = initialAda_AdaHolder_Internal};
    Token dollarAdaProviderInternal = {.currency = DOLLAR, .amount = initialDollar_AdaHolder_Internal};
    Token adaDollarProviderInternal = {.currency = ADA, .amount = initialAda_DollarHolder_Internal};
    Token dollarDollarProviderInternal = {.currency = DOLLAR, .amount = initialDollar_DollarHolder_Internal};

    // Define the wallets for internal accounts
    Token tokensAdaProviderInternal[] = {adaAdaProviderInternal, dollarAdaProviderInternal};
    Wallet* walletAdaProviderInternal = newWallet(tokensAdaProviderInternal, 2);
    Token tokensDollarProviderInternal[] = {adaDollarProviderInternal, dollarDollarProviderInternal};
    Wallet* walletDollarProviderInternal = newWallet(tokensDollarProviderInternal, 2);

    // Define the internal accounts
    InternalAccount accounts[] = {
        {1, *walletAdaProviderInternal},
        {2, *walletDollarProviderInternal}
    };

    // Define the internal wallet
    InternalWallet* internalWallet = newInternalWallet(accounts, 2);

    // Define the tokens for external wallets
    int initialAda_AdaHolder = constr_non_det_int(0,100);
    int initialDollar_AdaHolder = constr_non_det_int(0,100);
    int initialAda_DollarHolder = constr_non_det_int(0,100);
    int initialDollar_DollarHolder = constr_non_det_int(0,100);

    Token adaAdaProviderExternal = {.currency = ADA, .amount = initialAda_AdaHolder };
    Token dollarAdaProviderExternal = {.currency = DOLLAR, .amount = initialDollar_AdaHolder};
    Token adaDollarProviderExternal = {.currency = ADA, .amount = initialAda_DollarHolder};
    Token dollarDollarProviderExternal = {.currency = DOLLAR, .amount = initialDollar_DollarHolder};
    
    // Define the wallets for external wallets
    Token tokensAdaProviderExternal[] = {adaAdaProviderExternal, dollarAdaProviderExternal};
    Wallet* walletAdaProviderExternal = newWallet(tokensAdaProviderExternal, 2);
    Token tokensDollarProviderExternal[] = {adaDollarProviderExternal, dollarDollarProviderExternal};
    Wallet* walletDollarProviderExternal = newWallet(tokensDollarProviderExternal, 2);

    Party* dollarProvider = newParty(DOLLARPROVIDER, 1, walletDollarProviderExternal);
    Party* adaProvider = newParty(ADAPROVIDER, 2, walletAdaProviderExternal);


    // Define the contract

    // Define the contract template
    ContractTemplate template = {
        .amountAda = constr_non_det_int(0,100),
        .amountDollar = constr_non_det_int(0,100),
        .adaTimeout = constr_non_det_int(0,10),
        .dollarTimeout = constr_non_det_int(0,10)
    };

    // Define successContract as the close contract when the swap is successful
    Contract* successContract = newContract(CLOSE, (ContractParameters){
    .closeParams = {
        .id = 0
        }
    }, NULL, NULL);

    // Define failedContract as the close contract when the swap is not successful
    Contract* failedContract = newContract(CLOSE, (ContractParameters){
        .closeParams = {
            .id = 1
            }
        }, NULL, NULL);

    // Define payAdaProvider as the part of the contract that pays the adaProvider when the swap is successful
    Contract* payAdaProvider = newContract(PAY, (ContractParameters){
        .payParams = {
            .payer = dollarProvider,
            .receiver = adaProvider,
            .amount = template.amountDollar,
            .currency = DOLLAR
            }
        }, NULL, successContract);

    // Define payDollarProvider as the part of the contract that pays the dollarProvider when the swap is successful
    Contract* payDollarProvider = newContract(PAY, (ContractParameters){
        .payParams = {
            .payer = adaProvider,
            .receiver = dollarProvider,
            .amount = template.amountAda,
            .currency = ADA
            }
        }, NULL, payAdaProvider);

    // Define whenDepositDollarProvider as the part of the contract that awaits a deposit by the dollarProvider
    Contract* whenDepositDollarProvider = newContract(DEPOSIT, (ContractParameters){
        .depositParams = {
            .depositor = dollarProvider,
            .receiver = dollarProvider,
            .amount = template.amountDollar,
            .currency = DOLLAR,
            .timeout = template.dollarTimeout
            }
        }, payDollarProvider, failedContract);

    // Define whenDepositAdaProvider as the part of the contract that awaits a deposit by the adaProvider
    Contract* whenDepositAdaProvider = newContract(DEPOSIT, (ContractParameters){
        .depositParams = {
            .depositor = adaProvider,
            .receiver = adaProvider,
            .amount = template.amountAda,
            .currency = ADA,
            .timeout = template.adaTimeout
            }
        }, whenDepositDollarProvider, failedContract);

    // Define the contract state
    Party* parties[] = {adaProvider, dollarProvider};
    ContractState* state = newContractState(whenDepositAdaProvider, internalWallet, parties, 2);

    // Simulation time
    int currentTime = 0;
    int contractTimeout = 20;

    int success = -1;

    // THIS IS THE MAIN LOOP OF THE EXECUTION
    // PROBABLY NEED TO BE FACTORED OUT
    
    // Return value of the simulation
    // 0 means unfinished
    // 1 means finished with or without success
    int res_ret = 0;

    // Get the initial ammounts of ada and dollars
    int initialTotalAda = getTotalAda(state);
    int initialTotalDollar = getTotalDollars(state);

    while (currentTime < contractTimeout && res_ret == 0) {
        // prettyPrintWholeContractState(state, currentTime);
        currentTime++;

        if (state->currentContract == NULL) {
            printf("End of simulation because the contract is now NULL\n");
            break;
        }
        // TODO: Don't force an action 
        // if (constr_non_det_int(0,1) == 0){
        //     continue;
        // }
        switch (state->currentContract->type) {
            case PAY: {
                Transaction transaction = convertToTransaction(&(state->currentContract->params.payParams));
                int res = makePayment(state, &transaction);
                if (res == 0) {
                } else {
                    fprintf(stderr, "PAY action was not successful\n");
                    res_ret = 1;
                }
                break;
            }
            case CLOSE:
                processClose(state);
                if (state->currentContract->params.closeParams.id == 0) {
                    success = 1;
                } else {
                    success = 0;
                }
                state->currentContract = state->currentContract->continueAs;
                break;
            case DEPOSIT: {
                if (currentTime > state->currentContract->params.depositParams.timeout){
                    state->currentContract = state->currentContract->continueAs;
                }
                else {
                    // For the moment, we force the party to try to deposit whatever is asked
                    // TODO: Leave the choice to the simulation to do it or not
                    Transaction depositTransaction = {
                        .source = state->currentContract->params.depositParams.depositor,
                        .destination = state->currentContract->params.depositParams.receiver,
                        .amount = state->currentContract->params.depositParams.amount,
                        .currency = state->currentContract->params.depositParams.currency
                    };
                    int res = makeDeposit(state, &depositTransaction, &(state->currentContract->params.depositParams));
                    // Handle errors
                    if (res == 1){
                        state->currentContract = state->currentContract->continueAs;
                        }
                    else{
                        state->currentContract = state->currentContract->subContractOK;
                        }
                }
                break;
            }
            default:
                fprintf(stderr, "Error: Unsupported contract type\n");
                res_ret = 1;
        }
    }

    int finalTotalAda = getTotalAda(state);
    int finalTotalDollar = getTotalDollars(state);

    // Dead code check
    // Is expected to fail
    // If not, the properties are dead code and will evaluate true no matter what
    // int reach = 1;
    // __CPROVER_assert(reach == 0, "Are the properties dead-code -- needs to fail");
    
    // // Test case generation examples
    // // Can be made more complex by having more coverage criteria added in the model
    // __CPROVER_assert(success == 0, "Impossible to get a successful contract");
    // __CPROVER_assert(success == 1, "Impossible to get a failing contract");

    // General properties
    // Mainly used to show that I didn't mess up (too much) the modeling
    __CPROVER_assert(initialTotalAda == finalTotalAda, "Ada are preserved!");
    __CPROVER_assert(initialTotalDollar == finalTotalDollar, "Dollar are preserved!");

    // Marlowe assertions
    
    // Marlowe is expecte to always end on a close contract
    // All close contracts are expected to change success to something other than -1
    __CPROVER_assert(success != -1, "Always finish on a Close contract");

    // Check that the internal accounts are all empty
    __CPROVER_assert(adaAdaProviderInternal.amount == 0 && adaDollarProviderInternal.amount == 0, "No ada left in the contract");
    __CPROVER_assert(dollarAdaProviderInternal.amount == 0 && dollarDollarProviderInternal.amount == 0, "No dollar left in the contract");
    

    // Functional correctness of the SWAP contract

    // If the contract is succesful, funds were transfered properly
    // If not, the funds have not been transfered but whatever was inside the contract
    // for some unknown reasons at the beginning, have been correctly returned
    // __CPROVER_assert((success != 1) || (walletAdaProviderExternal->tokens[0].amount == initialAda_AdaHolder + initialAda_AdaHolder_Internal - template.amountAda), "On succesful contract: Ada Provider has always sent the correct amount of ada");
    // __CPROVER_assert((success != 1) || (walletDollarProviderExternal->tokens[0].amount == initialAda_DollarHolder + initialAda_DollarHolder_Internal + template.amountAda), "On succesful contract: Dollar Provider always receives the correct amount of ada");
    // __CPROVER_assert((success != 1) || (walletAdaProviderExternal->tokens[1].amount == initialDollar_AdaHolder + initialDollar_AdaHolder_Internal + template.amountDollar), "On succesful contract: Ada Provider always receives the correct amount of dollars");
    // __CPROVER_assert((success != 1) || (walletDollarProviderExternal->tokens[1].amount == initialDollar_DollarHolder + initialDollar_DollarHolder_Internal - template.amountDollar), "On succesful contract: Dollar Provider has always sent the correct amount of dollars");

    // __CPROVER_assert((success != 0) || (walletAdaProviderExternal->tokens[0].amount == initialAda_AdaHolder + initialAda_AdaHolder_Internal), "On failed contract: Ada Provider always receives back their ada");
    // __CPROVER_assert((success != 0) || (walletDollarProviderExternal->tokens[0].amount == initialAda_DollarHolder + initialAda_DollarHolder_Internal), "On failed contract: Dollar Provider always receives back their ada");
    // __CPROVER_assert((success != 0) || (walletAdaProviderExternal->tokens[1].amount == initialDollar_AdaHolder + initialDollar_AdaHolder_Internal), "On failed contract: Ada Provider always receives back their dollars");
    // __CPROVER_assert((success != 0) || (walletDollarProviderExternal->tokens[1].amount == initialDollar_DollarHolder + initialDollar_DollarHolder_Internal), "On failed contract: Dollar Provider always receives back their dollars");
    switch (success){
        case 0:
            __CPROVER_assert((walletAdaProviderExternal->tokens[0].amount == initialAda_AdaHolder + initialAda_AdaHolder_Internal), "On failed contract: Ada Provider always receives back their ada");
            __CPROVER_assert((walletDollarProviderExternal->tokens[0].amount == initialAda_DollarHolder + initialAda_DollarHolder_Internal), "On failed contract: Dollar Provider always receives back their ada");
            __CPROVER_assert((walletAdaProviderExternal->tokens[1].amount == initialDollar_AdaHolder + initialDollar_AdaHolder_Internal), "On failed contract: Ada Provider always receives back their dollars");
            __CPROVER_assert((walletDollarProviderExternal->tokens[1].amount == initialDollar_DollarHolder + initialDollar_DollarHolder_Internal), "On failed contract: Dollar Provider always receives back their dollars");
            break;
        case 1:
            __CPROVER_assert((walletAdaProviderExternal->tokens[0].amount == initialAda_AdaHolder + initialAda_AdaHolder_Internal - template.amountAda), "On succesful contract: Ada Provider has always sent the correct amount of ada");
            __CPROVER_assert((walletDollarProviderExternal->tokens[0].amount == initialAda_DollarHolder + initialAda_DollarHolder_Internal + template.amountAda), "On succesful contract: Dollar Provider always receives the correct amount of ada");
            __CPROVER_assert((walletAdaProviderExternal->tokens[1].amount == initialDollar_AdaHolder + initialDollar_AdaHolder_Internal + template.amountDollar), "On succesful contract: Ada Provider always receives the correct amount of dollars");
            __CPROVER_assert((walletDollarProviderExternal->tokens[1].amount == initialDollar_DollarHolder + initialDollar_DollarHolder_Internal - template.amountDollar), "On succesful contract: Dollar Provider has always sent the correct amount of dollars");
            break;
        default:
            break;
    }
    // Free allocated memory
    // TODO: Factor out the free functions

    // free(failedContract);
    // free(successContract);
    // free(payAdaProvider);
    // free(payDollarProvider);
    // free(whenDepositDollarProvider);
    // free(whenDepositAdaProvider);
    // free(walletAdaProviderExternal->tokens);
    // free(walletAdaProviderExternal);
    // free(walletDollarProviderExternal->tokens);
    // free(walletDollarProviderExternal);
    // free(internalWallet->accounts);
    // free(internalWallet);
    // free(walletAdaProviderInternal->tokens);
    // free(walletAdaProviderInternal);
    // free(walletDollarProviderInternal->tokens);
    // free(walletDollarProviderInternal);
    // free(adaProvider);
    // free(dollarProvider);
    // free(state->parties);
    // free(state);

    return res_ret;
}