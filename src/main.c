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
    Token adaAdaProviderInternal = {.currency = ADA, .amount = constr_non_det_int(0,0)};
    Token dollarAdaProviderInternal = {.currency = DOLLAR, .amount = constr_non_det_int(0,0)};
    Token adaDollarProviderInternal = {.currency = ADA, .amount = constr_non_det_int(0,0)};
    Token dollarDollarProviderInternal = {.currency = DOLLAR, .amount = constr_non_det_int(0,0)};

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
    Token adaAdaProviderExternal = {.currency = ADA, .amount = constr_non_det_int(0,100)};
    Token dollarAdaProviderExternal = {.currency = DOLLAR, .amount = constr_non_det_int(0,100)};
    Token adaDollarProviderExternal = {.currency = ADA, .amount = constr_non_det_int(0,100)};
    Token dollarDollarProviderExternal = {.currency = DOLLAR, .amount = constr_non_det_int(0,100)};
    
    // Define the wallets for external wallets
    Token tokensAdaProviderExternal[] = {adaDollarProviderExternal, dollarAdaProviderExternal};
    Wallet* walletAdaProviderExternal = newWallet(tokensAdaProviderExternal, 2);
    Token tokensDollarProviderExternal[] = {adaDollarProviderExternal, dollarDollarProviderExternal};
    Wallet* walletDollarProviderExternal = newWallet(tokensDollarProviderExternal, 2);

    Party* dollarProvider = newParty(DOLLARPROVIDER, 1, walletDollarProviderExternal);
    Party* adaProvider = newParty(ADAPROVIDER, 2, walletDollarProviderExternal);


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
                    // Most of the error handling has been moved to the makeDeposit function
                    if (res == 0){}else{}
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

    // Those are various properties
    // Mainly to debug modeling
    int reach = 1;
    __CPROVER_assert(reach == 0, "Are the properties dead-code -- needs to fail");
    
    __CPROVER_assert(success == 0, "Impossible to get a successful contract");
    __CPROVER_assert(success == 1, "Impossible to get a failing contract");
    __CPROVER_assert(initialTotalAda == finalTotalAda, "Ada are preserved!");
    __CPROVER_assert(initialTotalDollar == finalTotalDollar, "Dollar are preserved!");
    __CPROVER_assert(success != -1, "Always finish on a Close contract");
    // Check that the internal accounts are all empty
    __CPROVER_assert(adaAdaProviderInternal.amount == 0 && adaDollarProviderInternal.amount == 0, "No ada left in the contract");
    __CPROVER_assert(dollarAdaProviderInternal.amount == 0 && dollarDollarProviderInternal.amount == 0, "No dollar left in the contract");
    // Free allocated memory
    // TODO: Factor out the free functions
    free(failedContract);
    free(successContract);
    free(payAdaProvider);
    free(payDollarProvider);
    free(whenDepositDollarProvider);
    free(whenDepositAdaProvider);
    free(walletAdaProviderExternal->tokens);
    free(walletAdaProviderExternal);
    free(walletDollarProviderExternal->tokens);
    free(walletDollarProviderExternal);
    free(internalWallet->accounts);
    free(internalWallet);
    free(walletAdaProviderInternal->tokens);
    free(walletAdaProviderInternal);
    free(walletDollarProviderInternal->tokens);
    free(walletDollarProviderInternal);
    free(adaProvider);
    free(dollarProvider);
    free(state->parties);
    free(state);

    return res_ret;
}