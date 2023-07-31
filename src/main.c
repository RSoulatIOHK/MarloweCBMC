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
//#include "../include/mock_cbmc_helper.h"

int main() {
    // Define the tokens for internal accounts
    Token ada1 = {.currency = ADA, .amount = 0};
    Token dollar1 = {.currency = DOLLAR, .amount = 0};
    Token ada2 = {.currency = ADA, .amount = 0};
    Token dollar2 = {.currency = DOLLAR, .amount = 0};

    // Define the wallets for internal accounts
    Token tokens1[] = {ada1, dollar1};
    Wallet* wallet1 = newWallet(tokens1, 2);
    Token tokens2[] = {ada2, dollar2};
    Wallet* wallet2 = newWallet(tokens2, 2);

    // Define the internal accounts
    InternalAccount accounts[] = {
        {1, *wallet1},
        {2, *wallet2}
    };

    // Define the internal wallet
    InternalWallet* internalWallet = newInternalWallet(accounts, 2);

    // Define the tokens for external wallets
    Token ada3 = {.currency = ADA, .amount = constr_non_det_int(0,50)};
    Token dollar3 = {.currency = DOLLAR, .amount = constr_non_det_int(0,50)};
    Token ada4 = {.currency = ADA, .amount = constr_non_det_int(0,50)};
    Token dollar4 = {.currency = DOLLAR, .amount = constr_non_det_int(0,100)};
    
    // Define the wallets for external wallets
    Token tokens3[] = {ada3, dollar3};
    Wallet* wallet3 = newWallet(tokens3, 2);
    Token tokens4[] = {ada4, dollar4};
    Wallet* wallet4 = newWallet(tokens4, 2);

    Party* dollarProvider = newParty("DollarProvider", 1, wallet4);
    Party* adaProvider = newParty("AdaProvider", 2, wallet3);

    Contract* successContract = newContract(CLOSE, (ContractParameters){
    .closeParams = {
        .id = 0
        }
    }, NULL, NULL);

    Contract* failedContract = newContract(CLOSE, (ContractParameters){
        .closeParams = {
            .id = 1
            }
        }, NULL, NULL);

    Contract* payAdaProvider = newContract(PAY, (ContractParameters){
        .payParams = {
            .payer = dollarProvider,
            .receiver = adaProvider,
            .amount = 100,
            .currency = DOLLAR
            }
        }, NULL, successContract);

    Contract* payDollarProvider = newContract(PAY, (ContractParameters){
        .payParams = {
            .payer = adaProvider,
            .receiver = dollarProvider,
            .amount = 50,
            .currency = ADA
            }
        }, NULL, payAdaProvider);

    Contract* whenDepositDollarProvider = newContract(DEPOSIT, (ContractParameters){
        .depositParams = {
            .depositor = dollarProvider,
            .receiver = dollarProvider,
            .amount = 100,
            .currency = DOLLAR,
            .timeout = 12
            }
        }, payDollarProvider, failedContract);

    Contract* whenDepositAdaProvider = newContract(DEPOSIT, (ContractParameters){
        .depositParams = {
            .depositor = adaProvider,
            .receiver = adaProvider,
            .amount = 50,
            .currency = ADA,
            .timeout = 10
            }
        }, whenDepositDollarProvider, failedContract);


    // Define the contract state
    Party* parties[] = {adaProvider, dollarProvider};
    ContractState* state = newContractState(whenDepositAdaProvider, internalWallet, parties, 2);

    // Simulation time
    int currentTime = 0;
    int contractTimeout = 20;

    int success = 0;

    // THIS IS THE MAIN LOOP OF THE EXECUTION
    // PROBABLY NEED TO BE FACTORED OUT
    int res_ret = 0;

    int initialTotalAda = getTotalAda(state);
    int initialTotalDollar = getTotalDollars(state);

    while (currentTime < contractTimeout && res_ret == 0) {
        //prettyPrintWholeContractState(state, currentTime);
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
                    //state->currentContract = state->currentContract->continueAs;
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
                    Transaction depositTransaction = {
                        .source = state->currentContract->params.depositParams.depositor,
                        .destination = state->currentContract->params.depositParams.receiver,
                        .amount = state->currentContract->params.depositParams.amount,
                        .currency = state->currentContract->params.depositParams.currency
                    };
                    int res = makeDeposit(state, &depositTransaction, &(state->currentContract->params.depositParams));
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
    // Free allocated memory
    free(failedContract);
    free(successContract);
    free(payAdaProvider);
    free(payDollarProvider);
    free(whenDepositDollarProvider);
    free(whenDepositAdaProvider);
    free(wallet1->tokens);
    free(wallet1);
    free(wallet2->tokens);
    free(wallet2);
    free(internalWallet->accounts);
    free(internalWallet);
    free(wallet3->tokens);
    free(wallet3);
    free(wallet4->tokens);
    free(wallet4);
    free(adaProvider);
    free(dollarProvider);
    free(state->parties);
    free(state);

    return res_ret;
}
