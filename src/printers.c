#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/constants.h"
#include "../include/types.h"
#include "../include/getters.h"

void printLedgerState(Ledger* ledger) {
    printf("=== Ledger State ===\n");

    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];

        printf("UTxO ID: %d\n", i);
        printf("Spent: %s\n", utxo->spent ? "Yes" : "No");
        printf("Owner ID: %d\n", utxo->ownerID);
        printf("Token:\n");
        for (int i = 0; i <= NUMTOKENS; i++){
            printf(" - Token Amount: %d", utxo->tokens[i]->amount);
            switch (utxo->tokens[i]->currency){
            case ADA:
                printf("ADA\n");
                break;
            case DOLLAR:
                printf("DOLLARS\n");
                break;
            case OTHER_CURRENCY:
                printf("UNKNOWN\n");
                break;
            }
        }
        printf("\n");
    }

    printf("===================\n");
}

void prettyPrintPayContract(const PayParameters* payParams) {
    printf("%s has PAID %s from its internal account to their outside wallet the amount of %d %s\n",
       payParams->payer->name, payParams->receiver->name,
       payParams->amount, getCurrencyTypeName(payParams->currency));
}

void prettyPrintDepositContract(const DepositParameters* depositParams) {
    printf("%s has DEPOSITED into the internal account of %s the amount of %d %s\n",
           depositParams->depositor->name, depositParams->receiver->name,
           depositParams->amount, getCurrencyTypeName(depositParams->currency));
}


void prettyPrintWholeContractState(const ContractState* state, int currentTime) {
    printf("###########################################\n");
    printf("#         STATE OF THE SIMULATION         #\n");
    printf("###########################################\n\n");
    printf("Current time is: %d\n\n", currentTime);
    printf("-------------------------------------------\n");
    printf("Party private holdings:\n");

    for (int i = 0; i < state->numParties; i++) {
        printf("%s has the following holdings in their wallet:\n", state->parties[i]->name);
        for (int j = 0; j < NUMTOKENS; j++) {
            const Token* token = &state->parties[i]->wallet.tokens[j];
            printf("\t%d %s\n", token->amount, getCurrencyTypeName(token->currency));
        }
        printf("\n");
    }
    printf("-------------------------------------------\n");
    printf("Internal wallet holdings:\n");
    for (int i = 0; i < state->internalWallet.numAccounts; i++) {
        const char* partyName = NULL;
        for (int j = 0; j < state->numParties; j++) {
            if (state->parties[j]->id == state->internalWallet.accounts[i].id) {
                partyName = state->parties[j]->name;
                break;
            }
        }
        if (partyName) {
            printf("%s (Internal Account ID: %d) has the following holdings:\n", partyName, state->internalWallet.accounts[i].id);
            for (int j = 0; j < NUMTOKENS; j++) {
                const Token* token = &state->internalWallet.accounts[i].wallet.tokens[j];
                printf("\t%d %s\n", token->amount, getCurrencyTypeName(token->currency));
            }
            printf("\n");
        }
    }
    if (state->currentContract) {
        printf("Next Contract:\n");
        switch (state->currentContract->type) {
            case DEPOSIT:
                printf("Type: DEPOSIT\n");
                printf("Parameters: depositor=%s, receiver=%s, amount=%d, currency=%s, timeout=%d\n",
                       getPartyTypeName(state->currentContract->params.depositParams.depositor),
                       getPartyTypeName(state->currentContract->params.depositParams.receiver),
                       state->currentContract->params.depositParams.amount,
                       getCurrencyTypeName(state->currentContract->params.depositParams.currency),
                       state->currentContract->params.depositParams.timeout);
                break;
            case PAY:
                printf("Type: PAY\n");
                printf("Parameters: payer=%s, receiver=%s, amount=%d, currency=%s\n",
                       getPartyTypeName(state->currentContract->params.payParams.payer),
                       getPartyTypeName(state->currentContract->params.payParams.receiver),
                       state->currentContract->params.payParams.amount,
                       getCurrencyTypeName(state->currentContract->params.payParams.currency));
                break;
            case CLOSE:
                printf("Type: CLOSE\n");
                printf("Parameters: id=%d\n", state->currentContract->params.closeParams.id);
                break;
            default:
                printf("Unknown Contract Type\n");
                break;
        }
    } else {
        printf("No Next Contract\n");
    }
    printf("###########################################\n\n");
}