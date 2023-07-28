#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/constants.h"
#include "../include/types.h"
#include "../include/getters.h"

Transaction convertToTransaction(const PayParameters* payParams) {
    Transaction transaction;
    transaction.source = payParams->payer;
    transaction.destination = payParams->receiver;
    transaction.amount = payParams->amount;
    transaction.currency = payParams->currency;
    return transaction;
}

int makePayment(ContractState* state, const Transaction* candidateTransaction) {
    // Retrieve the source and destination parties
    Party* sourceParty = candidateTransaction->source;
    Party* destinationParty = candidateTransaction->destination;

    // Check if the source and destination parties exist
    if (sourceParty == NULL || destinationParty == NULL) {
        printf("Invalid transaction! Source or destination party not found.\n");
        return 1;
    }

    // Retrieve the source internal account
    InternalAccount* sourceAccount = NULL;
    for (int i = 0; i < state->internalWallet.numAccounts; i++) {
        if (state->internalWallet.accounts[i].id == sourceParty->id) {
            sourceAccount = &(state->internalWallet.accounts[i]);
        }
    }

    // Check if the source internal account exists
    if (sourceAccount == NULL) {
        printf("Invalid transaction! Source internal account not found.\n");
        return 1;
    }

    // Check if there are enough funds in the source internal account
    int sourceBalance = 0;
    for (int i = 0; i < NUMTOKENS; i++) {
        if (sourceAccount->wallet.tokens[i].currency == candidateTransaction->currency) {
            sourceBalance = sourceAccount->wallet.tokens[i].amount;
        }
    }

    if (sourceBalance < candidateTransaction->amount) {
        printf("Insufficient funds in the source internal account.\n");
        return 1;
    }

    // Deduct the payment amount from the source internal account
    for (int i = 0; i < NUMTOKENS; i++) {
        if (sourceAccount->wallet.tokens[i].currency == candidateTransaction->currency) {
            sourceAccount->wallet.tokens[i].amount -= candidateTransaction->amount;
        }
    }

    // Credit the payment amount to the destination external wallet
    for (int i = 0; i < NUMTOKENS; i++) {
        if (destinationParty->wallet.tokens[i].currency == candidateTransaction->currency) {
            destinationParty->wallet.tokens[i].amount += candidateTransaction->amount;
        }
    }

    printf("Payment processed:\n");
    printf("Source: %s (Internal Account ID: %d)\n", sourceParty->name, sourceAccount->id);
    printf("Destination: %s (Wallet ID: %d)\n", destinationParty->name, destinationParty->id);
    printf("Amount: %d\n", candidateTransaction->amount);
    printf("Currency: %s\n", getCurrencyTypeName(candidateTransaction->currency));

    // Move the contract state to the continueAs contract
    state->currentContract = state->currentContract->continueAs;
    return 0;
}
