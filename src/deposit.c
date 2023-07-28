#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/constants.h"
#include "../include/types.h"
#include "../include/getters.h"

int makeDeposit(ContractState* state, const Transaction* candidateTransaction, const DepositParameters* depositPayload) {
    // Retrieve the source and destination parties
    Party* sourceParty = candidateTransaction->source;
    Party* destinationParty = candidateTransaction->destination;

    // Check if the source and destination parties exist
    if (sourceParty == NULL || destinationParty == NULL) {
        printf("Invalid transaction! Source or destination party not found.\n");
        return 1;
    }

    // Retrieve the destination internal account
    InternalAccount* destinationAccount = NULL;
    for (int i = 0; i < state->internalWallet.numAccounts; i++) {
        // printf("DEBUG: Internal ID %d for Party ID %d\n", state->internalWallet.accounts[i].id, destinationParty->id);
        if (state->internalWallet.accounts[i].id == destinationParty->id) {
            destinationAccount = &(state->internalWallet.accounts[i]);
        }
    }

    // Check if the destination internal account exists
    if (destinationAccount == NULL) {
        printf("Invalid transaction! Destination internal account not found.\n");
        return 1;
    }

    // Check if there are enough funds in the source external wallet
    int sourceBalance = 0;
    // __CPROVER_assume(sourceParty->wallet.numTokens == 2);
    for (int i = 0; i < NUMTOKENS; i++) {
        if (sourceParty->wallet.tokens[i].currency == candidateTransaction->currency) {
            sourceBalance = sourceParty->wallet.tokens[i].amount;
        }
    }

    if (sourceBalance < candidateTransaction->amount) {
        printf("Insufficient funds in the source external wallet.\n");
        return 1;
    }

    // Check if the candidate transaction matches the deposit payload
    if (candidateTransaction->source == depositPayload->depositor &&
        candidateTransaction->destination == depositPayload->receiver &&
        candidateTransaction->amount == depositPayload->amount &&
        candidateTransaction->currency == depositPayload->currency) {

        // Credit the payment amount to the destination internal account
        if (destinationAccount->wallet.tokens[0].currency == candidateTransaction->currency) {
            destinationAccount->wallet.tokens[0].amount += candidateTransaction->amount;
        }
        if (destinationAccount->wallet.tokens[1].currency == candidateTransaction->currency) {
            destinationAccount->wallet.tokens[1].amount += candidateTransaction->amount;
        }

        // Deduct the payment amount from the source external wallet
        // __CPROVER_assume(sourceParty->wallet.numTokens == 2);
        printf("DEBUG: NumTokens is %d\n", NUMTOKENS);
        if (sourceParty->wallet.tokens[0].currency == candidateTransaction->currency) {
            sourceParty->wallet.tokens[0].amount -= candidateTransaction->amount;
        }
        if (sourceParty->wallet.tokens[1].currency == candidateTransaction->currency) {
            sourceParty->wallet.tokens[1].amount -= candidateTransaction->amount;
        }

        printf("Deposit processed:\n");
        printf("Source: %s (Wallet ID: %d)\n", candidateTransaction->source->name, sourceParty->id);
        printf("Destination: %s (Internal Account ID: %d)\n", candidateTransaction->destination->name, destinationAccount->id);
        printf("Amount: %d\n", candidateTransaction->amount);
        printf("Currency: %s\n", getCurrencyTypeName(candidateTransaction->currency));

        // Move the contract to the subContractOK pointer
        state->currentContract = state->currentContract->subContractOK;
        return 0; // Deposit successful
    } else {
        printf("Invalid transaction! Deposit failed.\n");

        // Move the contract to the continueAs pointer
        // TODO: Remove this when the timeout is added, as it's not the correct semantics
        state->currentContract = state->currentContract->continueAs;
        return 1; // Deposit failed
    }
}