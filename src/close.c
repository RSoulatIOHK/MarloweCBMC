#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/constants.h"
#include "../include/types.h"

void processClose(ContractState* state) {
    // Iterate over each internal account
    for (int i = 0; i < state->internalWallet.numAccounts; i++) {
        InternalAccount* account = &(state->internalWallet.accounts[i]);

        // Find the corresponding party for the internal account
        Party* externalParty = NULL;
        for (int j = 0; j < state->numParties; j++) {
            if (state->parties[j]->id == account->id) {
                externalParty = state->parties[j];
                break;
            }
        }

        // Refund the tokens from the internal account to the external wallet
        for (int j = 0; j < account->wallet.numTokens; j++) {
            Token* token = &(account->wallet.tokens[j]);
            for (int k = 0; k < externalParty->wallet.numTokens; k++) {
                if (externalParty->wallet.tokens[k].currency == token->currency) {
                    externalParty->wallet.tokens[k].amount += token->amount;
                    break;
                }
            }
        }

        // Clear the internal account
        for (int j = 0; j < account->wallet.numTokens; j++) {
            account->wallet.tokens[j].amount = 0;
        }
    }
}