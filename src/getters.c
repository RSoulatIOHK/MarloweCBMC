#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/constants.h"
#include "../include/types.h"

const char* getCurrencyTypeName(CurrencyType currency) {
    switch (currency) {
        case ADA:
            return "ADA";
        case DOLLAR:
            return "DOLLAR";
        case OTHER_CURRENCY:
            return "OTHER_CURRENCY";
        default:
            return "UNKNOWN";
    }
}

const char* getPartyTypeName(const Party* party) {
    return party->name;
}



int getTotalAda(const ContractState* state) {
    int totalAda = 0;
    for (int i = 0; i < state->numParties; i++) {
        const Party* party = state->parties[i];
        for (int j = 0; j < party->wallet.numTokens; j++) {
            if (party->wallet.tokens[j].currency == ADA) {
                totalAda += party->wallet.tokens[j].amount;
            }
        }
    }
    return totalAda;
}

int getTotalDollars(const ContractState* state) {
    int totalDollars = 0;
    for (int i = 0; i < state->numParties; i++) {
        const Party* party = state->parties[i];
        for (int j = 0; j < party->wallet.numTokens; j++) {
            if (party->wallet.tokens[j].currency == DOLLAR) {
                totalDollars += party->wallet.tokens[j].amount;
            }
        }
    }
    return totalDollars;
}
