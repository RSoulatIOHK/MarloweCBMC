#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/constants.h"
#include "../include/types.h"


Token* newTokenHolding(CurrencyType currency, int amount) {
    Token* token = malloc(sizeof(Token));
    token->currency = currency;
    token->amount = amount;
    return token;
}

// Function to create a new wallet
Wallet* newWallet(Token tokens[], int numTokens) {
    Wallet* wallet = malloc(sizeof(Wallet));
    wallet->tokens = malloc(sizeof(Token) * numTokens);
    memcpy(wallet->tokens, tokens, sizeof(Token) * numTokens);
    wallet->numTokens = numTokens;
    return wallet;
}

// Function to create a new party
Party* newParty(const char* name, int id, Wallet* wallet) {
    Party* party = malloc(sizeof(Party));
    party->name = name;
    party->id = id;
    memcpy(&party->wallet, wallet, sizeof(Wallet));
    return party;
}

// Function to create a new internal account
InternalAccount* newInternalAccount(int id, Wallet wallet) {
    InternalAccount* account = malloc(sizeof(InternalAccount));
    account->id = id;
    memcpy(&(account->wallet), &wallet, sizeof(Wallet));
    return account;
}

// Function to create a new internal wallet
InternalWallet* newInternalWallet(InternalAccount accounts[], int numAccounts) {
    InternalWallet* wallet = malloc(sizeof(InternalWallet));
    wallet->accounts = malloc(sizeof(InternalAccount) * numAccounts);
    memcpy(wallet->accounts, accounts, sizeof(InternalAccount) * numAccounts);
    wallet->numAccounts = numAccounts;
    return wallet;
}

ContractState* newContractState(Contract* currentContract, InternalWallet* internalWallet, Party* parties[], int numParties) {
    ContractState* state = malloc(sizeof(ContractState));
    state->currentContract = currentContract;
    memcpy(&state->internalWallet, internalWallet, sizeof(InternalWallet));
    state->parties = malloc(sizeof(Party*) * numParties);
    memcpy(state->parties, parties, sizeof(Party*) * numParties);
    state->numParties = numParties;
    return state;
}

Contract* newContract(ContractType type, ContractParameters params, Contract* subContractOK, Contract* continueAs) {
    Contract* contract = malloc(sizeof(Contract));
    contract->type = type;
    memcpy(&(contract->params), &params, sizeof(ContractParameters));
    contract->subContractOK = subContractOK;
    contract->continueAs = continueAs;
    return contract;
}
