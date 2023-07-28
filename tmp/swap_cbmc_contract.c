#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NUMTOKENS 2

typedef enum {
    ADAPROVIDER,
    DOLLARPROVIDER,
    ATTACKER,
    OTHER_PARTY
} PartyType;

typedef enum {
    ADA,
    DOLLAR,
    OTHER_CURRENCY
} CurrencyType;

typedef struct Token {
    CurrencyType currency;
    int amount;
} Token;

typedef struct Wallet {
    Token* tokens;
    int numTokens;
} Wallet;

typedef struct Party {
    PartyType partyType;
    const char* name;
    int id;
    Wallet wallet;
} Party;

typedef struct InternalAccount {
    int id;
    Wallet wallet;
} InternalAccount;

typedef struct InternalWallet {
    InternalAccount* accounts;
    int numAccounts;
} InternalWallet;

typedef struct Transaction {
    Party* source;
    Party* destination;
    int amount;
    CurrencyType currency;
} Transaction;

typedef struct PayParameters {
    Party* payer;
    Party* receiver;
    int amount;
    CurrencyType currency;
} PayParameters;

typedef struct DepositParameters {
    Party* depositor;
    Party* receiver;
    int amount;
    CurrencyType currency;
    int timeout;
} DepositParameters;

typedef struct CloseParameters {
    const int id;
} CloseParameters;

typedef union ContractParameters {
    PayParameters payParams;
    DepositParameters depositParams;
    CloseParameters closeParams;
} ContractParameters;

typedef enum {
    PAY,
    DEPOSIT,
    CLOSE
} ContractType;

typedef struct Contract Contract;

typedef struct Contract {
    ContractType type;
    ContractParameters params;
    Contract* subContractOK;
    Contract* continueAs;
} Contract;

typedef struct ContractState {
    Contract* currentContract;
    InternalWallet internalWallet;
    Party** parties;
    int numParties;
} ContractState;