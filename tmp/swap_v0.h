#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef const char* role_t;
typedef const char* token_t;

typedef enum {
    DEPOSIT,
    PAY,
    CLOSE
} ContractType;

typedef struct Contract {
    ContractType type;
    char* parameters;
    struct Contract* subContractOK;
    struct Contract* continueAs;
} Contract;

typedef struct DepositContract {
    role_t depositor;
    role_t receiver;
    int amount;
    token_t currency;
} DepositContract;

typedef struct PayContract {
    role_t payee;
    role_t receiver;
    int amount;
    token_t currency;
} PayContract;

// Define a token
typedef struct Token {
    const char* currency;
    int amount;
} Token;

// Define a wallet
typedef struct Wallet {
    Token* tokens;
    int numTokens;
} Wallet;

// Define a party
typedef struct Party {
    const char* name;
    int id;
    Wallet wallet;
} Party;

typedef struct InternalAccount {
    int id;
    Wallet wallet;
} InternalAccount;

// Define an internal wallet
typedef struct InternalWallet {
    InternalAccount* accounts;
    int numAccounts;
} InternalWallet;

typedef struct ContractState {
    Contract* currentContract;
    InternalWallet internalWallet;
    Party** parties;
    int numParties;
} ContractState;

typedef struct Transaction {
    role_t source;
    role_t destination;
    int amount;
    token_t currency;
} Transaction;
