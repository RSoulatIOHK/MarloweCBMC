#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
    DEPOSIT,
    PAY,
    CLOSE
} ContractType;

typedef struct Contract {
    ContractType type;
    char parameters[101];
    struct Contract* subContractOK;
    struct Contract* continueAs;
} Contract;

typedef struct DepositContract {
    char depositor[21];
    char receiver[21];
    int amount;
    char currency[21];
} DepositContract;

typedef struct PayContract {
    char payee[21];
    char receiver[21];
    int amount;
    char currency[21];
} PayContract;

typedef struct Token {
    char currency[21];
    int amount;
} Token;

typedef struct Wallet {
    Token* tokens;
    int numTokens;
} Wallet;

typedef struct Party {
    char name[21];
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

typedef struct ContractState {
    Contract* currentContract;
    InternalWallet internalWallet;
    Party** parties;
    int numParties;
} ContractState;

typedef struct Transaction {
    char source[21];
    char destination[21];
    int amount;
    char currency[21];
} Transaction;

