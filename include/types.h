#include "../include/constants.h"

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

typedef struct {
    int spent;
    int ownerID;
    Token* tokens[NUMTOKENS];
} UTxO;

typedef struct {
    UTxO* inputs[MAX_INPUTS];
    int numInputs;
    UTxO* outputs[MAX_OUTPUTS];
    int numOutputs;
    int signerID;
} Transaction;

// Structure to represent the ledger
typedef struct {
    UTxO* unspentTransactions[MAX_UTXOS];
    int numUnspentTransactions;
} Ledger;

typedef struct Wallet {
    Token* tokens;
    int numTokens;
    int ownerID;
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
