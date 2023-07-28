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
    int next_action;
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

Contract* newContract(ContractType type, ContractParameters params, Contract* subContractOK, Contract* continueAs) {
    Contract* contract = malloc(sizeof(Contract));
    contract->type = type;
    memcpy(&(contract->params), &params, sizeof(ContractParameters));
    contract->subContractOK = subContractOK;
    contract->continueAs = continueAs;
    return contract;
}

void freeContract(Contract* contract) {
    free(contract);
}

Transaction convertToTransaction(const PayParameters* payParams) {
    Transaction transaction;
    transaction.source = payParams->payer;
    transaction.destination = payParams->receiver;
    transaction.amount = payParams->amount;
    transaction.currency = payParams->currency;
    return transaction;
}

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
Party* newParty(const char* name, int id, Wallet* wallet, int first_action) {
    Party* party = malloc(sizeof(Party));
    party->name = name;
    party->id = id;
    party->next_action = first_action;
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

int main() {
    // Define the tokens for internal accounts
    Token ada1 = {.currency = ADA, .amount = 0};
    Token dollar1 = {.currency = DOLLAR, .amount = 0};
    Token ada2 = {.currency = ADA, .amount = 0};
    Token dollar2 = {.currency = DOLLAR, .amount = 0};

    // Define the wallets for internal accounts
    Token tokens1[] = {ada1, dollar1};
    Wallet* wallet1 = newWallet(tokens1, 2);
    Token tokens2[] = {ada2, dollar2};
    Wallet* wallet2 = newWallet(tokens2, 2);

    // Define the internal accounts
    InternalAccount accounts[] = {
        {1, *wallet1},
        {2, *wallet2}
    };

    // Define the internal wallet
    InternalWallet* internalWallet = newInternalWallet(accounts, 2);

    // Define the tokens for external wallets
    Token ada3 = {.currency = ADA, .amount = 50};
    Token dollar3 = {.currency = DOLLAR, .amount = 50};
    Token ada4 = {.currency = ADA, .amount = 50};
    Token dollar4 = {.currency = DOLLAR, .amount = 100};
    
    // Define the wallets for external wallets
    Token tokens3[] = {ada3, dollar3};
    Wallet* wallet3 = newWallet(tokens3, 2);
    Token tokens4[] = {ada4, dollar4};
    Wallet* wallet4 = newWallet(tokens4, 2);

    int first_action1 = 5;
    int first_action2 = 6;

    Party* dollarProvider = newParty("DollarProvider", 1, wallet4, first_action1);
    Party* adaProvider = newParty("AdaProvider", 2, wallet3, first_action2);

    Contract* successContract = newContract(CLOSE, (ContractParameters){
    .closeParams = {
        .id = 0
        }
    }, NULL, NULL);

    Contract* failedContract = newContract(CLOSE, (ContractParameters){
        .closeParams = {
            .id = 1
            }
        }, NULL, NULL);

    Contract* payAdaProvider = newContract(PAY, (ContractParameters){
        .payParams = {
            .payer = dollarProvider,
            .receiver = adaProvider,
            .amount = 100,
            .currency = DOLLAR
            }
        }, NULL, successContract);

    Contract* payDollarProvider = newContract(PAY, (ContractParameters){
        .payParams = {
            .payer = adaProvider,
            .receiver = dollarProvider,
            .amount = 50,
            .currency = ADA
            }
        }, NULL, payAdaProvider);

    Contract* whenDepositDollarProvider = newContract(DEPOSIT, (ContractParameters){
        .depositParams = {
            .depositor = dollarProvider,
            .receiver = dollarProvider,
            .amount = 100,
            .currency = DOLLAR,
            .timeout = 12
            }
        }, payDollarProvider, failedContract);

    Contract* whenDepositAdaProvider = newContract(DEPOSIT, (ContractParameters){
        .depositParams = {
            .depositor = adaProvider,
            .receiver = adaProvider,
            .amount = 50,
            .currency = ADA,
            .timeout = 10
            }
        }, whenDepositDollarProvider, failedContract);


    // Define the contract state
    Party* parties[] = {adaProvider, dollarProvider};
    ContractState* state = newContractState(whenDepositAdaProvider, internalWallet, parties, 2);

    // Simulation time
    int currentTime = 0;
    int contractTimeout = 20;

    int success = 0;

    // THIS IS THE MAIN LOOP OF THE EXECUTION
    // PROBABLY NEED TO BE FACTORED OUT
    int res_ret = 0;

    int initialTotalAda = getTotalAda(state);
    int initialTotalDollar = getTotalDollars(state);

    while (currentTime < contractTimeout && res_ret == 0) {
        prettyPrintWholeContractState(state, currentTime);
        currentTime++;

        if (state->currentContract == NULL) {
            printf("End of simulation because the contract is now NULL\n");
            break;
        }

        switch (state->currentContract->type) {
            case PAY: {
                Transaction transaction = convertToTransaction(&(state->currentContract->params.payParams));
                int res = makePayment(state, &transaction);
                if (res == 0) {
                    //state->currentContract = state->currentContract->continueAs;
                } else {
                    fprintf(stderr, "PAY action was not successful\n");
                    res_ret = 1;
                }
                break;
            }
            case CLOSE:
                processClose(state);
                if (state->currentContract->params.closeParams.id == 0) {
                    success = 1;
                } else {
                    success = 0;
                }
                state->currentContract = state->currentContract->continueAs;
                break;
            case DEPOSIT: {
                if (currentTime > state->currentContract->params.depositParams.timeout){
                    state->currentContract = state->currentContract->continueAs;
                }
                else {
                    Transaction depositTransaction = {
                        .source = state->currentContract->params.depositParams.depositor,
                        .destination = state->currentContract->params.depositParams.receiver,
                        .amount = state->currentContract->params.depositParams.amount,
                        .currency = state->currentContract->params.depositParams.currency
                    };
                    int res = makeDeposit(state, &depositTransaction, &(state->currentContract->params.depositParams));
                }
                break;
            }
            default:
                fprintf(stderr, "Error: Unsupported contract type\n");
                res_ret = 1;
        }
    }

    int finalTotalAda = getTotalAda(state);
    int finalTotalDollar = getTotalDollars(state);

    // Free allocated memory
    free(failedContract);
    free(successContract);
    free(payAdaProvider);
    free(payDollarProvider);
    free(whenDepositDollarProvider);
    free(whenDepositAdaProvider);
    free(wallet1->tokens);
    free(wallet1);
    free(wallet2->tokens);
    free(wallet2);
    free(internalWallet->accounts);
    free(internalWallet);
    free(wallet3->tokens);
    free(wallet3);
    free(wallet4->tokens);
    free(wallet4);
    free(adaProvider);
    free(dollarProvider);
    free(state->parties);
    free(state);

    return res_ret;
}
