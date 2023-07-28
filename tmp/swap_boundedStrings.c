#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "swap_v0.h"

// Type to type
Transaction convertToTransaction(const PayContract* payContract) {
    Transaction transaction;
    strncpy(transaction.source, payContract->payee, sizeof(transaction.source) - 1);
    strncpy(transaction.destination, payContract->receiver, sizeof(transaction.destination) - 1);
    transaction.amount = payContract->amount;
    strncpy(transaction.currency, payContract->currency, sizeof(transaction.currency) - 1);
    return transaction;
}

// Function to create a new token
Token* newTokenHolding(const char* currency, int amount) {
    Token* token = malloc(sizeof(Token));
    strncpy(token->currency, currency, sizeof(token->currency) - 1);
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
    strncpy(party->name, name, sizeof(party->name) - 1);
    party->id = id;
    memcpy(&party->wallet, wallet, sizeof(Wallet));
    return party;
}

// Function to create a new internal account
InternalAccount* newInternalAccount(int id, Wallet wallet) {
    InternalAccount* account = malloc(sizeof(InternalAccount));
    account->id = id;
    memcpy(&account->wallet, &wallet, sizeof(Wallet));
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

// Function to create a new contract state
ContractState* newContractState(Contract* currentContract, InternalWallet* internalWallet, Party* parties[], int numParties) {
    ContractState* state = malloc(sizeof(ContractState));
    state->currentContract = currentContract;
    memcpy(&state->internalWallet, internalWallet, sizeof(InternalWallet));
    state->parties = malloc(sizeof(Party*) * numParties);
    memcpy(state->parties, parties, sizeof(Party*) * numParties);
    state->numParties = numParties;
    return state;
}

PayContract* parsePayPayload(char* parameters) {
    PayContract* payContract = malloc(sizeof(PayContract));
    // Split the parameters string into tokens
    char* token = strtok(parameters, " ");
    strncpy(payContract->payee, token, sizeof(payContract->payee) - 1);

    token = strtok(NULL, " ");
    strncpy(payContract->receiver, token, sizeof(payContract->receiver) - 1);
    
    token = strtok(NULL, " ");
    payContract->amount = atoi(token);
    
    token = strtok(NULL, " ");
    strncpy(payContract->currency, token, sizeof(payContract->currency) - 1);
    
    return payContract;
}

DepositContract parseDepositPayload(char* parameters) {
    DepositContract depositContract;

    // Split the parameters string into tokens
    char* token = strtok(parameters, " ");
    strncpy(depositContract.depositor, token, sizeof(depositContract.depositor) - 1);

    token = strtok(NULL, " ");
    strncpy(depositContract.receiver, token, sizeof(depositContract.receiver) - 1);

    token = strtok(NULL, " ");
    depositContract.amount = atoi(token);

    token = strtok(NULL, " ");
    strncpy(depositContract.currency, token, sizeof(depositContract.currency) - 1);

    return depositContract;
}

Contract* newContract(ContractType type, const char* parameters, Contract* subContractOK, Contract* continueAs) {
    Contract* contract = malloc(sizeof(Contract));
    contract->type = type;
    
    if (parameters != NULL) {
        strncpy(contract->parameters, parameters, sizeof(contract->parameters) - 1);
    } else {
    }
    
    contract->subContractOK = subContractOK;
    contract->continueAs = continueAs;
    return contract;
}


void prettyPrintPayContract(PayContract payContract) {
    char buffer[256];
    sprintf(buffer, "%s has PAID %s from its internal account to their outside wallet the amount of %d %s",
            payContract.payee, payContract.receiver, payContract.amount, payContract.currency);
    printf("%s\n", buffer);
}

void prettyPrintDepositContract(DepositContract depositContract) {
    char buffer[256];
    sprintf(buffer, "%s has DEPOSITED into the internal account of %s the amount of %d %s ",
            depositContract.depositor, depositContract.receiver, depositContract.amount, depositContract.currency);
    printf("%s\n", buffer);
}

void prettyPrintWholeContractState(ContractState* state, int currentTime) {
    printf("###########################################\n");
    printf("#         STATE OF THE SIMULATION         #\n");
    printf("###########################################\n\n");
    printf("Current time is: %d\n\n", currentTime);
    printf("-------------------------------------------\n");
    printf("Party private holdings:\n");

    for (int i = 0; i < state->numParties; i++) {
        printf("%s has the following holdings in their wallet:\n", state->parties[i]->name);
        for (int j = 0; j < state->parties[i]->wallet.numTokens; j++) {
            Token* token = &state->parties[i]->wallet.tokens[j];
            printf("\t%d %s\n", token->amount, token->currency);
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
            for (int j = 0; j < state->internalWallet.accounts[i].wallet.numTokens; j++) {
                printf("\t%d %s\n", state->internalWallet.accounts[i].wallet.tokens[j].amount, state->internalWallet.accounts[i].wallet.tokens[j].currency);
            }
            printf("\n");
        }
    }
    if (state->currentContract) {
        printf("Next Contract:\n");
        switch (state->currentContract->type) {
            case DEPOSIT:
                printf("Type: DEPOSIT\n");
                printf("Parameters: %s\n", state->currentContract->parameters);
                break;
            case PAY:
                printf("Type: PAY\n");
                printf("Parameters: %s\n", state->currentContract->parameters);
                break;
            case CLOSE:
                printf("Type: CLOSE\n");
                printf("No parameters\n");
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


int makePayment(ContractState* state, Transaction candidateTransaction, int currentTime) {
    // Retrieve the source and destination parties
    Party* sourceParty = NULL;
    Party* destinationParty = NULL;
    for (int i = 0; i < state->numParties; i++) {
        if (strcmp(state->parties[i]->name, candidateTransaction.source) == 0) {
            sourceParty = state->parties[i];
        }
        if (strcmp(state->parties[i]->name, candidateTransaction.destination) == 0) {
            destinationParty = state->parties[i];
        }
    }

    // Check if the source and destination parties exist
    if (sourceParty == NULL || destinationParty == NULL) {
        printf("Invalid transaction! Source or destination party not found.\n");
        return 1;
    }

    // Retrieve the source internal accounts
    InternalAccount* sourceAccount = NULL;
    for (int i = 0; i < state->internalWallet.numAccounts; i++) {
        if (state->internalWallet.accounts[i].id == sourceParty->id) {
            sourceAccount = &(state->internalWallet.accounts[i]);
        }
    }

    // Check if the source internal accounts exist
    if (sourceAccount == NULL ) {
        printf("Invalid transaction! Source or destination internal account not found.\n");
        return 1;
    }

    // Check if there are enough funds in the source internal account
    int sourceBalance = 0;
    for (int i = 0; i < sourceAccount->wallet.numTokens; i++) {
        if (strcmp(sourceAccount->wallet.tokens[i].currency, candidateTransaction.currency) == 0) {
            sourceBalance = sourceAccount->wallet.tokens[i].amount;
            break;
        }
    }

    if (sourceBalance < candidateTransaction.amount) {
        printf("Insufficient funds in the source internal account.\n");
        return 1;
    }

    // Deduct the payment amount from the source internal account
    for (int i = 0; i < sourceAccount->wallet.numTokens; i++) {
        if (strcmp(sourceAccount->wallet.tokens[i].currency, candidateTransaction.currency) == 0) {
            sourceAccount->wallet.tokens[i].amount -= candidateTransaction.amount;
            break;
        }
    }

    // Credit the payment amount to the destination external wallet
    for (int i = 0; i < destinationParty->wallet.numTokens; i++) {
        if (strcmp(destinationParty->wallet.tokens[i].currency, candidateTransaction.currency) == 0) {
            destinationParty->wallet.tokens[i].amount += candidateTransaction.amount;
            break;
        }
    }

    printf("Payment processed:\n");
    printf("Source: %s (Internal Account ID: %d)\n", candidateTransaction.source, sourceAccount->id);
    printf("Destination: %s (Wallet ID: %d)\n", candidateTransaction.destination, destinationParty->id);
    printf("Amount: %d\n", candidateTransaction.amount);
    printf("Currency: %s\n", candidateTransaction.currency);

    // Move the contract state to the continueAs contract
    state->currentContract = state->currentContract->continueAs;
    return 0;
}

int makeDeposit(ContractState* state, Transaction candidateTransaction, DepositContract depositPayload) {
    // Retrieve the source and destination parties
    Party* sourceParty = NULL;
    Party* destinationParty = NULL;
    for (int i = 0; i < state->numParties; i++) {
        if (strcmp(state->parties[i]->name, candidateTransaction.source) == 0) {
            sourceParty = state->parties[i];
        }
        if (strcmp(state->parties[i]->name, candidateTransaction.destination) == 0) {
            destinationParty = state->parties[i];
        }
    }

    // Check if the source and destination parties exist
    if (sourceParty == NULL || destinationParty == NULL) {
        printf("Invalid transaction! Source or destination party not found.\n");
        return 1;
    }

    // Retrieve the destination internal accounts
    InternalAccount* destinationAccount = NULL;
    for (int i = 0; i < state->internalWallet.numAccounts; i++) {
        if (state->internalWallet.accounts[i].id == destinationParty->id) {
            destinationAccount = &(state->internalWallet.accounts[i]);
        }
    }

    if (destinationAccount == NULL ) {
        printf("Invalid transaction! Source or destination internal account not found.\n");
        return 1;
    }

    int sourceBalance = 0;
    for (int i = 0; i < sourceParty->wallet.numTokens; i++) {
        if (strcmp(sourceParty->wallet.tokens[i].currency, candidateTransaction.currency) == 0) {
            sourceBalance = sourceParty->wallet.tokens[i].amount;
            break;
        }
    }

    if (sourceBalance < candidateTransaction.amount) {
        printf("Insufficient funds in the source internal account.\n");
        return 1;
    }

    // Check if the candidate transaction matches the deposit payload
    if (strcmp(candidateTransaction.source, depositPayload.depositor) == 0 &&
        strcmp(candidateTransaction.destination, depositPayload.receiver) == 0 &&
        candidateTransaction.amount == depositPayload.amount &&
        strcmp(candidateTransaction.currency, depositPayload.currency) == 0) {




        // Credit the payment amount to the destination internal account
        for (int i = 0; i < destinationAccount->wallet.numTokens; i++) {
            if (strcmp(destinationAccount->wallet.tokens[i].currency, candidateTransaction.currency) == 0) {
                destinationAccount->wallet.tokens[i].amount += candidateTransaction.amount;
                break;
            }
        }

        // Deduct the payment amount to the source external wallet
        for (int i = 0; i < sourceParty->wallet.numTokens; i++) {
            if (strcmp(sourceParty->wallet.tokens[i].currency, candidateTransaction.currency) == 0) {
                sourceParty->wallet.tokens[i].amount -= candidateTransaction.amount;
                break;
            }
        }

        printf("Deposit processed:\n");
        printf("Source: %s (Wallet ID: %d)\n", candidateTransaction.source, sourceParty->id);
        printf("Destination: %s (Internal Account ID: %d)\n", candidateTransaction.destination, destinationAccount->id);
        printf("Amount: %d\n", candidateTransaction.amount);
        printf("Currency: %s\n", candidateTransaction.currency);

        // Move the contract to the subcontract_ok pointer
        state->currentContract = state->currentContract->subContractOK;
        return 0; // Deposit successful
    } else {
        printf("Invalid transaction! Deposit failed.\n");

        // Move the contract to the continueAs pointer
        // TODO: Remove that when the timeout is added, this is not the correct semantics
        state->currentContract = state->currentContract->continueAs;
        return 1; // Deposit failed
    }
}

int constr_non_det_int(int min, int max){
    int res_ret;
    __CPROVER_assume(min <= res_ret && res_ret <= max);
    return res_ret;
}

int main() {
    Contract* successContract = newContract(CLOSE, "Success", NULL, NULL);
    Contract* FailedContract = newContract(CLOSE, "Fail", NULL, NULL);
    Contract* payAdaProvider = newContract(PAY, "DollarProvider AdaProvider 100 DOLLAR", NULL, successContract);
    Contract* payDollarProvider = newContract(PAY, "AdaProvider DollarProvider 50 ADA", NULL, payAdaProvider);
    Contract* whenDepositDollarProvider = newContract(DEPOSIT, "DollarProvider DollarProvider 100 DOLLAR", payDollarProvider, FailedContract);
    Contract* whenDepositAdaProvider = newContract(DEPOSIT, "AdaProvider AdaProvider 50 ADA", whenDepositDollarProvider, FailedContract);

    // Define the tokens for internal accounts
    Token ada1 = *newTokenHolding("ADA", 0);
    Token dollar1 = *newTokenHolding("DOLLAR", 0);
    Token ada2 = *newTokenHolding("ADA", 0);
    Token dollar2 = *newTokenHolding("DOLLAR", 0);

    // Define the wallets for internal accounts
    Token tokens1[] = { ada1, dollar1 };
    Wallet* wallet1 = newWallet(tokens1, 2);
    Token tokens2[] = { ada2, dollar2 };
    Wallet* wallet2 = newWallet(tokens2, 2);

    // Define the internal accounts
    InternalAccount accounts[] = {
        { 1, *wallet1 },
        { 2, *wallet2 }
    };

    // Define the internal wallet
    InternalWallet* internalWallet = newInternalWallet(accounts, 2);

    // Define the tokens for external wallets
    Token ada3 = *newTokenHolding("ADA", constr_non_det_int(0,1000));
    Token dollar3 = *newTokenHolding("DOLLAR", constr_non_det_int(0,1000));
    Token ada4 = *newTokenHolding("ADA", constr_non_det_int(0,1000));
    Token dollar4 = *newTokenHolding("DOLLAR", constr_non_det_int(0,1000));

    // Define the wallets for external wallets
    Token tokens3[] = { ada3, dollar3 };
    Wallet* wallet3 = newWallet(tokens3, 2);
    Token tokens4[] = { ada4, dollar4 };
    Wallet* wallet4 = newWallet(tokens4, 2);

    // Define the parties
    Party* adaProvider = newParty("AdaProvider", 1, wallet3);
    Party* dollarProvider = newParty("DollarProvider", 2, wallet4);

    // Define the contract state
    Party* parties[] = { adaProvider, dollarProvider };
    ContractState* state = newContractState(whenDepositAdaProvider, internalWallet, parties, 2);


    // Simulation time
    int currentTime = 0;
    int contractTimeout = 10;

    int success = 0;


    // THIS IS THE MAIN LOOP OF THE EXECUTION
    // PROBABLY NEED TO BE FACTORED OUT
    while (currentTime < contractTimeout) {
        prettyPrintWholeContractState(state, currentTime);
        currentTime++;

        if (state->currentContract == NULL) {
            printf("End of simulation because the contract is now NULL\n");
            exit(0);
        }

        switch (state->currentContract->type) {
            case PAY:
                // Parse the pay payload and obtain a dynamically allocated PayContract
                PayContract* payAction = parsePayPayload(state->currentContract->parameters);
                Transaction transaction = convertToTransaction(payAction);
                int res = makePayment(state, transaction, currentTime);
                if (res == 0) {
                    //state->currentContract = state->currentContract->continueAs;
                } else {
                    fprintf(stderr, "PAY action was not successful\n");
                    exit(1);
                }
                break;
            case CLOSE:
                if (strcmp(state->currentContract->parameters,"Success") == 0){
                    success = 1;
                }
                else {
                    success = 0;
                }
                state->currentContract = state->currentContract->continueAs;
                break;
            case DEPOSIT: {
                DepositContract depositPayload = parseDepositPayload(state->currentContract->parameters);
                Transaction depositTransaction = {
                    .source = depositPayload.depositor,
                    .destination = depositPayload.receiver,
                    .amount = depositPayload.amount,
                    .currency = depositPayload.currency
                };
                int res = makeDeposit(state, depositTransaction, depositPayload);
                break;
            }
            default:
                fprintf(stderr, "Error: Unsupported contract type\n");
                exit(1);
        }
    }
    


    // Those are various properties
    // Mainly to debug modeling
    __CPROVER_assert(success == 0, "Impossible to get a succesful contract");
    // Free allocated memory
    free(FailedContract);
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

    return 0;
}
