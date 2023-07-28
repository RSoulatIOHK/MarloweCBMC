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

typedef struct {
    CurrencyType currency;
    int amount;
} Token;

typedef struct {
    Token* tokens;
    int numTokens;
} Wallet;

typedef struct {
    PartyType partyType;
    const char* name;
    int id;
    Wallet wallet;
} Party;

typedef struct {
    int id;
    Wallet wallet;
} InternalAccount;

typedef struct {
    InternalAccount* accounts;
    int numAccounts;
} InternalWallet;

typedef struct {
    Party* source;
    Party* destination;
    int amount;
    CurrencyType currency;
} Transaction;

typedef struct {
    Party* payer;
    Party* receiver;
    int amount;
    CurrencyType currency;
} PayParameters;

typedef struct {
    Party* depositor;
    Party* receiver;
    int amount;
    CurrencyType currency;
    int timeout;
} DepositParameters;

typedef struct {
    const int id;
} CloseParameters;

typedef union {
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

typedef struct {
    Contract* currentContract;
    InternalWallet internalWallet;
    Party** parties;
    int numParties;
} ContractState;

Contract* newContract(ContractType type, ContractParameters params, Contract* subContractOK, Contract* continueAs);
void freeContract(Contract* contract);
Transaction convertToTransaction(const PayParameters* payParams);
Token* newTokenHolding(CurrencyType currency, int amount);
Wallet* newWallet(Token tokens[], int numTokens);
Party* newParty(const char* name, int id, Wallet* wallet);
InternalAccount* newInternalAccount(int id, Wallet wallet);
InternalWallet* newInternalWallet(InternalAccount accounts[], int numAccounts);
ContractState* newContractState(Contract* currentContract, InternalWallet* internalWallet, Party* parties[], int numParties);
const char* getCurrencyTypeName(CurrencyType currency);
const char* getPartyTypeName(const Party* party);
void prettyPrintPayContract(const PayParameters* payParams);
void prettyPrintDepositContract(const DepositParameters* depositParams);
void prettyPrintWholeContractState(const ContractState* state, int currentTime);
int makePayment(ContractState* state, const Transaction* candidateTransaction);
int makeDeposit(ContractState* state, const Transaction* candidateTransaction, const DepositParameters* depositPayload);
void processClose(ContractState* state);
int constr_non_det_int(int min, int max);
int getTotalAda(const ContractState* state);
int getTotalDollars(const ContractState* state);

int main(void)
{
    Token ada1 = {.currency = ADA, .amount = 0};
    Token dollar1 = {.currency = DOLLAR, .amount = 0};
    Token ada2 = {.currency = ADA, .amount = 0};
    Token dollar2 = {.currency = DOLLAR, .amount = 0};
    Token tokens1[] = {ada1, dollar1};
    Token tokens2[] = {ada2, dollar2};
    Wallet* wallet1 = newWallet(tokens1, NUMTOKENS);
    Wallet* wallet2 = newWallet(tokens2, NUMTOKENS);

    Party* dollarProvider = newParty("DollarProvider", 1, wallet2);
    Party* adaProvider = newParty("AdaProvider", 2, wallet1);

    InternalAccount accounts[] = {
        {1, *wallet1},
        {2, *wallet2}
    };
    InternalWallet* internalWallet = newInternalWallet(accounts, 2);

    Token ada3 = {.currency = ADA, .amount = constr_non_det_int(0, 50)};
    Token dollar3 = {.currency = DOLLAR, .amount = constr_non_det_int(0, 50)};
    Token ada4 = {.currency = ADA, .amount = constr_non_det_int(0, 50)};
    Token dollar4 = {.currency = DOLLAR, .amount = constr_non_det_int(0, 100)};
    Token tokens3[] = {ada3, dollar3};
    Token tokens4[] = {ada4, dollar4};
    Wallet* wallet3 = newWallet(tokens3, NUMTOKENS);
    Wallet* wallet4 = newWallet(tokens4, NUMTOKENS);

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

    Party* parties[] = {adaProvider, dollarProvider};
    ContractState* state = newContractState(whenDepositAdaProvider, internalWallet, parties, 2);

    int currentTime = 0;
    int contractTimeout = 20;
    int res_ret = 0;

    int initialTotalAda = getTotalAda(state);
    int initialTotalDollar = getTotalDollars(state);

    while (currentTime < contractTimeout && res_ret == 0)
    {
        currentTime++;

        if (state->currentContract == NULL)
        {
            printf("End of simulation because the contract is now NULL\n");
            break;
        }

        switch (state->currentContract->type)
        {
            case PAY: {
                Transaction transaction = convertToTransaction(&(state->currentContract->params.payParams));
                int res = makePayment(state, &transaction);
                if (res == 0)
                {
                    printf("Payment made successfully.\n");
                    if (state->currentContract->continueAs != NULL)
                    {
                        state->currentContract = state->currentContract->continueAs;
                        prettyPrintWholeContractState(state, currentTime);
                    }
                    else
                    {
                        printf("End of simulation because continueAs contract is NULL\n");
                        res_ret = 1;
                    }
                }
                else
                {
                    printf("Payment failed.\n");
                    res_ret = 1;
                }
                break;
            }
            case DEPOSIT: {
                Transaction transaction = convertToTransaction(&(state->currentContract->params.depositParams));
                const DepositParameters* depositPayload = &(state->currentContract->params.depositParams);
                res_ret = makeDeposit(state, &transaction, depositPayload);
                if (res_ret == 0)
                {
                    printf("Deposit made successfully.\n");
                    if (state->currentContract->subContractOK != NULL)
                    {
                        state->currentContract = state->currentContract->subContractOK;
                        prettyPrintWholeContractState(state, currentTime);
                    }
                    else
                    {
                        printf("End of simulation because subContractOK contract is NULL\n");
                        res_ret = 1;
                    }
                }
                else
                {
                    printf("Deposit failed.\n");
                    res_ret = 1;
                }
                break;
            }
            case CLOSE:
                processClose(state);
                printf("Closing the contract.\n");
                prettyPrintWholeContractState(state, currentTime);
                res_ret = 1;
                break;
            default:
                printf("Unknown contract type.\n");
                res_ret = 1;
                break;
        }
    }

    int finalTotalAda = getTotalAda(state);
    int finalTotalDollar = getTotalDollars(state);

    printf("Total ADA before simulation: %d\n", initialTotalAda);
    printf("Total ADA after simulation: %d\n", finalTotalAda);
    printf("Total Dollars before simulation: %d\n", initialTotalDollar);
    printf("Total Dollars after simulation: %d\n", finalTotalDollar);

    freeContract(payAdaProvider);
    freeContract(payDollarProvider);
    freeContract(whenDepositDollarProvider);
    freeContract(whenDepositAdaProvider);
    freeContract(successContract);
    freeContract(failedContract);
    freeContract(state->currentContract);
    free(state->internalWallet.accounts);
    free(state->internalWallet.accounts[0].wallet.tokens);
    free(state->internalWallet.accounts[1].wallet.tokens);
    free(state->internalWallet.accounts);
    free(state->parties[0]->wallet.tokens);
    free(state->parties[1]->wallet.tokens);
    free(state->parties[0]);
    free(state->parties[1]);
    free(state->parties);
    free(state);
    free(wallet1);
    free(wallet2);
    free(wallet3);
    free(wallet4);

    return res_ret;
}

Contract* newContract(ContractType type, ContractParameters params, Contract* subContractOK, Contract* continueAs)
{
    Contract* contract = malloc(sizeof(Contract));
    contract->type = type;

    // Copy the ContractParameters object using memcpy
    memcpy(&(contract->params), &params, sizeof(ContractParameters));

    contract->subContractOK = subContractOK;
    contract->continueAs = continueAs;
    return contract;
}



void freeContract(Contract* contract)
{
    if (contract != NULL)
    {
        free(contract);
    }
}

Transaction convertToTransaction(const PayParameters* payParams)
{
    Transaction transaction;
    transaction.source = payParams->payer;
    transaction.destination = payParams->receiver;
    transaction.amount = payParams->amount;
    transaction.currency = payParams->currency;
    return transaction;
}

Token* newTokenHolding(CurrencyType currency, int amount)
{
    Token* token = (Token*)malloc(sizeof(Token));
    token->currency = currency;
    token->amount = amount;
    return token;
}

Wallet* newWallet(Token tokens[], int numTokens)
{
    Wallet* wallet = (Wallet*)malloc(sizeof(Wallet));
    wallet->numTokens = numTokens;
    wallet->tokens = (Token*)malloc(numTokens * sizeof(Token));
    memcpy(wallet->tokens, tokens, numTokens * sizeof(Token));
    return wallet;
}

Party* newParty(const char* name, int id, Wallet* wallet)
{
    Party* party = (Party*)malloc(sizeof(Party));
    party->partyType = OTHER_PARTY;
    party->name = name;
    party->id = id;
    party->wallet = *wallet;
    return party;
}

InternalAccount* newInternalAccount(int id, Wallet wallet)
{
    InternalAccount* account = (InternalAccount*)malloc(sizeof(InternalAccount));
    account->id = id;
    account->wallet = wallet;
    return account;
}

InternalWallet* newInternalWallet(InternalAccount accounts[], int numAccounts)
{
    InternalWallet* internalWallet = (InternalWallet*)malloc(sizeof(InternalWallet));
    internalWallet->numAccounts = numAccounts;
    internalWallet->accounts = (InternalAccount*)malloc(numAccounts * sizeof(InternalAccount));
    memcpy(internalWallet->accounts, accounts, numAccounts * sizeof(InternalAccount));
    return internalWallet;
}

ContractState* newContractState(Contract* currentContract, InternalWallet* internalWallet, Party* parties[], int numParties)
{
    ContractState* state = (ContractState*)malloc(sizeof(ContractState));
    state->currentContract = currentContract;
    state->internalWallet = *internalWallet;
    state->numParties = numParties;
    state->parties = (Party**)malloc(numParties * sizeof(Party*));
    memcpy(state->parties, parties, numParties * sizeof(Party*));
    return state;
}

const char* getCurrencyTypeName(CurrencyType currency)
{
    switch (currency)
    {
        case ADA:
            return "ADA";
        case DOLLAR:
            return "DOLLAR";
        default:
            return "UNKNOWN";
    }
}

const char* getPartyTypeName(const Party* party)
{
    switch (party->partyType)
    {
        case ADAPROVIDER:
            return "AdaProvider";
        case DOLLARPROVIDER:
            return "DollarProvider";
        case ATTACKER:
            return "Attacker";
        default:
            return "UnknownParty";
    }
}

void prettyPrintPayContract(const PayParameters* payParams)
{
    printf("Pay contract:\n");
    printf("Payer: %s (id: %d)\n", payParams->payer->name, payParams->payer->id);
    printf("Receiver: %s (id: %d)\n", payParams->receiver->name, payParams->receiver->id);
    printf("Amount: %d %s\n", payParams->amount, getCurrencyTypeName(payParams->currency));
}

void prettyPrintDepositContract(const DepositParameters* depositParams)
{
    printf("Deposit contract:\n");
    printf("Depositor: %s (id: %d)\n", depositParams->depositor->name, depositParams->depositor->id);
    printf("Receiver: %s (id: %d)\n", depositParams->receiver->name, depositParams->receiver->id);
    printf("Amount: %d %s\n", depositParams->amount, getCurrencyTypeName(depositParams->currency));
    printf("Timeout: %d\n", depositParams->timeout);
}

void prettyPrintWholeContractState(const ContractState* state, int currentTime)
{
    printf("Contract state at time: %d\n", currentTime);
    if (state->currentContract != NULL)
    {
        switch (state->currentContract->type)
        {
            case PAY:
                prettyPrintPayContract(&(state->currentContract->params.payParams));
                break;
            case DEPOSIT:
                prettyPrintDepositContract(&(state->currentContract->params.depositParams));
                break;
            case CLOSE:
                printf("Close contract.\n");
                break;
            default:
                printf("Unknown contract type.\n");
                break;
        }
    }
    else
    {
        printf("NULL contract\n");
    }

    printf("Internal Wallet:\n");
    for (int i = 0; i < state->internalWallet.numAccounts; i++)
    {
        const InternalAccount* account = &(state->internalWallet.accounts[i]);
        printf("Account id: %d\n", account->id);
        printf("Account Wallet:\n");
        for (int j = 0; j < account->wallet.numTokens; j++)
        {
            const Token* token = &(account->wallet.tokens[j]);
            printf("%s: %d\n", getCurrencyTypeName(token->currency), token->amount);
        }
    }

    printf("Parties:\n");
    for (int i = 0; i < state->numParties; i++)
    {
        const Party* party = state->parties[i];
        printf("Party name: %s (id: %d)\n", party->name, party->id);
        printf("Party Wallet:\n");
        for (int j = 0; j < party->wallet.numTokens; j++)
        {
            const Token* token = &(party->wallet.tokens[j]);
            printf("%s: %d\n", getCurrencyTypeName(token->currency), token->amount);
        }
    }

    printf("\n");
}

int makePayment(ContractState* state, const Transaction* candidateTransaction)
{
    const Party* source = candidateTransaction->source;
    const Party* destination = candidateTransaction->destination;
    CurrencyType currency = candidateTransaction->currency;
    int amount = candidateTransaction->amount;

    if (amount <= 0)
    {
        printf("Invalid payment amount.\n");
        return 1;
    }

    if (source == NULL || destination == NULL)
    {
        printf("Invalid payment parties.\n");
        return 1;
    }

    Token* sourceToken = NULL;
    for (int i = 0; i < source->wallet.numTokens; i++)
    {
        if (source->wallet.tokens[i].currency == currency)
        {
            sourceToken = &(source->wallet.tokens[i]);
            break;
        }
    }

    if (sourceToken == NULL || sourceToken->amount < amount)
    {
        printf("Insufficient funds for payment.\n");
        return 1;
    }

    Token* destinationToken = NULL;
    for (int i = 0; i < destination->wallet.numTokens; i++)
    {
        if (destination->wallet.tokens[i].currency == currency)
        {
            destinationToken = &(destination->wallet.tokens[i]);
            break;
        }
    }

    if (destinationToken == NULL)
    {
        printf("Destination party does not hold the currency for payment.\n");
        return 1;
    }

    sourceToken->amount -= amount;
    destinationToken->amount += amount;

    return 0;
}

int makeDeposit(ContractState* state, const Transaction* candidateTransaction, const DepositParameters* depositPayload)
{
    const Party* depositor = depositPayload->depositor;
    const Party* receiver = depositPayload->receiver;
    CurrencyType currency = depositPayload->currency;
    int amount = depositPayload->amount;
    int timeout = depositPayload->timeout;

    if (amount <= 0)
    {
        printf("Invalid deposit amount.\n");
        return 1;
    }

    if (timeout <= 0)
    {
        printf("Invalid deposit timeout.\n");
        return 1;
    }

    if (depositor == NULL || receiver == NULL)
    {
        printf("Invalid deposit parties.\n");
        return 1;
    }

    Token* depositorToken = NULL;
    for (int i = 0; i < depositor->wallet.numTokens; i++)
    {
        if (depositor->wallet.tokens[i].currency == currency)
        {
            depositorToken = &(depositor->wallet.tokens[i]);
            break;
        }
    }

    if (depositorToken == NULL || depositorToken->amount < amount)
    {
        printf("Insufficient funds for deposit.\n");
        return 1;
    }

    Token* receiverToken = NULL;
    for (int i = 0; i < receiver->wallet.numTokens; i++)
    {
        if (receiver->wallet.tokens[i].currency == currency)
        {
            receiverToken = &(receiver->wallet.tokens[i]);
            break;
        }
    }

    if (receiverToken == NULL)
    {
        printf("Receiver party does not hold the currency for deposit.\n");
        return 1;
    }

    depositorToken->amount -= amount;
    receiverToken->amount += amount;

    printf("Waiting for deposit timeout...\n");
    while (timeout > 0)
    {
        printf("Timeout remaining: %d\n", timeout);
        timeout--;
    }

    return 0;
}

void processClose(ContractState* state)
{
    if (state != NULL)
    {
        Contract* currentContract = state->currentContract;
        freeContract(currentContract);
        state->currentContract = NULL;
    }
}

int constr_non_det_int(int min, int max)
{
    // Implement non-deterministic behavior here
    // In MISRA-C, non-deterministic behavior is not allowed
    // You should provide a deterministic alternative for your specific use case
    // For the sake of demonstration, this function will simply return the minimum value
    return min;
}

int getTotalAda(const ContractState* state)
{
    int totalAda = 0;
    for (int i = 0; i < state->internalWallet.numAccounts; i++)
    {
        const InternalAccount* account = &(state->internalWallet.accounts[i]);
        for (int j = 0; j < account->wallet.numTokens; j++)
        {
            const Token* token = &(account->wallet.tokens[j]);
            if (token->currency == ADA)
            {
                totalAda += token->amount;
            }
        }
    }
    return totalAda;
}

int getTotalDollars(const ContractState* state)
{
    int totalDollars = 0;
    for (int i = 0; i < state->internalWallet.numAccounts; i++)
    {
        const InternalAccount* account = &(state->internalWallet.accounts[i]);
        for (int j = 0; j < account->wallet.numTokens; j++)
        {
            const Token* token = &(account->wallet.tokens[j]);
            if (token->currency == DOLLAR)
            {
                totalDollars += token->amount;
            }
        }
    }
    return totalDollars;
}
