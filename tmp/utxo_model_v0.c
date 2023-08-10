#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <time.h>

#define MAX_INPUTS 3
#define MAX_OUTPUTS 3
#define MAX_UTXOS 30

// Structure to represent a token
typedef struct {
    int amount;
    UTxO* utxo; // Add a reference to the UTxO that the token belongs to
} Token;

typedef struct {
    int amountToken1;
    int amountToken2;
} Datum;

// Structure to represent an Unspent Transaction Output (UTxO)
typedef struct {
    int spent;
    int ownerID;
    bool isScript;
    Datum datum;
    Token** tokens;
    int numTokens;
} UTxO;

// Structure to represent a transaction
typedef struct {
    UTxO** inputs;
    int numInputs;
    UTxO** outputs;
    int numOutputs;
    int signerID;
} Transaction;

// Structure to represent the ledger
typedef struct {
    UTxO** unspentTransactions;
    int numUnspentTransactions;
} Ledger;

// Function to create a new token
Token* createToken(int amount, UTxO* utxo) {
    Token* token = malloc(sizeof(Token));
    token->amount = amount;
    token->utxo = utxo; // Set the UTxO that the token belongs to
    return token;
}

// Function to spend a UTxO and remove it from the ledger
void spendUTxO(Ledger* ledger, UTxO* utxo) {
    utxo->spent = 1;
}

// Function to add a UTxO to the ledger
void addUTxOToLedger(Ledger* ledger, UTxO* utxo) {
    ledger->unspentTransactions = realloc(ledger->unspentTransactions, (ledger->numUnspentTransactions + 1) * sizeof(UTxO*));
    ledger->unspentTransactions[ledger->numUnspentTransactions] = utxo;
    ledger->numUnspentTransactions++;
}

// Function to create a new UTxO
UTxO* createUTxO(int ownerID, Token** tokens, int numTokens) {
    UTxO* utxo = malloc(sizeof(UTxO));
    utxo->spent = 0;  // UTxO is initially unspent
    utxo->ownerID = ownerID;
    utxo->tokens = tokens;
    utxo->numTokens = numTokens;
    utxo->isScript = false;
    utxo->datum.amountToken1 = 0;
    utxo->datum.amountToken2 = 0;

    // Update the tokens to reference the UTxO
    for (int i = 0; i < numTokens; i++) {
        tokens[i]->utxo = utxo;
    }

    return utxo;
}

void createTransferTransaction(Ledger* ledger, int senderID, UTxO** inputUTxOs, int numInputUTxOs, int* tokenAmounts, int receiverID) {
    int numTokens = 2; // TODO: More general, this is just to go through CBMC right now.

    // Check that all input UTxOs belong to the sender
    for (int i = 0; i < numInputUTxOs; i++) {
        if (inputUTxOs[i]->ownerID != senderID) {
            printf("Error: Input UTxO %d does not belong to sender %d\n", i, senderID);
            return;
        }
    }

    // Compute the total balance for each token from the input UTxOs
    int* tokenBalances = calloc(numTokens, sizeof(int));
    for (int i = 0; i < numInputUTxOs; i++) {
        UTxO* utxo = inputUTxOs[i];
        for (int j = 0; j < utxo->numTokens; j++) {
            Token* token = utxo->tokens[j];
            tokenBalances[j] += token->amount;
        }
    }

    // Check if there are sufficient funds for each token
    for (int i = 0; i < numTokens; i++) {
        if (tokenBalances[i] < tokenAmounts[i]) {
            printf("Error: Insufficient funds for token %d\n", i);
            free(tokenBalances);
            return;
        }
    }

    // Spend the input UTxOs
    for (int i = 0; i < numInputUTxOs; i++) {
        spendUTxO(ledger, inputUTxOs[i]);
    }

    // Create a new UTxO for the token transfer
    Token** transferTokens = malloc(numTokens * sizeof(Token*));
    if (transferTokens == NULL) {
        printf("Error: Failed to allocate memory for transfer tokens\n");
        free(tokenBalances);
        return;
    }
    for (int i = 0; i < numTokens; i++) {
        transferTokens[i] = createToken(tokenAmounts[i]);
    }
    UTxO* transferUTxO = createUTxO(receiverID, transferTokens, numTokens);

    // Add the transfer UTxO to the ledger
    addUTxOToLedger(ledger, transferUTxO);

    // Create a new UTxO for the rest of the tokens
    Token** unspentTokens = malloc(numTokens * sizeof(Token*));
    if (unspentTokens == NULL) {
        printf("Error: Failed to allocate memory for unspent tokens\n");
        free(tokenBalances);
        free(transferTokens);
        return;
    }
    for (int i = 0; i < numTokens; i++) {
        unspentTokens[i] = createToken(tokenBalances[i] - tokenAmounts[i]);
    }
    UTxO* backUTxO = createUTxO(senderID, unspentTokens, numTokens);

    addUTxOToLedger(ledger, backUTxO);

    // Pretty print the transaction details
    printf("=== Transaction Details ===\n");
    printf("Sender ID: %d\n", senderID);
    printf("Receiver ID: %d\n", receiverID);
    printf("Token Amounts:\n");
    for (int i = 0; i < numTokens; i++) {
        printf("Token %d: %d\n", i, tokenAmounts[i]);
    }
    printf("===========================\n");

    // Clean up memory
    free(tokenBalances);
}


// Function to create a new ledger
Ledger* createLedger() {
    Ledger* ledger = malloc(sizeof(Ledger));
    ledger->unspentTransactions = NULL;
    ledger->numUnspentTransactions = 0;
    return ledger;
}

// Function to print the state of the ledger
void printLedgerState(Ledger* ledger) {
    printf("=== Ledger State ===\n");

    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];

        printf("UTxO ID: %d\n", i);
        printf("Spent: %s\n", utxo->spent ? "Yes" : "No");
        printf("Owner ID: %d\n", utxo->ownerID);
        printf("Tokens:\n");

        for (int j = 0; j < utxo->numTokens; j++) {
            Token* token = utxo->tokens[j];
            printf(" - Token ID: %d, Amount: %d\n", j, token->amount);
        }

        printf("\n");
    }

    printf("===================\n");
}

int* computeTokenAmounts(Ledger* ledger) {
    int numTokens = 2; //TODO: more general
    // Create an array to store the token amounts
    int* tokenAmounts = calloc(numTokens, sizeof(int)); // Assuming MAX_TOKENS is the maximum number of tokens

    // Iterate over the unspent transactions in the ledger
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];

        // Iterate over the tokens in the UTxO
        for (int j = 0; j < 2; j++) {
            Token* token = utxo->tokens[j];

            // Accumulate the token amount
            tokenAmounts[j] += token->amount;
        }
    }

    return tokenAmounts;
}

bool isValid_TransferTransaction(Ledger* ledger, int senderID, UTxO** inputUTxOs, int numInputUTxOs, int* tokenAmounts, int receiverID) {
    int numTokens = 2; // TODO: More general, this is just to go through CBMC right now.

    // All inputs belong to Sender
    bool inputsBelongtoSender = true;
    for (int i = 0; i < numInputUTxOs; i++) {
        if (inputUTxOs[i]->ownerID != senderID) {
            inputsBelongtoSender = false;
        }
    }


    // Enough funds for transaction
    bool enoughFunds = true;

    int* tokenBalances = calloc(numTokens, sizeof(int));
    for (int i = 0; i < numInputUTxOs; i++) {
        UTxO* utxo = inputUTxOs[i];
        for (int j = 0; j < utxo->numTokens; j++) {
            Token* token = utxo->tokens[j];
            tokenBalances[j] += token->amount;
        }
    }

    // Check if there are sufficient funds for each token
    for (int i = 0; i < numTokens; i++) {
        if (tokenBalances[i] < tokenAmounts[i]) {
            enoughFunds = false;
        }
    }
    return inputsBelongtoSender && enoughFunds;
}

UTxO** getUnspentTransactionsByID(Ledger* ledger, int ownerID, int* numTransactions) {
    int count = 0;
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        if ((utxo->ownerID == ownerID || utxo->isScript) && utxo->spent == 0) {
            count++;
        }
    }

    UTxO** unspentTransactions = malloc(count * sizeof(UTxO*));
    if (unspentTransactions == NULL) {
        *numTransactions = 0;
        return NULL;
    }

    int index = 0;
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        if ((utxo->ownerID == ownerID || utxo->isScript) && utxo->spent == 0) {
            unspentTransactions[index] = utxo;
            index++;
        }
    }

    *numTransactions = count;
    return unspentTransactions;
}


int main() {
    // True RNG and not fixed RNG
    unsigned int seed = (unsigned int)time(NULL);
    srand(seed);

    // Create a ledger
    Ledger* ledger = createLedger();

    // Generate a non-deterministic amount of UTxOs
    int numUTxOs = 5;

    // Ensure that the number of UTxOs is within a valid range
    if (numUTxOs < 0 || numUTxOs > MAX_UTXOS) {
        printf("Error: Invalid number of UTxOs\n");
        return 1;
    }

    // Initialize the UTxOs with non-deterministic token amounts
    for (int i = 0; i < numUTxOs; i++) {
        // Generate non-deterministic token amounts
        int tokenAmount1 = rand() % 100;
        int tokenAmount2 = rand() % 100;

        // Create tokens
        Token* token1 = createToken(tokenAmount1);
        Token* token2 = createToken(tokenAmount2);

        // Create UTxO
        int ownerID = rand() % 2; // Non-deterministic owner ID
        Token** tokens = malloc(2 * sizeof(Token*));
        tokens[0] = token1;
        tokens[1] = token2;
        UTxO* utxo = createUTxO(ownerID, tokens, 2);

        // Add the UTxO to the ledger
        addUTxOToLedger(ledger, utxo);
    }

    // Print the state of the ledger
    printLedgerState(ledger);

    int* startAmounts = computeTokenAmounts(ledger);

    // Transfer some tokens
    int tokenAmounts[] = { 50, 30 };
    UTxO* utxosToSpend[MAX_INPUTS];
    int numTransactions = 0;
    UTxO** ptrToUtxos = getUnspentTransactionsByID(ledger, 1, &numTransactions);

    for (int i = 0; i < MAX_INPUTS && i < numTransactions; i++) {
        utxosToSpend[i] = ptrToUtxos[i];
    }
    createTransferTransaction(ledger, 1, utxosToSpend, numTransactions, tokenAmounts, 2);

    int* newAmounts = computeTokenAmounts(ledger);

    for (int i = 0; i < 2; i++) {
        if (startAmounts[i] != newAmounts[i]) {
            printf("Assertion failed: Token amount mismatch\n");
            break;
        }
    }

    // Spend UTxO utxo1
    printLedgerState(ledger);

    // Clean up memory
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        for (int j = 0; j < utxo->numTokens; j++) {
            free(utxo->tokens[j]);
        }
        free(utxo->tokens);
        free(utxo);
    }
    free(ledger->unspentTransactions);
    free(ledger);

    return 0;
}