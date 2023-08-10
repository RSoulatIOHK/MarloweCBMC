#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>

#define MAX_INPUTS 3
#define MAX_OUTPUTS 3
#define MAX_UTXOS 100
#define MAX_TOKENS 1

// Structure to represent a token
typedef struct {
    int amount;
} Token;

// Structure to represent an Unspent Transaction Output (UTxO)
typedef struct {
    int spent;
    int ownerID;
    bool isScript;
    Token* tokens[MAX_TOKENS];
} UTxO;

// Structure to represent a transaction
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

// Function to create a new token
Token* createToken(int amount) {
    Token* token = malloc(sizeof(Token));
    token->amount = amount;
    return token;
}

// Function to spend a UTxO and remove it from the ledger
void spendUTxO(Ledger* ledger, UTxO* utxo) {
    utxo->spent = 1;
}

// Function to add a UTxO to the ledger
void addUTxOToLedger(Ledger* ledger, UTxO* utxo) {
    ledger->unspentTransactions[ledger->numUnspentTransactions] = utxo;
    ledger->numUnspentTransactions++;
}

// Function to create a new UTxO
UTxO* createUTxO(int ownerID, Token* tokens[MAX_TOKENS]) {
    UTxO* utxo = malloc(sizeof(UTxO));
    utxo->spent = 0;  // UTxO is initially unspent
    utxo->ownerID = ownerID;
    utxo->isScript = false;
    for (int i = 0; i < MAX_TOKENS; i++) {
        utxo->tokens[i] = tokens[i];
    }
    return utxo;
}

// Function to create a transaction that transfers tokens from one owner to another
void createTransferTransaction(Ledger* ledger, int senderID, UTxO* inputUTxOs[MAX_INPUTS], int numInputUTxOs, int tokenAmounts[MAX_TOKENS], int receiverID) {
    int numTokens = MAX_TOKENS;
    bool useScriptUTxO = false;;
    int scriptID = -1;

    // Check that all input UTxOs belong to the sender or are part of a script
    for (int i = 0; i < numInputUTxOs; i++) {
        if (inputUTxOs[i]->ownerID != senderID && !(inputUTxOs[i]->isScript)) {
            printf("Error: Input UTxO %d does not belong to sender %d\n", i, senderID);
            return;
        }
        if (inputUTxOs[i]->isScript){
            useScriptUTxO = true;
            if (scriptID == -1){
                scriptID = inputUTxOs[i]->ownerID;
            }
            else {
                if (inputUTxOs[i]->ownerID != scriptID){
                    printf("Error: Multiple Scripts used, unsupported yet.\n I just want to do a swap example :'(\n");
                    return;
                }
            }
        }
    }

    // Check that all inputs are unspent
    for (int i = 0; i < numInputUTxOs; i++) {
        if (inputUTxOs[i]->spent) {
            return;
        }
    }

    // Compute the total balance for each token from the input UTxOs
    int tokenBalances[MAX_TOKENS] = {0};
    for (int i = 0; i < numInputUTxOs; i++) {
        UTxO* utxo = inputUTxOs[i];
        for (int j = 0; j < MAX_TOKENS; j++) {
            Token* token = utxo->tokens[j];
            tokenBalances[j] += token->amount;
        }
    }

    // If there is at least a script, then validate the transaction using this script
    if (useScriptUTxO){
        // Validate, here a swap for equal value ada

    }


    // Check if there are sufficient funds for each token
    for (int i = 0; i < numTokens; i++) {
        if (tokenBalances[i] < tokenAmounts[i]) {
            printf("Error: Insufficient funds for token %d\n", i);
            return;
        }
    }

    // If useScriptUTxO is true, you need to check if you can sped 


    // Spend the input UTxOs
    for (int i = 0; i < numInputUTxOs; i++) {
        spendUTxO(ledger, inputUTxOs[i]);
    }

    // Create a new UTxO for the token transfer
    Token* transferTokens[MAX_TOKENS];
    for (int i = 0; i < numTokens; i++) {
        transferTokens[i] = createToken(tokenAmounts[i]);
    }
    UTxO* transferUTxO = createUTxO(receiverID, transferTokens);

    // Add the transfer UTxO to the ledger
    addUTxOToLedger(ledger, transferUTxO);

    // Create a new UTxO for the rest of the tokens
    Token* unspentTokens[MAX_TOKENS];
    for (int i = 0; i < numTokens; i++) {
        unspentTokens[i] = createToken(tokenBalances[i] - tokenAmounts[i]);
    }
    UTxO* backUTxO = createUTxO(senderID, unspentTokens);

    addUTxOToLedger(ledger, backUTxO);

    // Clean up memory
    // Token deallocation is handled by UTxO deallocation
}

// Function to create a new ledger
Ledger* createLedger() {
    Ledger* ledger = malloc(sizeof(Ledger));
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

        for (int j = 0; j < MAX_TOKENS; j++) {
            Token* token = utxo->tokens[j];
            printf(" - Token ID: %d, Amount: %d\n", j, token->amount);
        }

        printf("\n");
    }

    printf("===================\n");
}

int* computeTokenAmounts(Ledger* ledger) {
    int numTokens = MAX_TOKENS;
    // Create an array to store the token amounts
    int* tokenAmounts = calloc(numTokens, sizeof(int));

    // Iterate over the unspent transactions in the ledger
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];

        // Iterate over the tokens in the UTxO
        for (int j = 0; j < MAX_TOKENS; j++) {
            Token* token = utxo->tokens[j];

            // Accumulate the token amount
            tokenAmounts[j] += token->amount;
        }
    }

    return tokenAmounts;
}

UTxO** getUnspentTransactionsByID(Ledger* ledger, int ownerID, int* numTransactions) {
    // Count the number of unspent transactions belonging to the specified ID
    int count = 0;
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        if ((utxo->ownerID == ownerID || utxo->isScript) && utxo->spent == 0) {
            count++;
        }
    }

    // Allocate memory for the array of unspent transactions
    UTxO** unspentTransactions = malloc(count * sizeof(UTxO*));
    if (unspentTransactions == NULL) {
        // Failed to allocate memory
        *numTransactions = 0;
        return NULL;
    }

    // Populate the array with the unspent transactions
    int index = 0;
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        if (utxo->ownerID == ownerID && utxo->spent == 0) {
            unspentTransactions[index] = utxo;
            index++;
        }
    }

    // Update the number of transactions and return the array
    *numTransactions = count;
    return unspentTransactions;
}

// Bunch of CBMC nondet functions
int constr_nondet_int(int min, int max){
    int res_ret;
    __CPROVER_assume(min <= res_ret && res_ret <= max);
    return res_ret;
}

// Bunch of isValid for CBMC assumes
// isValid transaction returns true if there are enough funds in the UTxOs
// and if all UTxOs belong to the sender

bool isValid_TransferTransaction(Ledger* ledger, int senderID, UTxO* inputUTxOs[MAX_INPUTS], int numInputUTxOs, int tokenAmounts[MAX_TOKENS], int receiverID) {
    int numTokens = MAX_TOKENS;

    bool tokenAmountPositive = true;
    for (int i = 0; i < numTokens; i++){
        if (tokenAmounts[i] < 0){
            tokenAmountPositive = false;
        }
    }

    // All inputs belong to Sender
    bool inputsBelongtoSender = true;
    for (int i = 0; i < numInputUTxOs; i++) {
        if (inputUTxOs[i]->ownerID != senderID) {
            inputsBelongtoSender = false;
        }
    }

    // All inputs belong to Sender
    bool allUnspent = true;
    for (int i = 0; i < numInputUTxOs; i++) {
        if (inputUTxOs[i]->spent) {
            allUnspent = false;
        }
    }

    // Enough funds for transaction
    bool enoughFunds = true;

    int tokenBalances[MAX_TOKENS] = {0};
    for (int i = 0; i < numInputUTxOs; i++) {
        UTxO* utxo = inputUTxOs[i];
        for (int j = 0; j < MAX_TOKENS; j++) {
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
    return (tokenAmountPositive && allUnspent && inputsBelongtoSender && enoughFunds);
}

int main() {
    // Create a ledger
    Ledger* ledger = createLedger();

    // Generate a non-deterministic amount of UTxOs
    int numUTxOs = 5;

    // Initialize the UTxOs with non-deterministic token amounts
    for (int i = 0; i < numUTxOs; i++) {
        // Generate non-deterministic token amounts
        int tokenAmount1 = constr_nondet_int(1, 100);
        //int tokenAmount2 = constr_nondet_int(1, 100);

        // Create tokens
        Token* token1 = createToken(tokenAmount1);
        //Token* token2 = createToken(tokenAmount2);

        // Create UTxO
        int ownerID = constr_nondet_int(1, 2); // Non-deterministic owner ID
        Token* tokens[MAX_TOKENS] = {token1};
        UTxO* utxo = createUTxO(ownerID, tokens);

        // Add the UTxO to the ledger
        addUTxOToLedger(ledger, utxo);
    }

    // User 1 create a few 10 Ada swap contracts
    
    // Print the state of the ledger
    printLedgerState(ledger);

    int* startAmounts = computeTokenAmounts(ledger);

    // Transfer some tokens
    int tokenAmounts[MAX_TOKENS] = {constr_nondet_int(10, 30)};
    int numTransactions;
    int sender = constr_nondet_int(1, 2);
    int receiver = constr_nondet_int(1, 2);

    UTxO* utxosToSpend[MAX_INPUTS];
    UTxO** ptrToUtxos = getUnspentTransactionsByID(ledger, sender, &numTransactions);
    for (int i = 0; i < numTransactions; i++) {
        utxosToSpend[i] = ptrToUtxos[i];
    }
    free(ptrToUtxos);

    __CPROVER_assume(isValid_TransferTransaction(ledger, sender, utxosToSpend, numTransactions, tokenAmounts, receiver));
    createTransferTransaction(ledger, sender, utxosToSpend, numTransactions, tokenAmounts, receiver);

    int* newAmounts = computeTokenAmounts(ledger);

    bool sameAmount = true;
    for (int i = 0; i < MAX_TOKENS; i++) {
        if (!(startAmounts[i] == newAmounts[i])) {
            sameAmount = false;
        }
    }

    __CPROVER_assert(sameAmount, "sameAmount");

    // Spend UTxO utxo1
    printLedgerState(ledger);

    // Clean up memory
    for (int i = 0; i < ledger->numUnspentTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        for (int j = 0; j < MAX_TOKENS; j++) {
            free(utxo->tokens[j]);
        }
        free(utxo);
    }
    free(ledger);

    return 0;
}