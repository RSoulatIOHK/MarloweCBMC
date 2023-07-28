#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>

// Careful not to have more inputs than MAX_INPUTS
// Careful not to have more outputs than MAX_OUTPUTS
// Result: segfaults

#define MAX_INPUTS 10
#define MAX_OUTPUTS 10
#define MAX_UTXOS 30
#define NUM_ACTORS 2
#define CONTRACT_ADDRESS 1337
// Structure to represent a token
// typedef struct {
//     int amount;
// } Token;

typedef struct {
    int originID;
    int amountToken1;
} Datum;

// Structure to represent an Unspent Transaction Output (UTxO)
typedef struct {
    int spent;
    int ownerID;
    bool isScript;
    Datum datum;
    int amount;
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
    int numTransactions;
} Ledger;

// Function to spend a UTxO and remove it from the ledger
void spendUTxO(Ledger* ledger, UTxO* utxo) {
    utxo->spent = 1;
}

// Function to add a UTxO to the ledger
void addUTxOToLedger(Ledger* ledger, UTxO* utxo) {
    ledger->unspentTransactions = realloc(ledger->unspentTransactions, (ledger->numTransactions + 1) * sizeof(UTxO*));
    ledger->unspentTransactions[ledger->numTransactions] = utxo;
    ledger->numTransactions++;
}

// Function to create a new UTxO
UTxO* createUTxO(int ownerID, int amount) {
    UTxO* utxo = malloc(sizeof(UTxO));
    utxo->spent = 0;  // UTxO is initially unspent
    utxo->ownerID = ownerID;
    utxo->isScript = false;
    utxo->amount = amount;
    utxo->datum.amountToken1 = amount;
    utxo->datum.originID = ownerID;
    return utxo;
}

void printUTxO(UTxO* utxo){
    printf("\033[1;34mUTxO ID:\033[1;0m\n");
    printf("Spent: %s\n", utxo->spent ? "\033[1;31mYes\033[1;0m" : "\033[1;32mNo\033[1;0m");
    printf("Owner ID: %d\n", utxo->ownerID);
    if (utxo->isScript){
        printf("\033[1;35mBelongs to a script\n");
        printf("Datum:\n");
        printf("  Origin ID: %d\n", utxo->datum.originID);
        printf("  Amount for: %d\033[1;0m\n", utxo->datum.amountToken1);
    }
    printf("Token:\n");
    printf(" - Token Amount: %d\n", utxo->amount);
    printf("\n");
}
bool checkValidator(UTxO** inputUTxOs, int numInputUTxOs, UTxO** outputUTxOs, int numOutputUTxOs){
    // For an input already in the script there is a correspoding output for the swap
    bool swapOK= true;
    for (int i = 0; i < numInputUTxOs; i++){
        if (inputUTxOs[i]->isScript && inputUTxOs[i]->ownerID == CONTRACT_ADDRESS){
            swapOK = false;
            // And that an output exist for the original ID
            for (int j = 0; j < numOutputUTxOs; j++){
                if ((outputUTxOs[j]->ownerID == inputUTxOs[i]->datum.originID && outputUTxOs[j]->amount == inputUTxOs[i]->datum.amountToken1)){
                    swapOK = true;
                    break;
                }
            }
        }
    }
    printf("Validator has evaluated to ");
    if (swapOK){
        printf(" OK!\n");
        }
    else{
        printf("KO :(\n");
    }
    return swapOK;
}

int createTransferTransaction(Ledger* ledger, int senderID, UTxO** inputUTxOs, int numInputUTxOs, UTxO** outputUTxOs, int numOutputUTxOs) {
    // Check that all input UTxOs belong to the sender or to the contract
    bool useScriptAddress = false;
    int debug_int = 0;
    printf("=======================================\n");
    printf("DEBUG: senderID = %d\n", senderID);
    // Printing the Inputs
    printf("  Declared %d input transactions\n", numInputUTxOs);
    for (int i = 0; i < numInputUTxOs; i++) {
        printf("UTxO %d\n",i);
        printUTxO(inputUTxOs[i]);
    }
    printf("\n");

    // Printing the Inputs
    printf("  Declared %d output transactions\n", numOutputUTxOs);
    for (int i = 0; i < numOutputUTxOs; i++) {
        printf("UTxO %d\n",i);
        printUTxO(outputUTxOs[i]);
    }
    printf("=======================================\n");

    for (int i = 0; i < numInputUTxOs; i++) {
        // printf("DEBUG: %d.%d\n", i, numInputUTxOs);
        if (inputUTxOs[i] == NULL){printf("WHAT ARE YOU DOING?\n");}
        if (inputUTxOs[i]->ownerID != senderID && inputUTxOs[i]->ownerID != CONTRACT_ADDRESS) {
            printf("Error: Input UTxO %d does not belong to sender %d\n", i, senderID);
            printf("DEBUG ID%d:\n",i);
            printUTxO(inputUTxOs[i]);
            printUTxO(inputUTxOs[i]);
            return -1;
        }
        else if (inputUTxOs[i]->ownerID == CONTRACT_ADDRESS){
            // printf("DEBUG in loop for: %d\n", debug_int);
            // debug_int++;
            useScriptAddress = true;
        }
    }
    debug_int++;
    // printf("DEBUG: %d\n", debug_int);
    // debug_int++;
    // Compute tokenAmount from the UTxOs outputs
    int tokenAmount = 0;
    for (int i = 0; i < numOutputUTxOs; i++){
        tokenAmount += outputUTxOs[i]->amount;
    }

    // Compute the total balance for each token from the input UTxOs
    int tokenBalance = 0;
    for (int i = 0; i < numInputUTxOs; i++) {
        UTxO* utxo = inputUTxOs[i];
        tokenBalance += utxo->amount;
    }

    // Check if there are sufficient funds for each token
    if (tokenBalance < tokenAmount) {
        printf("Error: Insufficient funds for token\n");
        return -1;
    }
    // printf("DEBUG: %d\n", debug_int);
    // debug_int++;

    // Check if the spending of the script UTXO is authorized by the contract

    if (useScriptAddress){
        printf("Script %d has been used, checking validator\n", CONTRACT_ADDRESS);
        if (!checkValidator(inputUTxOs, numInputUTxOs, outputUTxOs, numOutputUTxOs)){
            printf("\033[1;31mError: Script validator returned false\033[1;0m\n");
            return -1;
        }  
    } 

    // printf("DEBUG: %d\n", debug_int);
    // debug_int++;

    // Spend the input UTxOs
    for (int i = 0; i < numInputUTxOs; i++) {
        spendUTxO(ledger, inputUTxOs[i]);
    }

    // Add the output UTxOs to the ledger
    for (int i = 0; i < numOutputUTxOs; i++){
        addUTxOToLedger(ledger, outputUTxOs[i]);
    }

    // Create a new UTxO for the rest of the tokens
    int unspentToken = tokenBalance - tokenAmount;

    UTxO* backUTxO = createUTxO(senderID, unspentToken);
    // printf("DEBUG: %d\n", debug_int);
    // debug_int++;

    addUTxOToLedger(ledger, backUTxO);

    // Pretty print the transaction details
    printf("=== Transaction Details ===\n");
    printf("Sender ID: %d\n", senderID);
    for (int i = 0; i < numOutputUTxOs; i++){
        printf("Receiver ID: %d\n", outputUTxOs[i]->ownerID);
        printf("Token Amounts:\n");
        printf("Token: %d\n", outputUTxOs[i]->amount);
    }
    printf("===========================\n");

    return ledger->numTransactions;

}


// Function to create a new ledger
Ledger* createLedger() {
    Ledger* ledger = malloc(sizeof(Ledger));
    ledger->unspentTransactions = NULL;
    ledger->numTransactions = 0;
    return ledger;
}

// Function to print the state of the ledger
void printLedgerState(Ledger* ledger) {
    printf("\033[1;36m=== Ledger State ===\033[1;0m\n");

    for (int i = 0; i < ledger->numTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        printUTxO(utxo);
    }

    printf("\033[1;36m====================\033[1;0m\n\n");
}


int computeTokenAmounts(Ledger* ledger) {
    int numTokens = 2; //TODO: more general
    // Create an array to store the token amounts
    int tokenAmount = 0;

    // Iterate over the unspent transactions in the ledger
    for (int i = 0; i < ledger->numTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];


        // Accumulate the token amount
        if (utxo->spent == 0){
            tokenAmount += utxo->amount;    
        }  
    }

    return tokenAmount;
}

bool isValid_TransferTransaction(Ledger* ledger, int senderID, UTxO** inputUTxOs, int numInputUTxOs, int tokenAmount, int receiverID) {
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

    int tokenBalance = 0;
    for (int i = 0; i < numInputUTxOs; i++) {
        UTxO* utxo = inputUTxOs[i];
        tokenBalance += utxo->amount;
    }

    // Check if there are sufficient funds for each token
    if (tokenBalance < tokenAmount) {
        enoughFunds = false;
    }
    return inputsBelongtoSender && enoughFunds;
}

UTxO** getUnspentTransactionsByID(Ledger* ledger, int ownerID, int* numTransactions) {
    int count = 0;
    for (int i = 0; i < ledger->numTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        // if ((utxo->ownerID == ownerID || utxo->isScript) && utxo->spent == 0) {
        if (utxo->ownerID == ownerID && utxo->spent == 0){
            count++;
        }
    }

    UTxO** unspentTransactions = malloc(count * sizeof(UTxO*));
    if (unspentTransactions == NULL) {
        *numTransactions = 0;
        return NULL;
    }

    int index = 0;
    for (int i = 0; i < ledger->numTransactions; i++) {
        UTxO* utxo = ledger->unspentTransactions[i];
        // if ((utxo->ownerID == ownerID || utxo->isScript) && utxo->spent == 0) {
        if (utxo->ownerID == ownerID && utxo->spent == 0){
            unspentTransactions[index] = utxo;
            index++;
        }
    }

    *numTransactions = count;
    return unspentTransactions;
}

void initializeActors(Ledger* ledger, int numActors, int initialTokenAmount) {
    for (int i = 1; i <= numActors; i++) {
        // Create UTxO for each actor
        UTxO* utxo = createUTxO(i, initialTokenAmount);
        // Add UTxO to the ledger
        addUTxOToLedger(ledger, utxo);
    }
}

int initiateSwap(Ledger* ledger, int initiatorID, int tokenAmount) {
    // List all the inputs the initiator can have
    UTxO* utxosToSpend[MAX_INPUTS];
    int numTransactions = 0;

    UTxO** ptrToUtxos = getUnspentTransactionsByID(ledger, initiatorID, &numTransactions);

    for (int i = 0; i < MAX_INPUTS && i < numTransactions; i++) {
        utxosToSpend[i] = ptrToUtxos[i];
    }

    // Build the outputs the initiator wants
    UTxO* outputUTxO = malloc(sizeof(UTxO));
    outputUTxO->spent = 0;
    outputUTxO->ownerID = CONTRACT_ADDRESS;
    outputUTxO->isScript = true;
    outputUTxO->datum.amountToken1 = tokenAmount;
    outputUTxO->datum.originID = initiatorID;
    outputUTxO->amount = tokenAmount;

    UTxO* outputUtxos[1];
    outputUtxos[0] = outputUTxO;

    // Create the transfer transaction and return the ID
    // MASSIVE SIDE EFFECT IN THIS CALL
    int swap_ID = createTransferTransaction(ledger, initiatorID, utxosToSpend, numTransactions, outputUtxos, 1);
    
    return swap_ID;
}

void addInputUTxO(Transaction* transaction, UTxO* inputUTxO) {
    if (transaction->numInputs < MAX_INPUTS) {
        transaction->inputs[transaction->numInputs] = inputUTxO;
        transaction->numInputs++;
    }
}

void addOutputUTxO(Transaction* transaction, int ownerID, int amount){
    if (transaction->numOutputs < MAX_INPUTS) {
        UTxO* outputUTxO = createUTxO(ownerID, amount);
        transaction->outputs[transaction->numOutputs] = outputUTxO;
        transaction->numOutputs++;
    }
}

void initTransaction(Transaction* transaction, int signerID) {
    transaction->numInputs = 0;
    transaction->numOutputs = 0;
    transaction->signerID = signerID;

    // Allocate memory for inputs array
    transaction->inputs = malloc(MAX_INPUTS * sizeof(UTxO*));
    for (int i = 0; i < MAX_INPUTS; i++) {
        transaction->inputs[i] = NULL;
    }

    // Allocate memory for outputs array
    transaction->outputs = malloc(MAX_INPUTS * sizeof(UTxO*));
    for (int i = 0; i < MAX_INPUTS; i++) {
        transaction->outputs[i] = NULL;
    }
}

int main() {
    // Create a ledger
    Ledger* ledger = createLedger();
    int tokenAmounts = 10;
    initializeActors(ledger, NUM_ACTORS, 100);
    printLedgerState(ledger);

    int startAmount = computeTokenAmounts(ledger);

    // A initiates the 1st swap
    int A_swap_ID = initiateSwap(ledger, 1, tokenAmounts);

    // A initiates the 2nd swap
    int A_swap_ID_2 = initiateSwap(ledger, 1, tokenAmounts);
    printLedgerState(ledger);



    // B tries to take the swap
    // B list all the inputs he can have
    Transaction transactionB;
    initTransaction(&transactionB, 2); // Passing the address of transactionB and the signerID (2 in this case)

    int numTransactionsB = 0;
    printf("DEBUG\n");
    UTxO** ptrToUtxosB = getUnspentTransactionsByID(ledger, transactionB.signerID, &numTransactionsB);

    for (int i = 0; i < numTransactionsB; i++) {
        printf("Sub debug\n");
        addInputUTxO(&transactionB, ptrToUtxosB[i]);
        printf("End Sub debug\n");
    }
    printf("DEBUG\n");
    // B adds the swap he wants to conclude
    addInputUTxO(&transactionB, ledger->unspentTransactions[A_swap_ID - 2]);

    // B adds the second swap he wants to conclude
    addInputUTxO(&transactionB, ledger->unspentTransactions[A_swap_ID_2 - 2]);
    printf("DEBUG\n");
    // B writes the outputs
    addOutputUTxO(&transactionB, 1, tokenAmounts); // A gets its money back
    addOutputUTxO(&transactionB, 2, tokenAmounts); // B also gets its money back
    addOutputUTxO(&transactionB, 2, tokenAmounts); // B also gets its money back (second time)
    printf("DEBUG\n");
    // Execute the transaction for B
    createTransferTransaction(ledger, 2, transactionB.inputs, transactionB.numInputs, transactionB.outputs, transactionB.numOutputs);

    int newAmount = computeTokenAmounts(ledger);
    printf("DEBUG\n");
    if (startAmount != newAmount) {
        printf("Assertion failed: Token amount mismatch: start: %d vs new: %d\n", startAmount, newAmount);
    }
    // Spend UTxO utxo1
    printLedgerState(ledger);

    // Free the array of UTxO pointers
    free(ledger->unspentTransactions);

    // Free the ledger
    free(ledger);

    return 0;
}

