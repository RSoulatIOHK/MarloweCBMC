#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "jansson.h"

typedef struct {
    int id;
} CloseParams;

typedef struct {
    char* id;
    char* role;
} ChoiceParams;

typedef struct {
    char* caseId;
    char* role;
} CaseParams;

typedef struct {
    char* depositor;
    char* receiver;
    char* amount;
    char* currency;
    int timeout;
} DepositParams;

typedef struct {
    char* payer;
    char* receiver;
    char* amount;
    char* currency;
} PayParams;

typedef struct {
    char* timeout;
    struct Contract* contract;
} WhenParams;

typedef struct {
    struct Contract* contract;
    struct Contract* continuation;
} CaseParams;

typedef struct Contract {
    enum {
        CLOSE,
        CHOICE,
        DEPOSIT,
        PAY,
        WHEN,
        CASE,
    } tag;
    union {
        CloseParams closeParams;
        ChoiceParams choiceParams;
        DepositParams depositParams;
        PayParams payParams;
        WhenParams whenParams;
        CaseParams caseParams;
    };
    struct Contract* continuation;
} Contract;

// Helper function to create a new contract with CLOSE tag
Contract* newCloseContract(int id) {
    Contract* contract = malloc(sizeof(Contract));
    contract->tag = CLOSE;
    contract->closeParams.id = id;
    contract->continuation = NULL;
    return contract;
}

// Helper function to create a new contract with CHOICE tag
Contract* newChoiceContract(const char* id, const char* role, Contract* continuation) {
    Contract* contract = malloc(sizeof(Contract));
    contract->tag = CHOICE;
    contract->choiceParams.id = strdup(id);
    contract->choiceParams.role = strdup(role);
    contract->continuation = continuation;
    return contract;
}

// Helper function to create a new contract with DEPOSIT tag
Contract* newDepositContract(const char* depositor, const char* receiver, const char* amount,
                             const char* currency, int timeout, Contract* continuation) {
    Contract* contract = malloc(sizeof(Contract));
    contract->tag = DEPOSIT;
    contract->depositParams.depositor = strdup(depositor);
    contract->depositParams.receiver = strdup(receiver);
    contract->depositParams.amount = strdup(amount);
    contract->depositParams.currency = strdup(currency);
    contract->depositParams.timeout = timeout;
    contract->continuation = continuation;
    return contract;
}

// Helper function to create a new contract with PAY tag
Contract* newPayContract(const char* payer, const char* receiver, const char* amount,
                         const char* currency, Contract* continuation) {
    Contract* contract = malloc(sizeof(Contract));
    contract->tag = PAY;
    contract->payParams.payer = strdup(payer);
    contract->payParams.receiver = strdup(receiver);
    contract->payParams.amount = strdup(amount);
    contract->payParams.currency = strdup(currency);
    contract->continuation = continuation;
    return contract;
}

// Helper function to create a new contract with WHEN tag
Contract* newWhenContract(const char* timeout, Contract* contract, Contract* continuation) {
    Contract* whenContract = malloc(sizeof(Contract));
    whenContract->tag = WHEN;
    whenContract->whenParams.timeout = strdup(timeout);
    whenContract->whenParams.contract = contract;
    whenContract->continuation = continuation;
    return whenContract;
}

// Helper function to create a new contract with CASE tag
Contract* newCaseContract(const char* caseId, const char* role, Contract* contract, Contract* continuation) {
    Contract* caseContract = malloc(sizeof(Contract));
    caseContract->tag = CASE;
    caseContract->caseParams.caseId = strdup(caseId);
    caseContract->caseParams.role = strdup(role);
    caseContract->caseParams.contract = contract;
    caseContract->continuation = continuation;
    return caseContract;
}

// Helper function to extract string value from JSON object
const char* getStringValue(json_t* root, const char* fieldName) {
    json_t* field = json_object_get(root, fieldName);
    if (field && json_is_string(field)) {
        return json_string_value(field);
    }
    return NULL;
}

// Helper function to extract integer value from JSON object
int getIntValue(json_t* root, const char* fieldName) {
    json_t* field = json_object_get(root, fieldName);
    if (field && json_is_integer(field)) {
        return (int)json_integer_value(field);
    }
    return 0;
}

// Function to parse Marlowe contract and generate C structure
Contract* generateCStructureFromMarlowe(const char* marloweContract) {
    json_error_t error;
    json_t* root = json_loads(marloweContract, 0, &error);
    if (!root) {
        fprintf(stderr, "Error parsing Marlowe contract: %s\n", error.text);
        return NULL;
    }

    // Extract contract data from JSON
    const char* tag = getStringValue(root, "tag");
    Contract* continuation = NULL;
    Contract* contract = NULL;

    if (strcmp(tag, "Close") == 0) {
        int id = getIntValue(root, "id");
        contract = newCloseContract(id);
    } else if (strcmp(tag, "Choice") == 0) {
        const char* choiceId = getStringValue(root, "choiceId");
        const char* role = getStringValue(root, "role");
        // TODO: Extract continuation contract
        contract = newChoiceContract(choiceId, role, continuation);
    } else if (strcmp(tag, "Deposit") == 0) {
        const char* depositor = getStringValue(root, "depositor");
        const char* receiver = getStringValue(root, "receiver");
        const char* amount = getStringValue(root, "amount");
        const char* currency = getStringValue(root, "currency");
        int timeout = getIntValue(root, "timeout");
        // TODO: Extract continuation contract
        contract = newDepositContract(depositor, receiver, amount, currency, timeout, continuation);
    } else if (strcmp(tag, "Pay") == 0) {
        const char* payer = getStringValue(root, "payer");
        const char* receiver = getStringValue(root, "receiver");
        const char* amount = getStringValue(root, "amount");
        const char* currency = getStringValue(root, "currency");
        // TODO: Extract continuation contract
        contract = newPayContract(payer, receiver, amount, currency, continuation);
    } else if (strcmp(tag, "When") == 0) {
        const char* timeout = getStringValue(root, "timeout");
        // TODO: Extract contract and continuation contracts
        contract = newWhenContract(timeout, contract, continuation);
    } else if (strcmp(tag, "Case") == 0) {
        const char* caseId = getStringValue(root, "caseId");
        const char* role = getStringValue(root, "role");
        // TODO: Extract contract and continuation contracts
        contract = newCaseContract(caseId, role, contract, continuation);
    }

    json_decref(root);

    // Return the root contract of the generated C structure
    return contract;
}

int main() {
    // Load Marlowe contract from file
    const char* filename = "marlowe_contract.txt";
    FILE* file = fopen(filename, "r");
    if (!file) {
        fprintf(stderr, "Error opening file: %s\n", filename);
        return 1;
    }

    fseek(file, 0, SEEK_END);
    long fileSize = ftell(file);
    fseek(file, 0, SEEK_SET);

    char* marloweContract = malloc(fileSize + 1);
    if (!marloweContract) {
        fprintf(stderr, "Error allocating memory for contract\n");
        fclose(file);
        return 1;
    }

    size_t bytesRead = fread(marloweContract, 1, fileSize, file);
    if (bytesRead != (size_t)fileSize) {
        fprintf(stderr, "Error reading contract from file\n");
        free(marloweContract);
        fclose(file);
        return 1;
    }

    marloweContract[fileSize] = '\0';

    fclose(file);

    // Generate C structure from Marlowe contract
    Contract* cStructure = generateCStructureFromMarlowe(marloweContract);

    // Clean up memory
    free(marloweContract);

    // TODO: Use the generated C structure as needed

    return 0;
}
