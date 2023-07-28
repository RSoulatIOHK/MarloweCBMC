void makeDeposit(ContractState* state, Transaction candidateTransaction, DepositContract depositPayload) {
    // Check if the candidate transaction matches the deposit payload
    if (strcmp(candidateTransaction.source, depositPayload.depositor) == 0 &&
        strcmp(candidateTransaction.destination, depositPayload.receiver) == 0 &&
        candidateTransaction.amount == depositPayload.amount &&
        strcmp(candidateTransaction.currency, depositPayload.currency) == 0) {
        // Move the funds from the source wallet (external) to the destination wallet (internal)
        Party* sourceParty = NULL;
        Party* destinationParty = NULL;

        // Find the source and destination parties
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
            return;
        }

        // Retrieve the source and destination wallets
        Wallet* sourceWallet = &(sourceParty->wallet);
        Wallet* destinationWallet = &(destinationParty->wallet);

        // Deduct the deposit amount from the source wallet
        for (int i = 0; i < sourceWallet->numTokens; i++) {
            if (strcmp(sourceWallet->tokens[i].currency, candidateTransaction.currency) == 0) {
                sourceWallet->tokens[i].amount -= candidateTransaction.amount;
                break;
            }
        }

        // Credit the deposit amount to the destination wallet
        for (int i = 0; i < destinationWallet->numTokens; i++) {
            if (strcmp(destinationWallet->tokens[i].currency, candidateTransaction.currency) == 0) {
                destinationWallet->tokens[i].amount += candidateTransaction.amount;
                break;
            }
        }

        printf("Deposit successful!\n");

        // Move the contract to the subcontract_ok pointer
        state->currentContract = state->currentContract->subContractOK;
    } else {
        printf("Invalid transaction! Deposit failed.\n");

        // Move the contract to the continueAs pointer
        state->currentContract = state->currentContract->continueAs;
    }
}
