Token* newTokenHolding(CurrencyType currency, int amount);
Wallet* newWallet(Token tokens[], int numTokens);
Party* newParty(const char* name, int id, Wallet* wallet);
InternalAccount* newInternalAccount(int id, Wallet wallet);
InternalWallet* newInternalWallet(InternalAccount accounts[], int numAccounts);
ContractState* newContractState(Contract* currentContract, InternalWallet* internalWallet, Party* parties[], int numParties);
Contract* newContract(ContractType type, ContractParameters params, Contract* subContractOK, Contract* continueAs);