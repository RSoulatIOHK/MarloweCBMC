CBMC version 5.87.0 (cbmc-5.87.0) 64-bit x86_64 linux
Parsing utxo_cbmc.c
Converting
Type-checking utxo_cbmc
Generating GOTO Program
Adding CPROVER library (x86_64)
Removal of function pointers and virtual functions
Generic Property Instrumentation
Performing a full slice
Running with 10 object bits, 54 offset bits (user-specified)
Starting Bounded Model Checking
Runtime Symex: 0.324677s
size of program expression: 10836 steps
simple slicing removed 24 assignments
Generated 85 VCC(s), 1 remaining after simplification
Runtime Postprocess Equation: 0.00273599s
Passing problem to propositional reduction
converting SSA
Runtime Convert SSA: 0.0623782s
Running propositional reduction
Post-processing
Runtime Post-process: 5.364e-06s
Solving with MiniSAT 2.2.1 without simplifier
128599 variables, 126344 clauses
SAT checker: instance is SATISFIABLE
Runtime Solver: 0.0200366s
Runtime decision procedure: 0.0828569s
Building error trace

** Results:
utxo_cbmc.c function main
[main.assertion.1] line 450 Cannot steal: FAILURE

Trace for main.assertion.1:

↳ utxo_cbmc.c:403 main()

↳ utxo_cbmc.c:405 createLedger()

↳ utxo_cbmc.c:409 initializeActors(&dynamic_object, 2, 100)

↳ utxo_cbmc.c:310 createUTxO(1, 100)

↳ utxo_cbmc.c:312 addUTxOToLedger(&dynamic_object, &dynamic_object$0)

↳ utxo_cbmc.c:310 createUTxO(2, 100)

↳ utxo_cbmc.c:312 addUTxOToLedger(&dynamic_object, &dynamic_object$2)


=======================================================================================================
  413: choice_num=0 
  414: Choice: INITIATE SWAP

  419: swapOwner=1 

↳ utxo_cbmc.c:420 initiateSwap(&dynamic_object, 1, 20)

=======================================================================================================
  413: choice_num=1 
  414: Choice: INITIATE SWAP

  419: swapOwner=1 

↳ utxo_cbmc.c:420 initiateSwap(&dynamic_object, 1, 20)

=======================================================================================================
  413: choice_num=2 
  414: Choice: Transaction built 

  426: senderId=1 

↳ utxo_cbmc.c:428 initTransaction(&transaction!0@3, 1)

  430: numTransactions=0 

↳ utxo_cbmc.c:431 getUnspentTransactionsByIDorContract(&dynamic_object, 1, &numTransactions!0@3)
  280: count=0 
  281: i=0 

↳ utxo_cbmc.c:288 malloc(0ul)
  43: dynamic_object$66={  } ( })
  43: malloc_res=(const void *)&dynamic_object$66
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  288: unspentTransactions=(UTxO **)&dynamic_object$66
  294: index=0 
  295: i=0 
  303: numTransactions=0 
↵
  431: ptrToUtxosB=(UTxO **)&dynamic_object$66
  432: i=0 

↳ utxo_cbmc.c:445 createTransferTransaction(&dynamic_object, 1, dynamic_object$64, 0, dynamic_object$65, 0)
  114: useScriptAddress=FALSE 
  118: i=0 
  129: tokenAmount=0 
  130: i=0 
  135: tokenBalance=0 
  136: i=0 
  163: i=0 
  168: unspentToken=0 

  ↳ utxo_cbmc.c:170 createUTxO(1, 0) <- UNSPENT TX

    ↳ utxo_cbmc.c:63 malloc(sizeof(UTxO) /*24ul*/ )
      43: dynamic_object$83={ .spent=0, .ownerID=0, .isScript=FALSE, .$pad3=0,
        .datum={ .originID=0, .amountToken1=0 }, .amount=0 } 
      43: dynamic_object$83.spent=0 
      43: dynamic_object$83.ownerID=0 
      43: dynamic_object$83.isScript=FALSE 
      43: dynamic_object$83.$pad3=0 
      43: dynamic_object$83.datum={ .originID=0, .amountToken1=0 } 
      43: dynamic_object$83.datum.originID=0 
      43: dynamic_object$83.datum.amountToken1=0 
      43: dynamic_object$83.amount=0 
      43: malloc_res=(const void *)&dynamic_object$83.spent 
      46: record_malloc=FALSE (0)
      47: __CPROVER_malloc_is_new_array=FALSE (0)
  ↵
    63: utxo=&dynamic_object$83 
    64: dynamic_object$83.spent=0 
    65: dynamic_object$83.ownerID=1 
    66: dynamic_object$83.isScript=FALSE 
    67: dynamic_object$83.amount=0 
    68: dynamic_object$83.datum.amountToken1=0 
    69: dynamic_object$83.datum.originID=1 
  ↵
  170: backUTxO=&dynamic_object$83 

↳ utxo_cbmc.c:174 addUTxOToLedger(&dynamic_object, &dynamic_object$83)

↳ utxo_cbmc.c:56 realloc(NULL, 8ul)

↳ <builtin-library-realloc>:14 malloc(8ul)
  43: dynamic_object$84=((UTxO *)NULL) 
  43: malloc_res=(const void *)&dynamic_object$84 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
↵
↵
=======================================================================================================
  413: choice_num=3 
  414: Choice: Transaction built 

  426: senderId=1 

↳ utxo_cbmc.c:428 initTransaction(&transaction!0@4, 1)
  365: transaction.numInputs=0 
  366: transaction.numOutputs=0 
  367: transaction.signerID=1 

↳ utxo_cbmc.c:370 malloc(sizeof(UTxO *) * 5ul /*40ul*/ )
  43: dynamic_object$91={ ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL) } 
  43: dynamic_object$91[0l]=((UTxO *)NULL) 
  43: dynamic_object$91[1l]=((UTxO *)NULL) 
  43: dynamic_object$91[2l]=((UTxO *)NULL) 
  43: dynamic_object$91[3l]=((UTxO *)NULL) 
  43: dynamic_object$91[4l]=((UTxO *)NULL) 
  43: malloc_res=(const void *)dynamic_object$91
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  370: transaction.inputs=dynamic_object$91
  371: i=0 
  372: dynamic_object$91[0l]=((UTxO *)NULL) 
  371: i=1 
  372: dynamic_object$91[1l]=((UTxO *)NULL) 
  371: i=2 
  372: dynamic_object$91[2l]=((UTxO *)NULL) 
  371: i=3 
  372: dynamic_object$91[3l]=((UTxO *)NULL) 
  371: i=4
  372: dynamic_object$91[4l]=((UTxO *)NULL) 
  371: i=5 

↳ utxo_cbmc.c:376 malloc(sizeof(UTxO *) * 5ul /*40ul*/ )
  43: dynamic_object$92={ ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL) } 
  43: dynamic_object$92[0l]=((UTxO *)NULL) 
  43: dynamic_object$92[1l]=((UTxO *)NULL) 
  43: dynamic_object$92[2l]=((UTxO *)NULL) 
  43: dynamic_object$92[3l]=((UTxO *)NULL) 
  43: dynamic_object$92[4l]=((UTxO *)NULL) 
  43: malloc_res=(const void *)dynamic_object$92
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  376: transaction.outputs=dynamic_object$92
  377: i=0 
  378: dynamic_object$92[0l]=((UTxO *)NULL) 
  377: i=1 
  378: dynamic_object$92[1l]=((UTxO *)NULL) 
  377: i=2 
  378: dynamic_object$92[2l]=((UTxO *)NULL) 
  377: i=3 
  378: dynamic_object$92[3l]=((UTxO *)NULL) 
  377: i=4
  378: dynamic_object$92[4l]=((UTxO *)NULL) 
  377: i=5 
↵
  430: numTransactions=0 

↳ utxo_cbmc.c:431 getUnspentTransactionsByIDorContract(&dynamic_object, 1, &numTransactions!0@4)
  280: count=0 
  281: i=0 

↳ utxo_cbmc.c:288 malloc(0ul)
  43: dynamic_object$93={  } ( })
  43: malloc_res=(const void *)&dynamic_object$93
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  288: unspentTransactions=(UTxO **)&dynamic_object$93
  294: index=0 
  295: i=0 
  303: numTransactions=0 
↵
  431: ptrToUtxosB=(UTxO **)&dynamic_object$93
  432: i=0 

↳ utxo_cbmc.c:445 createTransferTransaction(&dynamic_object, 1, dynamic_object$91, 0, dynamic_object$92, 0)
  114: useScriptAddress=FALSE 
  118: i=0 
  129: tokenAmount=0 
  130: i=0 
  135: tokenBalance=0 
  136: i=0 
  163: i=0 
  168: unspentToken=0 

↳ utxo_cbmc.c:170 createUTxO(1, 0)

↳ utxo_cbmc.c:63 malloc(sizeof(UTxO) /*24ul*/ )
  43: dynamic_object$110={ .spent=0, .ownerID=0, .isScript=FALSE, .$pad3=0,
    .datum={ .originID=0, .amountToken1=0 }, .amount=0 } 
  43: dynamic_object$110.spent=0 
  43: dynamic_object$110.ownerID=0 
  43: dynamic_object$110.isScript=FALSE 
  43: dynamic_object$110.$pad3=0 
  43: dynamic_object$110.datum={ .originID=0, .amountToken1=0 } 
  43: dynamic_object$110.datum.originID=0 
  43: dynamic_object$110.datum.amountToken1=0 
  43: dynamic_object$110.amount=0 
  43: malloc_res=(const void *)&dynamic_object$110.spent 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  63: utxo=&dynamic_object$110 
  64: dynamic_object$110.spent=0 
  65: dynamic_object$110.ownerID=1 
  66: dynamic_object$110.isScript=FALSE 
  67: dynamic_object$110.amount=0 
  68: dynamic_object$110.datum.amountToken1=0 
  69: dynamic_object$110.datum.originID=1 
↵
  170: backUTxO=&dynamic_object$110 

↳ utxo_cbmc.c:174 addUTxOToLedger(&dynamic_object, &dynamic_object$110)

↳ utxo_cbmc.c:56 realloc(NULL, 8ul)

↳ <builtin-library-realloc>:14 malloc(8ul)
  43: dynamic_object$111=((UTxO *)NULL) 
  43: malloc_res=(const void *)&dynamic_object$111 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
↵
↵
=======================================================================================================
  413: choice_num=4
  414: Choice: Transaction built 

↳ utxo_cbmc.c:426 constr_nondet_int(1, 2)
↵
  426: senderId=1 

↳ utxo_cbmc.c:428 initTransaction(&transaction!0@5, 1)
  365: transaction.numInputs=0 
  366: transaction.numOutputs=0 
  367: transaction.signerID=1 

↳ utxo_cbmc.c:370 malloc(sizeof(UTxO *) * 5ul /*40ul*/ )
  43: dynamic_object$118={ ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL) } 
  43: dynamic_object$118[0l]=((UTxO *)NULL) 
  43: dynamic_object$118[1l]=((UTxO *)NULL) 
  43: dynamic_object$118[2l]=((UTxO *)NULL) 
  43: dynamic_object$118[3l]=((UTxO *)NULL) 
  43: dynamic_object$118[4l]=((UTxO *)NULL) 
  43: malloc_res=(const void *)dynamic_object$118 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  370: transaction.inputs=dynamic_object$118 
  371: i=0 
  372: dynamic_object$118[0l]=((UTxO *)NULL) 
  371: i=1 
  372: dynamic_object$118[1l]=((UTxO *)NULL) 
  371: i=2 
  372: dynamic_object$118[2l]=((UTxO *)NULL) 
  371: i=3 
  372: dynamic_object$118[3l]=((UTxO *)NULL) 
  371: i=4
  372: dynamic_object$118[4l]=((UTxO *)NULL) 
  371: i=5 

↳ utxo_cbmc.c:376 malloc(sizeof(UTxO *) * 5ul /*40ul*/ )
  43: dynamic_object$119={ ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL), ((UTxO *)NULL) } 
  43: dynamic_object$119[0l]=((UTxO *)NULL) 
  43: dynamic_object$119[1l]=((UTxO *)NULL) 
  43: dynamic_object$119[2l]=((UTxO *)NULL) 
  43: dynamic_object$119[3l]=((UTxO *)NULL) 
  43: dynamic_object$119[4l]=((UTxO *)NULL) 
  43: malloc_res=(const void *)dynamic_object$119
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  376: transaction.outputs=dynamic_object$119
  377: i=0 
  378: dynamic_object$119[0l]=((UTxO *)NULL) 
  377: i=1 
  378: dynamic_object$119[1l]=((UTxO *)NULL) 
  377: i=2 
  378: dynamic_object$119[2l]=((UTxO *)NULL) 
  377: i=3 
  378: dynamic_object$119[3l]=((UTxO *)NULL) 
  377: i=4
  378: dynamic_object$119[4l]=((UTxO *)NULL) 
  377: i=5 
↵
  430: numTransactions=0 

↳ utxo_cbmc.c:431 getUnspentTransactionsByIDorContract(&dynamic_object, 1, &numTransactions!0@5)
  280: count=0 
  281: i=0 

↳ utxo_cbmc.c:288 malloc(0ul)
  43: dynamic_object$120={  } ( })
  43: malloc_res=(const void *)&dynamic_object$120 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  288: unspentTransactions=(UTxO **)&dynamic_object$120 
  294: index=0 
  295: i=0 
  303: numTransactions=0 
↵
  431: ptrToUtxosB=(UTxO **)&dynamic_object$120 
  432: i=0 

↳ utxo_cbmc.c:445 createTransferTransaction(&dynamic_object, 1, dynamic_object$118, 0, dynamic_object$119, 0)
  114: useScriptAddress=FALSE 
  118: i=0 
  129: tokenAmount=0 
  130: i=0 
  135: tokenBalance=0 
  136: i=0 
  163: i=0 
  168: unspentToken=0 

↳ utxo_cbmc.c:170 createUTxO(1, 0)

↳ utxo_cbmc.c:63 malloc(sizeof(UTxO) /*24ul*/ )
  43: dynamic_object$137={ .spent=0, .ownerID=0, .isScript=FALSE, .$pad3=0,
    .datum={ .originID=0, .amountToken1=0 }, .amount=0 } 
  43: dynamic_object$137.spent=0 
  43: dynamic_object$137.ownerID=0 
  43: dynamic_object$137.isScript=FALSE 
  43: dynamic_object$137.$pad3=0 
  43: dynamic_object$137.datum={ .originID=0, .amountToken1=0 } 
  43: dynamic_object$137.datum.originID=0 
  43: dynamic_object$137.datum.amountToken1=0 
  43: dynamic_object$137.amount=0 
  43: malloc_res=(const void *)&dynamic_object$137.spent 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
  63: utxo=&dynamic_object$137 
  64: dynamic_object$137.spent=0 
  65: dynamic_object$137.ownerID=1 
  66: dynamic_object$137.isScript=FALSE 
  67: dynamic_object$137.amount=0 
  68: dynamic_object$137.datum.amountToken1=0 
  69: dynamic_object$137.datum.originID=1 
↵
  170: backUTxO=&dynamic_object$137 

↳ utxo_cbmc.c:174 addUTxOToLedger(&dynamic_object, &dynamic_object$137)

↳ utxo_cbmc.c:56 realloc(NULL, 8ul)

↳ <builtin-library-realloc>:14 malloc(8ul)
  43: dynamic_object$138=((UTxO *)NULL) 
  43: malloc_res=(const void *)&dynamic_object$138 
  46: record_malloc=FALSE (0)
  47: __CPROVER_malloc_is_new_array=FALSE (0)
↵
↵
↵
=======================================================================================================
  413: choice_num=5 

↳ utxo_cbmc.c:450 calculateOwnerTokens(&dynamic_object, 1)
  383: totalTokens=0 
  385: i=0 
↵

Violated property:
  file utxo_cbmc.c function main line 450 thread 0
  Cannot steal
  tmp_if_expr



** 1 of 28 failed (2 iterations)
VERIFICATION FAILED
