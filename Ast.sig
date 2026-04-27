sort : Type
term : Type

tSort : sort -> term

tProd : term -> (term -> term) -> term
tLambda : term -> (term -> term) -> term
tApp : term -> term -> term

tNat : term
tZero : term
tSucc : term -> term
tNatElim : (term -> term) -> term -> term -> term -> term

tEmpty : term
tEmptyElim : (term -> term) -> term -> term

tSig : term -> (term -> term) -> term
tPair : term -> (term -> term) -> term -> term -> term
tFst : term -> term
tSnd : term -> term

tId : term -> term -> term -> term
tRefl : term -> term -> term
tIdElim : term -> term -> (term -> term -> term) -> term -> term -> term -> term
