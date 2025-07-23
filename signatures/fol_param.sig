cod : Functor

term  : Type
form  : Type

Func (f : nat) : "cod (finat f)" (term) -> term
Fal : form
Pred (p : nat) : "cod (finat p)" (term) -> form
Impl : form -> form -> form
Conj : form -> form -> form
Disj : form -> form -> form
All  : (term -> form) -> form
Ex   : (term -> form) -> form
