cod : Functor

term  : Type
form  : Type

Func (f : nat) : "cod (fint f)" (term) -> term
Fal : form
Pred (p : nat) : "cod (fint p)" (term) -> form
Impl : form -> form -> form
Conj : form -> form -> form
Disj : form -> form -> form
All  : (term -> form) -> form
Ex   : (term -> form) -> form
