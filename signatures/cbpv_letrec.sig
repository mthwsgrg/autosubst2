-- Call-by-Push-Value with a recursive let, uses variadic syntax
cod : Functor 

value : Type
comp : Type
nat : Type

const : nat -> value
thunk: comp -> value

force: value -> comp
letrec (n : nat) : (<n,value>  -> "cod (finat n)" (comp)) -> (<n,value> -> comp) -> comp
prd : value -> comp
seq : comp -> (value -> comp) -> comp
app: comp -> value -> comp
op : value -> value -> value
if0 : value -> comp -> comp -> comp
