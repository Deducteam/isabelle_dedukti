constant symbol Typ : TYPE;
constant symbol fun : Typ → Typ → Typ;

injective symbol eta : Typ → TYPE;
rule eta (fun $a $b) ↪ eta $a → eta $b;

constant symbol prop : Typ;
constant symbol imp : eta prop → eta prop → eta prop;
constant symbol all [a] : (eta a → eta prop) → eta prop;

symbol eps : eta prop → TYPE;
rule eps (imp $a $b) ↪ eps $a → eps $b
with eps (@all $a $b) ↪ Π x: eta $a, eps ($b x);
