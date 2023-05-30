constant symbol Set : TYPE;
constant symbol arr : Set → Set → Set;

injective symbol El : Set → TYPE;
rule El (arr $a $b) ↪ El $a → El $b;

constant symbol prop : Set;
constant symbol imp : El prop → El prop → El prop;
constant symbol all [a] : (El a → El prop) → El prop;

symbol Prf : El prop → TYPE;
rule Prf (imp $a $b) ↪ Prf $a → Prf $b
with Prf (@all $a $b) ↪ Π x: El $a, Prf ($b x);
