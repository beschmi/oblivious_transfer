include "prime_fields.ec".

(* abelian groups of prime order *)
type group.
cnst g : group.

op [*] : (group, group) -> group as group_mult.
op [^] : (group, zq) -> group as group_pow.
op log : group -> zq.

axiom group_pow_add : forall (x, y:zq), g ^ x * g ^ y = g ^ (x + y).

axiom group_pow_mult : forall (x, y:zq),  (g ^ x) ^ y = g ^ (x * y).

axiom log_pow : forall (g':group), g ^ log(g') = g'.

axiom pow_log : forall (x:zq), log(g^x) = x.
