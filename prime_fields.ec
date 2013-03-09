(* prime fields Z/qZ *)
cnst q : int.
axiom q_pos : 0 < q.
type zq.

op [*] : (zq, zq) -> zq as zq_mult.
op [+] : (zq, zq) -> zq as zq_add.
op [-] : (zq) -> zq as zq_un_minus.
op inv : zq -> zq.
op [-] (x , y : zq) = x + (-y) as zq_minus.


cnst zq0 : zq.
cnst zq1 : zq.

(* See Harrison: Theorem proving with the Real Numbers, p. 10 *)
axiom one_zero: zq0 <> zq1.


axiom zq_add_comm : forall (x, y:zq), x + y = y + x.

axiom zq_add_assoc : forall (x, y, z : zq), x + (y + z) = (x + y) + z.

axiom zq_add_unit : forall (x : zq), zq0 + x = x.

axiom zq_plus_minus : forall (x : zq), x + (-x) = zq0.

axiom zq_mult_comm : forall (x, y:zq), x * y = y * x.

axiom zq_mult_assoc : forall (x, y, z : zq), x * (y * z) = (x * y) * z.

axiom zq_mult_unit : forall (x : zq), x * zq1 = x.

axiom zq_mult_inv : forall (x:zq), x <> zq0 => (x * inv(x)) = zq1.

axiom zq_distr : forall (x,y,z : zq), x * (y + z) = x*y + x*z.


lemma zq_mult_zero : forall (x : zq), x * zq0 = zq0.

lemma zq_minus : forall (x : zq), (x - x) = zq0.

lemma zq_minus_minus : forall (x : zq), -(-x) = x.

axiom (* lemma *) zq_mult_minus : forall (x, y : zq), (-x) * y = - (x * y).

lemma zq_minus_distr: forall (x,y,z : zq), x * (y - z) = x*y - x*z.



pop sample_uniform_zq : () -> zq.

(* conversion between int and zq *)
op i_to_zq : int -> zq.

op zq_to_i : zq -> int.

axiom zq_to_i_pos : forall (x : zq), 0 <= zq_to_i (x).

axiom zq_to_i_smaller : forall (x : zq), zq_to_i (x) <= q - 1.

axiom zq_to_i_i_to_zq : forall (x : int),  0 <= x && x < q => zq_to_i(i_to_zq(x)) = x.

axiom i_to_zq_zq_to_i : forall (x : zq), i_to_zq(zq_to_i(x)) = x.

(* some lemmas for testing *)

(*
lemma a:
forall (a, b, c, d : zq), (a + (b + zq0)) * c  * zq1 = a * c + b * c + (d + -d).

lemma b:
forall (a, b, c, d : zq),
  a + d <> zq0 => 
  (a + (b + zq0)) * c + zq1 = a * c + b * c + ((a+d) * inv(a+d)).
*)
