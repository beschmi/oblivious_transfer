include "groups_prime_order.ec".

type chooser_state.

type choice = bool.

type group4 = (group * group * group * group).

adversary A(mc : group4) : bool {}.

game ChooserSec = {
  abs A = A {}
  fun Chooser(sigma : bool) : group4 = {
    var a, b, c : zq;
    var z0, z1 : group;

    a = i_to_zq([0..q-1]);
    b = i_to_zq([0..q-1]);
    c = i_to_zq([0..q-1]);

    if (sigma) {
      z1 = g^(a*b); z0 = g^c;
    } else {
      z0 = g^(a*b); z1 = g^c;
    }
    return (g^a, g^b, z0, z1);
  }

  fun Main() : bool = {
    var sigma, sigma' : bool;
    var mc : group4;
    sigma = {0,1};
    mc = Chooser(sigma);
    sigma' = A(mc);
    return (sigma = sigma');
  }
}.

game DDH0 = {
  abs A = A {}

  fun Chooser(sigma : bool, U : group, V : group, W : group) : group4 = {
    var z0, z1 : group;
    var c : zq;

    c = i_to_zq([0..q-1]);
    if (sigma) {
      z1 = W; z0 = g^c;
    } else {
      z0 = W; z1 = g^c;
    }
    return (U, V, z0, z1);
  }

  fun B(U : group, V : group, W : group) : bool = {
    var sigma, sigma' : bool;
    var mc : group4;
    sigma = {0,1};
    mc = Chooser(sigma, U, V, W);
    sigma' = A(mc);
    return (sigma = sigma');
  }

  fun Main() : bool = {
    var a, b : zq;
    var guess : bool;
    a = i_to_zq([0..q-1]);
    b = i_to_zq([0..q-1]);

    guess = B(g^a, g^b, g^(a*b));
    return guess;
  }
}.

equiv Eq_ChooserSec_DDH0 : ChooserSec.Main ~ DDH0.Main : true ==> ={res}.
  inline.
  swap {2} 6 -5.
  rnd >>.
  sp.
  swap {2} 10 -7.
  derandomize.
  !3rnd>>.
  sp 3 10.
  case {1}: sigma_0.
    condt.
    auto.
  condf.
  auto.
save.


game DDH1 = DDH0
  where Main = {
    var a, b, u : zq;
    var guess : bool;
    a = i_to_zq([0..q-1]);
    b = i_to_zq([0..q-1]);
    u = i_to_zq([0..q-1]);

    guess = B(g^a, g^b, g^u);
    return guess;
  }.

game G1 = {
  abs A = A {}

  fun Main() : bool = {
    var sigma, sigma' : bool;
    var mc : group4;
    var a, b, c, d : zq;

    a = i_to_zq([0..q-1]);
    b = i_to_zq([0..q-1]);
    c = i_to_zq([0..q-1]);
    d = i_to_zq([0..q-1]);
    mc = (g^a, g^b, g^c, g^d);

    sigma' = A(mc);
    sigma = {0,1};
    return (sigma = sigma');
  }
}.

equiv Eq_DDH1_G1 : DDH1.Main ~ G1.Main : true ==> ={res}.
  inline.
  swap {2} 7 -6.
  swap {1} 7 -6.
  rnd >>.
  case {1} : sigma.
    condt {1} at 12.
      derandomize.
      !4rnd {1} >>. sp.
      trivial.
    derandomize.
    swap {2} 3 1.
    !4rnd >>.
    auto.
  condf {1} at 12.
    derandomize.
    !4rnd {1} >>. sp.
    trivial.
  derandomize.
  !4rnd >>.
  auto.
save.


claim C_G1 :G1.Main[res] = 1%r/2%r compute.

claim C_ChooserSec_DDH0: ChooserSec.Main[res] = DDH0.Main[res]
  using Eq_ChooserSec_DDH0.

claim C_DDH1_G1: DDH1.Main[res] = G1.Main[res] using Eq_DDH1_G1.

claim C_ChooserSec:
  | ChooserSec.Main[res] - 1%r/2%r | = | DDH0.Main[res] - DDH1.Main[res] |.



