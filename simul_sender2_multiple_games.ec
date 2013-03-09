include "groups_prime_order.ec".

type chooser_state.

type choice = bool.

cnst maxlen : int.

type group4 = (group * group * group * group).

(* input chooser: "for every distribution on the inputs (m0,m1)" *)
adversary IC() : group * group {}.
(* first step of (dishonest) chooser:
   "and any (not necessarily polynomial-time) adversarial A
    substituting the chooser" *)
adversary C1() : group4 * chooser_state {}.
(* second step of (dishonest) chooser *)
adversary C2(ms : group4 option, st: chooser_state) : bitstring{maxlen} {}.
(* ideal/real distinguisher: ".. the outputs of A and A' are statistically
                              indistinguishable given m0 and m1" *)
adversary D(co: bitstring{maxlen}, m0 : group, m1 : group) : bool {}.

game Real = {
  abs IC = IC {}
  abs C1 = C1 {}
  abs C2 = C2 {}
  abs D  = D  {}

  (* Protocol 4.1 (Basic Protocol) *)
  fun Enc(x:group, y:group, z: group, m:group) : (group * group) = {
    var r, s : zq;
    s = sample_uniform_zq();
    r = sample_uniform_zq();
    return (x^s*g^r, z^s * y^r * m);
  }

  fun Sender(m0: group, m1:group, mc: group4) : group4 option = {
    var res : group4 option = None;
    var x,y,z0,z1,e0,w0,e1,w1 : group;
    var r0, s0, r1, s1 : zq;
    (x,y,z0,z1) = mc;
    if (z0 <> z1) {
      (w0,e0) = Enc(x,y,z0,m0);
      (w1,e1) = Enc(x,y,z1,m1);
      res = Some((w0,e0,w1,e1));
    }
    return res;
  }

  fun Main() : bool = {
    var m0, m1 : group;
    var mc : group4;
    var ms : group4 option;
    var st : chooser_state;
    var co : bitstring{maxlen};
    var b : bool;
    
    (m0,m1) = IC();
    (mc,st)        = C1();
    ms             = Sender(m0,m1,mc);
    co             = C2(ms, st);
    b              = D(co, m0, m1);
    return b;
  }
}.


(* randomly sample e_i and w_i for non DH-triple(s) (x,y,z_i) *)
game G1 = Real
  where Enc = {
    var r, s, v, u : zq;
    var res : (group * group);
    if (x^log(y) = z) {
      s = sample_uniform_zq();
      r = sample_uniform_zq();
      res = (x^s*g^r, z^s * y^r * m);
    } else {
      s = sample_uniform_zq();
      u = sample_uniform_zq();
      v = (log (z) * s + log(y) * (u + - (log(x) * s)) + log (m));
      res = (g^u, g^v);
    }
    return res;
  }.

prover "alt-ergo", eprover, cvc3. timeout 5.

equiv Eq_Real_G1_Enc: Real.Enc ~ G1.Enc: ={x,y,z,m} ==> ={res}.
  case {2} : x ^ log (y) = z.
    condt {2}.
    trivial.
  condf {2}.
  rnd >>. wp.
  (* we require a patched version of easycrypt for this that concludes from
     the name sample_uniform_zq that the sampling is uniform over the range *)
  rnd >> (r -> log (x{1}) * s{1} + r),(r -> r - log (x{1}) * s{1}).
  app 0 0 (u{2} = log (x{1}) * s{1} + r{1} && ={x,y,z,m,s}). trivial.
  trivial.
save.

equiv Eq_Real_G1: Real.Main ~ G1.Main: true ==> ={res} by auto.

(* randomly sample e_i and w_i for non DH-triple(s) (x,y,z_i) *)
game G2 = Real
  where Enc = {
    var r, s, v, u : zq;
    var res : (group * group);
    if (x^log(y) = z) {
      s = sample_uniform_zq();
      r = sample_uniform_zq();
      res = (x^s*g^r, z^s * y^r * m);
    } else {
      u = sample_uniform_zq();
      v = sample_uniform_zq();
      res = (g^u, g^v);
    }
    return res;
  }.

timeout 10.

(* Lemmas for bijections required for rnd *)
lemma bij1_aux1:
forall (a,b,c,d,e,w : zq),
  (a * w + b * (e - c * w) + d - b * e - d) = (a * w  - b * c * w + d - d).

lemma bij1_aux2:
forall (a,b,c,d,e,w : zq),
  (a * w  - b * c * w + d - d) =  (a * w  - b * c * w).

unset all. set bij1_aux1, bij1_aux2.
lemma bij1_aux3:
  forall (a,b,c,d,e,w : zq),
  (a * w + b * (e - c * w) + d - b * e - d) = (a * w  - b * c * w).

set all.
lemma bij1_aux4:
forall (a,b,c,d,e,w : zq),
  (a * w  - b * c * w) = (w * (a - b * c)).

unset all. set bij1_aux3, bij1_aux4.
lemma bij1_aux5:
forall (a,b,c,d,e,w : zq),
  (a * w + b * (e - c * w) + d - b * e - d) = (w * (a - b * c)).

set all.
lemma bij1:
forall (a,b,c,d,e : zq), a - b * c <> zq0 =>
  forall (w : zq), w = inv(a - b * c) * (a * w + b * (e - c * w) + d - b * e - d).

lemma bij2_aux1:
forall (a,b,c,d,e : zq), a - b * c <> zq0 => 
  forall (w : zq),
    a*(inv(a - b*c) * (w - b*e - d)) + b*(e - c*(inv(a - b*c)*(w - b*e - d))) + d
  = a*(inv(a - b*c) * (w - b*e - d)) - b*c*(inv(a - b*c)*(w - b*e - d)) + d + b * e.

lemma bij2_aux2:
forall (a,b,c,d,e : zq), a - b * c <> zq0 => 
  forall (w : zq),
    a*(inv(a - b*c) * (w - b*e - d)) -  b*c*(inv(a - b*c)*(w - b*e - d)) + d + b * e
  = (a - b*c)* (inv (a - b*c) * (w - b*e - d)) + d + b * e.

lemma bij2_aux3:
forall (a,b,c,d,e : zq), a - b * c <> zq0 => 
  forall (w : zq),
    a * (inv (a - b*c) * (w - b*e - d)) - b*c*(inv(a - b*c)*(w - b*e - d))+ d + b * e
  = w.

unset all. set bij2_aux1, bij2_aux2, bij2_aux3. 
lemma bij2:
forall (a,b,c,d,e : zq), a - b * c <> zq0 => 
  forall (w : zq),
    a*(inv(a - b*c) * (w - b*e - d)) + b*(e - c*(inv(a - b*c)*(w - b*e - d))) + d = w.

set all.
(* END Lemmas for bijections required for rnd *)

equiv Eq_G1_G2_Enc: G1.Enc ~ G2.Enc: ={x,y,z,m} ==> ={res}.
  case {2} : x ^ log (y) = z.
    condt.
    derandomize.
    trivial.
  condf.
  swap {1} 1 1.
  rnd >>.
  app 0 0 (={x,y,z,m,u} &&  log (y{1}) * log(x{1}) <> log(z{1})). trivial.
  app 0 0 (={x,y,z,m,u} &&  log(z{1}) - log (y{1}) * log(x{1}) <> zq0). trivial.
  rnd >>
     (s -> log(z{1}) * s + log(y{1}) * (u{1} - log(x{1})*s) + log(m{1})),
     (s -> inv(log(z{1}) - log(y{1})*log(x{1})) * (s - log(y{1})*u{1} - log(m{1}))).
  app 0 0 (v{2} = log(z{1}) * s{1} + log(y{1}) * (u{1} - log(x{1}) * s{1}) + log(m{1})
           && ={x,y,z,m,u} && log (z{1}) - log (y{1}) * log (x{1}) <> zq0).
    trivial.
  trivial.
save.

equiv Eq_G1_G2: G1.Main ~ G2.Main: true ==> ={res} by auto.

(* We exhibit a (non-polynomial) simulator Ci_Sim such that the distinguisher cannot
   distinguish Ci in the real model and Ci_Sim in the ideal model. *)
game Ideal = {

  abs IC = IC {}
  abs C1 = C1 {}
  abs C2 = C2 {}
  abs D  = D  {}

  (* state of the TTP *)
  var ttp_m0, ttp_m1 : group
  var ttp_sigma : bool option

  fun TTP_Sender(m0 : group, m1 : group) : unit = {
    ttp_m0 = m0;
    ttp_m1 = m1;
    ttp_sigma = None;
  }

  fun TTP_Chooser(sigma_arg : bool) : group = {
    var  sigma : bool;
    if (ttp_sigma <> None) {
      sigma = proj(ttp_sigma);
    } else { 
      sigma = sigma_arg;
    }
    return (sigma ? ttp_m1 : ttp_m0);
  }

  fun C_Sim() : bitstring{maxlen} = {
    var mc : group4;
    var x,y,z0,z1 : group;
    var st : chooser_state;
    var co : bitstring{maxlen};
    var mso : group4 option;
    var u0, v0, u1, v1, r0, s0, r1, s1 : zq;
    var m0, m1 : group;
    
    (mc,st)    = C1();
    (x,y,z0,z1) = mc; 
    
    if (z0 = z1) {
      (* invalid chooser message *)
      mso = None;
    } else {
      if (x ^ log(y) <> z0 && x ^ log(y) <> z1) {
        (* no DH triple given, return four random group elements *)
        u0 = sample_uniform_zq();
        v0 = sample_uniform_zq();
        u1 = sample_uniform_zq();
        v1 = sample_uniform_zq();
        mso = Some((g^u0, g^v0, g^u1, g^v1));
      } else {
        if (x ^ log(y) = z0) {
          (* sigma = 0 *)
          m0 = TTP_Chooser(false);
          s0 = sample_uniform_zq();
          r0 = sample_uniform_zq();
          u1  = sample_uniform_zq();
          v1  = sample_uniform_zq();
          mso = Some((x^s0*g^r0, z0^s0 * y^r0 * m0, g^u1, g^v1));
        } else {
          (* sigma = 1 *)
          m1 = TTP_Chooser(true);
          u0  = sample_uniform_zq();
          v0  = sample_uniform_zq();
          s1 = sample_uniform_zq();
          r1 = sample_uniform_zq();
          mso = Some((g^u0, g^v0,x^s1*g^r1, z1^s1 * y^r1 * m1));
        }
      }
    }
    
    co = C2(mso, st);
    return co;
  }

  fun Main() : bool = {
    var m0, m1 : group;
    var sigma0, sigma : bool;
    var ms, mc : group4;
    var st : chooser_state;
    var co : bitstring{maxlen};
    var b : bool;
    
    (m0,m1) = IC();
    TTP_Sender(m0,m1);
    co      = C_Sim();
    b       = D(co, m0, m1);
    return b;
  }
}.

prover "alt-ergo". timeout 1.

equiv Eq_G2_Ideal: G2.Main ~ Ideal.Main :  true ==> ={res}.
  inline.
  call; wp. call.
  app 1 1 ={m0,m1}; [ call; trivial | ].
  sp 0 5.
  app 1 1 ={m0,m1} && mc{1} = mc_0{2}  && st{1} = st_0{2}
          && ttp_sigma{2} = None && ttp_m0{2} = m0{2} && ttp_m1{2} = m1{2}.
    call. trivial.
  sp 5 1.
  case {2} : (z0 = z1).
    (* both return None *)
    condf {1}.
    condt {2}.
    trivial.
  condt {1}.
  condf {2}.
  case {2} : (x ^ log (y) <> z0 && x ^ log (y) <> z1).
    condt {2}.
    condf {1} at 5. trivial.
    condf {1} at 13. trivial.
    sp. wp.
    !2rnd.
    wp.
    !2rnd.
    trivial.
  case {2} : (x ^ log(y) = z0).
    sp 4 0.
    condt {1}.
    condf {1} at 9. trivial.
    condf {2}.
    condt {2}.
    condf {2} at 2. trivial.
    wp. !2rnd. wp. !2rnd.
    trivial.
  sp 4 0.
  condf {1}.
  condt {1} at 9. trivial.
  condf {2}.
  condf {2}.
  sp. wp.
  !2rnd. !2rnd>>.
  trivial.
save.

claim C_Ideal_G1: Real.Main[res] = G1.Main[res] using Eq_Real_G1.

claim C_G1_G2: G1.Main[res] = G2.Main[res] using Eq_G1_G2.

claim C_G2_Ideal: G2.Main[res] = Ideal.Main[res] using Eq_G2_Ideal.

(* information-theoretic sender security *)
claim C_Sender_secure: Real.Main[res] = Ideal.Main[res].