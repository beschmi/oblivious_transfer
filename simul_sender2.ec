include "groups_prime_order.ec".

type chooser_state.

type choice = bool.

cnst maxlen : int.

type group4 = (group * group * group * group).

(* input chooser: "for every distribution on the inputs (m0,m1)" *)
adversary IC() : group * group {}.
(* first step of (dishonest) chooser:
   "and any (not necessarily polynomial-time) adversarial
    A substituting the chooser" *)
adversary C1() : group4 * chooser_state {}.
(* second step of (dishonest) chooser *)
adversary C2(ms : group4 option, st: chooser_state) : bitstring{maxlen} {}.
(* ideal/real distinguisher: ".. the outputs of A and A' are statistically
                              indistinguishable given m0 and m1" *)
adversary D(co: bitstring{maxlen}, m0 : group, m1 : group) : bool {}.

pop sample_uniform_zq2: () -> (zq *zq).

game Real = {
  abs IC = IC {}
  abs C1 = C1 {}
  abs C2 = C2 {}
  abs D  = D  {}
  (* Protocol 4.1 (Basic Protocol) *)
  fun Sender(m0: group, m1:group, mc: group4) : group4 option = {
    var res : group4 option = None;
    var x,y,z0,z1 : group;
    var r0, s0, r1, s1 : zq;
    (x,y,z0,z1) = mc;
    if (z0 <> z1) {
      (r0,s0) = sample_uniform_zq2();
      (r1,s1) = sample_uniform_zq2();
      res = Some((x^s0*g^r0, z0^s0 * y^r0 * m0
                 , x^s1*g^r1, z1^s1 * y^r1 * m1));
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


(* We exhibit a (non-polynomial) simulator Ci_Sim such that the distinguisher cannot
   distinguish Ci in the real model and Ci_Sim in the ideal model. *)
game Ideal = {
  (* state of simulator *)
  var cst : chooser_state
  var x,y,z0,z1 : group
  
  abs IC = IC {}
  abs C1 = C1 {}
  abs C2 = C2 {}
  abs D  = D  {}

  fun C1_Sim() : bool = {
    var mc : group4;
    (mc,cst)    = C1();
    (x,y,z0,z1) = mc;
    return ((y^log(x) = z0) ? false : true);
  }

  fun C2_Sim(m_sigma : group, sigma : bool) : bitstring{maxlen} = {
    var r_sigma, s_sigma, u, v : zq;
    var z_sigma, e_sigma, w_sigma, e_nsigma, w_nsigma : group;
    var mso : group4 option;
    var co : bitstring{maxlen};

    if (sigma) { z_sigma = z1; } else { z_sigma = z0; }

    (u,v) = sample_uniform_zq2();
    (r_sigma,s_sigma) = sample_uniform_zq2();

    w_sigma  = x^s_sigma*g^r_sigma;
    e_sigma  = z_sigma^s_sigma * y^r_sigma * m_sigma;
    w_nsigma = g^v;
    e_nsigma = g^u;

    if (z0 = z1) { mso = None;
    } else {
      if (sigma) { mso = Some((w_nsigma, e_nsigma, w_sigma,  e_sigma)); }
      else       { mso = Some((w_sigma,  e_sigma,  w_nsigma, e_nsigma)); }
    }
    co = C2(mso, cst);
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
    sigma   = C1_Sim();
    co      = C2_Sim(sigma ? m1 : m0, sigma); (* we inline the TTP here *)
    b       = D(co, m0, m1);
    return b;
  }
}.


(* We use rnd f,g in the next equiv proof for:
     f : <r,s> -> <a * s + b * r + d, c * s + r>
     g : <u,v> -> <(a*v + c*d - c * u)/(a - b*c), (u - d - b * v)/(a - b*c)>
   We therefore have to prove: g(f(<r,s>))=<r,s> [bij1] and f(g(<u,v>))=<u,v> [bij2].

   The axiomatized equalities have been checked in the computer-algebra
   system singular by computing the normal form:
   > ring R = (0,a,b,c,d)(v,u,r,s),dp;
   > (a*(c*s + r) + c*d - c*(a*s + b*r + d)) / (a - b*c);               // ==> r
   > ((a*s + b*r + d) - d - b*(c*s + r)) /(a - b*c);                    // ==> s
   > a * (u - d - b*v)/(a - b*c) + b*(a*v + c*d - c*u)/(a - b*c) + d;   // ==> u
   > c * (u - d - b*v)/(a - b*c) + (a*v + c*d - c*u)/(a - b*c);         // ==> v
*)
axiom bij1_fst:
forall (a,b,c,d : zq), a - b*c <> zq0 =>
  forall (r,s : zq), (a*(c*s + r) + c*d - c*(a*s + b*r + d))*inv (a - b*c) = r.

axiom bij1_snd:
forall (a,b,c,d : zq), a - b*c <> zq0 =>
  forall (r,s : zq), ((a*s + b*r + d) - d - b*(c*s + r))*inv (a - b*c) = s.

lemma bij1:
forall (a,b,c,d : zq), a - b*c <> zq0 =>
  forall (r,s : zq),
    let u,v = (a*s + b*r + d, c*s + r) in 
    ((a*v + c*d - c*u)*inv (a - b*c), (u - d - b*v)*inv (a - b*c)) = (r,s).

axiom bij2_fst:
forall (a,b,c,d : zq), a - b*c <> zq0 =>
  forall (u, v : zq),
    a * (u - d - b*v)*inv(a - b*c) + b*(a*v + c*d - c*u)*inv(a - b*c) + d = u.

axiom bij2_snd:
forall (a,b,c,d : zq), a - b*c <> zq0 =>
  forall (u, v : zq),
    c * (u - d - b*v)*inv(a - b*c) + (a*v + c*d - c*u) * inv(a - b*c) = v.

lemma bij2:
forall (a,b,c,d : zq), a - b*c <> zq0 =>
  forall (u, v : zq),
   let r,s = ((a*v + c*d - c*u) * inv(a - b*c),(u - d - b*v)*inv(a - b*c)) in 
   (a * s + b * r + d, c * s + r) = (u,v).


equiv Eq_Sender_secure: Real.Main ~ Ideal.Main : true ==> ={res}.
inline C1_Sim, C2_Sim, Sender.
call; wp. call.
app 1 1 ={m0,m1}; [ call; trivial | ].
app 1 1 ={m0,m1} &&  mc_0{2} = mc{1} && cst{2} = st{1}; [ call; trivial | sp 5 4].
case {2} : (z0 = z1).
  (* both return None *)
  condt {2} at 8; [ trivial | ].
  condf {1}.
  trivial.
(* z0 <> z1 *)
condt {1}.
condf {2} at 8; [ trivial | ].
case {2} : sigma_0.
  (* sigma_0 = 1 *)
  condt {2}.
  condt {2} at 8; [trivial | ].
  wp. rnd. sp.
  app 0 0 (={z0,z1,x,y,m0,m1} && m_sigma{2} = m1_0{1} && cst{2} = st{1}
           && (log(y{1}) * log(x{1}) <> log(z0{1}))
           && z_sigma{2} = z1{2}); [ trivial |].
  app 0 0 (={z0,z1,x,y,m0,m1} && m_sigma{2} = m1_0{1} && cst{2} = st{1}
           && (log(z0{1}) - log(y{1}) * log(x{1}) <> zq0)
           && z_sigma{2} = z1{2}); [ trivial |].
  app 2 2 (   (v{2} = ((log(x) * s0 + r0){1}))
           && (u{2} = ((log(z0) * s0 + log(y) * r0 + log(m0_0)){1}))
           && cst{2} = st{1}
           && ={z1,x,y,m0,m1} && m_sigma{2} = m1_0{1}
           && z_sigma{2} = z1{2}); [ | trivial].
    timeout 1.
    simpl.
    (* we apply rnd f,g in the next step. We can read off f from the required
       equalities in the post and compute the inverse g of f using linear algebra. *)
    rnd >>
        (r_s -> let r,s = r_s in
                ( log(z0{1}) * s + log(y{1}) * r + log(m0_0{1})
                , log(x{1}) * s + r)),
        (u_v -> let u,v = u_v in
                ( (log(z0{1})*v + log(x{1})*log(m0_0{1}) - log(x{1}) * u)
                   * inv(log(z0{1}) - log(y{1})*log(x{1}))
                , (u - log(m0_0{1}) - log(y{1}) * v)
                  * inv(log(z0{1}) - log(y{1})*log(x{1})))).
     app 0 0  (u{2} = log(z0{1}) * s0{1} + log(y{1}) * r0{1} + log(m0_0{1}) &&
               v{2} = log(x{1}) * s0{1} + r0{1} &&
               z_sigma{2} = z1{2} &&
               ={z0,z1,x,y,m0,m1} &&
               m_sigma{2} = m1_0{1} &&
               cst{2} = st{1} && log(z0{1}) - log(y{1})*log(x{1}) <> zq0).
     trivial.
     trivial.
(* sigma_0 = 0, analogous proof to previous case *)
condf {2}.
condf {2} at 8; [trivial | ].
swap {1} 1 1.
wp. rnd. sp.
app 0 0 (={z0,z1,x,y,m0,m1} && m_sigma{2} = m0_0{1} && cst{2} = st{1}
         && (log(y{1})*log(x{1}) <> log(z1{1}))
         && z_sigma{2} = z0{2}); [ trivial |].
app 0 0 (={z0,z1,x,y,m0,m1} && m_sigma{2} = m0_0{1} && cst{2} = st{1}
         && (log(z1{1}) - log(y{1})*log(x{1}) <> zq0)
         && z_sigma{2} = z0{2}). timeout 3. trivial.
app 2 2 (   v{2} = (log(x) * s1 + r1){1}
         && u{2} = (log(z1) * s1 + log(y) * r1 + log(m1_0)){1}
         && cst{2} = st{1}
         && ={z1,z0,x,y,m0,m1} && m_sigma{2} = m0_0{1}
         && z_sigma{2} = z0{2}).
  timeout 1.
  simpl.
  rnd >>
      (r_s -> let r,s = r_s in
              ( log(z1{1}) * s + log(y{1}) * r + log(m1_0{1})
              , log(x{1}) * s + r)),
      (u_v -> let u,v = u_v in
              ( (log(z1{1})*v + log(x{1})*log(m1_0{1}) - log(x{1}) * u)
                 * inv(log(z1{1}) - log(y{1})*log(x{1}))
              , (u - log(m1_0{1}) - log(y{1}) * v)
                * inv(log(z1{1}) - log(y{1})*log(x{1})))).
  app 0 0  (u{2} = log(z1{1}) * s1{1} + log(y{1}) * r1{1} + log(m1_0{1}) &&
            v{2} = log(x{1}) * s1{1} + r1{1} &&
            z_sigma{2} = z0{2} &&
            ={z0,z1,x,y,m0,m1} &&
            m_sigma{2} = m0_0{1} &&
            cst{2} = st{1} && log(z1{1}) - log(y{1})*log(x{1}) <> zq0).
    trivial.
  trivial.
  trivial.
save.

(* information-theoretic sender security *)
claim C_Sender_secure: Real.Main[res] = Ideal.Main[res] using Eq_Sender_secure.