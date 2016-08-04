(***********************************************************)
(*      This file contains the abstract term structure for *)
(*      the Fourier-Motzkin procedure                      *)
(***********************************************************)

Require Import ZArith.

Open Scope Z_scope.

Structure Fmodule: Type := {
   T: Type;
   injT: Z -> T;         (* injection of Z *)
   scalT: Z -> T -> T;   (* scalar multiplication *)
   opT: T -> T;          (* opposite *)
   plusT: T -> T -> T;   (* addition *)
   minusT: T -> T -> T;  (* subtraction *)
   leT: T -> T -> Prop;  (* comparison *)
   ltT: T -> T -> Prop   (* strict comparison *)
}.

Section Init.

Variable FT : Fmodule.

(* Unusal notation *)
Notation "x + y" := (plusT FT x y) : F_scope.
Notation "x - y" := (minusT FT x y) : F_scope.
Notation "x * y" := (scalT FT x y) : F_scope.
Notation "x <= y" := (leT FT x y) : F_scope.
Notation "x < y" := (ltT FT x y) : F_scope.

Let injT1: Z -> (T FT) := (injT FT).
Coercion injT1 : Z >-> T.
Open Scope F_scope.

 
(* Sets of axioms of the T type (not minimal!) *)
Structure Faxiom: Prop := {
 (* Arithmetic part *)
 injT_plus: forall z1 z2 : Z, (z1 + z2)%Z = z1 + z2 :> T _;
 scalT_plus_l: forall z1 z2 t, (z1 + z2) * t = z1 * t + z2 * t;
 scalT_mul: forall z1 z2 t, z1 * z2 * t = z1 * (z2 * t);
 injT_0_r: forall t, t + 0%Z = t :> T _;
 plusT_C: forall t1 t2, t1 + t2 = t2 + t1;
 plusT_A: forall t1 t2 t3, t1 + t2 + t3 = t1 + (t2 + t3);
 plusT_0: forall t1, t1 + (-1) * t1 = 0%Z;
 scalT_1: forall t, 1%Z * t = t;
 opT_def: forall t, opT _ t = (-1) * t;
 minusT_def: forall t1 t2, t1 - t2 = t1 + (-1) * t2;
 (* Inequality part *)
 leT_refl: forall x, x <= x;
 leT_compat: forall x y z t, x <= y -> z <= t -> x + z <= y + t;
 ltT_01: 0 < 1;
 ltT_compat: forall x y z t, x < y -> z <= t -> x + z < y + t;
 ltT_W: forall x y, x < y -> x <= y;
 leT_neg: forall x, (x < 0)%Z -> ~ 0 <= x;
 ltT_neg: forall x, (x <= 0)%Z -> ~ 0 < x
}.
Variable FA : Faxiom.

Let injT_plus := (injT_plus FA).
Let scalT_plus_l := (scalT_plus_l FA).
Let scalT_mul := (scalT_mul FA).
Let injT_0_r := (injT_0_r FA).
Let plusT_C := (plusT_C FA).
Let plusT_A := (plusT_A FA).
Let plusT_0 := (plusT_0 FA).
Let scalT_1 := (scalT_1 FA).
Let opT_def := (opT_def FA).
Let minusT_def := (minusT_def FA).
Let leT_refl := (leT_refl FA).
Let leT_compat := (leT_compat FA).
Let ltT_01 := (ltT_01 FA).
Let ltT_compat := (ltT_compat FA).
Let ltT_W := (ltT_W FA).
Let leT_neg := (leT_neg FA).

(************************************************************)
(*       Derived facts about the arithmetic fragment        *)
(************************************************************)

Lemma injT_0_l: forall t, 0%Z + t = t.
Proof.
intros t; rewrite plusT_C; auto; apply injT_0_r; auto.
Qed.

Lemma plusT_cancel: forall t t1 t2: T _, t + t1 = t + t2 -> t1 = t2.
intros t t1 t2 H.
Proof.
rewrite <- (injT_0_r t1); rewrite <- (plusT_0 t);
  rewrite <- plusT_A; rewrite (plusT_C t1);
  rewrite H; rewrite (plusT_C t); rewrite plusT_A;
  rewrite plusT_0; rewrite injT_0_r; trivial.
Qed.

Lemma scalT_0: forall t, 0%Z * t = 0%Z.
Proof.
intros t; rewrite <- (plusT_0 t).
pattern t at 2; rewrite <- (scalT_1 t).
rewrite <- scalT_plus_l; auto.
Qed.

Lemma scalT_m1: forall t, (-1) * ((-1) * t) = t.
Proof.
intros t; rewrite <- scalT_mul; rewrite scalT_1; auto.
Qed.

Lemma scalT_inj0: forall z, z * 0%Z = 0%Z.
Proof.
assert (Hp: forall p, (Zpos p) * 0 = 0).
intros p; induction p as [p Hrec | p Hrec | p].
rewrite Zpos_xI; rewrite Zmult_comm; 
  rewrite <- Zplus_diag_eq_mult_2.
repeat rewrite scalT_plus_l; rewrite Hrec.
rewrite injT_0_r; rewrite plusT_C; rewrite injT_0_r.
rewrite scalT_1; auto.
rewrite Zpos_xO; rewrite Zmult_comm; 
  rewrite <- Zplus_diag_eq_mult_2.
repeat rewrite scalT_plus_l; rewrite Hrec.
rewrite injT_0_r; auto.
rewrite scalT_1; auto.
intros z; destruct z as [| p | p]; auto.
apply scalT_0; auto.
change (Zneg p) with ((-1) * (Zpos p))%Z.
rewrite scalT_mul; rewrite Hp.
apply plusT_cancel with (0:T _).
rewrite plusT_0; rewrite injT_0_r; auto.
Qed.

Lemma scalT_plus_r: forall z t1 t2, z * (t1 + t2)= z * t1 + z * t2.
Proof.
assert (Hp0: forall t1 t2, (-1) * (t1 + t2)= (-1) * t1 + (-1) * t2).
intros p1 p2.
apply plusT_cancel with (p1 + p2).
rewrite plusT_0.
rewrite (plusT_C p1); rewrite plusT_A; rewrite (plusT_C p2).
repeat rewrite <- plusT_A; rewrite plusT_0; rewrite injT_0_l.
rewrite plusT_C; rewrite plusT_0; auto.
assert (Hp: forall p t1 t2,
 (Zpos p) * (t1 + t2)= (Zpos p) * t1 + (Zpos p) * t2).
intros p; induction p as [p Hrec | p Hrec|]; intros t1 t2.
rewrite Zpos_xI; repeat rewrite scalT_plus_l.
repeat rewrite (Zmult_comm 2); rewrite <- Zplus_diag_eq_mult_2.
repeat rewrite scalT_plus_l; repeat rewrite scalT_1.
rewrite Hrec.
repeat rewrite plusT_A; apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C.
repeat rewrite plusT_A; apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C.
repeat rewrite plusT_A; apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C.
repeat rewrite plusT_A; apply f_equal2 with (f := plusT FT); auto.
rewrite Zpos_xO.
repeat rewrite (Zmult_comm 2); rewrite <- Zplus_diag_eq_mult_2.
repeat rewrite scalT_plus_l; repeat rewrite scalT_1.
rewrite Hrec.
repeat rewrite plusT_A; apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C.
repeat rewrite plusT_A; apply f_equal2 with (f := plusT FT); auto.
repeat rewrite scalT_1; auto.
intros z; destruct z as [p | p |]; intros t1 t2; auto.
repeat rewrite scalT_0; rewrite injT_0_r; auto.
change (Zneg p) with ((-1) * (Zpos p))%Z.
repeat rewrite scalT_mul; rewrite Hp; rewrite Hp0; auto.
Qed.

Lemma injT_mul: forall z1 z2, (z1 * z2)%Z = z1 * z2 :> T _.
Proof.
assert (Hp: forall p z2, (Zpos p * z2)%Z = (Zpos p) * z2 :> T _).
intros p; induction p as [p Hrec | p Hrec | p]; intros z2.
rewrite Zpos_xI.
replace ((2 * Zpos p + 1) * z2)%Z with (Zpos p * (2 * z2) + z2)%Z;
  try ring.
rewrite scalT_plus_l; rewrite injT_plus; rewrite Hrec.
rewrite Zmult_comm; rewrite <- Zplus_diag_eq_mult_2.
rewrite injT_plus; rewrite scalT_plus_r.
rewrite (Zmult_comm 2); 
  rewrite <- Zplus_diag_eq_mult_2.
rewrite scalT_plus_l; rewrite scalT_1; auto.
rewrite Zpos_xO; rewrite (Zmult_comm 2); rewrite <- Zmult_assoc.
rewrite Hrec; rewrite scalT_mul.
replace (2 * z2)%Z with (z2 + z2)%Z; try ring.
change 2%Z with (1 + 1)%Z.
rewrite scalT_plus_l; rewrite injT_plus; rewrite scalT_1; auto.
rewrite scalT_1; rewrite Zmult_1_l; auto.
intros z1 z2; destruct z1 as [p | p|]; auto.
rewrite scalT_0; auto.
change (Zneg p) with ((-1) * (Zpos p))%Z.
rewrite <-Zmult_assoc. repeat rewrite scalT_mul; auto.
rewrite <- Hp.
apply plusT_cancel with (injT1 (Zpos p * z2)).
rewrite <- injT_plus; rewrite plusT_0.
apply f_equal with (f := injT1); ring.
Qed.

(*************************.***********************************)
(*       Derived facts about the comparison                 *)
(************************************************************)

Lemma ltT_cancel_l: forall x y z, x + y < x + z -> y < z.
Proof.
intros x y z H.
replace y with ((x + y) + (-1) * x).
replace z with ((x + z) + (-1) * x).
apply ltT_compat; auto.
rewrite (plusT_C x); rewrite plusT_A; rewrite plusT_0;
  rewrite injT_0_r; auto.
rewrite (plusT_C x); rewrite plusT_A; rewrite plusT_0;
  rewrite injT_0_r; auto.
Qed.

Lemma leT_cancel_l: forall x y z, x + y <= x + z -> y <= z.
Proof.
intros x y z H.
replace y with ((-1) * x + (x + y)).
replace z with ((-1) * x + (x + z)).
apply leT_compat; auto.
rewrite <- plusT_A; rewrite (fun z => plusT_C z x); rewrite plusT_0;
  rewrite injT_0_l; auto.
rewrite <- plusT_A; rewrite (fun z => plusT_C z x); rewrite plusT_0;
  rewrite injT_0_l; auto.
Qed.

Lemma leT_trans: forall x y z, x <= y -> y <= z -> x <= z.
Proof.
intros x y z H1 H2.
apply leT_cancel_l with y.
rewrite (plusT_C y).
apply leT_compat; auto.
Qed.

Lemma leT_opp: forall x y, x <= y -> (-1) * y <= (-1) * x.
Proof.
intros x y H.
apply leT_cancel_l with x.
rewrite plusT_0.
apply leT_cancel_l with y.
rewrite injT_0_r.
rewrite (plusT_C x); rewrite <- plusT_A; rewrite plusT_0;
  rewrite injT_0_l; auto.
Qed.

Lemma plusTss_pos: forall x y, 0 < x -> 0 < y -> 0 < x + y.
Proof.
intros x y Hx Hy.
rewrite <- (injT_0_r 0).
apply ltT_compat; auto; apply ltT_W; auto.
Qed.

Lemma plusT1s_pos: forall x y, 0 <= x -> 0 < y -> 0 < x + y.
Proof.
intros x y Hx Hy.
rewrite plusT_C; rewrite <- (injT_0_r 0).
apply ltT_compat; auto.
Qed.

Lemma plusTs1_pos: forall x y, 0 < x -> 0 <= y -> 0 < x + y.
Proof.
intros x y Hx Hy.
rewrite <- (injT_0_r 0).
apply ltT_compat; auto.
Qed.

Lemma plusT_pos: forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
intros x y Hx Hy.
rewrite <- (injT_0_r 0).
apply leT_compat; auto.
Qed.

Lemma eqT_pos: forall x y, (0:T _) = x -> (0:T _) = y -> (0:T _) = x + y.
Proof.
intros x y Hx Hy; rewrite <- Hx; rewrite <- Hy; rewrite injT_0_r; auto.
Qed.

Lemma injT_pos: forall x, (0 <= x)%Z -> 0 <= x.
Proof.
apply natlike_ind.
apply leT_refl.
intros x Hx H1x.
unfold Zsucc; rewrite injT_plus.
apply plusT_pos; auto.
Qed.

Lemma injT_spos: forall x, (0 < x)%Z -> 0 < x.
Proof.
intros x; destruct x as [|p|p]; intros HH;
  try (discriminate HH).
change 0 with (0+0)%Z.
replace (Zpos p) with (1 + (Zpos p - 1))%Z.
repeat rewrite injT_plus.
apply ltT_compat.
apply ltT_01.
apply injT_pos; case p; intros; intros HH1; discriminate HH1.
ring.
Qed.


Lemma scalT_pos: forall x y, (0 <= x)%Z -> 0 <= y -> 0 <= x * y.
Proof.
intros x y Hx Hy.
generalize x Hx; apply natlike_ind; auto; clear x Hx.
rewrite scalT_0; apply leT_refl.
intros x Hx Hp.
unfold Zsucc; rewrite scalT_plus_l.
apply plusT_pos; auto; rewrite scalT_1; auto.
Qed.

Lemma scalT_spos: forall x y, (0 < x)%Z -> 0 < y -> 0 < x * y.
Proof.
intros x y Hx Hy.
destruct x as [|p|p]; try discriminate Hx.
change 0 with (0+0)%Z.
replace (Zpos p) with (1 + (Zpos p - 1))%Z.
repeat rewrite injT_plus.
rewrite scalT_plus_l; rewrite scalT_1.
apply ltT_compat; auto.
apply scalT_pos; auto.
case p; intros; intros HH1; discriminate HH1.
ring.
Qed.

Lemma scalT_eq: forall x y, 0 = y -> (0:T _) = x * y.
Proof.
intros x y Hy; rewrite <- Hy; rewrite scalT_inj0; auto.
Qed.

End Init.

(* Unusal notation *)
Notation "x + y" := (plusT _ x y) : F_scope.
Notation "x - y" := (minusT _ x y) : F_scope.
Notation "x * y" := (scalT _ x y) : F_scope.
Notation "x <= y" := (leT _ x y) : F_scope.
Notation "x < y" := (ltT _ x y) : F_scope.

