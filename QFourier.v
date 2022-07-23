Require Import ZArith Reals List.
Require Export FourierConcTerm Fourier FourierAbsTerm.

From mathcomp Require Import all_ssreflect all_algebra.

Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.

Definition iZrat (z : Z) : rat :=
 match z with 
 | Z0 => 0
 | Zpos x =>  (Pos.to_nat x)%:R
 | Zneg x =>  - ((Pos.to_nat x)%:R)
 end. 

Lemma iZratD z1 z2 : iZrat(z1 + z2) = iZrat z1 + iZrat z2.
Proof.
(case: z1 => [|p1|p1]); (case: z2 => [|p2|p2]) => //=; rat_to_ring;
  rewrite ?(add0r,addr0) //.
- by rewrite Pos2Nat.inj_add natrD.
- rewrite Z.pos_sub_spec.
  case: Pos.compare_spec => /= [->|H|H].
  - by set x := _%:R; rewrite -(subrr x).
  - rewrite Pos2Nat.inj_sub // natrB ?opprB //.
    by apply/ssrnat.leP/Pos2Nat.inj_le/Pos.lt_le_incl.
  rewrite Pos2Nat.inj_sub // natrB ?opprB //.
  by apply/ssrnat.leP/Pos2Nat.inj_le/Pos.lt_le_incl.
- rewrite Z.pos_sub_spec.
  case: Pos.compare_spec => /= [->|H|H].
  - by set x := _%:R; rewrite -(subrr x) addrC.
  - rewrite Pos2Nat.inj_sub // natrB ?opprB 1?[_ - _]addrC //.
    by apply/ssrnat.leP/Pos2Nat.inj_le/Pos.lt_le_incl.
  rewrite Pos2Nat.inj_sub // natrB ?opprB  1?[_ - _]addrC //.
  by apply/ssrnat.leP/Pos2Nat.inj_le/Pos.lt_le_incl.
by rewrite Pos2Nat.inj_add natrD opprD.
Qed.

Lemma iZratM z1 z2 : iZrat (z1 * z2) = iZrat z1 * iZrat z2.
Proof.
(case: z1 => [|p1|p1]); (case: z2 => [|p2|p2]) => //=; rat_to_ring;
  rewrite ?(mul0r, mulr0,Pos2Nat.inj_mul) //.
- by rewrite natrM.
- by rewrite natrM mulrN.
- by rewrite natrM mulNr.
by rewrite natrM mulNr mulrN opprK.
Qed.

Definition Qmodule: Fmodule.
apply (Build_Fmodule rat).
 exact iZrat.                              (*   injT *)
 exact (fun z t =>((iZrat z) * t)).        (* scalar *)
 exact (-%R).                             (* opposite *)
 exact (+%R).                            (* addition *)
 exact (fun x y => x - y).                           (* subtraction *)
 exact Num.Def.ler.                              (* comparison *)
 exact Num.Def.ltr.                              (* comparison *)
Defined.

Theorem Qaxiom: Faxiom Qmodule.
(apply (Build_Faxiom Qmodule);
   lazy beta iota zeta delta 
     [T scalT plusT opT minusT leT ltT Qmodule injT]) =>
  [z1 z2|z1 z2 t|z1 z2 t|t|t1 t2|t1 t2 t3|t1|t1|
   t1|t1 t2||t1 t2 t3 t4||t1 t2 t3 t4|t1 t2 H|t1 H|t1 H]; 
   rewrite ?(Pos2Nat.inj_1, mul1r, mulr1) //=.
- by exact: iZratD.
- by rewrite iZratD mulrDl.
- by rewrite mulrA iZratM.
- by rewrite addr0.
- by rewrite addrC.
- by rewrite addrA.
- by rewrite mulr1n mulNr mul1r subrr.
- by rewrite mulr1n mulNr mul1r.
- by rewrite mulr1n mulNr mul1r.
- by apply: ler_add.
- by apply: ltr_le_add.
- by apply: ltW.
- case: t1 H => //= p _.
  apply/negP; rewrite -ltNge oppr_lt0 ltr0n.
  by apply/ssrnat.ltP/Pos2Nat.is_pos.
case: t1 H => [|p []|p _] //=.
by apply/negP; rewrite -leNgt oppr_le0 ler0n.
Qed.

(********************************************)
(* Test for constant in Q                   *)
(********************************************)


Ltac QCst t :=
 match t with
 | 0%R => constr:(true)
 | 1%R => constr:(true)
 | _%:R => constr:(true)
 | _ => constr:(false)
 end.

Ltac QCstz t :=
 match t with
 | 0%R => constr:(Z_of_nat 0)
 | 1%R=> constr:(Z_of_nat 1)
 | ?x%:R => constr:(Z_of_nat x)
 end.


(********************************************)
(* Belonging in a list for Q                *)
(********************************************)

Ltac qIN a l :=
 match l with
 | (cons a ?l) => constr:(true)
 | (cons _ ?l) => qIN a l
 | _ => constr:(false)
 end.

(********************************************)
(* Adding a variable in a list for Q        *)
(********************************************)

Ltac qAddFv a l :=
 match (qIN a l) with
 | true => constr:(l)
 | _ => constr:(cons a l)
 end.

(********************************************)
(* Adding a variable in a list for Q        *)
(********************************************)


Ltac qFind_at a l :=
 match l with
 | (cons a _) => constr:(O%N) 
 | (cons _ ?l) => let p := qFind_at a l in 
                  let v := constr:(p.+1) in
                  let v1 := eval compute in v in
                  v1
 | _ => constr:(0%N)
 end.

(********************************************)
(* Computing the list of variables for Q    *)
(********************************************)

Ltac qFV t :=
 let rec qTFV t fv :=
  match t with
| False => fv
| ?t1 -> ?g1 =>
       let fv1  := qTFV t1 fv in
       let fv2  := qTFV g1 fv1 in fv2
| is_true (?t1 <= ?t2) =>  
       let fv1  := qTFV t1 fv in
       let fv2  := qTFV t2 fv1 in fv2
| is_true (?t1 < ?t2) =>  
       let fv1  := qTFV t1 fv in
       let fv2  := qTFV t2 fv1 in fv2
| (?t1 = ?t2)%R =>  
       let fv1  := qTFV t1 fv in
       let fv2  := qTFV t2 fv1 in fv2
| (?t1 + ?t2)%R => 
       let fv1  := qTFV t1 fv in
       let fv2  := qTFV t2 fv1 in fv2
| (?t1 * ?t2)%R => 
       match QCst t1 with
        true => let fv1  := qTFV t2 fv in fv1
       end
| (?t1 - ?t2)%R => 
       let fv1  := qTFV t1 fv in
       let fv2  := qTFV t2 fv1 in fv2
| (- ?t1)%R => 
       let fv1  := qTFV t1 fv in fv1
| _ =>
    match QCst t with
    | false => let fv1 := qAddFv t fv in fv1
    | _ => fv
    end
  end
  in qTFV t (@nil rat).

Ltac qlift_term t fv  :=
  match t with
  | False => constr:(@nil equation)
  | ?X -> ?Y =>   let x1 := qlift_term X fv in 
                  let y1 := qlift_term Y fv in 
                  constr:(x1::y1)
  | (?X  = ?Y)%R => let x1 := qlift_term X fv in
                  let y1 := qlift_term Y fv in 
                  constr:(Eq x1 y1)
  | is_true (?X < ?Y)%R  => let x1 := qlift_term X fv in
                  let y1 := qlift_term Y fv in 
                  constr:(Lt x1 y1)
  | is_true (?X <= ?Y)%R => let x1 := qlift_term X fv in
                  let y1 := qlift_term Y fv in 
                  constr:(Le x1 y1)
  | (?X + ?Y)%R => let x := qlift_term X fv in
               let y := qlift_term Y fv in constr:(Plus x y)
  | (?X - ?Y)%R => let x := qlift_term X fv in
               let y := qlift_term Y fv in constr:(Minus x y)
  | (- ?X)%R => let x := qlift_term X fv in constr:(Op x)
  | (?X * ?Y)%R =>
       match QCst X with
        true => 
            let x := QCstz X in
            let y := qlift_term Y fv in constr:(Scal x y)
       end
  | _ =>
    match QCst t with
    | false => let p := qFind_at t fv in constr:(Var p)
    | true => let z := QCstz t in
              let z1 := eval compute in z in constr:(Const z1)
    end
  end.

Lemma fqpush0 (A : Prop) : (A -> False) -> ~ A.
Proof. by []. Qed.

Lemma fqpush0' (A : bool) : (A -> False) -> ~~ A.
Proof. by move=> H1; apply/negP. Qed.

Lemma fqpush1 (x y: rat) : (x <> y-> False) -> x = y.
Proof. by case: (x =P y). Qed.

Lemma fqpush2 (x y: rat) : (y < x -> False) -> x <= y.
Proof. by case: lerP => // _ /(_ isT). Qed.

Lemma fqpush3 (x y: rat) : (y <= x -> False) -> x < y.
Proof. by case: lerP => // _ /(_ isT). Qed.

Ltac isFalse :=
match goal with |- False => idtac end.

Ltac fqpush_concl := intros; 
  first [apply: fqpush1 | apply: fqpush3 | apply: fqpush2 |
         apply: fqpush0' | isFalse | apply: fqpush0 | apply: False_ind ]; intros.

Lemma fqpop1 (x y: rat) : x <> y -> x < y \/ y < x.
Proof.
move=> /eqP xDy; case: ltrP; first by left.
by rewrite le_eqVlt eq_sym (negPf xDy); right.
Qed.

Lemma fqpop1' (x y: rat) : x != y -> x < y \/ y < x.
Proof.
move=> xDy; case: ltrP; first by left.
by rewrite le_eqVlt eq_sym (negPf xDy); right.
Qed.

Lemma fqpop2 (x y: rat) : ~(x <= y) -> y < x.
Proof. by move=> /negP; rewrite ltNge. Qed.

Lemma fqpop3 (x y: rat) : ~(x < y) -> y <= x.
Proof. by move=> /negP H; rewrite leNgt. Qed.


Ltac is_type t a :=
  let tp := type of t in
  let tp' := eval compute in tp in
  match tp' with a => constr:(true) | _ => constr:(false) end.

Ltac fqpop_hyp := match goal with
|  H :   is_true (?X <= ?Y) |- _ => 
     match is_type X rat with true => move: H | _ => idtac end; clear H
|  H :   is_true (?X < ?Y) |- _ =>
     match is_type X rat with true => move: H | _ => idtac end; clear H
|  H :  ~ is_true (?X <= ?Y) |- _ => 
     match is_type X rat with true => move: (fqpop2 _ _ H)| _ => idtac end; clear H
|  H :  ~ is_true (?X < ?Y) |- _ => 
     match is_type X rat with true => move: (fqpop3 _ _ H) | _ => idtac end; clear H
|  H :  ~(?X = ?Y) |- _ =>  
     match is_type X rat with true => case: (fqpop1 _ _ H) | _ => idtac end; clear H
|  H : (?X = ?Y) |- _ => 
     match is_type X rat with true => move: H | _ => idtac end; clear H
|  H : is_true (?X != ?Y) |- _ =>  
     match is_type X rat with true => move/eqP : H => /fqpop1[] | _ => idtac end; clear H
|  H : is_true (?X == ?Y) |- _ => 
     match is_type X rat with true => move: (eqP H) | _ => idtac end; clear H
end.


Lemma fr1 (x y : rat) (n m : nat) :
    (x / n.+1%:R) + (y / m.+1%:R) = ((m.+1%:R) * x + (n.+1%:R)*y) / (n.+1 * m.+1)%:R.
Proof.
by rewrite addf_div ?natrM ?(eqr_nat _ _ 0) // [_ * x]mulrC [_ * y]mulrC.
Qed.

Lemma fr11 (x y : rat) (n : nat) :
    (x / n.+1%:R) + y = (x + (n.+1%:R)*y) / n.+1%:R.
Proof.
by rewrite  {1}(_ : y = y / 1%:R) 1?fr1 ?mul1r ?muln1 // divr1.
Qed.

Lemma fr12 (x y : rat) (n : nat) :
    y + (x / n.+1%:R) = ((n.+1%:R)*y + x) / n.+1%:R.
Proof. by rewrite addrC fr11 addrC. Qed.

Lemma fr2 (x y : rat) (n m : nat) :
    (x / n.+1%:R) * (y / m.+1%:R) = (x * y) / (n.+1 * m.+1)%:R.
Proof. by rewrite mulf_div natrM. Qed.

Lemma fr21 (x y : rat) (n : nat) :
    (x / n.+1%:R) * y  = (x * y) / (n.+1)%:R.
Proof. by rewrite  {1}(_ : y = y / 1%:R) 1?fr2 ?mul1r ?muln1 // divr1. Qed.

Lemma fr22 (x y : rat) (n : nat) :
    y * (x / n.+1%:R)  = (y * x) / (n.+1)%:R.
Proof. by rewrite mulrC fr21 [x * _]mulrC. Qed.

Lemma fr3 (x : rat) (n : nat) : -(x /n.+1%:R) = (- x) / n.+1%:R.
Proof. by rewrite -mulNr. Qed.

Lemma fr5 (x y : rat) (m n : nat) : 
 x / m.+1%:R  =  y / (n.+1)%:R -> n.+1%:R * x =   m.+1%:R * y.
Proof. 
by move=> /eqP; rewrite eqr_div ?(eqr_nat _ _ 0) // ![_ * _%:R]mulrC => /eqP.
Qed.

Lemma fr5b (x y : rat) (m n : nat) : 
n.+1%:R * x =   m.+1%:R * y -> x / m.+1%:R  =  y / (n.+1)%:R.
Proof.
move=> H; apply/eqP; rewrite eqr_div ?(eqr_nat _ _ 0) // ![_ * _%:R]mulrC.
by apply/eqP.
Qed.

Lemma fr6 (x y : rat) (m n : nat) : 
 x / m.+1%:R  <=  y / (n.+1)%:R -> n.+1%:R * x <=  m.+1%:R * y.
Proof. 
rewrite ler_pdivr_mulr ?(ltr_nat _ 0) //.
by rewrite mulrC mulrA ler_pdivl_mulr  ?[_ * _%:R]mulrC // (ltr_nat _ 0).
Qed.

Lemma fr6b (x y : rat) (m n : nat) : 
 n.+1%:R * x <=  m.+1%:R * y -> x / m.+1%:R  <=  y / (n.+1)%:R.
Proof. 
move=> H.
rewrite ler_pdivr_mulr ?(ltr_nat _ 0) //.
by rewrite mulrC mulrA ler_pdivl_mulr  ?[_ * _%:R]mulrC // (ltr_nat _ 0).
Qed.

Lemma fr7 (x y : rat) (m n : nat) : 
 x / m.+1%:R  <  y / (n.+1)%:R -> n.+1%:R * x <  m.+1%:R * y.
Proof. 
rewrite ltr_pdivr_mulr ?(ltr_nat _ 0) //.
by rewrite mulrC mulrA ltr_pdivl_mulr  ?[_ * _%:R]mulrC // (ltr_nat _ 0).
Qed.

Lemma fr7b (x y : rat) (m n : nat) : 
n.+1%:R * x <  m.+1%:R * y -> x / m.+1%:R  <  y / (n.+1)%:R.
Proof.
move=> H.
rewrite ltr_pdivr_mulr ?(ltr_nat _ 0) //.
by rewrite mulrC mulrA ltr_pdivl_mulr  ?[_ * _%:R]mulrC // (ltr_nat _ 0).
Qed.

Definition frC n : rat := n.+1%:R.

Lemma frCI n : n.+1%:R = frC n.
Proof. by []. Qed.

Lemma frE n : frC n = (locked n).+1%:R :> rat.
Proof. by unlock. Qed.

Ltac lift_rat := 
rewrite -?natrM ?frCI ?frE;
repeat match goal with 
| |- context [?x / ?n.+1%:R + ?y / ?m.+1%:R] =>
   rewrite (fr1 x y n m)
| |- context [?x / ?n.+1%:R + ?y] =>
   rewrite (fr11 x y n)
| |- context [?y + ?x / ?n.+1%:R] =>
   rewrite (fr12 x y n)
| |- context [?x / ?n.+1%:R * (?y / ?m.+1%:R)] =>
   rewrite (fr2 x y n m)
| |- context [?x / ?n.+1%:R * ?y] =>
   rewrite (fr21 x y n)
| |- context [?y * (?x / ?n.+1%:R)] =>
   rewrite (fr22 x y n)
| |- context [- (?x / ?n.+1%:R)] =>
   rewrite (fr3 x n)
end;
unlock.

Ltac rm_rat := 
repeat (
let H := fresh "H" in
match goal with 
| |- _ / _ = _ / _ -> _ => try (move/fr5); intro H
| |- is_true(_ / _ <= _ / _) -> _ => try (move/fr6); intro H
| |- is_true(_ / _ < _ / _) -> _ =>  try (move/fr7); intro H
| |- _ -> _ => intro H
| |- _ / _ = _ / _  => apply: fr5b
| |- is_true(_ / _ <= _ / _) => apply: fr6b
| |- is_true(_ / _ < _ / _) =>  apply: fr7b
end).

Ltac qfourier :=
fqpush_concl; repeat fqpop_hyp; rat_to_ring; lift_rat;
rm_rat; repeat fqpop_hyp;
match goal with |- ?X  => 
let fv0 := qFV X in 
let fv := eval lazy in fv0 in
let t := qlift_term X fv in
let v := constr:(refute (equations_to_dt Qmodule t fv)) in
let vv := eval vm_compute in v in
match vv with true =>
  vm_cast_no_check (equations_cor _ Qaxiom t fv (refl_equal _)) 
| false => fail
end
end.
