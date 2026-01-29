(***********************************************************)
(*      This file contains a direct implementation with no *)
(*      optimisation of Fourier-Mozkin algorithm. We use   *)
(*      it to show that a system is unsolvable             *)
(***********************************************************)

From Stdlib Require Import ZArith Znumtheory List.
Require Import FourierConcTerm.

(***********************************************************)
(* We first describe the algorithm then its partial        *)
(* correctness proof                                       *)
(***********************************************************)

(***********************************************************)
(* The implementation is naive. The set of inequations is  *)
(* as a matrices (i.e a list of list of integers), the     *)
(* constant part of the equation is separated in order to  *)
(* make variable elimination only for the variables part   *)
(* A sparse representation should be more sensible but     *)
(* anyway Fourier is not a good choice for large problems  *)
(*                                                         *)
(* A line of the inequation contains the list of the       *)
(* coefficients of the variable and a constant.            *)
(* For example                                             *)
(* 3x + z >= 4 is encoded as line (3::0::1::nil) -4 lLe    *)
(*  x + y >  2 is encoded as line (1::1::0::nil) -2 lLt    *)
(*  x = y      is encoded as line (1::-1::0::nil) 0 lEq    *)
(***********************************************************)
Inductive ltype : Type := lEq | lLt | lLe.
Inductive line : Type := Line (_: list Z) (_: Z) (_:ltype).

(* A system is a list of line *)
Definition dt := list line.

(* An example
      3x + y - z >= 0
      2x     + z >= 2
      -x + y + z >= 0
*)
Definition ex1 :=    Line (3::1::-1::nil)%Z 0 lLe::
                     Line (2::0::1::nil)%Z (-2) lLe :: 
                     Line (-1::1::1::nil)%Z 0 lLe ::nil.

(* How line types combine *)

Definition lmerge t1 t2 :=
  match t1 with
    lEq => t2
  | lLt => t1
  | lLe => match t2 with lLt => t2 | _ => t1 end
  end.

(* Some check *)
Lemma lmerge_id: forall t, lmerge t t = t.
Proof. intro t; destruct t; auto. Qed.

Lemma lmerge_sym: forall t1 t2, lmerge t1 t2 = lmerge t2 t1.
Proof. intros t1 t2; destruct t1; destruct t2; auto. Qed.


(***********************************************************)
(*  Splitting the system in 3 depending of the top coef    *)
(*    the positive part, the negative one, the zero one    *)
(***********************************************************)

(* The split datastructure *)
Inductive op_eq : Type :=
  | Some_eq (_: positive) (_: list Z) (_: Z)
  | No_eq.

Inductive dt4 :Type := DT4 (_: op_eq) (_ _ _: dt). 
(* Empty split *)
Definition nil_dt4 := DT4 No_eq nil nil nil.

(* Add an element in the zero part *)
Definition add4z l (v: dt4) : dt4 :=
  let (e,lp,ln,lz) := v in DT4 e lp ln (l::lz). 
(* Add an element in the positive part *)
Definition add4p l (v: dt4) : dt4 :=
  let (e,lp,ln,lz) := v in DT4  e (l::lp) ln lz.
(* Add an element in the negative part *)
Definition add4n l (v: dt4) : dt4 :=
  let (e,lp,ln,lz) := v in DT4  e lp (l::ln) lz.
(* Add an element in the equation part *)
Definition add4e p l c (v: dt4) : dt4 :=
  let (e,lp,ln,lz) := v in 
  match e with 
    No_eq => DT4 (Some_eq p l c) lp ln lz
  | Some_eq p1 l1 c1 =>
     match (p ?= p1)%positive with
       Lt => DT4 (Some_eq p l c) (Line (Zpos p1::l1) c1 lEq::lp) ln lz
    |  _  => DT4 e (Line (Zpos p::l) c lEq::lp) ln lz
    end
  end.

Fixpoint oppsm (l: list Z): list Z :=
  match l with nil => nil | v :: l1 => -v :: oppsm l1 end.

(* Splitting in a tail recursive way *)
Fixpoint split_aux (v: dt) (r: dt4) {struct v}: dt4 :=
  match v with 
    nil => r
  | Line nil _ _ as l::v1 => split_aux v1 r
  | Line (0%Z::l1) c t as l::v1 => 
      split_aux v1 (add4z (Line l1 c t) r)
  | Line (Zpos p::l1) c1 lEq :: v1 => 
      split_aux v1 (add4e p l1 c1 r)
  | Line (Zneg p::l1) c1 lEq :: v1 => 
      split_aux v1 (add4e p (oppsm l1) (-c1) r) 
  | Line (Zpos _::_) _ _  as l ::v1 => 
      split_aux v1 (add4p l r)
  | Line (Zneg x::l1) c e as l ::v1 => 
      split_aux v1 (add4n (Line (Zpos x :: l1) c e) r)
  end.

Definition split v := split_aux v nil_dt4.

(*
Eval vm_compute in split ex1.
*)

(***********************************************************)
(*  Adding the product of the positive and negative parts  *)
(*  to the zero part removing the top variable             *)
(***********************************************************)

Fixpoint mapsm (v: Z) (l: list Z) {struct l}: list Z :=
  match l with nil => nil | v1 :: l1 => (v * v1) :: mapsm v l1 end.

Fixpoint merge (v1 v2: Z) (l1 l2: list Z) {struct l1}: list Z :=
  match l1 with
    nil => mapsm v2 l2
  | v3:: l3 => match l2 with
                 nil => mapsm v1 l1
               | v4:: l4 => (v1*v3 + v2*v4) :: merge v1 v2 l3 l4
               end
  end.

Fixpoint app_one (v c: Z) (op: ltype) (l: list Z) (l1: dt) (r: dt) 
     {struct l1} :=
  match l1 with
    nil => r
  | (Line nil _  _  as a)::l2 => app_one v c op l l2 (a :: r)
  | (Line (v1::ll2) c1 op1)::l2 =>
        let v2 := Z.gcd v v1 in
        let k1 := v1/v2 in
        let k2 := v/v2 in
           app_one v c op l l2 
              (Line (merge k1 k2 l ll2) (k1 * c + k2 * c1)
                        (lmerge op op1) :: r)
  end.

Fixpoint product (l1 l2: dt) (r: dt) {struct l1} : dt :=
  match l1 with 
    nil => r
  | (Line (v::l) c lLt)::l3 => product l3 l2 (app_one v c lLt l l2 r)
  | (Line (v::l) c lLe)::l3 => product l3 l2 (app_one v c lLe l l2 r)
  | _ ::l3 => product l3 l2 r
  end.


(***********************************************************)
(*  Refuting by eliminating variables one by one           *)
(***********************************************************)

(* elim one variable *)
Definition elim_one v : dt :=
  match split v with
    DT4 No_eq x y z => product x y z
  | DT4 (Some_eq p l c) x y z => 
     app_one (Zpos p) (-c) lEq (oppsm l) x
       (app_one (Zpos p) c lEq l y z)
  end.

(* a system is unsolvable if there one constant negative element *)
Fixpoint unsolvable d :=
  match d with 
    nil => false
  | Line nil (Zneg _) lLe::_ => true
  | Line nil (0%Z) lLt::_ => true
  | Line nil (Zneg _) lLt::_ => true
  | Line nil (Zpos _) lEq::_ => true
  | Line nil (Zneg _) lEq::_ => true
  | _::d1 => unsolvable d1
  end.

(* we use a clause to count how many variable to eliminate *)
Fixpoint refute_l (a: list Z) (v: dt) :=
  match a with 
  | nil => unsolvable v 
  | _::b  => refute_l b (elim_one v)
  end.

(* extract the first clause *)
Definition first_clause (v: dt) :=
  match v with nil => nil | Line a _ _::_ => a end.

Definition refute (v: dt) := refute_l (first_clause v) v.

(*
Eval vm_compute in refute   (Line (1::nil) 0 lLe::
                             Line (-1::nil) (-0) lLt ::nil).
*)

(*
Eval vm_compute in refute ex1.
*)

(*
(* x >=0 and -x -1 <= 0 *)
Eval vm_compute in refute (Line (1::nil) 0 lLe::
                           Line (-1::nil) (-1) lLe ::nil).
*)

(***********************************************************)
(*                                                         *)
(*                   Proving Part                          *)
(*                                                         *)
(***********************************************************)

Section Proof.

Variable FT : Fmodule.
Variable FA : Faxiom FT.

Let injT1 := (injT FT).
Coercion injT1 : Z >-> T.

Open Scope F_scope.

(* Change the top coefficient of the line *)
Definition swap_top l := match l with
  |  Line nil _ _ => l
  |  Line (p::l1) c eq  => Line ((-p)::l1) c eq
end.

(* Change the top coefficient of the line *)
Definition op_line l := match l with
  |  Line l1 c t  => Line (oppsm l1) (-c) t
end.

(************************************************************)
(*          Line interpretation                             *)
(************************************************************)

Fixpoint list_to_T (l1: list Z) (l2: list (T _)) {struct l1} : T _ :=
  match l1, l2 with
    a::l3, x::l4 => a * x  + (list_to_T l3 l4)
  | _, _ => 0
  end.

Lemma list_to_T_nil: forall l1, list_to_T l1 nil = 0.
Proof.
intros l1; destruct l1; simpl; auto.
Qed.

Definition line_to_T (l: line) (env: list (T _)) :=
  match l with
    Line ll c lEq => (0:T _) = (list_to_T ll env) + c
  | Line ll c lLe => 0 <= (list_to_T ll env) + c
  | Line ll c lLt => 0 < (list_to_T ll env) + c
  end.

(* Dealing with opposite *)

Lemma opp_opp: forall (a: Z), -(-a) = a.
Proof. intros a; case a; auto. Qed.

Lemma opp_oppsm: forall l, oppsm (oppsm l) = l.
Proof.
intro l; induction l as [|a l Hrec]; simpl; auto.
rewrite Hrec; rewrite opp_opp; auto.
Qed.


Lemma list_to_T_opp: forall l env,
  list_to_T (oppsm l) env = (-1) * (list_to_T l env).
Proof.
intros l; induction l as [|v l Hrec]; simpl.
unfold injT1; rewrite scalT_inj0; auto.
intros [|e env].
unfold injT1; rewrite scalT_inj0; auto.
rewrite Hrec; rewrite scalT_plus_r; auto.
rewrite <-scalT_mul; auto.
Qed.

Lemma line_to_T_opp: forall l c env,
  line_to_T (Line l c lEq) env ->
  line_to_T (Line (oppsm l) (- c) lEq) env.
Proof.
unfold line_to_T; intros l c env H1.
rewrite list_to_T_opp.
change (Z.opp c) with (-1 * c)%Z.
unfold injT1; rewrite injT_mul; auto.
rewrite <- scalT_plus_r; auto.
fold injT1; rewrite <- H1.
unfold injT1; rewrite scalT_inj0; auto.
Qed.

(* All the elements of the dt are verified *)
Definition Pdt d env := forall a, In a d -> line_to_T a env.

(* All the element of the dt are verified with the flip of
   the first element  *)
Definition Pdot d env := forall a, In a d -> line_to_T (swap_top a) env.

(* Length of the variable part of a line *)
Definition llength l :=
  match l with Line w _ _ => length w end.

(************************************************************)
(*          Split correctness                               *)
(************************************************************)


(* the split only shuffle things around but we restrict
   ourself to prove inclusion *)

(* Special inclusion to handle the fact that
   we store only positive equation 
*)
Inductive InE: line -> dt -> Prop :=
  InE_base: forall i b, In i b -> InE i b
| InE_eq: forall l c b, 
     In (Line l c lEq) b -> InE (Line (oppsm l) (-c) lEq) b.

(* Absolute value like lemma for InE *)
Lemma InE_opp: forall l c b,
   InE (Line l c lEq) b -> InE (Line (oppsm l) (-c) lEq) b.
Proof.
intros l c b HH; inversion_clear HH.
apply InE_eq; auto.
rewrite opp_opp; rewrite opp_oppsm; auto.
apply InE_base; auto.
Qed.

Lemma InE_line_to_T: forall i d env,
  InE i d -> Pdt d env -> line_to_T i env.
Proof.
intros i d env HH; inversion_clear HH; auto.
intros H1; apply line_to_T_opp; auto.
Qed.

Definition dincl (a b: dt) (f: line -> line) := 
  forall i, In i a -> InE (f i) b.
(* identity filter *)
Definition id_elt (l: line) := l.
(* removing filter *)
Definition rm_elt l :=
  match l with Line l1 c eq => Line (0::l1) c eq end.

(* Inclusion behave well with correctness *)
Lemma Pdt_incl_id: forall d1 d2 env,
  dincl d1 d2 id_elt -> Pdt d2 env -> Pdt d1 env.
Proof.
intros d1 d2 env Hinc Hd2 i Hi.
apply InE_line_to_T with (2 := Hd2); auto.
apply (Hinc i Hi).
Qed.

Lemma Pdt_incl_op: forall d1 d2 env,
  dincl d1 d2 swap_top -> Pdt d2 env -> Pdot d1 env.
Proof.
intros d1 d2 env Hinc Hd2 i Hi.
apply InE_line_to_T with (2 := Hd2); auto.
Qed.

Lemma line_to_T_tail: forall i env,
  line_to_T (rm_elt i) env -> line_to_T i (tail env).
Proof.
intros [l c t] [| e env]; simpl; 
  try (rewrite scalT_0; auto; rewrite injT_0_l; auto);
  rewrite list_to_T_nil; auto.
Qed.

Lemma InE_tail_line_to_T: forall i d env,
  InE (rm_elt i) d -> Pdt d env ->  line_to_T i (tail env).
Proof.
intros i d env HI Hp; apply line_to_T_tail.
apply InE_line_to_T with (2 := Hp); auto.
Qed.

Lemma Pdt_incl_rm: forall d1 d2 env,
  dincl d1 d2 rm_elt -> Pdt d2 env -> Pdt d1 (tail env).
Proof.
intros d1 d2 env Hinc Hd2 i Hi.
apply InE_tail_line_to_T with (2 := Hd2); auto.
Qed.

Definition d4incl (a: dt4) (b: dt) := 
  match a with 
    DT4 No_eq d1 d2 d3 =>
      (dincl d1 b id_elt) 
   /\ (dincl d2 b swap_top) 
   /\ (dincl d3 b rm_elt)
  | DT4 (Some_eq p l c) d1 d2 d3 =>
      InE (Line (Zpos p::l) c lEq) b 
   /\ (dincl d1 b id_elt) 
   /\ (dincl d2 b swap_top) 
   /\ (dincl d3 b rm_elt)
      
  end. 

(* Horrible copy and paste proof, as we have to split  *)
(* similar cases (lLt lLe) we get similar subproofs    *)
(* This could be abstract away                         *)
Lemma split_aux_cor: forall v v1 (r: dt4),
  dincl v v1 id_elt -> d4incl r v1 -> d4incl (split_aux v r) v1.
Proof.
intro v; induction v as [| a v Hrec]; intros v1 r; simpl; auto.
destruct a as [x c t]; destruct x as [| x xs].
intros H1 H2; apply Hrec; auto with datatypes.
intros u Hu; apply H1; auto with datatypes.
destruct x as [|x|x]; intros H1 H2.
 apply Hrec; auto with datatypes;
  try (intros u Hu; apply H1; auto with datatypes).
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5));
  repeat split; auto.
intros i Hi; case Hi; auto; intros; subst.
simpl; apply (H1 (Line (0 :: xs) c t)); auto with datatypes.
case H2; clear H2; intros H2 (H3,H4);
  repeat split; auto.
intros i Hi; case Hi; auto; intros; subst.
simpl; apply (H1 (Line (0 :: xs) c t)); auto with datatypes.
destruct t; auto; apply Hrec;
  try (intros u Hu; apply H1; auto with datatypes).
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5)).
case Pos.compare_spec; repeat split; simpl; auto with datatypes.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
refine (H1 _ _); auto with datatypes.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
case H2; clear H2; intros H2 (H3,H4); repeat split; auto.
refine (H1 _ _); auto with datatypes.
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5)).
repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
case H2; clear H2; intros H2 (H3,H4);
  repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5)).
repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
case H2; clear H2; intros H2 (H3,H4); repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
destruct t; auto; apply Hrec;
  try (intros u Hu; apply H1; auto with datatypes).
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5)).
case Pos.compare_spec; repeat split; simpl; auto with datatypes.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
change (Zpos p :: oppsm xs) with (oppsm (Zneg p:: xs)); unfold id_elt.
apply InE_opp; refine (H1 _ _); auto with datatypes.
change (Zpos x :: oppsm xs) with (oppsm (Zneg x:: xs)); unfold id_elt.
apply InE_opp; refine (H1 _ _); auto with datatypes.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
change (Zpos x :: oppsm xs) with (oppsm (Zneg x:: xs)); unfold id_elt.
apply InE_opp; refine (H1 _ _); auto with datatypes.
case H2; clear H2; intros H2 (H3,H4); repeat split; auto.
change (Zpos x :: oppsm xs) with (oppsm (Zneg x:: xs)); unfold id_elt.
apply InE_opp; refine (H1 _ _); auto with datatypes.
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5)).
repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
refine (H1 _ _); auto with datatypes.
case H2; clear H2; intros H2 (H3,H4); repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
refine (H1 _ _); auto with datatypes.
destruct r as [e w1 w2 w3]; destruct e; simpl.
case H2; clear H2; intros H2 (H3,(H4,H5)).
repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
refine (H1 _ _); auto with datatypes.
case H2; clear H2; intros H2 (H3,H4); repeat split; auto.
intros i Hi; case Hi; auto; intros; subst; simpl; auto with datatypes.
refine (H1 _ _); auto with datatypes.
Qed.

Lemma split_cor: forall v, d4incl (split v) v.
Proof.
intros v; unfold split; apply split_aux_cor.
intros i Hi; apply InE_base; auto.
repeat split; intros i Hi; inversion Hi.
Qed.

Definition d4pos (a: dt4) := 
  match a with DT4 _ dp dn _ =>
      (forall x l c t, In (Line (x::l) c t) dp -> (0 < x)%Z)
   /\ (forall x l c t, In (Line (x::l) c t) dn -> (0 < x)%Z)
  end.

(* Another copy and paste proof *)
Lemma split_aux_pos: forall v r, 
  d4pos r -> d4pos (split_aux v r).
Proof.
intro v; induction v as [| a v Hrec];
  intros (w1,w2,w3,w4) (H1,H2); repeat split; auto.
destruct a as [[|[|x|x] l] c t]; simpl.
 apply Hrec; repeat split; auto with datatypes.
 apply Hrec; repeat split; auto with datatypes.
destruct t; simpl; apply Hrec.
destruct w1.
case Pos.compare_spec.
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
destruct t; simpl; apply Hrec.
destruct w1.
case Pos.compare_spec.
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H1 with (1 := H3).
repeat split; simpl; auto with datatypes.
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H2 with (1 := H3).
repeat split; simpl; auto with datatypes.
intros x1 l1 c1 t1 Hx1; case Hx1; auto; intros H3.
injection H3; intros; subst; red; simpl; auto.
apply H2 with (1 := H3).
Qed.

Lemma split_pos: forall v, d4pos (split v).
Proof.
intros v; unfold split; apply split_aux_pos.
repeat split; intros i l c t Hi; inversion Hi.
Qed.

(************************************************************)
(*          Product correctness                             *)
(************************************************************)

Lemma mapsm_cor: forall v l env,
  list_to_T (mapsm v l) env = v * list_to_T l env.
Proof.
intros v l; induction l as [| v1 l2 Hrec]; intros env; simpl; auto.
unfold injT1; rewrite scalT_inj0; auto.
destruct env as [| y env].
unfold injT1; rewrite scalT_inj0; auto.
rewrite scalT_plus_r; auto; rewrite Hrec; rewrite scalT_mul; auto.
Qed.

Lemma merge_cor: forall v1 v2 l1 l2 env,
  list_to_T (merge v1 v2 l1 l2) env = 
   v1 * list_to_T l1 env + v2 * list_to_T l2 env.
Proof.
intros v1 v2 l1; induction l1 as [| w1 l1 Hrec]; intros l2 env; simpl; auto.
rewrite mapsm_cor; unfold injT1; rewrite scalT_inj0; auto; rewrite injT_0_l; auto.
destruct l2 as [| w2 l2]; destruct env as [| x env]; simpl;
  unfold injT1; repeat rewrite scalT_inj0; repeat rewrite injT_0_r; auto.
rewrite mapsm_cor; rewrite scalT_plus_r; auto; rewrite scalT_mul; auto.
rewrite Hrec.
repeat rewrite scalT_plus_r; repeat rewrite scalT_plus_l; auto.
rewrite scalT_mul; repeat rewrite plusT_A; auto; 
  apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto;
  apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite scalT_mul; auto.
Qed.

Lemma dt_dot_nil: forall l, Pdt l nil -> Pdot l nil.
Proof.
intros l H i Hi; simpl.
generalize (H _ Hi); destruct i as [[|x w] c]; auto.
Qed.
 
Lemma Zgcd_spos: forall x y, (0 < x -> 0 < y -> 0 < Z.gcd x y)%Z.
Proof.
intros x y; case x; case y; auto with zarith.
Qed.

Lemma Zgcd_div_spos_l: forall x y, (0 < x -> 0 < y -> 0 < x/Z.gcd x y)%Z.
Proof.
intros x y Hx Hy; destruct (Zgcd_is_gcd x y) as [[z Hz] _ _].
pattern x at 1; rewrite Hz; rewrite Z_div_mult.
generalize Hx (Zgcd_spos _ _ Hx Hy); pattern x at 1; rewrite Hz.
case z; case Z.gcd; intros; auto with zarith; discriminate.
apply Z.lt_gt; apply Zgcd_spos; auto with zarith.
Qed.

Lemma Zgcd_div_spos_r: forall x y, (0 < x -> 0 < y -> 0 < y/ Z.gcd x y)%Z.
Proof.
intros x y Hx Hy; destruct (Zgcd_is_gcd x y) as [_ [z Hz] _].
pattern y at 1; rewrite Hz; rewrite Z_div_mult.
generalize Hy (Zgcd_spos _ _ Hx Hy); pattern y at 1; rewrite Hz.
case z; case Z.gcd; intros; auto with zarith; discriminate.
apply Z.lt_gt; apply Zgcd_spos; auto with zarith.
Qed.

Lemma app_one_cor: forall v c t l l1 r env,
  (0 < v)%Z -> (forall x ll c t, In (Line (x::ll) c t) l1 -> (0 < x)%Z) ->
  Pdt r (tail env) -> line_to_T (Line (v::l) c t) env ->
  Pdot l1 env ->
   Pdt (app_one v c t l l1 r) (tail env).
Proof.
intros v c t l l1; induction l1 as [| (li,c1,t1) l1 Hrec]; intros r env;
  destruct env as [| e env]; simpl; auto; destruct li as [|x li]; simpl; auto.
intros Hv Hl1 H1 H2 H3; apply (fun x => Hrec x nil); simpl; auto.
intros x ll cc tt Hx; apply (fun x => Hl1 x ll cc tt); auto.
intros i; simpl; intros [Hi | Hi]; subst; auto.
apply (H3 (Line nil c1 t1)); auto with datatypes.
intros i Hi; apply H3; auto with datatypes.
intros Hv Hl1 H1 H2 H3.
assert (Hxp: (0 < x)%Z).
  apply (fun x => Hl1 x li c1 t1); auto.
assert (Hzx:= Zgcd_div_spos_r _ _ Hv Hxp).
assert (Hzv:= Zgcd_div_spos_l _ _ Hv Hxp).
apply (fun x => Hrec x nil); simpl; auto.
intros x1 ll cc tt Hx; apply (fun x => Hl1 x ll cc tt); auto.
intros i; simpl; intros [Hi | Hi]; subst; simpl; auto.
rewrite merge_cor; repeat rewrite list_to_T_nil.
unfold injT1; repeat rewrite scalT_inj0; repeat (rewrite injT_0_l in H2,H3 |- *);
  repeat rewrite injT_0_l; auto.
rewrite injT_plus; repeat rewrite injT_mul; auto.
cut (line_to_T (swap_top (Line (x :: li) c1 t1)) nil); auto with datatypes.
destruct t; destruct t1; simpl; auto; unfold injT1 in H2 |- *; 
  rewrite injT_0_l in H2; auto; try rewrite <- H2; auto;
  repeat rewrite scalT_inj0; repeat rewrite injT_0_l; auto; intros H4.
rewrite <- H4; rewrite scalT_inj0; auto.
apply scalT_spos; auto.
apply scalT_pos; auto with zarith.
rewrite <- H4; rewrite scalT_inj0; auto.
rewrite injT_0_r; auto.
apply scalT_spos; auto.
apply plusTss_pos; auto; apply scalT_spos; auto.
apply plusTs1_pos; auto; try apply scalT_spos; auto;
  apply scalT_pos; auto with zarith.
rewrite <- H4; rewrite scalT_inj0; auto.
rewrite injT_0_r; auto.
apply scalT_pos; auto with zarith.
apply plusT1s_pos; auto; try apply scalT_spos; auto;
  apply scalT_pos; auto with zarith.
apply plusT_pos; auto; apply scalT_pos; auto with zarith.
intros i Hi; auto with datatypes.
intros Hv Hl1 H1 H2 H3.
apply (fun x => Hrec x (e::env)); simpl; auto.
intros x ll cc tt Hcc; apply (Hl1 x ll cc tt); auto.
intros i; simpl; intros [Hi | Hi]; subst; simpl; auto.
apply (H3 (Line nil c1 t1)); auto with datatypes.
intros i Hi; apply (H3 i); auto with datatypes.
intros Hv Hl1 H1 H2 H3.
assert (Hxp: (0 < x)%Z).
  apply (fun x => Hl1 x li c1 t1); auto.
assert (Hzx:= Zgcd_div_spos_r _ _ Hv Hxp).
assert (Hzv:= Zgcd_div_spos_l _ _ Hv Hxp).
apply (fun x => Hrec x (e::env)); simpl; auto.
intros xx ll cc tt Hcc; apply (Hl1 xx ll cc tt); auto.
intros i; simpl; intros [Hi|Hi]; subst; simpl; auto.
rewrite merge_cor.
match goal with |- context[?X + ?Y] =>
  replace (X + Y) with 
    ((x / Z.gcd v x) * (v * e + list_to_T l env + c) +
     (v / Z.gcd v x) * (- x * e + list_to_T li env + c1))
end.
cut (line_to_T (swap_top (Line (x :: li) c1 t1)) (e::env)); auto with datatypes.
destruct t; destruct t1; simpl; auto; unfold injT1 in H2 |- *; 
  auto; try rewrite <- H2; auto;
  repeat rewrite scalT_inj0; repeat rewrite injT_0_l; auto; intros H4.
rewrite <- H4; rewrite scalT_inj0; auto.
apply scalT_spos; auto.
apply scalT_pos; auto with zarith.
rewrite <- H4; rewrite scalT_inj0; auto.
rewrite injT_0_r; auto.
apply scalT_spos; auto.
apply plusTss_pos; auto; apply scalT_spos; auto.
apply plusTs1_pos; auto; try apply scalT_spos; auto;
  apply scalT_pos; auto with zarith.
rewrite <- H4; rewrite scalT_inj0; auto.
rewrite injT_0_r; auto.
apply scalT_pos; auto with zarith.
apply plusT1s_pos; auto; try apply scalT_spos; auto;
  apply scalT_pos; auto with zarith.
apply plusT_pos; auto; apply scalT_pos; auto with zarith.
repeat rewrite scalT_plus_r; auto.
repeat rewrite plusT_A; auto; rewrite plusT_C; repeat rewrite plusT_A; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
unfold injT1; rewrite injT_plus; repeat rewrite injT_mul; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
rewrite <- (injT_0_r); auto.
apply f_equal2 with (f := plusT FT); auto.
repeat rewrite <- scalT_mul; auto.
replace (x / Z.gcd v x * v)%Z with (v / Z.gcd v x * x)%Z.
replace (v / Z.gcd v x * - x)%Z with ((-1) * (v / Z.gcd v x * x))%Z; try ring.
rewrite (scalT_mul _ FA (-1)%Z); rewrite plusT_0; auto.
assert (Hdv: ((Z.gcd v x) | v)%Z).
assert (Hz:= (Zgcd_is_gcd v x)); inversion Hz; auto.
case Hdv; intros q Hq; pattern v at 1 4; rewrite Hq.
rewrite Z_div_mult.
assert (Hdx: ((Z.gcd v x) | x)%Z).
assert (Hz:= (Zgcd_is_gcd v x)); inversion Hz; auto.
case Hdx; intros q1 Hq1; pattern x at 1 2; rewrite Hq1.
rewrite Z_div_mult; try ring.
apply Z.lt_gt; apply Zgcd_spos; auto.
apply Z.lt_gt; apply Zgcd_spos; auto.
intros i Hi; apply (H3 i); auto with datatypes.
Qed.

(* Special case for elimination of the positive part with an equation *)
Lemma app_one_cor_eq: forall v c l l1 r env,
  (0 < v)%Z -> (forall x ll c t, In (Line (x::ll) c t) l1 -> (0 < x)%Z) ->
  Pdt r (tail env) -> line_to_T (Line (-v::l) c lEq) env ->
  Pdt l1 env ->
   Pdt (app_one v c lEq l l1 r) (tail env).
Proof.
intros v c l l1; induction l1 as [| (li,c1,t1) l1 Hrec]; intros r env;
  destruct env as [| e env]; simpl; auto; destruct li as [|x li]; simpl; auto.
intros Hv Hl1 H1 H2 H3; apply (fun x => Hrec x nil); simpl; auto.
intros x ll cc tt Hx; apply (fun x => Hl1 x ll cc tt); auto.
intros i; simpl; intros [Hi | Hi]; subst; auto.
apply (H3 (Line nil c1 t1)); auto with datatypes.
intros i Hi; apply H3; auto with datatypes.
intros Hv Hl1 H1 H2 H3.
unfold injT1 in H2; rewrite injT_0_l in H2; auto.
assert (Hxp: (0 < x)%Z).
  apply (fun x => Hl1 x li c1 t1); auto.
assert (Hzx:= Zgcd_div_spos_r _ _ Hv Hxp).
assert (Hzv:= Zgcd_div_spos_l _ _ Hv Hxp).
apply (fun x => Hrec x nil); simpl; auto.
intros x1 ll cc tt Hx; apply (fun x => Hl1 x ll cc tt); auto.
intros i; simpl; intros [Hi | Hi]; subst; simpl; auto.
rewrite merge_cor; repeat rewrite list_to_T_nil.
cut (line_to_T (Line (x :: li) c1 t1) nil); auto with datatypes; simpl.
unfold injT1; repeat rewrite scalT_inj0; repeat (rewrite injT_0_l in H2,H3 |- *);
  auto.
repeat rewrite injT_0_l; auto.
rewrite injT_plus; repeat rewrite injT_mul; auto.
destruct t1; simpl; intros H4;
  try (rewrite <- H2); try (rewrite <-H4); 
  repeat rewrite scalT_inj0; auto;
  try (rewrite injT_0_r); try (rewrite injT_0_l); auto.
apply scalT_spos; auto.
apply scalT_pos; auto with zarith.
unfold injT1; rewrite <- H2; rewrite injT_0_r; auto.
intros i Hi; auto with datatypes.
intros Hv Hl1 H1 H2 H3.
apply (fun x => Hrec x (e::env)); simpl; auto.
intros x ll cc tt Hcc; apply (Hl1 x ll cc tt); auto.
intros i; simpl; intros [Hi | Hi]; subst; simpl; auto.
apply (H3 (Line nil c1 t1)); auto with datatypes.
intros i Hi; apply (H3 i); auto with datatypes.
intros Hv Hl1 H1 H2 H3.
apply (fun x => Hrec x (e::env)); simpl; auto.
intros xx ll cc tt Hcc; apply (Hl1 xx ll cc tt); auto.
intros i; simpl; intros [Hi|Hi]; subst; simpl; auto.
rewrite merge_cor.
assert (Hxp: (0 < x)%Z).
  apply (fun x => Hl1 x li c1 t1); auto.
assert (Hzx:= Zgcd_div_spos_r _ _ Hv Hxp).
assert (Hzv:= Zgcd_div_spos_l _ _ Hv Hxp).
match goal with |- context[?X + ?Y] =>
  replace (X + Y) with 
    ((x / Z.gcd v x) * (-v * e + list_to_T l env + c) +
     (v / Z.gcd v x) * (x * e + list_to_T li env + c1))
end.
cut (line_to_T (Line (x :: li) c1 t1) (e::env)); auto with datatypes.
destruct t1; simpl; auto; unfold injT1 in H2 |- *; 
  auto; try rewrite <- H2; auto;
  repeat rewrite scalT_inj0; repeat rewrite injT_0_l; auto; intros H4.
rewrite <- H4; rewrite scalT_inj0; auto.
apply scalT_spos; auto.
apply scalT_pos; auto with zarith.
repeat rewrite scalT_plus_r; auto.
repeat rewrite plusT_A; auto; rewrite plusT_C; repeat rewrite plusT_A; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
unfold injT1; rewrite injT_plus; repeat rewrite injT_mul; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
rewrite <- (injT_0_r); auto.
apply f_equal2 with (f := plusT FT); auto.
repeat rewrite <- scalT_mul; auto.
rewrite plusT_C; auto.
replace (v / Z.gcd v x * x)%Z with (x / Z.gcd v x * v)%Z.
replace (x / Z.gcd v x * - v)%Z with ((-1) * (x / Z.gcd v x * v))%Z; try ring.
rewrite (scalT_mul _ FA (-1)%Z); rewrite plusT_0; auto.
assert (Hdv: ((Z.gcd v x) | x)%Z).
assert (Hz:= (Zgcd_is_gcd v x)); inversion Hz; auto.
case Hdv; intros q Hq; pattern x at 1 4; rewrite Hq.
rewrite Z_div_mult; auto.
assert (Hdx: ((Z.gcd v x) | v)%Z).
assert (Hz:= (Zgcd_is_gcd v x)); inversion Hz; auto.
case Hdx; intros q1 Hq1; pattern v at 1 2; rewrite Hq1.
rewrite Z_div_mult; try ring.
apply Z.lt_gt; apply Zgcd_spos; auto.
apply Z.lt_gt; apply Zgcd_spos; auto.
intros i Hi; apply (H3 i); auto with datatypes.
Qed.

Lemma product_cor: forall l1 l2 r env,
  (forall x ll c t, In (Line (x::ll) c t) l1 -> (0 < x)%Z) ->
  (forall x ll c t, In (Line (x::ll) c t) l2 -> (0 < x)%Z) ->
  Pdt r (tail env) -> Pdt l1 env ->
  Pdot l2 env -> Pdt (product l1 l2 r) (tail env).
Proof.
intros l1; elim l1; simpl; auto; clear l1.
intros ([|x w],c,t) l1 Hrec l2 r env Hp1 Hp2 H2 H3 H4; auto.
apply Hrec; auto with datatypes.
intros x ll c1 t1 Hx.
apply (Hp1 x ll c1 t1); auto.
intros i Hi; apply (H3 i); auto with datatypes.
destruct t.
apply Hrec; auto with datatypes.
intros x1 ll c1 t1 Hx.
apply (Hp1 x1 ll c1 t1); auto with datatypes.
intros i Hiu; apply H3; auto with datatypes.
apply Hrec; auto with datatypes.
intros x1 ll c1 t1 Hx.
apply (Hp1 x1 ll c1 t1); auto.
apply app_one_cor; auto with datatypes.
apply (Hp1 x w c lLt); auto.
intros i Hiu; apply H3; auto with datatypes.
apply Hrec; auto with datatypes.
intros x1 ll c1 t1 Hx.
apply (Hp1 x1 ll c1 t1); auto.
apply app_one_cor; auto with datatypes.
apply (Hp1 x w c lLe); auto.
intros i Hiu; apply H3; auto with datatypes.
Qed.

(************************************************************)
(*          Refute correctness                              *)
(************************************************************)

Lemma elim_one_cor: forall v env,
  Pdt v env -> Pdt (elim_one v) (tail env).
Proof.
intros v env Hv; unfold elim_one.
generalize (split_cor v) (split_pos v); 
  case split; intros [p l c|] w1 w2 w3.
intros (Hd1, (Hd2, (Hd3, Hd4))) (Hp1, Hp2).
apply app_one_cor_eq; auto with zarith.
red; auto.
apply app_one_cor; auto with zarith.
red; auto.
apply Pdt_incl_rm with (1 := Hd4); auto.
apply InE_line_to_T with (2 := Hv); auto.
apply Pdt_incl_op with (1 := Hd3); auto.
apply (line_to_T_opp (Zpos p::l)).
apply InE_line_to_T with (2 := Hv); auto.
apply Pdt_incl_id with (1 := Hd2); auto.
intros (Hd1, (Hd2, Hd3)) (Hp1, Hp2).
apply product_cor; auto.
apply Pdt_incl_rm with (1 := Hd3); auto.
apply Pdt_incl_id with (1 := Hd1); auto.
apply Pdt_incl_op with (1 := Hd2); auto.
Qed.

Lemma unsolvable_cor: forall d env,
  unsolvable d = true -> ~ Pdt d env.
Proof.
intros d env; induction d as [| [[| x w] c t] d Hrec]; simpl.
intros HH; discriminate HH.
destruct c; simpl; auto.
destruct t; simpl.
intros H H1; case (Hrec H).
intros i Hi; auto with datatypes.
intros _ H; case (ltT_neg _ FA (0%Z)); auto with zarith.
generalize (H (Line nil (0%Z) lLt)); simpl; auto.
unfold injT1; rewrite injT_0_r; auto with datatypes.
intros H H1; case (Hrec H).
intros i Hi; auto with datatypes.
destruct t; simpl.
intros _ H; case (leT_neg _ FA (Zneg p)).
red; simpl; auto.
change (Zneg p) with ((-1) * (Zpos p))%Z.
rewrite injT_mul; auto.
generalize (H (Line nil (Zpos p) lEq)); simpl.
unfold injT1; rewrite injT_0_l; auto.
intros HH; rewrite <-HH; auto; rewrite scalT_inj0; auto.
apply leT_refl; auto.
intros H H1; case (Hrec H); intros i Hi; auto with datatypes.
intros H H1; case (Hrec H); intros i Hi; auto with datatypes.
destruct t; simpl.
intros _ H; case (leT_neg _ FA (Zneg p)).
red; simpl; auto.
generalize (H (Line nil (Zneg p) lEq)); simpl.
unfold injT1; rewrite injT_0_l; auto.
intros HH; rewrite <-HH; auto.
apply leT_refl; auto.
intros _ H; case (ltT_neg _ FA (Zneg p)); try discriminate.
generalize (H (Line nil (Zneg p) lLt)); simpl.
unfold injT1; rewrite injT_0_l; auto.
intros _ H; case (leT_neg _ FA (Zneg p)).
red; simpl; auto.
generalize (H (Line nil (Zneg p) lLe)); simpl.
unfold injT1; rewrite injT_0_l; auto.
intros H H1; case (Hrec H); intros i Hi; auto with datatypes.
Qed.

Lemma refute_l_cor: forall a v env,
  length a = length env ->
  refute_l a v = true -> ~ Pdt v env.
intros a; induction a as [|x a Hrec].
intros; apply unsolvable_cor; auto.
intros v [|e env]; try (intros HH; discriminate).
intros HH Hr Hd; apply (Hrec (elim_one v) env); auto.
injection HH; auto.
intros HH1; apply (elim_one_cor v (e::env)); auto.
Qed.

Lemma refute_cor: forall v env,
  length (first_clause v) = length env ->
  refute v = true -> ~ Pdt v env.
Proof.
intros v env Hl Hr; apply (refute_l_cor (first_clause v)); auto.
Qed.

End Proof.