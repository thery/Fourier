From Stdlib Require Import ZArith List.
Require Import FourierConcTerm Fourier.

(************************************************************)
(*          Term structure for reflecting terms             *)
(************************************************************)

Inductive term : Type :=
  | Const (_: Z)          (* constant with integer value *)
  | Var (_: nat)          (* variable indexed by nat *)
  | Scal (_: Z) (_: term) (* multiplication by a scalar *)
  | Op (_ : term)         (* opposite *)
  | Plus (_ _ : term)     (* sum *)
  | Minus (_ _ : term)    (* subtraction *).

Inductive equation : Type :=
  | Eq (_ _: term)        (* equality *)
  | Lt (_ _: term)        (* strict inequality *)
  | Le (_ _: term).       (* inequality *)


Section Abs2Conc.

Variable FT: Fmodule.
Variable FA: Faxiom FT.

Open Scope F_scope.

(* reflecting term *)
Fixpoint term_to_T t (env: list (T FT)) {struct t}: (T FT) :=
  match t with Const c => injT FT c
             | Var n => nth n env (injT FT 0)
             | Scal z t1 => z * (term_to_T t1 env)
             | Op t1 => opT FT (term_to_T t1 env) 
             | Plus t1 t2 => (term_to_T t1 env) + (term_to_T t2 env)
             | Minus t1 t2 => (term_to_T t1 env) - (term_to_T t2 env)
  end.

(* reflecting a single equation *)
Definition equation_to_T e (env: list (T FT)) := 
  match e with Eq t1 t2 => term_to_T t1 env = term_to_T t2 env
             | Lt t1 t2 => ltT FT (term_to_T t1 env) (term_to_T t2 env)
             | Le t1 t2 => leT FT (term_to_T t1 env) (term_to_T t2 env)
  end.

(* reflecting a list of equations *)
Fixpoint equations_to_T l (env: list (T FT)) {struct l}: Prop :=
  match l with nil => False
             | e::l1 => equation_to_T e env -> equations_to_T l1 env
  end.

Fixpoint full_var (l: list (T FT)) :=
  match l with nil => nil | _ :: l1 => 0::full_var l1 end.

Lemma full_var_length: forall l,
  length (full_var l) = length l.
Proof.
intros l; induction l; simpl; auto.
Qed.

Lemma full_var0: forall l env, list_to_T FT (full_var l) env = injT _ 0.
Proof.
intros l; induction l as [| a l Hrec]; simpl; auto.
intros [| b env]; auto; rewrite Hrec; rewrite scalT_0; auto.
rewrite injT_0_l; auto.
Qed.

Fixpoint mk_var (n: nat) (l: list (T FT)) {struct l} :=
  match l with 
    nil => nil 
  | _ :: l1 => match n with 
                 O => 1::full_var l1 
               | S n1 => 0::mk_var n1 l1
               end
  end.

Lemma mk_var_length: forall n l,
  length (mk_var n l) = length l.
Proof.
intros n l; generalize n; induction l; simpl; auto.
intros n1; induction n1; simpl; auto.
rewrite full_var_length; auto.
Qed.

Definition mk_lvar n env := Line (mk_var n env) 0.

Lemma mk_var_cor: forall n env,
   term_to_T (Var n) env = list_to_T _ (mk_var n env) env.
Proof.
simpl.
intros n env; generalize n; induction env as [| e env Hrec]; 
  simpl; clear n; intros [| n]; simpl; try rewrite injT_0_r; auto.
rewrite full_var0; rewrite injT_0_r; auto; rewrite scalT_1; auto.
rewrite Hrec; rewrite scalT_0; auto; rewrite injT_0_l; auto.
Qed.

Lemma mapsm_length: forall v l, 
   length (mapsm v l) = length l.
Proof.
intros v l; induction l; simpl; auto.
Qed.

Definition scal_line v l :=
  match l with
   Line ll c t => Line (mapsm v ll) (v * c) t
  end.

Lemma scal_line_length: forall v l, 
   llength (scal_line v l) = llength l.
Proof.
intros v l; induction l; simpl; auto.
apply mapsm_length.
Qed.

Fixpoint plusm (l1 l2: list Z) {struct l1} : list Z :=
  match l1, l2 with 
  | nil, nil => nil
  | nil, _ => l2
  | _, nil => l1
  | (v1::l3), (v2::l4) => (v1 + v2)%Z:: plusm l3 l4
  end.

Lemma plusm_length: forall l1 l2 n,
   length l1 = n -> length l2 = n -> length (plusm l1 l2) = n.
Proof.
intros l1; induction l1 as [|a l1 Hrec]; simpl; auto; 
  intros [| b l2]; simpl; auto.
intros [|n] H1 H2; try discriminate H1.
rewrite (Hrec l2 n); auto.
Qed.

Lemma plusm_cor: forall l1 l2 env,
  list_to_T FT (plusm l1 l2) env =
   list_to_T _ l1 env + list_to_T _ l2 env.
Proof.
intros l1; induction l1 as [| a l1 Hrec]; intros [| b l2] env;
  simpl; try rewrite injT_0_r; try rewrite injT_0_l; auto.
case env; try rewrite injT_0_r; auto.
intros e env1; rewrite Hrec.
rewrite scalT_plus_l; repeat rewrite plusT_A; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; repeat rewrite plusT_A; auto.
apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; auto.
Qed.

Definition plus_line l1 l2 t :=
  match l1, l2 with 
    Line ll1 c1 _, Line ll2 c2 _ => Line (plusm ll1 ll2) (c1 + c2)%Z t
  end.

Lemma plus_line_length: forall l1 l2 n t,
   llength l1 = n -> llength l2 = n -> llength (plus_line l1 l2 t) = n.
Proof.
intros [l1 c1 t1] [l2 c2 t2] n t Hl1 Hl2; simpl; apply plusm_length; auto.
Qed.

Fixpoint term_to_line t (env: list (T FT)) ty {struct t}: line :=
  match t with Const c => Line (full_var env) c ty
             | Var n => mk_lvar n env ty
             | Scal z t1 => scal_line z (term_to_line t1 env ty)
             | Op t1 => scal_line (-1) (term_to_line t1 env ty) 
             | Plus t1 t2 => plus_line (term_to_line t1 env ty) 
                                (term_to_line t2 env ty) ty
             | Minus t1 t2 => plus_line (term_to_line t1 env ty)
                                (scal_line (-1) (term_to_line t2 env ty)) ty
  end.

Lemma term_to_line_length : forall t env ty,
  llength (term_to_line t env ty) = length env.
Proof.
intros t; elim t; simpl; auto.
intros; apply full_var_length.
intros; apply mk_var_length.
intros; rewrite scal_line_length; auto.
intros; rewrite scal_line_length; auto.
intros; rewrite (fun x y => plus_line_length x y (length env)); auto.
intros; rewrite (fun x y => plus_line_length x y (length env)); auto.
intros; rewrite scal_line_length; auto.
Qed.

Lemma term_to_line_cor: forall t env ty,
  match term_to_line t env ty with
    Line l c _ => 
      term_to_T t env = list_to_T _ l env + injT _ c
  end.
Proof.
intros t env ty; induction t as [
   c| n | z t1 Hrec | t1 Hrec | t1 Hrec1 t2 Hrec2 | t1 Hrec1 t2 Hrec2]; simpl.
rewrite full_var0; rewrite injT_0_l; auto.
rewrite <- mk_var_cor; rewrite injT_0_r; auto.
generalize Hrec; case term_to_line; simpl;
  intros l1 c1 ty1 HH; rewrite HH; rewrite mapsm_cor; auto;
  rewrite scalT_plus_r; auto; rewrite injT_mul; auto.
rewrite opT_def; auto.
generalize Hrec; case term_to_line; simpl;
  intros l1 c1 ty1 HH; rewrite HH; rewrite mapsm_cor; auto;
  rewrite scalT_plus_r; auto; rewrite <- injT_mul; auto.
generalize Hrec1 Hrec2; do 2 case term_to_line.
  intros l1 c1 ty1 l2 c2 ty2 HH1 HH2; rewrite HH1; rewrite HH2.
  simpl; rewrite plusm_cor.
  repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
  rewrite plusT_C; repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
  rewrite plusT_C; auto; rewrite injT_plus; auto.
generalize Hrec1 Hrec2; do 2 case term_to_line.
  intros l1 c1 ty1 l2 c2 ty2 HH1 HH2; rewrite HH1; rewrite HH2.
  simpl; rewrite plusm_cor; rewrite mapsm_cor; auto.
  rewrite minusT_def; auto.
  repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
  rewrite plusT_C; auto; rewrite scalT_plus_r; auto.
  repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
  rewrite plusT_C; auto; rewrite injT_plus; auto; rewrite <- injT_mul; simpl; auto.
Qed.

(* Reflection functions *)
Definition equation_to_P  (e: equation) env : Prop := 
  match e with 
    Eq t1 t2  => term_to_T t1 env = term_to_T t2 env
  | Lt t1 t2  => term_to_T t1 env < term_to_T t2 env
  | Le t1 t2  => term_to_T t1 env <= term_to_T t2 env
  end.

Fixpoint equations_to_P  (es: list equation) env {struct es} : Prop := 
  match es with 
    nil => False
  | e::es1 => equation_to_P e env ->  equations_to_P es1 env
  end.

(* Translation functions *)
Definition equation_to_line (e: equation) env : line :=
  match e with
    Eq t1 t2 => 
        plus_line (term_to_line t2 env lEq)
                   (scal_line (-1) (term_to_line t1 env lEq)) lEq
  | Le t1 t2 => 
        plus_line (term_to_line t2 env lLe)
                   (scal_line (-1) (term_to_line t1 env lLe)) lLe
  | Lt t1 t2 => 
        plus_line (term_to_line t2 env lLt)
                   (scal_line (-1) (term_to_line t1 env lLt)) lLt
  end.

Fixpoint equations_to_dt (es: list equation) env {struct es} : dt :=
  match es with 
    nil => nil
  | e::es1 => equation_to_line e env :: equations_to_dt es1 env
  end.

Lemma equation_to_line_length: forall e env,
  llength (equation_to_line e env) = length env.
Proof.
intros e env; destruct e; simpl; auto;
  try apply plus_line_length; auto;
  try apply term_to_line_length;
  try rewrite scal_line_length;
  apply term_to_line_length.
Qed.

Lemma equations_to_dt_length: forall s env i,
  In i (equations_to_dt s env) -> llength i = length env.
Proof.
intros s env i; induction s as [| t1 t2 s]; simpl; auto.
intros HH; case HH.
intros [HH | HH]; subst; auto.
apply equation_to_line_length; auto.
Qed.

(* Main theorem *)
Lemma equations_cor: forall es env,
  refute (equations_to_dt es env) = true -> 
  equations_to_P es env.
Proof.
intros es env H.
assert (H1: ~ Pdt _ (equations_to_dt es env) env).
  apply refute_cor; auto.
  generalize H (equations_to_dt_length es env); 
   case equations_to_dt; simpl.
  intros HH; discriminate.
  intros l1 l2 _ HH; generalize (HH l1); case l1; simpl; auto.
generalize H1; clear H H1.
induction es as [| e es Hrec]; simpl.
intros HH; case HH; intros a HH1; inversion HH1.
intros H1 H; apply Hrec; intros H2.
case H1.
intros a; simpl; intros [Ha | Ha]; subst; auto.
destruct e as [t1 t2|t1 t2|t1 t2]; simpl.
generalize H; simpl.
unfold plus_line.
generalize (term_to_line_cor t1 env lEq) (term_to_line_cor t2 env lEq).
do 2 case term_to_line.
intros l1 c1 ty1 l2 c2 ty2 HH1 HH2; rewrite HH1; rewrite HH2.
unfold scal_line, line_to_T; intros HH3.
rewrite plusm_cor; rewrite mapsm_cor; auto.
match goal with |- _ = ?X =>
  replace X with ((list_to_T FT l1 env + injT FT c1) + 
                    (-1) * (list_to_T FT l2 env + injT FT c2))
end; auto.
rewrite HH3; rewrite plusT_0; auto.
rewrite scalT_plus_r; auto; rewrite injT_plus; auto; rewrite injT_mul; auto.
repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; auto; repeat rewrite plusT_A; auto; 
  apply f_equal2 with (f := plusT FT); auto.
rewrite plusT_C; auto.
generalize H; simpl.
unfold plus_line.
generalize (term_to_line_cor t1 env lLt) (term_to_line_cor t2 env lLt).
do 2 case term_to_line.
intros l1 c1 ty1 l2 c2 ty2 HH1 HH2; rewrite HH1; rewrite HH2.
unfold scal_line, line_to_T; intros HH3.
rewrite plusm_cor; rewrite mapsm_cor; auto.
apply ltT_cancel_l with (list_to_T _ l2 env + (injT _ c2)); auto.
rewrite injT_0_r; auto.
match goal with |- _ < ?X =>
  replace X with (list_to_T FT l1 env + injT _ c1)
end; auto.
apply sym_equal.
rewrite plusT_C; auto.
repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
rewrite (plusT_C _  FA (list_to_T FT l2 env)); auto.
rewrite (plusT_C _ FA (-1 * list_to_T FT l2 env)); auto.
rewrite injT_plus; repeat rewrite plusT_A; auto.
rewrite injT_mul; auto; rewrite plusT_0; auto; rewrite injT_0_r; auto.
rewrite (plusT_C _ FA (-1 * injT _ c2)); auto.
rewrite plusT_0; auto; rewrite injT_0_r; auto.
generalize H; simpl.
unfold plus_line.
generalize (term_to_line_cor t1 env lLe) (term_to_line_cor t2 env lLe).
do 2 case term_to_line.
intros l1 c1 ty1 l2 c2 ty2 HH1 HH2; rewrite HH1; rewrite HH2.
unfold scal_line, line_to_T; intros HH3.
rewrite plusm_cor; rewrite mapsm_cor; auto.
apply leT_cancel_l with (list_to_T _ l2 env + (injT _ c2)); auto.
rewrite injT_0_r; auto.
match goal with |- _ <= ?X =>
  replace X with (list_to_T FT l1 env + injT _ c1)
end; auto.
apply sym_equal.
rewrite plusT_C; auto.
repeat rewrite plusT_A; auto; apply f_equal2 with (f := plusT FT); auto.
rewrite (plusT_C _  FA (list_to_T FT l2 env)); auto.
rewrite (plusT_C _ FA (-1 * list_to_T FT l2 env)); auto.
rewrite injT_plus; repeat rewrite plusT_A; auto.
rewrite injT_mul; auto; rewrite plusT_0; auto; rewrite injT_0_r; auto.
rewrite (plusT_C _ FA (-1 * injT _ c2)); auto.
rewrite plusT_0; auto; rewrite injT_0_r; auto.
Qed.

End Abs2Conc.
