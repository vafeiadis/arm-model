(******************************************************************************)
(** * Definition of execution graph events and labels *)
(******************************************************************************)

Require Import List Arith Lia.
From hahn Require Import Hahn.

Set Implicit Arguments.

Lemma doms_helper A (s1 s2 : A -> Prop) (r : relation A) :
  r ⊆ s1 × s2 -> r ≡ ⦗ s1 ⦘ ⨾ r ⨾ ⦗ s2 ⦘.
Proof using.
  split; unfolder in *; splits; ins; desf; eauto.
  all: eapply H; eauto.
Qed.

Definition thread_id := nat.
Definition tid_init := 0.

Definition location := nat.
Definition value := nat.

(******************************************************************************)
(** ** Execution graph events  *)
(******************************************************************************)

Inductive actid :=
  | InitEvent (l : location)
  | ThreadEvent (thread : thread_id) (index : nat) (subindex : nat) .

Definition tid a :=
  match a with
    | InitEvent l => tid_init
    | ThreadEvent i _ _ => i
  end.

Definition is_tid i a : Prop := tid a = i.

Definition index a :=
  match a with
    | InitEvent l => 0
    | ThreadEvent _ n _ => n
  end.

Definition is_init a :=
  match a with
    | InitEvent _ => True
    | ThreadEvent _ _ _ => False
  end.

Lemma tid_set_dec thread :
  (fun x => tid x = thread) ∪₁ (fun x => tid x <> thread) ≡₁ (fun x => True).
Proof using. unfolder; split; ins; desf; tauto. Qed.

(******************************************************************************)
(** ** Same tid restriction *)
(******************************************************************************)

Definition same_tid := (fun x y => tid x = tid y).

Lemma restr_eq_rel_same_tid r :  restr_eq_rel tid r  ≡ r ∩ same_tid.
Proof using. unfold same_tid; basic_solver. Qed.

Lemma loceq_same_tid (r: relation actid) (H: funeq tid r):
 r ⊆ r ∩ same_tid.
Proof using.
unfold same_tid; basic_solver.
Qed.

Lemma same_tid_loceq (r: relation actid) (H: r ⊆ r ∩ same_tid):
 funeq tid r.
Proof using.
unfold same_tid; unfolder; firstorder.
Qed.

(******************************************************************************)
(** ** Decidable equality *)
(******************************************************************************)

Lemma eq_dec_actid :
  forall x y : actid, {x = y} + {x <> y}.
Proof using.
  repeat decide equality.
Qed.

(******************************************************************************)
(** ** Labels  *)
(******************************************************************************)

Inductive r_mode := Opln_read | OacqSC | OacqPC.
Inductive w_mode := Opln_write | Orel.
Inductive f_mode := Odmbst | Odmbld | Odmbsy | Oisb.

Inductive label :=
  | Aload  (ex: bool) (o: r_mode) (l:location) (v:value)
  | Astore (ex: bool) (o: w_mode) (l:location) (v:value)
  | Afence (o: f_mode)
  | Abranch.


Section Labels.

Variable A : Type.
Variable lab : A -> label.

Definition loc a :=
  match lab a with
  | Aload _ _ l _
  | Astore _ _ l _ => Some l
  | _ => None
  end.

Definition val a :=
  match lab a with
  | Aload  _ _ _ v
  | Astore _ _ _ v => Some v
  | _ => None
  end.

Definition is_r a :=
  match lab a with
  | Aload  _ _ _ _ => true
  | _ => false
  end.

Definition is_w a :=
  match lab a with
  | Astore _ _ _ _ => true
  | _ => false
  end.

Definition is_f a :=
  match lab a with
  | Afence _ => true
  | _ => false
  end.

Definition is_br a :=
  match lab a with
  | Abranch => true
  | _ => false
  end.


Definition is_w_rel a :=
  match lab a with
  | Astore _ o _ _ => o = Orel
  | _ => False
  end.

Definition is_r_acqSC a :=
  match lab a with
  | Aload _ o _ _ => o = OacqSC
  | _ => False
  end.

Definition is_r_acqPC a :=
  match lab a with
  | Aload _ o _ _ => o = OacqPC
  | _ => False
  end.

Definition is_dmbst a := lab a = Afence Odmbst.
Definition is_dmbld a := lab a = Afence Odmbld.
Definition is_dmbsy a := lab a = Afence Odmbsy.
Definition is_isb   a := lab a = Afence Oisb.



Lemma lab_rwf a : is_r a \/ is_w a \/ is_f a \/ is_br a.
Proof using. unfold is_r, is_w, is_f, is_br; destruct (lab a); auto. Qed.

Definition R_ex a :=
  match lab a with
  | Aload r _ _ _ => r
  | _ => false
  end.

Lemma R_ex_in_R : R_ex ⊆₁ is_r.
Proof using.
unfold R_ex, is_r; basic_solver.
Qed.

(******************************************************************************)
(** ** Same location restriction *)
(******************************************************************************)

Definition same_loc := (fun x y => loc x = loc y).

Lemma restr_eq_rel_same_loc r :  restr_eq_rel loc r  ≡ r ∩ same_loc.
Proof using. unfold same_loc; basic_solver. Qed.

Lemma loceq_same_loc (r: relation A) (H: funeq loc r):
 r ⊆ r ∩ same_loc.
Proof using.
unfold same_loc; basic_solver.
Qed.

Lemma same_loc_loceq (r: relation A) (H: r ⊆ r ∩ same_loc):
 funeq loc r.
Proof using.
unfold same_loc; unfolder; firstorder.
Qed.

Lemma same_loc_trans : transitive same_loc.
Proof using. unfold same_loc; red; ins. by rewrite H. Qed.

Lemma same_loc_sym : symmetric same_loc.
Proof using. unfold same_loc; red; ins. Qed.

(******************************************************************************)
(** ** Values and locations getters  *)
(******************************************************************************)

Lemma is_w_val x (WX : is_w x) : exists v, val x = Some v.
Proof using. unfold is_w, val in *; desf. eexists; eauto. Qed.

Lemma is_w_loc x (WX : is_w x) : exists l, loc x = Some l.
Proof using. unfold is_w, loc in *; desf. eexists; eauto. Qed.

Lemma is_r_val x (WX : is_r x) : exists v, val x = Some v.
Proof using. unfold is_r, val in *; desf. eexists; eauto. Qed.

Lemma is_r_loc x (WX : is_r x) : exists l, loc x = Some l.
Proof using. unfold is_r, loc in *; desf. eexists; eauto. Qed.

End Labels.

(******************************************************************************)
(** ** Identical labeling up to value  *)
(******************************************************************************)

(*Definition same_mod {A} (lab : A -> label) : relation A :=
  (fun x y => mod lab x = mod lab y). *)

Definition same_val {A} (lab : A -> label) : relation A :=
  (fun x y => val lab x = val lab y).

Definition same_label_u2v label1 label2 :=
  match label1, label2 with
  | Aload  r1 o1 l1 _, Aload  r2 o2 l2 _ => r1 = r2 /\ o1 = o2 /\ l1 = l2
  | Astore s1 o1 l1 _, Astore s2 o2 l2 _ => s1 = s2 /\ o1 = o2 /\ l1 = l2
  | Afence o1, Afence o2 => o1 = o2
  | _,_ => False
  end.

(******************************************************************************)
(** ** Sequenced-Before *)
(******************************************************************************)

Definition ext_sb a b :=
  match a, b with
    | _, InitEvent _ => False
    | InitEvent _, ThreadEvent _ _ _ => True
    | ThreadEvent t i _, ThreadEvent t' i' _ => t = t' /\ i < i'
   end.

Lemma ext_sb_trans : transitive ext_sb.
Proof using.
  unfold ext_sb; red; ins; desf; desf; lia.
Qed.

Lemma ext_sb_irr : irreflexive ext_sb.
Proof using.
  unfold ext_sb; red; ins; desf; desf; lia.
Qed.

Lemma ext_sb_to_non_init : ext_sb ⊆ ext_sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
  unfold is_init, ext_sb; basic_solver.
Qed.

Lemma ext_sb_semi_total_l x y z
  (N: ~ is_init x) (NEQ: index y <> index z) (XY: ext_sb x y) (XZ: ext_sb x z):
  ext_sb y z \/ ext_sb z y.
Proof using.
  unfold ext_sb in *; desf; ins; desf; lia.
Qed.

Lemma ext_sb_semi_total_r x y z
  (NEQ: index y <> index z) (XY: ext_sb y x) (XZ: ext_sb z x):
  ext_sb y z \/ ext_sb z y.
Proof using.
  unfold ext_sb in *; desf; ins; desf; lia.
Qed.

Lemma ext_sb_tid_init x y (SB : ext_sb x y): tid x = tid y \/ is_init x.
Proof using.
  unfold ext_sb in *; desf; ins; desf; eauto.
Qed.

Lemma ext_sb_tid_init': ext_sb ⊆ ext_sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ ext_sb.
Proof using.
  generalize ext_sb_tid_init; firstorder.
Qed.

(******************************************************************************)
(** ** Same Instruction *)
(******************************************************************************)

Definition si_matching_label label1 label2 :=
  match label1, label2 with
  | Aload  r1 o1 _ _, Aload  r2 o2 _ _ => r1 = r2 /\ o1 = o2
  | Astore s1 o1 _ _, Astore s2 o2 _ _ => s1 = s2 /\ o1 = o2
  | Afence o1, Afence o2 => o1 = o2
  | Abranch , Abranch => True
  | _ , _ => False
  end.

Definition ext_si a b :=
  match a, b with
  | InitEvent l, InitEvent l' => l = l'
  | ThreadEvent t i _, ThreadEvent t' i' _ => t = t' /\ i = i'
  | _ , _ => False
  end.

Lemma ext_si_refl : reflexive ext_si.
Proof using.
  unfold ext_si; unfolder; ins; desf; ins.
Qed.

Lemma ext_si_symm : symmetric ext_si.
Proof using.
  unfold ext_si; unfolder; ins; desf; desf.
Qed.

Lemma ext_si_trans : transitive ext_si.
Proof using.
  unfold ext_si; red; ins; desf; desf.
Qed.

(******************************************************************************)
(** ** is_init properties *)
(******************************************************************************)

Lemma is_init_tid :
  is_init ⊆₁ fun x => tid x = tid_init.
Proof using. unfolder. unfold is_init. ins. desf. Qed.

Lemma initninit_in_ext_sb : is_init × (set_compl is_init) ⊆ ext_sb.
Proof using. unfold ext_sb. basic_solver. Qed.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)

#[global]
Hint Unfold set_union set_inter is_r is_w is_f is_br R_ex : type_unfolderDb.
#[global]
Hint Unfold is_w_rel is_r_acqSC is_r_acqPC is_dmbst is_dmbld : type_unfolderDb.
#[global]
Hint Unfold is_dmbsy is_isb : type_unfolderDb.
Tactic Notation "type_unfolder" :=  repeat autounfold with type_unfolderDb in *.

Tactic Notation "type_solver" int_or_var(index) :=
  type_unfolder; basic_solver index.

Tactic Notation "type_solver" :=  type_solver 4.
