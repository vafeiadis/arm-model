(******************************************************************************)
(** * Definition of the ARMv8.3 memory model                                  *)
(******************************************************************************)

Require Import PropExtensionality.
Require Import Hahn Arith.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.

Lemma set_irr T (X Y : T -> Prop) :
  X ≡₁ Y -> X = Y.
Proof.
  ins. apply functional_extensionality; ins.
  apply propositional_extensionality; split; apply H.
Qed.  

Definition classes T (eqv : relation T) (X : T -> Prop) :=
  exists x, X ≡₁ eqv x.

Definition lift T (eqv r : relation T) (X Y : T -> Prop) :=
  exists x y, r x y /\ X ≡₁ eqv x /\ Y ≡₁ eqv y.

Definition delift T (eqv : relation T) (r : relation (T -> Prop)) x y :=
  r (eqv x) (eqv y) /\ eqv x x /\ eqv y y.

Global Hint Unfold classes lift delift : unfolderDb.

Add Parametric Morphism A : (@lift A) with signature
  same_relation ==> same_relation ==> same_relation as lift_more.
Proof.
  unfolder; splits; ins; desf;
    do 2 eexists; splits; ins; desf; eauto.
  all: try solve [ eapply H2 in H8; desf; eauto
                 | eapply H3 in H8; desf; eauto].
Qed.

Add Parametric Morphism A : (@lift A) with signature
  eq ==> inclusion ==> inclusion as lift_mori.
Proof.
  unfolder; ins; desf; do 2 eexists; splits; ins; eauto.
Qed.

Add Parametric Morphism A : (@delift A) with signature
  eq ==> same_relation ==> same_relation as delift_more.
Proof.
  unfolder; splits; ins; desf; eauto 10.
Qed.

Add Parametric Morphism A : (@delift A) with signature
  eq ==> inclusion ==> inclusion as delift_mori.
Proof.
  unfolder; ins; desf; eauto 10.
Qed.

Section lift_lemmas.

Variable T : Type.
Variables eqv r : relation T.
Hypothesis REFL: forall x y, r x y \/ r y x -> eqv x x.
Hypothesis SYM: symmetric eqv.
Hypothesis TRAN: transitive eqv.
  
Lemma step_lift x y :
  (lift eqv r) (eqv x) (eqv y) <-> (eqv ⨾ r ⨾ eqv) x y.
Proof using REFL SYM TRAN.
  unfolder; split; induction 1; desf; eauto.
  { repeat eexists; try apply H; splits; eauto. }
  all: do 2 eexists; splits; try edone; ins; desf; eauto.
Qed.

Lemma ct_lift1
      X Y (CT: clos_trans (lift eqv r) X Y) x y :
  X ≡₁ eqv x -> Y ≡₁ eqv y -> (eqv ⨾ (r ⨾ eqv)⁺) x y.
Proof using REFL SYM TRAN.
  revert x y.
  apply clos_trans_t1n in CT; induction CT; ins; desf.
  { unfolder in *; desf.
    exists x1; split; [| eapply t_step]; eauto 8. }
  unfold lift in H; desf.
  forward eapply IHCT as Z; eauto.
  exists x1; split.
  { unfolder in *; desf; eauto. }
  red in Z; desc; eapply t_trans; eauto.
  eapply t_step; unfolder; eauto.
Qed.

Lemma ct_lift x y :
  clos_trans (lift eqv r) (eqv x) (eqv y) <-> (eqv ⨾ (r ⨾ eqv)⁺) x y.
Proof using REFL SYM TRAN.
  split; ins; [ by eapply ct_lift1; eauto | ].
  pattern x; pattern y.
  red in H; desf; generalize dependent x.
  apply clos_trans_t1n in H0.
  induction H0; ins; desf; red in H; desc.
    by apply t_step, step_lift; ins; unfold seq; eauto.
  eapply t_trans; eauto.
  eapply t_step, step_lift; unfold seq in *; desf; eauto 8.
Qed.

Lemma ct_lift2 X Y :
  clos_trans (lift eqv r) X Y <-> exists x y, X ≡₁ eqv x /\ Y ≡₁ eqv y /\ (r ⨾ eqv)⁺ x y.
Proof using REFL SYM TRAN.
  split; ins.
  { unfolder in H; unfolder; induction H; desf; eauto.
    { do 2 eexists; splits; eauto 6 using t_step. }
    do 2 eexists; splits; eauto; eapply t_trans with x0; eauto.
    apply ct_end in IHclos_trans7; unfolder in IHclos_trans7; desf.
    apply ct_end; unfolder; do 2 (eexists; split; eauto).
  } 
  desf; generalize dependent X; generalize dependent Y.
  apply clos_trans_t1n in H1.
  induction H1; ins; desf; red in H; desc.
    apply t_step; unfolder in *; desc; do 2 eexists; splits; eauto.
  eapply t_trans; eauto.
  eapply t_step; unfolder in *; desc; do 2 eexists; splits; eauto.
Qed.


Lemma acyclic_lift :
  acyclic (lift eqv r) <-> acyclic (r ⨾ eqv).
Proof using REFL SYM TRAN.
  unfold acyclic, irreflexive; split; ins.
    assert (eqv x x) by (apply ct_begin in H0; unfolder in H0; desf; eauto).
    eapply H, ct_lift with (x := x); red; eauto.
  assert (exists y, x ≡₁ eqv y).
  { induction H0; ins; unfold lift in *; desf; eauto. }
  desf; eapply ct_lift1 in H0; eauto.
  red in H0; desf; eapply (H z).
  eapply ct_end; eapply ct_end in H2; unfold seq in *; desf.
  eexists; split; eauto.
Qed.

Lemma delift_restr_classes rel :
  delift eqv (restr_rel (classes eqv) rel) ≡ delift eqv rel.
Proof using.
  unfold delift, restr_rel, classes; split; red.
  all: ins; splits; ins; desf; splits; ins; eauto. 
Qed.

Lemma delift_lift :
  delift eqv (lift eqv r) ≡ eqv ⨾ r ⨾ eqv.
Proof using REFL SYM TRAN.
  unfolder; splits; ins; desf; splits; ins; desf; eauto 8.
  do 2 eexists; splits; eauto.
Qed.

Lemma delift_ct_lift :
  delift eqv (lift eqv r)⁺ ≡ eqv ⨾ (r ⨾ eqv)⁺.
Proof using REFL SYM TRAN.
  unfold delift; split; red; ins; desf; splits; ins; try eapply ct_lift; eauto.
  unfolder in H; desf; eauto.
  hahn_rewrite ct_end in H; unfolder in H; desf; eauto.
Qed.

End lift_lemmas.
  
Section Arm.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'acts'" := (acts G).
Notation "'lab'" := (lab G).
Notation "'po'" := (po G).
Notation "'si'" := (si G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'lxsx'" := (lxsx G).
Notation "'amo'" := (amo G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'deps'" := (deps G).
Notation "'fre'" := (fre G).
Notation "'rfe'" := (rfe G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'rfi'" := (rfi G).
Notation "'fri'" := (fri G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'iico_data'" := (iico_data G).
Notation "'iico_ctrl'" := (iico_ctrl G).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Br'" := (fun a => is_true (is_br lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'W_ex'" := (W_ex G).

Notation "'L'" := (W ∩₁ is_w_rel lab).
Notation "'Q'" := (R ∩₁ is_r_acqPC lab).
Notation "'A'" := (R ∩₁ is_r_acqSC lab).
(* Notation "'T'" := (RW ∩₁ (fun a => is_true (is_T lab a))). *)

Notation "'F^dmbld'" := (F ∩₁ is_dmbld lab).
Notation "'F^dmbst'" := (F ∩₁ is_dmbst lab).
Notation "'F^dmbsy'" := (F ∩₁ is_dmbsy lab).
Notation "'F^isb'"   := (F ∩₁ is_isb lab).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(** Initial memory order *)
Definition im0 :=
  (E × E) ∩ (is_init × (W \₁ is_init) ∩ same_loc).

(** Local read successor *)
Definition lrs :=
  ⦗W⦘ ⨾ ((po ∩ same_loc) \ (po ⨾ ⦗W⦘ ⨾ (po ∩ same_loc))) ⨾ ⦗R⦘.

(** Local write successor *)
Definition lws :=
  ⦗RW⦘ ⨾ (po ∩ same_loc) ⨾ ⦗W⦘.

(** Observed-by *)
Definition obs := rfe ∪ coe ∪ fre.

(** Dependency-ordered-before *)
Definition dob :=
    (addr ∪ data)
 ∪ ctrl ⨾ ⦗W⦘
 ∪ (ctrl ∪ (addr⨾ po)) ⨾ ⦗F^isb⦘ ⨾ po ⨾ ⦗R⦘
 ∪ addr ⨾ po ⨾ ⦗W⦘
 ∪ (addr ∪ data) ⨾ lrs.

(** Atomic-ordered-before *)
Definition aob :=
  rmw ∪ ⦗W_ex⦘ ⨾ lrs ⨾ (⦗ A ∪₁ Q⦘).

(** Barrier-ordered-before *)
Definition bob :=
    po ⨾ ⦗F^dmbsy⦘ ⨾ po (*todo: dmb.full/dpo.full*)
  ∪ po⨾ ⦗A⦘⨾ amo⨾ ⦗L⦘ ⨾ po
  ∪ ⦗L⦘ ⨾ po ⨾ ⦗A⦘
  ∪ ⦗R⦘ ⨾ po ⨾ ⦗F^dmbld⦘ ⨾ po
  ∪ (⦗A ∪₁ Q⦘) ⨾ po
  ∪ ⦗W⦘ ⨾ po ⨾ ⦗F^dmbst⦘ ⨾ po ⨾ ⦗W⦘
  ∪ po ⨾ ⦗L⦘.

(* Tag-ordered-before *)
(*Definition tob := ∅₂. ⦗ R ∩₁ T ⦘⨾ iico_data⨾ ⦗ Br ⦘⨾ iico_ctrl⨾ ⦗ RW \₁ T ⦘. *)

(** Local-ordered-before *)
Definition lob :=
  (lws ⨾ si
  ∪ dob
  ∪ aob
  ∪ bob
  (*∪ tob*) )⁺.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Definition InternalConsistent :=
  acyclic (po ∩ same_loc ∪ co ∪ fr ∪ rf).

Definition ArmCommon :=
  ⟪ WF : Wf G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ INTERNAL : InternalConsistent ⟫ /\
  ⟪ ATOM : rmw_atomicity G ⟫.

Definition ArmConsistent :=
  ArmCommon /\
  ⟪ ACYC : acyclic (obs ⨾ si ∪ lob) ⟫.


(******************************************************************************)
(** ** Mixed-size equivalence classes *)
(******************************************************************************)

Definition rfisw := rfi⁻¹ ⨾ si ⨾ rfi.

Definition erln :=
  si ∩ (W × W)
  ∪ si ∩ (codom_rel rfe × codom_rel rfe)
  ∪ si ∩ (R × R) ∩ rfisw
  ∪ ⦗ E ⦘.

(** NB: The paper defines [erln] using transitive closure, but it's unnecessary
   as the following lemma shows. *)

Lemma erln_trans WF : transitive erln.
Proof using.
  unfold erln, rfisw, Execution.si.
  rewrite interA, <- !inter_union_r, wf_rfeD; ins.
  ie_unfolder.
  unfolder; ins; desc.
  destruct H, H0; desc; clarify; eauto 10.
  left; splits; eauto using ext_si_trans.
  desf; eauto.
  all: repeat match goal with
  | H : rf ?y ?x, H' : rf ?z ?x |- _ =>
    assert (y = z); [eapply wf_rff; try apply H; try apply H'; eauto | clear H'; subst y] end.
  all: try solve [exfalso; type_solver 2].
    eauto 18.
  right; splits; ins; eexists; splits; eauto.
  exists z2; splits; eauto using ext_si_trans.
Qed.

Lemma erln_sym : symmetric erln.
Proof using.
  unfolder; ins; desf; auto.
  unfold erln, rfisw in *; unfolder in *; desf;
    eauto 15 using (@si_sym G).
Qed.

Lemma erln_in_si : erln ⊆ si.
Proof using.
  unionL; eauto with hahn.
  unfold Execution.si; unfolder; ins; desf; auto using ext_si_refl.
Qed.

Local Hint Immediate erln_sym erln_trans : core.


(******************************************************************************)
(** ** External completion model *)
(******************************************************************************)

(** Single-copy-atomic-ordered-before *)
Definition scaob := si ∩ (codom_rel rfe × codom_rel rfi).

Definition rf_fwd cb :=
  ( W × R) ∩ po ∩ cb ⁻¹ ∩ same_loc
  \ ( po ⨾ ⦗ W ⦘ ⨾  (po ∩ same_loc)).

Definition rf_nfwd cb :=
  ( W × R) ∩ cb ∩ same_loc
  \ ( (cb ∪ po)  ⨾ ⦗ W ⦘ ⨾  ((cb ∪ po) ∩ same_loc)).

Definition linearization_of r cb :=
  ⟪ INCL : r ⊆ cb ⟫ /\
  ⟪ STO : strict_total_order (classes erln) cb ⟫ /\
  ⟪ DOM : cb ⊆ classes erln × classes erln ⟫.

Definition ArmConsistentExtComp :=
  ArmCommon /\ exists cb,
    ⟪ LIN : linearization_of (lift erln (im0 ∪ lob ∪ scaob)) cb ⟫ /\
    ⟪ RF : rf ≡ rf_fwd (delift erln cb) ∪ rf_nfwd (delift erln cb) ⟫ /\
    ⟪ CO : co ≡ delift erln cb ∩ same_loc ∩ (W × W) ⟫.

(******************************************************************************)
(** ** External global completion model *)
(******************************************************************************)

Definition gc_req :=
  ( W × (fun _ => True)) ∪ (codom_rel rfe × (fun _ => True))
  ∪ (rfi ⁻¹ ⨾ lob).

Definition rf_gcb gcb :=
  ( W × R) ∩ gcb ∩ same_loc
  \ ( gcb ⨾ ⦗ W ⦘ ⨾ (gcb ∩ same_loc)).

Definition ArmConsistentGlobExtComp :=
  ArmCommon /\ exists gcb,
    ⟪ LIN : linearization_of (lift erln (im0 ∪ lob ∩ gc_req ∪ scaob)) gcb ⟫ /\
    ⟪ RF : rf ≡ rf_gcb (delift erln gcb) ⟫ /\
    ⟪ CO : co ≡ (W × W) ∩ delift erln gcb ∩ same_loc ⟫.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Ltac dom_helper :=
  match goal with |- ?x ≡ _ => apply doms_helper; unfold x end.

Lemma wf_lrsE WF: lrs ≡ ⦗E⦘ ⨾ lrs ⨾ ⦗E⦘.
Proof using. dom_helper; rewrite wf_poE; basic_solver. Qed.

Lemma wf_lwsE WF: lws ≡ ⦗E⦘ ⨾ lws ⨾ ⦗E⦘.
Proof using. dom_helper; rewrite wf_poE; basic_solver. Qed.

Lemma wf_obsE WF: obs ≡ ⦗E⦘ ⨾ obs ⨾ ⦗E⦘.
Proof using. dom_helper; rewrite wf_rfeE, wf_coeE, wf_freE; basic_solver. Qed.

Lemma wf_dobE WF: dob ≡ ⦗E⦘ ⨾ dob ⨾ ⦗E⦘.
Proof using.
  dom_helper; rewrite wf_addrE, wf_dataE, wf_ctrlE, wf_poE, wf_lrsE; basic_solver.
Qed.

Lemma wf_aobE WF: aob ≡ ⦗E⦘ ⨾ aob ⨾ ⦗E⦘.
Proof using. dom_helper; rewrite wf_rmwE, wf_lrsE; basic_solver. Qed.

Lemma wf_bobE WF: bob ≡ ⦗E⦘ ⨾ bob ⨾ ⦗E⦘.
Proof using. dom_helper; rewrite wf_poE; basic_solver. Qed.

Lemma wf_lobE WF: lob ≡ ⦗E⦘ ⨾ lob ⨾ ⦗E⦘.
Proof using.
  split; [|basic_solver].
  unfold lob.
  rewrite <- inclusion_ct_seq_eqv_r.
  rewrite <- inclusion_ct_seq_eqv_l.
  apply inclusion_t_t.
  rewrite (wf_lwsE WF) at 1.
  rewrite (wf_dobE WF) at 1.
  rewrite (wf_aobE WF) at 1.
  rewrite (wf_bobE WF) at 1.
  rewrite (wf_siE WF) at 1.
  basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_lrsD: lrs ≡ ⦗W⦘ ⨾ lrs ⨾ ⦗R⦘.
Proof using. dom_helper; basic_solver. Qed.

Lemma wf_lwsD: lws ≡ ⦗RW⦘ ⨾ lws ⨾ ⦗W⦘.
Proof using. dom_helper; basic_solver. Qed.

Lemma wf_obsD WF: obs ≡ ⦗RW⦘ ⨾ obs ⨾ ⦗RW⦘.
Proof using. dom_helper; rewrite wf_rfeD, wf_coeD, wf_freD; basic_solver. Qed.

Lemma wf_dobD WF: dob ≡ dob ⨾ ⦗RW⦘.
Proof using.
  split; [|basic_solver].
  unfold dob.
  rewrite (dom_r (wf_addrD WF)) at 1.
  rewrite (dom_r (wf_dataD WF)) at 1.
  rewrite (dom_r (wf_lrsD)) at 1.
  basic_solver 42.
Qed.

Lemma wf_aobD WF: aob ≡ aob ⨾ ⦗RW⦘.
Proof using.
  split; [|basic_solver].
  unfold aob.
  rewrite (dom_r (wf_rmwD WF)) at 1.
  basic_solver 42.
Qed.


(******************************************************************************)
(** ** Inclusions in program order  *)
(******************************************************************************)

Hint Rewrite inclusion_seq_eqv_l inclusion_seq_eqv_r po_po unionK : in_po.
Hint Rewrite rmw_in_po data_in_po addr_in_po ctrl_in_po po_si : in_po.

Ltac solve_in_po :=
  match goal with |- ?x ⊆ _ => unfold x end;
  autorewrite with in_po; ins; try basic_solver.

Lemma amo_in_po WF: amo ⊆ po.
Proof using. arewrite (amo ⊆ rmw); auto using rmw_in_po. Qed.
Hint Rewrite amo_in_po : in_po.

Lemma lws_in_po: lws ⊆ po.
Proof using. solve_in_po. Qed.
Hint Rewrite lws_in_po : in_po.

Lemma lrs_in_po: lrs ⊆ po.
Proof using. solve_in_po. Qed.
Hint Rewrite lrs_in_po : in_po.

Lemma dob_in_po WF: dob ⊆ po.
Proof using. solve_in_po. Qed.
Hint Rewrite dob_in_po : in_po.

Lemma aob_in_po WF: aob ⊆ po.
Proof using. solve_in_po. Qed.
Hint Rewrite aob_in_po : in_po.

Lemma bob_in_po WF: bob ⊆ po.
Proof using. solve_in_po. Qed.
Hint Rewrite bob_in_po : in_po.

Lemma lob_in_po WF: lob ⊆ po.
Proof using. solve_in_po; generalize (@po_trans G); rels. Qed.


(******************************************************************************)
(** ** Properties of consistent executions  *)
(******************************************************************************)

Lemma wf_ecol WF: eco ⊆ same_loc.
Proof using.
  unfold Execution_eco.eco; rewrite wf_rfl, wf_col, wf_frl; ins.
  unfolder; ins; desf; congruence.
Qed.

Lemma InternalConsistent_sc_per_loc WF (INT : InternalConsistent) : sc_per_loc G.
Proof using.
  assert (IRR: irreflexive (po ∩ same_loc ⨾ eco)). {
    eapply irreflexive_inclusion, INT.
    rewrite ct_begin, <- inclusion_t_rt, eco_alt3; ins.
    apply seq_mori, clos_trans_mori; basic_solver 10.
  }
  clear INT; red; unfolder in *; ins; desf.
  eapply IRR; eexists; splits; eauto.
  eapply wf_ecol in H0; ins; congruence.
Qed.

Lemma obs_in_eco : obs ⊆ eco.
Proof using. unfold Arm.obs. rewrite rfe_in_eco, fre_in_eco, coe_in_eco. eauto with hahn. Qed.

Lemma eco_in_po_obs_po WF :  eco ⊆ po^? ⨾ obs^? ⨾ obs^? ⨾ po^?.
Proof using.
  rewrite (eco_alt WF).
  rewrite cr_union_r, seq_union_l.
  rewrite coi_union_coe, fri_union_fre, rfi_union_rfe.
  rewrite coi_in_po, fri_in_po, rfi_in_po.
  arewrite (coe ⊆ obs).
  arewrite (fre ⊆ obs).
  arewrite (rfe ⊆ obs).
  rewrite !seq_union_l, !seq_union_r.
  basic_solver 20.
Qed.

Lemma coi_lws WF SC_PER_LOC : coi ≡ ⦗W⦘ ⨾ lws.
Proof using.
  unfold Execution.coi, lws.
  rewrite (wf_coD WF).
  unfolder; split; ins; desf; splits; ins; auto using (wf_col WF);
    try type_solver.
  destruct (classic (x = y)) as [|NEQ]; desf.
    by exfalso; eapply po_irr; eauto.
  eapply wf_poE in H0; unfolder in H0; desc.
  eapply (wf_co_total WF) in NEQ; desf; unfolder; ins; desf.
  edestruct SC_PER_LOC; unfold Execution_eco.eco; unfolder; eauto 8.
Qed.

Lemma fri_lws WF COMP SC_PER_LOC : fri ≡ ⦗R⦘ ⨾ lws.
Proof using.
  unfold Execution.fri, lws.
  rewrite (wf_frD WF).
  unfolder; split; ins; desf; splits; ins; auto using (wf_frl WF);
    try type_solver.
  red; unfolder.
  eapply wf_poE in H0; unfolder in H0; desc.
  assert (RF: exists w, rf w x) by (eapply COMP; ins); desc.
  destruct (classic (w = y)) as [|NEQ]; desf.
    by edestruct SC_PER_LOC; unfold Execution_eco.eco; unfolder; eauto 8.
  eapply (wf_rfE WF) in RF; unfolder in RF; desc.
  eapply (wf_rfD WF) in RF0; unfolder in RF0; desc.
  eapply (wf_co_total WF) in NEQ; desf; unfolder; ins; desf; splits; eauto.
    by edestruct SC_PER_LOC; unfold Execution_eco.eco; unfolder; eauto 8.
  eapply (wf_rfl WF) in RF2; unfold Events.same_loc in *; congruence.
Qed.

Lemma lws_expand WF COMP SC_PER_LOC : lws ≡ coi ∪ fri.
Proof using.
  rewrite fri_lws, coi_lws; ins.
  rewrite (dom_l wf_lwsD) at 1; ins.
  basic_solver.
Qed.

Lemma bob_fri WF : bob ⨾ fri ⊆ bob ⨾ bob^?.
Proof using.
  unfold bob at 1; relsf; rewrite ?seqA.
  arewrite_false (⦗W⦘ ⨾ fri).
  { rewrite (wf_friD WF). type_solver. }
  arewrite_false (⦗L⦘ ⨾ fri).
  { rewrite (wf_friD WF). type_solver. }
  repeat first [rewrite union_false_r |
                rewrite union_false_l |
                rewrite seq_false_r | rewrite seq_false_l ].
  arewrite (fri ⊆ po).
  sin_rewrite !(@po_po G).
  assert (bob ⊆ bob ⨾ bob^?) as AA by basic_solver.
  unionL.
  all: try by rewrite <- AA; unfold bob; eauto 8 with hahn.
  arewrite (⦗A⦘ ⊆ ⦗A⦘ ⨾ ⦗A ∪₁ Q ⦘) by type_solver.
  arewrite (⦗A ∪₁ Q⦘ ⨾ po ⊆ bob).
  arewrite (⦗L⦘ ⨾ po ⨾ ⦗A⦘ ⊆ bob); auto with hahn.
  unionR left; eauto with hahn.
Qed.

Lemma co_in_ob WF SC_PER_LOC : co ⊆ obs ∪ lob.
Proof using.
  rewrite coi_union_coe, coi_lws; ins; unfold obs, lob.
  unionL; unfolder; ins; desf; eauto 8 using t_step with hahn.
  assert (si y y); eauto 8 using t_step with hahn.
  red; apply wf_lwsE in H0; ins; unfolder in *; desf; eauto using ext_si_refl.
Qed.

Lemma fr_in_ob WF COMP SC_PER_LOC : fr ⊆ obs ∪ lob.
Proof using.
  rewrite fri_union_fre, fri_lws; ins; unfold obs, lob.
  unionL; unfolder; ins; desf; eauto 8 using t_step with hahn.
  assert (si y y); eauto 8 using t_step with hahn.
  red; apply wf_lwsE in H0; ins; unfolder in *; desf; eauto using ext_si_refl.
Qed.

Lemma po_loc_ww WF SC_PER_LOC x y (PO : po x y)
      (Wx : W x) (Wy: W y) (SL: same_loc x y) : co x y.
Proof using.
  assert (N: x <> y) by (intro; desf; eapply po_irr; eauto).
  eapply wf_poE in PO; unfolder in PO; desf.
  eapply (wf_co_total WF) in N; unfolder; splits; ins; desf.
  exfalso; eapply SC_PER_LOC; unfold Execution_eco.eco.
  unfolder; eauto 10.
Qed.

Lemma im0_in_co WF SC_PER_LOC : im0 ⊆ co.
Proof using.
  unfold im0; unfolder; ins; desc.
  forward eapply (wf_co_total WF) with (a := x) (b := y); unfolder; splits; ins; try intro; desf;
    auto using (init_w WF).
  exfalso; eapply (SC_PER_LOC x); unfold Execution_eco.eco.
  edestruct no_co_to_init; eauto; unfolder in *; desf.
Qed.

Lemma no_obs_to_init WF SC_PER_LOC : obs ⊆ (fun _ => True) × (set_compl is_init).
Proof using.
  unfold obs; ie_unfolder.
  rewrite no_rf_to_init, no_co_to_init, no_fr_to_init; basic_solver.
Qed.

Lemma no_lob_to_init WF SC_PER_LOC : lob ⊆ (fun _ => True) × (set_compl is_init).
Proof using.
  rewrite lob_in_po, no_po_to_init; ins; basic_solver.
Qed.

Lemma si_init : si ⊆ is_init × is_init ∪ set_compl is_init × set_compl is_init.
Proof using.
  unfold Execution.si, ext_si; unfolder; ins; desf; ins; tauto.
Qed.

(******************************************************************************)
(** ** Equivalence to external completion model  *)
(******************************************************************************)

Lemma L_si WF : ⦗L⦘ ⨾ si ≡ si ⨾ ⦗L⦘.
Proof using.
  unfolder; split; ins; desf; forward eapply (wf_siD WF) as X; eauto.
  all: split; ins.
  all: unfold is_w, is_w_rel in *; desf; ins; desf.
Qed.

Lemma A_si WF : ⦗A⦘ ⨾ si ≡ si ⨾ ⦗A⦘.
Proof using.
  unfolder; split; ins; desf; forward eapply (wf_siD WF) as X; eauto.
  all: split; ins.
  all: unfold is_r, is_r_acqSC in *; desf; ins; desf.
Qed.

Lemma Q_si WF : ⦗Q⦘ ⨾ si ≡ si ⨾ ⦗Q⦘.
Proof using.
  unfolder; split; ins; desf; forward eapply (wf_siD WF) as X; eauto.
  all: split; ins.
  all: unfold is_r, is_r_acqPC in *; desf; ins; desf.
Qed.

Lemma bob_si WF : bob ⨾ si ≡ bob.
Proof using.
  unfold bob; rewrite id_union; relsf.
  rewrite ?seqA, A_si, L_si, W_si, !po_si; ins.
  seq_rewrite !po_si; ins.
Qed.

Lemma scaob_scaob WF : scaob ⨾ scaob ≡ ∅₂ .
Proof using.
  unfold scaob; ie_unfolder; unfolder; split; ins; desf.
   assert (x2 = x1) by (eapply (wf_rff WF); eauto); desf.
Qed.


Ltac rf_matcher :=
  repeat match goal with
    H : rf ?y ?x , H': rf ?z ?x |- _ =>
    assert (z = y); [solve [eapply wf_rff; eauto]|clear H']; clarify
  end.

Lemma erln_refl x : E x -> erln x x.
Proof using.
  vauto.
Qed.

Local Hint Resolve erln_refl : core.

Lemma erln_scaob WF : erln ⨾ scaob ≡ scaob .
Proof using.
  unfold erln, scaob, rfisw; split.
  { ie_unfolder.
    rewrite (wf_rfD WF) at 1 2 3 4 5 6.
    rewrite !seq_union_l; unionL.
    unfolder; ins; exfalso; desf; type_solver.
    all: unfolder; ins; desf; rf_matcher.
    all: splits; eauto; apply si_si; unfolder; eauto. }
  rewrite wf_siE at 1; basic_solver 10.
Qed.

Lemma scaob_erln WF : scaob ⨾ erln ⊆ scaob .
Proof using.
  unfold erln, scaob, rfisw; ie_unfolder.
  rewrite (wf_rfD WF) at 1 2 3 4 5 6.
  rewrite !seq_union_r; unionL.
  unfolder; ins; exfalso; desf; type_solver.
  unfolder; ins; exfalso; desf; rf_matcher.
  rewrite <- si_si at 4; ins.
  all: unfolder; ins; desf; splits; eauto.
Qed.

Lemma coh_helper WF SC_PER_LOC x y z (RF : rf z y) :
  po z x ->
  po x y ->
  is_w lab x ->
  same_loc x y ->
  False.
Proof using.
  ins; assert (same_loc z y) by (apply wf_rfl; auto).
  assert (X: same_loc z x) by congruence.
  apply po_loc_ww in X; ins.
  apply (SC_PER_LOC x); exists y; split; ins; apply fr_in_eco; eexists; vauto.
  apply wf_rfD in RF; unfolder in RF; desf.
Qed.

Lemma lrs_erln WF SC_PER_LOC :
  lrs ⨾ erln ⊆  si ⨾ lrs ∪ (obs ⨾ si)⁺ ∪ is_init × set_compl is_init.
Proof using.
  unfold lrs, erln, rfisw; ie_unfolder.
  rewrite wf_rfD, wf_rfE; ins.
  rewrite wf_poE at 1; ins.
  unfolder; ins; desf.
  { type_solver. }
  {
    assert (SL: same_loc x1 z0) by (eapply (wf_rfl WF); eauto).
    assert (NEQ: x <> x1) by (intro; desf).
    eapply wf_co_total in NEQ; unfolder; ins; eauto; desf.
    2: { exfalso; eapply SC_PER_LOC with x; exists z0; split; ins.
         eapply fr_in_eco; eexists; split; eauto. }
    destruct (classic (is_init x)) as [INIT | NINIT].
    { right; split; ins.
      eapply no_rf_to_init in H11; unfolder in *; desf. }
    left; right; eapply t_trans with x1; eapply t_step.
    { eexists; splits; eauto using si_refl.
      left; right; split; ins.
      intro.
      rename x1 into w, z0 into r, y into r', x0 into w', x into ww.
      forward apply po_semi_total_l with (y := r) (z := w) as X; eauto; desf.
      - eapply (SC_PER_LOC r); exists w; split; try apply rf_in_eco; ins.
      - eapply wf_siD in X; ins.
        eapply wf_rfD in H16; ins; type_solver. }
    eexists; split; vauto.
  }
  { assert (SL: same_loc z1 z0) by (apply wf_rfl; eauto).
    forward eapply po_semi_total_r with (y := x) (z := z1) as PO; eauto.
    desf.
      by destruct H4; do 2 (eexists; splits; eauto).
      by exfalso; eauto using coh_helper.
      { assert (z1 = x); desf.
          unfold is_init, Events.same_loc in *; desf; ins.
          unfold loc in *; rewrite wf_init_lab in *; desf.
        left; left; exists z2; splits; try apply wf_rfl; unfolder; eauto.
        intro; desf; eauto using coh_helper.
      }
    left; left; exists z2; splits; try apply wf_rfl; try apply si_si; unfolder; eauto.
    intro; desf; eauto using coh_helper.
  }
  { eauto 10 using si_refl. }
Qed.

Lemma dob_erln WF SC_PER_LOC : dob ⨾ erln ⊆ dob ∪ dob ⨾ (obs ⨾ si)⁺.
Proof using.
  unfold dob at 1 2; rewrite ?seq_union_l, ?seqA.
  rewrite lrs_erln, ?seq_union_r; ins.
  rewrite erln_in_si, W_si, R_si, addr_si, data_si; ins.
  seq_rewrite !po_si; ins.
  seq_rewrite !ctrl_si; ins.
  seq_rewrite !addr_si; ins.
  seq_rewrite !data_si; ins.
  unionL; eauto 8 with hahn.
  rewrite addr_in_po at 1; ins; rewrite no_po_to_init; unfolder; ins; desf.
  rewrite data_in_po at 1; ins; rewrite no_po_to_init; unfolder; ins; desf.
Qed.

Lemma rmw_in_lws WF :
  rmw ⊆ lws.
Proof using.
  rewrite wf_rmwD, rmw_in_po_loc; ins.
  unfold lws; eauto with hahn.
Qed.

Lemma aob_erln WF SC_PER_LOC :
  aob ⨾ erln ⊆ (obs ⨾ si ∪ lob)⁺ ∪ ⦗ W_ex ⦘ ⨾ si ⨾ aob ∪ is_init × set_compl is_init.
Proof using.
  unfold aob; rewrite ?seq_union_l, ?seqA.
  unionL; eauto with hahn.
  { unfold lob; unionR left -> left; rewrite <- 2!ct_step.
    rewrite erln_in_si, rmw_in_lws; eauto with hahn. }
  { arewrite ( ⦗ A ∪₁ Q ⦘ ⨾ erln ⊆ erln ⨾ ⦗ A ∪₁ Q ⦘).
    { unfolder; ins; desf; split; ins.
      all: apply erln_in_si in H0.
      forward apply (proj1 (A_si WF)) with (x := x) (y := y) as X;
        unfolder in *; desf; eauto.
      forward apply (proj1 (Q_si WF)) with (x := x) (y := y) as X;
        unfolder in *; desf; eauto. }
    sin_rewrite lrs_erln; ins.
    rewrite ?seq_union_l, ?seq_union_r, ?seqA.
    seq_rewrite !W_ex_si; ins; rewrite ?seqA; rels.
    unionL; eauto with hahn; try basic_solver.
    unionR left -> left; rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r.
    eauto with hahn.
  }
Qed.

Lemma lrs_si_aob WF : lrs ⨾ si ⨾ aob ⊆ lob.
Proof using.
  transitivity (lws ⨾ si); eauto with hahn.
  unfold lrs, lws, aob.
  rewrite ?seq_union_r, si_rmw, wf_rmwD, ?seqA; ins.
  unionL.
  { rewrite rmw_in_po_loc; ins; unfolder; ins; desf.
    eexists; splits; eauto; exists z2; splits; try eapply po_trans; eauto; congruence. }
  seq_rewrite <- W_ex_si; ins; rewrite ?seqA.
  rewrite W_ex_in_W; unfolder; ins; desc; type_solver.
Qed.

Lemma dob_si_aob WF : dob ⨾ si ⨾ aob ⊆ lob.
Proof using.
  unfold dob; rewrite ?seq_union_l, ?seqA.
  rewrite lrs_si_aob, ?seq_union_r; ins.
  seq_rewrite W_si; ins.
  seq_rewrite R_si; ins; rewrite ?seqA.
  seq_rewrite !po_si; ins.
  seq_rewrite !ctrl_si; ins.
  seq_rewrite !addr_si; ins.
  seq_rewrite !data_si; ins.
  arewrite (aob ⊆ lob).
  rewrite <- ?seqA, <- !seq_union_l, ?seqA.
  apply inclusion_seq_trans; vauto.
  transitivity dob; ins; eauto with hahn.
Qed.

Lemma aob_si_aob WF : aob ⨾ si ⨾ aob ⊆ lob ∪ si ⨾ aob⁺.
Proof using.
  unfold aob at 1; rewrite ?seq_union_l, ?seqA.
  rewrite 2!inclusion_seq_eqv_l, lrs_si_aob; unionL; ins; auto with hahn.
  seq_rewrite <- si_rmw; ins.
  arewrite ( rmw ⊆ aob^* ); rels.
Qed.

Lemma aob_Wex WF : aob⨾ eqv_rel W_ex ⊆ lws.
Proof using.
  unfold aob; rewrite rmw_in_lws, seq_union_l, inclusion_seq_eqv_l at 1; ins.
  unionL; try basic_solver.
  rewrite W_ex_in_W; type_solver.
Qed.

Lemma lob_si_aob WF SC_PER_LOC :
   lob ⨾ ⦗W_ex ⦘ ⨾ si ⨾ aob ⊆ (obs ⨾ si ∪ lob)⁺ .
Proof using.
  unfold lob at 1.
  rewrite ct_end at 1; rewrite <- rt_ct, ?seqA.
  apply seq_mori; eauto with hahn.
  rewrite !seq_union_l, !seqA.
  sin_rewrite aob_Wex; ins.
  rewrite inclusion_seq_eqv_l; seq_rewrite si_si.
  sin_rewrite dob_si_aob; ins.
  seq_rewrite bob_si; ins.
  arewrite (bob ⊆ lob).
  arewrite !(lws ⨾ si ⊆ lob).
  arewrite ( aob ⊆ lob^* ); rels.
  unionL; eauto with hahn.
Qed.

Lemma ob_si_aob WF SC_PER_LOC :
   (obs ⨾ si ∪ lob)⁺ ⨾ ⦗W_ex ⦘ ⨾ si ⨾ aob ⊆ (obs ⨾ si ∪ lob)⁺ .
Proof using.
  rewrite ct_end at 1; rewrite <- rt_ct, ?seqA.
  apply seq_mori; eauto with hahn.
  rewrite !seq_union_l, !seqA, lob_si_aob; ins.
  rewrite inclusion_seq_eqv_l; seq_rewrite si_si.
  arewrite ( aob ⊆ lob^* ); rels.
  unionL; eauto with hahn.
  rewrite ct_begin, <- seqA; apply seq_mori; auto with hahn.
Qed.

Lemma lob_erln WF SC_PER_LOC :
  lob ⨾ erln ⊆ (obs ⨾ si ∪ lob)⁺ ∪ ⦗ W_ex ⦘ ⨾ si ⨾ aob ∪ is_init × set_compl is_init.
Proof using.
  unfold lob at 1; rewrite ct_end, seqA; ins.
  arewrite (clos_refl_trans (lws⨾ si ∪ dob ∪ aob ∪ bob) ⊆ lob^?) by unfold lob; rels.
  rewrite !seq_union_l, ?seqA.
  rewrite erln_in_si at 1 4; rewrite si_si, bob_si; ins.
  arewrite (lws ⨾ si ⊆ lob).
  arewrite (bob ⊆ lob).
  rewrite dob_erln; ins; arewrite (dob ⊆ lob).
  rewrite aob_erln; ins.
  repeat rewrite ?seq_union_l, ?seq_union_r.
  repeat arewrite (lob^? ⨾ lob ⊆ lob) by unfold lob; rels.
  unionL; eauto with hahn.
  - unionR left; rewrite ct_begin with (r := _ ∪ _); eauto with hahn.
  - unionR left; rewrite <- rt_ct with (r := _ ∪ _) at 2; eauto with hahn.
  - rewrite crE; relsf; unionL; eauto with hahn.
    rewrite lob_si_aob; ins; eauto with hahn.
  - rewrite lob_in_po at 1; ins; rewrite no_po_to_init; unfolder; ins; desf; eauto.
Qed.


Lemma lrs_scaob WF SC_PER_LOC :
  lrs ⨾ scaob ⊆  (obs ⨾ si)⁺ ∪ is_init × set_compl is_init.
Proof using.
  unfold lrs, scaob; ie_unfolder.
  rewrite wf_rfD, wf_rfE; ins.
  rewrite wf_poE at 1; ins.
  unfolder; ins; desf.
  assert (SL: same_loc x1 z0) by (eapply (wf_rfl WF); eauto).
  assert (NEQ: x <> x1) by (intro; desf).
  eapply wf_co_total in NEQ; unfolder; ins; eauto; desf.
  2: { exfalso; eapply SC_PER_LOC with x; exists z0; split; ins.
       eapply fr_in_eco; eexists; split; eauto. }
  destruct (classic (is_init x)) as [INIT | NINIT].
  { right; split; ins.
    eapply no_po_to_init in H5; unfolder in *; desf. }
  left; eapply t_trans with x1; eapply t_step.
  { eexists; splits; eauto using si_refl.
    left; right; split; ins.
    intro PO.
    forward eapply po_semi_total_l with (y := x1) (z := z0) as X; desf; eauto.
      by eapply SC_PER_LOC; eexists; split; [|eapply rf_in_eco]; eauto.
    apply (wf_rfD WF) in H11; unfolder in *; desc.
    apply (wf_siD WF) in X; type_solver.
  }
  eexists; split; vauto.
Qed.


Lemma dob_scaob WF SC_PER_LOC : dob ⨾ scaob ⊆ dob ∪ dob ⨾ (obs ⨾ si)⁺.
Proof using.
  unfold dob at 1 2; rewrite ?seq_union_l, ?seqA.
  do 6 arewrite (scaob ⊆ si) at 1.
  rewrite W_si, R_si, addr_si, data_si; ins.
  seq_rewrite !po_si; ins.
  seq_rewrite ctrl_si; ins.
  rewrite lrs_scaob; ins.
  rewrite !seq_union_r; unionL; eauto 8 with hahn.
  - rewrite addr_in_po at 1; ins; rewrite no_po_to_init at 1; basic_solver.
  - rewrite data_in_po at 1; ins; rewrite no_po_to_init at 1; basic_solver.
Qed.

Lemma aob_scaob WF SC_PER_LOC : aob ⨾ scaob ⊆ ⦗ W_ex ⦘ ⨾ (obs ⨾ si)⁺.
Proof using.
  unfold aob; rewrite ?seq_union_l, ?seqA.
  unionL; eauto with hahn.
  { unfold scaob at 1; rewrite wf_rmwD, wf_rfeD; ins.
    unfolder; ins; exfalso; ins; desf; eauto; type_solver. }
  rewrite inclusion_seq_eqv_l with (dom := A ∪₁ Q), lrs_scaob, seq_union_r; unionL; ins.
  unfold Execution.W_ex at 1; rewrite rmw_in_po, no_po_to_init; ins; basic_solver.
Qed.

Lemma lob_scaob WF SC_PER_LOC :
  lob ⨾ scaob ⊆ (obs ⨾ si ∪ lob)⁺.
Proof using.
  unfold lob at 1; rewrite ct_end, seqA; ins.
  arewrite (clos_refl_trans (lws⨾ si ∪ dob ∪ aob ∪ bob) ⊆ lob^?) by unfold lob; rels.
  rewrite !seq_union_l.
  arewrite (scaob ⊆ si) at 1; rewrite si_si; ins.
  arewrite (scaob ⊆ si) at 3; rewrite bob_si; ins.
  rewrite dob_scaob; ins.
  rewrite aob_scaob; ins.
  arewrite (lws ⨾ si ⊆ lob).
  arewrite (dob ⊆ lob).
  arewrite (bob ⊆ lob).
  repeat rewrite ?seq_union_l, ?seq_union_r.
  repeat arewrite (lob^? ⨾ lob ⊆ lob) by unfold lob; rels.
  rewrite inclusion_seq_eqv_l.
  unionL; eauto with hahn.
    rewrite ct_begin with (r := _ ∪ _); eauto with hahn.
    rewrite <- rt_ct with (r := _ ∪ _); eauto with hahn.
Qed.

Local Hint Resolve erln_sym : core.

Lemma erln_refl1 WF x y :
  (im0 ∪ obs⨾ si ∪ lob ∪ scaob) x y \/ (im0 ∪ obs⨾ si ∪ lob ∪ scaob) y x ->
  erln x x.
Proof using.
  unfold im0, scaob.
  right; split; ins.
  unfolder in *; ins; desf; eauto.
  all: try solve [match goal with H: si _ _ |- _ =>
                                  apply wf_siE in H; unfolder in H; desf
                  end].
  all: try solve [apply wf_lobE in H; unfolder in H; desf].
  apply wf_obsE in H; unfolder in H; desf.
Qed.

Local Hint Resolve erln_refl1 : core.

Lemma erln_refl2 WF x : erln x x <-> E x.
Proof using.
  unfold erln; unfolder; split; ins; desf; auto.
  all: apply wf_siE in H; unfolder in H; desf.
Qed.


Lemma acyclic_pre_helper
      WF SC_PER_LOC (ACYC : acyclic (obs ⨾ si ∪ lob)) :
 acyclic
    (eqv_rel W_ex⨾ si⨾ aob
     ∪ (scaob ∪ (clos_trans (obs⨾ si ∪ lob) ∪ is_init × set_compl is_init))).
Proof using.
  apply acyclic_absorb.
  {
    right; rewrite !seq_union_l; ins; unionL; eauto using ob_si_aob with hahn.
    unfold scaob; rewrite wf_rfiD, W_ex_in_W; unfolder; ins; desf; type_solver.
    rewrite aob_in_po, no_po_to_init; ins; unfolder; ins; desf; auto.
  }
  split.
  { rewrite <- seqA, acyclic_seqC.
    sin_rewrite aob_Wex; ins.
    arewrite (lws ⨾ si ⊆ lob); eauto with hahn. }
  apply acyclic_absorb.
  { right.
    rewrite ct_end at 1.
    rewrite ?seq_union_r, !seq_union_l, ?seqA, lob_scaob; ins.
    arewrite (scaob ⊆ si); rewrite si_si, rt_ct.
    unionL; eauto with hahn.
      by rewrite ct_end; eauto with hahn.
    rewrite si_init at 1; unfolder; ins; desf; eauto.
  }
  split; auto using acyclic_disj, scaob_scaob.
  red; rewrite ct_of_union_ct_l.
  apply acyclic_absorb.
  right.
  rewrite lob_in_po, no_po_to_init, no_obs_to_init, si_init; ins; basic_solver.
  split; ins; apply acyclic_disj; basic_solver.
Qed.


Lemma acyclic_pre_ec
      WF SC_PER_LOC (ACYC : acyclic (obs ⨾ si ∪ lob)) :
  acyclic (lift erln (im0 ∪ obs ⨾ si ∪ lob ∪ scaob)).
Proof using.
  apply acyclic_lift; eauto.
  rewrite !seq_union_l, ?seqA.
  rewrite lob_erln, scaob_erln; ins.
  rewrite erln_in_si, si_si.
  arewrite (im0 ⨾ si ⊆ is_init × set_compl is_init).
  { rewrite si_init; unfold im0; unfolder; ins; desf. }

  eapply inclusion_acyclic, acyclic_pre_helper; ins.
  unionL; eauto with hahn.
Qed.

Lemma partial_order_pre_ec
      WF SC_PER_LOC (ACYC : acyclic (obs ⨾ si ∪ lob)) :
  strict_partial_order (lift erln (im0 ∪ obs ⨾ si ∪ lob ∪ scaob))⁺ .
Proof using.
  split; ins; apply acyclic_pre_ec; ins.
Qed.

Lemma co_in_ob2 WF SC_PER_LOC : co ⊆ obs ⨾ si ∪ lob.
Proof using.
  rewrite co_in_ob, wf_obsE at 1; ins; unfolder; ins; desf; eauto using si_refl.
Qed.

Lemma fr_in_ob2 WF COMP SC_PER_LOC : fr ⊆ obs ⨾ si ∪ lob.
Proof using.
  rewrite fri_union_fre, fri_lws; ins; unfold obs, lob.
  unionL; unfolder; ins; desf; eauto 8 using t_step with hahn.
  all: assert (si y y); eauto 8 using t_step with hahn.
  red; apply wf_lwsE in H0; ins; unfolder in *; desf; eauto 8 using ext_si_refl.
  red; apply wf_freE in H; ins; unfolder in *; desf; eauto 8 using ext_si_refl.
Qed.


Lemma step_lift2 T (eqv r : relation T) x y :
  r x y -> (lift eqv r) (eqv x) (eqv y).
Proof using.
  unfolder; eauto 10.
Qed.


Lemma ArmConsistent_implies_ExtComp (C : ArmConsistent) : ArmConsistentExtComp.
Proof using.
  unfold ArmConsistent, ArmConsistentExtComp, ArmCommon, linearization_of in *; desf; unnw.
  splits; ins; assert (SC_PER_LOC := InternalConsistent_sc_per_loc WF INTERNAL).
  forward eapply (partial_order_included_in_total_order) as (cb & INCL & (IRR & TRANS) & TOT).
  { eapply partial_order_pre_ec; eauto. }
  exists (restr_rel (classes erln) cb).
  unfold rf_fwd, rf_nfwd; rewrite delift_restr_classes.
  assert (CO_EQ: co ≡ delift erln cb ∩ same_loc ∩ W × W).
  {
    split.
      rewrite wf_coE, wf_coD, <- INCL, delift_ct_lift; eauto.
      arewrite (co ⊆ co ∩ co); rewrite co_in_ob2 at 1; ins; rewrite wf_col; ins.
      rewrite <- ct_step; unfolder; ins; desf; splits; ins;
        exists x; splits; ins; try exists y; splits; eauto 8;
          eapply erln_refl1; unfolder; eauto 8.
    unfolder; ins; desf.
    forward eapply wf_co_total with (a := x) (b := y); eauto; unfolder; splits; ins; desf.
    - eapply erln_in_si, wf_siE in H3; unfolder in H3; ins; desf. 
    - eapply erln_in_si, wf_siE in H4; unfolder in H4; ins; desf. 
    - intro; desf; eauto.
    - exfalso; eapply IRR, TRANS, INCL, ct_step, step_lift2; eauto.
      apply co_in_ob2 in H5; ins; unfolder in H5; unfolder; desf; eauto 8.
  }
  splits; ins.
  { rewrite restr_relEE, <- INCL, <- ct_step; apply inclusion_inter_r.
    apply lift_mori; ins; unionL; eauto with hahn.
    unfolder; ins; desc; splits; eauto.
  }
  { split; [split;  eauto using irreflexive_restr, transitive_restr|].
    eapply is_total_restr. red; ins; apply TOT; auto. }
  { basic_solver. }

  rewrite  wf_rfE, wf_rfD; ins.
  split; unfolder; ins; desf.
  {
    assert (Sxy: same_loc x y) by (apply (wf_rfl WF); ins).
    assert (NEQ: forall X (xEQ: X ≡₁ erln x) Y (yEQ: Y ≡₁ erln y),
               cb X Y \/ cb Y X).
    {
      ins; forward eapply TOT with (a := X) (b := Y) as T; ins.
      intro M; apply f_equal with (f := fun f => f x) in M.
      assert (Z: erln x x); [ by vauto | apply xEQ in Z; rewrite M in Z; clear M].
      apply yEQ in Z; unfold erln in Z; unfolder in Z; desf; try type_solver.
      apply wf_rfeD in Z1; ins; unfolder in Z1; desf; type_solver.
    }
    forward apply NEQ with (X := erln x) (Y := erln y) as N; ins.
    desf; [right | left]; splits; ins; desc.
    all: try rewrite erln_refl2; ins.
    
    {
      intro; desc.
      assert (COxz: co x z); [ | clear H4; desf]. {
        clear H6; desf; [apply CO_EQ; unfolder; splits; ins| eapply po_loc_ww]; ins; eauto.
        all: unfold Events.same_loc in *; congruence.
      }
      { eapply (IRR (erln z)), TRANS, INCL, ct_step, step_lift2; eauto.
        forward eapply fr_in_ob2 with (x := y) (y := z); vauto; unfolder; ins; desf; eauto 8. }
      eapply (SC_PER_LOC z); unfold Execution_eco.eco, Execution.fr; unfolder; eauto 10.
    }
    { apply NNPP; intro.
      eapply IRR, TRANS, INCL, t_step;
        unfold obs, Execution.rfe; unfolder; eauto 20 using si_refl.
    }
    { intro; desc.
      eapply po_loc_ww in H4; eauto.
      eapply (SC_PER_LOC z); unfold Execution_eco.eco, Execution.fr; unfolder; eauto 10.
      unfold Events.same_loc in *; congruence.
    }
  }
  {
    apply erln_in_si, wf_siE in H3; ins; destruct H3 as (m & [Ex ?] & _); subst m.
    apply erln_in_si, wf_siE in H4; ins; destruct H4 as (m & [Ey ?] & _); subst m.
    splits; ins.
    eapply wf_poE in H5; unfolder in H5; desf.
    forward eapply COMP with (x:=y) as [w RF]; ins.
    assert (Swy: same_loc w y) by (apply (wf_rfl WF); ins).
    destruct (classic (x = w)) as [|NEQ]; desf.
    hahn_rewrite (wf_rfE WF) in RF; unfolder in RF; desf.
    hahn_rewrite (wf_rfD WF) in RF0; unfolder in RF0; desf.
    exfalso; destruct (classic (is_init w)) as [|NINIT]. {
       assert (MO: po w x). {
         unfold Execution.po, ext_sb; unfolder; desf; ins.
         destruct NEQ; f_equal; unfold Events.same_loc in *.
         unfold Events.loc in *; rewrite (wf_init_lab WF) in *; desf.
       }
       apply po_loc_ww in MO; ins.
       eapply (SC_PER_LOC x); unfold Execution_eco.eco, Execution.fr; unfolder; eauto 10.
       unfold Events.same_loc in *; congruence.
    }
    assert (MO  := NEQ).
    eapply (wf_co_total WF) in MO; unfolder; splits; ins.
    2: unfold Events.same_loc in *; congruence.
    desf.
    2: eapply (SC_PER_LOC x); unfold Execution_eco.eco, Execution.fr; unfolder; eauto 10.
    destruct (classic (po w y)) as [PO | NPO].
    {
      destruct H0; eexists w; splits; eauto.
      eapply po_semi_total_r with (y := x) in PO; desf; eauto.
      exfalso; eapply (SC_PER_LOC w); unfold Execution_eco.eco; basic_solver 20.
      destruct NEQ; eapply (wf_sil WF); split; ins; congruence.
    }
    { eapply IRR, TRANS, TRANS; eauto.
      all: eapply INCL, ct_step, step_lift2; eauto.
      apply co_in_ob2 in MO; ins; left; hahn_rewrite unionA; right; eassumption.
      left; left; right; eexists; split; auto using si_refl; vauto.
    }
  }
  {
    apply erln_in_si, wf_siE in H3; ins; destruct H3 as (m & [Ex ?] & _); subst m.
    apply erln_in_si, wf_siE in H4; ins; destruct H4 as (m & [Ey ?] & _); subst m.
    splits; ins.
    forward eapply COMP with (x:=y) as [w RF]; ins.

    assert (Swy: same_loc w y) by (apply (wf_rfl WF); ins).
    destruct (classic (x = w)) as [|NEQ]; desf.
    hahn_rewrite (wf_rfE WF) in RF; unfolder in RF; desf.
    hahn_rewrite (wf_rfD WF) in RF0; unfolder in RF0; desf.
    exfalso.
    assert (MO  := NEQ).
    eapply (wf_co_total WF) in MO; unfolder; splits; ins.
    2: unfold Events.same_loc in *; congruence.
    desf.
    {
      destruct H0; eexists w; splits; eauto.
        by apply CO_EQ in MO; unfolder in MO; desc; auto.
      destruct (classic (po w y)) as [PO | NPO]; eauto.
      left; splits; ins; vauto; apply INCL, ct_step, step_lift2.
      left; left; right; eexists; split; auto using si_refl; vauto.
    }
    { eapply IRR, TRANS, INCL, ct_step, step_lift2; eauto.
      forward apply fr_in_ob2 with (x := y) (y := x); vauto.
      unfolder; ins; desf; eauto 8 using si_refl.
    }
  }
Qed.


Lemma obs_si_scaob WF COMP :
  obs ⨾ si ≡ obs ⨾ erln ∪  rfe ⨾ scaob.
Proof using.
  unfold obs; split.
    2: by rewrite erln_in_si; ins; unfold scaob; unfolder; ins; desf; eauto.
  unfold erln; unfolder; ins; desf.
  all: forward apply wf_siD as D; eauto.
  { apply (wf_rfeD WF) in H; unfolder in H; desc.
    apply wf_rfeD in H1; unfolder in H1; ins; desc.
    apply wf_siE in H0; unfolder in H0; ins; desc.
    forward apply COMP with (x := y) as [k RF].
      split; ins; type_solver.
      destruct (classic (po k y)).
        by right; unfold scaob; ie_unfolder; unfolder; eauto 10.
      ie_unfolder; unfolder; left; eexists; splits; eauto 10. }
  { apply (wf_coeD WF) in H; unfolder in H; desc.
    left; eexists; splits; eauto.
    do 3 left; splits; ins; type_solver. }
  { apply (wf_freD WF) in H; unfolder in H; desc.
    left; eexists; splits; eauto.
    do 3 left; splits; ins; type_solver. }
Qed.


Lemma erln_rewrite WF x y : erln x y -> erln x = erln y.
Proof using.
  ins; eapply set_irr; unfolder; split; ins.
  all: eapply erln_trans; eauto.
Qed.

Lemma ArmConsistentExtComp_equiv :
  ArmConsistent <-> ArmConsistentExtComp.
Proof using.
  split; auto using ArmConsistent_implies_ExtComp.
  unfold ArmConsistent, ArmConsistentExtComp, ArmCommon, linearization_of in *.
  ins; desf; unnw.
  destruct STO as [[cbIRR cbTRAN] Tcb].
  assert (RFE_IN : rfe ⊆ delift erln cb). {
    unfold Execution.rfe; rewrite RF; unfold rf_fwd, rf_nfwd.
    unfolder; ins; desf.
  }
  assert (FR_IN : fr ⊆ delift erln cb). {
    unfold Execution.fr; rewrite RF, CO; unfold rf_fwd, rf_nfwd.
    unfolder; ins; desf; eauto.
    forward apply Tcb with (a := erln x) (b := erln y) as X.
      1-2: solve [ unfolder; ins; eauto ].
      intro Y; apply f_equal with (f := fun f => f x) in Y.
      assert (Z: erln x x); [ by vauto | rewrite Y in Z; clear Y].
      unfold erln in Z; unfolder in Z; desf; try type_solver.
      apply wf_rfeD in Z0; ins; unfolder in Z0; desf; type_solver.
    desf; eauto.
    destruct H6; exists y; splits; eauto; congruence.
  }
  splits; ins.
  {
    eapply irreflexive_inclusion with (r' := delift erln cb).
    2: by unfolder; ins; desf; eauto.
    apply inclusion_t_ind; ins.
    2: by unfolder; ins; desf; eauto.
    rewrite obs_si_scaob; ins.
    unfold obs; rewrite ?seq_union_l, RFE_IN, coe_in_co, CO, fre_in_fr, FR_IN.
      unfolder; ins; desf; splits;
        try rewrite erln_refl2 in *; ins.
      all: try solve [rewrite (erln_rewrite WF H0) in *; ins].
      all: try solve [eapply erln_in_si, wf_siE in H0; unfolder in H0; desf].
      all: try solve [unfold scaob, Execution.si in H0; unfolder in H0; desf].
      all: try solve [apply lob_in_po, wf_poE in H; unfolder in H; desf].
      eapply cbTRAN, INCL; eauto; unfolder; eauto 8.
      eapply INCL; eauto; unfolder; eauto 10.
  }
Qed.


(******************************************************************************)
(** ** Equivalence to global external completion model  *)
(******************************************************************************)


Lemma acyclic_pre_gcb1 WF COMP SC_PER_LOC (ACYC : acyclic (obs ⨾ si ∪ lob)) :
  acyclic ((rfi ∪ is_init × set_compl is_init
            ∪ scaob
            ∪ erln ⨾ obs ⨾ si
            ∪ erln ⨾ (lob ∩ gc_req)) ⨾ erln).
Proof using.
  rewrite !seq_union_l.
  arewrite (is_init × set_compl is_init⨾ erln ⊆ is_init × set_compl is_init)
    by rewrite erln_in_si, si_init; basic_solver.
  arewrite (si ⨾ erln ⊆ si)
    by rewrite erln_in_si, si_si.
  assert (RO: rfi ⨾ erln ⨾ obs ⊆ is_init × set_compl is_init ∪ erln ⨾ coe). {
    unfold obs; relsf; unionL.
    rewrite erln_in_si at 1; rewrite (wf_rfiD WF), (wf_rfeD WF); unfolder; ins; desf;
      eapply wf_siD in H2; desf; type_solver.
    rewrite erln_in_si at 1; rewrite (wf_rfiD WF), (wf_coeD WF); unfolder; ins; desf;
      eapply wf_siD in H2; desf; type_solver.
    arewrite (rfi ⨾ erln ⊆ (si ⨾ rfi)).
    { rewrite (wf_rfiD WF) at 1; unfold erln, rfisw; ie_unfolder; unfolder; ins; desf;
        rf_matcher; splits; eauto using si_refl; try type_solver.
      apply wf_rfE in H0; unfolder in H0; desf; eauto using si_refl.
    }
    ie_unfolder; unfold Execution.fr.
    rewrite no_co_to_init, wf_coD at 1; ins.
    rewrite wf_rfD at 1; ins.
    unfold erln; unfolder; ins; desf; rf_matcher.
    destruct (classic (is_init x)); [left | right]; ins.
    assert (is_w lab x) by (apply wf_siD in H; ins; type_solver).
    eexists; splits; eauto 6; intro POzy.
    forward eapply po_semi_total_l with (y := y) (z := z0) as [[]|N]; desc; eauto.
      by apply si_init in H; unfolder in H; desf.
    desf.
      eapply (SC_PER_LOC y); exists z0; split; ins; apply fr_in_eco; eexists; eauto.
    apply wf_rfl in H8; ins; apply wf_col in H4; ins.
    forward apply (proj1 (wf_sil WF) y z0); unfolder; splits; ins; desf;
        try congruence; type_solver.
  }
  assert (RL: rfi ⨾ erln ⨾ lob ∩ gc_req ⊆ erln ⨾ lob ∩ gc_req). {
    arewrite (rfi ⨾ erln ⊆ (erln ⨾ rfi)).
    { rewrite (wf_rfiD WF) at 1; unfold erln, rfisw; ie_unfolder; unfolder; ins; desf;
        rf_matcher; splits; try type_solver.
      apply wf_rfD in H7; unfolder in H7;
        desf; eauto 10 using si_refl.
      apply wf_rfE in H0; unfolder in H0; desf;
        apply wf_rfD in H1; unfolder in H1;
        desf; eauto 10 using si_refl.
    }
    unfold gc_req at 1, Execution.rfe; rewrite (wf_rfiD WF) at 1.
    unfold Execution.rfi; unfolder; ins; desf; rf_matcher; try type_solver.
    eexists; splits; eauto; unfold gc_req; unfolder; eauto.
  }
  rewrite !unionA, unionC.
  apply acyclic_absorb.
  { left; rewrite !seq_union_r, ?seqA.
    arewrite !(erln ⨾ erln ⊆ erln).
    sin_rewrite RO; sin_rewrite RL; rewrite ?seq_union_l.
    rewrite erln_in_si at 1; rewrite si_init at 1 2.
    unionL; auto with hahn; try basic_solver.
    unfold Execution.rfi; rewrite (no_rf_to_init WF); basic_solver.
    seq_rewrite erln_scaob; ins.
    by unfold scaob; ie_unfolder; unfolder; ins; desf; rf_matcher.
    unfold obs; basic_solver 15.
    basic_solver 10. }
  split.
  2: { rewrite wf_rfiD, erln_in_si; ins; apply acyclic_disj.
       split; unfolder; ins; desf.
       apply wf_siD in H2; type_solver. }
  apply acyclic_absorb.
  { left; unfold scaob; rewrite no_obs_to_init, erln_in_si, si_init; ins.
    rewrite lob_in_po, no_po_to_init; ins; unfolder; ins; desf. }
  split; [ apply acyclic_disj; split; basic_solver | ].
  rewrite scaob_erln, <- erln_scaob; ins.
  rewrite <- ?seq_union_r, acyclic_seqC, ?seq_union_l, ?seqA.
  arewrite (erln ⨾ erln ⊆ erln); rewrite scaob_erln; ins.
  rewrite erln_in_si at 1; rewrite si_si.
  arewrite (lob ∩ gc_req ⊆ lob).
  rewrite lob_erln; ins.
  eapply inclusion_acyclic, acyclic_pre_helper; ins.
  unionL; eauto with hahn.
Qed.

Lemma erln_refl3 WF x y :
  (im0 ∪ rf ∪ co ∪ fr ∪ obs⨾ si ∪ lob ∩ gc_req ∪ scaob) x y \/
  (im0 ∪ rf ∪ co ∪ fr ∪ obs⨾ si ∪ lob ∩ gc_req ∪ scaob) y x -> 
  erln x x.
Proof using.
  unfold im0, scaob; unfolder; ins; desf; eauto.
  all: try first [ apply (wf_rfE WF) in H
                 | apply (wf_coE WF) in H
                 | apply (wf_frE WF) in H
                 | apply (lob_in_po WF) in H; apply wf_poE in H
                 | apply (wf_siE WF) in H1
                 | apply (wf_obsE WF) in H ]; unfolder in *; desf; eauto.
  all: match goal with H: si _ _ |- _ => apply (wf_siE WF) in H end;
    unfolder in *; desf; eauto.
Qed.

Local Hint Resolve erln_refl3 : core.

Lemma acyclic_pre_egc
      WF SC_PER_LOC COMP (ACYC : acyclic (obs ⨾ si ∪ lob)) :
  acyclic (lift erln (im0 ∪ rf ∪ co ∪ fr ∪ obs ⨾ si ∪ lob ∩ gc_req ∪ scaob)).
Proof using.
  apply acyclic_lift; eauto.
  eapply inclusion_acyclic, acyclic_pre_gcb1; ins.
  apply seq_mori; ins.
  arewrite (im0 ⊆ is_init × set_compl is_init) by unfold im0; basic_solver.
  rewrite rfi_union_rfe, coi_union_coe, fri_union_fre.
  rewrite coi_lws, fri_lws; ins.
  arewrite (⦗W⦘ ⨾ lws ⊆ lob ∩ gc_req).
  { unfold lob, gc_req; rewrite <- ct_step; unfolder; ins; desf.
    split; eauto.
    do 3 left; eexists; split; eauto; apply si_refl.
    apply lws_in_po, wf_poE in H0; unfolder in H0; desf. }
  arewrite (⦗R⦘ ⨾ lws ⊆ lob ∩ gc_req).
  { unfold lob, gc_req; rewrite <- ct_step; unfolder; ins; desf.
    assert (E x /\ E y) by (apply lws_in_po, wf_poE in H0; unfolder in H0; desf).
    desc; splits; eauto 8 using si_refl.
    forward apply COMP with (x := x) as [w RF]; ins.
    destruct (classic (po w x)); ie_unfolder; unfolder; eauto 8.
    right; eexists; split; eauto; apply ct_step; unfold lws in *; unfolder in *.
    eapply wf_rfD in RF; unfolder in RF; desc; ins.
    do 3 left; exists y; splits; eauto using si_refl; try eapply po_trans; eauto.
    eapply wf_rfl in RF0; ins; congruence.
  }
  assert (OBS: obs ⊆ erln ⨾ obs).
  { unfolder; ins; apply wf_obsE in H; ins; unfolder in H; desc.
    eexists; rewrite erln_refl2; eauto. }
  rewrite <- ?seqA, <- OBS; clear OBS.
  arewrite (rfe ⊆ obs).
  arewrite (fre ⊆ obs).
  arewrite (coe ⊆ obs).
  assert (OBS: obs ⊆ obs ⨾ si).
  { unfolder; ins; apply wf_obsE in H; ins; unfolder in H; desc; eauto using si_refl. }
  assert (LOB: lob ∩ gc_req ⊆ erln ⨾ lob ∩ gc_req).
  { unfolder; ins; desf; assert (E x); eauto.
    apply lob_in_po, wf_poE in H; ins; unfolder in H; desf. }
  rewrite OBS at 1 2 3; unionL; eauto with hahn.
Qed.

Lemma partial_order_pre_egc
      WF SC_PER_LOC COMP (ACYC : acyclic (obs ⨾ si ∪ lob)) :
  strict_partial_order (lift erln (im0 ∪ rf ∪ co ∪ fr ∪ obs ⨾ si ∪ lob ∩ gc_req
                                   ∪ scaob))⁺.
Proof using.
  split; ins; apply acyclic_pre_egc; ins.
Qed.


Lemma ArmConsistent_implies_GlobExtComp (C : ArmConsistent) : ArmConsistentGlobExtComp.
Proof using.
  unfold ArmConsistent, ArmConsistentGlobExtComp,
     ArmCommon, linearization_of in *; desf; unnw.
  splits; ins; assert (SC_PER_LOC := InternalConsistent_sc_per_loc WF INTERNAL).
  forward eapply partial_order_included_in_total_order as (gcb & INCL & (IRR & TRANS) & TOT).
    by apply partial_order_pre_egc; ins.
  exists (restr_rel (classes erln) gcb).
  unfold rf_gcb; rewrite delift_restr_classes.
  assert (CO_IN: co ⊆ delift erln gcb).
  { rewrite <- INCL, <- ct_step, delift_lift; eauto with hahn.
    rewrite wf_coE at 1; unfolder; ins; desf; eauto 15. }
  assert (CO_EQ: co ≡ (W × W) ∩ delift erln gcb ∩ same_loc).
  {
    split.
      arewrite (co ⊆ co ∩ delift erln gcb).
      rewrite wf_coE, wf_coD, wf_col; ins; unfolder; ins; desf.
    unfolder; ins; desf; splits; ins.
    assert (NEQ: x <> y) by (intro; desf; eapply IRR; eauto).
    rewrite erln_refl2 in *; ins.
    eapply (wf_co_total WF) in NEQ; unfolder; desf; ins.
    exfalso; eapply CO_IN in NEQ; red in NEQ; desf; eauto.
  }
  splits; ins.
  { rewrite <- INCL.
    unfolder; splits; ins; desf; eauto.
    all: apply ct_step; eauto 15. }
  { repeat split; unfold restr_rel in *; try red; ins; desf; eauto.
    eapply TOT in NEQ; desf; eauto. }
  { unfold restr_rel; red; ins; desf. }
  split.
  { rewrite (wf_rfE WF), (wf_rfD WF); unfolder; ins; desf.
    splits; auto; try apply wf_rfl; ins.
    { apply INCL, ct_lift; eauto.
      unfolder; eauto 30 using erln_refl, t_step. }
    intro M; desf.
    rewrite !erln_refl2 in *; ins.
    assert (N: z <> x) by (intro; desf; eauto).
    eapply (wf_co_total WF) in N; unfolder; splits; ins.
    2: apply (wf_rfl WF) in H0; congruence.
    desf; [ by apply CO_IN in N; unfolder in N; desf; eauto | ].
    assert (FF: fr y z) by vauto.
    eapply (IRR (erln z)), TRANS with (erln y), INCL, ct_step; unfolder; eauto 15. }
  unfolder; ins; desf.
  rewrite !erln_refl2 in *; ins.
  forward eapply (COMP y) as [z RF]; ins.
  apply (wf_rfE WF) in RF; unfolder in RF; desf.
  apply (wf_rfD WF) in RF0; unfolder in RF0; desf.
  destruct (classic (z = x)) as [|N]; desf; exfalso.
  eapply (wf_co_total WF) in N; ins; unfolder; splits; ins.
  2: apply wf_rfl in RF2; ins; congruence.
  desf.
    eapply IRR, TRANS, INCL, ct_step; unfold Execution.fr; unfolder; eauto 15.
  eapply H0; exists z; splits; eauto.
  all: try (apply INCL, ct_lift; eauto; unfolder; eauto 15 using t_step).
  apply wf_rfl in RF2; ins; congruence.
Qed.


Lemma scaob_aob WF : scaob ⨾ aob ⊆ lob ∩ gc_req.
Proof using.
  unfold aob, gc_req; rewrite ?seq_union_r.
  arewrite (scaob ⊆ ⦗ codom_rel rfe ⦘ ⨾ si) at 1.
    by unfold scaob; unfolder; ins; desf; eauto.
  rewrite si_rmw, rmw_in_lws; ins.
  unionL; eauto with hahn.
    unfolder; ins; desf; splits; try apply t_step; unfolder; eauto 8.
  unfold scaob.
  rewrite ?seqA, wf_rfiD, W_ex_in_W; ins.
  unfolder; ins; desf; type_solver.
Qed.

Lemma si_dob WF : si ⨾ dob ⊆ dob.
Proof using.
  unfold dob, scaob; rewrite ?seq_union_l, ?seq_union_r, ?seqA; ins.
  seq_rewrite !si_data; ins.
  seq_rewrite !si_ctrl; ins.
  seq_rewrite !si_addr; ins.
Qed.

Lemma si_bob WF : si ⨾ bob ⊆ bob.
Proof using.
  unfold bob, scaob; rewrite id_union, ?seq_union_l, ?seq_union_r, ?seqA; ins.
  seq_rewrite <- L_si; ins.
  seq_rewrite <- A_si; ins.
  seq_rewrite <- Q_si; ins.
  seq_rewrite <- W_si; ins.
  seq_rewrite <- R_si; ins.
  rewrite ?seqA; seq_rewrite !si_po; ins.
Qed.

Lemma scaob_lob' WF : scaob ⨾ (lob \ gc_req) ⊆ lob ∩ gc_req.
Proof using.
  transitivity ( ⦗ codom_rel rfe ⦘ ⨾ lob ).
  2: by unfold gc_req; basic_solver 10.
  arewrite (scaob ⊆ ⦗ codom_rel rfe ⦘ ⨾ si ⨾ ⦗ codom_rel rfi ⦘)
    by unfold scaob; basic_solver.
  apply seq_mori; ins.
  unfold lob at 1; rewrite ct_begin at 1.
  arewrite (clos_refl_trans (lws⨾ si ∪ dob ∪ aob ∪ bob) ⊆ lob^?) by unfold lob; rels.
  rewrite ?seq_union_l, ?minus_union_l, ?seq_union_r, ?seqA.
  unionL.
  {
    unfold lws, gc_req; rewrite wf_rfiD; ins.
    unfolder; ins; desf; [ | type_solver |  | type_solver ].
    all: destruct H2; ins; eauto.
    all: right; eexists x0; splits; eauto.
    2: eapply t_trans; eauto.
    all: apply t_step; do 3 left; eexists; split; eauto.
    all: ie_unfolder; unfold lws; unfolder in *; desf; splits; eauto using (@po_trans G).
    all: eapply wf_rfl in H10; ins; congruence.
  }
  { rewrite inclusion_seq_eqv_l, inclusion_minus_rel; sin_rewrite si_dob; ins.
    arewrite (dob ⊆ lob); unfold lob; rels. }
  {
    unfold aob, gc_req; rewrite inclusion_minus_rel, ?seq_union_l, ?seq_union_r.
    rewrite inclusion_seq_eqv_l at 1.
    seq_rewrite si_rmw; ins; rewrite rmw_in_lws; ins.
    arewrite (lws ⨾ si ⊆ lob).
    unionL; [ unfold lob; rels | ].
    rewrite wf_rfiD, W_ex_in_W; ins.
    unfolder; ins; desf; type_solver. }
  { rewrite inclusion_seq_eqv_l, inclusion_minus_rel; sin_rewrite si_bob; ins.
    arewrite (bob ⊆ lob); unfold lob; rels. }
Qed.


Lemma scaob_lob WF : scaob ⨾ lob ⊆ scaob^? ⨾ (lob ∩ gc_req).
Proof using.
  arewrite (lob ⊆ (lob ∩ gc_req ∪ lob \ gc_req)).
    unfolder; ins; tauto.
  rewrite seq_union_r, scaob_lob'; ins.
  basic_solver 8.
Qed.

Lemma ArmConsistentGlobExtComp_equiv :
  ArmConsistent <-> ArmConsistentGlobExtComp.
Proof using.
  split; auto using ArmConsistent_implies_GlobExtComp.
  unfold ArmConsistent, ArmConsistentGlobExtComp, ArmCommon, linearization_of in *.
  ins; desf; unnw.
  destruct STO as [[cbIRR cbTRAN] Tcb].
  splits; ins.
  assert (OBS: obs ⊆ delift erln gcb).
  {
    unfold obs, Execution.rfe, Execution.coe, Execution.fre, Execution.fr.
    rewrite RF, CO; unfold rf_gcb; unfolder; ins; desf.
    forward eapply Tcb with (a := erln x) (b := erln y) as []; vauto.
      intro M; rewrite M in *.
      apply erln_in_si, wf_siD in H11; type_solver.
    edestruct H7; exists y; splits; eauto; congruence. }
  assert (OBS': obs ⨾ si ⊆ delift erln gcb).
  {
    rewrite obs_si_scaob, OBS; ins; unionL.
      unfolder; ins; desf; splits; eauto.
      rewrite (erln_rewrite WF H0) in *; ins.
      eapply erln_trans, erln_sym; eauto.
    ie_unfolder; rewrite RF; unfold rf_gcb; unfolder; ins; desf.
    splits; eauto.
    eapply cbTRAN, INCL; unfolder; eauto 10.
    unfold scaob in H0; unfolder in H0; desc.
    apply wf_siE in H0; ins; unfolder in H0; desc; auto. }
  rewrite acyclic_ut; splits; vauto.
  { rewrite OBS'; intros x M.
    eapply (cbIRR (erln x)).
    revert M; unfolder; generalize x at 2 4; ins; induction M; desf; eauto. }
  { rewrite lob_in_po; eauto using po_irr. }
  rewrite acyclic_seqC, ct_end, seqA.
  arewrite ((obs ⨾ si) ⨾ lob ⊆ obs ⨾ si ⨾ lob ∩ gc_req).
  {
    rewrite obs_si_scaob, ?seq_union_l, ?seqA; ins.
    rewrite scaob_lob; ins.
    unionL.
    {
      unfold obs, gc_req, erln, rfisw.
      rewrite (wf_rfeD WF) at 1.
      rewrite (wf_coeD WF) at 1.
      rewrite (wf_freD WF) at 1; unfolder; ins; desf.
      all: do 2 (eexists; splits; eauto).
      all: try type_solver.
      solve [ exfalso; destruct H7, H2; rf_matcher ].
      all: apply lob_in_po, wf_poE in H1; unfolder in H1;
        ins; desf; auto using si_refl.
    }
    rewrite wf_rfeE, inclusion_seq_eqv_l, seqA, <- seqA with (r1 := ⦗E⦘); ins.
    apply seq_mori, seq_mori; unfold obs, scaob; unfolder; ins; desf;
      eauto using si_refl.
  }
  rewrite <- seqA with (r3 := lob ∩ gc_req); rels.
  rewrite OBS'; intros x M.
  eapply (cbIRR (erln x)).
  revert M; unfolder; generalize x at 2 4; ins; induction M; desf; eauto.
  eapply cbTRAN with (erln z), INCL; unfolder; eauto 10.
  clear H0 H1; induction H; desf; eauto.
Qed.


End Arm.
