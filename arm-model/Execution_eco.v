(******************************************************************************)
(** * Sc-per-loc   *)
(******************************************************************************)

Require Import Classical Peano_dec.
Require Import Hahn.

Require Import Events.
Require Import Execution.

Set Implicit Arguments.


Section ECO.
Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'po'" := (po G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).

Notation "'fr'" := (fr G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'fre'" := (fre G).
Notation "'fri'" := (fri G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.

(******************************************************************************)
(** ** extended coherence order  *)
(******************************************************************************)

Definition eco := rf ∪ co ⨾ rf^? ∪ fr ⨾ rf^?.

Definition sc_per_loc := irreflexive (po ⨾ eco).

Implicit Type SC_PER_LOC : sc_per_loc.

(******************************************************************************)
(** ** Basic Properties  *)
(******************************************************************************)

Lemma co_in_eco: co ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma rf_in_eco: rf ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma fr_in_eco: fr ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma co_rf_in_eco: co ⨾ rf ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma fr_rf_in_eco: fr ⨾ rf ⊆ eco.
Proof using. unfold eco; basic_solver 6. Qed.

Lemma rfe_in_eco : rfe ⊆ eco.
Proof using. rewrite rfe_in_rf. apply rf_in_eco. Qed.

Lemma coe_in_eco : coe ⊆ eco.
Proof using. rewrite coe_in_co. apply co_in_eco. Qed.

Lemma fre_in_eco : fre ⊆ eco.
Proof using. rewrite fre_in_fr. apply fr_in_eco. Qed.

Lemma loceq_eco WF : funeq loc eco.
Proof using. destruct WF; desf. eauto 10 with hahn. Qed.

Lemma wf_ecoE WF : eco ≡ ⦗E⦘ ⨾ eco ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; unfold eco.
  rewrite wf_rfE, wf_coE, wf_frE; basic_solver.
Qed.

Lemma wf_ecoD WF : eco ≡ ⦗RW⦘ ⨾ eco ⨾ ⦗RW⦘.
Proof using.
  apply doms_helper; unfold eco.
  rewrite wf_rfD, wf_coD, wf_frD; basic_solver.
Qed.

Lemma eco_alt WF: eco ≡ (co ∪ fr) ∪ (co ∪ fr)^? ⨾ rf.
Proof using.
  unfold eco, Execution.fr; basic_solver 42.
Qed.

Lemma eco_alt2 WF: eco ≡ rf ∪ (rf⁻¹)^? ⨾ co ⨾ rf^?.
Proof using.
  unfold eco, Execution.fr; basic_solver 42.
Qed.

Lemma eco_trans WF: transitive eco.
Proof using.
unfold eco.
apply transitiveI.
generalize (rf_rf WF) (rf_fr WF) (co_co WF) (rf_co WF) (co_fr WF) (fr_fr WF) (fr_co WF).
unfolder; ins; desf; try basic_solver 1.
all: try (exfalso; basic_solver).
all: basic_solver 42.
Qed.

Lemma eco_irr WF: irreflexive eco.
Proof using.
unfold eco.
generalize (co_irr WF) (rf_irr WF) (fr_irr WF).
generalize (rf_fr WF) (rf_co WF).
basic_solver 5.
Qed.

Lemma eco_alt3 WF: eco ≡ (rf ∪ co ∪ fr)^+.
Proof using.
split; eauto 8 using rf_in_eco, co_in_eco, fr_in_eco, eco_trans with hahn.
unfold eco; rewrite !crE; relsf.
unionL; eauto 6 using inclusion_step2_ct with hahn.
Qed.

Lemma eco_f WF : eco ⨾ ⦗F⦘ ⊆ ∅₂.
Proof using.
rewrite (wf_ecoD WF); type_solver.
Qed.

Lemma eco_almost_total WF COMP x y
  (ACTx: E x) (ACTy: E y)
  (RWx: RW x) (RWy: RW y) (LOC: loc x = loc y)
  (NEQ: x <> y):
  eco x y \/ eco y x \/ exists z, rf z x /\ rf z y.
Proof using.
generalize (dom_to_doma (wf_rfE WF)); intro rfE1; unfolder in rfE1.
generalize (dom_to_domb (wf_rfE WF)); intro rfE2; unfolder in rfE2.
generalize (dom_to_doma (wf_rfD WF)); intro rfD1; unfolder in rfD1.
generalize (dom_to_domb (wf_rfD WF)); intro rfD2; unfolder in rfD2.
generalize (loceq_rf WF); intro rfL; unfolder in rfL.
assert (exists l, loc x = l).
by destruct x; eauto.
unfolder in RWx.
unfolder in RWy.
ins; desf.
- assert (exists wx, rf wx x) by (apply COMP; basic_solver).
  assert (exists wy, rf wy y) by (apply COMP; basic_solver).
  desf.
  destruct (classic (wx=wy)); try subst; eauto.
  assert (co wx wy \/ co wy wx); cycle 1.
  by unfold eco, Execution.fr; basic_solver 42.
  eapply WF; unfolder; splits; eauto.
  by apply (loceq_rf WF) in H; apply (loceq_rf WF) in H0; congruence.
- assert (exists wy, rf wy y) by (apply COMP; basic_solver).
  desf.
  destruct (classic (wy=x)); [subst; unfold eco; basic_solver 5|].
  assert (co wy x \/ co x wy); cycle 1.
  by unfold eco, Execution.fr; basic_solver 42.
  eapply WF; unfolder; splits; eauto.
  by apply (loceq_rf WF) in H; congruence.
- assert (exists wx, rf wx x).
  by apply COMP; basic_solver.
  desf.
  destruct (classic (wx=y)); [subst; unfold eco; basic_solver 5|].
  assert (co wx y \/ co y wx); cycle 1.
  by unfold eco, Execution.fr; basic_solver 42.
  eapply WF; unfolder; splits; eauto.
  by apply (loceq_rf WF) in H; congruence.
- assert (co x y \/ co y x); [eapply WF|unfold eco]; basic_solver 10.
Qed.

Lemma transp_rf_rf_eco_in_eco WF : rf⁻¹ ⨾ rf ⨾ eco ⊆ eco.
Proof using.
unfold eco, Execution.fr; relsf.
rewrite rf_rf; auto.
seq_rewrite rf_co; auto.
rewrite !seqA.
sin_rewrite rf_transp_rf; basic_solver 10.
Qed.

Lemma eco_transp_rf_rf_in_eco WF : eco ⨾ rf⁻¹ ⨾ rf ⊆ eco.
Proof using.
unfold eco, Execution.fr; relsf.
rewrite !seqA, !crE; relsf.
arewrite_false (co ⨾ rf⁻¹).
by rewrite (wf_coD WF), (wf_rfD WF); type_solver.
sin_rewrite !rf_transp_rf; auto.
basic_solver 8.
Qed.

(******************************************************************************)
(** ** implications of SC_PER_LOC  *)
(******************************************************************************)

Lemma no_co_to_init WF SC_PER_LOC : co ⊆ co ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
rewrite wf_coE at 1; try done.
unfolder; ins; splits; auto; desf; intro.
eapply SC_PER_LOC; exists x; splits; [|eby apply co_in_eco].
unfold Execution.po; unfolder; splits; try done.
cut (~ is_init x).
by destruct x, y; ins.
intro.
assert (x=y).
eby apply (loceq_co WF) in H0; eapply init_same_loc.
eby subst; eapply (co_irr WF).
Qed.

Lemma no_fr_to_init WF SC_PER_LOC : fr ⊆ fr ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
unfold Execution.fr.
rewrite no_co_to_init at 1; try done.
basic_solver.
Qed.

Lemma co_from_init WF SC_PER_LOC :
  ⦗fun x => is_init x⦘ ⨾ (same_loc \ (fun x y => x = y)) ⨾ ⦗E ∩₁ W⦘ ⊆ co.
Proof using.
unfolder; ins; desf.
forward eapply init_w with (x := x) as Wx; eauto.
generalize (is_w_loc lab x Wx).
unfold Events.same_loc in *; ins; desf.
eapply tot_ex.
- eapply WF.
- basic_solver.
- unfolder; splits; try edone.
  destruct x; [|unfold is_init in *; desf].
  eapply (wf_init WF); exists y; splits; eauto.
  unfold Events.loc in *.
  rewrite (wf_init_lab WF) in *.
  congruence.
- intro A.
  hahn_rewrite (no_co_to_init WF SC_PER_LOC) in A.
  unfolder in *; desf.
- intro; eauto.
Qed.

Lemma BasicRMW WF SC_PER_LOC: irreflexive (co^? ⨾ rf ⨾ rmw).
Proof using.
rewrite rmw_in_po; try done.
unfold sc_per_loc, eco in *; unfolder in *; basic_solver 10.
Qed.

Lemma w_r_loc_w_in_co WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘) (IRR: irreflexive r)
  (A: irreflexive (r ⨾ eco)):
  ⦗W⦘ ⨾ r ∩ same_loc ⨾ ⦗W⦘ ⊆ co.
Proof using.
rewrite rE.
unfolder; ins; desf.
eapply tot_ex.
- eapply WF.
- unfolder; splits; try edone.
- unfolder; splits; try edone.
- intro; eapply A; unfold eco; basic_solver 12.
- intro; subst; eapply IRR; eauto.
Qed.

Lemma w_r_loc_r_in_co_rf WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘)
  (A: irreflexive (r ⨾ eco)) COMP :
  ⦗W⦘ ⨾ r ∩ same_loc ⨾ ⦗R⦘ ⊆ co^? ⨾ rf.
Proof using.
rewrite rE.
cut (⦗W⦘ ⨾  ⦗E⦘ ⨾ r ∩ same_loc ⨾ ⦗E ∩₁ R⦘ ⊆ co^? ⨾ rf).
by basic_solver 12.
red in COMP; rewrite COMP.
rewrite (dom_l (wf_rfD WF)) at 1.
rewrite (dom_l (wf_rfE WF)) at 1.
rewrite (loceq_same_loc (loceq_rf WF)) at 1.
unfolder; ins; desf; eexists; splits; [|edone].
destruct (classic (x=z)); [eauto|].
right; eapply tot_ex.
- eapply WF.
- splits; try edone.
- splits; try edone.
- intro; eapply A.
unfold eco, Execution.fr; basic_solver 22.
- congruence.
Qed.

Lemma r_r_loc_w_in_fr WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘)
  (A: irreflexive (r ⨾ eco)) COMP :
  ⦗R⦘ ⨾ r ∩ same_loc ⨾ ⦗W⦘ ⊆ fr.
Proof using.
rewrite rE.
cut (⦗E ∩₁ R⦘ ⨾ r ∩ same_loc ⨾ ⦗E ∩₁ W⦘ ⊆ fr).
by basic_solver 12.
red in COMP; rewrite COMP.
rewrite (dom_l (wf_rfD WF)) at 1.
rewrite (dom_l (wf_rfE WF)) at 1.
rewrite (loceq_same_loc (loceq_rf WF)) at 1.
unfolder; ins; desf; eexists; splits; [edone|].
eapply tot_ex.
- eapply WF.
- splits; try edone.
- unfolder; splits; [done | done | unfolder in *; congruence].
- intro; eapply A.
unfold eco; basic_solver 22.
- intro; subst.
eapply A.
unfold eco; basic_solver 22.
Qed.

Lemma r_r_loc_r_in_fr_rf WF r
  (rE: r ≡ ⦗E⦘ ⨾ r ⨾  ⦗E⦘)
  (A: irreflexive (r ⨾ eco)) COMP :
  ⦗R⦘ ⨾ r ∩ same_loc ⨾ ⦗R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf.
Proof using.
rewrite rE.
cut (⦗E ∩₁ R⦘ ⨾ r ∩ same_loc ⨾ ⦗E ∩₁ R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf).
by basic_solver 12.
red in COMP; rewrite COMP.
rewrite (dom_l (wf_rfD WF)) at 1 2.
rewrite (dom_l (wf_rfE WF)) at 1 2.
rewrite (loceq_same_loc (loceq_rf WF)) at 1 2.
unfolder; ins; desf.
destruct (classic (z0=z)).
by right; eexists; subst; eauto.
left.
unfold Execution.fr; unfolder.
eexists; splits; [|edone].
eexists; splits; [edone|].
eapply tot_ex.
- eapply WF.
- splits; try edone.
- unfolder; splits; [done | done | unfolder in *; congruence].
- intro; eapply A.
unfold eco, Execution.fr; basic_solver 22.
- intro; subst; eauto.
Qed.

Lemma w_po_loc_w_in_coi WF SC_PER_LOC:
  ⦗W⦘ ⨾ po ∩ same_loc ⨾ ⦗W⦘ ⊆ coi.
Proof using.
arewrite (⦗W⦘ ⨾ po ∩ same_loc ⨾ ⦗W⦘ ⊆ (⦗W⦘ ⨾ po ∩ same_loc ⨾ ⦗W⦘) ∩ po).
basic_solver.
rewrite (w_r_loc_w_in_co WF (@wf_poE G) (@po_irr G) SC_PER_LOC).
by ie_unfolder.
Qed.

Lemma w_po_loc_r_in_co_rf WF SC_PER_LOC COMP:
  ⦗W⦘ ⨾ po ∩ same_loc ⨾ ⦗R⦘ ⊆ co^? ⨾ rf.
Proof using.
apply (w_r_loc_r_in_co_rf WF (@wf_poE G) SC_PER_LOC COMP).
Qed.

Lemma r_po_loc_w_in_fri WF SC_PER_LOC COMP:
  ⦗R⦘ ⨾ po ∩ same_loc ⨾ ⦗W⦘ ⊆ fri.
Proof using.
arewrite (⦗R⦘ ⨾ po ∩ same_loc ⨾ ⦗W⦘ ⊆ (⦗R⦘ ⨾ po ∩ same_loc ⨾ ⦗W⦘) ∩ po).
basic_solver.
rewrite (r_r_loc_w_in_fr WF (@wf_poE G) SC_PER_LOC COMP).
by ie_unfolder.
Qed.

Lemma r_po_loc_r_in_fr_rf WF SC_PER_LOC COMP:
  ⦗R⦘ ⨾ po ∩ same_loc ⨾ ⦗R⦘ ⊆ fr ⨾ rf ∪ rf^{-1} ⨾ rf.
Proof using.
apply (r_r_loc_r_in_fr_rf WF (@wf_poE G) SC_PER_LOC COMP).
Qed.

Lemma rmw_in_fri WF SC_PER_LOC COMP : rmw ⊆ fri.
Proof using.
rewrite (wf_rmwD WF), (rmw_in_po_loc WF).
rewrite (r_po_loc_w_in_fri WF SC_PER_LOC COMP).
ie_unfolder; basic_solver.
Qed.

Lemma rmw_in_fr WF SC_PER_LOC COMP : rmw ⊆ fr.
Proof using.
  rewrite rmw_in_fri; auto. apply fri_in_fr.
Qed.

Lemma rf_rmw_in_co_helper WF SC_PER_LOC: rf ⨾ rmw ⊆ co ∪ co^{-1}.
Proof using.
rewrite (dom_l (wf_rfE WF)).
rewrite (dom_r (wf_rmwE WF)).
rewrite (dom_l (wf_rfD WF)).
rewrite (dom_r (wf_rmwD WF)).
unfolder; ins; desf.
eapply (wf_co_total WF); [basic_solver| |].
{ unfolder; ins; desf; splits; eauto.
  apply (wf_rfl WF) in H0.
  apply (wf_rmwl WF) in H1.
  unfold Events.same_loc in *; congruence. }
intro; subst.
eapply SC_PER_LOC.
exists y; splits; eauto.
eapply (rmw_in_po WF); edone.
eapply rf_in_eco; edone.
Qed.

Lemma rf_rmw_in_co WF SC_PER_LOC : rf ⨾ rmw ⊆ co.
Proof using.
arewrite (rf ⨾ rmw ⊆ (rf ⨾ rmw) ∩ (rf ⨾ rmw)).
rewrite rf_rmw_in_co_helper at 1; eauto.
rewrite inter_union_l; unionL; [basic_solver|].
transitivity (fun _ _ : actid => False); [|basic_solver].
unfolder; ins; desf.
eapply SC_PER_LOC.
exists y; splits; eauto.
eapply (rmw_in_po WF); edone.
eapply co_rf_in_eco; basic_solver.
Qed.

Lemma rf_rmw_ct_in_co WF SC_PER_LOC : (rf ⨾ rmw)^+ ⊆ co.
Proof using. by rewrite rf_rmw_in_co, (ct_of_trans (co_trans WF)). Qed.

Lemma rf_rmw_rt_in_co WF SC_PER_LOC : (rf ⨾ rmw)^* ⊆ co^?.
Proof using. by rewrite rf_rmw_in_co, (rt_of_trans (co_trans WF)). Qed.

End ECO.
