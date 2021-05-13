(******************************************************************************)
(** * Definition of executions (common basis for all types of executions) *)
(******************************************************************************)

Require Import Arith Lia.
Require Import Classical Peano_dec.
(*From hahn*) Require Import Hahn.
Require Import Events.

Set Implicit Arguments.

(** Definition of an execution *)
Record execution :=
  { acts : list actid;
    lab : actid -> label;
    iico_data : actid -> actid -> Prop ;   (** intrinsic data dependency *)
    iico_ctrl : actid -> actid -> Prop ;   (** intrinsic control dependency *)

    data : actid -> actid -> Prop ;   (** data dependency *)
    addr : actid -> actid -> Prop ;   (** address dependency *)
    ctrl : actid -> actid -> Prop ;   (** control dependency *)
    lxsx : actid -> actid -> Prop ;   (** load-exclusive -> store-exclusive *)
    amo : actid -> actid -> Prop ;    (** read -> write of atomic operation *)

    (* Representation of a data dependency to CAS.
        It goes from a read to an exclusive read.
        Consider the example:

        a := read (x);
        CAS(y, a, 1);

        In the execution, there is an rmw_dep edge between a read event representing `a := ⦗x⦘'
        and a read event representing `CAS(y, a, 1)'.
     *)
    (* rmw_dep : actid -> actid -> Prop ; *)

    rf : actid -> actid -> Prop ;
    co : actid -> actid -> Prop ;
  }.

Section Execution.

Variable G : execution.

Definition acts_set := fun x => In x (acts G).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'E'" := acts_set.
Notation "'lab'" := (lab G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'lxsx'" := (lxsx G).
Notation "'amo'" := (amo G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Br'" := (fun a => is_true (is_br lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Definition po := ⦗E⦘ ⨾ ext_sb ⨾  ⦗E⦘.
Definition si := ⦗E⦘ ⨾ ext_si ⨾  ⦗E⦘.
Definition rmw := lxsx ∪ amo.


Record Wf :=
  { data_in_po : data ⊆ po ;
    wf_dataD : data ≡ ⦗R⦘ ⨾ data ⨾ ⦗W⦘ ;
    addr_in_po : addr ⊆ po ;
    wf_addrD : addr ≡ ⦗R⦘ ⨾ addr ⨾ ⦗RW⦘ ;
    ctrl_in_po : ctrl ⊆ po ;
    wf_ctrlD : ctrl ≡ ⦗R⦘ ⨾ ctrl ;
    ctrl_po : ctrl ⨾ po ⊆ ctrl ;
    wf_rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    wf_rmwl : rmw ⊆ same_loc ;
    wf_rmwi : rmw ⊆ immediate po ;

    wf_siD     : forall x y, si x y -> si_matching_label (lab x) (lab y) ;
    wf_sil     : si ∩ same_loc ≡ ⦗ E ⦘ ;
    wf_si_data : si ⨾ data ⨾ si ⊆ data ;
    wf_si_ctrl : si ⨾ ctrl ⨾ si ⊆ ctrl ;
    wf_si_addr : si ⨾ addr ⨾ si ⊆ addr ;
    si_lxsx    : si ⨾ lxsx ≡ lxsx ⨾ si ;
    si_amo     : si ⨾ amo ≡ amo ⨾ si ;

    wf_rfE : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ;
    wf_rfD : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ;
    wf_rfl : rf ⊆ same_loc ;
    wf_rfv : funeq val rf ;
    wf_rff : functional rf⁻¹ ;
    wf_coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    wf_coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    wf_col : co ⊆ same_loc ;
    co_trans : transitive co ;
    wf_co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co ;
    co_irr : irreflexive co ;
    wf_init : forall l, (exists b, E b /\ loc b = Some l) -> E (InitEvent l) ;
    wf_init_lab : forall l, lab (InitEvent l) = Astore false Opln_write l 0 ;
  }.

Implicit Type WF : Wf.

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* reads-before, aka from-read *)
Definition fr := rf⁻¹ ⨾ co.

Definition deps := data ∪ addr ∪ ctrl.

(******************************************************************************)
(** ** Consistency definitions  *)
(******************************************************************************)

Definition complete := E ∩₁ R  ⊆₁ codom_rel rf.
Definition rmw_atomicity := rmw ∩ ((fr \ po) ⨾ (co \ po)) ⊆ ∅₂.

(******************************************************************************)
(** ** Basic transitivity properties *)
(******************************************************************************)

Lemma po_trans : transitive po.
Proof using.
  unfold po; unfolder; ins; desf; splits; auto.
  eby eapply ext_sb_trans.
Qed.

Lemma po_po : po ⨾ po ⊆ po.
Proof using.
  generalize po_trans; basic_solver 21.
Qed.

Lemma po_same_loc_trans: transitive (po ∩ same_loc).
Proof using.
  apply transitiveI.
  unfold Events.same_loc.
  unfolder; ins; desf; eauto.
  splits.
  generalize po_trans; basic_solver 21.
  congruence.
Qed.

Lemma po_same_loc_W_trans : transitive (po ∩ same_loc ⨾ ⦗W⦘).
Proof using.
  generalize po_same_loc_trans; unfold transitive.
  basic_solver 21.
Qed.


(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma po_neq_loc_in_po : po \ same_loc ⊆ po.
Proof using. basic_solver. Qed.

Lemma fr_co WF : fr ⨾ co ⊆ fr.
Proof using. by unfold fr; rewrite seqA, rewrite_trans; [|apply WF]. Qed.

Lemma rmw_in_po WF: rmw ⊆ po.
Proof using. rewrite wf_rmwi; basic_solver. Qed.

Lemma deps_in_po WF: deps ⊆ po.
Proof using. unfold deps; unionL; apply WF. Qed.

Lemma amo_in_po WF: amo ⊆ po.
Proof using. eapply inclusion_trans, rmw_in_po; vauto. Qed.

Lemma lxsx_in_po WF: lxsx ⊆ po.
Proof using. eapply inclusion_trans, rmw_in_po; vauto. Qed.



(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Lemma loceq_rf WF : funeq loc rf.
Proof using. apply WF. Qed.

Lemma loceq_co WF : funeq loc co.
Proof using. apply WF. Qed.

Lemma loceq_rmw WF : funeq loc rmw.
Proof using. apply WF. Qed.

Lemma loceq_fr WF : funeq loc fr.
Proof using.
  generalize (loceq_co WF), (loceq_rf WF).
  unfold funeq, fr; unfolder; ins; desf.
  transitivity (loc z); eauto using sym_eq.
Qed.

Lemma wf_frl WF : fr ⊆ same_loc.
Proof using.
  unfold fr.
  rewrite (wf_rfl WF), (wf_col WF).
  unfold Events.same_loc.
  unfolder; ins; desc; congruence.
Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_poE : po ≡ ⦗E⦘ ⨾ po ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; unfold po; basic_solver.
Qed.

Lemma wf_dataE WF: data ≡ ⦗E⦘ ⨾ data ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite data_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_addrE WF: addr ≡ ⦗E⦘ ⨾ addr ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite addr_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_ctrlE WF: ctrl ≡ ⦗E⦘ ⨾ ctrl ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite ctrl_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_depsE WF: deps ≡ ⦗E⦘ ⨾ deps ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite deps_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_amoE WF: amo ≡ ⦗E⦘ ⨾ amo ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite amo_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_lxsxE WF: lxsx ≡ ⦗E⦘ ⨾ lxsx ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite lxsx_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_rmwE WF : rmw ≡ ⦗E⦘ ⨾ rmw ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; rewrite rmw_in_po, wf_poE; basic_solver.
Qed.

Lemma wf_frE WF : fr ≡ ⦗E⦘ ⨾ fr ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; unfold fr;
    rewrite wf_rfE, wf_coE; basic_solver.
Qed.

Lemma wf_siE WF: si ≡ ⦗E⦘ ⨾ si ⨾ ⦗E⦘.
Proof using.
  apply doms_helper; unfold si; basic_solver.
Qed.


(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_frD WF : fr ≡ ⦗R⦘ ⨾ fr ⨾ ⦗W⦘.
Proof using.
  apply doms_helper; unfold fr;
    rewrite wf_rfD, wf_coD; basic_solver.
Qed.

Lemma wf_depsD WF : deps ≡ ⦗R⦘ ⨾ deps.
Proof using.
  split; [|basic_solver].
  unfold deps.
  rewrite (wf_dataD WF) at 1.
  rewrite (wf_ctrlD WF) at 1.
  rewrite (wf_addrD WF) at 1.
  basic_solver.
Qed.

(******************************************************************************)
(** ** Irreflexive relations *)
(******************************************************************************)

Lemma po_irr : irreflexive po.
Proof using.
  unfold po; unfolder; ins; desf.
  eby eapply ext_sb_irr.
Qed.

Lemma fr_irr WF : irreflexive fr.
Proof using.
  rewrite (wf_frD WF); type_solver.
Qed.

(******************************************************************************)
(** ** Same instruction *)
(******************************************************************************)

Lemma si_po : si ⨾ po ≡ po.
Proof using.
  unfold si, po, ext_si, ext_sb; unfolder; splits; ins; desf; desf; splits; ins.
  exists (InitEvent l); ins.
  eexists (ThreadEvent _ _ _); splits; ins; eauto.
Qed.

Lemma po_si : po ⨾ si ≡ po.
Proof using.
  unfold si, po; unfolder; splits; ins; desf; splits; ins;
    try exists y; unfold ext_si, ext_sb in *; desf; desf.
Qed.

Lemma si_refl x (EV: E x) :  si x x.
Proof using.
  unfold si in *; unfolder; auto using ext_si_refl.
Qed.

Lemma si_sym :  symmetric si.
Proof using.
  unfold si in *; unfolder; ins; desf.
  eauto 8 using ext_si_symm.
Qed.

Lemma si_trans : transitive si.
Proof using.
  unfold si in *; unfolder; ins; desf; eauto using ext_si_trans.
Qed.

Lemma si_si : si ⨾ si ≡ si.
Proof using.
  unfold si; unfolder; split; ins; desf; splits; ins.
  eapply ext_si_trans; eauto.
  eauto 6 using ext_si_refl.
Qed.

Lemma si_rmw WF : si ⨾ rmw ≡ rmw ⨾ si.
Proof using.
  unfold rmw; relsf; rewrite si_amo, si_lxsx; ins.
Qed.

Lemma addr_si WF : addr ⨾ si ≡ addr.
Proof using.
  rewrite wf_addrE; ins.
  assert (X := wf_si_addr WF); unfolder in *; ins; splits; ins; desf; splits; ins;
    eauto 8 using si_refl.
  unfold si in *; unfolder in *; desf.
Qed.

Lemma ctrl_si WF : ctrl ⨾ si ≡ ctrl.
Proof using.
  rewrite wf_ctrlE; ins.
  assert (X := wf_si_ctrl WF); unfolder in *; ins; splits; ins; desf; splits; ins;
    eauto 8 using si_refl.
  unfold si in *; unfolder in *; desf.
Qed.

Lemma data_si WF : data ⨾ si ≡ data.
Proof using.
  rewrite wf_dataE; ins.
  assert (X := wf_si_data WF); unfolder in *; ins; splits; ins; desf; splits; ins;
    eauto 8 using si_refl.
  unfold si in *; unfolder in *; desf.
Qed.

Lemma si_addr WF : si ⨾ addr ≡ addr.
Proof using.
  rewrite wf_addrE; ins.
  assert (X := wf_si_addr WF); unfolder in *; ins; splits; ins; desf; splits; ins;
    eauto 8 using si_refl.
  unfold si in *; unfolder in *; desf.
Qed.

Lemma si_ctrl WF : si ⨾ ctrl ≡ ctrl.
Proof using.
  rewrite wf_ctrlE; ins.
  assert (X := wf_si_ctrl WF); unfolder in *; ins; splits; ins; desf; splits; ins;
    eauto 8 using si_refl.
  unfold Execution.si in *; unfolder in *; desf.
Qed.

Lemma si_data WF : si ⨾ data ≡ data.
Proof using.
  rewrite wf_dataE; ins.
  assert (X := wf_si_data WF); unfolder in *; ins; splits; ins; desf; splits; ins;
    eauto 8 using si_refl.
  unfold Execution.si in *; unfolder in *; desf.
Qed.

Lemma W_si WF : ⦗W⦘ ⨾ si ≡ si ⨾ ⦗W⦘.
Proof using.
  unfolder; ins; desf; splits; ins; desf; splits; eauto.
  eapply (wf_siD WF) in H0; unfolder in *; desf; type_solver.
  eapply (wf_siD WF) in H; unfolder in *; desf; type_solver.
Qed.

Lemma R_si WF : ⦗R⦘ ⨾ si ≡ si ⨾ ⦗R⦘.
Proof using.
  unfolder; ins; desf; splits; ins; desf; splits; eauto.
  eapply (wf_siD WF) in H0; unfolder in *; desf; type_solver.
  eapply (wf_siD WF) in H; unfolder in *; desf; type_solver.
Qed.

(******************************************************************************)
(** ** Acyclic relations *)
(******************************************************************************)

Lemma po_acyclic : acyclic po.
Proof using.
  apply trans_irr_acyclic; [apply po_irr| apply po_trans].
Qed.

Lemma co_acyclic WF: acyclic co.
Proof using.
    by apply trans_irr_acyclic; [apply co_irr| apply co_trans].
Qed.

Lemma wf_po : well_founded po.
Proof using.
  eapply wf_finite; auto.
  apply po_acyclic.
  rewrite (dom_l wf_poE).
  unfold doma; basic_solver.
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma init_w WF: is_init ⊆₁ W.
Proof using.
  unfolder; ins.
  unfold is_init in *; destruct x; desf.
  specialize (wf_init_lab WF l); unfold is_w; desf.
Qed.

Lemma read_or_fence_is_not_init WF a (A: R a \/ F a) : ~ is_init a.
Proof using.
  generalize ((init_w WF) a).
  type_solver.
Qed.

Lemma no_po_to_init : po ≡ po ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
  split; [|basic_solver].
  unfold po; rewrite ext_sb_to_non_init at 1; basic_solver.
Qed.

Lemma no_rf_to_init WF : rf ≡ rf ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
  split; [|basic_solver].
  rewrite (wf_rfD WF) at 1.
  generalize (read_or_fence_is_not_init WF).
  basic_solver 42.
Qed.

Lemma rmw_from_non_init WF : rmw ≡ ⦗fun x => ~ is_init x⦘ ⨾ rmw.
Proof using.
  split; [|basic_solver].
  rewrite (wf_rmwD WF).
  generalize (read_or_fence_is_not_init WF).
  basic_solver 42.
Qed.

Lemma rmw_non_init_lr WF : rmw ≡ ⦗set_compl is_init⦘ ⨾ rmw ⨾ ⦗set_compl is_init⦘.
Proof using.
  split; [|basic_solver].
  rewrite (rmw_from_non_init WF) at 1.
  rewrite <- seqA.
  apply codom_rel_helper.
  rewrite (rmw_in_po WF).
  rewrite no_po_to_init.
  basic_solver.
Qed.

Lemma init_same_loc WF a b (A: is_init a) (B: is_init b) (LOC: loc a = loc b):
  a = b.
Proof using.
destruct a, b; desf.
cut (l = l0); [by ins; subst|].
unfold Events.loc in LOC.
rewrite (wf_init_lab WF l), (wf_init_lab WF l0) in LOC; desf.
Qed.




(******************************************************************************)
(** ** More properties *)
(******************************************************************************)

Lemma po_semi_total_l x y z :
  po x y -> po x z -> is_init x /\ ~ is_init y /\ ~ is_init z \/ po y z \/ po z y \/ si y z.
Proof using.
  unfold Execution.po, Execution.si, ext_sb, ext_si; ins; unfolder in *; desf; desf;
    ins; eauto 6.
  right; forward eapply (Nat.lt_trichotomy index0 index1) as K; desf.
    + left; eexists; splits; eauto; eexists; splits; eauto; ins.
    + right; right; eexists; splits; eauto; eexists; splits; eauto; ins.
    + right; left; eexists; splits; eauto; eexists; splits; eauto; ins.
Qed.

Lemma po_semi_total_r x y z :
  po y x -> po z x -> po y z \/ po z y \/ is_init y /\ is_init z \/ si y z.
Proof using.
  unfold Execution.po, Execution.si, ext_sb, ext_si; ins; unfolder in *; desf; desf; eauto.
  - left; eexists; splits; eauto; eexists; splits; eauto; ins.
  - right; left; eexists; splits; eauto; eexists; splits; eauto; ins.
  - forward eapply (Nat.lt_trichotomy index index1) as K; desf.
    + left; eexists; splits; eauto; eexists; splits; eauto; ins.
    + right; right; right; eexists; splits; eauto; eexists; splits; eauto; ins.
    + right; left; eexists; splits; eauto; eexists; splits; eauto; ins.
Qed.

Lemma po_tid_init x y (PO : po x y): tid x = tid y \/ is_init x.
Proof using.
  generalize ext_sb_tid_init; unfold po in *.
  unfolder in *; basic_solver.
Qed.

Lemma E_ntid_po_prcl thread :
  dom_rel (⦗set_compl is_init⦘ ⨾ po ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ E ∩₁ NTid_ thread.
Proof using.
  rewrite (dom_l wf_poE).
  unfolder. ins. desf. splits; auto.
  match goal with
  | H : po _ _ |- _ => rename H into PO
  end.
  apply po_tid_init in PO. desf.
  intros BB. rewrite BB in *. desf.
Qed.

Lemma po_tid_init': po ≡ po ∩ same_tid ∪ ⦗is_init⦘ ⨾ po.
Proof using.
split; [|basic_solver].
unfold po.
rewrite ext_sb_tid_init' at 1.
basic_solver 42.
Qed.

Lemma ninit_po_same_tid : ⦗ set_compl is_init ⦘ ⨾ po ⊆ same_tid.
Proof using.
  rewrite po_tid_init'.
  basic_solver.
Qed.

Lemma same_tid_trans : transitive same_tid.
Proof using.
  red. unfold same_tid. ins.
  etransitivity; eauto.
Qed.

Lemma rf_rf WF : rf ⨾ rf ≡ ∅₂.
Proof using. rewrite (wf_rfD WF); type_solver. Qed.
Lemma rf_co WF : rf ⨾ co ≡ ∅₂.
Proof using. rewrite (wf_rfD WF), (wf_coD WF); type_solver. Qed.
Lemma co_transp_rf WF : co ⨾  rf⁻¹ ≡ ∅₂.
Proof using. rewrite (wf_rfD WF), (wf_coD WF); type_solver. Qed.
Lemma co_fr WF : co ⨾ fr ≡ ∅₂.
Proof using. rewrite (wf_coD WF), (wf_frD WF); type_solver. Qed.
Lemma fr_fr WF : fr ⨾ fr ≡ ∅₂.
Proof using. rewrite (wf_frD WF); type_solver. Qed.
Lemma rf_transp_rf WF: rf ⨾ rf⁻¹ ⊆ ⦗fun _ => True⦘.
Proof using. by apply functional_alt, WF. Qed.
Lemma rf_fr WF : rf ⨾ fr ⊆ co.
Proof using. unfold fr; sin_rewrite rf_transp_rf; rels. Qed.
Lemma rmw_in_po_loc WF: rmw ⊆ po ∩ same_loc.
Proof using. by rewrite (loceq_same_loc (loceq_rmw WF)), (rmw_in_po WF). Qed.
Lemma rf_irr WF: irreflexive rf.
Proof using. rewrite (wf_rfD WF); type_solver. Qed.
Lemma co_co WF: co ⨾ co ⊆ co.
Proof using. apply rewrite_trans, WF. Qed.

Lemma wf_rmwf WF: functional rmw.
Proof using.
  rewrite (rmw_from_non_init WF).
  arewrite (rmw ⊆ rmw ∩ rmw).
  rewrite (wf_rmwi WF) at 1.
  rewrite (wf_rmwl WF) at 1.
  unfolder; ins; desc.
  forward eapply po_semi_total_l with (y:=y) (z:=z) as X; eauto; desf.
  all: try solve [exfalso; eauto].
  apply (wf_sil WF); split; ins; congruence.
Qed.

Lemma wf_rmw_invf WF: functional (rmw)⁻¹.
Proof using.
  rewrite (rmw_from_non_init WF).
  arewrite (rmw ⊆ rmw ∩ rmw).
  rewrite (wf_rmwi WF) at 1.
  rewrite (wf_rmwl WF) at 1.
  unfolder; ins; desc.
  forward eapply po_semi_total_r with (y:=y) (z:=z) as X; eauto; desf.
  all: try solve [exfalso; eauto].
  apply (wf_sil WF); split; ins; congruence.
Qed.


(******************************************************************************)
(** ** external-internal restrictions *)
(******************************************************************************)

Definition rfe := rf \ po.
Definition coe := co \ po.
Definition fre := fr \ po.
Definition rfi := rf ∩ po.
Definition coi := co ∩ po.
Definition fri := fr ∩ po.

Lemma ri_union_re r : r ≡ r ∩ po ∪ r \ po.
Proof using. unfolder; split; ins; desf; tauto. Qed.

Lemma rfi_union_rfe : rf ≡ rfi ∪ rfe.
Proof using. apply ri_union_re. Qed.
Lemma coi_union_coe : co ≡ coi ∪ coe.
Proof using. apply ri_union_re. Qed.
Lemma fri_union_fre : fr ≡ fri ∪ fre.
Proof using. apply ri_union_re. Qed.

Lemma ri_dom r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r ∩ po ⊆ ⦗d1⦘ ⨾ r ∩ po ⨾ ⦗d2⦘.
Proof using. rewrite DOM at 1; basic_solver. Qed.
Lemma re_dom r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r \ po ⊆ ⦗d1⦘ ⨾ (r \ po) ⨾ ⦗d2⦘.
Proof using. rewrite DOM at 1; basic_solver. Qed.

Lemma wf_rfiE WF: rfi ≡ ⦗E⦘ ⨾ rfi ⨾ ⦗E⦘.
Proof using. split; [|basic_solver]. apply (ri_dom (wf_rfE WF)). Qed.
Lemma wf_coiE WF: coi ≡ ⦗E⦘ ⨾ coi ⨾ ⦗E⦘.
Proof using. split; [|basic_solver]. apply (ri_dom (wf_coE WF)). Qed.
Lemma wf_friE WF: fri ≡ ⦗E⦘ ⨾ fri ⨾ ⦗E⦘.
Proof using. split; [|basic_solver]. apply (ri_dom (wf_frE WF)). Qed.
Lemma wf_rfeE WF: rfe ≡ ⦗E⦘ ⨾ rfe ⨾ ⦗E⦘.
Proof using. split; [|basic_solver]. apply (re_dom (wf_rfE WF)). Qed.
Lemma wf_coeE WF: coe ≡ ⦗E⦘ ⨾ coe ⨾ ⦗E⦘.
Proof using. split; [|basic_solver]. apply (re_dom (wf_coE WF)). Qed.
Lemma wf_freE WF: fre ≡ ⦗E⦘ ⨾ fre ⨾ ⦗E⦘.
Proof using. split; [|basic_solver]. apply (re_dom (wf_frE WF)). Qed.
Lemma wf_rfiD WF : rfi ≡ ⦗W⦘ ⨾ rfi ⨾ ⦗R⦘.
Proof using. split; [|basic_solver]. apply (ri_dom (wf_rfD WF)). Qed.
Lemma wf_coiD WF : coi ≡ ⦗W⦘ ⨾ coi ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply (ri_dom (wf_coD WF)). Qed.
Lemma wf_friD WF : fri ≡ ⦗R⦘ ⨾ fri ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply (ri_dom (wf_frD WF)). Qed.
Lemma wf_rfeD WF : rfe ≡ ⦗W⦘ ⨾ rfe ⨾ ⦗R⦘.
Proof using. split; [|basic_solver]. apply (re_dom (wf_rfD WF)). Qed.
Lemma wf_coeD WF : coe ≡ ⦗W⦘ ⨾ coe ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply (re_dom (wf_coD WF)). Qed.
Lemma wf_freD WF : fre ≡ ⦗R⦘ ⨾ fre ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply (re_dom (wf_frD WF)). Qed.

Lemma rfi_in_po : rfi ⊆ po.
Proof using. unfold rfi; basic_solver. Qed.

Lemma rfi_in_rf : rfi ⊆ rf.
Proof using. unfold rfi; basic_solver. Qed.

Lemma rfe_in_rf : rfe ⊆ rf.
Proof using. unfold rfe; basic_solver. Qed.


Lemma coi_in_po : coi ⊆ po.
Proof using. unfold coi; basic_solver. Qed.

Lemma coi_in_co : coi ⊆ co.
Proof using. unfold coi; basic_solver. Qed.

Lemma coe_in_co : coe ⊆ co.
Proof using. unfold coe; basic_solver. Qed.

Lemma ninit_rfi_same_tid : ⦗ set_compl is_init ⦘ ⨾ rfi ⊆ same_tid.
Proof using.
  arewrite (rfi ⊆ po).
  apply ninit_po_same_tid.
Qed.

Lemma coi_trans WF : transitive coi.
Proof using.
  apply transitiveI.
  generalize po_trans (co_trans WF). intros PO CO.
  unfold coi.
  unfolder. ins. desf.
  split; [eapply CO|eapply PO]; eauto.
Qed.

Lemma fri_in_po : fri ⊆ po.
Proof using. unfold fri; basic_solver. Qed.

Lemma fri_in_fr : fri ⊆ fr.
Proof using. unfold fri; basic_solver. Qed.

Lemma fre_in_fr : fre ⊆ fr.
Proof using. unfold fre; basic_solver. Qed.

Lemma fri_coi WF : fri ⨾ coi ⊆ fri.
Proof using.
  unfold fri, coi.
  unfolder. ins. desf.
  split.
  { apply fr_co; auto. basic_solver. }
  eapply po_trans; eauto.
Qed.

(******************************************************************************)
(** ** properties of external/internal relations *)
(******************************************************************************)

Lemma seq_ii r1 r2 r3 (A: r1 ⨾ r2 ⊆ r3): r1 ∩ po ⨾ r2 ∩ po ⊆ r3 ∩ po.
Proof using.
generalize po_trans.
unfolder in *; basic_solver 21.
Qed.

(*
Lemma re_ri WF  r r' (IRR: irreflexive r)  (IRR2: irreflexive (r ⨾ po))
  (N: r ⊆ r ⨾  ⦗ fun x => ~ is_init x ⦘): (r \ po) ⨾ (r' ∩ po) ⊆ r ⨾  r' \ po.
Proof using.
  rewrite N at 1.
  unfolder; ins; desf; splits; eauto.
  intro.
  forward eapply po_semi_total_r with (y:=x) (z:=z) as X; eauto; desf.
admit.
  eauto using po_irr.
  eapply po_irr; eauto.
  by desf; revert IRR2; basic_solver.
eby intro; subst; eapply IRR.
Qed.

Lemma ri_re WF  r r' (IRR: irreflexive r')  (IRR2: irreflexive (r' ⨾ po)):
 ⦗ fun x => ~ is_init x ⦘ ⨾ (r ∩ po) ⨾ (r' \ po) ⊆ r ⨾  r' \ po.
Proof using.
unfolder; ins; desf; splits; eauto.
intro.
eapply po_semi_total_l with (x:=x) (y:=z) (z:=y) in H4; eauto.
by desf; revert IRR2; basic_solver.
eby intro; subst; eapply IRR.
Qed.
 *)

Lemma rfi_in_poloc WF : rf ∩ po ⊆ restr_eq_rel loc po.
Proof using. rewrite wf_rfl; basic_solver 12. Qed.
Lemma coi_in_poloc WF : co ∩ po ⊆ restr_eq_rel loc po.
Proof using. rewrite wf_col; basic_solver 12. Qed.
Lemma fri_in_poloc WF : fr ∩ po ⊆ restr_eq_rel loc po.
Proof using. rewrite (loceq_same_loc (loceq_fr WF)).
unfolder; unfold Events.same_loc in *.
ins; desf; splits; eauto; congruence.
Qed.
Lemma rfi_in_poloc' WF : rfi ⊆ po ∩ same_loc.
Proof using. generalize (wf_rfl WF); unfold rfi; basic_solver 12. Qed.
Lemma coi_in_poloc' WF : coi ⊆ po ∩ same_loc.
Proof using. generalize (wf_col WF); unfold coi; basic_solver 12. Qed.
Lemma fri_in_poloc' WF : fri ⊆ po ∩ same_loc.
Proof using. generalize (wf_frl WF); unfold fri; basic_solver 12. Qed.

Lemma rf_rmw_po_minus_po WF: (rf ⨾ rmw ⨾ po^? ⨾ ⦗W⦘) \ po ⊆ rfe ⨾ rmw ⨾ po^? ⨾ ⦗W⦘.
Proof using.
rewrite (seq_minus_transitive po_trans).
unionL; [by unfold rfe; basic_solver 12|].
rewrite (rmw_in_po WF) at 1.
arewrite (po ⨾ po^? ⨾ ⦗W⦘ ⊆ po) by generalize po_trans; basic_solver 21.
relsf.
Qed.

Lemma rf_rmw_po_rt_rf WF: ((rf ⨾ rmw ⨾ po^? ⨾ ⦗W⦘)^* ⨾ rf) \ po ⊆ po^? ⨾ rfe ⨾ (rmw ⨾ po^? ⨾ ⦗W⦘ ⨾ rf)^*.
Proof using.
rewrite rtE; relsf.
rewrite rtE, minus_union_l.
relsf; unionL; [by unfold rfe; basic_solver 12|].
rewrite (seq_minus_transitive po_trans).
unionL; [|by unfold rfe; basic_solver 12].
unionR right.
rewrite (ct_minus_transitive po_trans).
arewrite ((rf ⨾ rmw ⨾ po^? ⨾ ⦗W⦘) ∩ po ⊆ po).
generalize po_trans; ins; relsf.
rewrite (rf_rmw_po_minus_po WF).
rewrite !seqA.
arewrite (rmw ⨾ po^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw ⨾ po^? ⨾ ⦗W⦘)^* ⨾ rf ⊆ (rmw ⨾ po^? ⨾ ⦗W⦘ ⨾ rf )^+); [|done].
rewrite rtE; relsf; unionL; [by econs|].
rewrite ct_seq_swap, !seqA.
rewrite ct_begin at 2.
by rewrite inclusion_t_rt, !seqA.
Qed.

Lemma rmw_rf_ct WF : (rmw ⨾ po^? ⨾ ⦗W⦘ ⨾ rf)^+ ⊆ (rmw ⨾ po^? ⨾ ⦗W⦘ ∪ rfe)^+ ⨾ rf.
Proof using.
  apply inclusion_t_ind_left.
  { hahn_frame; vauto. }
  rewrite ct_begin; hahn_frame; relsf.
  arewrite (rfe ⊆ rf) at 2.
  seq_rewrite (rf_rf WF).
  relsf.
  rewrite rfi_union_rfe; relsf; unionL.
  { arewrite (rfi ⊆ po).
    rewrite (rmw_in_po WF) at 2.
    arewrite (po^? ⨾ ⦗W⦘ ⨾ po ⨾ po ⨾ po^? ⊆ po^?).
    generalize po_trans; basic_solver 21.
    basic_solver 21. }
  rewrite rt_begin at 2.
  rewrite rt_begin at 2.
  basic_solver 42.
Qed.

Lemma rmw_rf_rt_1 WF : (rmw ⨾ po^? ⨾ ⦗W⦘ ⨾ rf)^* ⊆ (rmw ⨾ po^? ⨾ ⦗W⦘ ∪ rfe)^* ⨾ rfi^?.
Proof using.
rewrite rtE; unionL; [basic_solver 12|].
rewrite (rmw_rf_ct WF).
rewrite rfi_union_rfe; relsf.
rewrite inclusion_t_rt.
relsf; unionL.
basic_solver 12.
rewrite rt_end at 2; basic_solver 12.
Qed.

(******************************************************************************)
(** ** exclusive reads/writes *)
(******************************************************************************)

Definition W_ex := codom_rel rmw.

Lemma W_ex_not_init WF : W_ex ⊆₁ set_compl is_init.
Proof using.
  unfolder. ins. desf.
  match goal with
  | H : W_ex _ |- _ => rename H into WEX
  end.
  destruct WEX as [z WEX].
  apply (rmw_in_po WF) in WEX.
  apply no_po_to_init in WEX. unfolder in WEX. desf.
Qed.

Lemma W_ex_in_W WF : W_ex ⊆₁ W.
Proof using.
unfold W_ex; rewrite (dom_r (wf_rmwD WF)); basic_solver.
Qed.

Lemma W_ex_in_E WF : W_ex ⊆₁ E.
Proof using.
  unfold W_ex. rewrite (dom_r (wf_rmwE WF)). basic_solver.
Qed.

Lemma W_ex_eq_EW_W_ex WF : W_ex ≡₁ E ∩₁ W ∩₁ W_ex.
Proof using.
  generalize (W_ex_in_E WF).
  generalize (W_ex_in_W WF).
  clear. basic_solver 10.
Qed.

Lemma rmw_W_ex : rmw ⊆ rmw ⨾ ⦗W_ex⦘.
Proof using.
  unfold W_ex; basic_solver.
Qed.

Lemma W_ex_si WF : ⦗W_ex⦘ ⨾ si ≡ si ⨾ ⦗W_ex⦘.
Proof using.
  unfold W_ex; unfolder; split; ins; desf.
  forward apply (proj2 (si_rmw WF) x0 y); unfolder; ins; desf; eauto.
  forward apply (proj2 (si_rmw WF) x0 x); unfolder; ins; desf; eauto using si_sym.
Qed.




(******************************************************************************)
(** ** rf ; rmw *)
(******************************************************************************)

Lemma wf_rfrmwE WF: rf ⨾ rmw ≡ ⦗ E ⦘ ⨾ (rf ⨾ rmw) ⨾ ⦗ E ⦘.
Proof using.
split; [|basic_solver].
rewrite (wf_rfE WF) at 1.
rewrite (wf_rmwE WF) at 1.
basic_solver.
Qed.

Lemma wf_rfrmwD WF: rf ⨾ rmw ≡ ⦗ W ⦘ ⨾ (rf ⨾ rmw) ⨾ ⦗ W ⦘.
Proof using.
split; [|basic_solver].
rewrite (wf_rfD WF) at 1.
rewrite (wf_rmwD WF) at 1.
basic_solver.
Qed.

Lemma wf_rfrmwl WF: rf ⨾ rmw ⊆ same_loc.
Proof using.
rewrite (wf_rfl WF), (wf_rmwl WF).
generalize same_loc_trans; basic_solver.
Qed.

Lemma wf_rfrmwf WF: functional (rf ⨾ rmw)⁻¹.
Proof using.
hahn_rewrite transp_seq.
by apply functional_seq; [apply wf_rmw_invf|apply WF].
Qed.

Lemma wf_rfirmwf WF : functional (rfi ⨾ rmw)⁻¹.
Proof using. arewrite (rfi ⊆ rf). eapply wf_rfrmwf; eauto. Qed.

Lemma wf_rfermwf WF : functional (rfe ⨾ rmw)⁻¹.
Proof using. arewrite (rfe ⊆ rf). eapply wf_rfrmwf; eauto. Qed.

Lemma rt_rf_rmw : (rf ⨾ rmw)^* ⊆ (rfi ⨾ rmw)^* ⨾ (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)^*)^*.
Proof using.
  eapply rt_ind_left with (P:=fun r=> r); eauto with hahn.
  basic_solver 12.
  intros k H.
  rewrite !seqA, H.
  rewrite rfi_union_rfe; relsf; unionL.
  { rewrite rt_begin at 3.
    basic_solver 21. }
  rewrite (rt_begin (rfe ⨾ rmw ⨾ (rfi ⨾ rmw)^*)) at 2.
  basic_solver 21.
Qed.

Lemma rfi_rmw_in_po_same_loc_W WF : rfi ⨾ rmw ⊆ (po ∩ same_loc) ⨾ ⦗W⦘.
Proof using.
  rewrite (dom_r (wf_rmwD WF)).
  rewrite rfi_in_poloc', rmw_in_po_loc; auto.
  sin_rewrite rewrite_trans; [done|].
  apply po_same_loc_trans.
Qed.

Lemma rfi_rmw_in_po_loc WF : rfi ⨾ rmw ⊆ po ∩ same_loc.
Proof using.
  rewrite (rfi_rmw_in_po_same_loc_W WF). basic_solver.
Qed.


End Execution.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)

#[global]
Hint Unfold rfe coe fre rfi coi fri : ie_unfolderDb.
Tactic Notation "ie_unfolder" :=  repeat autounfold with ie_unfolderDb in *.
