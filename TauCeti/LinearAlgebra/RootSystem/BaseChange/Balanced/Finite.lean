/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Balanced finite root pairings in characteristic zero

Over a field of characteristic zero, every root pairing with finitely many roots is balanced
(`RootPairing.instIsBalancedOfCharZero`), with no crystallographic or anisotropy assumption: the
Weyl group acts on `P.rootSpan R` through a finite quotient, and averaging over that quotient kills
every root (since each reflection negates its own root) while fixing `P.corootKer` pointwise,
forcing `Disjoint (P.rootSpan R) P.corootKer`.

## Main results

* `RootPairing.disjoint_rootSpan_corootKer`: for finitely many roots and a torsion-free additive
  weight group, the root span and the central kernel intersect trivially.
* `RootPairing.finrank_add_finrank_corootKer_eq`: dimension formula
  `finrank K (Q.corootSpan K) + finrank K Q.corootKer = finrank K M` over any field.
* `RootPairing.finrank_rootSpan_eq_finrank_corootSpan_of_charZero`: in characteristic zero with
  finitely many roots, the root span and coroot span have equal dimension.
* `RootPairing.instIsBalancedOfCharZero`: every finite root pairing over a field of characteristic
  zero is balanced.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §1.
-/

public section

open Function Module Set Submodule

namespace RootPairing

section Finite

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

private noncomputable def weylQuotientAct
    (q : P.weylGroup ⧸ P.weylGroupToPerm.ker) (x : P.rootSpan R) : M :=
  Quotient.liftOn' q (fun w ↦ w • (x : M)) fun w₁ w₂ h ↦ by
    have hk : w₁⁻¹ * w₂ ∈ P.weylGroupToPerm.ker := QuotientGroup.leftRel_apply.mp h
    calc
      w₁ • (x : M) = w₁ • ((w₁⁻¹ * w₂) • (x : M)) :=
        congrArg (w₁ • ·) (P.smul_eq_self_of_mem_ker_indexHom hk x.property).symm
      _ = w₂ • (x : M) := by rw [← mul_smul, mul_inv_cancel_left]

private lemma weylQuotientAct_mk (w : P.weylGroup) (x : P.rootSpan R) :
    weylQuotientAct P (QuotientGroup.mk w) x = w • (x : M) :=
  rfl

private lemma sum_weylQuotientAct_eq_zero
    [Fintype (P.weylGroup ⧸ P.weylGroupToPerm.ker)] [HasUniqueDiv M]
    {x : M} (hx : x ∈ P.rootSpan R) :
    ∑ q : P.weylGroup ⧸ P.weylGroupToPerm.ker, weylQuotientAct P q ⟨x, hx⟩ = 0 := by
  let G := P.weylGroup ⧸ P.weylGroupToPerm.ker
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    let s : G := QuotientGroup.mk (weylGroup.ofIdx P i)
    let S : M := ∑ q : G, weylQuotientAct P q ⟨P.root i, subset_span (mem_range_self i)⟩
    have hneg : S = -S := by
      calc
        S = ∑ q : G, weylQuotientAct P (q * s) ⟨P.root i, subset_span (mem_range_self i)⟩ :=
          (Fintype.sum_equiv (_root_.Equiv.mulRight s) _ _ fun _ ↦ rfl).symm
        _ = ∑ q : G, -weylQuotientAct P q ⟨P.root i, subset_span (mem_range_self i)⟩ := by
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          induction q using QuotientGroup.induction_on with | _ w => ?_
          rw [← QuotientGroup.mk_mul, weylQuotientAct_mk, weylQuotientAct_mk, mul_smul,
            weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_self, smul_neg]
        _ = -S := Finset.sum_neg_distrib _
    have htwo : 2 • S = 0 := by
      rw [two_nsmul]
      exact add_eq_zero_iff_eq_neg.mpr hneg
    exact (nsmul_right_inj (M := M) (by decide : 2 ≠ 0)).mp (by simpa only [nsmul_zero] using htwo)
  | zero =>
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    induction q using QuotientGroup.induction_on with | _ w => exact smul_zero w
  | add y z hy hz ihy ihz =>
    have hadd (q : G) : weylQuotientAct P q ⟨y + z, add_mem hy hz⟩ =
        weylQuotientAct P q ⟨y, hy⟩ + weylQuotientAct P q ⟨z, hz⟩ := by
      induction q using QuotientGroup.induction_on with | _ w => exact smul_add w y z
    simp only [hadd, Finset.sum_add_distrib, ihy, ihz, add_zero]
  | smul c y hy ihy =>
    have hsmul (q : G) : weylQuotientAct P q ⟨c • y, smul_mem _ c hy⟩ =
        c • weylQuotientAct P q ⟨y, hy⟩ := by
      induction q using QuotientGroup.induction_on with | _ w => exact smul_comm w c y
    simp only [hsmul, ← Finset.smul_sum, ihy, smul_zero]

/-- For finitely many roots and a torsion-free additive weight group, the root span and the
central kernel intersect trivially. -/
theorem disjoint_rootSpan_corootKer [Finite ι] [HasUniqueDiv M] :
    Disjoint (P.rootSpan R) P.corootKer := by
  let G := P.weylGroup ⧸ P.weylGroupToPerm.ker
  have : Finite G :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange P.weylGroupToPerm).toEquiv.symm
  let _ : Fintype G := Fintype.ofFinite G
  rw [Submodule.disjoint_def]
  intro x hx₁ hx₂
  have hzero : ∑ q : G, weylQuotientAct P q ⟨x, hx₁⟩ = 0 := P.sum_weylQuotientAct_eq_zero hx₁
  have hfix (q : G) : weylQuotientAct P q ⟨x, hx₁⟩ = x := by
    induction q using QuotientGroup.induction_on with | _ w =>
      exact weylGroup_smul_eq_self_of_mem_corootKer hx₂ w
  simp only [hfix, Finset.sum_const, Finset.card_univ] at hzero
  exact (nsmul_right_inj (M := M) Fintype.card_ne_zero).mp (by simpa only [nsmul_zero] using hzero)

end Finite

section CharZero

/-- Over any field, the dimensions of the coroot span and the central kernel sum to the
dimension of the weight space. -/
theorem finrank_add_finrank_corootKer_eq {ι K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (Q : RootPairing ι K M N) :
    finrank K (Q.corootSpan K) + finrank K Q.corootKer = finrank K M := by
  have : IsReflexive K M := .of_isPerfPair Q.toLinearMap
  have : IsReflexive K N := .of_isPerfPair Q.flip.toLinearMap
  have hker : finrank K Q.corootKer = finrank K (Q.corootSpan K).dualAnnihilator := by
    rw [corootKer_def, ← Q.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
    exact LinearEquiv.finrank_map_eq _ _
  rw [hker, Q.toPerfPair.finrank_eq, Subspace.dual_finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq]

variable {ι K M N : Type*} [Finite ι] [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

private lemma finrank_rootSpan_le_finrank_corootSpan (Q : RootPairing ι K M N) :
    finrank K (Q.rootSpan K) ≤ finrank K (Q.corootSpan K) := by
  have : HasUniqueDiv M := .of_isTorsionFree K M
  have : IsReflexive K M := .of_isPerfPair Q.toLinearMap
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Q.rootSpan K) Q.corootKer
  rw [Q.disjoint_rootSpan_corootKer.eq_bot, finrank_bot, add_zero] at hsup
  have hle : finrank K (Q.rootSpan K) + finrank K Q.corootKer ≤ finrank K M :=
    hsup ▸ Submodule.finrank_le _
  have hker := finrank_add_finrank_corootKer_eq Q
  omega

/-- For a finite root pairing over a field of characteristic zero, the root span and the coroot
span have the same dimension. -/
theorem finrank_rootSpan_eq_finrank_corootSpan_of_charZero (Q : RootPairing ι K M N) :
    finrank K (Q.rootSpan K) = finrank K (Q.corootSpan K) :=
  le_antisymm (finrank_rootSpan_le_finrank_corootSpan Q)
    (finrank_rootSpan_le_finrank_corootSpan Q.flip)

private lemma isCompl_rootSpan_corootKer_of_charZero (Q : RootPairing ι K M N) :
    IsCompl (Q.rootSpan K) Q.corootKer := by
  have : HasUniqueDiv M := .of_isTorsionFree K M
  have : IsReflexive K M := .of_isPerfPair Q.toLinearMap
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr Q.disjoint_rootSpan_corootKer
  rw [finrank_rootSpan_eq_finrank_corootSpan_of_charZero Q, finrank_add_finrank_corootKer_eq]

/-- **Every finite root pairing over a field of characteristic zero is balanced.** Neither
crystallographicity nor nondegeneracy of the trace root form is needed. -/
instance instIsBalancedOfCharZero (Q : RootPairing ι K M N) : Q.IsBalanced :=
  Q.isBalanced_iff_isCompl.mpr
    ⟨isCompl_rootSpan_corootKer_of_charZero Q, isCompl_rootSpan_corootKer_of_charZero Q.flip⟩

end CharZero

end RootPairing
