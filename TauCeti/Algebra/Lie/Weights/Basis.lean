/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.FormalCharacter
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Formal characters from a weight basis

A basis of simultaneous eigenvectors makes every acting endomorphism diagonalizable, so its
honest and generalized weight spaces agree over the original field. The formal character is
the sum of the corresponding group-algebra basis elements, counting repeated weights with
their multiplicities. If the basis weights are pairwise distinct, each occurring weight space
is a line and each weight has coefficient one.

These results connect explicit diagonal actions, such as the exterior model of spinors, to
`TauCeti.formalCharacter` without requiring algebraic closedness or characteristic zero.
-/

public section

open LieModule Module

namespace Module.Basis

universe u v w t

variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L]
  [LieRing.IsNilpotent L] {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] {ι : Type t}
  (b : Module.Basis ι K M) {μ : ι → Module.Dual K L}
  (hb : ∀ i x, ⁅x, b i⁆ = μ i x • b i)

include hb

/-- A basis of weight vectors makes generalized weight spaces equal to honest weight spaces. -/
theorem genWeightSpace_eq_weightSpace_of_weight_basis (χ : L → K) :
    genWeightSpace M χ = weightSpace M χ := by
  have hss (x : L) : (toEnd K L M x).IsSemisimple := by
    apply TauCeti.isSemisimple_of_iSup_eigenspace_eq_top
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (μ i x) (Module.End.mem_eigenspace_iff.mpr (hb i x))
  ext m
  rw [mem_genWeightSpace, mem_weightSpace]
  refine forall_congr' fun x => ?_
  rw [← Module.End.mem_maxGenEigenspace,
    (hss x).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff, LieModule.toEnd_apply_apply]

omit [LieRing.IsNilpotent L] in
/-- With distinct basis weights, the weight space at a basis weight is its basis-vector line. -/
theorem weightSpace_eq_span_singleton_of_weight_basis
    (hμ : Function.Injective μ) (i : ι) :
    (weightSpace M (μ i : L → K)).toSubmodule = K ∙ b i := by
  classical
  refine le_antisymm (fun m hm => ?_) ?_
  · have hm' := (mem_weightSpace _ m).mp hm
    have hsupp : (b.repr m).support ⊆ {i} := by
      intro j hj
      by_contra hji
      have hne : (μ j : L → K) ≠ μ i := fun h =>
        hji (Finset.mem_singleton.mpr (hμ (DFunLike.coe_injective h)))
      exact Finsupp.mem_support_iff.mp hj
        (b.repr_eq_zero_of_weight_ne (f := toEnd K L M)
          (a := fun i => (μ i : L → K)) hb hm' hne)
    rw [b.eq_smul_of_repr_support_subset_singleton hsupp]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (mem_weightSpace _ _).mpr (hb i)

/-- A basis of weight vectors gives linear generalized weights vanishing on brackets. -/
theorem linearWeights_of_weight_basis : LinearWeights K L M := by
  have aux (χ : L → K) (hχ : genWeightSpace M χ ≠ ⊥) :
      ∃ m : M, m ≠ 0 ∧ ∀ x, ⁅x, m⁆ = χ x • m := by
    obtain ⟨m, hm, hm₀⟩ := (⟨χ, hχ⟩ : Weight K L M).exists_ne_zero
    rw [b.genWeightSpace_eq_weightSpace_of_weight_basis hb] at hm
    exact ⟨m, hm₀, (mem_weightSpace _ _).mp hm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ x y
    obtain ⟨m, hm, hw⟩ := aux χ hχ
    apply smul_left_injective K hm
    simpa only [hw, add_smul] using (add_lie x y m)
  · intro χ hχ t x
    obtain ⟨m, hm, hw⟩ := aux χ hχ
    apply smul_left_injective K hm
    simpa only [hw, smul_assoc] using (smul_lie t x m)
  · intro χ hχ x y
    obtain ⟨m, hm, hw⟩ := aux χ hχ
    apply smul_left_injective K hm
    simpa only [hw, lie_smul, smul_smul, mul_comm, sub_self, zero_smul] using (lie_lie x y m)

variable [Fintype ι]

/-- The formal character of a module with a finite basis of weight vectors is the sum of
those weights, counting repeated weights with their multiplicities. -/
theorem formalCharacter_eq_sum_single_of_weight_basis :
    letI := b.finiteDimensional_of_finite
    letI := b.linearWeights_of_weight_basis hb
    TauCeti.formalCharacter K L M = ∑ i, AddMonoidAlgebra.single (μ i) (1 : ℤ) := by
  let _ := b.finiteDimensional_of_finite
  let _ := b.linearWeights_of_weight_basis hb
  classical
  refine AddMonoidAlgebra.ext (Finsupp.ext fun χ => ?_)
  rw [TauCeti.formalCharacter_coeff,
    b.genWeightSpace_eq_weightSpace_of_weight_basis hb, ← TauCeti.finrank_toSubmodule]
  have hspace : (weightSpace M (χ : L → K)).toSubmodule =
      Submodule.span K (b '' {i | μ i = χ}) := by
    refine le_antisymm (fun m hm => ?_) (Submodule.span_le.mpr ?_)
    · apply b.mem_span_image.mpr
      intro i hi
      by_contra hne
      have hne' : (μ i : L → K) ≠ χ := fun h => hne (DFunLike.coe_injective h)
      exact Finsupp.mem_support_iff.mp hi
        (b.repr_eq_zero_of_weight_ne (f := toEnd K L M)
          (a := fun i => (μ i : L → K)) hb ((mem_weightSpace _ _).mp hm) hne')
    · rintro _ ⟨i, hi, rfl⟩
      exact (mem_weightSpace _ _).mpr (by
        simpa only [Set.mem_ofPred_eq.mp hi] using hb i)
  rw [hspace, Set.image_eq_range]
  have hlin : LinearIndependent K (fun i : ({i | μ i = χ} : Set ι) => b i) :=
    b.linearIndependent.comp _ Subtype.val_injective
  rw [finrank_span_eq_card hlin]
  simp [Fintype.card_subtype, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, eq_comm]

end Module.Basis
