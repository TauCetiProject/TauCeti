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
honest and generalized weight spaces agree over the original field. If the basis weights are
pairwise distinct, each occurring weight space is a line and the formal character is the sum
of the corresponding group-algebra basis elements, with coefficient one.

These results connect explicit diagonal actions, such as the exterior model of spinors, to
`TauCeti.formalCharacter` without requiring algebraic closedness or characteristic zero.
The diagonalizability argument uses `TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`.
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
    Module.End.mem_eigenspace_iff]
  rfl

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

variable [Fintype ι] [LinearWeights K L M] [FiniteDimensional K M]

/-- The formal character of a module with a basis of distinct weight vectors is the sum of
those weights, each with multiplicity one. -/
theorem formalCharacter_eq_sum_single_of_weight_basis (hμ : Function.Injective μ) :
    TauCeti.formalCharacter K L M = ∑ i, AddMonoidAlgebra.single (μ i) (1 : ℤ) := by
  classical
  refine AddMonoidAlgebra.ext (Finsupp.ext fun χ => ?_)
  rw [TauCeti.formalCharacter_coeff,
    b.genWeightSpace_eq_weightSpace_of_weight_basis hb]
  by_cases hχ : χ ∈ Set.range μ
  · obtain ⟨i, rfl⟩ := hχ
    rw [← TauCeti.finrank_toSubmodule,
      b.weightSpace_eq_span_singleton_of_weight_basis hb hμ,
      finrank_span_singleton (b.ne_zero i)]
    simp only [Nat.cast_one, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact ite_eq_right (fun h => hji (hμ h))
    · simp
  · have hbot : weightSpace M (χ : L → K) = ⊥ := by
      rw [LieSubmodule.eq_bot_iff]
      intro m hm
      apply b.repr.injective
      ext i
      have hne : (μ i : L → K) ≠ χ := fun h => hχ ⟨i, DFunLike.coe_injective h⟩
      simpa using b.repr_eq_zero_of_weight_ne (f := toEnd K L M)
          (a := fun i => (μ i : L → K)) hb ((mem_weightSpace _ _).mp hm) hne
    rw [hbot]
    simp only [LieSubmodule.finrank_bot, Nat.cast_zero, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right (fun h => hχ ⟨i, h⟩)).symm

end Module.Basis
