/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Generators

/-!
# The center of the split odd orthogonal Lie algebra

The split odd orthogonal Lie algebra has zero center over a commutative ring when two is a
regular element. This center-free property supports the semisimplicity and Killing-form APIs.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate II.
-/

public section

namespace TauCeti

open Matrix LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

/-- The center of the split odd orthogonal Lie algebra vanishes over a commutative ring
when multiplication by two is injective. -/
@[simp]
theorem center_typeB_eq_bot (h2 : IsRegular (2 : K)) : center K (Orthogonal.typeB ι K) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  intro x hx
  have hc := (mem_maxTrivSubmodule K (Orthogonal.typeB ι K) _ x).mp hx
  have hxH : x ∈ typeBDiagonalCartan K ι := by
    rw [← typeBDiagonalCartan_normalizer_eq_self K ι h2,
      LieSubalgebra.mem_normalizer_iff']
    intro y _
    rw [hc y]
    exact (typeBDiagonalCartan K ι).zero_mem
  let d := (typeBDiagonalEquiv (K := K) (ι := ι)).symm ⟨x, hxH⟩
  have hx' : x = (typeBDiagonalEquiv d : typeBDiagonalCartan K ι) := by
    simp only [d, LinearEquiv.apply_symm_apply]
  have hd0 : d = 0 := by
    funext i
    have h := hc (typeBShortRootGenerator i)
    rw [hx', coe_typeBDiagonalEquiv_apply, ← lie_skew,
      typeBDiagonalMatrix_lie_shortRootGenerator, neg_eq_zero] at h
    have he := congrArg (fun a : Orthogonal.typeB ι K ↦
      (a : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inl ())) h
    simpa [coe_typeBShortRootGenerator, typeBShortRootMatrix_def,
      h2.right.mul_right_eq_zero_iff] using he
  rw [hx', hd0, map_zero]
  rfl

end TauCeti
