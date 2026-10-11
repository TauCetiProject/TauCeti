/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Generators
public import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# The standard module of the split odd orthogonal Lie algebra

The standard module of `LieAlgebra.Orthogonal.typeB ι K` is irreducible over a field of
characteristic different from two, including when `ι` is empty. This supplies a faithful
irreducible module for the reductivity criterion.

The matrix conventions and root operators are those of
`TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Generators`.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 20 (the standard orthogonal module).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate II.
-/

public section

namespace TauCeti

open Matrix LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [Fintype ι] [DecidableEq ι]

section Ring

variable [CommRing K]

private theorem short_negative_diagonal_mulVec (i : ι) (v : Unit ⊕ ι ⊕ ι → K) :
    typeBShortNegativeRootMatrix i *ᵥ (typeBDiagonalMatrix (Pi.single i 1) *ᵥ v) =
      v (.inr (.inl i)) • Pi.single (.inl ()) 1 := by
  rw [typeBShortNegativeRootMatrix_def, sub_mulVec, single_mulVec, single_mulVec]
  ext a
  simp [typeBDiagonalMatrix_apply, mulVec, dotProduct, Pi.single_apply,
    Function.update_apply]

private theorem short_positive_diagonal_mulVec (i : ι) (v : Unit ⊕ ι ⊕ ι → K) :
    typeBShortRootMatrix i *ᵥ (typeBDiagonalMatrix (Pi.single i 1) *ᵥ v) =
      v (.inr (.inr i)) • Pi.single (.inl ()) 1 := by
  rw [typeBShortRootMatrix_def, sub_mulVec, single_mulVec, single_mulVec]
  ext a
  simp [typeBDiagonalMatrix_apply, mulVec, dotProduct, Pi.single_apply,
    Function.update_apply]
  split_ifs <;> simp

end Ring

variable [Field K]

private theorem middle_mem_of_ne_bot
    (N : LieSubmodule K (Orthogonal.typeB ι K) (Unit ⊕ ι ⊕ ι → K)) (hN : N ≠ ⊥) :
    Pi.single (.inl ()) 1 ∈ N := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((LieSubmodule.toSubmodule_eq_bot N).not.mpr hN)
  by_cases hp : ∃ i : ι, v (.inr (.inl i)) ≠ 0
  · obtain ⟨i, hi⟩ := hp
    have h := N.lie_mem (x := typeBShortNegativeRootGenerator i)
      (N.lie_mem (x := (typeBDiagonalEquiv (Pi.single i 1) :
        typeBDiagonalCartan K ι)) hv)
    simp only [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply,
      coe_typeBShortNegativeRootGenerator, coe_typeBDiagonalEquiv_apply] at h
    rw [short_negative_diagonal_mulVec] at h
    exact (N.toSubmodule.smul_mem_iff hi).mp h
  by_cases hn : ∃ i : ι, v (.inr (.inr i)) ≠ 0
  · obtain ⟨i, hi⟩ := hn
    have h := N.lie_mem (x := typeBShortRootGenerator i)
      (N.lie_mem (x := (typeBDiagonalEquiv (Pi.single i 1) :
        typeBDiagonalCartan K ι)) hv)
    simp only [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply,
      coe_typeBShortRootGenerator, coe_typeBDiagonalEquiv_apply] at h
    rw [short_positive_diagonal_mulVec] at h
    exact (N.toSubmodule.smul_mem_iff hi).mp h
  push Not at hp hn
  have hv' : v = v (.inl ()) • Pi.single (.inl ()) 1 := by
    ext (a | (i | i))
    · cases a; simp
    · simp [hp]
    · simp [hn]
  have h0 : v (.inl ()) ≠ 0 := by
    intro h
    exact hv0 (by rw [hv', h, zero_smul])
  rw [hv'] at hv
  exact (N.toSubmodule.smul_mem_iff h0).mp hv

variable [NeZero (2 : K)]

/-- The standard module of the split odd orthogonal Lie algebra is irreducible over any field
in which two is nonzero, including the one-dimensional module when `ι` is empty. -/
instance isIrreducible_typeB_standard :
    LieModule.IsIrreducible K (Orthogonal.typeB ι K) (Unit ⊕ ι ⊕ ι → K) := by
  apply LieModule.IsIrreducible.mk
  intro N hN
  have hm := middle_mem_of_ne_bot N hN
  have hp (i : ι) : Pi.single (.inr (.inl i)) 1 ∈ N := by
    have h := N.lie_mem (x := typeBShortRootGenerator i) hm
    rw [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply,
      coe_typeBShortRootGenerator] at h
    have heq : typeBShortRootMatrix i *ᵥ Pi.single (.inl ()) (1 : K) =
        (2 : K) • Pi.single (.inr (.inl i)) 1 := by
      have h := toLinAlgEquiv_typeBShortRootMatrix_apply_basis
        (Pi.basisFun K (Unit ⊕ ι ⊕ ι)) i (.inl ())
      rw [Matrix.toLinAlgEquiv_self] at h
      ext a
      simpa [Pi.single_apply] using congrFun h a
    rw [heq] at h
    exact (N.toSubmodule.smul_mem_iff (NeZero.ne (2 : K))).mp h
  have hn (i : ι) : Pi.single (.inr (.inr i)) 1 ∈ N := by
    have h := N.lie_mem (x := typeBShortNegativeRootGenerator i) hm
    rw [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply,
      coe_typeBShortNegativeRootGenerator] at h
    have heq : typeBShortNegativeRootMatrix i *ᵥ Pi.single (.inl ()) (1 : K) =
        -((2 : K) • Pi.single (.inr (.inr i)) 1) := by
      have h := toLinAlgEquiv_typeBShortNegativeRootMatrix_apply_basis
        (Pi.basisFun K (Unit ⊕ ι ⊕ ι)) i (.inl ())
      rw [Matrix.toLinAlgEquiv_self] at h
      ext a
      simpa [Pi.single_apply] using congrFun h a
    rw [heq] at h
    exact (N.toSubmodule.smul_mem_iff (NeZero.ne (2 : K))).mp (by simpa using N.neg_mem h)
  apply top_unique
  intro v _
  rw [← (Pi.basisFun K (Unit ⊕ ι ⊕ ι)).sum_repr v]
  apply N.sum_mem
  intro a _
  apply N.smul_mem
  rcases a with a | (i | i)
  · cases a; simpa using hm
  · simpa using hp i
  · simpa using hn i

end TauCeti
