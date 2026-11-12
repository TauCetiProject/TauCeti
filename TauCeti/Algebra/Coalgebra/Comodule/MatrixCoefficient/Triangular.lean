/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.Data.Finset.Max

/-!
# Matrix coefficients in a triangular basis

In an upper-triangular comodule, the last nonzero coordinate of a vector has a particularly
simple matrix coefficient: it is that coordinate times the corresponding diagonal entry.
If the diagonal entries are group-like, normalizing this coordinate gives a group-like
matrix coefficient of every nonzero vector.

For a Hopf algebra, this coefficient is a unit. Thus the projective orbit of the vector
avoids a hyperplane, the affine-chart input to the fixed-point argument for solvable groups.
The coefficient calculation itself needs only a coalgebra.
-/

public section

namespace Module.Basis

open TauCeti TauCeti.Comodule

universe u v w x

section Coalgebra

variable {R : Type u} {C : Type v} {M : Type w} {ι : Type x}
  [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]
  [LinearOrder ι]

/-- If a vector has no coordinates above `i`, its `i`th matrix coefficient is its
`i`th coordinate times the corresponding diagonal entry. -/
theorem matrixCoefficient_coord_eq_smul_diagonal_of_isUpperTriangular
    (b : Module.Basis ι R M) (hb : (coefficientMatrix (C := C) b).IsUpperTriangular)
    (m : M) (i : ι) (hi : ∀ j, i < j → b.repr m j = 0) :
    matrixCoefficient (C := C) (b.coord i) m =
      b.repr m i • coefficientMatrix (C := C) b i i := by
  classical
  have h := congrArg (matrixCoefficientLinear (C := C) (b.coord i)) (b.linearCombination_repr m)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    matrixCoefficientLinear_apply] at h
  rw [← h, coefficientMatrix_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [← coefficientMatrix_apply, hb hj, smul_zero]
    · rw [hi j hj, zero_smul]
  · intro hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]

end Coalgebra

section GroupLike

variable {k : Type u} {H : Type v} {M : Type w} {ι : Type x}
  [Field k] [AddCommMonoid H] [Module k H] [Coalgebra k H]
  [AddCommMonoid M] [Module k M] [Comodule k H M]
  [LinearOrder ι]

/-- Every nonzero vector in a comodule with a triangular basis and group-like diagonal
entries has a group-like matrix coefficient. The functional is normalized at that vector
because the counit of a group-like element is one. -/
theorem exists_isGroupLikeElem_matrixCoefficient_of_isUpperTriangular
    (b : Module.Basis ι k M) (hb : (coefficientMatrix (C := H) b).IsUpperTriangular)
    (hdiag : ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i))
    {m : M} (hm : m ≠ 0) :
    ∃ φ : Module.Dual k M, IsGroupLikeElem k (matrixCoefficient (C := H) φ m) := by
  classical
  have hs : (b.repr m).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact b.repr.map_ne_zero_iff.mpr hm
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (b.repr m).support id hs
  have hcoord : b.repr m i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hvanish (j : ι) (hj : i < j) : b.repr m j = 0 := by
    by_contra h
    exact (not_le_of_gt hj) (hmax j (Finsupp.mem_support_iff.mpr h))
  refine ⟨(b.repr m i)⁻¹ • b.coord i, ?_⟩
  simpa [matrixCoefficient_smul_functional,
    b.matrixCoefficient_coord_eq_smul_diagonal_of_isUpperTriangular hb m i hvanish,
    smul_smul, hcoord] using hdiag i

end GroupLike

end Module.Basis
