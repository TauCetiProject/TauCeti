/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.RingTheory.Bialgebra.GroupLike
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

A coalgebra morphism into a bialgebra spanned by its group-like elements that sends the diagonal
coefficients of an upper-unitriangular basis to `1` sends the whole coefficient matrix to the
identity matrix (`TauCeti.Comodule.map_coefficientMatrix_eq_one_of_isUpperUnitriangular`): the
comultiplication `Δ cᵢⱼ = ∑ₗ cᵢₗ ⊗ cₗⱼ` and an induction on `j - i` exhibit each image of an
off-diagonal coefficient as a primitive element, and such a bialgebra has none but `0`
(`TauCeti.Subcoalgebra.eq_zero_of_comul_eq_of_groupLikeSetSpan_eq_top`).
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

namespace TauCeti.Comodule

open scoped TensorProduct

universe u v

variable {k : Type u} {H : Type*} {K : Type v} {M : Type*}
variable [Field k] [Semiring H] [Module k H] [Coalgebra k H]
variable [Ring K] [Bialgebra k K]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- **A coalgebra morphism to a group-like-spanned bialgebra trivializes an upper-unitriangular
representation.** If `f` preserves `1` on the diagonal coefficients, then it sends the
coefficient matrix of an upper-unitriangular basis to the identity matrix. -/
theorem map_coefficientMatrix_eq_one_of_isUpperUnitriangular {n : ℕ}
    (b : Module.Basis (Fin n) k M)
    (hb : (coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤)
    (f : H →ₗc[k] K) (hf : ∀ i, f (coefficientMatrix (C := H) b i i) = 1) :
    (coefficientMatrix (C := H) b).map f = 1 := by
  -- Entries below the diagonal vanish, and the diagonal maps to `1`.
  have hlow {i j : Fin n} (h : j < i) : f (coefficientMatrix (C := H) b i j) = 0 := by
    rw [hb.isUpperTriangular h, map_zero]
  -- Above the diagonal, induct on the distance `j - i` to the diagonal.
  suffices h : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) - i = d → i < j →
      f (coefficientMatrix (C := H) b i j) = 0 by
    ext i j
    rw [Matrix.map_apply]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h _ i j rfl hij]
    · rw [Matrix.one_apply_eq, hf]
    · rw [Matrix.one_apply_ne hij.ne', hlow hij]
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij
    refine Subcoalgebra.eq_zero_of_comul_eq_of_groupLikeSetSpan_eq_top hK
      ⟨1, IsGroupLikeElem.one⟩ ?_
    dsimp only
    rw [← CoalgHomClass.map_comp_comul_apply, comul_coefficientMatrix_eq_sum, map_sum]
    simp only [TensorProduct.map_tmul, CoalgHom.coe_linearMapOfClass]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.ne, Finset.mem_univ i⟩)]
    -- The intermediate terms vanish: below the diagonal, or by the inductive hypothesis.
    have hrest : ∑ l ∈ (Finset.univ.erase j).erase i,
        f (coefficientMatrix (C := H) b i l) ⊗ₜ[k] f (coefficientMatrix (C := H) b l j) = 0 := by
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      simp only [Finset.mem_erase] at hl
      rcases lt_or_gt_of_ne hl.1 with hl' | hl'
      · rw [hlow hl', TensorProduct.zero_tmul]
      rcases lt_or_gt_of_ne hl.2.1 with hl'' | hl''
      · rw [ih ((j : ℕ) - l) (by omega) l j rfl hl'', TensorProduct.tmul_zero]
      · rw [hlow hl'', TensorProduct.tmul_zero]
    have hi := hf i
    have hj := hf j
    rw [hrest, hi, hj, add_zero, add_comm]

end TauCeti.Comodule
