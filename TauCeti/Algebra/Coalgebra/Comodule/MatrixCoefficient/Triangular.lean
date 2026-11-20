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

Over a domain, let `K` be a torsion-free bialgebra spanned by its group-like elements. A
`K`-comodule whose coefficient matrix is upper triangular with `1` on the diagonal has the
identity coefficient matrix
(`Module.Basis.coefficientMatrix_eq_one_of_isUpperTriangular_of_groupLikeSetSpan_eq_top`): the
comultiplication `Δ cᵢⱼ = ∑ₗ cᵢₗ ⊗ cₗⱼ` and an induction on the column `j` exhibit each
off-diagonal coefficient as a primitive element, and such a bialgebra has none but `0`
(`TauCeti.Subcoalgebra.eq_zero_of_groupLikeSetSpan_eq_top_of_comul_eq_tmul_add_tmul`).
Corestriction gives the same conclusion for the image of a coefficient matrix under a coalgebra
morphism into `K`
(`Module.Basis.map_coefficientMatrix_eq_one_of_isUpperTriangular_of_groupLikeSetSpan_eq_top`).
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

section GroupLikeSpan

open scoped TensorProduct

variable {R : Type u} {H : Type v} {K : Type w} {M : Type x} {ι : Type*}
  [CommRing R] [IsDomain R] [AddCommMonoid H] [Module R H] [Coalgebra R H]
  [Ring K] [Bialgebra R K] [Module.IsTorsionFree R K]
  [AddCommMonoid M] [Module R M]
  [Finite ι] [LinearOrder ι]

/-- **A comodule over a group-like-spanned bialgebra with an upper-triangular basis and diagonal
coefficients `1` is trivial.** Over a domain, let `K` be a torsion-free bialgebra spanned by its
group-like elements. If the coefficient matrix of a `K`-comodule is upper triangular with `1` on
the diagonal, then it is the identity matrix. -/
theorem coefficientMatrix_eq_one_of_isUpperTriangular_of_groupLikeSetSpan_eq_top
    [Comodule R K M] (b : Module.Basis ι R M)
    (hb : (coefficientMatrix (C := K) b).IsUpperTriangular)
    (hK : Subcoalgebra.groupLikeSetSpan (R := R) (C := K) Set.univ = ⊤)
    (hdiag : ∀ i, coefficientMatrix (C := K) b i i = 1) :
    coefficientMatrix (C := K) b = 1 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Above the diagonal, fix the row `i` and induct on the column `j`.
  have hup (i j : ι) : i < j → coefficientMatrix (C := K) b i j = 0 := by
    induction j using WellFoundedLT.induction with
    | _ j ih =>
      intro hij
      refine Subcoalgebra.eq_zero_of_groupLikeSetSpan_eq_top_of_comul_eq_tmul_add_tmul hK
        (Bialgebra.comul_one (R := R) (A := K)) ?_
      rw [comul_coefficientMatrix_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.ne, Finset.mem_univ i⟩)]
      -- The intermediate terms vanish: below the diagonal, or by the inductive hypothesis.
      have hrest : ∑ l ∈ (Finset.univ.erase j).erase i,
          coefficientMatrix (C := K) b i l ⊗ₜ[R] coefficientMatrix (C := K) b l j = 0 := by
        refine Finset.sum_eq_zero fun l hl ↦ ?_
        simp only [Finset.mem_erase] at hl
        rcases lt_or_gt_of_ne hl.1 with hl' | hl'
        · rw [hb hl', TensorProduct.zero_tmul]
        rcases lt_or_gt_of_ne hl.2.1 with hl'' | hl''
        · rw [ih l hl'' hl', TensorProduct.zero_tmul]
        · rw [hb hl'', TensorProduct.tmul_zero]
      rw [hrest, hdiag i, hdiag j, add_zero, add_comm]
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [Matrix.one_apply_ne hij.ne, hup i j hij]
  · rw [Matrix.one_apply_eq, hdiag]
  · rw [Matrix.one_apply_ne hij.ne', hb hij]

/-- **A coalgebra morphism to a group-like-spanned bialgebra trivializes an upper-triangular
representation.** Over a domain, let `K` be a torsion-free bialgebra spanned by its group-like
elements. If the image under `f` of a coefficient matrix is upper triangular with `1` on the
diagonal, then it is the identity matrix. -/
theorem map_coefficientMatrix_eq_one_of_isUpperTriangular_of_groupLikeSetSpan_eq_top
    [Comodule R H M] (b : Module.Basis ι R M) (f : H →ₗc[R] K)
    (hb : ((coefficientMatrix (C := H) b).map f).IsUpperTriangular)
    (hK : Subcoalgebra.groupLikeSetSpan (R := R) (C := K) Set.univ = ⊤)
    (hf : ∀ i, f (coefficientMatrix (C := H) b i i) = 1) :
    (coefficientMatrix (C := H) b).map f = 1 := by
  -- Corestricting along `f` turns the mapped matrix into a coefficient matrix over `K`.
  let _ : Comodule R K M := Corestrict f
  rw [← coefficientMatrix_corestrict b f] at hb ⊢
  refine b.coefficientMatrix_eq_one_of_isUpperTriangular_of_groupLikeSetSpan_eq_top hb hK
    fun i ↦ ?_
  rw [coefficientMatrix_corestrict, Matrix.map_apply, hf]

end GroupLikeSpan

end Module.Basis
