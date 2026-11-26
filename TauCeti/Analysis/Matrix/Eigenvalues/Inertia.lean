/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Indices of inertia of a Hermitian matrix and the sign of its determinant

Let `G` be a Hermitian matrix over an `RCLike` field, with its Hermitian form
`v ↦ star v ⬝ᵥ G *ᵥ v`. The eigenvectors of `G` with positive eigenvalues span a subspace on which
the form is positive definite, so it meets every subspace on which the form is nonpositive only in
`0`. Hence the number of positive eigenvalues of `G` plus the dimension of any subspace on which
the form is nonpositive is at most the size of `G`, and likewise for the negative eigenvalues and
the subspaces on which the form is nonnegative.

If the form is nonpositive on a subspace `W`, nonnegative on a subspace `W'`, and the dimensions
of `W` and `W'` add up to at least the size of `G`, then either `G` is singular or exactly
`dim W` of its eigenvalues are negative. In both cases `(-1) ^ dim W * det G ≥ 0`.

## Main results

* `Matrix.IsHermitian.card_pos_eigenvalues_add_finrank_le`: the number of positive eigenvalues
  plus the dimension of a subspace on which the form is nonpositive is at most the size.
* `Matrix.IsHermitian.card_neg_eigenvalues_add_finrank_le`: the same for the negative eigenvalues
  and a subspace on which the form is nonnegative.
* `Matrix.IsHermitian.neg_one_pow_finrank_mul_re_det_nonneg`: the sign of the determinant.
-/

public section

open Module

namespace Matrix.IsHermitian

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {G : Matrix ι ι 𝕜}

/-- The eigenvectors of `G` with index satisfying `P`, as the columns of a matrix. -/
private noncomputable abbrev eigenColumns (hG : G.IsHermitian) (P : ι → Prop) :
    Matrix ι {i // P i} 𝕜 :=
  (hG.eigenvectorUnitary : Matrix ι ι 𝕜).submatrix id Subtype.val

/-- Compressing a matrix to the span of some of the eigenvectors of `G` is taking a square
block of its conjugate by the eigenvector unitary. -/
private theorem conjTranspose_eigenColumns_mul_mul (hG : G.IsHermitian) (P : ι → Prop)
    (M : Matrix ι ι 𝕜) :
    (hG.eigenColumns P)ᴴ * M * hG.eigenColumns P =
      (star (hG.eigenvectorUnitary : Matrix ι ι 𝕜) * M * hG.eigenvectorUnitary).submatrix
        Subtype.val Subtype.val := by
  rw [conjTranspose_submatrix, ← submatrix_id_id M, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id, star_eq_conjTranspose, submatrix_id_id]

/-- The form of `G` on the span of the eigenvectors with index satisfying `P`, in the
coordinates given by these eigenvectors. -/
private theorem re_star_dotProduct_mulVec_eigenColumns (hG : G.IsHermitian) (P : ι → Prop)
    [DecidablePred P] (c : {i // P i} → 𝕜) :
    RCLike.re (star (hG.eigenColumns P *ᵥ c) ⬝ᵥ G *ᵥ (hG.eigenColumns P *ᵥ c)) =
      ∑ i, hG.eigenvalues i.val * ‖c i‖ ^ 2 := by
  have h_diag : (hG.eigenColumns P)ᴴ * G * hG.eigenColumns P =
      diagonal fun i => (hG.eigenvalues i.val : 𝕜) := by
    have h := hG.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [conjTranspose_eigenColumns_mul_mul, h, submatrix_diagonal _ _ Subtype.val_injective]
    rfl
  rw [← star_dotProduct_conjTranspose_mul_mul_mulVec, h_diag]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-- The span of the eigenvectors of `G` with index satisfying `P` has dimension the number of
these indices. -/
private theorem finrank_range_eigenColumns (hG : G.IsHermitian) (P : ι → Prop)
    [DecidablePred P] :
    finrank 𝕜 (LinearMap.range (hG.eigenColumns P).mulVecLin) = Fintype.card {i // P i} := by
  have h_one : (hG.eigenColumns P)ᴴ * hG.eigenColumns P = 1 := by
    rw [← Matrix.mul_one (hG.eigenColumns P)ᴴ, conjTranspose_eigenColumns_mul_mul,
      Matrix.mul_one, Unitary.coe_star_mul_self, submatrix_one _ Subtype.val_injective]
  have h_inj : Function.Injective (hG.eigenColumns P).mulVecLin := fun c c' hcc' => by
    have h := congrArg ((hG.eigenColumns P)ᴴ *ᵥ ·) hcc'
    simpa only [mulVecLin_apply, mulVec_mulVec, h_one, one_mulVec] using h
  rw [LinearMap.finrank_range_of_inj h_inj, finrank_fintype_fun_eq_card]

/-- If no nonzero vector of the span of the eigenvectors with index satisfying `P` lies in `W`,
then the number of these indices plus the dimension of `W` is at most the size of `G`. -/
private theorem card_add_finrank_le (hG : G.IsHermitian) (P : ι → Prop) [DecidablePred P]
    {W : Submodule 𝕜 (ι → 𝕜)}
    (hW : ∀ c : {i // P i} → 𝕜, c ≠ 0 → hG.eigenColumns P *ᵥ c ∉ W) :
    Fintype.card {i // P i} + finrank 𝕜 W ≤ Fintype.card ι := by
  set V := LinearMap.range (hG.eigenColumns P).mulVecLin
  have h_inf : V ⊓ W = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v ⟨⟨c, hc⟩, hvW⟩ => ?_
    subst hc
    by_contra hv
    exact hW c (by rintro rfl; simp at hv) hvW
  simpa [V, finrank_range_eigenColumns, finrank_fintype_fun_eq_card] using
    Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.2 h_inf)

/-- **Positive eigenvalues against nonpositive subspaces.** If the form of the Hermitian matrix
`G` is nonpositive on a subspace `W`, then the number of positive eigenvalues of `G` plus the
dimension of `W` is at most the size of `G`. -/
theorem card_pos_eigenvalues_add_finrank_le (hG : G.IsHermitian) {W : Submodule 𝕜 (ι → 𝕜)}
    (hW : ∀ v ∈ W, RCLike.re (star v ⬝ᵥ G *ᵥ v) ≤ 0) :
    Fintype.card {i // 0 < hG.eigenvalues i} + finrank 𝕜 W ≤ Fintype.card ι := by
  refine hG.card_add_finrank_le _ fun c hc hcW => (hW _ hcW).not_gt ?_
  rw [re_star_dotProduct_mulVec_eigenColumns]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  exact Finset.sum_pos' (fun j _ => mul_nonneg j.property.le (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos i.property (pow_pos (norm_pos_iff.2 (by simpa using hi)) 2)⟩

/-- **Negative eigenvalues against nonnegative subspaces.** If the form of the Hermitian matrix
`G` is nonnegative on a subspace `W`, then the number of negative eigenvalues of `G` plus the
dimension of `W` is at most the size of `G`. -/
theorem card_neg_eigenvalues_add_finrank_le (hG : G.IsHermitian) {W : Submodule 𝕜 (ι → 𝕜)}
    (hW : ∀ v ∈ W, 0 ≤ RCLike.re (star v ⬝ᵥ G *ᵥ v)) :
    Fintype.card {i // hG.eigenvalues i < 0} + finrank 𝕜 W ≤ Fintype.card ι := by
  refine hG.card_add_finrank_le _ fun c hc hcW => (hW _ hcW).not_gt ?_
  rw [re_star_dotProduct_mulVec_eigenColumns]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  exact Finset.sum_neg' (fun j _ => mul_nonpos_of_nonpos_of_nonneg j.property.le (sq_nonneg _))
    ⟨i, Finset.mem_univ _,
      mul_neg_of_neg_of_pos i.property (pow_pos (norm_pos_iff.2 (by simpa using hi)) 2)⟩

/-- **The sign of the determinant of a Hermitian matrix.** If the form of the Hermitian matrix
`G` is nonpositive on a subspace `W` and nonnegative on a subspace `W'`, and the dimensions of
`W` and `W'` add up to at least the size of `G`, then `(-1) ^ dim W * det G ≥ 0`: either `G` is
singular, or exactly `dim W` of its eigenvalues are negative. -/
theorem neg_one_pow_finrank_mul_re_det_nonneg (hG : G.IsHermitian) {W W' : Submodule 𝕜 (ι → 𝕜)}
    (hW : ∀ v ∈ W, RCLike.re (star v ⬝ᵥ G *ᵥ v) ≤ 0)
    (hW' : ∀ v ∈ W', 0 ≤ RCLike.re (star v ⬝ᵥ G *ᵥ v))
    (h : Fintype.card ι ≤ finrank 𝕜 W + finrank 𝕜 W') :
    0 ≤ (-1) ^ finrank 𝕜 W * RCLike.re G.det := by
  rw [hG.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  by_cases h0 : ∃ i, hG.eigenvalues i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
  push Not at h0
  -- With no zero eigenvalue, the indices split into those of negative and positive eigenvalues.
  have h_split : Fintype.card {i // hG.eigenvalues i < 0} +
      Fintype.card {i // 0 < hG.eigenvalues i} = Fintype.card ι := by
    have e : {i // 0 < hG.eigenvalues i} ≃ {i // ¬hG.eigenvalues i < 0} :=
      Equiv.subtypeEquivRight fun i =>
        ⟨fun hi => not_lt.2 hi.le, fun hi => lt_of_le_of_ne (not_lt.1 hi) (h0 i).symm⟩
    rw [Fintype.card_congr e, Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le fun i => hG.eigenvalues i < 0
    omega
  have h_neg : Fintype.card {i // hG.eigenvalues i < 0} = finrank 𝕜 W := by
    have := hG.card_pos_eigenvalues_add_finrank_le hW
    have := hG.card_neg_eigenvalues_add_finrank_le hW'
    omega
  rw [← h_neg, Fintype.card_subtype, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => hG.eigenvalues i < 0), ← mul_assoc, ← Finset.prod_neg]
  exact mul_nonneg
    (Finset.prod_nonneg fun i hi => neg_nonneg.2 (Finset.mem_filter.1 hi).2.le)
    (Finset.prod_nonneg fun i hi => not_lt.1 (Finset.mem_filter.1 hi).2)

end Matrix.IsHermitian
