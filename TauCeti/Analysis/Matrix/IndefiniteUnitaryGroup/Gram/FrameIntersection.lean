/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.FrameGram
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# When the Gram determinant of two frames vanishes

In a space of signature `(p, q)`, an isotropic vector orthogonal to a maximal nonpositive
subspace belongs to that subspace. Consequently the Gram matrix of two such subspaces can be
singular only if their column spaces meet. For Bessel frames this characterizes the vanishing
of the frame discriminant, which separates the intersecting-frame terms from the open-cell ones.

The frame criterion is the matrix form of `New.Filling.termDisc_eq_zero_iff` in
`New/Spanning/Unfolding/Link.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
at revision `72fead1`.
-/

public section

open Fin LieAlgebra.Orthogonal

namespace Matrix

variable {p q m 𝕜 : Type*} [Fintype p] [Fintype q] [Fintype m] [DecidableEq p] [DecidableEq q]
  [RCLike 𝕜]

/-- For the form of signature `(p, q)`, a nonpositive vector with zero negative coordinates
vanishes. -/
theorem eq_zero_of_re_indefiniteDiagonal_nonpos_of_forall_inr_eq_zero {x : p ⊕ q → 𝕜}
    (hx : RCLike.re (star x ⬝ᵥ indefiniteDiagonal p q 𝕜 *ᵥ x) ≤ 0)
    (hneg : ∀ j : q, x (.inr j) = 0) : x = 0 := by
  rw [star_dotProduct_indefiniteDiagonal_mulVec_self, RCLike.ofReal_re] at hx
  simp only [hneg, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero, sub_zero] at hx
  funext i
  cases i with
  | inr j => exact hneg j
  | inl i =>
    have hi : ‖x (.inl i)‖ ^ 2 ≤ 0 :=
      (Finset.single_le_sum (f := fun j : p ↦ ‖x (.inl j)‖ ^ 2)
        (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)).trans hx
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x (.inl i))])

/-- A nonpositive vector orthogonal to an independent nonpositive family of at least `#q`
columns belongs to its column space. -/
theorem mem_range_mulVecLin_of_nonpos_of_conjTranspose_mulVec_eq_zero
    (F : Matrix (p ⊕ q) m 𝕜) (hq : Fintype.card q ≤ Fintype.card m)
    (hF : Function.Injective F.mulVec)
    (hnonpos : ∀ c, RCLike.re (star c ⬝ᵥ (Fᴴ * indefiniteDiagonal p q 𝕜 * F) *ᵥ c) ≤ 0)
    {x : p ⊕ q → 𝕜} (hx : RCLike.re (star x ⬝ᵥ indefiniteDiagonal p q 𝕜 *ᵥ x) ≤ 0)
    (horth : Fᴴ *ᵥ (indefiniteDiagonal p q 𝕜 *ᵥ x) = 0) :
    x ∈ LinearMap.range F.mulVecLin := by
  let J := indefiniteDiagonal p q 𝕜
  let f := (F.submatrix Sum.inr id).mulVecLin
  have hf_apply (v : m → 𝕜) (j : q) : f v j = (F *ᵥ v) (.inr j) := rfl
  have hQ (v : m → 𝕜) : RCLike.re (star (F *ᵥ v) ⬝ᵥ J *ᵥ (F *ᵥ v)) ≤ 0 := by
    rw [← star_dotProduct_conjTranspose_mul_mul_mulVec]
    exact hnonpos v
  have hf : Function.Injective f := by
    refine (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv ↦ ?_))
    apply hF
    simpa using eq_zero_of_re_indefiniteDiagonal_nonpos_of_forall_inr_eq_zero (hQ v)
      (fun j ↦ (hf_apply v j).symm.trans (congrFun hv j))
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  simp only [Module.finrank_fintype_fun_eq_card] at hdim
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa only [Module.finrank_fintype_fun_eq_card] using hdim.antisymm hq) (f := f)).mp hf
  obtain ⟨v, hv⟩ := hsurj (fun j ↦ x (.inr j))
  -- Subtract the unique vector of the column space with the same negative coordinates.
  let y := F *ᵥ v
  have hy : star y = star v ᵥ* Fᴴ := by simp [y, star_mulVec]
  have hyx : star y ⬝ᵥ J *ᵥ x = 0 := by
    rw [hy, ← dotProduct_mulVec, horth, dotProduct_zero]
  have hxy : star x ⬝ᵥ J *ᵥ y = 0 := by
    have hJ : J.IsHermitian := isHermitian_indefiniteDiagonal
    rw [← hJ.star_dotProduct_mulVec_comm y x, hyx, star_zero]
  have hsub : RCLike.re (star (x - y) ⬝ᵥ J *ᵥ (x - y)) ≤ 0 := by
    simp only [mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub, hxy, hyx,
      sub_zero, zero_sub, sub_neg_eq_add, map_add]
    exact add_nonpos hx (hQ v)
  have hzero := eq_zero_of_re_indefiniteDiagonal_nonpos_of_forall_inr_eq_zero hsub
    (fun j ↦ sub_eq_zero.mpr ((congrFun hv j).symm.trans (hf_apply v j)))
  exact ⟨v, (sub_eq_zero.mp hzero).symm⟩

/-- The combined Gram matrix of two independent nonpositive families of maximal dimension is
nonsingular exactly when their column spaces are disjoint. -/
theorem det_conjTranspose_fromCols_mul_mul_fromCols_ne_zero_iff
    [DecidableEq m] (F F' : Matrix (p ⊕ q) m 𝕜) (hq : Fintype.card q ≤ Fintype.card m)
    (hF : Function.Injective F.mulVec) (hF' : Function.Injective F'.mulVec)
    (hneg : ∀ c, RCLike.re (star c ⬝ᵥ (Fᴴ * indefiniteDiagonal p q 𝕜 * F) *ᵥ c) ≤ 0)
    (hneg' : ∀ c, RCLike.re (star c ⬝ᵥ (F'ᴴ * indefiniteDiagonal p q 𝕜 * F') *ᵥ c) ≤ 0) :
    ((fromCols F F')ᴴ * indefiniteDiagonal p q 𝕜 * fromCols F F').det ≠ 0 ↔
      Disjoint (LinearMap.range F.mulVecLin) (LinearMap.range F'.mulVecLin) := by
  classical
  let P := fromCols F F'
  let J := indefiniteDiagonal p q 𝕜
  have hP : Function.Injective P.mulVec ↔
      Disjoint (LinearMap.range F.mulVecLin) (LinearMap.range F'.mulVecLin) := by
    simp only [mulVec_injective_iff, range_mulVecLin] at hF hF' ⊢
    rw [linearIndependent_sum]
    have hl : P.col ∘ Sum.inl = F.col := rfl
    have hr : P.col ∘ Sum.inr = F'.col := rfl
    rw [hl, hr, and_iff_right hF, and_iff_right hF']
  rw [← hP, ← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  constructor
  · intro h
    exact Function.Injective.of_comp (f := fun x ↦ Pᴴ *ᵥ (J *ᵥ x)) (g := P.mulVec)
      (by simpa only [Function.comp_def, mulVec_mulVec] using h)
  · intro h
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    let x := P *ᵥ c
    have hz : Pᴴ *ᵥ (J *ᵥ x) = 0 := by
      simpa only [mulVecLin_apply, mulVec_mulVec, x, ← Matrix.mul_assoc] using hc
    have hstar : star x = star c ᵥ* Pᴴ := by simp [x, star_mulVec]
    have hx : star x ⬝ᵥ J *ᵥ x = 0 := by
      rw [hstar, ← dotProduct_mulVec, hz, dotProduct_zero]
    have hrows : Pᴴ = fromRows Fᴴ F'ᴴ := conjTranspose_fromCols_eq_fromRows_conjTranspose F F'
    rw [hrows, fromRows_mulVec] at hz
    have hx' : RCLike.re (star x ⬝ᵥ J *ᵥ x) ≤ 0 := by rw [hx, map_zero]
    have hl := mem_range_mulVecLin_of_nonpos_of_conjTranspose_mulVec_eq_zero F hq hF hneg hx'
      (funext fun j ↦ congrFun hz (.inl j))
    have hr := mem_range_mulVecLin_of_nonpos_of_conjTranspose_mulVec_eq_zero F' hq hF' hneg' hx'
      (funext fun j ↦ congrFun hz (.inr j))
    apply h
    simpa only [mulVec_zero] using Submodule.disjoint_def.1 (hP.mp h) x hl hr

/-- The squared norm of the determinant of the frame products equals the weighted squared norm
of its leading principal minor exactly when the two frame spans meet nontrivially. -/
theorem norm_det_sq_eq_mul_mul_norm_det_submatrix_castSucc_sq_iff_not_disjoint
    {n : ℕ} (F F' : Matrix (p ⊕ q) (Fin (n + 1)) 𝕜) {T T' : ℝ}
    (hq : Fintype.card q ≤ n + 1) (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (hF : Function.Injective F.mulVec) (hF' : Function.Injective F'.mulVec)
    (hgram : Fᴴ * indefiniteDiagonal p q 𝕜 * F = single (last n) (last n) (-(T : 𝕜)))
    (hgram' : F'ᴴ * indefiniteDiagonal p q 𝕜 * F' = single (last n) (last n) (-(T' : 𝕜))) :
    ‖(Fᴴ * indefiniteDiagonal p q 𝕜 * F').det‖ ^ 2 = T * T' *
      ‖((Fᴴ * indefiniteDiagonal p q 𝕜 * F').submatrix castSucc castSucc).det‖ ^ 2 ↔
      ¬ Disjoint (LinearMap.range F.mulVecLin) (LinearMap.range F'.mulVecLin) := by
  have hh := det_conjTranspose_fromCols_mul_mul_fromCols_ne_zero_iff F F'
    (by simpa only [Fintype.card_fin] using hq) hF hF'
    (re_star_dotProduct_mulVec_nonpos_of_frame hT hgram)
    (re_star_dotProduct_mulVec_nonpos_of_frame hT' hgram')
  rw [← hh, not_ne_iff,
    det_conjTranspose_fromCols_mul_mul_fromCols_of_frame
      isHermitian_indefiniteDiagonal hgram hgram',
    mul_eq_zero, or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)), sub_eq_zero]
  simp only [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_inj]

end Matrix
