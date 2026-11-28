/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Skew-symmetric maps and orthogonal hyperplane frames on real inner product spaces

A map `f : E → E` on a real inner product space satisfying `⟪f x, y⟫ = -⟪x, f y⟫` sends every
vector `x` into its orthogonal complement `(ℝ ∙ x)ᗮ`. When `f` also satisfies `f (f x) = -x`, it
preserves inner products and norms, and any two anticommuting skew-symmetric maps take orthogonal
values at every vector `x`. Evaluating a family of `card ι` pairwise anticommuting skew-symmetric
maps squaring to `-1` at a unit vector `x` therefore produces an orthonormal family in `(ℝ ∙ x)ᗮ`,
which forms an `OrthonormalBasis` of `(ℝ ∙ x)ᗮ` whenever `finrank ℝ E = card ι + 1`. In odd
finite dimension a skew-symmetric linear map `f` has a nonzero kernel vector, since otherwise
`x, y ↦ ⟪f x, y⟫` would be a nondegenerate alternating form, forcing even dimension.

## Main definitions and results

* `TauCeti.inner_apply_self_eq_zero_of_skew`, `TauCeti.mem_orthogonal_span_singleton_of_skew`:
  for a skew-symmetric map `f`, `⟪f x, x⟫ = 0` and `f x ∈ (ℝ ∙ x)ᗮ`.
* `TauCeti.norm_sq_apply_of_skew`: for a skew-symmetric map `f`, `‖f x‖ ^ 2 = -⟪x, f (f x)⟫`.
* `TauCeti.inner_apply_apply_of_skew_of_sq_neg_id`, `TauCeti.norm_apply_of_skew_of_sq_neg_id`:
  a skew-symmetric map satisfying `f (f x) = -x` preserves inner products and norms.
* `TauCeti.inner_apply_apply_eq_zero_of_skew_anticommute`: anticommuting skew-symmetric maps take
  orthogonal values at every vector.
* `TauCeti.orthonormal_apply_of_skew_anticommute`,
  `TauCeti.orthonormal_orthogonal_of_skew_anticommute`: evaluating pairwise anticommuting
  skew-symmetric maps squaring to `-1` at a unit vector `x` produces an orthonormal family in `E`
  and in `(ℝ ∙ x)ᗮ`.
* `TauCeti.orthonormalBasisOrthogonalOfSkewFamily`: when `finrank ℝ E = card ι + 1`, this family
  is an `OrthonormalBasis ι ℝ (ℝ ∙ x)ᗮ`.
* `TauCeti.exists_ne_zero_apply_eq_zero_of_skew_of_odd_finrank`: a skew-symmetric linear map of an
  odd-dimensional space has a nonzero kernel vector.
* `OrthonormalBasis.sum_smul_apply_eq_neg_sum_smul`: a skew-symmetric linear map `A` moves across
  a sum over an orthonormal basis, `∑ₖ G(bₖ) • Φ(A bₖ) = -∑ₖ G(A bₖ) • Φ(bₖ)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A skew-symmetric map on a real inner product space sends every vector to an orthogonal vector:
`⟪f x, x⟫ = 0`. -/
theorem inner_apply_self_eq_zero_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    ⟪f x, x⟫_ℝ = 0 := by
  have h₁ := hf x x
  have h₂ := real_inner_comm x (f x)
  linarith

/-- A skew-symmetric map on a real inner product space satisfies `⟪x, f x⟫ = 0`. -/
theorem inner_self_apply_eq_zero_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    ⟪x, f x⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_apply_self_eq_zero_of_skew hf]

/-- For a skew-symmetric map `f` on a real inner product space, `f x` lies in `(ℝ ∙ x)ᗮ`. -/
theorem mem_orthogonal_span_singleton_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    f x ∈ (ℝ ∙ x)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_self_apply_eq_zero_of_skew hf x)

/-- For a skew-symmetric map `f` on a real inner product space, `‖f x‖ ^ 2 = -⟪x, f (f x)⟫`. -/
theorem norm_sq_apply_of_skew {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (x : E) :
    ‖f x‖ ^ 2 = -⟪x, f (f x)⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, hf]

/-- A skew-symmetric map satisfying `f (f y) = -y` preserves the inner product. -/
theorem inner_apply_apply_of_skew_of_sq_neg_id {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hsq : ∀ x, f (f x) = -x) (x y : E) :
    ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [hf, hsq, inner_neg_right, neg_neg]

/-- A skew-symmetric map satisfying `f (f x) = -x` preserves norms. -/
theorem norm_apply_of_skew_of_sq_neg_id {f : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hsq : ∀ x, f (f x) = -x) (x : E) :
    ‖f x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    inner_apply_apply_of_skew_of_sq_neg_id hf hsq]

/-- A skew-symmetric linear map of a real inner product space of odd finite dimension has a
nonzero kernel vector. -/
theorem exists_ne_zero_apply_eq_zero_of_skew_of_odd_finrank [FiniteDimensional ℝ E]
    {f : E →ₗ[ℝ] E} (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hodd : Odd (finrank ℝ E)) :
    ∃ x, x ≠ 0 ∧ f x = 0 := by
  by_contra! hker
  have hinj (x : E) (hx : f x = 0) : x = 0 := by_contra fun h ↦ hker x h hx
  -- The form `x, y ↦ ⟪f x, y⟫` is alternating, and nondegenerate since `f` is injective, so
  -- the dimension would be even.
  let B : LinearMap.BilinForm ℝ E := (innerₗ E).comp f
  have hB : B.IsAlt := inner_apply_self_eq_zero_of_skew hf
  have hnd : B.Nondegenerate := by
    refine ⟨fun x hx ↦ hinj x ?_, fun y hy ↦ hinj y ?_⟩
    · simpa [B] using hx (f x)
    · simpa [B, hf] using hy (f y)
  exact Nat.not_even_iff_odd.mpr hodd (hB.even_finrank hnd)

/-- Two anticommuting skew-symmetric maps on a real inner product space take orthogonal values at
every vector `x`. -/
theorem inner_apply_apply_eq_zero_of_skew_anticommute {f g : E → E}
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = -⟪x, f y⟫_ℝ) (hg : ∀ x y, ⟪g x, y⟫_ℝ = -⟪x, g y⟫_ℝ)
    (hanti : ∀ x, f (g x) + g (f x) = 0) (x : E) :
    ⟪f x, g x⟫_ℝ = 0 := by
  have h₁ := hf x (g x)
  have h₂ := hg (f x) x
  have h₃ := real_inner_comm (g (f x)) x
  have hsum : ⟪x, f (g x)⟫_ℝ + ⟪x, g (f x)⟫_ℝ = 0 := by
    rw [← inner_add_right, hanti x, inner_zero_right]
  linarith

/-- Evaluating a family of pairwise anticommuting skew-symmetric maps squaring to `-1` at a unit
vector produces an orthonormal family in `E`. -/
theorem orthonormal_apply_of_skew_anticommute {ι : Type*} {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ (fun i ↦ A i x) :=
  ⟨fun i ↦ (norm_apply_of_skew_of_sq_neg_id (hskew i) (hsq i) x).trans hx,
    fun {i j} hij ↦ inner_apply_apply_eq_zero_of_skew_anticommute (hskew i) (hskew j)
      (hanti i j hij) x⟩

/-- Evaluating a family of pairwise anticommuting skew-symmetric maps squaring to `-1` at a unit
vector `x` produces an orthonormal family in `(ℝ ∙ x)ᗮ`. -/
theorem orthonormal_orthogonal_of_skew_anticommute {ι : Type*} {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ
      (fun i ↦ (⟨A i x, mem_orthogonal_span_singleton_of_skew (hskew i) x⟩ : (ℝ ∙ x)ᗮ)) :=
  (orthonormal_apply_of_skew_anticommute hskew hsq hanti hx).codRestrict (ℝ ∙ x)ᗮ fun i ↦
    mem_orthogonal_span_singleton_of_skew (hskew i) x

/-- When `finrank ℝ E = card ι + 1`, a family of `card ι` pairwise anticommuting skew-symmetric
maps squaring to `-1` evaluates at each unit vector `x` to an orthonormal basis of `(ℝ ∙ x)ᗮ`. -/
noncomputable def orthonormalBasisOrthogonalOfSkewFamily {ι : Type*} [Fintype ι]
    {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (hrank : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) :
    OrthonormalBasis ι ℝ (ℝ ∙ x)ᗮ := by
  have : FiniteDimensional ℝ E :=
    FiniteDimensional.of_finrank_pos (by rw [hrank]; exact Nat.succ_pos _)
  let : Fact (finrank ℝ E = Fintype.card ι + 1) := ⟨hrank⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
  have hcard : Fintype.card ι = finrank ℝ (ℝ ∙ x)ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) hx0).symm
  let v : ι → (ℝ ∙ x)ᗮ := fun i ↦ ⟨A i x, mem_orthogonal_span_singleton_of_skew (hskew i) x⟩
  have hv : Orthonormal ℝ v := orthonormal_orthogonal_of_skew_anticommute hskew hsq hanti hx
  exact (basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent hcard).toOrthonormalBasis
    (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv)

/-- Each vector of `TauCeti.orthonormalBasisOrthogonalOfSkewFamily` coerces in `E` to `A i x`. -/
@[simp]
theorem coe_orthonormalBasisOrthogonalOfSkewFamily_apply {ι : Type*} [Fintype ι]
    {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (hrank : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (i : ι) :
    ((orthonormalBasisOrthogonalOfSkewFamily hskew hsq hanti hrank hx i : (ℝ ∙ x)ᗮ) : E) =
      A i x := by
  simp [orthonormalBasisOrthogonalOfSkewFamily]

/-- Coordinates in `TauCeti.orthonormalBasisOrthogonalOfSkewFamily` are inner products against
`A i x` in the ambient space `E`. -/
@[simp]
theorem orthonormalBasisOrthogonalOfSkewFamily_repr_apply {ι : Type*} [Fintype ι]
    {A : ι → E → E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (hrank : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (v : (ℝ ∙ x)ᗮ) (i : ι) :
    (orthonormalBasisOrthogonalOfSkewFamily hskew hsq hanti hrank hx).repr v i =
      ⟪A i x, (v : E)⟫_ℝ := by
  rw [OrthonormalBasis.repr_apply_apply, Submodule.coe_inner,
    coe_orthonormalBasisOrthogonalOfSkewFamily_apply]

end TauCeti

namespace OrthonormalBasis

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddCommGroup W] [Module ℝ W]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- **Moving a skew-symmetric map across a sum over an orthonormal basis.** For a skew-symmetric
linear map `A`, an orthonormal basis `(bₖ)` and linear maps `G` and `Φ`,
`∑ₖ G(bₖ) • Φ(A bₖ) = -∑ₖ G(A bₖ) • Φ(bₖ)`. -/
theorem sum_smul_apply_eq_neg_sum_smul {A : E →ₗ[ℝ] E}
    (hA : ∀ u w, ⟪A u, w⟫_ℝ = -⟪u, A w⟫_ℝ) (G : E →ₗ[ℝ] ℝ) (Φ : E →ₗ[ℝ] W) :
    ∑ k, G (b k) • Φ (A (b k)) = -∑ k, G (A (b k)) • Φ (b k) := by
  have hrow (j : ι) : ∑ k, ⟪b j, A (b k)⟫_ℝ • b k = -A (b j) := by
    conv_rhs => rw [← b.sum_repr' (A (b j))]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [real_inner_comm, hA, neg_smul]
  calc ∑ k, G (b k) • Φ (A (b k))
      = ∑ k, ∑ j, (⟪b j, A (b k)⟫_ℝ * G (b k)) • Φ (b j) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        conv_lhs => rw [← b.sum_repr' (A (b k))]
        simp [map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
    _ = ∑ j, G (∑ k, ⟪b j, A (b k)⟫_ℝ • b k) • Φ (b j) := by
        rw [Finset.sum_comm]
        simp [map_sum, map_smul, Finset.sum_smul]
    _ = -∑ k, G (A (b k)) • Φ (b k) := by
        simp [hrow, ← Finset.sum_neg_distrib]

end OrthonormalBasis
