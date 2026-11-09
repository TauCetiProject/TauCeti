/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Orthonormal coordinates

This module describes coordinates adapted to a vector in a real inner product space and
rotated coordinates in a complex inner product space.

For an orthonormal basis `b`, the `i`-th coordinate functional of the underlying basis is the
inner product with `b i`.

In a finite-dimensional real inner product space, an orthonormal coordinate system can be
chosen so that the inner product with a given vector is its norm times any prescribed coordinate.

For an orthonormal basis `b` of a complex inner product space `E`, indexed by a finite type `ι`,
every `v : E` has the complex coordinates `⟪b j, v⟫`:

* Each holomorphic quadratic form `∑ⱼ c j ⟪b j, v⟫²` in these coordinates is `v ↦ Q v v` for a
  continuous complex bilinear form `Q`.
* For units `ω j`, the real and imaginary parts of the rotated coordinates `conj (ω j) ⟪b j, v⟫`
  are real coordinates on `E`: they form a real linear equivalence `E ≃ₗ[ℝ] (ι ⊕ ι → ℝ)`.
  Rotating each coordinate so that `c j ω j²` is real diagonalizes the real quadratic form
  `Re (∑ⱼ c j ⟪b j, v⟫²)` in these real coordinates.

## Main definitions

* `OrthonormalBasis.rotatedRealCoords`: the real and imaginary parts of the rotated coordinates
  `conj (ω j) ⟪b j, v⟫`, as a real linear equivalence `E ≃ₗ[ℝ] (ι ⊕ ι → ℝ)`.

## Main statements

* `OrthonormalBasis.toBasis_coord`: the coordinate functional `b.toBasis.coord i` is
  `innerₛₗ 𝕜 (b i)`.
* `OrthonormalBasis.repr_apply_of_eigenbasis`: in an orthonormal eigenbasis of a linear map `S`,
  the coordinates of `S x` are those of `x` scaled by the eigenvalues.
* `TauCeti.exists_linearIsometryEquiv_inner_eq_norm_mul_eval`: for a vector `v` and a prescribed
  coordinate `i`, there is a linear isometry equivalence `f` with
  `⟪v, x⟫ = ‖v‖ * f x i` for all `x`.
* `OrthonormalBasis.exists_apply_self_eq_sum_mul_inner_sq`: `∑ⱼ c j ⟪b j, v⟫²` is `Q v v` for a
  continuous complex bilinear form `Q`.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace

/-- Choose orthonormal coordinates in which the inner product with `v` is its norm times the
prescribed coordinate. This also holds for `v = 0`. -/
theorem exists_linearIsometryEquiv_inner_eq_norm_mul_eval {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (v : E) (i : Fin (Module.finrank ℝ E)) :
    ∃ f : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      ∀ x, ⟪v, x⟫ = ‖v‖ * f x i := by
  let g := (stdOrthonormalBasis ℝ E).repr
  let w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := ‖v‖ • EuclideanSpace.single i 1
  have hnorm : ‖g v‖ = ‖w‖ := by simp [w, g, norm_smul]
  let f := g.trans (Submodule.reflection (ℝ ∙ (g v - w))ᗮ)
  have hfv : f v = w := Submodule.reflection_sub hnorm
  refine ⟨f, fun x ↦ ?_⟩
  rw [← f.inner_map_map, hfv]
  simp [w, real_inner_smul_left, EuclideanSpace.inner_single_left]

end TauCeti

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- The `i`-th coordinate functional of an orthonormal basis is the inner product with its
`i`-th vector. -/
@[simp]
theorem toBasis_coord (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.toBasis.coord i = innerₛₗ 𝕜 (b i) :=
  LinearMap.ext fun v ↦ (b.coe_toBasis_repr_apply v i).trans (b.repr_apply_apply v i)

/-- The coordinate functional of a real orthonormal basis, expressed using the real bilinear
inner product. -/
theorem toBasis_coord_real {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ F) (i : ι) :
    b.toBasis.coord i = innerₗ F (b i) := by
  ext v
  simp only [toBasis_coord, innerₛₗ_apply_apply, innerₗ_apply_apply]

/-- The coordinates of `S x` in an orthonormal eigenbasis of `S` are the coordinates of `x`
scaled by the eigenvalues. -/
theorem repr_apply_of_eigenbasis (b : OrthonormalBasis ι 𝕜 E) (S : E →ₗ[𝕜] E) {μ : ι → 𝕜}
    (hb : ∀ i, S (b i) = μ i • b i) (x : E) (i : ι) :
    b.repr (S x) i = μ i * b.repr x i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp [map_sum, hb, smul_smul, mul_comm, Pi.single_apply]

end OrthonormalBasis

open Complex ComplexConjugate
open scoped InnerProductSpace

namespace OrthonormalBasis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- The holomorphic quadratic form `∑ⱼ c j ⟪b j, z⟫²` is `z ↦ Q z z` for a continuous complex
bilinear form `Q`. -/
theorem exists_apply_self_eq_sum_mul_inner_sq (b : OrthonormalBasis ι ℂ E) (c : ι → ℂ) :
    ∃ Q : E →L[ℂ] E →L[ℂ] ℂ, ∀ v, Q v v = ∑ j, c j * ⟪b j, v⟫_ℂ ^ 2 :=
  ⟨∑ j, c j • (ContinuousLinearMap.mul ℂ ℂ).bilinearComp (innerSL ℂ (b j)) (innerSL ℂ (b j)),
    fun v ↦ by simp [sq]⟩

/-- The real and imaginary parts of the coordinates `conj (ω j) ⟪b j, v⟫` in an orthonormal
basis `b`, rotated by units `ω j`, as a real linear equivalence. -/
noncomputable def rotatedRealCoords (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) : E ≃ₗ[ℝ] (ι ⊕ ι → ℝ) where
  toFun v := Sum.elim (fun j ↦ (conj (ω j) * ⟪b j, v⟫_ℂ).re) (fun j ↦ (conj (ω j) * ⟪b j, v⟫_ℂ).im)
  invFun u := ∑ j, (ω j * ⟨u (Sum.inl j), u (Sum.inr j)⟩) • b j
  map_add' v w := by ext (j | j) <;> simp [inner_add_right, mul_add]
  map_smul' r v := by
    ext (j | j) <;> simp [← coe_smul, inner_smul_right, mul_left_comm _ (r : ℂ)]
  left_inv v := by
    conv_rhs => rw [← b.sum_repr' v]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.eta, ← mul_assoc, hω, one_mul]
  right_inv u := by
    have hk (k : ι) : conj (ω k) * ⟪b k, ∑ j, (ω j * ⟨u (Sum.inl j), u (Sum.inr j)⟩) • b j⟫_ℂ =
        ⟨u (Sum.inl k), u (Sum.inr k)⟩ := by
      rw [b.orthonormal.inner_right_fintype, ← mul_assoc, mul_comm (conj _), hω, one_mul]
    ext (j | j) <;> simp only [hk, Sum.elim_inl, Sum.elim_inr]

/-- The `Sum.inl j` coordinate of `rotatedRealCoords` is the real part of
`conj (ω j) ⟪b j, v⟫`. -/
@[simp]
theorem rotatedRealCoords_apply_inl (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) (v : E) (j : ι) :
    b.rotatedRealCoords ω hω v (Sum.inl j) = (conj (ω j) * ⟪b j, v⟫_ℂ).re := by
  rfl

/-- The `Sum.inr j` coordinate of `rotatedRealCoords` is the imaginary part of
`conj (ω j) ⟪b j, v⟫`. -/
@[simp]
theorem rotatedRealCoords_apply_inr (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) (v : E) (j : ι) :
    b.rotatedRealCoords ω hω v (Sum.inr j) = (conj (ω j) * ⟪b j, v⟫_ℂ).im := by
  rfl

/-- The inverse of `rotatedRealCoords` sends real coordinates `u` to the vector whose rotated
coordinate `conj (ω j) ⟪b j, v⟫` is `u (Sum.inl j) + u (Sum.inr j) i`. -/
@[simp]
theorem rotatedRealCoords_symm_apply (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) (u : ι ⊕ ι → ℝ) :
    (b.rotatedRealCoords ω hω).symm u = ∑ j, (ω j * ⟨u (Sum.inl j), u (Sum.inr j)⟩) • b j := by
  rfl

end OrthonormalBasis
