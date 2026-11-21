/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal coordinates

This module describes coordinates in an orthonormal basis of an inner product space over
`𝕜 = ℝ` or `ℂ`: coordinates adapted to a given vector, and rotated real coordinates in a complex
inner product space.

For an orthonormal basis `b`, the `i`-th coordinate functional of the underlying basis is the
inner product with `b i`.

In a finite-dimensional inner product space, an orthonormal coordinate system can be chosen so
that the inner product with a given vector is its norm times any prescribed coordinate.

For an orthonormal basis `b` of a complex inner product space `E`, indexed by a finite type `ι`,
and complex scalars `ω j` of modulus one, the real and imaginary parts of the rotated
coordinates `conj (ω j) ⟪b j, v⟫` are real coordinates on `E`: they form a real linear
equivalence `E ≃ₗ[ℝ] (ι ⊕ ι → ℝ)`.
Rotating each coordinate so that `c j ω j²` is real diagonalizes the real quadratic form
`Re (∑ⱼ c j ⟪b j, v⟫²)` in these real coordinates.

## Main definitions

* `OrthonormalBasis.rotatedRealCoords`: the real and imaginary parts of the rotated coordinates
  `conj (ω j) ⟪b j, v⟫`, as a real linear equivalence `E ≃ₗ[ℝ] (ι ⊕ ι → ℝ)`.

## Main statements

* `OrthonormalBasis.toBasis_coord`: the coordinate functional `b.toBasis.coord i` is
  `innerₛₗ 𝕜 (b i)`.
* `OrthonormalBasis.toLinearMapₛₗ₂_one_eq_innerₛₗ`: the sesquilinear form making `b.toBasis`
  orthonormal is `innerₛₗ 𝕜`.
* `OrthonormalBasis.exists_clm_norm_le_one_and_repr_eq`: each coordinate of a real orthonormal
  basis is a complex-valued continuous real-linear form of norm at most one.
* `OrthonormalBasis.subsingleton_of_isEmpty`: a space with an orthonormal basis indexed by an
  empty type is trivial.
* `OrthonormalBasis.repr_apply_of_eigenbasis`: in an orthonormal eigenbasis of a linear map `S`,
  the coordinates of `S x` are those of `x` scaled by the eigenvalues.
* `OrthonormalBasis.toBasis_equiv_refl`: for two finite orthonormal bases over the same index type,
  `Basis.equiv` along `Equiv.refl` agrees with `d₀.repr.trans c.repr.symm`.
* `OrthonormalBasis.map_sum_smul`: a linear map applied to `∑ i, c i • b i`, expanded in `b`.
* `TauCeti.exists_linearIsometryEquiv_inner_eq_norm_mul_eval`: for a vector `v` and a prescribed
  coordinate `i`, there is a linear isometry equivalence `f` with
  `⟪v, x⟫ = ‖v‖ * f x i` for all `x`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- Choose orthonormal coordinates in which the inner product with `v` is its norm times the
prescribed coordinate. This also holds for `v = 0`. For `v ≠ 0` the coordinates are those of an
orthonormal basis whose `i`-th vector is `‖v‖⁻¹ • v`, obtained by extending this unit vector with
Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`. -/
theorem exists_linearIsometryEquiv_inner_eq_norm_mul_eval {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v : E) (i : Fin (Module.finrank 𝕜 E)) :
    ∃ f : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E)),
      ∀ x, ⟪v, x⟫_𝕜 = ‖v‖ * f x i := by
  -- In infinite dimension `finrank = 0`, so there is no coordinate `i`.
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by
    have := i.isLt
    omega)
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨(stdOrthonormalBasis 𝕜 E).repr, by simp⟩
  -- Extend the unit vector `‖v‖⁻¹ • v` to an orthonormal basis whose `i`-th vector it is.
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (Fintype.card_fin _).symm (v := fun _ ↦ (‖v‖⁻¹ : 𝕜) • v) (s := {i})
    (orthonormal_subsingleton_iff.mpr fun _ ↦ norm_smul_inv_norm (𝕜 := 𝕜) hv)
  refine ⟨b.repr, fun x ↦ ?_⟩
  rw [b.repr_apply_apply, hb i (Set.mem_singleton i), inner_smul_left, ← mul_assoc]
  simp [hv]

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

/-- The sesquilinear form making the underlying basis of an orthonormal basis orthonormal is the
inner product `innerₛₗ 𝕜`. -/
@[simp]
theorem toLinearMapₛₗ₂_one_eq_innerₛₗ [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) :
    Matrix.toLinearMapₛₗ₂ (starRingEnd 𝕜) b.toBasis b.toBasis (1 : Matrix ι ι 𝕜) =
      innerₛₗ 𝕜 := by
  refine LinearMap.ext_basis b.toBasis b.toBasis fun i j ↦ ?_
  rw [Matrix.toLinearMapₛₗ₂_apply_basis, Matrix.one_apply, innerₛₗ_apply_apply, b.coe_toBasis,
    orthonormal_iff_ite.mp b.orthonormal i j]

/-- The `i`-th coordinate `y ↦ bᵢ(y)` of a real orthonormal basis, as a complex-valued continuous
real-linear form of norm at most one. -/
theorem exists_clm_norm_le_one_and_repr_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (b : OrthonormalBasis ι ℝ F) (i : ι) :
    ∃ A : F →L[ℝ] ℂ, ‖A‖ ≤ 1 ∧ ∀ y, ((b.toBasis.repr y i : ℝ) : ℂ) = A y := by
  refine ⟨Complex.ofRealCLM.comp (innerSL ℝ (b i)), ?_, fun y ↦ by simp [b.repr_apply_apply]⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ ?_
  simpa [b.orthonormal.1 i] using norm_inner_le_norm (𝕜 := ℝ) (b i) y

/-- The space carrying an orthonormal basis indexed by an empty type is trivial. -/
theorem subsingleton_of_isEmpty [IsEmpty ι] (b : OrthonormalBasis ι 𝕜 E) : Subsingleton E :=
  b.repr.toEquiv.subsingleton

/-- The coordinates of `S x` in an orthonormal eigenbasis of `S` are the coordinates of `x`
scaled by the eigenvalues. -/
theorem repr_apply_of_eigenbasis (b : OrthonormalBasis ι 𝕜 E) (S : E →ₗ[𝕜] E) {μ : ι → 𝕜}
    (hb : ∀ i, S (b i) = μ i • b i) (x : E) (i : ι) :
    b.repr (S x) i = μ i * b.repr x i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp [map_sum, hb, smul_smul, mul_comm, Pi.single_apply]

/-- For two orthonormal bases indexed by the same finite type, the algebraic `Basis.equiv` along
`Equiv.refl ι` coincides with `d₀.repr.trans c.repr.symm`. -/
theorem toBasis_equiv_refl {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (d₀ : OrthonormalBasis ι 𝕜 E) (c : OrthonormalBasis ι 𝕜 F) :
    d₀.toBasis.equiv c.toBasis (Equiv.refl ι) = (d₀.repr.trans c.repr.symm).toLinearEquiv := by
  classical
  refine LinearEquiv.toLinearMap_injective (d₀.toBasis.ext fun i ↦ ?_)
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  simp

/-- A linear map applied to a combination of an orthonormal basis, expanded in the same basis:
the new coefficients are those of `c` transformed by the matrix of `f` in `b`. -/
theorem map_sum_smul {F : Type*} [FunLike F E E] [LinearMapClass F 𝕜 E E]
    (b : OrthonormalBasis ι 𝕜 E) (f : F) (c : ι → 𝕜) :
    f (∑ i, c i • b i) = ∑ i, (∑ j, b.repr (f (b j)) i * c j) • b i := by
  simp_rw [map_sum, map_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp_rw [mul_comm _ (c j), mul_smul, ← Finset.smul_sum, OrthonormalBasis.sum_repr]

end OrthonormalBasis

open Complex ComplexConjugate

namespace OrthonormalBasis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- The real and imaginary parts of the coordinates `conj (ω j) ⟪b j, v⟫` in an orthonormal
basis `b`, rotated by complex scalars `ω j` of modulus one, as a real linear equivalence. -/
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
