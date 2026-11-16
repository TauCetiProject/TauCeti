/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Inversion
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic

/-!
# Orthogonal-sphere inversions, homogeneity, and the Cayley isometry of the Poincaré ball

For any real inner product space `E`, every Euclidean sphere centred at `c : E` with `1 < ‖c‖` and
radius `√(‖c‖² - 1)` meets the unit sphere `‖x‖ = 1` orthogonally. Euclidean inversion in this
sphere preserves the open unit ball `{x : E | ‖x‖ < 1}` and scales `1 - ‖x‖²` by the same factor
`(√(‖c‖² - 1) / dist x c)²` by which its differential scales tangent vectors. Hence it restricts to
an involutive Riemannian isometry `PoincareBall.inversion` of `PoincareBall E` (hyperbolic
reflection in the totally geodesic hypersurface cut out by the orthogonal sphere).

Specialising `c = ‖a‖⁻² • a` for a nonzero point `a : PoincareBall E` produces an involutive
Riemannian isometry `PoincareBall.inversionSwapZero` exchanging `0` and `a`. Consequently, the
Riemannian isometry group `Isom 𝓘(ℝ, E) (PoincareBall E)` acts transitively on `PoincareBall E` in
every real inner product space, finite- or infinite-dimensional.

Finally, in the Euclidean product `WithLp 2 (E × ℝ)`, Euclidean inversion in the sphere of radius
`√2` centred at `(0, -1)` carries the open upper half-space `UpperHalfSpace E` bijectively onto
`PoincareBall (WithLp 2 (E × ℝ))`, sending `(0, 1)` to `0` and pulling back the Poincaré ball
metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²` to the upper-half-space metric `(‖dx‖² + dt²) / t²`. This defines
the canonical Cayley Riemannian isometry `PoincareBall.cayleyIsometry`.

## Main definitions

* `TauCeti.PoincareBall.inversion`: hyperbolic reflection in the orthogonal sphere of centre `c`
  (`1 < ‖c‖`) and radius `√(‖c‖² - 1)`.
* `TauCeti.PoincareBall.inversionSwapZero`: the involutive Riemannian isometry exchanging `0` and a
  nonzero point `a : PoincareBall E`.
* `TauCeti.PoincareBall.cayleyIsometry`: the Cayley Riemannian isometry from `UpperHalfSpace E` onto
  `PoincareBall (WithLp 2 (E × ℝ))`.

## Main results

* `TauCeti.PoincareBall.inversion_mul_self`: orthogonal-sphere inversions are involutions.
* `TauCeti.PoincareBall.inversionSwapZero_zero`, `TauCeti.PoincareBall.inversionSwapZero_self`, and
  `TauCeti.PoincareBall.norm_coe_inversionSwapZero`: `inversionSwapZero ha` exchanges `0` and `a`
  and computes the resulting Euclidean radius from `0`.
* `TauCeti.PoincareBall.isPretransitive_isom`: `Isom 𝓘(ℝ, E) (PoincareBall E)` acts transitively on
  `PoincareBall E`.
* `TauCeti.PoincareBall.cayleyIsometry_mk_zero_one` and
  `TauCeti.PoincareBall.cayleyIsometry_symm_zero`: `cayleyIsometry` exchanges `(0, 1)` and `0`.

## References

* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019), §4.5
  (reflections and homogeneity of the conformal ball model, and the Cayley inversion between the
  upper half-space and ball models).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (Proposition 3.5 and Theorem 3.7).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.PoincareBall

section Inversion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem norm_sq_sub_one_pos {c : E} (hc : 1 < ‖c‖) : 0 < ‖c‖ ^ 2 - 1 := by
  nlinarith

omit [InnerProductSpace ℝ E] in
private theorem sqrt_norm_sq_sub_one_pos {c : E} (hc : 1 < ‖c‖) :
    0 < Real.sqrt (‖c‖ ^ 2 - 1) :=
  Real.sqrt_pos.2 (norm_sq_sub_one_pos hc)

omit [InnerProductSpace ℝ E] in
private theorem coe_ne_center {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    (x : E) ≠ c := fun h ↦
  ((norm_lt_one x).trans hc).ne (congrArg norm h)

/-- Squared Euclidean norm of sphere inversion: for `y : E`,
`‖inversion c R y‖² = (R / dist y c)⁴ ‖y - c‖² + 2 (R / dist y c)² ⟪y - c, c⟫ + ‖c‖²`. -/
private theorem norm_inversion_sq (c : E) (R : ℝ) (y : E) :
    ‖EuclideanGeometry.inversion c R y‖ ^ 2 =
      ((R / dist y c) ^ 2) ^ 2 * ‖y - c‖ ^ 2 +
        2 * (R / dist y c) ^ 2 * inner ℝ (y - c) c + ‖c‖ ^ 2 := by
  simp only [EuclideanGeometry.inversion_def, vsub_eq_sub, vadd_eq_add]
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left]
  ring

/-- Key conformal identity for orthogonal-sphere inversion: if `R² = ‖c‖² - 1` and `y ≠ c`, then
`1 - ‖inversion c R y‖² = (R / dist y c)² (1 - ‖y‖²)`. -/
private theorem one_sub_norm_inversion_sq {c y : E} (hc : 1 < ‖c‖) (hy : y ≠ c) :
    1 - ‖EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) y‖ ^ 2 =
      (Real.sqrt (‖c‖ ^ 2 - 1) / dist y c) ^ 2 * (1 - ‖y‖ ^ 2) := by
  set R : ℝ := Real.sqrt (‖c‖ ^ 2 - 1)
  have hRsq : R ^ 2 = ‖c‖ ^ 2 - 1 := Real.sq_sqrt (norm_sq_sub_one_pos hc).le
  have hd : dist y c ≠ 0 := dist_ne_zero.2 hy
  set t : ℝ := (R / dist y c) ^ 2
  have ht_mul : t * ‖y - c‖ ^ 2 = ‖c‖ ^ 2 - 1 := by
    dsimp only [t]
    rw [← dist_eq_norm, div_pow, hRsq]
    field_simp [hd]
  have hsub : ‖y - c‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y c + ‖c‖ ^ 2 := norm_sub_sq_real y c
  have hinner : 2 * inner ℝ (y - c) c = ‖y‖ ^ 2 - ‖y - c‖ ^ 2 - ‖c‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    linarith [hsub]
  rw [norm_inversion_sq, sq t, mul_assoc t t, ht_mul]
  linear_combination ht_mul - t * hinner

private def inversionMap {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) : PoincareBall E :=
  mk (EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E)) <| by
    have hpos : 0 < 1 - ‖EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E)‖ ^ 2 := by
      rw [one_sub_norm_inversion_sq hc (coe_ne_center hc x)]
      exact mul_pos (pow_pos (div_pos (sqrt_norm_sq_sub_one_pos hc)
        (dist_pos.2 (coe_ne_center hc x))) 2) (one_sub_norm_sq_pos x)
    nlinarith [norm_nonneg (EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E))]

private theorem coe_inversionMap {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    (inversionMap hc x : E) = EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E) :=
  coe_mk _ _

private theorem coe_comp_inversionMap {c : E} (hc : 1 < ‖c‖) :
    coe ∘ inversionMap hc = EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) ∘ coe :=
  funext (coe_inversionMap hc)

private theorem inversionMap_inversionMap {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    inversionMap hc (inversionMap hc x) = x :=
  ext <| by
    rw [coe_inversionMap, coe_inversionMap,
      EuclideanGeometry.inversion_inversion _ (sqrt_norm_sq_sub_one_pos hc).ne']

private theorem contMDiff_inversionMap {n : ℕ∞ω} {c : E} (hc : 1 < ‖c‖) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (inversionMap hc) := by
  refine contMDiff_coe_comp_iff.1 fun x ↦ ?_
  rw [coe_comp_inversionMap]
  exact (EuclideanGeometry.contDiffAt_inversion (coe_ne_center hc x)).contMDiffAt.comp x
    (contMDiff_coe.of_le le_top x)

private theorem tangentSpaceCastModel_mfderiv_inversionMap {c : E} (hc : 1 < ‖c‖)
    (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    tangentSpaceCastModel 𝓘(ℝ, E) (inversionMap hc x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (inversionMap hc) x v) =
      fderiv ℝ (EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1))) (x : E)
        (tangentSpaceCastModel 𝓘(ℝ, E) x v) := by
  have hf := EuclideanGeometry.hasFDerivAt_inversion (R := Real.sqrt (‖c‖ ^ 2 - 1))
    (coe_ne_center hc x)
  rw [hf.fderiv]
  exact tangentSpaceCastModel_mfderiv_apply hf (coe_comp_inversionMap hc) v

private def inversionDiffeomorph {c : E} (hc : 1 < ‖c‖) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (PoincareBall E) (PoincareBall E) ∞ where
  toFun := inversionMap hc
  invFun := inversionMap hc
  left_inv := inversionMap_inversionMap hc
  right_inv := inversionMap_inversionMap hc
  contMDiff_toFun := contMDiff_inversionMap hc
  contMDiff_invFun := contMDiff_inversionMap hc

private theorem coe_inversionDiffeomorph {c : E} (hc : 1 < ‖c‖) :
    ⇑(inversionDiffeomorph hc) = inversionMap hc :=
  (rfl)

/-- Euclidean inversion in the sphere centred at `c` (`1 < ‖c‖`) of radius `√(‖c‖² - 1)` restricts
to an involutive Riemannian isometry of `PoincareBall E`. Geometrically, this is hyperbolic
reflection across the totally geodesic hypersurface cut out by the orthogonal sphere. -/
def inversion {c : E} (hc : 1 < ‖c‖) : Isom 𝓘(ℝ, E) (PoincareBall E) where
  toDiffeomorph := inversionDiffeomorph hc
  inner_mfderiv' x v w := by
    rw [coe_inversionDiffeomorph, inner_def, inner_def,
      tangentSpaceCastModel_mfderiv_inversionMap, tangentSpaceCastModel_mfderiv_inversionMap,
      EuclideanGeometry.inner_fderiv_inversion, coe_inversionMap,
      one_sub_norm_inversion_sq hc (coe_ne_center hc x)]
    have hR : Real.sqrt (‖c‖ ^ 2 - 1) ≠ 0 := (sqrt_norm_sq_sub_one_pos hc).ne'
    have hd : dist (x : E) c ≠ 0 := dist_ne_zero.2 (coe_ne_center hc x)
    have hden : 1 - ‖(x : E)‖ ^ 2 ≠ 0 := (one_sub_norm_sq_pos x).ne'
    field_simp [hR, hd, hden]

private theorem coe_inversion {c : E} (hc : 1 < ‖c‖) :
    ⇑(inversion hc) = inversionMap hc :=
  (rfl)

@[simp]
theorem coe_inversion_apply {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    (inversion hc x : E) = EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E) :=
  coe_inversionMap hc x

/-- Orthogonal-sphere inversions are involutions in the Riemannian isometry group. -/
@[simp]
theorem inversion_mul_self {c : E} (hc : 1 < ‖c‖) :
    inversion hc * inversion hc = 1 :=
  RiemannianIsometry.ext fun x ↦ by
    rw [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply, coe_inversion,
      inversionMap_inversionMap]

@[simp]
theorem inversion_inv {c : E} (hc : 1 < ‖c‖) :
    (inversion hc)⁻¹ = inversion hc :=
  inv_eq_iff_mul_eq_one.2 (inversion_mul_self hc)

/-- The differential of `inversion hc` acts on the model space by `(R / dist x c)²` composed with
reflection across the hyperplane orthogonal to `x - c`. -/
theorem tangentSpaceCastModel_mfderiv_inversion {c : E} (hc : 1 < ‖c‖)
    (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    tangentSpaceCastModel 𝓘(ℝ, E) (inversion hc x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (inversion hc) x v) =
      (Real.sqrt (‖c‖ ^ 2 - 1) / dist (x : E) c) ^ 2 •
        (ℝ ∙ ((x : E) - c))ᗮ.reflection (tangentSpaceCastModel 𝓘(ℝ, E) x v) := by
  rw [coe_inversion]
  exact tangentSpaceCastModel_mfderiv_apply
    (EuclideanGeometry.hasFDerivAt_inversion (coe_ne_center hc x)) (coe_comp_inversionMap hc) v

/-! ### Origin-swapping inversions and transitivity -/

omit [InnerProductSpace ℝ E] in
private theorem one_lt_norm_inv_sq_smul [NormedSpace ℝ E] {a : PoincareBall E} (ha : a ≠ 0) :
    1 < ‖(‖(a : E)‖ ^ 2)⁻¹ • (a : E)‖ := by
  have ha0 : 0 < ‖(a : E)‖ := norm_pos_iff.2 (coe_eq_zero.not.2 ha)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
  have hsimp : (‖(a : E)‖ ^ 2)⁻¹ * ‖(a : E)‖ = ‖(a : E)‖⁻¹ := by
    field_simp [ha0.ne']
  rw [hsimp]
  exact (one_lt_inv₀ ha0).2 (norm_lt_one a)

/-- For a nonzero point `a : PoincareBall E`, the orthogonal-sphere inversion centred at
`‖a‖⁻² • a` is an involutive Riemannian isometry of `PoincareBall E` exchanging `0` and `a`. -/
def inversionSwapZero {a : PoincareBall E} (ha : a ≠ 0) : Isom 𝓘(ℝ, E) (PoincareBall E) :=
  inversion (one_lt_norm_inv_sq_smul ha)

/-- Coordinate formula for `inversionSwapZero ha` as Euclidean inversion in the orthogonal sphere
centred at `‖a‖⁻² • a`. -/
theorem coe_inversionSwapZero_apply {a : PoincareBall E} (ha : a ≠ 0) (x : PoincareBall E) :
    (inversionSwapZero ha x : E) =
      EuclideanGeometry.inversion ((‖(a : E)‖ ^ 2)⁻¹ • (a : E))
        (Real.sqrt (‖(‖(a : E)‖ ^ 2)⁻¹ • (a : E)‖ ^ 2 - 1)) (x : E) :=
  coe_inversion_apply _ x

@[simp]
theorem inversionSwapZero_mul_self {a : PoincareBall E} (ha : a ≠ 0) :
    inversionSwapZero ha * inversionSwapZero ha = 1 :=
  inversion_mul_self _

@[simp]
theorem inversionSwapZero_inv {a : PoincareBall E} (ha : a ≠ 0) :
    (inversionSwapZero ha)⁻¹ = inversionSwapZero ha :=
  inversion_inv _

@[simp]
theorem inversionSwapZero_zero {a : PoincareBall E} (ha : a ≠ 0) :
    inversionSwapZero ha 0 = a := by
  ext
  rw [coe_inversionSwapZero_apply, coe_zero]
  set c : E := (‖(a : E)‖ ^ 2)⁻¹ • (a : E)
  have hc : 1 < ‖c‖ := one_lt_norm_inv_sq_smul ha
  have ha0 : ‖(a : E)‖ ≠ 0 := norm_ne_zero_iff.2 (coe_eq_zero.not.2 ha)
  have hc_norm : ‖c‖ = ‖(a : E)‖⁻¹ := by
    simp only [c, norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
    field_simp [ha0]
  have hRsq : Real.sqrt (‖c‖ ^ 2 - 1) ^ 2 = ‖c‖ ^ 2 - 1 :=
    Real.sq_sqrt (norm_sq_sub_one_pos hc).le
  simp only [EuclideanGeometry.inversion_def, vsub_eq_sub, vadd_eq_add]
  rw [dist_zero_left, zero_sub, div_pow, hRsq]
  have hcoef : (‖c‖ ^ 2 - 1) / ‖c‖ ^ 2 = 1 - ‖(a : E)‖ ^ 2 := by
    rw [hc_norm]
    field_simp [ha0]
  rw [hcoef, smul_neg, sub_smul, one_smul]
  have hsmul : ‖(a : E)‖ ^ 2 • c = (a : E) := by
    simp [c, smul_smul, ha0]
  rw [hsmul]
  abel

@[simp]
theorem inversionSwapZero_self {a : PoincareBall E} (ha : a ≠ 0) :
    inversionSwapZero ha a = 0 := by
  have h := congrArg (inversionSwapZero ha) (inversionSwapZero_zero ha)
  rw [← RiemannianIsometry.mul_apply, inversionSwapZero_mul_self, RiemannianIsometry.one_apply] at h
  exact h.symm

/-- For `a ≠ 0`, `inversionSwapZero ha` sends `y` to a point at Euclidean radius
`‖a - y‖ / √(‖a - y‖² + (1 - ‖a‖²)(1 - ‖y‖²))` from the origin. -/
theorem norm_coe_inversionSwapZero {a : PoincareBall E} (ha : a ≠ 0) (y : PoincareBall E) :
    ‖(inversionSwapZero ha y : E)‖ =
      ‖(a : E) - (y : E)‖ /
        Real.sqrt (‖(a : E) - (y : E)‖ ^ 2 + (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)) := by
  set c : E := (‖(a : E)‖ ^ 2)⁻¹ • (a : E)
  have hc : 1 < ‖c‖ := one_lt_norm_inv_sq_smul ha
  have ha0 : ‖(a : E)‖ ≠ 0 := norm_ne_zero_iff.2 (coe_eq_zero.not.2 ha)
  have hc_sq : ‖c‖ ^ 2 = (‖(a : E)‖ ^ 2)⁻¹ := by
    simp only [c, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    field_simp [ha0]
  set D : ℝ := ‖(a : E) - (y : E)‖ ^ 2 + (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)
  have hD_pos : 0 < D :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (one_sub_norm_sq_pos a) (one_sub_norm_sq_pos y))
  have hdist_sq : dist (y : E) c ^ 2 = D / ‖(a : E)‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hc_sq]
    have hinner : inner ℝ (y : E) c = (‖(a : E)‖ ^ 2)⁻¹ * inner ℝ (a : E) (y : E) := by
      rw [real_inner_comm]
      exact real_inner_smul_left _ _ _
    rw [hinner]
    dsimp only [D]
    rw [norm_sub_sq_real]
    field_simp [ha0]
    ring
  have h1 : 1 - ‖(inversionSwapZero ha y : E)‖ ^ 2 =
      (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2) / D := by
    rw [coe_inversionSwapZero_apply, one_sub_norm_inversion_sq hc (coe_ne_center hc y), div_pow,
      Real.sq_sqrt (norm_sq_sub_one_pos hc).le, hc_sq, hdist_sq]
    field_simp [ha0, hD_pos.ne']
  have hsq : ‖(inversionSwapZero ha y : E)‖ ^ 2 = ‖(a : E) - (y : E)‖ ^ 2 / D := by
    have hdiv :
        ‖(a : E) - (y : E)‖ ^ 2 / D + (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2) / D = 1 := by
      rw [← add_div, div_self hD_pos.ne']
    linarith [h1, hdiv]
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- The Riemannian isometry group of `PoincareBall E` acts transitively on `PoincareBall E` in every
real inner product space `E`. -/
instance isPretransitive_isom :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, E) (PoincareBall E)) (PoincareBall E) where
  exists_smul_eq x y := by
    -- Move `x` to `0`, then move `0` to `y`.
    obtain ⟨g₁, hg₁⟩ : ∃ g₁ : Isom 𝓘(ℝ, E) (PoincareBall E), g₁ x = 0 := by
      rcases eq_or_ne x 0 with rfl | hx
      · exact ⟨1, RiemannianIsometry.one_apply 0⟩
      · exact ⟨inversionSwapZero hx, inversionSwapZero_self hx⟩
    obtain ⟨g₂, hg₂⟩ : ∃ g₂ : Isom 𝓘(ℝ, E) (PoincareBall E), g₂ 0 = y := by
      rcases eq_or_ne y 0 with rfl | hy
      · exact ⟨1, RiemannianIsometry.one_apply 0⟩
      · exact ⟨inversionSwapZero hy, inversionSwapZero_zero hy⟩
    refine ⟨g₂ * g₁, ?_⟩
    rw [RiemannianIsometry.smul_def, RiemannianIsometry.mul_apply, hg₁, hg₂]

end Inversion

/-! ### The Cayley Riemannian isometry -/

section Cayley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "P" => WithLp 2 (E × ℝ)

omit [InnerProductSpace ℝ E] in
private theorem upper_ne_cayleyCenter (x : UpperHalfSpace E) :
    (x : P) ≠ WithLp.toLp 2 (0, -1) := fun h ↦ by
  have hsnd := congrArg WithLp.snd h
  simp only [UpperHalfSpace.snd_coe, WithLp.toLp_snd] at hsnd
  linarith [UpperHalfSpace.height_pos x]

private theorem norm_cayleyCenter_sq : ‖(WithLp.toLp 2 ((0 : E), (-1 : ℝ)) : P)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq]
  simp

private theorem dist_cayleyCenter_sq (p : P) :
    dist p (WithLp.toLp 2 (0, -1)) ^ 2 = ‖p‖ ^ 2 + 2 * p.snd + 1 := by
  rw [dist_eq_norm, norm_sub_sq_real, norm_cayleyCenter_sq]
  have hinner : inner ℝ p (WithLp.toLp 2 ((0 : E), (-1 : ℝ))) = -p.snd := by simp
  rw [hinner]
  ring

private theorem ball_ne_cayleyCenter (x : PoincareBall P) :
    (x : P) ≠ WithLp.toLp 2 (0, -1) := fun h ↦ by
  have hnorm : ‖(x : P)‖ ^ 2 = 1 := by rw [h, norm_cayleyCenter_sq]
  linarith [norm_sq_lt_one x]

/-- Identity A: for `p ≠ (0, -1)`, Cayley inversion satisfies
`1 - ‖inversion (0, -1) √2 p‖² = 4 p.snd / dist p (0, -1)²`. -/
private theorem one_sub_norm_cayleyInversion_sq {p : P} (hp : p ≠ WithLp.toLp 2 (0, -1)) :
    1 - ‖EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) p‖ ^ 2 =
      4 * p.snd / dist p (WithLp.toLp 2 (0, -1)) ^ 2 := by
  set c : P := WithLp.toLp 2 (0, -1)
  have hd : dist p c ≠ 0 := dist_ne_zero.2 hp
  set t : ℝ := (Real.sqrt 2 / dist p c) ^ 2
  have ht_eq : t = 2 / dist p c ^ 2 := by
    dsimp only [t]
    rw [div_pow, Real.sq_sqrt zero_le_two]
  have ht_mul : t * ‖p - c‖ ^ 2 = 2 := by
    rw [← dist_eq_norm, ht_eq]
    field_simp [hd]
  have hinner : inner ℝ (p - c) c = -(p.snd + 1) := by simp [c]
  have hc_norm : ‖c‖ ^ 2 = 1 := norm_cayleyCenter_sq
  rw [norm_inversion_sq, hinner, hc_norm, sq t, mul_assoc t t, ht_mul]
  have hlin : 1 - (t * 2 + 2 * t * -(p.snd + 1) + 1) = 2 * t * p.snd := by ring
  rw [hlin, ht_eq]
  ring

/-- Identity B: for `q ≠ (0, -1)`, the vertical coordinate of Cayley inversion is
`(1 - ‖q‖²) / dist q (0, -1)²`. -/
private theorem snd_cayleyInversion {q : P} (hq : q ≠ WithLp.toLp 2 (0, -1)) :
    (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) q).snd =
      (1 - ‖q‖ ^ 2) / dist q (WithLp.toLp 2 (0, -1)) ^ 2 := by
  have hd : dist q (WithLp.toLp 2 (0, -1)) ≠ 0 := dist_ne_zero.2 hq
  simp only [EuclideanGeometry.inversion_def, vsub_eq_sub, vadd_eq_add, div_pow,
    Real.sq_sqrt zero_le_two, WithLp.add_snd, WithLp.smul_snd, WithLp.sub_snd,
    WithLp.toLp_snd, smul_eq_mul]
  have hdist := dist_cayleyCenter_sq q
  field_simp [hd]
  linarith [hdist]

private def cayleyToFun (x : UpperHalfSpace E) : PoincareBall P :=
  mk (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P)) <| by
    set y : P := EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P)
    have hpos : 0 < 1 - ‖y‖ ^ 2 := by
      dsimp only [y]
      rw [one_sub_norm_cayleyInversion_sq (upper_ne_cayleyCenter x), UpperHalfSpace.snd_coe]
      exact div_pos (mul_pos (by norm_num) (UpperHalfSpace.height_pos x))
        (pow_pos (dist_pos.2 (upper_ne_cayleyCenter x)) 2)
    nlinarith [norm_nonneg y]

private theorem coe_cayleyToFun (x : UpperHalfSpace E) :
    (cayleyToFun x : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P) :=
  coe_mk _ _

private theorem coe_comp_cayleyToFun :
    coe ∘ cayleyToFun (E := E) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) ∘ UpperHalfSpace.coe :=
  funext coe_cayleyToFun

private def cayleyInvFun (y : PoincareBall P) : UpperHalfSpace E :=
  UpperHalfSpace.mk
      (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (y : P)) <| by
    rw [snd_cayleyInversion (ball_ne_cayleyCenter y)]
    exact div_pos (one_sub_norm_sq_pos y) (pow_pos (dist_pos.2 (ball_ne_cayleyCenter y)) 2)

private theorem coe_cayleyInvFun (y : PoincareBall P) :
    (cayleyInvFun y : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (y : P) :=
  UpperHalfSpace.coe_mk _ _

private theorem coe_comp_cayleyInvFun :
    UpperHalfSpace.coe ∘ cayleyInvFun (E := E) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) ∘ coe :=
  funext coe_cayleyInvFun

private theorem cayleyInvFun_cayleyToFun (x : UpperHalfSpace E) :
    cayleyInvFun (cayleyToFun x) = x :=
  UpperHalfSpace.ext <| by
    rw [coe_cayleyInvFun, coe_cayleyToFun,
      EuclideanGeometry.inversion_inversion _ (Real.sqrt_pos.2 zero_lt_two).ne']

private theorem cayleyToFun_cayleyInvFun (y : PoincareBall P) :
    cayleyToFun (cayleyInvFun y) = y :=
  ext <| by
    rw [coe_cayleyToFun, coe_cayleyInvFun,
      EuclideanGeometry.inversion_inversion _ (Real.sqrt_pos.2 zero_lt_two).ne']

private theorem contMDiff_cayleyToFun {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) n (cayleyToFun (E := E)) := by
  refine contMDiff_coe_comp_iff.1 ?_
  rw [coe_comp_cayleyToFun]
  exact fun x ↦ (EuclideanGeometry.contDiffAt_inversion (upper_ne_cayleyCenter x)).contMDiffAt.comp
    x (UpperHalfSpace.contMDiff_coe.of_le le_top x)

private theorem contMDiff_cayleyInvFun {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) n (cayleyInvFun (E := E)) := by
  refine UpperHalfSpace.contMDiff_coe_comp_iff.1 ?_
  rw [coe_comp_cayleyInvFun]
  exact fun y ↦ (EuclideanGeometry.contDiffAt_inversion (ball_ne_cayleyCenter y)).contMDiffAt.comp
    y (contMDiff_coe.of_le le_top y)

private theorem tangentSpaceCastModel_mfderiv_cayleyToFun
    (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, P) x) :
    tangentSpaceCastModel 𝓘(ℝ, P) (cayleyToFun x)
        (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) cayleyToFun x v) =
      fderiv ℝ (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2)) (x : P)
        (tangentSpaceCastModel 𝓘(ℝ, P) x v) := by
  have hf := EuclideanGeometry.hasFDerivAt_inversion (R := Real.sqrt 2) (upper_ne_cayleyCenter x)
  have hcoe : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, P) (UpperHalfSpace.coe : UpperHalfSpace E → P) x :=
    (UpperHalfSpace.contMDiff_coe x).mdifferentiableAt (by simp)
  rw [tangentSpaceCastModel_mfderiv_coe_comp, coe_comp_cayleyToFun,
    TauCeti.mvfderiv_comp_apply_of_differentiableAt hf.differentiableAt hcoe]
  have hmvf : mvfderiv 𝓘(ℝ, P) (UpperHalfSpace.coe : UpperHalfSpace E → P) x v = (v : P) :=
    TauCeti.mvfderiv_apply_of_eventuallyEq_extChartAt
      (Filter.EventuallyEq.of_eq (funext fun y ↦ by simp [extChartAt])) v
  -- `TangentSpace 𝓘(ℝ, P) x` is a type synonym of `P`, and `tangentSpaceCastModel` is the identity
  -- on vectors (`Mathlib/Geometry/Manifold/IsManifold/Basic.lean`).
  have hcast : tangentSpaceCastModel 𝓘(ℝ, P) x v = (v : P) := (rfl)
  rw [hmvf, hcast]

private def cayleyDiffeomorph :
    Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) (UpperHalfSpace E) (PoincareBall P) ∞ where
  toFun := cayleyToFun
  invFun := cayleyInvFun
  left_inv := cayleyInvFun_cayleyToFun
  right_inv := cayleyToFun_cayleyInvFun
  contMDiff_toFun := contMDiff_cayleyToFun
  contMDiff_invFun := contMDiff_cayleyInvFun

private theorem coe_cayleyDiffeomorph :
    ⇑(cayleyDiffeomorph (E := E)) = cayleyToFun :=
  (rfl)

variable (E) in
/-- **The Cayley Riemannian isometry**: Euclidean inversion in the sphere of radius `√2` centred at
`(0, -1)` restricts to an analytic Riemannian isometry from `UpperHalfSpace E` onto
`PoincareBall (WithLp 2 (E × ℝ))`, sending `(0, 1)` to `0`. -/
def cayleyIsometry :
    RiemannianIsometry 𝓘(ℝ, P) 𝓘(ℝ, P) (UpperHalfSpace E) (PoincareBall P) where
  toDiffeomorph := cayleyDiffeomorph
  inner_mfderiv' x v w := by
    rw [coe_cayleyDiffeomorph, inner_def, UpperHalfSpace.inner_def,
      tangentSpaceCastModel_mfderiv_cayleyToFun, tangentSpaceCastModel_mfderiv_cayleyToFun,
      EuclideanGeometry.inner_fderiv_inversion, coe_cayleyToFun,
      one_sub_norm_cayleyInversion_sq (upper_ne_cayleyCenter x), UpperHalfSpace.snd_coe]
    have hd : dist (x : P) (WithLp.toLp 2 (0, -1)) ≠ 0 := dist_ne_zero.2 (upper_ne_cayleyCenter x)
    have hh : UpperHalfSpace.height x ≠ 0 := (UpperHalfSpace.height_pos x).ne'
    have hpow4 : (Real.sqrt 2 / dist (x : P) (WithLp.toLp 2 (0, -1))) ^ 4 =
        4 / dist (x : P) (WithLp.toLp 2 (0, -1)) ^ 4 := by
      rw [div_pow]
      have h4 : Real.sqrt 2 ^ 4 = 4 := by
        calc
          Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
          _ = 4 := by rw [Real.sq_sqrt zero_le_two]; norm_num
      rw [h4]
    rw [hpow4]
    field_simp [hd, hh]

private theorem coe_cayleyIsometry :
    ⇑(cayleyIsometry E) = cayleyToFun :=
  (rfl)

@[simp]
theorem coe_cayleyIsometry_apply (x : UpperHalfSpace E) :
    (cayleyIsometry E x : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P) :=
  coe_cayleyToFun x

@[simp]
theorem coe_cayleyIsometry_symm_apply (y : PoincareBall P) :
    ((cayleyIsometry E).symm y : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (y : P) := by
  have h : (cayleyIsometry E).symm (cayleyIsometry E (cayleyInvFun y)) = cayleyInvFun y :=
    RiemannianIsometry.symm_apply_apply _ _
  rw [coe_cayleyIsometry, cayleyToFun_cayleyInvFun] at h
  rw [h, coe_cayleyInvFun]

/-- The Cayley isometry sends the base point `(0, 1)` of `UpperHalfSpace E` to the origin `0` of
`PoincareBall (WithLp 2 (E × ℝ))`. -/
@[simp]
theorem cayleyIsometry_mk_zero_one :
    cayleyIsometry E (UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)) = 0 := by
  ext
  rw [coe_cayleyIsometry_apply, UpperHalfSpace.coe_mk, coe_zero]
  simp only [EuclideanGeometry.inversion_def, vsub_eq_sub, vadd_eq_add, div_pow,
    Real.sq_sqrt zero_le_two]
  have hnorm : ‖(WithLp.toLp 2 ((0 : E), (1 : ℝ)) : P)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp
  have hd : dist (WithLp.toLp 2 ((0 : E), (1 : ℝ))) (WithLp.toLp 2 (0, -1)) ^ 2 = 4 := by
    rw [dist_cayleyCenter_sq, hnorm]
    simp
    norm_num
  rw [hd]
  exact (WithLp.ext_iff 2).2 (Prod.ext (by simp) (by simp; norm_num))

/-- The inverse Cayley isometry sends the origin `0` of `PoincareBall (WithLp 2 (E × ℝ))` to the
base point `(0, 1)` of `UpperHalfSpace E`. -/
@[simp]
theorem cayleyIsometry_symm_zero :
    (cayleyIsometry E).symm 0 = UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp) := by
  rw [← cayleyIsometry_mk_zero_one, RiemannianIsometry.symm_apply_apply]

end Cayley

end TauCeti.PoincareBall
