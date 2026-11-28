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

For any real inner product space `E`, every Euclidean sphere centred at `c : E` (`1 < ‖c‖`) of
radius `√(‖c‖² - 1)` meets the unit sphere orthogonally and scales `1 - ‖x‖²` by the conformal
factor `(√(‖c‖² - 1) / dist x c)²`. Euclidean inversion in this sphere restricts to an involutive
Riemannian isometry `PoincareBall.inversion` of `PoincareBall E`. Taking `c = ‖a‖⁻² • a` gives the
origin-swapping involution `PoincareBall.inversionSwapZero`, proving transitive action of
`Isom 𝓘(ℝ, E) (PoincareBall E)` on `PoincareBall E`. Finally, inversion in the sphere of radius `√2`
centred at `(0, -1)` defines the Cayley Riemannian isometry `PoincareBall.cayleyIsometry` from
`UpperHalfSpace E` onto `PoincareBall (WithLp 2 (E × ℝ))`.

## Main definitions and results

* `TauCeti.PoincareBall.inversion` and `TauCeti.PoincareBall.inversionSwapZero`: orthogonal-sphere
  reflections and origin-swapping involutions (`inversion_mul_self`, `inversionSwapZero_zero`,
  `inversionSwapZero_self`, `norm_coe_inversionSwapZero`, `isPretransitive_isom`).
* `TauCeti.PoincareBall.cayleyIsometry`: the Cayley Riemannian isometry from `UpperHalfSpace E` onto
  `PoincareBall (WithLp 2 (E × ℝ))` (`cayleyIsometry_mk_zero_one`, `cayleyIsometry_symm_zero`).

## References

* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019), §4.5.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.PoincareBall

section Inversion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem norm_sq_sub_one_pos {c : E} (hc : 1 < ‖c‖) : 0 < ‖c‖ ^ 2 - 1 := by nlinarith

omit [InnerProductSpace ℝ E] in
private theorem sqrt_norm_sq_sub_one_pos {c : E} (hc : 1 < ‖c‖) :
    0 < Real.sqrt (‖c‖ ^ 2 - 1) :=
  Real.sqrt_pos.2 (norm_sq_sub_one_pos hc)

omit [InnerProductSpace ℝ E] in
private theorem sq_sqrt_norm_sq_sub_one {c : E} (hc : 1 < ‖c‖) :
    Real.sqrt (‖c‖ ^ 2 - 1) ^ 2 = ‖c‖ ^ 2 - 1 :=
  Real.sq_sqrt (norm_sq_sub_one_pos hc).le

omit [InnerProductSpace ℝ E] in
private theorem coe_ne_center {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) : (x : E) ≠ c :=
  fun h ↦ ((norm_lt_one x).trans hc).ne (congrArg norm h)

private def inversionMap {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) : PoincareBall E :=
  mk (EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E)) <| by
    have hpos : 0 < 1 - ‖EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E)‖ ^ 2 := by
      rw [EuclideanGeometry.one_sub_norm_inversion_sq (sq_sqrt_norm_sq_sub_one hc)
        (coe_ne_center hc x)]
      exact mul_pos (pow_pos (div_pos (sqrt_norm_sq_sub_one_pos hc)
        (dist_pos.2 (coe_ne_center hc x))) 2) (one_sub_norm_sq_pos x)
    nlinarith [norm_nonneg (EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E))]

private theorem coe_inversionMap {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    (inversionMap hc x : E) = EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E) :=
  coe_mk _ _

private theorem inversionMap_inversionMap {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    inversionMap hc (inversionMap hc x) = x :=
  ext <| by
    rw [coe_inversionMap, coe_inversionMap,
      EuclideanGeometry.inversion_inversion _ (sqrt_norm_sq_sub_one_pos hc).ne']

private theorem contMDiff_inversionMap {n : ℕ∞ω} {c : E} (hc : 1 < ‖c‖) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (inversionMap hc) := by
  have h : coe ∘ inversionMap hc = EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) ∘ coe :=
    funext (coe_inversionMap hc)
  rw [← contMDiff_coe_comp_iff, h]
  exact fun x ↦ (EuclideanGeometry.contDiffAt_inversion (coe_ne_center hc x)).contMDiffAt.comp x
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
  exact tangentSpaceCastModel_mfderiv_apply hf (funext (coe_inversionMap hc)) v

private def inversionDiffeomorph {c : E} (hc : 1 < ‖c‖) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (PoincareBall E) (PoincareBall E) ∞ where
  toFun := inversionMap hc
  invFun := inversionMap hc
  left_inv := inversionMap_inversionMap hc
  right_inv := inversionMap_inversionMap hc
  contMDiff_toFun := contMDiff_inversionMap hc
  contMDiff_invFun := contMDiff_inversionMap hc

private theorem coe_inversionDiffeomorph {c : E} (hc : 1 < ‖c‖) :
    ⇑(inversionDiffeomorph hc) = inversionMap hc := (rfl)

/-- Euclidean inversion in the sphere centred at `c` (`1 < ‖c‖`) of radius `√(‖c‖² - 1)` restricts
to an involutive Riemannian isometry of `PoincareBall E`. Geometrically, this is hyperbolic
reflection across the totally geodesic hypersurface cut out by the orthogonal sphere. -/
def inversion {c : E} (hc : 1 < ‖c‖) : Isom 𝓘(ℝ, E) (PoincareBall E) where
  toDiffeomorph := inversionDiffeomorph hc
  inner_mfderiv' x v w := by
    rw [coe_inversionDiffeomorph, inner_def, inner_def,
      tangentSpaceCastModel_mfderiv_inversionMap, tangentSpaceCastModel_mfderiv_inversionMap,
      EuclideanGeometry.inner_fderiv_inversion, coe_inversionMap,
      EuclideanGeometry.one_sub_norm_inversion_sq (sq_sqrt_norm_sq_sub_one hc) (coe_ne_center hc x)]
    field_simp [(sqrt_norm_sq_sub_one_pos hc).ne', dist_ne_zero.2 (coe_ne_center hc x),
      (one_sub_norm_sq_pos x).ne']

private theorem coe_inversion {c : E} (hc : 1 < ‖c‖) : ⇑(inversion hc) = inversionMap hc := (rfl)

@[simp] theorem coe_inversion_apply {c : E} (hc : 1 < ‖c‖) (x : PoincareBall E) :
    (inversion hc x : E) = EuclideanGeometry.inversion c (Real.sqrt (‖c‖ ^ 2 - 1)) (x : E) :=
  coe_inversionMap hc x

/-- Orthogonal-sphere inversions are involutions in the Riemannian isometry group. -/
@[simp] theorem inversion_mul_self {c : E} (hc : 1 < ‖c‖) : inversion hc * inversion hc = 1 :=
  RiemannianIsometry.ext fun x ↦ by
    rw [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply, coe_inversion,
      inversionMap_inversionMap]

@[simp] theorem inversion_inv {c : E} (hc : 1 < ‖c‖) : (inversion hc)⁻¹ = inversion hc :=
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
    (EuclideanGeometry.hasFDerivAt_inversion (coe_ne_center hc x)) (funext (coe_inversionMap hc)) v

/-! ### Origin-swapping inversions and transitivity -/

omit [InnerProductSpace ℝ E] in
private theorem norm_inv_sq_smul [NormedSpace ℝ E] {a : PoincareBall E} (ha : a ≠ 0) :
    ‖(‖(a : E)‖ ^ 2)⁻¹ • (a : E)‖ = ‖(a : E)‖⁻¹ := by
  have ha0 : ‖(a : E)‖ ≠ 0 := norm_ne_zero_iff.2 (coe_eq_zero.not.2 ha)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
  field_simp [ha0]

omit [InnerProductSpace ℝ E] in
private theorem one_lt_norm_inv_sq_smul [NormedSpace ℝ E] {a : PoincareBall E} (ha : a ≠ 0) :
    1 < ‖(‖(a : E)‖ ^ 2)⁻¹ • (a : E)‖ :=
  norm_inv_sq_smul ha ▸ (one_lt_inv₀ (norm_pos_iff.2 (coe_eq_zero.not.2 ha))).2 (norm_lt_one a)

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

@[simp] theorem inversionSwapZero_mul_self {a : PoincareBall E} (ha : a ≠ 0) :
    inversionSwapZero ha * inversionSwapZero ha = 1 := inversion_mul_self _

@[simp] theorem inversionSwapZero_inv {a : PoincareBall E} (ha : a ≠ 0) :
    (inversionSwapZero ha)⁻¹ = inversionSwapZero ha := inversion_inv _

@[simp] theorem inversionSwapZero_zero {a : PoincareBall E} (ha : a ≠ 0) :
    inversionSwapZero ha 0 = a := by
  ext
  rw [coe_inversionSwapZero_apply, coe_zero]
  have ha0 : ‖(a : E)‖ ≠ 0 := norm_ne_zero_iff.2 (coe_eq_zero.not.2 ha)
  simp only [EuclideanGeometry.inversion_def, vsub_eq_sub, vadd_eq_add]
  rw [dist_zero_left, zero_sub, div_pow, sq_sqrt_norm_sq_sub_one (one_lt_norm_inv_sq_smul ha),
    norm_inv_sq_smul ha]
  have hcoef : (‖(a : E)‖⁻¹ ^ 2 - 1) / ‖(a : E)‖⁻¹ ^ 2 = 1 - ‖(a : E)‖ ^ 2 := by field_simp [ha0]
  have hsmul : ‖(a : E)‖ ^ 2 • ((‖(a : E)‖ ^ 2)⁻¹ • (a : E)) = (a : E) := by simp [smul_smul, ha0]
  rw [hcoef, smul_neg, sub_smul, one_smul, hsmul]
  abel

@[simp] theorem inversionSwapZero_self {a : PoincareBall E} (ha : a ≠ 0) :
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
  have hc_sq : ‖c‖ ^ 2 = (‖(a : E)‖ ^ 2)⁻¹ := by rw [norm_inv_sq_smul ha, inv_pow]
  set D : ℝ := ‖(a : E) - (y : E)‖ ^ 2 + (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)
  have hD_pos : 0 < D :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (one_sub_norm_sq_pos a) (one_sub_norm_sq_pos y))
  have hdist_sq : dist (y : E) c ^ 2 = D / ‖(a : E)‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hc_sq, real_inner_comm, real_inner_smul_left]
    dsimp only [D]
    rw [norm_sub_sq_real]
    field_simp [ha0]
    ring
  have h1 : 1 - ‖(inversionSwapZero ha y : E)‖ ^ 2 =
      (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2) / D := by
    rw [coe_inversionSwapZero_apply,
      EuclideanGeometry.one_sub_norm_inversion_sq (sq_sqrt_norm_sq_sub_one hc)
        (coe_ne_center hc y),
      div_pow, sq_sqrt_norm_sq_sub_one hc, hc_sq, hdist_sq]
    field_simp [ha0, hD_pos.ne']
  have hdiv : ‖(a : E) - (y : E)‖ ^ 2 / D + (1 - ‖(a : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2) / D = 1 := by
    rw [← add_div, div_self hD_pos.ne']
  have hsq : ‖(inversionSwapZero ha y : E)‖ ^ 2 = ‖(a : E) - (y : E)‖ ^ 2 / D := by
    linarith [h1, hdiv]
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- The Riemannian isometry group of `PoincareBall E` acts transitively on `PoincareBall E` in every
real inner product space `E`. -/
instance isPretransitive_isom :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, E) (PoincareBall E)) (PoincareBall E) where
  exists_smul_eq x y := by
    have h0 (z : PoincareBall E) : ∃ g : Isom 𝓘(ℝ, E) (PoincareBall E), g 0 = z := by
      rcases eq_or_ne z 0 with rfl | hz
      · exact ⟨1, RiemannianIsometry.one_apply 0⟩
      · exact ⟨inversionSwapZero hz, inversionSwapZero_zero hz⟩
    obtain ⟨g₁, hg₁⟩ := h0 x
    obtain ⟨g₂, hg₂⟩ := h0 y
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    rw [RiemannianIsometry.smul_def, ← hg₁, ← RiemannianIsometry.mul_apply, mul_assoc,
      inv_mul_cancel, mul_one, hg₂]

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

private theorem ball_ne_cayleyCenter (x : PoincareBall P) :
    (x : P) ≠ WithLp.toLp 2 (0, -1) := fun h ↦ by
  have hnorm : ‖(x : P)‖ ^ 2 = 1 := by rw [h, ← real_inner_self_eq_norm_sq]; simp
  linarith [norm_sq_lt_one x]

private def cayleyToFun (x : UpperHalfSpace E) : PoincareBall P :=
  mk (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P)) <| by
    have hpos : 0 < 1 -
        ‖EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P)‖ ^ 2 := by
      rw [one_sub_norm_inversion_toLp_zero_neg_one_sqrt_two_sq (upper_ne_cayleyCenter x),
        UpperHalfSpace.snd_coe]
      exact div_pos (mul_pos (by norm_num) (UpperHalfSpace.height_pos x))
        (pow_pos (dist_pos.2 (upper_ne_cayleyCenter x)) 2)
    nlinarith [norm_nonneg
      (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P))]

private theorem coe_cayleyToFun (x : UpperHalfSpace E) :
    (cayleyToFun x : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P) :=
  coe_mk _ _

private def cayleyInvFun (y : PoincareBall P) : UpperHalfSpace E :=
  UpperHalfSpace.mk
      (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (y : P)) <| by
    rw [snd_inversion_toLp_zero_neg_one_sqrt_two (ball_ne_cayleyCenter y)]
    exact div_pos (one_sub_norm_sq_pos y) (pow_pos (dist_pos.2 (ball_ne_cayleyCenter y)) 2)

private theorem coe_cayleyInvFun (y : PoincareBall P) :
    (cayleyInvFun y : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (y : P) :=
  UpperHalfSpace.coe_mk _ _

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

private theorem coe_comp_cayleyToFun :
    coe ∘ cayleyToFun (E := E) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) ∘ UpperHalfSpace.coe :=
  funext coe_cayleyToFun

private theorem contMDiff_cayleyToFun {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) n (cayleyToFun (E := E)) := by
  rw [← contMDiff_coe_comp_iff, coe_comp_cayleyToFun]
  exact fun x ↦ (EuclideanGeometry.contDiffAt_inversion (upper_ne_cayleyCenter x)).contMDiffAt.comp
    x (UpperHalfSpace.contMDiff_coe.of_le le_top x)

private theorem contMDiff_cayleyInvFun {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, P) n (cayleyInvFun (E := E)) := by
  have h : UpperHalfSpace.coe ∘ cayleyInvFun (E := E) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) ∘ coe :=
    funext coe_cayleyInvFun
  rw [← UpperHalfSpace.contMDiff_coe_comp_iff, h]
  exact fun y ↦ (EuclideanGeometry.contDiffAt_inversion (ball_ne_cayleyCenter y)).contMDiffAt.comp
    y (contMDiff_coe.of_le le_top y)

private theorem tangentSpaceCastModel_mfderiv_cayleyToFun
    (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, P) x) :
    tangentSpaceCastModel 𝓘(ℝ, P) (cayleyToFun x) (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) cayleyToFun x v) =
      fderiv ℝ (EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2)) (x : P)
        (tangentSpaceCastModel 𝓘(ℝ, P) x v) := by
  have hf := EuclideanGeometry.hasFDerivAt_inversion (R := Real.sqrt 2) (upper_ne_cayleyCenter x)
  have hcoe := (UpperHalfSpace.contMDiff_coe x).mdifferentiableAt (by simp)
  rw [tangentSpaceCastModel_mfderiv_coe_comp, coe_comp_cayleyToFun,
    TauCeti.mvfderiv_comp_apply_of_differentiableAt hf.differentiableAt hcoe]
  have hmvf : mvfderiv 𝓘(ℝ, P) (UpperHalfSpace.coe : UpperHalfSpace E → P) x v = (v : P) :=
    TauCeti.mvfderiv_apply_of_eventuallyEq_extChartAt
      (Filter.EventuallyEq.of_eq (funext fun y ↦ by simp [extChartAt])) v
  -- `TangentSpace 𝓘(ℝ, P) x` is a type synonym of `P`, and `tangentSpaceCastModel` is the identity.
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

private theorem coe_cayleyDiffeomorph : ⇑(cayleyDiffeomorph (E := E)) = cayleyToFun := (rfl)

variable (E) in
/-- **The Cayley Riemannian isometry**: Euclidean inversion in the sphere of radius `√2` centred at
`(0, -1)` restricts to an analytic Riemannian isometry from `UpperHalfSpace E` onto
`PoincareBall (WithLp 2 (E × ℝ))`, sending `(0, 1)` to `0`. -/
def cayleyIsometry : RiemannianIsometry 𝓘(ℝ, P) 𝓘(ℝ, P) (UpperHalfSpace E) (PoincareBall P) where
  toDiffeomorph := cayleyDiffeomorph
  inner_mfderiv' x v w := by
    rw [coe_cayleyDiffeomorph, inner_def, UpperHalfSpace.inner_def,
      tangentSpaceCastModel_mfderiv_cayleyToFun, tangentSpaceCastModel_mfderiv_cayleyToFun,
      EuclideanGeometry.inner_fderiv_inversion, coe_cayleyToFun,
      one_sub_norm_inversion_toLp_zero_neg_one_sqrt_two_sq (upper_ne_cayleyCenter x),
      UpperHalfSpace.snd_coe]
    have hd : dist (x : P) (WithLp.toLp 2 (0, -1)) ≠ 0 := dist_ne_zero.2 (upper_ne_cayleyCenter x)
    have hh : UpperHalfSpace.height x ≠ 0 := (UpperHalfSpace.height_pos x).ne'
    have h4 : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
    rw [div_pow, h4, Real.sq_sqrt zero_le_two]
    field_simp [hd, hh]
    ring

private theorem coe_cayleyIsometry : ⇑(cayleyIsometry E) = cayleyToFun := (rfl)

@[simp] theorem coe_cayleyIsometry_apply (x : UpperHalfSpace E) :
    (cayleyIsometry E x : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (x : P) :=
  coe_cayleyToFun x

@[simp] theorem coe_cayleyIsometry_symm_apply (y : PoincareBall P) :
    ((cayleyIsometry E).symm y : P) =
      EuclideanGeometry.inversion (WithLp.toLp 2 (0, -1)) (Real.sqrt 2) (y : P) := by
  have h : (cayleyIsometry E).symm (cayleyIsometry E (cayleyInvFun y)) = cayleyInvFun y :=
    RiemannianIsometry.symm_apply_apply _ _
  rw [coe_cayleyIsometry, cayleyToFun_cayleyInvFun] at h
  rw [h, coe_cayleyInvFun]

/-- The Cayley isometry sends the base point `(0, 1)` of `UpperHalfSpace E` to the origin `0` of
`PoincareBall (WithLp 2 (E × ℝ))`. -/
@[simp] theorem cayleyIsometry_mk_zero_one :
    cayleyIsometry E (UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)) = 0 := by
  ext
  rw [coe_cayleyIsometry_apply, UpperHalfSpace.coe_mk, coe_zero]
  simp only [EuclideanGeometry.inversion_def, vsub_eq_sub, vadd_eq_add, div_pow,
    Real.sq_sqrt zero_le_two]
  have hd : dist (WithLp.toLp 2 ((0 : E), (1 : ℝ))) (WithLp.toLp 2 (0, -1)) ^ 2 = 4 := by
    rw [dist_eq_norm, ← WithLp.toLp_sub, ← real_inner_self_eq_norm_sq]
    simp
    norm_num
  rw [hd]
  exact (WithLp.ext_iff 2).2 (Prod.ext (by simp)
    (by norm_num [WithLp.add_snd, WithLp.smul_snd, WithLp.sub_snd, WithLp.toLp_snd, smul_eq_mul]))

/-- The inverse Cayley isometry sends the origin `0` of `PoincareBall (WithLp 2 (E × ℝ))` to the
base point `(0, 1)` of `UpperHalfSpace E`. -/
@[simp] theorem cayleyIsometry_symm_zero :
    (cayleyIsometry E).symm 0 = UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp) := by
  rw [← cayleyIsometry_mk_zero_one, RiemannianIsometry.symm_apply_apply]

end Cayley

end TauCeti.PoincareBall
