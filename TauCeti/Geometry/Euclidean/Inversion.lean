/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Inversion: the punctured space, analyticity, isometries, and orientation

Inversion in a sphere of positive radius exchanges the punctured open ball with the exterior of the
closed ball (`TauCeti.dist_inversion_center_lt_iff`, `TauCeti.lt_dist_inversion_center_iff`). For a
nonzero radius it restricts to an involutive self-homeomorphism of the complement of its centre
(`TauCeti.inversionHomeomorph`). In an `RCLike` field it is given by the conjugate-reciprocal
formula `c + R ^ 2 / conj (z - c)`, which in `ℂ` is the classical formula for reflection in a
circle.

Inversion is analytic away from its centre (`EuclideanGeometry.contDiffAt_inversion`). This
extends the smooth regularity provided by Mathlib's `ContDiffAt.inversion` to the analytic order.

Inversion in a sphere (`EuclideanGeometry.inversion c R`) is defined from the distance to the
centre and the vector from the centre, both of which an affine isometry preserves. So an affine
isometry carries the inversion in a sphere to the inversion in the image sphere, and a linear
isometry fixing the centre commutes with the inversion. This is the compatibility used to compare
inversion charts of the closed unit balls of two inner product spaces along a linear isometry.

For a nonzero radius `R`, the derivative of the inversion at a point `x ≠ c` is a positive
multiple of the reflection in the hyperplane orthogonal to `x - c` (`hasFDerivAt_inversion`), so
in finite dimension its determinant is negative: inversion reverses orientation. A transition
between two inversion charts whose linear isometries lie in the same orientation class is a
composite of two inversions and a linear isometry of positive determinant, so it preserves
orientation. This is how the inversion charts of the closed unit ball attached to the isometries
of one orientation class give an oriented atlas.

## Main results

* `TauCeti.inversionHomeomorph`: inversion as a self-homeomorphism of the complement of its centre.
* `TauCeti.inversion_eq_conj_reciprocal`: inversion in an `RCLike` field is
  `z ↦ c + R ^ 2 / conj (z - c)`.
* `EuclideanGeometry.contDiffAt_inversion`: inversion is analytic away from its centre.
* `TauCeti.snd_inversion`: the last coordinate of inversion about a centre in `E × {0}`.
* `AffineIsometry.map_inversion`: an affine isometry carries inversion in the sphere of centre `c`
  and radius `R` to inversion in the sphere of centre `f c` and radius `R`.
* `LinearIsometry.map_inversion`: the same for a linear isometry.
* `EuclideanGeometry.det_fderiv_inversion_neg`: the derivative of an inversion has negative
  determinant.
-/

public section

open EuclideanGeometry
open scoped ComplexConjugate ContDiff

namespace EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inversion in a sphere is `C^n`, including analytic, away from its centre. -/
theorem contDiffAt_inversion {c x : E} {R : ℝ} {n : ℕ∞ω} (hx : x ≠ c) :
    ContDiffAt ℝ n (inversion c R) x := by
  have h : ContDiffAt ℝ n (fun y : E ↦ R / dist y c) x :=
    contDiffAt_const.div (contDiffAt_id.dist ℝ contDiffAt_const hx) (dist_ne_zero.2 hx)
  exact ((h.pow 2).smul (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const

end EuclideanGeometry

variable {V V₂ P P₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
  [NormedAddTorsor V₂ P₂]

/-- An affine isometry carries the inversion in the sphere of centre `c` and radius `R` to the
inversion in the sphere of centre `f c` and radius `R`. -/
theorem AffineIsometry.map_inversion (f : P →ᵃⁱ[ℝ] P₂) (c : P) (R : ℝ) (x : P) :
    f (inversion c R x) = inversion (f c) R (f x) := by
  simp only [inversion, f.map_vadd, f.linearIsometry.map_smul, f.map_vsub, f.dist_map]

/-- A linear isometry carries the inversion in the sphere of centre `c` and radius `R` to the
inversion in the sphere of centre `f c` and radius `R`. -/
theorem LinearIsometry.map_inversion (f : V →ₗᵢ[ℝ] V₂) (c : V) (R : ℝ) (x : V) :
    f (inversion c R x) = inversion (f c) R (f x) :=
  f.toAffineIsometry.map_inversion c R x

namespace EuclideanGeometry

/-- The derivative of inversion away from its centre is a continuous linear equivalence. -/
noncomputable def inversionFDerivEquiv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (c z : V) (R : ℝ) (hR : R ≠ 0) (hz : z ≠ c) : V ≃L[ℝ] V :=
  ((ℝ ∙ (z - c))ᗮ.reflection).toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((R / dist z c) ^ 2)
      (pow_ne_zero _ (div_ne_zero hR (dist_ne_zero.mpr hz)))))

/-- The inversion derivative equivalence represents the actual Fréchet derivative. -/
theorem hasFDerivAt_inversionFDerivEquiv {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (c z : V) (R : ℝ)
    (hR : R ≠ 0) (hz : z ≠ c) :
    HasFDerivAt (inversion c R) (inversionFDerivEquiv c z R hR hz).toContinuousLinearMap z := by
  convert hasFDerivAt_inversion hz using 1
  ext v
  -- Reflection followed by scalar multiplication evaluates to Mathlib’s derivative formula.
  rfl

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Inversion reverses orientation**: away from its centre, the derivative of the inversion in a
sphere of nonzero radius has negative determinant. The derivative is `(R / dist x c) ^ 2` times
the reflection in the hyperplane orthogonal to `x - c`, whose determinant is `-1`. -/
theorem det_fderiv_inversion_neg {c x : F} {R : ℝ} (hR : R ≠ 0) (hx : x ≠ c) :
    LinearMap.det (fderiv ℝ (inversion c R) x : F →ₗ[ℝ] F) < 0 := by
  have hK : Module.finrank ℝ (ℝ ∙ (x - c))ᗮᗮ = 1 := by
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton (sub_ne_zero.2 hx)]
  have hpos : 0 < (R / dist x c) ^ 2 := by
    have : R / dist x c ≠ 0 := div_ne_zero hR (dist_ne_zero.2 hx)
    positivity
  rw [(hasFDerivAt_inversion hx).fderiv, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  -- The reflection, coerced to a continuous linear map and then to a linear map, is its
  -- underlying linear map.
  have hrefl : (((ℝ ∙ (x - c))ᗮ.reflection : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      (ℝ ∙ (x - c))ᗮ.reflection.toLinearMap := (rfl)
  rw [hrefl, Submodule.det_reflection, hK, pow_one, mul_neg_one, neg_lt_zero]
  exact pow_pos hpos _

end EuclideanGeometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The last coordinate of the inversion in a sphere centred on the boundary hyperplane. -/
theorem snd_inversion (a : E) (R : ℝ) (p : WithLp 2 (E × ℝ)) :
    (EuclideanGeometry.inversion (WithLp.toLp 2 (a, 0)) R p).snd =
      (R / dist p (WithLp.toLp 2 (a, 0))) ^ 2 * p.snd := by
  simp [EuclideanGeometry.inversion]

/-- Inversion in a sphere of positive radius sends a point other than the centre into the open
ball exactly when the point lies outside the closed ball. -/
@[simp]
theorem dist_inversion_center_lt_iff {c x : P} {R : ℝ} (hR : 0 < R) (hx : x ≠ c) :
    dist (inversion c R x) c < R ↔ R < dist x c := by
  rw [dist_inversion_center, div_lt_iff₀ (dist_pos.2 hx), sq, mul_lt_mul_iff_right₀ hR]

/-- Inversion in a sphere of positive radius sends a point other than the centre outside the
closed ball exactly when the point lies in the open ball. -/
@[simp]
theorem lt_dist_inversion_center_iff {c x : P} {R : ℝ} (hR : 0 < R) (hx : x ≠ c) :
    R < dist (inversion c R x) c ↔ dist x c < R := by
  rw [dist_inversion_center, lt_div_iff₀ (dist_pos.2 hx), sq, mul_lt_mul_iff_right₀ hR]

/-- Inversion in a sphere of nonzero radius restricts to a self-homeomorphism of the complement of
its centre. -/
noncomputable def inversionHomeomorph (c : P) {R : ℝ} (hR : R ≠ 0) :
    ({c}ᶜ : Set P) ≃ₜ ({c}ᶜ : Set P) where
  toFun x := ⟨inversion c R x, (inversion_eq_center hR).not.2 x.2⟩
  invFun x := ⟨inversion c R x, (inversion_eq_center hR).not.2 x.2⟩
  left_inv x := Subtype.ext (inversion_inversion c hR x)
  right_inv x := Subtype.ext (inversion_inversion c hR x)
  continuous_toFun :=
    (continuousOn_const.inversion continuousOn_const continuousOn_id fun _ ↦ id).domRestrict
      |>.subtype_mk _
  continuous_invFun :=
    (continuousOn_const.inversion continuousOn_const continuousOn_id fun _ ↦ id).domRestrict
      |>.subtype_mk _

/-- The restricted inversion homeomorphism acts by inversion. -/
@[simp]
theorem coe_inversionHomeomorph_apply (c : P) {R : ℝ} (hR : R ≠ 0) (x : ({c}ᶜ : Set P)) :
    (inversionHomeomorph c hR x : P) = inversion c R x :=
  (rfl)

/-- The restricted inversion homeomorphism is its own inverse. -/
@[simp]
theorem inversionHomeomorph_symm (c : P) {R : ℝ} (hR : R ≠ 0) :
    (inversionHomeomorph c hR).symm = inversionHomeomorph c hR :=
  Homeomorph.ext fun x ↦ (inversionHomeomorph c hR).symm_apply_eq.2 <|
    Subtype.ext (inversion_inversion c hR x).symm

/-- In an `RCLike` field, inversion in the sphere of centre `c` and radius `R` is given by the
conjugate-reciprocal formula; in `ℂ` this is the standard formula for reflection in a circle. -/
theorem inversion_eq_conj_reciprocal {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (R : ℝ) (z : 𝕜) :
    inversion c R z = c + (R : 𝕜) ^ 2 / conj (z - c) := by
  simp only [inversion, vsub_eq_sub, vadd_eq_add, dist_eq_norm, RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [add_comm, div_pow, ← RCLike.conj_mul]
  rcases eq_or_ne (z - c) 0 with h | h
  · simp [h]
  · field_simp

end TauCeti
