/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Coercive
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

/-!
# The model geometry `SL₂ℝ~`

The model geometry `SL₂ℝ~` of Thurston's eight three-dimensional geometries is the universal
cover of the unit tangent bundle of the hyperbolic plane, with its natural (Sasaki) metric. Its
isometry group is four-dimensional and contains the universal cover of `PSL₂ℝ`, acting by
left translations, whence the name.

This file models it on `ℝ³` with coordinates `(x, y, z)`. The pair `(x, y)` is the point
`x + i eʸ` of the upper half-plane, so that `e^{-2y} dx² + dy²` is the hyperbolic metric in
horocyclic coordinates, and `z` is an angle coordinate on the fibre, unwound to a real line.
In the orthonormal frame `e₁ = eʸ ∂ₓ`, `e₂ = ∂_y` of the hyperbolic plane, with dual coframe
`θ₁ = e^{-y} dx`, `θ₂ = dy`, one has `dθ₁ = θ₁ ∧ θ₂` and `dθ₂ = 0`, so the Levi-Civita
connection is `∇e₁ = θ₁ ⊗ e₂`, `∇e₂ = -θ₁ ⊗ e₁`. Along a curve `γ`, the covariant derivative of
the unit vector `cos z e₁ + sin z e₂` is therefore `(z' + θ₁(γ'))` times the unit vector
`-sin z e₁ + cos z e₂`. The Sasaki metric of the unit tangent bundle, in which the horizontal
part projects isometrically and the vertical part is measured by this covariant derivative, is
thus `θ₁² + θ₂² + (dz + θ₁)²`. So `SL₂ℝ~` is `ℝ³` with the Riemannian metric
`e^{-2y} dx² + dy² + (dz + e^{-y} dx)²`. The connection form has nonzero exterior derivative,
`d(e^{-y} dx) = e^{-y} dx ∧ dy`, the area form of the hyperbolic plane, which is what
distinguishes this twisted metric from the product metric of `ℍ² × ℝ`.

The orientation-preserving affine maps `x ↦ eˢ x + a` of the boundary line of the upper
half-plane, together with the translations of the fibre, act by the isometries
`(x, y, z) ↦ (eˢ x + a, y + s, z + c)`. These form a three-dimensional group acting simply
transitively, so `SL₂ℝ~` is a homogeneous Riemannian manifold.

## Main definitions

* `TauCeti.SL2Tilde`: the model geometry `SL₂ℝ~`, with the coordinate equivalence
  `SL2Tilde.toProd` to `ℝ³` and the coordinates `SL2Tilde.x`, `SL2Tilde.y`, `SL2Tilde.z`.
* `TauCeti.SL2Tilde.riemannianMetric`: the analytic metric
  `e^{-2y} dx² + dy² + (dz + e^{-y} dx)²`, which is the `RiemannianBundle` instance of `SL2Tilde`.
* `TauCeti.SL2Tilde.translate a s c`: the isometry `(x, y, z) ↦ (eˢ x + a, y + s, z + c)`.

## Main results

* `TauCeti.SL2Tilde.inner_def`: the inner product of two tangent vectors at a point with second
  coordinate `y` is `e^{-2y} v₁ w₁ + v₂ w₂ + (v₃ + e^{-y} v₁) (w₃ + e^{-y} w₁)`.
* `TauCeti.SL2Tilde.translate_mul_translate`: the isometries `translate a s c` compose as the
  group `Aff⁺(ℝ) × ℝ`, and `TauCeti.SL2Tilde.translate_inj` says distinct parameters give
  distinct isometries.
* `TauCeti.SL2Tilde.isPretransitive_isom`: the isometry group of `SL₂ℝ~` acts transitively on it.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §3.8
  (the eight model geometries).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487, §4
  (the geometry `SL₂ℝ~` as the unit tangent bundle of the hyperbolic plane).
* The formal structure of this file (the coordinate type synonym, its charts, the metric built with
  `TauCeti.coerciveRiemannianMetric`, the explicit isometries and the transitivity instance)
  follows `TauCeti.Geometry.Manifold.Riemannian.Sol`.
-/

public section

open Bundle Manifold Real
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

/-- Thurston's model geometry `SL₂ℝ~`: the space `ℝ³`, with coordinates `(x, y, z)`, carrying the
Riemannian metric `e^{-2y} dx² + dy² + (dz + e^{-y} dx)²` of the universal cover of the unit
tangent bundle of the hyperbolic plane. -/
def SL2Tilde : Type := ℝ × ℝ × ℝ

namespace SL2Tilde

/-- The coordinates `(x, y, z)` of a point of `SL2Tilde`, as an equivalence with `ℝ³`. -/
def toProd : SL2Tilde ≃ ℝ × ℝ × ℝ := Equiv.refl _

/- `SL2Tilde` is a type synonym for `ℝ × ℝ × ℝ`, so that it can carry its own `RiemannianBundle`
instance. Its topology and charts are those of `ℝ × ℝ × ℝ`. -/

instance : TopologicalSpace SL2Tilde := inferInstanceAs (TopologicalSpace (ℝ × ℝ × ℝ))

instance : T2Space SL2Tilde := inferInstanceAs (T2Space (ℝ × ℝ × ℝ))

instance : ChartedSpace (ℝ × ℝ × ℝ) SL2Tilde :=
  inferInstanceAs (ChartedSpace (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ))

instance : IsManifold 𝓘(ℝ, ℝ × ℝ × ℝ) ω SL2Tilde :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ))

/-- The point of `SL2Tilde` with coordinates `(x, y, z)`. -/
def mk (x y z : ℝ) : SL2Tilde := toProd.symm (x, y, z)

/-- The first coordinate of a point of `SL2Tilde`, the horizontal coordinate of its image in
the upper half-plane. -/
def x (p : SL2Tilde) : ℝ := (toProd p).1

/-- The second coordinate of a point of `SL2Tilde`, the logarithm of the height of its image in
the upper half-plane. -/
def y (p : SL2Tilde) : ℝ := (toProd p).2.1

/-- The third coordinate of a point of `SL2Tilde`, the fibre coordinate. -/
def z (p : SL2Tilde) : ℝ := (toProd p).2.2

@[simp] theorem x_mk (a b c : ℝ) : (mk a b c).x = a := (rfl)

@[simp] theorem y_mk (a b c : ℝ) : (mk a b c).y = b := (rfl)

@[simp] theorem z_mk (a b c : ℝ) : (mk a b c).z = c := (rfl)

@[simp] theorem toProd_mk (a b c : ℝ) : toProd (mk a b c) = (a, b, c) := (rfl)

@[simp] theorem x_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).x = r.1 := (rfl)

@[simp] theorem y_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).y = r.2.1 := (rfl)

@[simp] theorem z_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).z = r.2.2 := (rfl)

@[simp] theorem fst_toProd (p : SL2Tilde) : (toProd p).1 = p.x := (rfl)

@[simp] theorem fst_snd_toProd (p : SL2Tilde) : (toProd p).2.1 = p.y := (rfl)

@[simp] theorem snd_snd_toProd (p : SL2Tilde) : (toProd p).2.2 = p.z := (rfl)

/-- A point of `SL2Tilde` is determined by its coordinates. -/
@[ext]
theorem ext {p q : SL2Tilde} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q :=
  toProd.injective (Prod.ext hx (Prod.ext hy hz))

@[simp]
theorem mk_x_y_z (p : SL2Tilde) : mk p.x p.y p.z = p := (rfl)

/-! ### The metric -/

/-- The coordinate functional `x`. -/
private def xL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- The coordinate functional `y`. -/
private def yL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The coordinate functional `z`. -/
private def zL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The bilinear form `e^{-2t} dx² + dy² + (dz + e^{-t} dx)²` on `ℝ³`. -/
private def form (t : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (exp (-2 * t) • xL).smulRight xL + yL.smulRight yL +
    (zL + exp (-t) • xL).smulRight (zL + exp (-t) • xL)

private theorem form_apply (t : ℝ) (v w : ℝ × ℝ × ℝ) :
    form t v w = exp (-2 * t) * v.1 * w.1 + v.2.1 * w.2.1 +
      (v.2.2 + exp (-t) * v.1) * (w.2.2 + exp (-t) * w.1) := by
  simp [form, xL, yL, zL]
  ring

private theorem contDiff_form : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ form r.2.1 := by
  have hy : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ r.2.1 := yL.contDiff
  have h : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ zL + exp (-r.2.1) • xL :=
    contDiff_const.add (hy.neg.exp.smul_const _)
  unfold form
  exact ((((contDiff_const.mul hy).exp.smul_const _).smulRight contDiff_const).add
    contDiff_const).add (h.smulRight h)

private theorem isCoercive_form (t : ℝ) : IsCoercive (form t) := by
  refine ⟨exp (-2 * |t|) / 3, by positivity, fun v ↦ ?_⟩
  have h₁ : exp (-2 * |t|) ≤ exp (-2 * t) := exp_le_exp.2 (by linarith [le_abs_self t])
  have h₂ : exp (-2 * |t|) ≤ 1 := exp_le_one_iff.2 (by linarith [abs_nonneg t])
  have h₃ : exp (-2 * t) = exp (-t) * exp (-t) := by rw [← exp_add]; ring_nf
  -- The square of the sup norm of `ℝ³` is at most the sum of the squares of the coordinates.
  have hv : ‖v‖ ≤ √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;>
      refine Real.abs_le_sqrt ?_ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
  have hv' : ‖v‖ * ‖v‖ ≤ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 :=
    (mul_self_le_mul_self (norm_nonneg v) hv).trans (Real.mul_self_sqrt (by positivity)).le
  -- With `u = e^{-t} v₁`, the form is `u² + v₂² + (v₃ + u)²`, which is at least
  -- `(u² + v₂² + v₃²) / 3` because `5 u² + 6 u v₃ + 2 v₃² ≥ 0`.
  set u := exp (-t) * v.1 with hu
  have key : (exp (-2 * t) * v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) / 3 ≤ form t v v := by
    rw [form_apply, h₃]
    nlinarith [sq_nonneg (5 * u + 3 * v.2.2), sq_nonneg v.2.2, sq_nonneg v.2.1]
  calc exp (-2 * |t|) / 3 * ‖v‖ * ‖v‖
      = exp (-2 * |t|) / 3 * (‖v‖ * ‖v‖) := by ring
    _ ≤ exp (-2 * |t|) / 3 * (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) :=
        mul_le_mul_of_nonneg_left hv' (by positivity)
    _ ≤ (exp (-2 * t) * v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) / 3 := by
        nlinarith [mul_le_mul_of_nonneg_right h₁ (sq_nonneg v.1),
          mul_le_mul_of_nonneg_right h₂ (sq_nonneg v.2.1),
          mul_le_mul_of_nonneg_right h₂ (sq_nonneg v.2.2)]
    _ ≤ form t v v := key

/-- The analytic Riemannian metric `e^{-2y} dx² + dy² + (dz + e^{-y} dx)²` of `SL₂ℝ~`: the metric
`coerciveRiemannianMetric` of `ℝ × ℝ × ℝ` for this field of bilinear forms, read on the type
synonym `SL2Tilde`. -/
def riemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ)
      (fun p : SL2Tilde ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  coerciveRiemannianMetric (fun r : ℝ × ℝ × ℝ ↦ form r.2.1) contDiff_form
    (fun r v w ↦ by rw [form_apply, form_apply]; ring) fun r ↦ isCoercive_form r.2.1

/-- The metric of `SL₂ℝ~` at `p` is `e^{-2y} v₁ w₁ + v₂ w₂ + (v₃ + e^{-y} v₁) (w₃ + e^{-y} w₁)`,
where `y` is the second coordinate of `p` and the tangent vectors are read in the model space
`ℝ³`. -/
@[simp]
theorem riemannianMetric_inner (p : SL2Tilde) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    riemannianMetric.inner p v w =
      exp (-2 * p.y) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1 +
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1 +
        ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2 +
            exp (-p.y) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1) *
          ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.2 +
            exp (-p.y) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1) :=
  (coerciveRiemannianMetric_inner _ _ _ _ (toProd p) v w).trans (form_apply _ _ _)

/-- `SL2Tilde` carries the metric `e^{-2y} dx² + dy² + (dz + e^{-y} dx)²`. -/
instance : RiemannianBundle (fun p : SL2Tilde ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  ⟨riemannianMetric.toRiemannianMetric⟩

/-- The metric of `SL₂ℝ~` is analytic. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ)
    (fun p : SL2Tilde ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  Bundle.instIsContMDiffRiemannianBundle riemannianMetric

/-- The metric of `SL₂ℝ~` is continuous, as the Riemannian volume construction requires. -/
instance : IsContinuousRiemannianBundle (ℝ × ℝ × ℝ)
    (fun p : SL2Tilde ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  Bundle.instIsContinuousRiemannianBundle riemannianMetric.toContinuousRiemannianMetric

/-- The inner product of two tangent vectors `v`, `w` at a point `p` of `SL₂ℝ~` is
`e^{-2y} v₁ w₁ + v₂ w₂ + (v₃ + e^{-y} v₁) (w₃ + e^{-y} w₁)`, where `y` is the second coordinate
of `p`. -/
@[simp]
theorem inner_def (p : SL2Tilde) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    inner ℝ v w =
      exp (-2 * p.y) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1 +
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1 +
        ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2 +
            exp (-p.y) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1) *
          ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.2 +
            exp (-p.y) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1) :=
  riemannianMetric_inner p v w

/-! ### A transitive family of isometries -/

/-- The map `(x, y, z) ↦ (eˢ x + a, y + s, z + c)`. -/
private def translateFun (a s c : ℝ) (p : SL2Tilde) : SL2Tilde :=
  mk (exp s * p.x + a) (p.y + s) (p.z + c)

private theorem translateFun_translateFun_neg (a s c : ℝ) (p : SL2Tilde) :
    translateFun a s c (translateFun (-(exp (-s) * a)) (-s) (-c) p) = p := by
  ext <;> simp [translateFun, mul_add, ← mul_assoc, ← exp_add]

private theorem translateFun_neg_translateFun (a s c : ℝ) (p : SL2Tilde) :
    translateFun (-(exp (-s) * a)) (-s) (-c) (translateFun a s c p) = p := by
  ext <;> simp [translateFun, mul_add, ← mul_assoc, ← exp_add]

/-- The linear part `(v₁, v₂, v₃) ↦ (eˢ v₁, v₂, v₃)` of `translateFun a s c`. -/
private def linearPart (s : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  (exp s • xL).prod (yL.prod zL)

/-- In coordinates, `translateFun a s c` is the affine map with linear part `linearPart s` and
translation part `(a, s, c)`. -/
private theorem translateFun_eq (a s c : ℝ) :
    translateFun a s c = toProd.symm ∘ (fun r ↦ linearPart s r + (a, s, c)) ∘ toProd := by
  funext p
  ext <;> simp [translateFun, linearPart, xL, yL, zL]

/- `SL2Tilde` has the charts of `ℝ × ℝ × ℝ` and `toProd` is the identity, so the two results
below are the corresponding statements about the affine map `r ↦ linearPart s r + (a, s, c)` of
`ℝ × ℝ × ℝ`. -/

private theorem contMDiff_translateFun {n : ℕ∞ω} (a s c : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) n (translateFun a s c) := by
  rw [translateFun_eq]
  exact ((linearPart s).contDiff.add contDiff_const).contMDiff

private theorem hasMFDerivAt_translateFun (a s c : ℝ) (p : SL2Tilde) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c) p (linearPart s) := by
  rw [translateFun_eq]
  exact ((linearPart s).hasFDerivAt.add_const (a, s, c)).hasMFDerivAt

/-- The differential of `translateFun a s c`, read in the model space, is `linearPart s`. -/
private theorem tangentSpaceCastModel_mfderiv_translateFun (a s c : ℝ) (p : SL2Tilde)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c) p v) =
      linearPart s (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v) :=
  congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p →L[ℝ]
      TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c p) ↦
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c p) (L v))
    (hasMFDerivAt_translateFun a s c p).mfderiv

/-- `translateFun a s c` preserves the inner product of tangent vectors. -/
private theorem inner_mfderiv_translateFun (a s c : ℝ) (p : SL2Tilde)
    (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c) p v)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (translateFun a s c) p w) =
      inner ℝ v w := by
  rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_translateFun,
    tangentSpaceCastModel_mfderiv_translateFun]
  set v' := tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v
  set w' := tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w
  have h₁ : exp (-2 * (p.y + s)) * exp s * exp s = exp (-2 * p.y) := by
    rw [← exp_add, ← exp_add]
    ring_nf
  have h₂ : exp (-(p.y + s)) * exp s = exp (-p.y) := by
    rw [← exp_add]
    ring_nf
  simp only [translateFun, y_mk, linearPart, xL, yL, zL, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul]
  linear_combination v'.1 * w'.1 * h₁ +
    (v'.2.2 * w'.1 + v'.1 * w'.2.2 + (exp (-(p.y + s)) * exp s + exp (-p.y)) * v'.1 * w'.1) * h₂

/-- The isometry `(x, y, z) ↦ (eˢ x + a, y + s, z + c)` of `SL₂ℝ~`: the lift of the hyperbolic
isometry `w ↦ eˢ w + a` of the upper half-plane, followed by the translation by `c` along the
fibres. -/
def translate (a s c : ℝ) : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) SL2Tilde where
  toFun := translateFun a s c
  invFun := translateFun (-(exp (-s) * a)) (-s) (-c)
  left_inv := translateFun_neg_translateFun a s c
  right_inv := translateFun_translateFun_neg a s c
  contMDiff_toFun := contMDiff_translateFun a s c
  contMDiff_invFun := contMDiff_translateFun _ _ _
  inner_mfderiv' := inner_mfderiv_translateFun a s c

@[simp]
theorem x_translate (a s c : ℝ) (p : SL2Tilde) : (translate a s c p).x = exp s * p.x + a :=
  (rfl)

@[simp]
theorem y_translate (a s c : ℝ) (p : SL2Tilde) : (translate a s c p).y = p.y + s := (rfl)

@[simp]
theorem z_translate (a s c : ℝ) (p : SL2Tilde) : (translate a s c p).z = p.z + c := (rfl)

/-- The isometry `translate 0 0 0` is the identity. -/
@[simp]
theorem translate_zero : translate 0 0 0 = 1 :=
  RiemannianIsometry.ext fun p ↦ by ext <;> simp [RiemannianIsometry.one_apply]

/-- The isometries `translate a s c` compose as the group `Aff⁺(ℝ) × ℝ`: the affine maps
`w ↦ eˢ w + a` compose by `(a, s) * (a', s') = (eˢ a' + a, s + s')`, and the fibre translations
add. -/
@[simp]
theorem translate_mul_translate (a s c a' s' c' : ℝ) :
    translate a s c * translate a' s' c' = translate (exp s * a' + a) (s + s') (c + c') :=
  RiemannianIsometry.ext fun p ↦ by
    ext <;> simp [RiemannianIsometry.mul_apply, exp_add] <;> ring

/-- The inverse of `translate a s c` is `translate (-(e^{-s} a)) (-s) (-c)`. -/
@[simp]
theorem translate_inv (a s c : ℝ) :
    (translate a s c)⁻¹ = translate (-(exp (-s) * a)) (-s) (-c) :=
  inv_eq_of_mul_eq_one_left <| by
    rw [translate_mul_translate, ← translate_zero]
    congr 1 <;> simp

/-- Distinct parameters give distinct isometries: `translate a s c` sends the point `(0, 0, 0)` to
`(a, s, c)`. -/
@[simp]
theorem translate_inj {a s c a' s' c' : ℝ} :
    translate a s c = translate a' s' c' ↔ a = a' ∧ s = s' ∧ c = c' := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hs, hc⟩ ↦ ha ▸ hs ▸ hc ▸ rfl⟩
  have h₀ := DFunLike.congr_fun h (mk 0 0 0)
  exact ⟨by simpa using congrArg x h₀, by simpa using congrArg y h₀, by simpa using congrArg z h₀⟩

/-- The isometry `translate (q.x - e^{q.y - p.y} p.x) (q.y - p.y) (q.z - p.z)` sends `p` to
`q`. -/
theorem translate_apply_eq (p q : SL2Tilde) :
    translate (q.x - exp (q.y - p.y) * p.x) (q.y - p.y) (q.z - p.z) p = q := by
  ext <;> simp

/-- The isometry group of `SL₂ℝ~` acts transitively: `SL₂ℝ~` is a homogeneous Riemannian
manifold. Already the isometries `translate a s c` act transitively. -/
instance isPretransitive_isom :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) SL2Tilde) SL2Tilde :=
  ⟨fun p q ↦ ⟨_, translate_apply_eq p q⟩⟩

end SL2Tilde

end TauCeti
