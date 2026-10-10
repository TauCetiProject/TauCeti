/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Coercive
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

/-!
# The model geometry Sol

`Sol` is `ℝ³`, with coordinates `(x, y, z)`, carrying the Riemannian metric
`e^{2z} dx² + e^{-2z} dy² + dz²`. It is one of Thurston's eight model geometries of
three-manifolds, the geometry of torus bundles over the circle with Anosov monodromy.

`Sol` is also the solvable Lie group `ℝ² ⋊ ℝ` in which `ℝ` acts on `ℝ²` by
`t • (x, y) = (e^{-t} x, e^{t} y)`: the product is
`(a, b, c) * (x, y, z) = (e^{-c} x + a, e^{c} y + b, c + z)`. The metric is left-invariant, so
left multiplication by any element is a Riemannian isometry. This gives an injective group
homomorphism from `Sol` into its isometry group, and already its image acts transitively, so
`Sol` is a homogeneous Riemannian manifold.

## Main definitions

* `TauCeti.Sol`: the model geometry Sol, with the coordinate equivalence `Sol.toProd` to `ℝ³`,
  its smooth version `Sol.toProdDiffeomorph`, and the coordinates `Sol.x`, `Sol.y`, `Sol.z`.
* `TauCeti.Sol.instGroup`: the group structure of `Sol`.
* `TauCeti.Sol.riemannianMetric`: the analytic metric `e^{2z} dx² + e^{-2z} dy² + dz²`, which is
  the `RiemannianBundle` instance of `Sol`.
* `TauCeti.Sol.toIsom`: left multiplication, as a homomorphism from `Sol` to its isometry group.

## Main results

* `TauCeti.Sol.inner_def`: the inner product of two tangent vectors at a point of height `z` is
  `e^{2z} v₁ w₁ + e^{-2z} v₂ w₂ + v₃ w₃`.
* `TauCeti.Sol.toIsom_injective`: distinct elements of `Sol` give distinct isometries.
* `TauCeti.Sol.isPretransitive_isom`: the isometry group of `Sol` acts transitively on it.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §3.8
  (the eight model geometries).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487, §5
  (the geometry Sol and its metric).
-/

public section

open Bundle Manifold Real
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

/-- Thurston's model geometry Sol: the space `ℝ³`, with coordinates `(x, y, z)`, carrying the
left-invariant Riemannian metric `e^{2z} dx² + e^{-2z} dy² + dz²` of the solvable Lie group
`ℝ² ⋊ ℝ`. -/
def Sol : Type := ℝ × ℝ × ℝ

namespace Sol

/-- The coordinates `(x, y, z)` of a point of `Sol`, as an equivalence with `ℝ³`. -/
def toProd : Sol ≃ ℝ × ℝ × ℝ := Equiv.refl _

/- `Sol` is a type synonym for `ℝ × ℝ × ℝ`, so that it can carry its own group structure and
`RiemannianBundle` instance. Its topology and charts are those of `ℝ × ℝ × ℝ`. -/

instance : TopologicalSpace Sol := inferInstanceAs (TopologicalSpace (ℝ × ℝ × ℝ))

instance : T2Space Sol := inferInstanceAs (T2Space (ℝ × ℝ × ℝ))

/-- Sol is contractible: its underlying topology is that of real three-space. -/
instance : ContractibleSpace Sol := inferInstanceAs (ContractibleSpace (ℝ × ℝ × ℝ))

instance : ChartedSpace (ℝ × ℝ × ℝ) Sol := inferInstanceAs (ChartedSpace (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ))

instance : IsManifold 𝓘(ℝ, ℝ × ℝ × ℝ) ω Sol :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ))

/-- The point of `Sol` with coordinates `(x, y, z)`. -/
def mk (x y z : ℝ) : Sol := toProd.symm (x, y, z)

/-- The first coordinate of a point of `Sol`. -/
def x (p : Sol) : ℝ := (toProd p).1

/-- The second coordinate of a point of `Sol`. -/
def y (p : Sol) : ℝ := (toProd p).2.1

/-- The third coordinate, or height, of a point of `Sol`. -/
def z (p : Sol) : ℝ := (toProd p).2.2

@[simp] theorem x_mk (a b c : ℝ) : (mk a b c).x = a := (rfl)

@[simp] theorem y_mk (a b c : ℝ) : (mk a b c).y = b := (rfl)

@[simp] theorem z_mk (a b c : ℝ) : (mk a b c).z = c := (rfl)

@[simp] theorem toProd_mk (a b c : ℝ) : toProd (mk a b c) = (a, b, c) := (rfl)

@[simp] theorem x_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).x = r.1 := (rfl)

@[simp] theorem y_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).y = r.2.1 := (rfl)

@[simp] theorem z_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).z = r.2.2 := (rfl)

@[simp] theorem fst_toProd (p : Sol) : (toProd p).1 = p.x := (rfl)

@[simp] theorem fst_snd_toProd (p : Sol) : (toProd p).2.1 = p.y := (rfl)

@[simp] theorem snd_snd_toProd (p : Sol) : (toProd p).2.2 = p.z := (rfl)

/-- A point of `Sol` is determined by its coordinates. -/
@[ext]
theorem ext {p q : Sol} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q :=
  toProd.injective (Prod.ext hx (Prod.ext hy hz))

@[simp]
theorem mk_x_y_z (p : Sol) : mk p.x p.y p.z = p := (rfl)

/-- The global coordinate diffeomorphism of Sol with real three-space. -/
def toProdDiffeomorph : Sol ≃ₘ⟮𝓘(ℝ, ℝ × ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ × ℝ)⟯
    (ℝ × ℝ × ℝ) where
  toEquiv := toProd
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id

@[simp] theorem coe_toProdDiffeomorph : ⇑toProdDiffeomorph = toProd := (rfl)

@[simp] theorem coe_toProdDiffeomorph_symm : ⇑toProdDiffeomorph.symm = toProd.symm := (rfl)

/-- The differential of the global coordinates reads a tangent vector in the model of Sol. -/
@[simp] theorem mfderiv_toProd_apply (p : Sol) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) toProd p v =
      tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v := by
  exact congrArg (fun L => L v)
    (ContinuousLinearMap.id ℝ (ℝ × ℝ × ℝ)).hasFDerivAt.hasMFDerivAt.mfderiv

/-- The differential of the inverse global coordinates retains the model vector. -/
@[simp] theorem tangentSpaceCastModel_mfderiv_toProd_symm (p : ℝ × ℝ × ℝ)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (toProd.symm p)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) toProd.symm p v) = v := by
  exact congrArg (fun L => L v)
    (ContinuousLinearMap.id ℝ (ℝ × ℝ × ℝ)).hasFDerivAt.hasMFDerivAt.mfderiv

/-! ### The group structure -/

/-- The product `(a, b, c) * (x, y, z) = (e^{-c} x + a, e^{c} y + b, c + z)` of the semidirect
product `ℝ² ⋊ ℝ`. -/
instance : Mul Sol := ⟨fun p q ↦ mk (exp (-p.z) * q.x + p.x) (exp p.z * q.y + p.y) (p.z + q.z)⟩

instance : One Sol := ⟨mk 0 0 0⟩

instance : Inv Sol := ⟨fun p ↦ mk (-(exp p.z * p.x)) (-(exp (-p.z) * p.y)) (-p.z)⟩

@[simp] theorem x_mul (p q : Sol) : (p * q).x = exp (-p.z) * q.x + p.x := (rfl)

@[simp] theorem y_mul (p q : Sol) : (p * q).y = exp p.z * q.y + p.y := (rfl)

@[simp] theorem z_mul (p q : Sol) : (p * q).z = p.z + q.z := (rfl)

@[simp] theorem x_one : (1 : Sol).x = 0 := (rfl)

@[simp] theorem y_one : (1 : Sol).y = 0 := (rfl)

@[simp] theorem z_one : (1 : Sol).z = 0 := (rfl)

@[simp] theorem x_inv (p : Sol) : p⁻¹.x = -(exp p.z * p.x) := (rfl)

@[simp] theorem y_inv (p : Sol) : p⁻¹.y = -(exp (-p.z) * p.y) := (rfl)

@[simp] theorem z_inv (p : Sol) : p⁻¹.z = -p.z := (rfl)

/-- `Sol` is a group: the semidirect product `ℝ² ⋊ ℝ` in which `t ∈ ℝ` acts on `ℝ²` by
`(x, y) ↦ (e^{-t} x, e^{t} y)`. -/
instance instGroup : Group Sol where
  mul_assoc p q r := by
    ext <;> simp [exp_add] <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext <;> simp

/-! ### The metric -/

/-- The coordinate functional `x`. -/
private def xL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- The coordinate functional `y`. -/
private def yL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The coordinate functional `z`. -/
private def zL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The bilinear form `e^{2t} dx² + e^{-2t} dy² + dz²` on `ℝ³`. -/
private def form (t : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (exp (2 * t) • xL).smulRight xL + (exp (-2 * t) • yL).smulRight yL + zL.smulRight zL

private theorem form_apply (t : ℝ) (v w : ℝ × ℝ × ℝ) :
    form t v w = exp (2 * t) * v.1 * w.1 + exp (-2 * t) * v.2.1 * w.2.1 + v.2.2 * w.2.2 := by
  simp [form, xL, yL, zL]

private theorem contDiff_form : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ form r.2.2 := by
  have hz : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ r.2.2 := zL.contDiff
  unfold form
  exact ((((contDiff_const.mul hz).exp.smul_const _).smulRight contDiff_const).add
    (((contDiff_const.mul hz).exp.smul_const _).smulRight contDiff_const)).add contDiff_const

private theorem isCoercive_form (t : ℝ) : IsCoercive (form t) := by
  refine ⟨exp (-2 * |t|), exp_pos _, fun v ↦ ?_⟩
  have h₁ : exp (-2 * |t|) ≤ exp (2 * t) := exp_le_exp.2 (by linarith [neg_abs_le t])
  have h₂ : exp (-2 * |t|) ≤ exp (-2 * t) := exp_le_exp.2 (by linarith [le_abs_self t])
  have h₃ : exp (-2 * |t|) ≤ 1 := exp_le_one_iff.2 (by linarith [abs_nonneg t])
  -- The square of the sup norm of `ℝ³` is at most the sum of the squares of the coordinates.
  have hv : ‖v‖ * ‖v‖ ≤ v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2 := by
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := abs_mul_abs_self v.1
    have h2 := abs_mul_abs_self v.2.1
    have h3 := abs_mul_abs_self v.2.2
    rcases max_choice |v.1| (max |v.2.1| |v.2.2|) with h | h <;> rw [h]
    · nlinarith [mul_self_nonneg v.2.1, mul_self_nonneg v.2.2]
    · rcases max_choice |v.2.1| |v.2.2| with h' | h' <;> rw [h'] <;>
        nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2.1, mul_self_nonneg v.2.2]
  rw [form_apply, mul_assoc]
  calc exp (-2 * |t|) * (‖v‖ * ‖v‖)
      ≤ exp (-2 * |t|) * (v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2) :=
        mul_le_mul_of_nonneg_left hv (exp_pos _).le
    _ ≤ exp (2 * t) * v.1 * v.1 + exp (-2 * t) * v.2.1 * v.2.1 + v.2.2 * v.2.2 := by
        nlinarith [mul_le_mul_of_nonneg_right h₁ (mul_self_nonneg v.1),
          mul_le_mul_of_nonneg_right h₂ (mul_self_nonneg v.2.1),
          mul_le_mul_of_nonneg_right h₃ (mul_self_nonneg v.2.2)]

/-- The analytic Riemannian metric `e^{2z} dx² + e^{-2z} dy² + dz²` of `Sol`: the metric
`coerciveRiemannianMetric` of `ℝ × ℝ × ℝ` for this field of bilinear forms, read on the type
synonym `Sol`. -/
def riemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ)
      (fun p : Sol ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  coerciveRiemannianMetric (fun r : ℝ × ℝ × ℝ ↦ form r.2.2) contDiff_form
    (fun r v w ↦ by rw [form_apply, form_apply]; ring) fun r ↦ isCoercive_form r.2.2

/-- The metric of `Sol` at `p` is `e^{2z} v₁ w₁ + e^{-2z} v₂ w₂ + v₃ w₃`, where `z` is the height
of `p` and the tangent vectors are read in the model space `ℝ³`. -/
@[simp]
theorem riemannianMetric_inner (p : Sol) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    riemannianMetric.inner p v w =
      exp (2 * p.z) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1 +
        exp (-2 * p.z) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1 +
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.2 :=
  (coerciveRiemannianMetric_inner _ _ _ _ (toProd p) v w).trans (form_apply _ _ _)

/-- `Sol` carries the metric `e^{2z} dx² + e^{-2z} dy² + dz²`. -/
instance : RiemannianBundle (fun p : Sol ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  ⟨riemannianMetric.toRiemannianMetric⟩

/-- The metric of `Sol` is analytic. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ)
    (fun p : Sol ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  Bundle.instIsContMDiffRiemannianBundle riemannianMetric

/-- The metric of `Sol` is continuous, as the Riemannian volume construction requires. -/
instance : IsContinuousRiemannianBundle (ℝ × ℝ × ℝ)
    (fun p : Sol ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  Bundle.instIsContinuousRiemannianBundle riemannianMetric.toContinuousRiemannianMetric

/-- The inner product of two tangent vectors `v`, `w` at a point `p` of `Sol` is
`e^{2z} v₁ w₁ + e^{-2z} v₂ w₂ + v₃ w₃`, where `z` is the height of `p`. -/
@[simp]
theorem inner_def (p : Sol) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    inner ℝ v w =
      exp (2 * p.z) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1 +
        exp (-2 * p.z) * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1 +
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.2 :=
  riemannianMetric_inner p v w

/-! ### Left multiplication is an isometry -/

/-- The linear part `(v₁, v₂, v₃) ↦ (e^{-c} v₁, e^{c} v₂, v₃)` of left multiplication by a point
`p` of height `c`. -/
private def linearPart (p : Sol) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  (exp (-p.z) • xL).prod ((exp p.z • yL).prod zL)

/-- In coordinates, left multiplication by `p` is the affine map with linear part
`linearPart p` and translation part `p`. -/
private theorem mul_left_eq (p : Sol) :
    (p * ·) = toProd.symm ∘ (fun r ↦ linearPart p r + toProd p) ∘ toProd := by
  funext q
  ext <;> simp [linearPart, xL, yL, zL, add_comm]

/- `Sol` has the charts of `ℝ × ℝ × ℝ` and `toProd` is the identity, so the two results below
are the corresponding statements about the affine map `r ↦ linearPart p r + toProd p` of
`ℝ × ℝ × ℝ`. -/

private theorem contMDiff_mul_left {n : ℕ∞ω} (p : Sol) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) n (p * ·) := by
  rw [mul_left_eq]
  exact ((linearPart p).contDiff.add contDiff_const).contMDiff

private theorem hasMFDerivAt_mul_left (p q : Sol) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q (linearPart p) := by
  rw [mul_left_eq]
  exact ((linearPart p).hasFDerivAt.add_const (toProd p)).hasMFDerivAt

/-- The differential of left multiplication by `p`, read in the model space, is
`linearPart p`. -/
private theorem tangentSpaceCastModel_mfderiv_mul_left (p q : Sol)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (p * q)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q v) =
      linearPart p (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q v) :=
  congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (p * q) ↦
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (p * q) (L v)) (hasMFDerivAt_mul_left p q).mfderiv

/-- Left multiplication by `p` preserves the inner product of tangent vectors. -/
private theorem inner_mfderiv_mul_left (p q : Sol) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q v)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q w) =
      inner ℝ v w := by
  rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_mul_left,
    tangentSpaceCastModel_mfderiv_mul_left]
  have h₁ : exp (2 * (p * q).z) * exp (-p.z) * exp (-p.z) = exp (2 * q.z) := by
    rw [← exp_add, ← exp_add, z_mul]
    ring_nf
  have h₂ : exp (-2 * (p * q).z) * exp p.z * exp p.z = exp (-2 * q.z) := by
    rw [← exp_add, ← exp_add, z_mul]
    ring_nf
  simp only [linearPart, xL, yL, zL, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul]
  linear_combination
    (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q v).1 *
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q w).1 * h₁ +
      (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q v).2.1 *
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q w).2.1 * h₂

/-- Left multiplication by `p`, as an isometry of `Sol`. -/
private def mulLeft (p : Sol) : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol where
  toFun := (p * ·)
  invFun := (p⁻¹ * ·)
  left_inv q := inv_mul_cancel_left p q
  right_inv q := mul_inv_cancel_left p q
  contMDiff_toFun := contMDiff_mul_left p
  contMDiff_invFun := contMDiff_mul_left p⁻¹
  inner_mfderiv' q v w := by
    -- The underlying map of the diffeomorphism under construction is `(p * ·)` by definition;
    -- `change` states the goal in terms of that function, so that its differential applies.
    change inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q v)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q w) = inner ℝ v w
    exact inner_mfderiv_mul_left p q v w

private theorem mulLeft_apply (p q : Sol) : mulLeft p q = p * q := (rfl)

/-- Left multiplication, as a group homomorphism from `Sol` to its isometry group: the metric
of `Sol` is left-invariant. -/
def toIsom : Sol →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol where
  toFun := mulLeft
  map_one' := RiemannianIsometry.ext fun q ↦ by
    rw [mulLeft_apply, RiemannianIsometry.one_apply, one_mul]
  map_mul' p p' := RiemannianIsometry.ext fun q ↦ by
    rw [RiemannianIsometry.mul_apply, mulLeft_apply, mulLeft_apply, mulLeft_apply, mul_assoc]

/-- The isometry `toIsom p` is left multiplication by `p`. -/
@[simp]
theorem toIsom_apply (p q : Sol) : toIsom p q = p * q := (rfl)

/-- Distinct elements of `Sol` act by distinct isometries. -/
theorem toIsom_injective : Function.Injective toIsom := fun p p' h ↦ by
  simpa using DFunLike.congr_fun h 1

/-- The isometry group of `Sol` acts transitively: `Sol` is a homogeneous Riemannian manifold.
This is transferred along `toIsom` from the transitive action of `Sol` on itself by left
multiplication. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol) Sol :=
  .of_smul_eq toIsom fun {_ _} ↦ by rw [RiemannianIsometry.smul_def, toIsom_apply, smul_eq_mul]

end Sol

end TauCeti
