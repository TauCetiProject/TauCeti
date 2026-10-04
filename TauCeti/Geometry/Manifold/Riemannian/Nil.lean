/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg
public import TauCeti.Geometry.Manifold.Riemannian.Coercive
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

/-!
# The model geometry Nil

`Nil` is `ℝ³`, with coordinates `(x, y, z)`, carrying the Riemannian metric
`dx² + dy² + (dz - x dy)²`. It is one of Thurston's eight model geometries of three-manifolds,
the geometry of the Seifert fibred spaces with Euclidean base orbifold and nonzero Euler number,
such as the circle bundles of nonzero Euler number over the torus.

`Nil` is also the real Heisenberg group `TauCeti.HeisenbergGroup ℝ` of unipotent upper triangular
`3 × 3` matrices, whose product in the coordinates of the strictly upper triangle is
`(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)`; the coordinates give a group isomorphism
`Nil.toHeisenberg`. The one-forms `dx`, `dy` and `dz - x dy` are left-invariant, so the metric is
left-invariant and left multiplication by any element is a Riemannian isometry. This gives an
injective group homomorphism from `Nil` into its isometry group, and already its image acts
transitively, so `Nil` is a homogeneous Riemannian manifold.

## Main definitions

* `TauCeti.Nil`: the model geometry Nil, with the coordinate equivalence `Nil.toProd` to `ℝ³`
  and the coordinates `Nil.x`, `Nil.y`, `Nil.z`.
* `TauCeti.Nil.instGroup`: the group structure of `Nil`, and `TauCeti.Nil.toHeisenberg`, the
  group isomorphism with the real Heisenberg group.
* `TauCeti.Nil.riemannianMetric`: the analytic metric `dx² + dy² + (dz - x dy)²`, which is the
  `RiemannianBundle` instance of `Nil`.
* `TauCeti.Nil.toIsom`: left multiplication, as a homomorphism from `Nil` to its isometry group.

## Main results

* `TauCeti.Nil.inner_def`: the inner product of two tangent vectors at a point with first
  coordinate `x` is `v₁ w₁ + v₂ w₂ + (v₃ - x v₂) (w₃ - x w₂)`.
* `TauCeti.Nil.toIsom_injective`: distinct elements of `Nil` give distinct isometries.
* `TauCeti.Nil.isPretransitive_isom`: the isometry group of `Nil` acts transitively on it.

## Implementation notes

`Nil` is a type synonym for `ℝ × ℝ × ℝ` rather than for `HeisenbergGroup ℝ`, following
`TauCeti.Sol`: its charts are then those of the model space `ℝ × ℝ × ℝ` itself, and the metric
is a field of bilinear forms on that space (`TauCeti.coerciveRiemannianMetric`).

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §3.8
  (the eight model geometries).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487
  (the geometry Nil and its metric).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

/-- Thurston's model geometry Nil: the space `ℝ³`, with coordinates `(x, y, z)`, carrying the
left-invariant Riemannian metric `dx² + dy² + (dz - x dy)²` of the real Heisenberg group. -/
def Nil : Type := ℝ × ℝ × ℝ

namespace Nil

/-- The coordinates `(x, y, z)` of a point of `Nil`, as an equivalence with `ℝ³`. -/
def toProd : Nil ≃ ℝ × ℝ × ℝ := Equiv.refl _

/- `Nil` is a type synonym for `ℝ × ℝ × ℝ`, so that it can carry its own group structure and
`RiemannianBundle` instance. Its topology and charts are those of `ℝ × ℝ × ℝ`. -/

instance : TopologicalSpace Nil := inferInstanceAs (TopologicalSpace (ℝ × ℝ × ℝ))

instance : T2Space Nil := inferInstanceAs (T2Space (ℝ × ℝ × ℝ))

/-- Nil is contractible: its underlying topology is that of real three-space. -/
instance : ContractibleSpace Nil := inferInstanceAs (ContractibleSpace (ℝ × ℝ × ℝ))

instance : ChartedSpace (ℝ × ℝ × ℝ) Nil := inferInstanceAs (ChartedSpace (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ))

instance : IsManifold 𝓘(ℝ, ℝ × ℝ × ℝ) ω Nil :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ))

/-- The point of `Nil` with coordinates `(x, y, z)`. -/
def mk (x y z : ℝ) : Nil := toProd.symm (x, y, z)

/-- The first coordinate of a point of `Nil`. -/
def x (p : Nil) : ℝ := (toProd p).1

/-- The second coordinate of a point of `Nil`. -/
def y (p : Nil) : ℝ := (toProd p).2.1

/-- The third coordinate of a point of `Nil`. -/
def z (p : Nil) : ℝ := (toProd p).2.2

@[simp] theorem x_mk (a b c : ℝ) : (mk a b c).x = a := (rfl)

@[simp] theorem y_mk (a b c : ℝ) : (mk a b c).y = b := (rfl)

@[simp] theorem z_mk (a b c : ℝ) : (mk a b c).z = c := (rfl)

@[simp] theorem toProd_mk (a b c : ℝ) : toProd (mk a b c) = (a, b, c) := (rfl)

@[simp] theorem x_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).x = r.1 := (rfl)

@[simp] theorem y_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).y = r.2.1 := (rfl)

@[simp] theorem z_toProd_symm (r : ℝ × ℝ × ℝ) : (toProd.symm r).z = r.2.2 := (rfl)

@[simp] theorem fst_toProd (p : Nil) : (toProd p).1 = p.x := (rfl)

@[simp] theorem fst_snd_toProd (p : Nil) : (toProd p).2.1 = p.y := (rfl)

@[simp] theorem snd_snd_toProd (p : Nil) : (toProd p).2.2 = p.z := (rfl)

/-- A point of `Nil` is determined by its coordinates. -/
@[ext]
theorem ext {p q : Nil} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q :=
  toProd.injective (Prod.ext hx (Prod.ext hy hz))

@[simp]
theorem mk_x_y_z (p : Nil) : mk p.x p.y p.z = p := (rfl)

/-! ### The group structure -/

/-- The product `(a, b, c) * (x, y, z) = (a + x, b + y, c + z + a y)` of the real Heisenberg
group. -/
instance : Mul Nil := ⟨fun p q ↦ mk (p.x + q.x) (p.y + q.y) (p.z + q.z + p.x * q.y)⟩

instance : One Nil := ⟨mk 0 0 0⟩

instance : Inv Nil := ⟨fun p ↦ mk (-p.x) (-p.y) (-p.z + p.x * p.y)⟩

@[simp] theorem x_mul (p q : Nil) : (p * q).x = p.x + q.x := (rfl)

@[simp] theorem y_mul (p q : Nil) : (p * q).y = p.y + q.y := (rfl)

@[simp] theorem z_mul (p q : Nil) : (p * q).z = p.z + q.z + p.x * q.y := (rfl)

@[simp] theorem x_one : (1 : Nil).x = 0 := (rfl)

@[simp] theorem y_one : (1 : Nil).y = 0 := (rfl)

@[simp] theorem z_one : (1 : Nil).z = 0 := (rfl)

@[simp] theorem x_inv (p : Nil) : p⁻¹.x = -p.x := (rfl)

@[simp] theorem y_inv (p : Nil) : p⁻¹.y = -p.y := (rfl)

@[simp] theorem z_inv (p : Nil) : p⁻¹.z = -p.z + p.x * p.y := (rfl)

/-- `Nil` is a group: the real Heisenberg group, in the coordinates of `toHeisenberg`. -/
instance instGroup : Group Nil where
  mul_assoc p q r := by
    ext <;> simp <;> ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext <;> simp

/-- The coordinates of `Nil` identify it with the real Heisenberg group of unipotent upper
triangular `3 × 3` matrices, as a group. -/
def toHeisenberg : Nil ≃* HeisenbergGroup ℝ where
  toEquiv := toProd.trans HeisenbergGroup.equivProd.symm
  map_mul' p q := by ext <;> simp

@[simp] theorem x_toHeisenberg (p : Nil) : (toHeisenberg p).x = p.x := by simp [toHeisenberg]

@[simp] theorem y_toHeisenberg (p : Nil) : (toHeisenberg p).y = p.y := by simp [toHeisenberg]

@[simp] theorem z_toHeisenberg (p : Nil) : (toHeisenberg p).z = p.z := by simp [toHeisenberg]

/-! ### The metric -/

/-- The coordinate functional `x`. -/
private def xL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- The coordinate functional `y`. -/
private def yL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The coordinate functional `z`. -/
private def zL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The bilinear form `dx² + dy² + (dz - t dy)²` on `ℝ³`. -/
private def form (t : ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  xL.smulRight xL + yL.smulRight yL + (zL - t • yL).smulRight (zL - t • yL)

private theorem form_apply (t : ℝ) (v w : ℝ × ℝ × ℝ) :
    form t v w = v.1 * w.1 + v.2.1 * w.2.1 + (v.2.2 - t * v.2.1) * (w.2.2 - t * w.2.1) := by
  simp [form, xL, yL, zL]

private theorem contDiff_form : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ form r.1 := by
  have h : ContDiff ℝ ω fun r : ℝ × ℝ × ℝ ↦ zL - r.1 • yL :=
    contDiff_const.sub (xL.contDiff.smul contDiff_const)
  exact (contDiff_const.add contDiff_const).add (h.smulRight h)

private theorem isCoercive_form (t : ℝ) : IsCoercive (form t) := by
  refine ⟨(2 + 2 * t ^ 2)⁻¹, by positivity, fun v ↦ ?_⟩
  -- The sup norm of `v` is at most its Euclidean norm.
  have hv : ‖v‖ ≤ √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;>
      refine Real.abs_le_sqrt ?_ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
  have hv' : ‖v‖ * ‖v‖ ≤ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 :=
    (mul_self_le_mul_self (norm_nonneg v) hv).trans (Real.mul_self_sqrt (by positivity)).le
  rw [mul_assoc, inv_mul_le_iff₀ (by positivity), form_apply]
  nlinarith [sq_nonneg (t * v.2.1 - (v.2.2 - t * v.2.1)), sq_nonneg v.1, sq_nonneg v.2.1,
    sq_nonneg (v.2.2 - t * v.2.1), mul_nonneg (sq_nonneg t) (sq_nonneg v.1),
    mul_nonneg (sq_nonneg t) (sq_nonneg (v.2.2 - t * v.2.1))]

/-- The analytic Riemannian metric `dx² + dy² + (dz - x dy)²` of `Nil`: the metric
`coerciveRiemannianMetric` of `ℝ × ℝ × ℝ` for this field of bilinear forms, read on the type
synonym `Nil`. -/
def riemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ)
      (fun p : Nil ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  coerciveRiemannianMetric (fun r : ℝ × ℝ × ℝ ↦ form r.1) contDiff_form
    (fun r v w ↦ by rw [form_apply, form_apply]; ring) fun r ↦ isCoercive_form r.1

/-- The metric of `Nil` at `p` is `v₁ w₁ + v₂ w₂ + (v₃ - x v₂) (w₃ - x w₂)`, where `x` is the first
coordinate of `p` and the tangent vectors are read in the model space `ℝ³`. -/
@[simp]
theorem riemannianMetric_inner (p : Nil) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    riemannianMetric.inner p v w =
      (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1 +
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1 +
        ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2 -
            p.x * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1) *
          ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.2 -
            p.x * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1) :=
  (coerciveRiemannianMetric_inner _ _ _ _ (toProd p) v w).trans (form_apply _ _ _)

/-- `Nil` carries the metric `dx² + dy² + (dz - x dy)²`. -/
instance : RiemannianBundle (fun p : Nil ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  ⟨riemannianMetric.toRiemannianMetric⟩

/-- The metric of `Nil` is analytic. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ × ℝ × ℝ) ω (ℝ × ℝ × ℝ)
    (fun p : Nil ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  Bundle.instIsContMDiffRiemannianBundle riemannianMetric

/-- The metric of `Nil` is continuous, as the Riemannian volume construction requires. -/
instance : IsContinuousRiemannianBundle (ℝ × ℝ × ℝ)
    (fun p : Nil ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :=
  Bundle.instIsContinuousRiemannianBundle riemannianMetric.toContinuousRiemannianMetric

/-- The inner product of two tangent vectors `v`, `w` at a point `p` of `Nil` is
`v₁ w₁ + v₂ w₂ + (v₃ - x v₂) (w₃ - x w₂)`, where `x` is the first coordinate of `p`. -/
@[simp]
theorem inner_def (p : Nil) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    inner ℝ v w =
      (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).1 +
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1 *
          (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1 +
        ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.2 -
            p.x * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v).2.1) *
          ((tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.2 -
            p.x * (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w).2.1) :=
  riemannianMetric_inner p v w

/-! ### Left multiplication is an isometry -/

/-- The linear part `(v₁, v₂, v₃) ↦ (v₁, v₂, v₃ + a v₂)` of left multiplication by a point `p`
with first coordinate `a`. -/
private def linearPart (p : Nil) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  xL.prod (yL.prod (zL + p.x • yL))

/-- In coordinates, left multiplication by `p` is the affine map with linear part
`linearPart p` and translation part `p`. -/
private theorem mul_left_eq (p : Nil) :
    (p * ·) = toProd.symm ∘ (fun r ↦ linearPart p r + toProd p) ∘ toProd := by
  funext q
  ext <;> simp [linearPart, xL, yL, zL] <;> ring

/- `Nil` has the charts of `ℝ × ℝ × ℝ` and `toProd` is the identity, so the two results below
are the corresponding statements about the affine map `r ↦ linearPart p r + toProd p` of
`ℝ × ℝ × ℝ`. -/

private theorem contMDiff_mul_left {n : ℕ∞ω} (p : Nil) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) n (p * ·) := by
  rw [mul_left_eq]
  exact ((linearPart p).contDiff.add contDiff_const).contMDiff

private theorem hasMFDerivAt_mul_left (p q : Nil) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q (linearPart p) := by
  rw [mul_left_eq]
  exact ((linearPart p).hasFDerivAt.add_const (toProd p)).hasMFDerivAt

/-- The differential of left multiplication by `p`, read in the model space, is
`linearPart p`. -/
private theorem tangentSpaceCastModel_mfderiv_mul_left (p q : Nil)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (p * q)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q v) =
      linearPart p (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q v) :=
  congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (p * q) ↦
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (p * q) (L v)) (hasMFDerivAt_mul_left p q).mfderiv

/-- Left multiplication by `p` preserves the inner product of tangent vectors. -/
private theorem inner_mfderiv_mul_left (p q : Nil) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q v)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (p * ·) q w) =
      inner ℝ v w := by
  rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_mul_left,
    tangentSpaceCastModel_mfderiv_mul_left]
  simp only [linearPart, xL, yL, zL, x_mul, ContinuousLinearMap.prod_apply, add_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul]
  ring

/-- Left multiplication by `p`, as an isometry of `Nil`. -/
private def mulLeft (p : Nil) : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Nil where
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

private theorem mulLeft_apply (p q : Nil) : mulLeft p q = p * q := (rfl)

/-- Left multiplication, as a group homomorphism from `Nil` to its isometry group: the metric
of `Nil` is left-invariant. -/
def toIsom : Nil →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Nil where
  toFun := mulLeft
  map_one' := RiemannianIsometry.ext fun q ↦ by
    rw [mulLeft_apply, RiemannianIsometry.one_apply, one_mul]
  map_mul' p p' := RiemannianIsometry.ext fun q ↦ by
    rw [RiemannianIsometry.mul_apply, mulLeft_apply, mulLeft_apply, mulLeft_apply, mul_assoc]

/-- The isometry `toIsom p` is left multiplication by `p`. -/
@[simp]
theorem toIsom_apply (p q : Nil) : toIsom p q = p * q := (rfl)

/-- Distinct elements of `Nil` act by distinct isometries. -/
theorem toIsom_injective : Function.Injective toIsom := fun p p' h ↦ by
  simpa using DFunLike.congr_fun h 1

/-- The isometry group of `Nil` acts transitively: `Nil` is a homogeneous Riemannian manifold.
This is transferred along `toIsom` from the transitive action of `Nil` on itself by left
multiplication. -/
instance isPretransitive_isom : MulAction.IsPretransitive (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Nil) Nil :=
  .of_smul_eq toIsom fun {_ _} ↦ by rw [RiemannianIsometry.smul_def, toIsom_apply, smul_eq_mul]

end Nil

end TauCeti
