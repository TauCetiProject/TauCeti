/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
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

The orthogonal group `O(2)` acts on `Nil` by group automorphisms fixing the identity. In the
coordinates `(x, y, z - x y / 2)`, in which the product is
`(a, b, c) * (x, y, z) = (a + x, b + y, c + z + (a y - b x) / 2)`, an orthogonal matrix `g` acts
by `g` on the first two coordinates and by multiplication by `det g = ± 1` on the third. These
automorphisms preserve `dx² + dy²` and multiply the form `dz - x dy` by `det g`, so they are
isometries.
Together with left translations they give an injective homomorphism from the semidirect product
`Nil ⋊ O(2)` into the isometry group of `Nil`. This is the whole isometry group of `Nil` (Scott,
Section 4), but that every isometry is of this form is not proved here.

## Main definitions

* `TauCeti.Nil`: the model geometry Nil, with the coordinate equivalence `Nil.toProd` to `ℝ³`
  and the coordinates `Nil.x`, `Nil.y`, `Nil.z`.
* `TauCeti.Nil.toProdDiffeomorph`: the smooth global coordinates in real three-space.
* `TauCeti.Nil.instGroup`: the group structure of `Nil`, and `TauCeti.Nil.toHeisenberg`, the
  group isomorphism with the real Heisenberg group.
* `TauCeti.Nil.riemannianMetric`: the analytic metric `dx² + dy² + (dz - x dy)²`, which is the
  `RiemannianBundle` instance of `Nil`.
* `TauCeti.Nil.toIsom`: left multiplication, as a homomorphism from `Nil` to its isometry group.
* `TauCeti.Nil.orthogonalMulAut`: the action of `O(2)` on `Nil` by group automorphisms.
* `TauCeti.Nil.orthogonalToIsom`: the same action, as a homomorphism from `O(2)` to the isometry
  group of `Nil`.
* `TauCeti.Nil.semidirectProductToIsom`: the homomorphism from `Nil ⋊ O(2)` to the isometry
  group of `Nil`, in which `(n, g)` acts by `p ↦ n * g p`.

## Main results

* `TauCeti.Nil.inner_def`: the inner product of two tangent vectors at a point with first
  coordinate `x` is `v₁ w₁ + v₂ w₂ + (v₃ - x v₂) (w₃ - x w₂)`.
* `TauCeti.Nil.toIsom_injective`: distinct elements of `Nil` give distinct isometries.
* `TauCeti.Nil.isPretransitive_isom`: the isometry group of `Nil` acts transitively on it.
* `TauCeti.Nil.range_orthogonalToIsom_le_stabilizer`: the orthogonal isometries fix the identity.
* `TauCeti.Nil.semidirectProductToIsom_injective`: distinct elements of `Nil ⋊ O(2)` act by
  distinct isometries.

## Implementation notes

`Nil` is a type synonym for `ℝ × ℝ × ℝ` rather than for `HeisenbergGroup ℝ`, following
`TauCeti.Sol`: its charts are then those of the model space `ℝ × ℝ × ℝ` itself, and the metric
is a field of bilinear forms on that space (`TauCeti.coerciveRiemannianMetric`).

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §3.8
  (the eight model geometries).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487,
  Section 4 (the geometry Nil, its metric and its isometry group).
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

/-- The global coordinate diffeomorphism of Nil with real three-space. -/
def toProdDiffeomorph : Nil ≃ₘ⟮𝓘(ℝ, ℝ × ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ × ℝ)⟯
    (ℝ × ℝ × ℝ) where
  toEquiv := toProd
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id

@[simp] theorem coe_toProdDiffeomorph : ⇑toProdDiffeomorph = toProd := (rfl)

@[simp] theorem coe_toProdDiffeomorph_symm : ⇑toProdDiffeomorph.symm = toProd.symm := (rfl)

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

/-! ### The orthogonal group fixing the identity -/

/-- A `2 × 2` real matrix `A` acts on `Nil` by the group endomorphism
`(x, y, z) ↦ (x', y', det A * (z - x y / 2) + x' y' / 2)`, where `(x', y') = A (x, y)`. -/
private def matrixHom (A : Matrix (Fin 2) (Fin 2) ℝ) : Nil →* Nil where
  toFun p := mk (A 0 0 * p.x + A 0 1 * p.y) (A 1 0 * p.x + A 1 1 * p.y)
    (A.det * (p.z - p.x * p.y / 2) +
      (A 0 0 * p.x + A 0 1 * p.y) * (A 1 0 * p.x + A 1 1 * p.y) / 2)
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp [Matrix.det_fin_two] <;> ring

private theorem matrixHom_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Nil) :
    matrixHom A p = mk (A 0 0 * p.x + A 0 1 * p.y) (A 1 0 * p.x + A 1 1 * p.y)
      (A.det * (p.z - p.x * p.y / 2) +
        (A 0 0 * p.x + A 0 1 * p.y) * (A 1 0 * p.x + A 1 1 * p.y) / 2) := (rfl)

private theorem matrixHom_one (p : Nil) : matrixHom 1 p = p := by
  ext <;> simp [matrixHom_apply]

private theorem matrixHom_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) (p : Nil) :
    matrixHom (A * B) p = matrixHom A (matrixHom B p) := by
  ext <;> simp [matrixHom_apply, Matrix.mul_apply, Matrix.det_mul] <;> ring

/-- The coordinate functional `(v₁, v₂, v₃) ↦ A₀₀ v₁ + A₀₁ v₂`. -/
private def firstL (A : Matrix (Fin 2) (Fin 2) ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  A 0 0 • xL + A 0 1 • yL

/-- The coordinate functional `(v₁, v₂, v₃) ↦ A₁₀ v₁ + A₁₁ v₂`. -/
private def secondL (A : Matrix (Fin 2) (Fin 2) ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  A 1 0 • xL + A 1 1 • yL

/-- `matrixHom A`, read in the model space `ℝ³`. -/
private def matrixMap (A : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (firstL A r, secondL A r,
    A.det * (zL r - 2⁻¹ * (xL r * yL r)) + 2⁻¹ * (firstL A r * secondL A r))

private theorem coe_matrixHom (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ⇑(matrixHom A) = toProd.symm ∘ matrixMap A ∘ toProd := by
  funext p
  ext <;> simp [matrixHom_apply, matrixMap, firstL, secondL, xL, yL, zL]
  ring

/-- The differential of `matrixMap A` at `r`. -/
private def matrixDeriv (A : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ × ℝ × ℝ) :
    (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  (firstL A).prod ((secondL A).prod
    (A.det • (zL - (2⁻¹ : ℝ) • (xL r • yL + yL r • xL)) +
      (2⁻¹ : ℝ) • (firstL A r • secondL A + secondL A r • firstL A)))

private theorem hasFDerivAt_matrixMap (A : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ × ℝ × ℝ) :
    HasFDerivAt (matrixMap A) (matrixDeriv A r) r :=
  (firstL A).hasFDerivAt.prodMk ((secondL A).hasFDerivAt.prodMk
    (((zL.hasFDerivAt.sub ((xL.hasFDerivAt.fun_mul yL.hasFDerivAt).const_mul (2⁻¹ : ℝ))).const_mul
      A.det).add (((firstL A).hasFDerivAt.fun_mul (secondL A).hasFDerivAt).const_mul (2⁻¹ : ℝ))))

private theorem contMDiff_matrixHom {n : ℕ∞ω} (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) n (matrixHom A) := by
  have h : ContDiff ℝ n (matrixMap A) := by
    unfold matrixMap
    fun_prop
  rw [coe_matrixHom]
  exact h.contMDiff

/-- The differential of `matrixHom A`, read in the model space, is `matrixDeriv A`. -/
private theorem tangentSpaceCastModel_mfderiv_matrixHom (A : Matrix (Fin 2) (Fin 2) ℝ) (q : Nil)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A q)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A) q v) =
      matrixDeriv A (toProd q) (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q v) := by
  have h : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A) q
      (matrixDeriv A (toProd q)) := by
    rw [coe_matrixHom]
    exact (hasFDerivAt_matrixMap A (toProd q)).hasMFDerivAt
  exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q →L[ℝ]
      TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A q) ↦
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A q) (L v)) h.mfderiv

/-- An orthogonal matrix acts on `Nil` preserving the inner product of tangent vectors. -/
private theorem inner_mfderiv_matrixHom {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) (q : Nil) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A) q v)
        (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (matrixHom A) q w) =
      inner ℝ v w := by
  have hA' : A.transpose * A = 1 := by rwa [Matrix.mem_orthogonalGroup_iff'] at hA
  have h₁ : A 0 0 * A 0 0 + A 1 0 * A 1 0 = 1 := by
    simpa [Matrix.mul_apply] using congrFun (congrFun hA' 0) 0
  have h₂ : A 0 1 * A 0 1 + A 1 1 * A 1 1 = 1 := by
    simpa [Matrix.mul_apply] using congrFun (congrFun hA' 1) 1
  have h₃ : A 0 0 * A 0 1 + A 1 0 * A 1 1 = 0 := by
    simpa [Matrix.mul_apply] using congrFun (congrFun hA' 0) 1
  -- The determinant of an orthogonal matrix is `± 1`.
  have hdet : (A 0 0 * A 1 1 - A 0 1 * A 1 0) * (A 0 0 * A 1 1 - A 0 1 * A 1 0) = 1 := by
    linear_combination (A 0 1 * A 0 1 + A 1 1 * A 1 1) * h₁ + h₂ -
      (A 0 0 * A 0 1 + A 1 0 * A 1 1) * h₃
  rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_matrixHom,
    tangentSpaceCastModel_mfderiv_matrixHom]
  set V := tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q v
  set W := tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) q w
  simp only [matrixDeriv, firstL, secondL, xL, yL, zL, matrixHom_apply, x_mk, Matrix.det_fin_two,
    ContinuousLinearMap.prod_apply, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_comp,
    Function.comp_apply, fst_toProd, fst_snd_toProd, smul_eq_mul]
  linear_combination (V.1 * W.1) * h₁ + (V.2.1 * W.2.1) * h₂ + (V.1 * W.2.1 + V.2.1 * W.1) * h₃ +
    ((V.2.2 - q.x * V.2.1) * (W.2.2 - q.x * W.2.1)) * hdet

/-- The orthogonal group `O(2)` acts on `Nil` by group automorphisms: `g` sends `(x, y, z)` to
`(x', y', det g * (z - x y / 2) + x' y' / 2)`, where `(x', y') = g (x, y)`.

In the coordinates `(x, y, z - x y / 2)`, in which the product of `Nil` is
`(a, b, c) * (x, y, z) = (a + x, b + y, c + z + (a y - b x) / 2)`, the automorphism
`orthogonalMulAut g` is `g` on the first two coordinates and multiplication by `det g = ± 1` on
the third. -/
def orthogonalMulAut : Matrix.orthogonalGroup (Fin 2) ℝ →* MulAut Nil where
  toFun g :=
    { matrixHom g with
      invFun := matrixHom ↑g⁻¹
      left_inv p := (matrixHom_mul _ _ p).symm.trans <| by
        rw [← Matrix.UnitaryGroup.mul_val, inv_mul_cancel, Matrix.UnitaryGroup.one_val,
          matrixHom_one]
      right_inv p := (matrixHom_mul _ _ p).symm.trans <| by
        rw [← Matrix.UnitaryGroup.mul_val, mul_inv_cancel, Matrix.UnitaryGroup.one_val,
          matrixHom_one] }
  map_one' := MulEquiv.ext matrixHom_one
  map_mul' g h := MulEquiv.ext (matrixHom_mul g h)

@[simp]
theorem x_orthogonalMulAut (g : Matrix.orthogonalGroup (Fin 2) ℝ) (p : Nil) :
    (orthogonalMulAut g p).x = g.1 0 0 * p.x + g.1 0 1 * p.y := (rfl)

@[simp]
theorem y_orthogonalMulAut (g : Matrix.orthogonalGroup (Fin 2) ℝ) (p : Nil) :
    (orthogonalMulAut g p).y = g.1 1 0 * p.x + g.1 1 1 * p.y := (rfl)

@[simp]
theorem z_orthogonalMulAut (g : Matrix.orthogonalGroup (Fin 2) ℝ) (p : Nil) :
    (orthogonalMulAut g p).z = g.1.det * (p.z - p.x * p.y / 2) +
      (g.1 0 0 * p.x + g.1 0 1 * p.y) * (g.1 1 0 * p.x + g.1 1 1 * p.y) / 2 := (rfl)

/-- Distinct orthogonal matrices act by distinct automorphisms of `Nil`. -/
theorem orthogonalMulAut_injective : Function.Injective orthogonalMulAut := fun g h hgh ↦ by
  have h₁ := DFunLike.congr_fun hgh (mk 1 0 0)
  have h₂ := DFunLike.congr_fun hgh (mk 0 1 0)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg x h₁
  · simpa using congrArg x h₂
  · simpa using congrArg y h₁
  · simpa using congrArg y h₂

/-- The orthogonal group `O(2)` acts on `Nil` by isometries fixing the identity
(`TauCeti.Nil.range_orthogonalToIsom_le_stabilizer`): the automorphisms `orthogonalMulAut g`,
which rotate or reflect the `(x, y)`-plane and preserve the form `dz - x dy` up to the sign
`det g`. -/
def orthogonalToIsom : Matrix.orthogonalGroup (Fin 2) ℝ →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Nil where
  -- The forward and inverse maps of `orthogonalMulAut g` are `matrixHom g` and `matrixHom g⁻¹` by
  -- definition, so the smoothness and inner-product facts about `matrixHom` apply to them.
  toFun g :=
    { toEquiv := (orthogonalMulAut g).toEquiv
      contMDiff_toFun := contMDiff_matrixHom _
      contMDiff_invFun := contMDiff_matrixHom _
      inner_mfderiv' := inner_mfderiv_matrixHom g.2 }
  map_one' := RiemannianIsometry.ext fun p ↦ by
    rw [RiemannianIsometry.one_apply]
    exact DFunLike.congr_fun (map_one orthogonalMulAut) p
  map_mul' g h := RiemannianIsometry.ext fun p ↦ by
    rw [RiemannianIsometry.mul_apply]
    exact DFunLike.congr_fun (map_mul orthogonalMulAut g h) p

/-- The isometry `orthogonalToIsom g` is the automorphism `orthogonalMulAut g`. -/
@[simp]
theorem orthogonalToIsom_apply (g : Matrix.orthogonalGroup (Fin 2) ℝ) (p : Nil) :
    orthogonalToIsom g p = orthogonalMulAut g p := (rfl)

/-- At the identity, an orthogonal Nil automorphism has differential `g` on the
horizontal plane and multiplication by `det g` on the central line. -/
@[simp]
theorem tangentSpaceCastModel_mfderiv_orthogonalToIsom_one
    (g : Matrix.orthogonalGroup (Fin 2) ℝ)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (1 : Nil)) :
    let u := tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (1 : Nil) v
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (orthogonalToIsom g 1)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (orthogonalToIsom g) 1 v) =
        (g.1 0 0 * u.1 + g.1 0 1 * u.2.1,
          g.1 1 0 * u.1 + g.1 1 1 * u.2.1, g.1.det * u.2.2) := by
  have hfun : (orthogonalToIsom g : Nil → Nil) = matrixHom g.1 := rfl
  rw [hfun]
  simpa [matrixDeriv, firstL, secondL, xL, yL, zL] using
    tangentSpaceCastModel_mfderiv_matrixHom g.1 1 v

/-- Distinct orthogonal matrices act by distinct isometries of `Nil`. -/
theorem orthogonalToIsom_injective : Function.Injective orthogonalToIsom := fun _ _ h ↦
  orthogonalMulAut_injective <| MulEquiv.ext fun p ↦ DFunLike.congr_fun h p

/-- The orthogonal isometries of `Nil` fix its identity element. -/
theorem range_orthogonalToIsom_le_stabilizer :
    orthogonalToIsom.range ≤ MulAction.stabilizer (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Nil) (1 : Nil) := by
  rintro _ ⟨g, rfl⟩
  rw [MulAction.mem_stabilizer_iff, RiemannianIsometry.smul_def, orthogonalToIsom_apply, map_one]

/-! ### The semidirect product `Nil ⋊ O(2)` -/

/-- Left translations and the orthogonal isometries together give an action of the semidirect
product `Nil ⋊ O(2)` on `Nil` by isometries, in which `(n, g)` acts by `p ↦ n * g p`. -/
def semidirectProductToIsom :
    Nil ⋊[orthogonalMulAut] Matrix.orthogonalGroup (Fin 2) ℝ →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Nil :=
  SemidirectProduct.lift toIsom orthogonalToIsom fun g ↦ MonoidHom.ext fun n ↦
    RiemannianIsometry.ext fun p ↦ by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        RiemannianIsometry.mul_apply, toIsom_apply, orthogonalToIsom_apply, map_mul]
      rw [← orthogonalToIsom_apply g ((orthogonalToIsom g)⁻¹ p), ← RiemannianIsometry.mul_apply,
        mul_inv_cancel, RiemannianIsometry.one_apply]

/-- The element `(n, g)` of `Nil ⋊ O(2)` acts on `Nil` by `p ↦ n * g p`. -/
@[simp]
theorem semidirectProductToIsom_apply
    (a : Nil ⋊[orthogonalMulAut] Matrix.orthogonalGroup (Fin 2) ℝ) (p : Nil) :
    semidirectProductToIsom a p = a.left * orthogonalMulAut a.right p := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right a]
  rw [map_mul, RiemannianIsometry.mul_apply, semidirectProductToIsom, SemidirectProduct.lift_inl,
    SemidirectProduct.lift_inr, toIsom_apply, orthogonalToIsom_apply]

/-- Distinct elements of `Nil ⋊ O(2)` act by distinct isometries of `Nil`. -/
theorem semidirectProductToIsom_injective : Function.Injective semidirectProductToIsom := by
  intro a b h
  have hl : a.left = b.left := by
    simpa using DFunLike.congr_fun h 1
  refine SemidirectProduct.ext hl (orthogonalToIsom_injective (RiemannianIsometry.ext fun p ↦ ?_))
  simpa [hl] using DFunLike.congr_fun h p

end Nil

end TauCeti
