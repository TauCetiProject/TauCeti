/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.TwoFieldFamily
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Triple
public import TauCeti.Topology.VectorBundle.SphereBundle.VerticalField
import TauCeti.Topology.VectorBundle.TangentCircle

/-!
# The family of two-spheres of a sphere bundle with two orthonormal vertical fields

Let `E → B` be a real vector bundle whose fibres are inner product spaces, with continuous fibre
norm, and let `Q = S(E)` be its unit sphere bundle. A **vertical vector field** on `Q` assigns to
each unit vector `x ∈ E_b` a vector `u x ∈ E_b` of the same fibre. Two continuous vertical fields
that are tangent to the sphere fibres and linearly independent at every point can be normalized
to fields `u`, `v` with `x`, `u x`, `v x` orthonormal for every `x`, cutting out the same equators
(`TauCeti.exists_orthonormal_sphereBundle_fields`).

For such `u`, `v`, over each `x ∈ S(E_b)` lies the equator `Σₓ` of unit vectors `w ∈ E_b`
orthogonal to `u x` and to `v x`: the carrier of Barraud–Damian–Humilière–Oancea's Example 6.20
for the sphere `S(E_b)` and the restrictions of `u`, `v` to it
(`TauCeti.sphereBundleFiberField`), a sphere of codimension two in `S(E_b)` through `x`. These
equators form the space `Σ` (`TauCeti.SphereBundleTwoFieldEquators`) of pairs `(x, w)`, with the
topology of a subspace of `Q × E`. Projection to `x` (`TauCeti.SphereBundleTwoFieldEquators.proj`)
maps `Σ` to `Q`, with the section `x ↦ (x, x)` (`TauCeti.SphereBundleTwoFieldEquators.diag`), and
`w` is itself a point of `Q` in the sphere fibre through `x`
(`TauCeti.SphereBundleTwoFieldEquators.point`). The space of equators of the sphere `S(E_b)` and
the restricted fields maps continuously into `Σ`
(`TauCeti.SphereBundleTwoFieldEquators.ofFiber`,
`TauCeti.SphereBundleTwoFieldEquators.continuous_ofFiber`).

Putting the two-sphere of Example 6.20 into each sphere fibre gives the family
(`TauCeti.sphereBundleTwoFieldSphereFamily`)

`σ : Σ → Map(S², Q)`,

where `σ (x, w)` sweeps, through each point `w'` of the circle through `x` and `w` tangent to
`v x`, the circle through `x` and `w'` tangent to `u x`. It lies over `Q`: evaluation at the north
pole sends `σ (x, w)` to `x` (`TauCeti.mappingSpaceEval_comp_sphereBundleTwoFieldSphereFamily`).
Over a point of the fibre `S(E_b)`, it agrees pointwise, in the fibre of `E` over `b`, with the
family `TauCeti.twoFieldSphereFamily` of the sphere `S(E_b)` and the restricted fields
(`TauCeti.coe_sphereBundleTwoFieldSphereFamily_ofFiber`). The induced map of double loop spaces
`Ω²S(E_b) → Ω²Q` is not formalised here.

This is the family of two-spheres of the second alternative of the source's Proposition 6.23, for
an `Sⁿ`-bundle `Q → B` with `n ≡ 3 (mod 4)` and two everywhere independent vertical vector fields.
Continuity as the base point moves comes from writing each two-sphere as a fibrewise linear
combination of `x`, `w`, `u x` and `v x` with continuous coefficients: the circles are
`TauCeti.tangentCircle`, whose coefficients involve only the fibre norm
(`Continuous.tangentCircle_totalSpace`). The local triviality and orientation of `Σ → Q` and the
class of a fibre are not addressed here.

## Main declarations

* `TauCeti.SphereBundleTwoFieldEquators F E u v`: the space `Σ` of pairs `(x, w)` with `w` a unit
  vector of the fibre through `x` orthogonal to `u x` and `v x`.
* `TauCeti.sphereBundleTwoFieldSphereFamily`: the family `σ : Σ → Map(S², Q)`.
* `TauCeti.coe_sphereBundleTwoFieldSphereFamily_sphereCollapse`: on the square, `σ (x, w)` is
  `y ↦ tangentCircle x (u x) (tangentCircle x (v x) w (2π y₀)) (2π y₁)`.
* `TauCeti.mappingSpaceEval_comp_sphereBundleTwoFieldSphereFamily`: `σ` lies over `Q`.
* `TauCeti.coe_sphereBundleTwoFieldSphereFamily_ofFiber`: over a point of `S(E_b)`, `σ` agrees
  pointwise, in the fibre of `E` over `b`, with the family of the sphere `S(E_b)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Example 6.20
  and Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Real
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

universe w

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)]

/-! ### The space of equators -/

variable (F E) in
/-- The space `Σ` of the equators cut out by two vertical vector fields `u`, `v` of the unit
sphere bundle `S(E)`: the pairs `(x, w)` of a point `x` of `S(E)` and a unit vector `w` of the
fibre of `E` through `x` orthogonal to `u x` and to `v x`. When `x`, `u x`, `v x` are orthonormal,
the fibre over `x` is a sphere of codimension two in the sphere fibre through `x`. Its topology is
induced by `(x, w) ↦ (x, w)` into `S(E) × E` (`TauCeti.SphereBundleTwoFieldEquators.toProd`). -/
structure SphereBundleTwoFieldEquators (u v : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj)
    where
  /-- The base point `x` of the equator, a point of the unit sphere bundle. -/
  base : sphereBundle F E
  /-- The point `w` of the equator over `x`, a vector of the fibre of `E` through `x`. -/
  vec : E (base : TotalSpace F E).proj
  /-- The vector `w` is a unit vector. -/
  norm_vec : ‖vec‖ = 1
  /-- The vector `w` is orthogonal to `u x`. -/
  inner_vec_u : ⟪vec, u base⟫ = 0
  /-- The vector `w` is orthogonal to `v x`. -/
  inner_vec_v : ⟪vec, v base⟫ = 0

namespace SphereBundleTwoFieldEquators

variable {u v : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj}

/-- A point `(x, w)` of `Σ`, as a pair of a point of `S(E)` and a point of the total space of `E`
over the same base point. -/
def toProd (p : SphereBundleTwoFieldEquators F E u v) : sphereBundle F E × TotalSpace F E :=
  (p.base, ⟨(p.base : TotalSpace F E).proj, p.vec⟩)

@[simp]
theorem toProd_apply (p : SphereBundleTwoFieldEquators F E u v) :
    toProd p = (p.base, ⟨(p.base : TotalSpace F E).proj, p.vec⟩) :=
  (rfl)

theorem toProd_injective : Function.Injective (toProd (u := u) (v := v)) := by
  intro p q hpq
  obtain ⟨x, w, _, _, _⟩ := p
  obtain ⟨x', w', _, _, _⟩ := q
  simp only [toProd, Prod.mk.injEq] at hpq
  obtain ⟨rfl, hw⟩ := hpq
  obtain rfl := eq_of_heq (TotalSpace.mk.inj hw).2
  rfl

/-- Two points of `Σ` are equal when their base points are, and their vectors are as points of the
total space of `E`. -/
@[ext]
theorem ext {p q : SphereBundleTwoFieldEquators F E u v} (hbase : p.base = q.base)
    (hvec : TotalSpace.mk' F (p.base : TotalSpace F E).proj p.vec =
      TotalSpace.mk' F (q.base : TotalSpace F E).proj q.vec) : p = q :=
  toProd_injective (Prod.ext hbase hvec)

variable [TopologicalSpace (TotalSpace F E)]

/-- The topology of `Σ` as a subspace of `S(E) × E`. -/
instance : TopologicalSpace (SphereBundleTwoFieldEquators F E u v) :=
  .induced toProd inferInstance

theorem isEmbedding_toProd : Topology.IsEmbedding (toProd (u := u) (v := v)) :=
  ⟨⟨rfl⟩, toProd_injective⟩

theorem continuous_toProd : Continuous (toProd (u := u) (v := v)) :=
  isEmbedding_toProd.continuous

/-- A map into `Σ` is continuous exactly when its base point and its vector are, the latter in
the total space of `E`. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → SphereBundleTwoFieldEquators F E u v} :
    Continuous f ↔ Continuous (fun x ↦ (f x).base) ∧
      Continuous (fun x ↦ TotalSpace.mk' F ((f x).base : TotalSpace F E).proj (f x).vec) := by
  rw [isEmbedding_toProd.continuous_iff, continuous_prodMk]
  rfl

/-- The projection `Σ → S(E)`, `(x, w) ↦ x`. -/
def proj : C(SphereBundleTwoFieldEquators F E u v, sphereBundle F E) :=
  ⟨base, continuous_fst.comp continuous_toProd⟩

@[simp]
theorem proj_apply (p : SphereBundleTwoFieldEquators F E u v) : proj p = p.base :=
  (rfl)

/-- The point `w` of a point `(x, w)` of `Σ`, as a point of the unit sphere bundle: it lies in the
sphere fibre through `x`. -/
def point : C(SphereBundleTwoFieldEquators F E u v, sphereBundle F E) :=
  ⟨fun p ↦ ⟨⟨(p.base : TotalSpace F E).proj, p.vec⟩, mem_sphereBundle.2 p.norm_vec⟩,
    (continuous_snd.comp continuous_toProd).subtype_mk _⟩

@[simp]
theorem coe_point_apply (p : SphereBundleTwoFieldEquators F E u v) :
    (point p : TotalSpace F E) = ⟨(p.base : TotalSpace F E).proj, p.vec⟩ :=
  (rfl)

/-- The point `w` lies in the sphere fibre through `x`. -/
theorem sphereBundleProj_point [TopologicalSpace B] [NormedAddCommGroup F] [FiberBundle F E]
    (p : SphereBundleTwoFieldEquators F E u v) :
    sphereBundleProj F E (point p) = sphereBundleProj F E (proj p) := by
  simp only [sphereBundleProj_apply, coe_point_apply, proj_apply]

end SphereBundleTwoFieldEquators

open SphereBundleTwoFieldEquators

variable {u v : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj}

/-! ### The family of two-spheres -/

section Pointwise

variable (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).snd, u x, v x])
include h

omit h in
/-- The point at the angles `(θ₀, θ₁)` of the two-sphere of `(x, w)`, in the fibre of `E` through
`x`: the point at the angle `θ₁` of the circle through `x` tangent to `u x` and through the point at
the angle `θ₀` of the circle through `x` and `w` tangent to `v x`. -/
private def twoFieldPoint (p : SphereBundleTwoFieldEquators F E u v) (θ₀ θ₁ : ℝ) :
    E (p.base : TotalSpace F E).proj :=
  tangentCircle (p.base : TotalSpace F E).snd (u p.base)
    (tangentCircle (p.base : TotalSpace F E).snd (v p.base) p.vec θ₀) θ₁

private theorem norm_twoFieldPoint (p : SphereBundleTwoFieldEquators F E u v) (θ₀ θ₁ : ℝ) :
    ‖twoFieldPoint p θ₀ θ₁‖ = 1 := by
  have hx : ‖(p.base : TotalSpace F E).snd‖ = 1 := mem_sphereBundle.1 p.base.property
  have h := h p.base
  exact norm_tangentCircle hx h.norm_eq_one_vecCons_one h.inner_eq_zero_vecCons_zero_one
    (norm_tangentCircle hx h.norm_eq_one_vecCons_two h.inner_eq_zero_vecCons_zero_two p.norm_vec
      p.inner_vec_v θ₀)
    (inner_tangentCircle_eq_zero h.inner_eq_zero_vecCons_zero_one
      (inner_eq_zero_symm.1 h.inner_eq_zero_vecCons_one_two) p.inner_vec_u θ₀) θ₁

omit h in
/-- On the boundary of the square, the two-sphere of `(x, w)` is at `x`. -/
private theorem twoFieldPoint_of_mem_boundary (p : SphereBundleTwoFieldEquators F E u v)
    {y : I^(Fin 2)} (hy : y ∈ Cube.boundary (Fin 2)) :
    twoFieldPoint p (2 * π * y 0) (2 * π * y 1) = (p.base : TotalSpace F E).snd := by
  rcases Fin.exists_fin_two.1 hy with (hi | hi) | (hi | hi) <;>
    simp [twoFieldPoint, hi]

end Pointwise

section Diagonal

variable [TopologicalSpace (TotalSpace F E)]
  (hxu : ∀ x : sphereBundle F E, ⟪(x : TotalSpace F E).snd, u x⟫ = 0)
  (hxv : ∀ x : sphereBundle F E, ⟪(x : TotalSpace F E).snd, v x⟫ = 0)

/-- The **diagonal section** `x ↦ (x, x)` of `Σ → S(E)`: when both fields are tangent to the
sphere fibres, every point lies on its own equator. -/
def SphereBundleTwoFieldEquators.diag : C(sphereBundle F E, SphereBundleTwoFieldEquators F E u v)
    where
  toFun x :=
    { base := x
      vec := (x : TotalSpace F E).snd
      norm_vec := mem_sphereBundle.1 x.property
      inner_vec_u := hxu x
      inner_vec_v := hxv x }
  continuous_toFun := continuous_iff.2 ⟨continuous_id, continuous_subtypeVal⟩

/-- The base point of `(x, x)` is `x`. -/
@[simp]
theorem SphereBundleTwoFieldEquators.base_diag (x : sphereBundle F E) :
    (SphereBundleTwoFieldEquators.diag hxu hxv x).base = x :=
  (rfl)

/-- The vector of `(x, x)` is its base point `x`, in the fibre through `x`. -/
theorem SphereBundleTwoFieldEquators.vec_diag (x : sphereBundle F E) :
    (SphereBundleTwoFieldEquators.diag hxu hxv x).vec =
      ((SphereBundleTwoFieldEquators.diag hxu hxv x).base : TotalSpace F E).snd :=
  (rfl)

/-- The point `w` of `(x, x)` is `x`. -/
@[simp]
theorem SphereBundleTwoFieldEquators.point_diag (x : sphereBundle F E) :
    point (SphereBundleTwoFieldEquators.diag hxu hxv x) = x :=
  (rfl)

@[simp]
theorem SphereBundleTwoFieldEquators.proj_comp_diag :
    proj.comp (SphereBundleTwoFieldEquators.diag hxu hxv) = ContinuousMap.id (sphereBundle F E) :=
  (rfl)

end Diagonal

/-! ### The equators over a sphere fibre -/

section Fiber

/-- A point `(z, w)` of the space of equators of the sphere `S(E_b)`, for the restricted fields,
as a point of the space of equators of the sphere bundle over `z`. -/
def SphereBundleTwoFieldEquators.ofFiber {b : B}
    (zw : twoFieldEquators (sphereBundleFiberField u b) (sphereBundleFiberField v b)) :
    SphereBundleTwoFieldEquators F E u v where
  base := ⟨⟨b, zw.val.1⟩, mem_sphereBundle.2 (norm_eq_of_mem_sphere zw.val.1)⟩
  vec := (zw.val.2 : E b)
  norm_vec := norm_eq_of_mem_sphere zw.val.2
  inner_vec_u := by
    have h := (mem_twoFieldEquators.1 zw.property).1
    rwa [sphereBundleFiberField_apply] at h
  inner_vec_v := by
    have h := (mem_twoFieldEquators.1 zw.property).2
    rwa [sphereBundleFiberField_apply] at h

/-- The base point of `ofFiber zw` is the point `z` of the sphere fibre over `b`. -/
@[simp]
theorem SphereBundleTwoFieldEquators.coe_base_ofFiber {b : B}
    (zw : twoFieldEquators (sphereBundleFiberField u b) (sphereBundleFiberField v b)) :
    ((SphereBundleTwoFieldEquators.ofFiber zw).base : TotalSpace F E) = ⟨b, zw.val.1⟩ :=
  (rfl)

/-- The point `w` of `ofFiber zw` is the point `w` of the sphere fibre over `b`. -/
theorem SphereBundleTwoFieldEquators.coe_point_ofFiber [TopologicalSpace (TotalSpace F E)] {b : B}
    (zw : twoFieldEquators (sphereBundleFiberField u b) (sphereBundleFiberField v b)) :
    (point (SphereBundleTwoFieldEquators.ofFiber zw) : TotalSpace F E) = ⟨b, zw.val.2⟩ :=
  (rfl)

/-- The map `ofFiber` from the space of equators of the sphere `S(E_b)` into `Σ` is continuous. -/
theorem SphereBundleTwoFieldEquators.continuous_ofFiber [TopologicalSpace B]
    [NormedAddCommGroup F] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] {b : B} :
    Continuous (SphereBundleTwoFieldEquators.ofFiber (u := u) (v := v) (b := b)) :=
  continuous_iff.2
    ⟨((FiberBundle.continuous_totalSpaceMk F E b).comp
        (continuous_subtypeVal.comp (continuous_fst.comp continuous_subtypeVal))).subtype_mk _,
      (FiberBundle.continuous_totalSpaceMk F E b).comp
        (continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal))⟩

end Fiber

section Family

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]
  (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).snd, u x, v x])
  (hu : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u x))
  (hv : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (v x))

include h hu hv in
/-- The two-spheres on the square: `((x, w), y) ↦ tangentCircle x (u x) (w' y₀) (2π y₁)`, where
`w' y₀ = tangentCircle x (v x) w (2π y₀)` runs along the inner circle. -/
private def twoFieldSquare : C(SphereBundleTwoFieldEquators F E u v × I^(Fin 2), sphereBundle F E)
    where
  toFun a := ⟨TotalSpace.mk' F (a.1.base : TotalSpace F E).proj
      (twoFieldPoint a.1 (2 * π * a.2 0) (2 * π * a.2 1)),
    mem_sphereBundle.2 (norm_twoFieldPoint h a.1 _ _)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    obtain ⟨hx, hw⟩ :=
      continuous_iff.1 (continuous_id (X := SphereBundleTwoFieldEquators F E u v))
    -- The base point `x`, as a continuous map into the total space of `E`.
    have hx' : Continuous fun a : SphereBundleTwoFieldEquators F E u v × I^(Fin 2) ↦
        TotalSpace.mk' F (a.1.base : TotalSpace F E).proj (a.1.base : TotalSpace F E).snd :=
      continuous_subtypeVal.comp (hx.comp continuous_fst)
    exact Continuous.tangentCircle_totalSpace hx' (hu.comp (hx.comp continuous_fst))
      (Continuous.tangentCircle_totalSpace hx' (hv.comp (hx.comp continuous_fst))
        (hw.comp continuous_fst) (by fun_prop)) (by fun_prop)

private theorem coe_twoFieldSquare_apply (a : SphereBundleTwoFieldEquators F E u v × I^(Fin 2)) :
    (twoFieldSquare h hu hv a : TotalSpace F E) =
      TotalSpace.mk' F (a.1.base : TotalSpace F E).proj
        (twoFieldPoint a.1 (2 * π * a.2 0) (2 * π * a.2 1)) :=
  (rfl)

private theorem factorsThrough_twoFieldSquare :
    Function.FactorsThrough (twoFieldSquare h hu hv)
      ((ContinuousMap.id (SphereBundleTwoFieldEquators F E u v)).prodMap
        (sphereCollapse 2 Sphere2.north)) := by
  rintro ⟨p, y⟩ ⟨p', y'⟩ hyy
  simp only [ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map, Prod.mk.injEq] at hyy
  obtain ⟨rfl, hyy⟩ := hyy
  rcases eq_or_mem_boundary_of_sphereCollapse_eq 2 Sphere2.north hyy with rfl | ⟨hy, hy'⟩
  · rfl
  · -- both boundary points go to the base point `x`
    refine Subtype.ext ?_
    simp only [coe_twoFieldSquare_apply, twoFieldPoint_of_mem_boundary _ hy,
      twoFieldPoint_of_mem_boundary _ hy']

/-- **The family of two-spheres of a sphere bundle with two orthonormal vertical fields.** For
`(x, w)` in the space of equators `Σ`, `σ (x, w) : S² → S(E)` sweeps, in the sphere fibre through
`x`, through each point `w'` of the circle through `x` and `w` tangent to `v x`, the circle
through `x` and `w'` tangent to `u x`; it sends the north pole to `x`. This is the family of
Barraud–Damian–Humilière–Oancea's Example 6.20 in every sphere fibre, as used in the second
alternative of their Proposition 6.23. -/
def sphereBundleTwoFieldSphereFamily :
    C(SphereBundleTwoFieldEquators F E u v, C(Sphere2, sphereBundle F E)) :=
  ((isQuotientMap_prodMap_id_sphereCollapse 2 Sphere2.north _).lift _
    (factorsThrough_twoFieldSquare h hu hv)).curry

/-- On the square, the two-sphere of `(x, w)` is
`y ↦ tangentCircle x (u x) (tangentCircle x (v x) w (2π y₀)) (2π y₁)` in the fibre through `x`. -/
@[simp]
theorem coe_sphereBundleTwoFieldSphereFamily_sphereCollapse
    (p : SphereBundleTwoFieldEquators F E u v) (y : I^(Fin 2)) :
    (sphereBundleTwoFieldSphereFamily h hu hv p (sphereCollapse 2 Sphere2.north y) :
        TotalSpace F E) =
      TotalSpace.mk' F (p.base : TotalSpace F E).proj
        (tangentCircle (p.base : TotalSpace F E).snd (u p.base)
          (tangentCircle (p.base : TotalSpace F E).snd (v p.base) p.vec (2 * π * y 0))
          (2 * π * y 1)) :=
  congrArg Subtype.val (DFunLike.congr_fun ((isQuotientMap_prodMap_id_sphereCollapse 2
    Sphere2.north _).lift_comp _ (factorsThrough_twoFieldSquare h hu hv)) (p, y))

/-- The two-sphere of `(x, w)` sends the north pole to `x`. -/
@[simp]
theorem sphereBundleTwoFieldSphereFamily_north (p : SphereBundleTwoFieldEquators F E u v) :
    sphereBundleTwoFieldSphereFamily h hu hv p Sphere2.north = p.base := by
  rw [← (sphereCollapse_eq_basepoint_iff 2 Sphere2.north 0).2 zero_mem_cubeBoundary]
  refine Subtype.ext ?_
  rw [coe_sphereBundleTwoFieldSphereFamily_sphereCollapse]
  exact congrArg (TotalSpace.mk' F _) (twoFieldPoint_of_mem_boundary p zero_mem_cubeBoundary)

/-- **The family of two-spheres lies over the sphere bundle**: evaluation at the north pole sends
the two-sphere of `(x, w)` to `x`. -/
@[simp]
theorem mappingSpaceEval_comp_sphereBundleTwoFieldSphereFamily :
    (mappingSpaceEval Sphere2.north).comp (sphereBundleTwoFieldSphereFamily h hu hv) = proj :=
  ContinuousMap.ext fun p ↦ by
    rw [ContinuousMap.comp_apply, mappingSpaceEval_apply, sphereBundleTwoFieldSphereFamily_north,
      proj_apply]

/-- Every two-sphere of the family lies in the sphere fibre through its base point. -/
theorem sphereBundleProj_sphereBundleTwoFieldSphereFamily
    (p : SphereBundleTwoFieldEquators F E u v) (z : Sphere2) :
    sphereBundleProj F E (sphereBundleTwoFieldSphereFamily h hu hv p z) =
      sphereBundleProj F E p.base := by
  obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
  simp only [sphereBundleProj_apply]
  rw [coe_sphereBundleTwoFieldSphereFamily_sphereCollapse]

/-- The two-sphere of the point `(x, x)` is constant at `x`. -/
@[simp]
theorem sphereBundleTwoFieldSphereFamily_diag (x : sphereBundle F E) :
    sphereBundleTwoFieldSphereFamily h hu hv
        (SphereBundleTwoFieldEquators.diag (fun x ↦ (h x).inner_eq_zero_vecCons_zero_one)
          (fun x ↦ (h x).inner_eq_zero_vecCons_zero_two) x) =
      ContinuousMap.const Sphere2 x := by
  ext z : 1
  obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
  refine Subtype.ext ?_
  rw [coe_sphereBundleTwoFieldSphereFamily_sphereCollapse]
  rw [vec_diag, tangentCircle_self, tangentCircle_self]
  exact congrArg Subtype.val (base_diag _ _ x)

/-! ### The family over a point -/

/-- **The family over a point is the family of the sphere fibre.** For a point `(z, w)` of the
space of equators of the sphere `S(E_b)` and the restricted fields, the two-sphere of `(z, w)` in
the sphere bundle is the two-sphere `TauCeti.twoFieldSphereFamily` of the sphere `S(E_b)`, read in
the fibre of `E` over `b`. -/
theorem coe_sphereBundleTwoFieldSphereFamily_ofFiber {b : B}
    (zw : twoFieldEquators (sphereBundleFiberField u b) (sphereBundleFiberField v b))
    (z : Sphere2) :
    (sphereBundleTwoFieldSphereFamily h hu hv (.ofFiber zw) z : TotalSpace F E) =
      ⟨b, twoFieldSphereFamily (orthonormal_sphereBundleFiberField h b)
        (continuous_sphereBundleFiberField hu b) (continuous_sphereBundleFiberField hv b) zw
        z⟩ := by
  obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
  rw [coe_sphereBundleTwoFieldSphereFamily_sphereCollapse, coe_twoFieldSphereFamily_sphereCollapse]
  -- Both sides are the same tangent circles in `E_b`: the base point of `ofFiber zw` is the point
  -- `z` of the sphere bundle, and the restricted fields are `u`, `v` at that point.
  simp only [sphereBundleFiberField_apply]
  rfl

end Family

end TauCeti
