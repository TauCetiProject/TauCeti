/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.AlgebraicTopology.Sphere.TwoFieldFamily
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# The family of two-spheres of a sphere bundle with two orthonormal vertical fields

Let `E → B` be a real vector bundle whose fibres are inner product spaces, with continuous fibre
norm, and let `Q = S(E)` be its unit sphere bundle. A **vertical vector field** on `Q` assigns to
each unit vector `x ∈ E_b` a vector `u x ∈ E_b` of the same fibre; it is tangent to the sphere
fibre through `x` when `u x ⊥ x`. Two continuous vertical fields that are tangent to the sphere
fibres and linearly independent at every point can be normalized by Gram–Schmidt to fields `u`,
`v` with `x`, `u x`, `v x` orthonormal for every `x`, cutting out the same equators
(`TauCeti.exists_orthonormal_sphereBundle_fields`).

For such `u`, `v`, over each `x ∈ S(E_b)` lies the equator `Σₓ` of unit vectors `w ∈ E_b`
orthogonal to `u x` and to `v x`: the carrier of Barraud–Damian–Humilière–Oancea's Example 6.20
for the sphere `S(E_b)` and the restrictions of `u`, `v` to it
(`TauCeti.sphereBundleFiberField`), a sphere of codimension two in `S(E_b)` through `x`. These
equators form the space `Σ` (`TauCeti.SphereBundleTwoFieldEquators`) of pairs `(x, w)`, with the
topology of a subspace of `Q × E`. Projection to `x` (`TauCeti.SphereBundleTwoFieldEquators.proj`)
maps `Σ` to `Q`, with the section `x ↦ (x, x)` (`TauCeti.SphereBundleTwoFieldEquators.diag`), and
`w` is itself a point of `Q` in the sphere fibre through `x`
(`TauCeti.SphereBundleTwoFieldEquators.point`).

Putting the two-sphere of Example 6.20 into each sphere fibre gives the family
(`TauCeti.sphereBundleTwoFieldSphereFamily`)

`σ : Σ → Map(S², Q)`,

where `σ (x, w)` sweeps, through each point `w'` of the circle through `x` and `w` tangent to
`v x`, the circle through `x` and `w'` tangent to `u x`. It lies over `Q`: evaluation at the north
pole sends `σ (x, w)` to `x` (`TauCeti.mappingSpaceEval_comp_sphereBundleTwoFieldSphereFamily`).
Over a point of the fibre `S(E_b)`, it is the family `TauCeti.twoFieldSphereFamily` of the sphere
`S(E_b)` and the restricted fields, followed by the inclusion `S(E_b) → Q` of the sphere fibre
(`TauCeti.coe_sphereBundleTwoFieldSphereFamily_ofFiber`). So on the fibre `Σₓ`, read as based
maps at `x`, the family is the based family of the sphere `S(E_b)` followed by the map of double
loop spaces `Ω²S(E_b) → Ω²Q` induced by the fibre.

This is the family of two-spheres of the second alternative of the source's Proposition 6.23, for
an `Sⁿ`-bundle `Q → B` with `n ≡ 3 (mod 4)` and two everywhere independent vertical vector fields.
Continuity as the base point moves comes from writing each two-sphere as a fibrewise linear
combination of `x`, `w`, `u x` and `v x` with continuous coefficients: the circles are
`TauCeti.tangentCircle`, whose coefficients involve only the fibre norm
(`Continuous.tangentCircle_totalSpace`). The local triviality and orientation of `Σ → Q` and the
class of a fibre are not addressed here.

## Main declarations

* `Continuous.tangentCircle_totalSpace`: tangent circles of continuously varying vectors of a
  vector bundle vary continuously in the total space.
* `TauCeti.exists_orthonormal_sphereBundle_fields`: Gram–Schmidt normalization of two
  independent vertical fields tangent to the sphere fibres.
* `TauCeti.SphereBundleTwoFieldEquators F E u v`: the space `Σ` of pairs `(x, w)` with `w` a unit
  vector of the fibre through `x` orthogonal to `u x` and `v x`.
* `TauCeti.sphereBundleTwoFieldSphereFamily`: the family `σ : Σ → Map(S², Q)`.
* `TauCeti.coe_sphereBundleTwoFieldSphereFamily_sphereCollapse`: on the square, `σ (x, w)` is
  `y ↦ tangentCircle x (u x) (tangentCircle x (v x) w (2π y₀)) (2π y₁)`.
* `TauCeti.mappingSpaceEval_comp_sphereBundleTwoFieldSphereFamily`: `σ` lies over `Q`.
* `TauCeti.coe_sphereBundleTwoFieldSphereFamily_ofFiber`: over a point of `S(E_b)`, `σ` is the
  family of the sphere `S(E_b)` followed by the inclusion of the sphere fibre.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Example 6.20
  and Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Real
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

/-! ### Tangent circles in a vector bundle -/

section TangentCircle

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [TauCeti.ContinuousFiberNorm F E]
  {Y : Type*} [TopologicalSpace Y] {b : Y → B} {p u q : ∀ y, E (b y)} {θ : Y → ℝ}

/-- **Tangent circles in a vector bundle vary continuously.** If the vectors `p y`, `u y`, `q y`
of the fibre over `b y` depend continuously on `y` in the total space, and the angle `θ y` is
continuous, then so does the point `tangentCircle (p y) (u y) (q y) (θ y)`. The coefficients of
the circle are continuous because the fibre norm is. -/
theorem Continuous.tangentCircle_totalSpace
    (hp : Continuous fun y ↦ TotalSpace.mk' F (b y) (p y))
    (hu : Continuous fun y ↦ TotalSpace.mk' F (b y) (u y))
    (hq : Continuous fun y ↦ TotalSpace.mk' F (b y) (q y)) (hθ : Continuous θ) :
    Continuous fun y ↦ TotalSpace.mk' F (b y) (TauCeti.tangentCircle (p y) (u y) (q y) (θ y)) := by
  have hqp : Continuous fun y ↦ TotalSpace.mk' F (b y) (q y - p y) := by
    simpa only [sub_eq_add_neg, neg_one_smul] using
      hq.add_totalSpace ℝ ((continuous_const (y := (-1 : ℝ))).smul_totalSpace hp)
  have hn : Continuous fun y ↦ ‖q y - p y‖ := hqp.norm_bundle_of_continuousFiberNorm
  simp only [TauCeti.tangentCircle_def]
  refine (Continuous.add_totalSpace ℝ ?_ ?_).add_totalSpace ℝ ?_
  · exact (by fun_prop : Continuous fun y ↦ (1 + cos (θ y)) / 2).smul_totalSpace hp
  · exact (by fun_prop : Continuous fun y ↦ (1 - cos (θ y)) / 2).smul_totalSpace hq
  · exact (hn.div_const 2 |>.mul (continuous_sin.comp hθ)).smul_totalSpace hu

end TangentCircle

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
  inner_vec_left : ⟪vec, u base⟫ = 0
  /-- The vector `w` is orthogonal to `v x`. -/
  inner_vec_right : ⟪vec, v base⟫ = 0

namespace SphereBundleTwoFieldEquators

variable {u v : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj}

/-- A point `(x, w)` of `Σ`, as a pair of a point of `S(E)` and a point of the total space of `E`
over the same base point. -/
def toProd (p : SphereBundleTwoFieldEquators F E u v) : sphereBundle F E × TotalSpace F E :=
  (p.base, ⟨(p.base : TotalSpace F E).proj, p.vec⟩)

theorem toProd_injective : Function.Injective (toProd (u := u) (v := v)) := by
  intro p q hpq
  obtain ⟨x, w, _, _, _⟩ := p
  obtain ⟨x', w', _, _, _⟩ := q
  simp only [toProd, Prod.mk.injEq] at hpq
  obtain ⟨rfl, hw⟩ := hpq
  obtain rfl := eq_of_heq (TotalSpace.mk.inj hw).2
  rfl

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

/-! ### Normalizing two independent vertical fields -/

section Normalize

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]

/-- **Normalizing two independent vertical fields.** Let `u`, `v` be continuous vertical fields of
the unit sphere bundle, tangent to the sphere fibres (`u x ⊥ x`, `v x ⊥ x`) and linearly
independent at every point. Their Gram–Schmidt normalizations `u' x`, `v' x`
(`InnerProductSpace.gramSchmidtNormed` of the pair `(u x, v x)`) are continuous vertical fields
with `x`, `u' x`, `v' x` orthonormal, and they cut out the same equators: a vector of the fibre
through `x` is orthogonal to `u' x` and `v' x` exactly when it is orthogonal to `u x` and
`v x`. -/
theorem exists_orthonormal_sphereBundle_fields
    (hu : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u x))
    (hv : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (v x))
    (hxu : ∀ x : sphereBundle F E, ⟪(x : TotalSpace F E).2, u x⟫ = 0)
    (hxv : ∀ x : sphereBundle F E, ⟪(x : TotalSpace F E).2, v x⟫ = 0)
    (huv : ∀ x, LinearIndependent ℝ ![u x, v x]) :
    ∃ u' v' : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj,
      (Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u' x)) ∧
      (Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (v' x)) ∧
      (∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).2, u' x, v' x]) ∧
      ∀ (x : sphereBundle F E) (w : E (x : TotalSpace F E).proj),
        ⟪w, u' x⟫ = 0 ∧ ⟪w, v' x⟫ = 0 ↔ ⟪w, u x⟫ = 0 ∧ ⟪w, v x⟫ = 0 := by
  -- Orthogonality to the two vectors of a pair depends only on the plane they span, which
  -- Gram–Schmidt preserves.
  have hspan (x : sphereBundle F E) (w : E (x : TotalSpace F E).proj) :
      (∀ i, ⟪w, InnerProductSpace.gramSchmidtNormed ℝ ![u x, v x] i⟫ = 0) ↔
        ⟪w, u x⟫ = 0 ∧ ⟪w, v x⟫ = 0 := by
    have key (f : Fin 2 → E (x : TotalSpace F E).proj) :
        (∀ i, ⟪w, f i⟫ = 0) ↔ Submodule.span ℝ (Set.range f) ≤ (ℝ ∙ w)ᗮ := by
      simp [Submodule.span_le, Set.range_subset_iff,
        Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [key, InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt,
      ← key, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hc (i : Fin 2) : Continuous fun x : sphereBundle F E ↦
      TotalSpace.mk' F (x : TotalSpace F E).proj (![u x, v x] i) := by
    fin_cases i
    exacts [hu, hv]
  refine ⟨fun x ↦ InnerProductSpace.gramSchmidtNormed ℝ ![u x, v x] 0,
    fun x ↦ InnerProductSpace.gramSchmidtNormed ℝ ![u x, v x] 1,
    Continuous.gramSchmidtNormed_bundle 0 (fun i _ ↦ hc i) fun x ↦ (huv x).linearIndepOn _,
    Continuous.gramSchmidtNormed_bundle 1 (fun i _ ↦ hc i) fun x ↦ (huv x).linearIndepOn _,
    fun x ↦ orthonormal_vecCons_iff.2 ⟨mem_sphereBundle.1 x.2, ?_, ?_⟩,
    fun x w ↦ by rw [← hspan x w, Fin.forall_fin_two]⟩
  · have h := (hspan x (x : TotalSpace F E).2).2 ⟨hxu x, hxv x⟩
    exact Fin.forall_fin_two.2 ⟨h 0, h 1⟩
  · convert InnerProductSpace.gramSchmidtNormed_orthonormal (huv x) using 1
    ext i
    fin_cases i <;> rfl

end Normalize

/-! ### The family of two-spheres -/

section Pointwise

variable (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).2, u x, v x])
include h

/-! The orthonormality relations of `x`, `u x`, `v x`, read off from `h` by index. -/

private theorem inner_u_eq_zero (x : sphereBundle F E) : ⟪(x : TotalSpace F E).2, u x⟫ = 0 := by
  simpa using (h x).inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)

private theorem inner_v_eq_zero (x : sphereBundle F E) : ⟪(x : TotalSpace F E).2, v x⟫ = 0 := by
  simpa using (h x).inner_eq_zero (by decide : (0 : Fin 3) ≠ 2)

private theorem inner_v_u_eq_zero (x : sphereBundle F E) : ⟪v x, u x⟫ = 0 := by
  simpa using (h x).inner_eq_zero (by decide : (2 : Fin 3) ≠ 1)

private theorem norm_u_eq_one (x : sphereBundle F E) : ‖u x‖ = 1 := by
  simpa using (h x).norm_eq_one 1

private theorem norm_v_eq_one (x : sphereBundle F E) : ‖v x‖ = 1 := by
  simpa using (h x).norm_eq_one 2

omit h in
/-- The point at the angles `(θ₀, θ₁)` of the two-sphere of `(x, w)`, in the fibre of `E` through
`x`: the point at the angle `θ₁` of the circle through `x` tangent to `u x` and through the point at
the angle `θ₀` of the circle through `x` and `w` tangent to `v x`. -/
private def twoFieldPoint (p : SphereBundleTwoFieldEquators F E u v) (θ₀ θ₁ : ℝ) :
    E (p.base : TotalSpace F E).proj :=
  tangentCircle (p.base : TotalSpace F E).2 (u p.base)
    (tangentCircle (p.base : TotalSpace F E).2 (v p.base) p.vec θ₀) θ₁

private theorem norm_twoFieldPoint (p : SphereBundleTwoFieldEquators F E u v) (θ₀ θ₁ : ℝ) :
    ‖twoFieldPoint p θ₀ θ₁‖ = 1 := by
  have hx : ‖(p.base : TotalSpace F E).2‖ = 1 := mem_sphereBundle.1 p.base.2
  exact norm_tangentCircle hx (norm_u_eq_one h _) (inner_u_eq_zero h _)
    (norm_tangentCircle hx (norm_v_eq_one h _) (inner_v_eq_zero h _) p.norm_vec
      p.inner_vec_right θ₀)
    (inner_tangentCircle_eq_zero (inner_u_eq_zero h _) (inner_v_u_eq_zero h _) p.inner_vec_left
      θ₀) θ₁

omit h in
/-- On the boundary of the square, the two-sphere of `(x, w)` is at `x`. -/
private theorem twoFieldPoint_of_mem_boundary (p : SphereBundleTwoFieldEquators F E u v)
    {y : I^(Fin 2)} (hy : y ∈ Cube.boundary (Fin 2)) :
    twoFieldPoint p (2 * π * y 0) (2 * π * y 1) = (p.base : TotalSpace F E).2 := by
  rcases Fin.exists_fin_two.1 hy with (hi | hi) | (hi | hi) <;>
    simp [twoFieldPoint, hi]

end Pointwise

section Diagonal

variable [TopologicalSpace (TotalSpace F E)]
  (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).2, u x, v x])

/-- The **diagonal section** `x ↦ (x, x)` of `Σ → S(E)`: every point lies on its own equator. -/
def SphereBundleTwoFieldEquators.diag : C(sphereBundle F E, SphereBundleTwoFieldEquators F E u v)
    where
  toFun x :=
    { base := x
      vec := (x : TotalSpace F E).2
      norm_vec := mem_sphereBundle.1 x.2
      inner_vec_left := inner_u_eq_zero h x
      inner_vec_right := inner_v_eq_zero h x }
  continuous_toFun := continuous_iff.2 ⟨continuous_id, continuous_subtype_val⟩

@[simp]
theorem SphereBundleTwoFieldEquators.proj_comp_diag :
    proj.comp (SphereBundleTwoFieldEquators.diag h) = ContinuousMap.id (sphereBundle F E) :=
  (rfl)

end Diagonal

/-! ### Restricting vertical fields to a sphere fibre -/

section Fiber

/-- The point `z` of the sphere fibre over `b`, as a point of the sphere bundle. -/
private def fiberPoint (b : B) (z : sphere (0 : E b) 1) : sphereBundle F E :=
  ⟨⟨b, z⟩, mem_sphereBundle.2 (norm_eq_of_mem_sphere z)⟩

variable (u) in
/-- A vertical field `u` of `S(E)`, restricted to the sphere fibre over `b`: a vector field on the
unit sphere `S(E_b)`. -/
def sphereBundleFiberField (b : B) (z : sphere (0 : E b) 1) : E b :=
  u (fiberPoint b z)

/-- A point `z` of the sphere fibre over `b` and the restricted fields at `z` are orthonormal. -/
theorem orthonormal_sphereBundleFiberField
    (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).2, u x, v x]) (b : B)
    (z : sphere (0 : E b) 1) :
    Orthonormal ℝ ![(z : E b), sphereBundleFiberField u b z, sphereBundleFiberField v b z] :=
  h (fiberPoint b z)

/-- A point `(z, w)` of the space of equators of the sphere `S(E_b)`, for the restricted fields,
as a point of the space of equators of the sphere bundle over `z`. -/
def SphereBundleTwoFieldEquators.ofFiber {b : B}
    (zw : twoFieldEquators (sphereBundleFiberField u b) (sphereBundleFiberField v b)) :
    SphereBundleTwoFieldEquators F E u v where
  base := fiberPoint b zw.1.1
  vec := (zw.1.2 : E b)
  norm_vec := norm_eq_of_mem_sphere zw.1.2
  inner_vec_left := (mem_twoFieldEquators.1 zw.2).1
  inner_vec_right := (mem_twoFieldEquators.1 zw.2).2

omit [∀ b, InnerProductSpace ℝ (E b)] in
/-- At a point `x` of the sphere bundle, the field `u` restricted to the sphere fibre through `x`
is `u x`. -/
@[simp]
theorem sphereBundleFiberField_apply (x : sphereBundle F E)
    (hx : (x : TotalSpace F E).2 ∈ sphere (0 : E (x : TotalSpace F E).proj) 1) :
    sphereBundleFiberField u (x : TotalSpace F E).proj ⟨(x : TotalSpace F E).2, hx⟩ = u x :=
  (rfl)

omit [∀ b, InnerProductSpace ℝ (E b)] in
/-- The restriction of a continuous vertical field to a sphere fibre is continuous. -/
theorem continuous_sphereBundleFiberField [TopologicalSpace B] [NormedAddCommGroup F]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    (hu : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u x))
    (b : B) : Continuous (sphereBundleFiberField u b) :=
  (FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff.2 <| hu.comp <|
    ((FiberBundle.continuous_totalSpaceMk F E b).comp continuous_subtype_val).subtype_mk _

/-- The base point of `ofFiber zw` is the point `z` of the sphere fibre over `b`. -/
@[simp]
theorem SphereBundleTwoFieldEquators.coe_base_ofFiber {b : B}
    (zw : twoFieldEquators (sphereBundleFiberField u b) (sphereBundleFiberField v b)) :
    ((SphereBundleTwoFieldEquators.ofFiber zw).base : TotalSpace F E) = ⟨b, zw.1.1⟩ :=
  (rfl)

end Fiber

section Family

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]
  (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).2, u x, v x])
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
        TotalSpace.mk' F (a.1.base : TotalSpace F E).proj (a.1.base : TotalSpace F E).2 :=
      continuous_subtype_val.comp (hx.comp continuous_fst)
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
        (tangentCircle (p.base : TotalSpace F E).2 (u p.base)
          (tangentCircle (p.base : TotalSpace F E).2 (v p.base) p.vec (2 * π * y 0))
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
    sphereBundleTwoFieldSphereFamily h hu hv (SphereBundleTwoFieldEquators.diag h x) =
      ContinuousMap.const Sphere2 x := by
  ext z : 1
  obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
  refine Subtype.ext ?_
  rw [coe_sphereBundleTwoFieldSphereFamily_sphereCollapse]
  -- The base point of `diag h x` is `x` and its vector is `x.2`, by definition; the vector is a
  -- dependent field, so no rewriting lemma can replace it, and we restate the goal instead.
  change TotalSpace.mk' F _ (tangentCircle (x : TotalSpace F E).2 (u x)
    (tangentCircle (x : TotalSpace F E).2 (v x) (x : TotalSpace F E).2 _) _) = (x : TotalSpace F E)
  rw [tangentCircle_self, tangentCircle_self]

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
  rfl

end Family

end TauCeti
