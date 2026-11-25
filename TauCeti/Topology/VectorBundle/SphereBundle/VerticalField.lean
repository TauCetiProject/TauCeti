/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GramSchmidt
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# Vertical vector fields on a unit sphere bundle

Let `E → B` be a real vector bundle whose fibres are inner product spaces, with continuous fibre
norm, and let `S(E)` be its unit sphere bundle. A **vertical vector field** on `S(E)` assigns to
each unit vector `x ∈ E_b` a vector `u x ∈ E_b` of the same fibre; it is tangent to the sphere
fibre through `x` when `u x ⊥ x`. Restricted to the sphere fibre `S(E_b)` over `b`, a vertical
field is a vector field on the unit sphere `S(E_b)` (`TauCeti.sphereBundleFiberField`), continuous
when the vertical field is (`TauCeti.continuous_sphereBundleFiberField`). Two continuous vertical
fields that are tangent to the sphere fibres and linearly independent at every point can be
normalized by Gram–Schmidt to fields `u'`, `v'` with `x`, `u' x`, `v' x` orthonormal for every `x`,
cutting out the same equators (`TauCeti.exists_orthonormal_sphereBundle_fields`).
-/

public section

open Bundle Metric
open scoped RealInnerProductSpace

namespace TauCeti

universe w

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, NormedAddCommGroup (E b)]
  {u v : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj}

/-! ### Restricting vertical fields to a sphere fibre -/

section Fiber

variable (u) in
/-- A vertical field `u` of `S(E)`, restricted to the sphere fibre over `b`: a vector field on the
unit sphere `S(E_b)`. -/
def sphereBundleFiberField (b : B) (z : sphere (0 : E b) 1) : E b :=
  u ⟨⟨b, z⟩, mem_sphereBundle.2 (norm_eq_of_mem_sphere z)⟩

variable (u) in
/-- At a point `z` of the sphere fibre over `b`, the field `u` restricted to that fibre is `u` at
the point `z` of the sphere bundle. -/
@[simp]
theorem sphereBundleFiberField_apply (b : B) (z : sphere (0 : E b) 1) :
    sphereBundleFiberField u b z = u ⟨⟨b, z⟩, mem_sphereBundle.2 (norm_eq_of_mem_sphere z)⟩ :=
  (rfl)

/-- A point `z` of the sphere fibre over `b` and the restricted fields at `z` are orthonormal. -/
theorem orthonormal_sphereBundleFiberField [∀ b, InnerProductSpace ℝ (E b)]
    (h : ∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).snd, u x, v x]) (b : B)
    (z : sphere (0 : E b) 1) :
    Orthonormal ℝ ![(z : E b), sphereBundleFiberField u b z, sphereBundleFiberField v b z] :=
  h ⟨⟨b, z⟩, mem_sphereBundle.2 (norm_eq_of_mem_sphere z)⟩

/-- The restriction of a continuous vertical field to a sphere fibre is continuous. -/
theorem continuous_sphereBundleFiberField [TopologicalSpace B] [NormedAddCommGroup F]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    (hu : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u x))
    (b : B) : Continuous (sphereBundleFiberField u b) :=
  (FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff.2 <| hu.comp <|
    ((FiberBundle.continuous_totalSpaceMk F E b).comp continuous_subtypeVal).subtype_mk _

end Fiber

/-! ### Normalizing two independent vertical fields -/

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E]

/-- **Normalizing two independent vertical fields.** Let `u`, `v` be continuous vertical fields of
the unit sphere bundle, tangent to the sphere fibres (`u x ⊥ x`, `v x ⊥ x`) and linearly
independent at every point. Then there are continuous vertical fields `u'`, `v'` with `x`, `u' x`,
`v' x` orthonormal for every `x`, cutting out the same equators: a vector of the fibre through `x`
is orthogonal to `u' x` and `v' x` exactly when it is orthogonal to `u x` and `v x`. -/
theorem exists_orthonormal_sphereBundle_fields
    (hu : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u x))
    (hv : Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (v x))
    (hxu : ∀ x : sphereBundle F E, ⟪(x : TotalSpace F E).snd, u x⟫ = 0)
    (hxv : ∀ x : sphereBundle F E, ⟪(x : TotalSpace F E).snd, v x⟫ = 0)
    (huv : ∀ x, LinearIndependent ℝ ![u x, v x]) :
    ∃ u' v' : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj,
      (Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (u' x)) ∧
      (Continuous fun x : sphereBundle F E ↦ TotalSpace.mk' F (x : TotalSpace F E).proj (v' x)) ∧
      (∀ x : sphereBundle F E, Orthonormal ℝ ![(x : TotalSpace F E).snd, u' x, v' x]) ∧
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
      ← key]
    simp [Fin.forall_fin_two]
  have hc (i : Fin 2) : Continuous fun x : sphereBundle F E ↦
      TotalSpace.mk' F (x : TotalSpace F E).proj (![u x, v x] i) := by
    fin_cases i
    exacts [hu, hv]
  refine ⟨fun x ↦ InnerProductSpace.gramSchmidtNormed ℝ ![u x, v x] 0,
    fun x ↦ InnerProductSpace.gramSchmidtNormed ℝ ![u x, v x] 1,
    Continuous.gramSchmidtNormed_bundle 0 (fun i _ ↦ hc i) fun x ↦ (huv x).linearIndepOn _,
    Continuous.gramSchmidtNormed_bundle 1 (fun i _ ↦ hc i) fun x ↦ (huv x).linearIndepOn _,
    fun x ↦ orthonormal_vecCons_iff.2 ⟨mem_sphereBundle.1 x.property, ?_, ?_⟩,
    fun x w ↦ by rw [← hspan x w, Fin.forall_fin_two]⟩
  · have h := (hspan x (x : TotalSpace F E).snd).2 ⟨hxu x, hxv x⟩
    exact Fin.forall_fin_two.2 ⟨h 0, h 1⟩
  · convert InnerProductSpace.gramSchmidtNormed_orthonormal (huv x) using 1
    ext i
    fin_cases i <;> rfl

end TauCeti
