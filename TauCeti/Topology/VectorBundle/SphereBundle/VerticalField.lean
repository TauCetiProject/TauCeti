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
fibre through `x` when `u x ⊥ x`. Two continuous vertical fields that are tangent to the sphere
fibres and linearly independent at every point can be normalized by Gram–Schmidt to fields `u'`,
`v'` with `x`, `u' x`, `v' x` orthonormal for every `x`, cutting out the same equators
(`TauCeti.exists_orthonormal_sphereBundle_fields`).
-/

public section

open Bundle
open scoped RealInnerProductSpace

namespace TauCeti

universe w

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {u v : ∀ x : sphereBundle F E, E (x : TotalSpace F E).proj}

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
    fun x ↦ orthonormal_vecCons_iff.2 ⟨mem_sphereBundle.1 x.2, ?_, ?_⟩,
    fun x w ↦ by rw [← hspan x w, Fin.forall_fin_two]⟩
  · have h := (hspan x (x : TotalSpace F E).2).2 ⟨hxu x, hxv x⟩
    exact Fin.forall_fin_two.2 ⟨h 0, h 1⟩
  · convert InnerProductSpace.gramSchmidtNormed_orthonormal (huv x) using 1
    ext i
    fin_cases i <;> rfl

end TauCeti
