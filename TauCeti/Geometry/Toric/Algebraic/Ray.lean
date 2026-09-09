/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Cone
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rays of toric cones

A ray of a cone is a one-dimensional face. This file defines the ray type on Mathlib's face
lattice and proves the finiteness needed to index the primitive ray generators of a toric cone.
It also records the geometric content of one-dimensionality: every nonzero point of a ray spans
it as a pointed cone when the ambient cone is salient.

## Main declarations

* `TauCeti.Toric.ToricRay`: the one-dimensional faces of a pointed cone.
* `TauCeti.Toric.IsToricCone.finite_toricRay`: a toric cone has finitely many rays.
* `TauCeti.Toric.ToricRay.exists_mem_ne_zero`: every ray contains a nonzero point.
* `TauCeti.Toric.ToricRay.eq_hull_singleton`: every nonzero point of a ray in a salient cone
  generates that ray.

## References

The ray description is from §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §1.2 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : PointedCone ℝ V}

/-- A ray of a pointed cone is a face whose linear span has real dimension one. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
abbrev ToricRay (σ : PointedCone ℝ V) :=
  {ρ : σ.Face // Module.finrank ℝ (Submodule.span ℝ ((ρ : PointedCone ℝ V) : Set V)) = 1}

namespace ToricRay

/-- The pointed cone underlying a ray. -/
abbrev toPointedCone (ρ : ToricRay σ) : PointedCone ℝ V := ρ.1.toPointedCone

instance : SetLike (ToricRay σ) V where
  coe ρ := ρ.toPointedCone
  coe_injective _ρ _τ h := Subtype.ext (PointedCone.Face.ext fun x ↦ Set.ext_iff.mp h x)

/-- Membership in the face underlying a ray is membership in the ray. Mathlib's
`PointedCone.Face.mem_toPointedCone` already normalises `x ∈ ρ.toPointedCone` to this form. -/
@[simp]
theorem mem_coe_face (ρ : ToricRay σ) (x : V) : x ∈ (ρ : σ.Face) ↔ x ∈ ρ := Iff.rfl

/-- The span of the cone underlying a ray has real dimension one. -/
@[simp]
theorem finrank_span (ρ : ToricRay σ) :
    Module.finrank ℝ (Submodule.span ℝ (ρ : Set V)) = 1 := ρ.2

/-- A ray is not the zero pointed cone. -/
theorem toPointedCone_ne_bot (ρ : ToricRay σ) : ρ.toPointedCone ≠ ⊥ := by
  intro hρ
  have hset : (ρ : Set V) = ({0} : Set V) :=
    congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) hρ
  have hdim := ρ.finrank_span
  rw [hset, Submodule.span_zero_singleton, finrank_bot] at hdim
  omega

/-- Every ray contains a nonzero point. -/
theorem exists_mem_ne_zero (ρ : ToricRay σ) : ∃ x : V, x ∈ ρ ∧ x ≠ 0 := by
  by_contra h
  push Not at h
  apply ρ.toPointedCone_ne_bot
  apply le_antisymm
  · intro x hx
    have hx0 : x = 0 := h x hx
    simp [hx0]
  · exact bot_le

/-- In a salient ambient cone, every nonzero point of a ray generates the ray as a pointed cone. -/
theorem eq_hull_singleton [FiniteDimensional ℝ V]
    (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay σ)
    {x : V} (hx : x ∈ ρ) (hx0 : x ≠ 0) : ρ.toPointedCone = PointedCone.hull ℝ {x} := by
  apply le_antisymm
  · rw [PointedCone.le_hull_singleton_iff]
    intro y hy
    have hspan_le : ℝ ∙ x ≤ Submodule.span ℝ (ρ : Set V) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr hx)
    have hspan_eq : ℝ ∙ x = Submodule.span ℝ (ρ : Set V) :=
      Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [finrank_span_singleton hx0,
        ρ.finrank_span])
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan_eq ▸ Submodule.subset_span hy)
    refine ⟨a, ?_, ha⟩
    by_contra ha0
    have ha_neg : a < 0 := lt_of_not_ge ha0
    have hnegx : -x ∈ ρ := by
      have hscale : -a⁻¹ • y ∈ ρ :=
        ρ.toPointedCone.smul_mem (neg_nonneg.mpr (inv_nonpos.mpr ha_neg.le)) hy
      rw [← ha, smul_smul, neg_mul, inv_mul_cancel₀ ha_neg.ne, neg_one_smul] at hscale
      exact hscale
    exact hσ x (ρ.1.isFaceOf.le hx) hx0 (ρ.1.isFaceOf.le hnegx)
  · exact Submodule.span_le.2 fun _ hx' ↦ by simpa using hx' ▸ hx

end ToricRay

variable {N : Type*} [AddCommGroup N] {i : N →+ V}

/-- A toric cone has finitely many rays. In fact finite generation alone makes its entire face
lattice finite; this is inherited by the subtype of one-dimensional faces. -/
theorem IsToricCone.finite_toricRay (hσ : IsToricCone i σ) : Finite (ToricRay σ) := by
  let _ := PointedCone.FG.finite_face hσ.fg
  infer_instance

end TauCeti.Toric
