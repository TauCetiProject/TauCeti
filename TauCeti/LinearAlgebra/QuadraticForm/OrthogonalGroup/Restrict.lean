/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Restricting an orthogonal map to the complement of a fixed vector

An orthogonal automorphism of a finite-dimensional quadratic space over a field in which `2` is
invertible that fixes a vector `a` preserves the orthogonal complement of `a`, and so restricts to
an orthogonal automorphism of it.

## Main definitions

* `TauCeti.QuadraticMap.orthogonalGroup.restrictOrthogonal`: the restriction of an orthogonal map
  fixing `a` to the orthogonal complement of `a`, as an element of the orthogonal group of the
  restricted form.

## Main results

* `TauCeti.QuadraticMap.map_orthogonal_span_singleton_of_mem_orthogonalGroup`: an orthogonal map
  fixing `a` maps the orthogonal complement of `a` onto itself.
* `TauCeti.QuadraticMap.coe_restrictOrthogonal_apply`: the restriction acts as the original map.
-/

public section

open QuadraticMap

namespace TauCeti.QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)] {Q : QuadraticForm K V} {a : V}

/-- An orthogonal map fixing `a` maps the orthogonal complement of `a` onto itself. -/
theorem map_orthogonal_span_singleton_of_mem_orthogonalGroup {g : V ≃ₗ[K] V}
    (hg : g ∈ QuadraticMap.orthogonalGroup Q) (ha : g a = a) :
    (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a)).map g.toLinearMap =
      LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a) := by
  refine Submodule.eq_of_le_of_finrank_le ?_ (LinearEquiv.finrank_map_eq _ _).ge
  rintro _ ⟨u, hu, rfl⟩ w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [← ha, ← map_smul]
  simpa only [QuadraticMap.associated_apply, ← map_add, LinearEquiv.coe_coe,
    QuadraticMap.map_app_of_mem_orthogonalGroup hg] using hu _ hw

/-- The restriction of an orthogonal map `g` fixing `a` to the orthogonal complement of `a`, as an
orthogonal map of the restricted form. This is the restriction step of the dimension induction in
the Cartan--Dieudonne theorem. -/
def orthogonalGroup.restrictOrthogonal (g : QuadraticMap.orthogonalGroup Q)
    (ha : (g : V ≃ₗ[K] V) a = a) :
    QuadraticMap.orthogonalGroup
      (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a))) :=
  ⟨(g : V ≃ₗ[K] V).ofSubmodules _ _ (map_orthogonal_span_singleton_of_mem_orthogonalGroup g.2 ha),
    QuadraticMap.mem_orthogonalGroup_iff.mpr fun u ↦ by
      simp only [QuadraticMap.restrict_apply, LinearEquiv.ofSubmodules_apply]
      exact QuadraticMap.map_app_of_mem_orthogonalGroup g.2 u⟩

@[simp]
theorem coe_restrictOrthogonal_apply (g : QuadraticMap.orthogonalGroup Q)
    (ha : (g : V ≃ₗ[K] V) a = a)
    (u : LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a)) :
    ((orthogonalGroup.restrictOrthogonal g ha :
      LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a) ≃ₗ[K]
        LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a)) u : V) =
      (g : V ≃ₗ[K] V) u :=
  LinearEquiv.ofSubmodules_apply _ _ _

end TauCeti.QuadraticMap
