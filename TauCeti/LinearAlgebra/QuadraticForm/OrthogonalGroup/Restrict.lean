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

## Main results

* `TauCeti.QuadraticMap.exists_orthogonalGroup_restrict_apply`: the restriction of an orthogonal
  map fixing `a` to the orthogonal complement of `a` exists.
-/

public section

open QuadraticMap

namespace TauCeti.QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- An orthogonal map fixing `a` restricts to an orthogonal map of the orthogonal complement of
`a`. This is the restriction step of the dimension induction in the Cartan--Dieudonne theorem. -/
theorem exists_orthogonalGroup_restrict_apply [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (g : QuadraticMap.orthogonalGroup Q) {a : V}
    (ha : (g : V ≃ₗ[K] V) a = a) :
    ∃ gU : QuadraticMap.orthogonalGroup
        (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a))),
      ∀ u, (gU.1 u : V) = (g : V ≃ₗ[K] V) u := by
  set U := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) (K ∙ a)
  have hgU : U.map (g : V ≃ₗ[K] V).toLinearMap = U := by
    refine Submodule.eq_of_le_of_finrank_le ?_ (LinearEquiv.finrank_map_eq _ _).ge
    rintro _ ⟨u, hu, rfl⟩ w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ha, ← map_smul]
    simpa only [QuadraticMap.associated_apply, ← map_add, LinearEquiv.coe_coe,
      QuadraticMap.map_app_of_mem_orthogonalGroup g.2] using hu _ hw
  exact ⟨⟨(g : V ≃ₗ[K] V).ofSubmodules U U hgU, QuadraticMap.mem_orthogonalGroup_iff.mpr
    fun u ↦ QuadraticMap.map_app_of_mem_orthogonalGroup g.2 u⟩, fun _ ↦ rfl⟩

end TauCeti.QuadraticMap
