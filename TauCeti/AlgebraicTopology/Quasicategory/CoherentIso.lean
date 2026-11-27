/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.CoherentIso
public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic

/-!
# Extending equivalence edges to coherent isomorphisms

An edge of a quasicategory is an equivalence precisely when it extends to a map from
Mathlib's coherent isomorphism. An equivalence edge factors through the core, which
is Kan, and the standard-edge inclusion is anodyne.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.7.
-/

public section

universe u

open CategoryTheory Limits Simplicial
open SSet.modelCategoryQuillen

namespace SSet

/-- An edge of a quasicategory extends to the coherent isomorphism exactly when it is
an equivalence. -/
theorem exists_extension_coherentIso_iff {D : SSet.{u}} [Quasicategory D]
    (f : Δ[1] ⟶ D) :
    (∃ g : coherentIso ⟶ D, coherentIso.edgeInclusion ≫ g = f) ↔
      (Edge.mk' (yonedaEquiv f)).IsEquivalence := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact (coherentIso.invStructOfEqMapHom (g := g) (by simp [yonedaEquiv_comp])).isEquivalence
  · have hr : Subcomplex.range f ≤ D.core := by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      exact (Edge.edge_mem_core_iff (Edge.mk' (yonedaEquiv f))).2 hf
    let a := Subcomplex.lift f hr
    have := coherentIso.anodyneExtensions_edgeInclusion (terminal.from (D.core : SSet))
      ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
    have sq : CommSq a coherentIso.edgeInclusion (terminal.from (D.core : SSet))
        (terminal.from coherentIso) := ⟨by simp⟩
    exact ⟨sq.lift ≫ D.core.ι, by rw [sq.fac_left_assoc, Subcomplex.lift_ι]⟩

end SSet
