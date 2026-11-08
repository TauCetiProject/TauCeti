/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Quasi-compactness from a finite open cover of the source

A morphism is quasi-compact if its restrictions to the members of a finite open cover of its
source are quasi-compact. This allows quasi-compact morphisms to be glued along open subschemes.
Finiteness is essential: an infinite union of quasi-compact pieces need not be quasi-compact.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A morphism is quasi-compact if its restrictions to a finite open cover of the source are
quasi-compact. -/
theorem QuasiCompact.of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : X.OpenCover)
    [Finite 𝒰.I₀] (H : ∀ i, QuasiCompact (𝒰.f i ≫ f)) : QuasiCompact f := by
  constructor
  intro V hV hVc
  have he : f ⁻¹' V = ⋃ i, (𝒰.f i) '' ((𝒰.f i ≫ f) ⁻¹' V) := by
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      Set.image_preimage_eq_inter_range]
    rw [← Set.inter_iUnion, 𝒰.iUnion_range, Set.inter_univ]
  rw [he]
  exact isCompact_iUnion fun i ↦ by
    have := H i
    exact (QuasiCompact.isCompact_preimage (f := 𝒰.f i ≫ f) V hV hVc).image (𝒰.f i).continuous

end AlgebraicGeometry
