/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExactCochains.Basic
import TauCeti.RepresentationTheory.Continuous.TopRep.KernelCokernel
import TauCeti.Topology.Discrete

/-!
# Lifting continuous cochains along continuous sections

A map of topological representations admitting a continuous set-theoretic section induces
surjections on homogeneous continuous cochains in every degree, provided the source action is
jointly continuous and the group is locally compact. In particular, this holds for surjections
onto discrete representations. This is the degreewise lifting input for Tate's inverse-limit
theorem; see K. Rubin, *Euler Systems*, Appendix B, §2, Remark 2.2.
-/

public section

open CategoryTheory Topology

namespace TauCeti.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] {Y Z : TopRep.{v} R G}

/-- Over a locally compact topological group, a coefficient map admitting a continuous
set-theoretic section induces a surjection on continuous homogeneous cochains in every degree,
when the source action is jointly continuous. -/
theorem continuousCochainsFunctor_map_f_surjective_of_continuous_section (g : Y ⟶ Z)
    (hs : ∃ s : Z.V → Y.V, Continuous s ∧ ∀ z, g.hom (s z) = z)
    (hρ : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    Function.Surjective (((continuousCochainsFunctor R G).map g).f n).hom := by
  rw [continuousCochainsFunctor_map]
  let S := ShortComplex.mk (TopRep.kerι g) g (TopRep.kerι_comp g)
  have hS : S.TopShortExact :=
    { isEmbedding_f := TopRep.isEmbedding_kerι g
      exact := TopRep.exact_kerι g
      exists_continuous_section := hs
      continuous_ρ₂ := hρ }
  exact hS.cochainsMap_g_f_surjective n

/-- Over a locally compact topological group, a surjective coefficient map onto a discrete
representation induces a surjection on continuous homogeneous cochains in every degree, when the
source action is jointly continuous. -/
theorem continuousCochainsFunctor_map_f_surjective_of_discrete [DiscreteTopology Z.V] (g : Y ⟶ Z)
    (hg : Function.Surjective g.hom)
    (hρ : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    Function.Surjective (((continuousCochainsFunctor R G).map g).f n).hom :=
  continuousCochainsFunctor_map_f_surjective_of_continuous_section g
    (TauCeti.exists_continuous_lift hg continuous_id) hρ n

end TauCeti.ContinuousCohomology
