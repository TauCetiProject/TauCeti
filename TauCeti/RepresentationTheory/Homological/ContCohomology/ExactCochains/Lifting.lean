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
# Lifting continuous cochains to discrete quotients

A surjection of topological representations onto a discrete representation induces surjections
on homogeneous continuous cochains in every degree, provided the source action is jointly
continuous and the group is locally compact. This is the degreewise lifting input for Tate's
inverse-limit theorem; see K. Rubin, *Euler Systems*, Appendix B, §2, Remark 2.2.
-/

public section

open CategoryTheory Topology

namespace TauCeti.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] {Y Z : TopRep.{v} R G}

/-- A surjective coefficient map onto a discrete representation induces a surjection on
continuous homogeneous cochains in every degree, when the source action is jointly continuous.
The discrete target supplies a continuous section via `TauCeti.exists_continuous_lift`.
The kernel sequence then supplies the invariant lift via
`TopShortExact.cochainsMap_g_f_surjective`. -/
theorem continuousCochainsFunctor_map_f_surjective_of_discrete [DiscreteTopology Z.V] (g : Y ⟶ Z)
    (hg : Function.Surjective g.hom)
    (hρ : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    Function.Surjective (((continuousCochainsFunctor R G).map g).f n).hom := by
  rw [continuousCochainsFunctor_map]
  have hker : ⇑(TopRep.kerι g).hom = (Subtype.val : TopRep.ker g → Y.V) := by
    funext x
    exact TopRep.kerι_apply g x
  have hEmb : IsEmbedding (TopRep.kerι g).hom := by
    rw [hker]
    exact IsEmbedding.subtypeVal
  let S := ShortComplex.mk (TopRep.kerι g) g (TopRep.kerι_comp g)
  have hS : S.TopShortExact :=
    { isEmbedding_f := hEmb
      exact := TopRep.exact_kerι g
      exists_continuous_section := TauCeti.exists_continuous_lift hg continuous_id
      continuous_ρ₂ := hρ }
  exact hS.cochainsMap_g_f_surjective n

end TauCeti.ContinuousCohomology
