/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExactCochains.Basic
import TauCeti.Topology.Discrete

/-!
# Lifting continuous cochains along continuous sections

This file specializes the continuous-section criterion from `ExactCochains.Basic` to surjections
onto discrete representations: any set-theoretic section from a discrete space is continuous.
Consequently, these maps induce surjections on homogeneous continuous cochains in every degree,
provided the source action is jointly continuous. This is the degreewise lifting input for Tate's
inverse-limit theorem; see K. Rubin, *Euler Systems*, Appendix B, §2, Remark 2.2.
-/

public section

open CategoryTheory Topology

namespace TauCeti.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Y Z : TopRep.{v} R G}

/-- Over a topological group, a surjective coefficient map onto a discrete representation
induces a surjection on continuous homogeneous cochains in every degree, when the
source action is jointly continuous. -/
theorem continuousCochainsFunctor_map_f_surjective_of_discrete [DiscreteTopology Z.V] (g : Y ⟶ Z)
    (hg : Function.Surjective g.hom)
    (hρ : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    Function.Surjective (((continuousCochainsFunctor R G).map g).f n).hom :=
  continuousCochainsFunctor_map_f_surjective_of_continuous_section g
    (TauCeti.exists_continuous_lift hg continuous_id) hρ n

end TauCeti.ContinuousCohomology
