/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Strongly continuous unitary representations

A unitary representation `π` of a topological monoid is *strongly continuous* when every orbit
`g ↦ π g v` is continuous. Since every operator `π g` is an isometry, the family of operators is
uniformly Lipschitz, so strong continuity upgrades to joint continuity of the action map
`(g, v) ↦ π g v`. For a group, orbits through inverses `g ↦ π g⁻¹ v` are continuous as well,
without assuming that inversion is continuous on the group: the distance
`‖π g⁻¹ v - π h⁻¹ v‖` equals `‖π g (π h⁻¹ v) - v‖`.
-/

public section

namespace ContRepresentation.IsUnitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [TopologicalSpace G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- A strongly continuous unitary representation is jointly continuous. -/
theorem continuous_apply_prod [Monoid G] {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π)
    (hcont : ∀ v, Continuous fun g => π g v) : Continuous fun p : G × V => π p.1 p.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ 1 (fun g => (hπ.isometry g).lipschitzWith) hcont

/-- Orbits of a strongly continuous unitary group representation through inverses are
continuous. Continuity of inversion in `G` is not needed. -/
theorem continuous_inv_apply [Group G] {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π)
    (hcont : ∀ v, Continuous fun g => π g v) (v : V) : Continuous fun g => π g⁻¹ v := by
  refine continuous_iff_continuousAt.2 fun h => ?_
  have hdist (g : G) : dist (π g⁻¹ v) (π h⁻¹ v) = dist (π g (π h⁻¹ v)) v := by
    rw [← (hπ.isometry g).dist_eq, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self, dist_comm]
  have hlim : Filter.Tendsto (fun g => π g (π h⁻¹ v)) (nhds h) (nhds v) := by
    simpa [← mul_apply_eq_comp, ← map_mul] using (hcont (π h⁻¹ v)).tendsto h
  rw [tendsto_iff_dist_tendsto_zero] at hlim
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simpa only [hdist] using hlim

end ContRepresentation.IsUnitary
