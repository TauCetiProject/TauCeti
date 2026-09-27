/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Topology.Algebra.Group.Quotient.Basic
public import TauCeti.GroupTheory.TransversalWord

/-!
# Continuity of the transversal word

For an open subgroup `U` of a group `G` with separately continuous multiplication,
`continuous_lWord` says that the transversal word is continuous in the group variable for each
fixed coset. The joint statement `continuous_lWord_inv_smul` allows the coset index to be
translated by a second group variable. Neither theorem requires the transversal map to be
continuous.

The group-theoretic calculus is in `TauCeti/GroupTheory/TransversalWord.lean`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (t : G ⧸ U → G)

/-- For an *open* subgroup `U` the transversal word `γ ↦ ℓᵗ_u(γ)` is continuous, for any map `t`
at all: the quotient `G ⧸ U` is discrete, so `γ ↦ t (γ⁻¹ • u)` is locally constant. -/
theorem continuous_lWord (hU : IsOpen (U : Set G)) (u : G ⧸ U) : Continuous (lWord U t u) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h : lWord U t u = fun γ : G => (t u)⁻¹ * γ * t (γ⁻¹ • u) := funext (lWord_def U t u)
  rw [h]
  have hmul : Continuous (fun p : G × (G ⧸ U) => (t u)⁻¹ * p.1 * t p.2) :=
    continuous_prod_of_discrete_right.mpr fun x => by
      simpa using (continuous_const_mul ((t u)⁻¹)).mul_const (t x)
  exact hmul.comp (continuous_id.prodMk (QuotientGroup.continuous_inv_smul U hU u))

/-- For an *open* subgroup `U` the transversal word is continuous jointly in its group variable
and in a coset index translated by a second group variable: `(γ, η) ↦ ℓᵗ_{γ⁻¹ • u}(η)`. Here both
`γ ↦ t (γ⁻¹ • u)` and `(γ, η) ↦ t (η⁻¹ • γ⁻¹ • u)` are locally constant, again because `G ⧸ U` is
discrete, so no continuity is required of `t` itself. -/
theorem continuous_lWord_inv_smul (hU : IsOpen (U : Set G)) (u : G ⧸ U) :
    Continuous fun q : G × G => lWord U t (q.1⁻¹ • u) q.2 := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h : (fun q : G × G => lWord U t (q.1⁻¹ • u) q.2) =
      fun q : G × G => (t (q.1⁻¹ • u))⁻¹ * q.2 * t (q.2⁻¹ • q.1⁻¹ • u) :=
    funext fun q => lWord_def U t _ _
  rw [h]
  have hfst : Continuous fun q : G × G => (q.1⁻¹ • u : G ⧸ U) :=
    (QuotientGroup.continuous_inv_smul U hU u).comp continuous_fst
  have hsnd : Continuous fun q : G × G => (q.2⁻¹ • q.1⁻¹ • u : G ⧸ U) := by
    have hact : Continuous (fun p : G × (G ⧸ U) => p.1⁻¹ • p.2) :=
      continuous_prod_of_discrete_right.mpr fun x =>
        QuotientGroup.continuous_inv_smul U hU x
    exact hact.comp (continuous_snd.prodMk hfst)
  have hmul : Continuous (fun p : G × ((G ⧸ U) × (G ⧸ U)) =>
      (t p.2.1)⁻¹ * p.1 * t p.2.2) :=
    continuous_prod_of_discrete_right.mpr fun x => by
      simpa using (continuous_const_mul ((t x.1)⁻¹)).mul_const (t x.2)
  exact hmul.comp (continuous_snd.prodMk (hfst.prodMk hsnd))

end TauCeti
