/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.GroupTheory.TransversalWord
public import TauCeti.Topology.Algebra.Group.Quotient.Basic

/-!
# Continuity of the transversal word

For a subgroup `U` of a group `G` and a map `t : G ⧸ U → G`, the transversal word
`ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)` of `TauCeti.lWord` is a purely group-theoretic construction.
If multiplication on `G` is separately continuous and `U` is *open*, then
`γ ↦ ℓᵗ_u(γ)` is continuous (`TauCeti.continuous_lWord`). Openness of `U` makes `G ⧸ U`
discrete, so `γ ↦ γ⁻¹ • u`, and hence `γ ↦ t (γ⁻¹ • u)`, is locally constant. On each such
neighborhood the word has the form `γ ↦ c₁ * γ * c₂` for fixed `c₁` and `c₂`, which is
continuous by separate continuity of multiplication. No continuity is required of `t` itself.
The variant
`TauCeti.continuous_lWord_inv_smul` lets the coset index itself be translated by a second group
variable, which is the shape the degree-two corestriction sum is indexed by.

The continuity results live here, separate from the group-theoretic transversal calculus in
`TauCeti/GroupTheory/TransversalWord.lean`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (t : G ⧸ U → G)

private theorem continuous_lWord_mul [DiscreteTopology (G ⧸ U)] :
    Continuous (fun p : G × ((G ⧸ U) × (G ⧸ U)) =>
      (t p.2.1)⁻¹ * p.1 * t p.2.2) :=
  continuous_prod_of_discrete_right.mpr fun v => by
    simpa using (continuous_const_mul ((t v.1)⁻¹)).mul_const (t v.2)

/-- For an *open* subgroup `U` the transversal word `γ ↦ ℓᵗ_u(γ)` is continuous, for any map `t`
at all: the quotient `G ⧸ U` is discrete, so `γ ↦ t (γ⁻¹ • u)` is locally constant. -/
theorem continuous_lWord (hU : IsOpen (U : Set G)) (u : G ⧸ U) : Continuous (lWord U t u) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h : lWord U t u = fun γ : G => (t u)⁻¹ * γ * t (γ⁻¹ • u) := funext (lWord_def U t u)
  rw [h]
  exact (continuous_lWord_mul U t).comp
    (continuous_id.prodMk
      (continuous_const.prodMk (U.continuous_inv_smul_const u)))

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
    (U.continuous_inv_smul_const u).comp continuous_fst
  have hsnd : Continuous fun q : G × G => (q.2⁻¹ • q.1⁻¹ • u : G ⧸ U) :=
    U.continuous_inv_smul.comp (continuous_snd.prodMk hfst)
  exact (continuous_lWord_mul U t).comp (continuous_snd.prodMk (hfst.prodMk hsnd))

end TauCeti
