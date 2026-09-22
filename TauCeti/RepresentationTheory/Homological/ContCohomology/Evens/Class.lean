/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# The index-two graph class of the Evens norm

For an open subgroup `U` of index two and a continuous homomorphism
`α : U → Multiplicative (ZMod 2)`, the two-point graph cochain constructed in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain` is a continuous
`2`-cocycle. This file takes its class in continuous cohomology.

The cochain formula uses an element `s ∉ U`, but its class does not. The difference between the
formulas attached to two such elements is the explicit continuous coboundary proved in
`TauCeti.ContCohomology.evensGraphCochain_sub_evensGraphCochain`. Thus `graphClass` only takes
the index-two hypothesis, while `graphClass_eq_cochainClass` identifies it with the cochain class
for every possible `s`.

The raw formula is `ZMod 2`-valued. The coefficient object `TauCeti.trivialF2 G` uses a universe
lift, so `TauCeti.trivialF2Equiv` crosses that lift before the explicit degree-two comparison
places the class in Mathlib's canonical continuous cohomology.

## Main definitions

* `TauCeti.ContCohomology.evensGraphCocycle`: the lifted continuous graph `2`-cocycle.
* `TauCeti.ContCohomology.evensGraphCochainClass`: its canonical continuous-cohomology class for
  a specified `s ∉ U`.
* `TauCeti.ContCohomology.graphClass`: the choice-free graph class.

## Main result

* `TauCeti.ContCohomology.graphClass_eq_cochainClass`: `graphClass` is the class of the graph
  cochain for every element outside `U`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section Choice

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An element outside an index-two open subgroup, used only to define `graphClass`. -/
private noncomputable def graphElement (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) : G :=
  Classical.choose (Subgroup.index_eq_two_iff_exists_notMem_and.mp hU)

private theorem graphElement_not_mem (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) : graphElement U hU ∉ U :=
  (Classical.choose_spec (Subgroup.index_eq_two_iff_exists_notMem_and.mp hU)).1

end Choice

section GraphClass

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

private theorem evensGraphCochain_mem_Z2 (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) :
    (fun p => (trivialF2Equiv G).symm (evensGraphCochain U.toSubgroup s α p)) ∈
      Z2 G (trivialF2 G).V := by
  refine mem_Z2_iff.2 ⟨?_, ?_⟩
  · exact (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
      (continuous_evensGraphCochain U.toSubgroup s α U.isOpen' hα)
  · intro g h j
    apply (trivialF2Equiv G).injective
    simp only [map_add, AddEquiv.apply_symm_apply, TopRep.distribMulAction_smul,
      trivialF2_ρ_apply_apply]
    exact evensGraphCochain_cocycle_identity hU hs g h j

/-- The two-point graph cochain as a continuous `2`-cocycle with coefficients in `trivialF2 G`.

The inverse of `trivialF2Equiv` is applied pointwise because the canonical coefficient object has
carrier `ULift (ZMod 2)`, while the explicit formula naturally takes values in `ZMod 2`. -/
noncomputable def evensGraphCocycle (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) : Z2 G (trivialF2 G).V :=
  ⟨fun p => (trivialF2Equiv G).symm (evensGraphCochain U.toSubgroup s α p),
    evensGraphCochain_mem_Z2 U s α hU hs hα⟩

/-- The underlying function of `evensGraphCocycle` is the graph cochain, transported across the
universe lift in `trivialF2`. -/
@[simp]
theorem coe_evensGraphCocycle (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) :
    (evensGraphCocycle U s α hU hs hα : G × G → (trivialF2 G).V) =
      fun p => (trivialF2Equiv G).symm (evensGraphCochain U.toSubgroup s α p) :=
  (rfl)

/-- The canonical continuous-cohomology class of the graph cochain attached to a specified
element `s ∉ U`.

This named intermediate is the right-hand side of `graphClass_eq_cochainClass`; unlike
`graphClass`, it records the cochain representative used to present the class. -/
noncomputable def evensGraphCochainClass [LocallyCompactSpace G] (U : OpenSubgroup G) (s : G)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hU : U.toSubgroup.index = 2)
    (hs : s ∉ U) (hα : Continuous α) : continuousCohomology 2 (trivialF2 G) :=
  (eqToHom (congrArg (continuousCohomology 2)
    (ofDiscreteModule_trivialF2 G))).hom
    (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V
      (evensGraphCocycle U s α hU hs hα))

private theorem evensGraphCochainClass_eq [LocallyCompactSpace G] (U : OpenSubgroup G)
    (s s' : G) (α : U.toSubgroup →* Multiplicative (ZMod 2))
    (hU : U.toSubgroup.index = 2) (hs : s ∉ U) (hs' : s' ∉ U) (hα : Continuous α) :
    evensGraphCochainClass U s' α hU hs' hα =
      evensGraphCochainClass U s α hU hs hα := by
  have hcocycle :
      (evensGraphCocycle U s' α hU hs' hα : H2 G (trivialF2 G).V) =
        (evensGraphCocycle U s α hU hs hα : H2 G (trivialF2 G).V) := by
    rw [H2pi_eq_iff]
    refine mem_B2_iff'.2 ⟨fun g => (trivialF2Equiv G).symm
        (evensExtend U.toSubgroup α (s⁻¹ * s') * evensExtend U.toSubgroup α g), ?_, ?_⟩
    · exact (continuous_of_discreteTopology : Continuous (trivialF2Equiv G).symm).comp
        ((continuous_of_discreteTopology : Continuous (fun x : ZMod 2 =>
          evensExtend U.toSubgroup α (s⁻¹ * s') * x)).comp
            (continuous_evensExtend U.toSubgroup α U.isOpen' hα))
    · intro g h
      apply (trivialF2Equiv G).injective
      simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, map_sub, map_add,
        AddEquiv.apply_symm_apply, coe_evensGraphCocycle, Pi.sub_apply]
      exact (evensGraphCochain_sub_evensGraphCochain hU hs hs' g h).symm
  unfold evensGraphCochainClass
  apply congrArg _
  exact congrArg (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V) hcocycle

/-- The choice-free class of the two-point graph cocycle at an index-two open subgroup.

An element outside `U` is chosen internally. The theorem `graphClass_eq_cochainClass` proves that
the result is the class of the graph cochain for every such element, so no choice occurs in the
public signature. -/
noncomputable def graphClass [LocallyCompactSpace G] (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (α : U.toSubgroup →* Multiplicative (ZMod 2))
    (hα : Continuous α) : continuousCohomology 2 (trivialF2 G) :=
  evensGraphCochainClass U (graphElement U hU) α hU (graphElement_not_mem U hU) hα

/-- The choice-free graph class is the class of the graph cochain formed using every element
outside `U`. -/
theorem graphClass_eq_cochainClass [LocallyCompactSpace G] (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (s : G) (hs : s ∉ U)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    graphClass U hU α hα = evensGraphCochainClass U s α hU hs hα := by
  unfold graphClass
  exact evensGraphCochainClass_eq U s (graphElement U hU) α hU hs
    (graphElement_not_mem U hU) hα

end GraphClass

end TauCeti.ContCohomology
