/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.IndexTwo

/-!
# Restriction of the explicit Evens graph-cocycle class

Let `U` be an open subgroup of index two in a topological group `G` and let
`α : U →* Multiplicative (ZMod 2)` be a continuous homomorphism. For a chosen `s ∉ U`, this file
computes the restriction of the class of `evensGraphCocycle U s α` in the explicit
inhomogeneous cohomology model. It is the `(1,1)` cup product of the class of `α` with its
conjugate, for the multiplication pairing of `𝔽₂`:
```text
res_U [graph_s(α)] = [α] ⌣ evensConj1([α]).
```
Here `TauCeti.ContCohomology.evensConj1` is defined on explicit `H¹` as `res ∘ cor - id`, and
equals conjugation by every element outside `U`. The class of `α` is represented by the cocycle
`TauCeti.ContCohomology.evensHomCocycleAmbient` with the lifted trivial `𝔽₂` coefficients of the
ambient group.

## Main result

* `TauCeti.ContCohomology.explicitRes2_evensGraphCocycle`: in explicit cohomology, the restriction
  of the graph-cocycle class for a chosen `s ∉ U` is the cup product with the conjugate class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- Restriction of the explicit graph-cocycle class for a chosen `s ∉ U` is the `(1,1)` cup
product of the class of `α` with its choice-free conjugate `TauCeti.ContCohomology.evensConj1`,
for the multiplication pairing of `𝔽₂`. Both sides lie in explicit `H²(U, 𝔽₂)`. -/
theorem explicitRes2_evensGraphCocycle (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    {s : G} (hs : s ∉ U) (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    explicitRes2 G (trivialF2 G).V U.toSubgroup
        (evensGraphCocycle U s α hU hs hα : H2 G (trivialF2 G).V) =
      explicitCup11 U.toSubgroup (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V
        (trivialF2Pairing G) continuous_of_discreteTopology
        (fun u m n => trivialF2Pairing_smul_smul G (u : G) m n)
        (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V)
        (evensConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen'
          (evensHomCocycleAmbient U.toSubgroup α hα : H1 U.toSubgroup (trivialF2 G).V)) := by
  have := Subgroup.normal_of_index_eq_two hU
  rw [evensConj1_eq_explicitConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen' hs,
    explicitConj1_apply_eq_smul, smul_mk, explicitCup11_mk, explicitRes2_mk]
  apply congrArg (fun z : Z2 U.toSubgroup (trivialF2 G).V => (z : H2 U.toSubgroup (trivialF2 G).V))
  apply Subtype.ext
  funext ⟨γ, η⟩
  have hconj : s⁻¹ * (η : G) * s ∈ U.toSubgroup :=
    (Subgroup.normal_of_index_eq_two hU).conj_mem' η η.2 s
  simp only [cocyclesMap2_coe, cochainsMap2_apply, ContinuousMonoidHom.coe_subgroupSubtype,
    Subgroup.subtype_apply, AddMonoidHom.id_apply, coe_evensGraphCocycle, cocyclesMap1_coe,
    cochainsMap1_apply, coe_evensHomCocycleAmbient, DistribSMul.toAddMonoidHom_apply,
    MonoidHom.coe_ofClass, Subgroup.inverseConjugationHom_apply, trivialF2Pairing_apply,
    Subgroup.smul_def, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply,
    AddEquiv.apply_symm_apply]
  rw [evensGraphCochain_apply_of_mem_of_mem hU hs γ.2 η.2, evensExtend_of_mem γ.2,
    evensExtend_of_mem hconj]

end TauCeti.ContCohomology
