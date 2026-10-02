/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.IndexTwo

/-!
# The Evens graph class of a restricted class

Let `U` be an open subgroup of index two in a topological group `G`, with character
`χ_U : G → 𝔽₂` (`Subgroup.indexTwoCharacter`, the homomorphism with kernel `U`), and let
`y : G → 𝔽₂` be a continuous homomorphism, that is a continuous `1`-cocycle of `G` with trivial
`𝔽₂` coefficients. This file evaluates the index-two Evens graph class on the restriction of `y`
to `U`: in the explicit inhomogeneous model,

```text
N^{Ev}(res_U [y]) = [y] ⌣ [y] + [χ_U] ⌣ [y]   in H²(G, 𝔽₂),
```

where `⌣` is the `(1,1)` cup product for the multiplication pairing of `𝔽₂`. Restriction of the
class of `y` is the class of `y|_U` (`TauCeti.ContCohomology.explicitRes1_evensHomCocycle`), so
the left-hand side is the graph class of `y|_U`.

The identity is not determined by the restriction and polarization identities of the graph class,
which fix it only up to the kernel of restriction in degree two. On cochains both Shapiro
components of `y|_U` are `b = y + y(s) · χ_U`, and the graph cochain is `b ⌣ b + χ_U ⌣ b`
(`TauCeti.ContCohomology.evensGraphCochain_comp_subtype`). Expanding it leaves the two
`χ_U ⌣ χ_U` terms, which cancel in characteristic two, and `y(s) · (y ⌣ χ_U + χ_U ⌣ y)`, which is
the coboundary of `γ ↦ y(s) · y(γ) · χ_U(γ)`: the two orders of a `(1,1)` cup agree on classes
with `𝔽₂` coefficients, although not on cochains.

## Main results

* `TauCeti.ContCohomology.explicitRes1_evensHomCocycle`: restriction of the class of `y` is the
  class of `y|_U`.
* `TauCeti.ContCohomology.evensGraphCocycle_comp_subtype`: the identity above for the
  graph-cocycle class formed with a chosen `s ∉ U`.
* `TauCeti.ContCohomology.explicitGraphClass_comp_subtype`: the same identity for the choice-free
  graph class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G]

/-- The difference of the two sides of the identity, on cochains, is the coboundary of
`γ ↦ y(s) · y(γ) · χ_U(γ)`, with every factor read additively. -/
private theorem evensGraphCochain_comp_subtype_sub {U : Subgroup G} (hU : U.index = 2) {s : G}
    (hs : s ∉ U) (y : G →* Multiplicative (ZMod 2)) (γ η : G) :
    (y s).toAdd * (y η).toAdd * (U.indexTwoCharacter hU η).toAdd -
        (y s).toAdd * (y (γ * η)).toAdd * (U.indexTwoCharacter hU (γ * η)).toAdd +
        (y s).toAdd * (y γ).toAdd * (U.indexTwoCharacter hU γ).toAdd =
      evensGraphCochain U s (y.comp U.subtype) (γ, η) -
        ((y γ).toAdd * (y η).toAdd + (U.indexTwoCharacter hU γ).toAdd * (y η).toAdd) := by
  simp only [evensGraphCochain_comp_subtype hU hs, evensB1_comp_subtype hU hs,
    MonoidHom.map_mul, toAdd_mul]
  -- every value is in `𝔽₂`; the identity is the expansion described in the module docstring
  generalize (y s).toAdd = a
  generalize (y γ).toAdd = b
  generalize (y η).toAdd = b'
  generalize (U.indexTwoCharacter hU γ).toAdd = x
  generalize (U.indexTwoCharacter hU η).toAdd = x'
  revert a b b' x x'
  decide

variable [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `G` acts continuously on the trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance : ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- **Restriction of the class of a homomorphism** `y : G → 𝔽₂` to a subgroup `U` is the class of
the restricted homomorphism `y|_U`, in explicit `H¹(U, 𝔽₂)`. -/
theorem explicitRes1_evensHomCocycle (U : Subgroup G) (y : G →* Multiplicative (ZMod 2))
    (hy : Continuous y) :
    explicitRes1 G (trivialF2 G).V U (evensHomCocycle y hy : H1 G (trivialF2 G).V) =
      (evensHomCocycleAmbient U (y.comp U.subtype) (hy.comp continuous_subtype_val) :
        H1 U (trivialF2 G).V) := by
  rw [explicitRes1_mk]
  exact congrArg (fun z : Z1 U (trivialF2 G).V => (z : H1 U (trivialF2 G).V))
    (Subtype.ext (funext fun h => by simp [cocyclesMap1_apply]))

/-- **The graph-cocycle class of a restricted homomorphism.** For an open subgroup `U` of index
two, an element `s ∉ U` and a continuous homomorphism `y : G → 𝔽₂`, the class of the graph cocycle
of `y|_U` is `[y] ⌣ [y] + [χ_U] ⌣ [y]` in explicit `H²(G, 𝔽₂)`, with `χ_U` the character of `U`
and `⌣` the `(1,1)` cup product for the multiplication pairing of `𝔽₂`. -/
theorem evensGraphCocycle_comp_subtype (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    {s : G} (hs : s ∉ U) (y : G →* Multiplicative (ZMod 2)) (hy : Continuous y) :
    (evensGraphCocycle U s (y.comp U.toSubgroup.subtype) hU hs (hy.comp continuous_subtype_val) :
        H2 G (trivialF2 G).V) =
      explicitCup11 G (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V (trivialF2Pairing G)
          continuous_of_discreteTopology (trivialF2Pairing_smul_smul G)
          (evensHomCocycle y hy : H1 G (trivialF2 G).V)
          (evensHomCocycle y hy : H1 G (trivialF2 G).V) +
        explicitCup11 G (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V (trivialF2Pairing G)
          continuous_of_discreteTopology (trivialF2Pairing_smul_smul G)
          (evensHomCocycle (U.toSubgroup.indexTwoCharacter hU)
              (Subgroup.continuous_indexTwoCharacter hU U.isOpen') :
            H1 G (trivialF2 G).V)
          (evensHomCocycle y hy : H1 G (trivialF2 G).V) := by
  rw [explicitCup11_mk, explicitCup11_mk, ← QuotientAddGroup.mk_add, H2pi_eq_iff]
  refine mem_B2_iff'.2 ⟨fun x => (trivialF2Equiv G).symm ((y s).toAdd * (y x).toAdd *
      (U.toSubgroup.indexTwoCharacter hU x).toAdd), continuous_of_discreteTopology.comp
    (((continuous_const.mul (continuous_toAdd.comp hy))).mul (continuous_toAdd.comp
      (Subgroup.continuous_indexTwoCharacter hU U.isOpen'))), fun γ η => ?_⟩
  apply (trivialF2Equiv G).injective
  simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply, map_add, map_sub,
    AddEquiv.apply_symm_apply, AddSubgroup.coe_add, Pi.sub_apply,
    Pi.add_apply, coe_evensGraphCocycle, coe_evensHomCocycle, trivialF2Pairing_apply]
  exact evensGraphCochain_comp_subtype_sub hU hs y γ η

/-- **The Evens graph class of a restricted class.** For an open subgroup `U` of index two and a
continuous homomorphism `y : G → 𝔽₂`, the choice-free graph class of `y|_U`, which is the
restriction of `[y]` by `TauCeti.ContCohomology.explicitRes1_evensHomCocycle`, is
`[y] ⌣ [y] + [χ_U] ⌣ [y]` in explicit `H²(G, 𝔽₂)`, with `χ_U` the character of `U` and `⌣` the
`(1,1)` cup product for the multiplication pairing of `𝔽₂`. -/
theorem explicitGraphClass_comp_subtype (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (y : G →* Multiplicative (ZMod 2)) (hy : Continuous y) :
    explicitGraphClass U hU (y.comp U.toSubgroup.subtype) (hy.comp continuous_subtype_val) =
      explicitCup11 G (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V (trivialF2Pairing G)
          continuous_of_discreteTopology (trivialF2Pairing_smul_smul G)
          (evensHomCocycle y hy : H1 G (trivialF2 G).V)
          (evensHomCocycle y hy : H1 G (trivialF2 G).V) +
        explicitCup11 G (trivialF2 G).V (trivialF2 G).V (trivialF2 G).V (trivialF2Pairing G)
          continuous_of_discreteTopology (trivialF2Pairing_smul_smul G)
          (evensHomCocycle (U.toSubgroup.indexTwoCharacter hU)
              (Subgroup.continuous_indexTwoCharacter hU U.isOpen') :
            H1 G (trivialF2 G).V)
          (evensHomCocycle y hy : H1 G (trivialF2 G).V) := by
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hU
  rw [explicitGraphClass_eq_evensGraphCocycle U hU s hs,
    evensGraphCocycle_comp_subtype U hU hs y hy]

end TauCeti.ContCohomology
