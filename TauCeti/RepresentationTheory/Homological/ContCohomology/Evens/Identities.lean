/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.IndexTwo.EvensConj
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Character
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.NormOfRestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Polarization
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Restriction

/-!
# The index-two Evens identities on canonical cohomology

Let `U` be an open subgroup of index two in a topological group `G` and let
`α : U → 𝔽₂` be a continuous homomorphism, with canonical class `[α] ∈ H¹(U, 𝔽₂)`. The graph
class `TauCeti.ContCohomology.graphClass` of `α` is the value `N^{Ev}[α] ∈ H²(G, 𝔽₂)` of the
index-two Evens norm. This file reads three of its characterizing identities, proved on explicit
cocycles in the neighbouring files, in Mathlib's canonical continuous cohomology, against the
canonical operations: restriction `TauCeti.trivialF2ResMap`, corestriction
`TauCeti.trivialF2CorMap`, the cup product of `TauCeti.trivialF2TopPairing`, the choice-free
conjugation `OpenSubgroup.evensConj` and the character class `OpenSubgroup.indexTwoCharacterClass`:

```text
res_U N^{Ev}[α]                          = [α] ⌣ (s · [α]),
N^{Ev}[α + β] - N^{Ev}[α] - N^{Ev}[β]    = cor ([α] ⌣ (s · [β])),
N^{Ev}[y|_U]                             = [y] ⌣ [y] + χ_U ⌣ [y]      (y : G → 𝔽₂).
```

The degree-one classes are those of the explicit cocycles
`TauCeti.ContCohomology.evensHomCocycleAmbient` and `TauCeti.ContCohomology.evensHomCocycle`,
read through the degree-one comparison and the identification of the coefficient object with the
trivial `𝔽₂` object, which is how the restriction, corestriction, cup and conjugation comparisons
present them. Each identity is the image of its explicit counterpart under the degree-two
comparison, once restriction, corestriction, the cup product and the conjugation are known to
commute with the comparisons.

The same three identities are then stated for the norm
`TauCeti.ContCohomology.evensNormIndexTwo : H¹(U, 𝔽₂) → H²(G, 𝔽₂)` on arbitrary classes, with no
homomorphism in the statement. Every class of `H¹(U, 𝔽₂)` is the `homClass` of a continuous
homomorphism, and that class is the one the graph-class identities are stated with
(`homClass_eq_evensHomCocycleAmbient`).

## Main results

* `TauCeti.ContCohomology.trivialF2ResMap_graphClass`: restriction of the graph class is the cup
  of `[α]` with its conjugate.
* `TauCeti.ContCohomology.graphClass_polarization`: the failure of additivity of the graph class
  is the corestriction of the cup of `[α]` with the conjugate of `[β]`.
* `TauCeti.ContCohomology.graphClass_comp_subtype`: the graph class of a restricted homomorphism
  is `[y] ⌣ [y] + χ_U ⌣ [y]`.
* `TauCeti.ContCohomology.trivialF2ResMap_evensNormIndexTwo`,
  `TauCeti.ContCohomology.evensNormIndexTwo_polarization`,
  `TauCeti.ContCohomology.evensNormIndexTwo_trivialF2ResMap`: the same three identities for the
  index-two Evens norm of a class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass continuousSMul_trivialF2

/-- **The ambient-coefficient class of a homomorphism on a subgroup is its `homClass`.** For a
subgroup `U` and a continuous homomorphism `α : U → 𝔽₂`, the explicit class of
`evensHomCocycleAmbient U α`, valued in the carrier of `trivialF2 G` and read in
`continuousCohomology 1 (trivialF2 U)` through `ofDiscreteModule_subgroup_trivialF2`, is
`homClass U α`. This is the form in which restriction, corestriction, the cup product and
`OpenSubgroup.evensConj` present degree-one classes of `U`. -/
theorem homClass_eq_evensHomCocycleAmbient (U : Subgroup G)
    (α : U →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    homClass U α hα =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_subgroup_trivialF2 G U))).hom
        (explicitH1AddEquivContinuousCohomology U (trivialF2 G).V
          (evensHomCocycleAmbient U α hα)) := by
  rw [homClass_eq_cochainClass, explicitH1AddEquivContinuousCohomology_apply]
  refine (TopRep.eqToHom_π_eq_cochainClass (ofDiscreteModule_subgroup_trivialF2 G U) _ _ _
    (Subtype.ext ?_)).symm
  ext g₀ g₁
  rw [inhomogeneousCochain1_apply]
  -- The transported cocycle is read through a `cast` between the two lifted `ZMod 2` carriers,
  -- which `trivialF2Equiv_cast` removes after decoding both sides to `ZMod 2`.
  refine (TopRep.eval_iCycles_eqToHom (ofDiscreteModule_subgroup_trivialF2 G U) _ (n := 1)
    (T := TopRep.V) (fun B a => a.val g₀ g₁)).trans ?_
  apply (trivialF2Equiv U).injective
  refine (trivialF2Equiv_cast G (H := U) _ _).trans ?_
  refine (congrArg (fun z => trivialF2Equiv G (z.val g₀ g₁))
    (iCycles_cocycleEquiv1 U (trivialF2 G).V (evensHomCocycleAmbient U α hα))).trans ?_
  simp only [coe_evensHomCocycleAmbient, trivialF2Equiv_symm_apply, cochainEquiv1_apply,
    homogeneous1_apply, Subgroup.smul_def, TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply,
    trivialF2Equiv_apply]

/-- **The norm of a restricted class, on canonical cohomology.** For an open subgroup `U` of index
two and a continuous homomorphism `y : G → 𝔽₂`, the graph class of `y|_U` is
`[y] ⌣ [y] + χ_U ⌣ [y]` in `H²(G, 𝔽₂)`, where `[y]` is the canonical class of `y` and `χ_U` the
class of the character of `U`. -/
theorem graphClass_comp_subtype [LocallyCompactSpace G] (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (y : G →* Multiplicative (ZMod 2)) (hy : Continuous y) :
    graphClass U hU (y.comp U.toSubgroup.subtype) (hy.comp continuous_subtype_val) =
      (trivialF2TopPairing G).cup 1 1
          ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
            (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V
              (evensHomCocycle y hy)))
          ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
            (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V
              (evensHomCocycle y hy))) +
        (trivialF2TopPairing G).cup 1 1 (U.indexTwoCharacterClass hU)
          ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
            (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V
              (evensHomCocycle y hy))) := by
  have h := congrArg (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V)
    (explicitGraphClass_comp_subtype U hU y hy)
  simp only [map_add] at h
  have h := congrArg
    (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G))).hom h
  simp only [map_add] at h
  simp only [graphClass_eq_explicitGraphClass]
  simp only [OpenSubgroup.indexTwoCharacterClass_def,
    trivialF2TopPairing_cup_one_one_explicitH1]
  rw [h]

/-- **The index-two Evens norm of a restricted class.** For an open subgroup `U` of index two and
`y ∈ H¹(G, 𝔽₂)`, `N^{Ev}(res_U y) = y ⌣ y + χ_U ⌣ y` in `H²(G, 𝔽₂)`, where `χ_U` is the class of
the character of `U`. -/
theorem evensNormIndexTwo_trivialF2ResMap [LocallyCompactSpace G] (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (y : continuousCohomology 1 (trivialF2 G)) :
    evensNormIndexTwo U hU (trivialF2ResMap G U.toSubgroup 1 y) =
      (trivialF2TopPairing G).cup 1 1 y y +
        (trivialF2TopPairing G).cup 1 1 (U.indexTwoCharacterClass hU) y := by
  obtain ⟨y, hy, rfl⟩ := homClass_surjective G y
  rw [trivialF2ResMap_homClass, evensNormIndexTwo_homClass, homClass_def]
  exact graphClass_comp_subtype U hU y hy

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Restriction of the graph class, on canonical cohomology.** For an open subgroup `U` of index
two in a profinite group `G` and a continuous homomorphism `α : U → 𝔽₂` with canonical class
`[α] ∈ H¹(U, 𝔽₂)`, restriction to `U` of the graph class of `α` is the cup product of `[α]` with
its conjugate `OpenSubgroup.evensConj`. -/
theorem trivialF2ResMap_graphClass (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    trivialF2ResMap G U.toSubgroup 2 (graphClass U hU α hα) =
      (trivialF2TopPairing U.toSubgroup).cup 1 1
        ((eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).hom
          (explicitH1AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V
            (evensHomCocycleAmbient U.toSubgroup α hα)))
        (U.evensConj hU 1
          ((eqToHom (congrArg (continuousCohomology 1)
            (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).hom
            (explicitH1AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V
              (evensHomCocycleAmbient U.toSubgroup α hα)))) := by
  have : LocallyCompactSpace U.toSubgroup :=
    (U.toSubgroup.isClosed_of_isOpen U.isOpen).locallyCompactSpace
  have h := congrArg
    (fun z ↦
      (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_subgroup_trivialF2 G
        U.toSubgroup))).hom
        (explicitH2AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V z))
    (explicitRes2_explicitGraphClass U hU α hα)
  simp only [graphClass_eq_explicitGraphClass,
    trivialF2ResMap_explicitH2AddEquivContinuousCohomology]
  simp only [
    OpenSubgroup.evensConj_explicitH1AddEquivContinuousCohomology,
    trivialF2TopPairing_cup_one_one_explicitH1_subgroup]
  exact h

/-- **Restriction of the index-two Evens norm.** For an open subgroup `U` of index two in a
profinite group `G` and `x ∈ H¹(U, 𝔽₂)`, `res_U N^{Ev}(x) = x ⌣ (s · x)`, the conjugate `s · x`
being the choice-free `OpenSubgroup.evensConj`. -/
theorem trivialF2ResMap_evensNormIndexTwo (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    trivialF2ResMap G U.toSubgroup 2 (evensNormIndexTwo U hU x) =
      (trivialF2TopPairing U.toSubgroup).cup 1 1 x (U.evensConj hU 1 x) := by
  obtain ⟨α, hα, rfl⟩ := homClass_surjective U.toSubgroup x
  rw [evensNormIndexTwo_homClass, homClass_eq_evensHomCocycleAmbient]
  exact trivialF2ResMap_graphClass U hU α hα

/-- **Polarization of the graph class, on canonical cohomology.** For an open subgroup `U` of
index two in a profinite group `G` and continuous homomorphisms `α β : U → 𝔽₂` with canonical
classes `[α], [β] ∈ H¹(U, 𝔽₂)`, the failure of additivity of the graph class,
`N^{Ev}[α + β] - N^{Ev}[α] - N^{Ev}[β]`, is the corestriction of the cup product of `[α]` with
the conjugate `OpenSubgroup.evensConj` of `[β]`. The sum `α + β` is written `α * β`, the
pointwise product in `Multiplicative (ZMod 2)`. -/
theorem graphClass_polarization (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (α β : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) (hβ : Continuous β) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    graphClass U hU (α * β) (hα.mul hβ) - graphClass U hU α hα - graphClass U hU β hβ =
      trivialF2CorMap G U.toSubgroup U.isOpen 2
        ((trivialF2TopPairing U.toSubgroup).cup 1 1
          ((eqToHom (congrArg (continuousCohomology 1)
            (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).hom
            (explicitH1AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V
              (evensHomCocycleAmbient U.toSubgroup α hα)))
          (U.evensConj hU 1
            ((eqToHom (congrArg (continuousCohomology 1)
              (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).hom
              (explicitH1AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V
                (evensHomCocycleAmbient U.toSubgroup β hβ))))) := by
  have : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  have : LocallyCompactSpace U.toSubgroup :=
    (U.toSubgroup.isClosed_of_isOpen U.isOpen).locallyCompactSpace
  have h := congrArg (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V)
    (explicitGraphClass_polarization U hU α β hα hβ)
  simp only [map_sub] at h
  have h := congrArg
    (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G))).hom h
  simp only [map_sub] at h
  simp only [graphClass_eq_explicitGraphClass]
  simp only [
    OpenSubgroup.evensConj_explicitH1AddEquivContinuousCohomology,
    trivialF2TopPairing_cup_one_one_explicitH1_subgroup,
    trivialF2CorMap_explicitH2AddEquivContinuousCohomology]
  rw [h]

/-- **Polarization of the index-two Evens norm.** For an open subgroup `U` of index two in a
profinite group `G` and `x, y ∈ H¹(U, 𝔽₂)`, the failure of additivity
`N^{Ev}(x + y) - N^{Ev}(x) - N^{Ev}(y)` is the corestriction of `x ⌣ (s · y)`, with the
**conjugate** `OpenSubgroup.evensConj` of `y`. -/
theorem evensNormIndexTwo_polarization (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (x y : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    evensNormIndexTwo U hU (x + y) - evensNormIndexTwo U hU x - evensNormIndexTwo U hU y =
      trivialF2CorMap G U.toSubgroup U.isOpen 2
        ((trivialF2TopPairing U.toSubgroup).cup 1 1 x (U.evensConj hU 1 y)) := by
  obtain ⟨α, hα, rfl⟩ := homClass_surjective U.toSubgroup x
  obtain ⟨β, hβ, rfl⟩ := homClass_surjective U.toSubgroup y
  rw [← homClass_mul, evensNormIndexTwo_homClass, evensNormIndexTwo_homClass,
    evensNormIndexTwo_homClass, homClass_eq_evensHomCocycleAmbient,
    homClass_eq_evensHomCocycleAmbient]
  exact graphClass_polarization U hU α β hα hβ

end TauCeti.ContCohomology
