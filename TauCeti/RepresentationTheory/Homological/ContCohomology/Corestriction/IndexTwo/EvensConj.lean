/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.IndexTwo.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TrivialF2

/-!
# The conjugate class at index two, in every degree

Let `U` be an open subgroup of index two in a profinite group `G`. On `Hⁿ(U, 𝔽₂)` the composite
`res ∘ cor` of corestriction and restriction is `1 + s` for either element `s` of the nontrivial
coset of `U`, so `res ∘ cor - id` is the conjugation action of that coset, and it is defined
without choosing `s`. This file defines it in every degree, on Mathlib's canonical continuous
cohomology with trivial `𝔽₂` coefficients, as `OpenSubgroup.evensConj`. It is the conjugate class
`α ↦ s · α` in the identities of the index-two Evens norm, such as
`res N(α) = α ⌣ (s · α)`.

Its basic laws follow from `cor ∘ res = [G : U] = 2`
(`TauCeti.trivialF2ResMap_comp_trivialF2CorMap`) alone: it is an involution, it fixes every class
restricted from `G`, and corestriction does not see it. In degree one it is the explicit
conjugation `TauCeti.ContCohomology.evensConj1` read through the degree-one comparison
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology`, and so it is conjugation by every
element outside `U` (`TauCeti.ContCohomology.evensConj1_eq_explicitConj1`).

## Main definitions

* `OpenSubgroup.evensConj`: the endomorphism `res ∘ cor - id` of `Hⁿ(U, 𝔽₂)` for an open
  subgroup `U` of index two.

## Main results

* `OpenSubgroup.trivialF2CorMap_comp_trivialF2ResMap`,
  `OpenSubgroup.trivialF2ResMap_trivialF2CorMap`: `res ∘ cor = id + evensConj`.
* `OpenSubgroup.evensConj_comp_evensConj`: `evensConj` is an involution.
* `OpenSubgroup.trivialF2ResMap_comp_evensConj`: `evensConj` fixes restricted classes.
* `OpenSubgroup.evensConj_comp_trivialF2CorMap`: corestriction is invariant under `evensConj`.
* `OpenSubgroup.evensConj_explicitH1AddEquivContinuousCohomology`: in degree one, `evensConj` is
  the explicit conjugation `TauCeti.ContCohomology.evensConj1`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313, Lemma 2.4.
-/

public section

noncomputable section

namespace OpenSubgroup

open CategoryTheory TauCeti TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (U : OpenSubgroup G)
  (hU : U.toSubgroup.index = 2)

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass continuousSMul_trivialF2

/-- **The conjugation of the nontrivial coset on `Hⁿ(U, 𝔽₂)`**, for an open subgroup `U` of index
two, defined choice-free as `res ∘ cor - id`. At index two `res ∘ cor` is `1 + s` for every
`s ∉ U`, so this is conjugation by any such `s`, while depending on `U` alone; in degree one this
identification is `evensConj_explicitH1AddEquivContinuousCohomology`. -/
def evensConj (n : ℕ) :
    continuousCohomology n (trivialF2 U.toSubgroup) ⟶
      continuousCohomology n (trivialF2 U.toSubgroup) :=
  haveI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  trivialF2CorMap G U.toSubgroup U.isOpen n ≫ trivialF2ResMap G U.toSubgroup n - 𝟙 _

/-- The definition of `evensConj` as corestriction followed by restriction, minus the identity. -/
theorem evensConj_def (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    U.evensConj hU n =
      trivialF2CorMap G U.toSubgroup U.isOpen n ≫ trivialF2ResMap G U.toSubgroup n - 𝟙 _ :=
  (rfl)

/-- **`res ∘ cor = id + evensConj`** on `Hⁿ(U, 𝔽₂)` at index two, the definition of `evensConj`
solved for `res ∘ cor`. -/
theorem trivialF2CorMap_comp_trivialF2ResMap (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    trivialF2CorMap G U.toSubgroup U.isOpen n ≫ trivialF2ResMap G U.toSubgroup n =
      𝟙 _ + U.evensConj hU n := by
  rw [evensConj_def, add_sub_cancel]

/-- **`res (cor y) = y + evensConj y`** for every class `y ∈ Hⁿ(U, 𝔽₂)`, at index two. -/
@[simp]
theorem trivialF2ResMap_trivialF2CorMap (n : ℕ)
    (y : continuousCohomology n (trivialF2 U.toSubgroup)) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    trivialF2ResMap G U.toSubgroup n (trivialF2CorMap G U.toSubgroup U.isOpen n y) =
      y + U.evensConj hU n y := by
  have h := ConcreteCategory.congr_hom (U.trivialF2CorMap_comp_trivialF2ResMap hU n) y
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- At index two, `cor ∘ res = 2`. -/
private theorem trivialF2ResMap_comp_trivialF2CorMap_eq_two (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    trivialF2ResMap G U.toSubgroup n ≫ trivialF2CorMap G U.toSubgroup U.isOpen n =
      2 • 𝟙 (continuousCohomology n (trivialF2 G)) := by
  have : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  -- Not `rw [hU]` after the general identity: the index also occurs in the proof of the
  -- `FiniteIndex` instance, so the rewrite motive would not be type correct.
  exact (trivialF2ResMap_comp_trivialF2CorMap G U.toSubgroup U.isOpen n).trans (by rw [hU])

/-- At index two, `res ∘ cor ∘ res ∘ cor = 2 • (res ∘ cor)`. -/
private theorem cor_res_cor_res (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    trivialF2CorMap G U.toSubgroup U.isOpen n ≫ trivialF2ResMap G U.toSubgroup n ≫
        trivialF2CorMap G U.toSubgroup U.isOpen n ≫ trivialF2ResMap G U.toSubgroup n =
      2 • (trivialF2CorMap G U.toSubgroup U.isOpen n ≫ trivialF2ResMap G U.toSubgroup n) := by
  rw [reassoc_of% (trivialF2ResMap_comp_trivialF2CorMap_eq_two U hU n),
    Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul]

/-- **`evensConj` is an involution**: conjugating twice by the nontrivial coset is the
identity. -/
theorem evensConj_comp_evensConj (n : ℕ) :
    U.evensConj hU n ≫ U.evensConj hU n = 𝟙 _ := by
  simp only [evensConj_def, Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    Category.id_comp, Category.comp_id, cor_res_cor_res U hU]
  abel

/-- **`evensConj (evensConj y) = y`** for every class `y ∈ Hⁿ(U, 𝔽₂)`. -/
@[simp]
theorem evensConj_evensConj (n : ℕ) (y : continuousCohomology n (trivialF2 U.toSubgroup)) :
    U.evensConj hU n (U.evensConj hU n y) = y := by
  have h := ConcreteCategory.congr_hom (U.evensConj_comp_evensConj hU n) y
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  exact h

/-- **`evensConj` fixes restricted classes**: restriction from `G` followed by `evensConj` is
restriction. -/
theorem trivialF2ResMap_comp_evensConj (n : ℕ) :
    trivialF2ResMap G U.toSubgroup n ≫ U.evensConj hU n = trivialF2ResMap G U.toSubgroup n := by
  rw [evensConj_def, Preadditive.comp_sub, Category.comp_id,
    reassoc_of% (trivialF2ResMap_comp_trivialF2CorMap_eq_two U hU n), Preadditive.nsmul_comp,
    Category.id_comp, two_nsmul, add_sub_cancel_right]

/-- **`evensConj (res x) = res x`** for every class `x ∈ Hⁿ(G, 𝔽₂)`. -/
@[simp]
theorem evensConj_trivialF2ResMap (n : ℕ) (x : continuousCohomology n (trivialF2 G)) :
    U.evensConj hU n (trivialF2ResMap G U.toSubgroup n x) =
      trivialF2ResMap G U.toSubgroup n x := by
  have h := ConcreteCategory.congr_hom (U.trivialF2ResMap_comp_evensConj hU n) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- **Corestriction is invariant under `evensConj`**: `evensConj` followed by corestriction to
`G` is corestriction. -/
theorem evensConj_comp_trivialF2CorMap (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    U.evensConj hU n ≫ trivialF2CorMap G U.toSubgroup U.isOpen n =
      trivialF2CorMap G U.toSubgroup U.isOpen n := by
  rw [evensConj_def, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    trivialF2ResMap_comp_trivialF2CorMap_eq_two U hU n, Preadditive.comp_nsmul, Category.comp_id,
    two_nsmul, add_sub_cancel_right]

/-- **`cor (evensConj y) = cor y`** for every class `y ∈ Hⁿ(U, 𝔽₂)`. -/
@[simp]
theorem trivialF2CorMap_evensConj (n : ℕ)
    (y : continuousCohomology n (trivialF2 U.toSubgroup)) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    trivialF2CorMap G U.toSubgroup U.isOpen n (U.evensConj hU n y) =
      trivialF2CorMap G U.toSubgroup U.isOpen n y := by
  have h := ConcreteCategory.congr_hom (U.evensConj_comp_trivialF2CorMap hU n) y
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- **In degree one, `evensConj` is the explicit conjugation `evensConj1`.** A class of
`H¹(U, 𝔽₂)` presented by an explicit cocycle valued in the carrier of `trivialF2 G` is sent to the
class of its image under `TauCeti.ContCohomology.evensConj1`, both read in continuous cohomology
through the identification of the coefficient object with `trivialF2 U`. Hence `evensConj` in
degree one is conjugation by every element outside `U`
(`TauCeti.ContCohomology.evensConj1_eq_explicitConj1`). -/
theorem evensConj_explicitH1AddEquivContinuousCohomology
    (x : H1 U.toSubgroup (trivialF2 G).V) :
    U.evensConj hU 1
        ((eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).hom
          (explicitH1AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V x)) =
      (eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).hom
        (explicitH1AddEquivContinuousCohomology U.toSubgroup (trivialF2 G).V
          (evensConj1 G (trivialF2 G).V U.toSubgroup hU U.isOpen x)) := by
  have : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  rw [evensConj1_apply, map_sub, map_sub,
    ← trivialF2ResMap_explicitH1AddEquivContinuousCohomology,
    ← trivialF2CorMap_explicitH1AddEquivContinuousCohomology, trivialF2ResMap_trivialF2CorMap,
    add_sub_cancel_left]

end OpenSubgroup
