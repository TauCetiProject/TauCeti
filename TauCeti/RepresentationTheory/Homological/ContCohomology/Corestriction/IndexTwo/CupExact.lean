/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.IndexTwo.Exact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Character

import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pairing
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ConnectingMap
import TauCeti.RepresentationTheory.Homological.ContCohomology.ConnectingMapComparison

/-!
# The index-two cup--restriction exact sequence

For an open subgroup `U` of index two in a profinite group `G`, let `χ_U` be the associated
class in `H¹(G, 𝔽₂)`. This file identifies the degree-one connecting map of the coinduced
coefficient sequence with cup product by `χ_U`. The long exact sequence then gives

```text
H¹(G, 𝔽₂) --χ_U ⌣ -→ H²(G, 𝔽₂) --res→ H²(U, 𝔽₂).
```

## Main results

* `OpenSubgroup.indexTwoDelta0_one`: the degree-zero connecting morphism sends `1` to the
  subgroup character.
* `OpenSubgroup.indexTwoDelta1_eq_cup_character`: the degree-one connecting morphism is cup
  product by the subgroup character.
* `OpenSubgroup.exact_cup_res2_of_index_two`: the displayed sequence is exact.

## References

* J. Kr. Arason, *Cohomologische Invarianten quadratischer Formen*, J. Algebra **36** (1975),
  448--491.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.5).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

namespace ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass continuousSMul_trivialF2

private noncomputable def f2One : H0 G (trivialF2 G).V :=
  ⟨(trivialF2Equiv G).symm 1, fun g => by
    rw [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply]⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem explicitCup10_f2One (x : H1 G (trivialF2 G).V) :
    explicitCup10 G _ _ _ (trivialF2Pairing G) continuous_of_discreteTopology
      (trivialF2Pairing_smul_smul G) x (f2One (G := G)) = x := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    rw [explicitCup10_mk]
    apply congrArg (fun z : Z1 G (trivialF2 G).V => (z : H1 G (trivialF2 G).V))
    apply Subtype.ext
    funext g
    apply (trivialF2Equiv G).injective
    simp [f2One]

omit [TotallyDisconnectedSpace G] in
private theorem explicitDelta0_f2One (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    (DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
      (trivialF2_two_nsmul_eq_zero G)).explicitDelta0 (f2One (G := G)) =
      (evensHomCocycle (U.toSubgroup.indexTwoCharacter hU)
        (Subgroup.continuous_indexTwoCharacter hU U.isOpen') : H1 G (trivialF2 G).V) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  rw [indexTwoShortExact_explicitDelta0]
  apply congrArg (fun z : Z1 G (trivialF2 G).V => (z : H1 G (trivialF2 G).V))
  apply Subtype.ext
  funext g
  apply (trivialF2Equiv G).injective
  by_cases hg : g ∈ U.toSubgroup
  · simp [indexTwoConnectingCocycle_apply, hg, f2One]
  · simp [indexTwoConnectingCocycle_apply, hg, f2One]

omit [TotallyDisconnectedSpace G] in
private theorem explicitDelta1_eq_cup_character (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (x : H1 G (trivialF2 G).V) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    (DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
      (trivialF2_two_nsmul_eq_zero G)).explicitDelta1 x =
      explicitCup11 G _ _ _ (trivialF2Pairing G) continuous_of_discreteTopology
        (trivialF2Pairing_smul_smul G)
        (evensHomCocycle (U.toSubgroup.indexTwoCharacter hU)
          (Subgroup.continuous_indexTwoCharacter hU U.isOpen') : H1 G (trivialF2 G).V) x := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let S := DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
    (trivialF2_two_nsmul_eq_zero G)
  let mu := DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
    (trivialF2Pairing_smul_smul G)
  have hcup := explicitDelta1_explicitCup10_right S S mu (trivialF2Pairing G)
    (trivialF2Pairing G) continuous_of_discreteTopology continuous_of_discreteTopology
    continuous_of_discreteTopology
    (DiscreteCoind.pairing_smul U.toSubgroup U.isOpen' (trivialF2Pairing G)
      (trivialF2Pairing_smul_smul G))
    (trivialF2Pairing_smul_smul G) (trivialF2Pairing_smul_smul G)
    (fun a b => by
      -- The general connecting-map lemma exposes the coefficient maps through `S`; unfolding
      -- that wrapper presents exactly the coinduction unit identity proved by `pairing_apply`.
      simp only [S, mu, DiscreteCoind.indexTwoShortExact_incl]
      change DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
        (trivialF2Pairing_smul_smul G) a (DiscreteCoind.unit G U.toSubgroup _ b) =
          DiscreteCoind.unit G U.toSubgroup _ (trivialF2Pairing G a b)
      ext g
      rw [DiscreteCoind.pairing_apply, DiscreteCoind.unit_apply, DiscreteCoind.unit_apply,
        trivialF2Pairing_smul_smul])
    (fun a b => by
      -- As above, unfolding the short-exact-sequence wrapper exposes the trace identity needed
      -- by the generic compatibility theorem.
      simp only [S, mu, DiscreteCoind.indexTwoShortExact_proj]
      change trivialF2Pairing G a (DiscreteCoind.trace G U.toSubgroup _ b) =
        DiscreteCoind.trace G U.toSubgroup _
          (DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
            (trivialF2Pairing_smul_smul G) a b)
      exact (DiscreteCoind.trace_pairing U.toSubgroup U.isOpen'
        (trivialF2Pairing G) (trivialF2Pairing_smul_smul G) a b).symm)
    x (f2One (G := G))
  rw [explicitCup10_f2One, explicitDelta0_f2One] at hcup
  rw [hcup]
  have hneg : ∀ y : H2 G (trivialF2 G).V, -y = y := fun y => by
    rw [eq_comm, eq_neg_iff_add_eq_zero, ← two_nsmul]
    exact nsmul_H2_eq_zero (trivialF2_two_nsmul_eq_zero G) y
  rw [hneg]
  have hflip : (trivialF2Pairing G).flip = trivialF2Pairing G := by
    apply AddMonoidHom.ext
    intro a
    apply AddMonoidHom.ext
    intro b
    apply (trivialF2Equiv G).injective
    simp [mul_comm]
  simpa only [hflip] using explicitCup11_comm_of_neg_eq_self G _ _ _ (trivialF2Pairing G)
    continuous_of_discreteTopology (trivialF2Pairing_smul_smul G)
    (fun z => by
      apply (trivialF2Equiv G).injective
      simp)
    x (evensHomCocycle (U.toSubgroup.indexTwoCharacter hU)
      (Subgroup.continuous_indexTwoCharacter hU U.isOpen') : H1 G (trivialF2 G).V)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Transport of the unit class along `ofDiscreteModule_trivialF2` is the explicit unit
`f2One`, read in canonical continuous cohomology. -/
private theorem eqToHom_cohomF2_one :
    (eqToHom (congrArg (continuousCohomology 0) (ofDiscreteModule_trivialF2 G).symm)).hom
        (cohomF2.one G) =
      (explicitH0IsoContinuousCohomology G (trivialF2 G).V).hom (f2One (G := G)) := by
  have key : ∀ (X : TopRep ℤ G) (hX : trivialF2 G = X),
      (eqToHom (congrArg (continuousCohomology 0) hX)).hom (cohomF2.one G) =
        ContinuousCohomology.degreeZeroClass X (eqToHom hX ((trivialF2Equiv G).symm 1))
          (by subst hX; exact fun g => trivialF2_ρ_apply_apply G g _) := by
    rintro X rfl
    simp only [eqToHom_refl]
    rw [cohomF2.one_def]
    rfl
  rw [key _ (ofDiscreteModule_trivialF2 G).symm,
    explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass]
  congr 1
  exact eqToHom_ofDiscreteModule_trivialF2_symm_apply G _

end ContCohomology

end TauCeti

namespace OpenSubgroup

open CategoryTheory TauCeti TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass continuousSMul_trivialF2

omit [TotallyDisconnectedSpace G] in
/-- **The degree-zero connecting map of the index-two coinduced sequence sends `1` to the
subgroup character.** The unit class of `H⁰(G, 𝔽₂)` is sent to `χ_U ∈ H¹(G, 𝔽₂)`; the transports
identify the discrete coefficient module with `trivialF2 G`. -/
theorem indexTwoDelta0_one (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom
        (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
          (trivialF2_two_nsmul_eq_zero G)).delta 0).hom
          ((eqToHom (congrArg (continuousCohomology 0)
            (ofDiscreteModule_trivialF2 G).symm)).hom (cohomF2.one G))) =
      U.indexTwoCharacterClass hU := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  rw [eqToHom_cohomF2_one, DiscreteShortExact.explicitIso_delta0,
    explicitH1IsoContinuousCohomology_hom_apply, explicitDelta0_f2One,
    indexTwoCharacterClass_def]
  simp

omit [TotallyDisconnectedSpace G] in
/-- **The connecting map of the index-two coinduced sequence is cup product by the subgroup
character.** This is the canonical continuous-cohomology form of the explicit cochain identity.
The transports identify the discrete coefficient module with `trivialF2 G`. -/
theorem indexTwoDelta1_eq_cup_character (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2)
    (x : continuousCohomology 1 (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G))).hom
        (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
          (trivialF2_two_nsmul_eq_zero G)).delta 1).hom x) =
      (trivialF2TopPairing G).cup 1 1 (U.indexTwoCharacterClass hU)
        ((eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_trivialF2 G))).hom x) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let S := DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
    (trivialF2_two_nsmul_eq_zero G)
  obtain ⟨a, rfl⟩ := (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V).surjective x
  let a' : DiscreteH1 G (trivialF2 G).V :=
    (discreteH1Equiv G (trivialF2 G).V).symm a
  have ha : (explicitH1IsoContinuousCohomology G (trivialF2 G).V).hom a' =
      explicitH1AddEquivContinuousCohomology G (trivialF2 G).V a := by
    rw [explicitH1IsoContinuousCohomology_hom_apply]
    simp [a']
  rw [← ha, S.explicitIso_delta1, explicitH2IsoContinuousCohomology_hom_apply,
    explicitH1IsoContinuousCohomology_hom_apply]
  simp only [a', AddEquiv.apply_symm_apply]
  rw [indexTwoCharacterClass_def,
    trivialF2TopPairing_cup_one_one_explicitH1, explicitDelta1_eq_cup_character]

/-- **The index-two cup--restriction sequence is exact in degree two.** A class in
`H²(G, 𝔽₂)` restricts to zero on an open subgroup `U` of index two exactly when it is the
cup product of the character class `χ_U` with a class in `H¹(G, 𝔽₂)`. -/
theorem exact_cup_res2_of_index_two (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    Function.Exact
      ((trivialF2TopPairing G).cup 1 1 (U.indexTwoCharacterClass hU))
      (trivialF2ResMap G U.toSubgroup 2) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  -- Generalize the coefficient object so that the equality identifying the discrete module with
  -- `trivialF2 G` can be eliminated before applying the long exact sequence.
  have key : ∀ (X : TopRep ℤ G) (hX : ofDiscreteModule ℤ G (trivialF2 G).V = X),
      Function.Exact
        (fun x => (eqToHom (congrArg (continuousCohomology 2) hX)).hom
          (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
            (trivialF2_two_nsmul_eq_zero G)).delta 1).hom
            ((eqToHom (congrArg (continuousCohomology 1) hX.symm)).hom x)))
        (fun x => (ContinuousCohomology.res U.toSubgroup X 2).hom x) := by
    rintro X rfl
    simpa only [eqToHom_refl, ConcreteCategory.id_apply, one_add_one_eq_two] using
      (ContinuousCohomology.exact_delta_res_of_index_two U.toSubgroup U.isOpen'
        (trivialF2 G).V hU (trivialF2_two_nsmul_eq_zero G) 1)
  have h := key (trivialF2 G) (ofDiscreteModule_trivialF2 G)
  have hf (x : cohomF2 G 1) :
      (eqToHom (congrArg (continuousCohomology 2)
          (ofDiscreteModule_trivialF2 G))).hom
        (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
          (trivialF2_two_nsmul_eq_zero G)).delta 1).hom
            ((eqToHom (congrArg (continuousCohomology 1)
              (ofDiscreteModule_trivialF2 G).symm)).hom x)) =
        (trivialF2TopPairing G).cup 1 1 (U.indexTwoCharacterClass hU) x := by
    have hx : (eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_trivialF2 G))).hom
        ((eqToHom (congrArg (continuousCohomology 1)
          (ofDiscreteModule_trivialF2 G).symm)).hom x) = x := by
      rw [← ConcreteCategory.comp_apply (eqToHom _) (eqToHom _), eqToHom_trans,
        eqToHom_refl, ConcreteCategory.id_apply]
    calc
      _ = (trivialF2TopPairing G).cup 1 1 (U.indexTwoCharacterClass hU)
          ((eqToHom (congrArg (continuousCohomology 1)
            (ofDiscreteModule_trivialF2 G))).hom
              ((eqToHom (congrArg (continuousCohomology 1)
                (ofDiscreteModule_trivialF2 G).symm)).hom x)) :=
        indexTwoDelta1_eq_cup_character U hU _
      _ = _ := congrArg ((trivialF2TopPairing G).cup 1 1
        (U.indexTwoCharacterClass hU)) hx
  intro y
  constructor
  · intro hy
    have hy' : (ContinuousCohomology.res U.toSubgroup (trivialF2 G) 2).hom y = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (eqToHom
        (congrArg (continuousCohomology 2) (res_trivialF2 G U.toSubgroup)))).injective
      simpa only [map_zero, trivialF2ResMap_def, ConcreteCategory.comp_apply] using hy
    obtain ⟨x, hxy⟩ := (h y).1 hy'
    exact ⟨x, (hf x).symm.trans hxy⟩
  · rintro ⟨x, hxy⟩
    have hy' := (h y).2 ⟨x, (hf x).trans hxy⟩
    simp only [trivialF2ResMap_def, ConcreteCategory.comp_apply, hy', map_zero]

end OpenSubgroup
