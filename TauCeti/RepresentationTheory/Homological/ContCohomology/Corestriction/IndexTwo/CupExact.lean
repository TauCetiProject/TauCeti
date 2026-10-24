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
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ConnectingMap.AllDegrees
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Unit
import TauCeti.RepresentationTheory.Homological.ContCohomology.ConnectingMapComparison

/-!
# The index-two cup--restriction exact sequence

For an open subgroup `U` of index two in a profinite group `G`, let `χ_U` be the associated
class in `H¹(G, 𝔽₂)`. This file identifies every connecting map of the coinduced
coefficient sequence with cup product by `χ_U`. The long exact sequence then gives

```text
Hⁿ(U, 𝔽₂) --cor→ Hⁿ(G, 𝔽₂) --(- ⌣ χ_U)→ Hⁿ⁺¹(G, 𝔽₂) --res→ Hⁿ⁺¹(U, 𝔽₂).
```

## Main results

* `OpenSubgroup.indexTwoDelta0_one`: the degree-zero connecting morphism sends `1` to the
  subgroup character.
* `OpenSubgroup.indexTwoDelta_eq_cup_character`: every connecting morphism is cup product
  by the subgroup character.
* `OpenSubgroup.exact_cor_cup_of_index_two` and `OpenSubgroup.exact_cup_res_of_index_two`:
  the displayed sequence is exact.

## References

* J. Kr. Arason, *Cohomologische Invarianten quadratischer Formen*, J. Algebra **36** (1975),
  448--491.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.4.5) and (1.6.5).
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

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem discreteTrivialF2_cup_one_right (n : ℕ)
    (x : continuousCohomology n (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    (ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)).cup n 0 x
      ((eqToHom (congrArg (continuousCohomology 0)
        (ofDiscreteModule_trivialF2 G).symm)).hom (cohomF2.one G)) = x := by
  rw [eqToHom_cohomF2_one, explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass]
  apply TopPairing.cup_one_right
  intro a
  have hright (b : (trivialF2 G).V) :
      (ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)).bil
        b ((trivialF2Equiv G).symm 1) = b := by
    rw [ofDiscreteModulePairing_bil_apply]
    apply (trivialF2Equiv G).injective
    simp only [trivialF2Pairing_apply, AddEquiv.apply_symm_apply, mul_one]
  exact hright a

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
private theorem discreteTrivialF2_pairing_transport (a b : (trivialF2 G).V) :
    eqToHom (ofDiscreteModule_trivialF2 G)
        ((ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)).bil a b) =
      (trivialF2TopPairing G).bil (eqToHom (ofDiscreteModule_trivialF2 G) a)
        (eqToHom (ofDiscreteModule_trivialF2 G) b) := by
  rw [ofDiscreteModulePairing_bil_apply, eqToHom_ofDiscreteModule_trivialF2_apply,
    eqToHom_ofDiscreteModule_trivialF2_apply, eqToHom_ofDiscreteModule_trivialF2_apply,
    trivialF2TopPairing_bil_apply, trivialF2Pairing_apply]

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

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem indexTwoShortExact_pairing_incl (U : OpenSubgroup G)
    [U.toSubgroup.FiniteIndex] (hU : U.toSubgroup.index = 2) :
    let S := DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
      (trivialF2_two_nsmul_eq_zero G)
    let P := ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)
    let μ := DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
      (trivialF2Pairing_smul_smul G)
    let Q := ofDiscreteModulePairing μ (DiscreteCoind.pairing_smul U.toSubgroup U.isOpen'
      (trivialF2Pairing G) (trivialF2Pairing_smul_smul G))
    ∀ a b : (trivialF2 G).V, S.incl (P.bil a b) = Q.bil a (S.incl b) := by
  intro S P μ Q a b
  simp only [S, Q, P, DiscreteCoind.indexTwoShortExact_incl,
    ofDiscreteModulePairing_bil_apply]
  -- Restricting to the underlying coefficient carriers identifies the bundled unit.
  change DiscreteCoind.unit G U.toSubgroup _ (trivialF2Pairing G a b) =
    DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
      (trivialF2Pairing_smul_smul G) a (DiscreteCoind.unit G U.toSubgroup _ b)
  ext g
  rw [DiscreteCoind.pairing_apply, DiscreteCoind.unit_apply, DiscreteCoind.unit_apply,
    trivialF2Pairing_smul_smul]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem indexTwoShortExact_pairing_proj (U : OpenSubgroup G)
    [U.toSubgroup.FiniteIndex] (hU : U.toSubgroup.index = 2) :
    let S := DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
      (trivialF2_two_nsmul_eq_zero G)
    let P := ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)
    let μ := DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
      (trivialF2Pairing_smul_smul G)
    let Q := ofDiscreteModulePairing μ (DiscreteCoind.pairing_smul U.toSubgroup U.isOpen'
      (trivialF2Pairing G) (trivialF2Pairing_smul_smul G))
    ∀ (a : (trivialF2 G).V) (b : DiscreteCoind G U.toSubgroup (trivialF2 G).V),
      S.proj (Q.bil a b) = P.bil a (S.proj b) := by
  intro S P μ Q a b
  simp only [S, Q, P, DiscreteCoind.indexTwoShortExact_proj,
    ofDiscreteModulePairing_bil_apply]
  -- The short exact sequence records the underlying additive map of the trace.
  change DiscreteCoind.trace G U.toSubgroup _
    (DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
      (trivialF2Pairing_smul_smul G) a b) =
    trivialF2Pairing G a (DiscreteCoind.trace G U.toSubgroup _ b)
  exact DiscreteCoind.trace_pairing U.toSubgroup U.isOpen'
    (trivialF2Pairing G) (trivialF2Pairing_smul_smul G) a b

omit [TotallyDisconnectedSpace G] in
/-- **The connecting map of the index-two coinduced sequence is cup product by the subgroup
character in every degree.** The transports identify the discrete coefficient module with
`trivialF2 G`. Placing the character on the right keeps the resulting degree `n + 1`. -/
theorem indexTwoDelta_eq_cup_character (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (n : ℕ)
    (x : continuousCohomology n (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    (eqToHom (congrArg (continuousCohomology (n + 1)) (ofDiscreteModule_trivialF2 G))).hom
        (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
          (trivialF2_two_nsmul_eq_zero G)).delta n).hom x) =
      (trivialF2TopPairing G).cup n 1
        ((eqToHom (congrArg (continuousCohomology n)
          (ofDiscreteModule_trivialF2 G))).hom x) (U.indexTwoCharacterClass hU) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let S := DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
    (trivialF2_two_nsmul_eq_zero G)
  let P := ofDiscreteModulePairing (trivialF2Pairing G) (trivialF2Pairing_smul_smul G)
  let μ := DiscreteCoind.pairing U.toSubgroup U.isOpen' (trivialF2Pairing G)
    (trivialF2Pairing_smul_smul G)
  let Q := ofDiscreteModulePairing μ (DiscreteCoind.pairing_smul U.toSubgroup U.isOpen'
    (trivialF2Pairing G) (trivialF2Pairing_smul_smul G))
  let u := (eqToHom (congrArg (continuousCohomology 0)
    (ofDiscreteModule_trivialF2 G).symm)).hom (cohomF2.one G)
  have hcup := S.delta_cup_right S Q P P
    (indexTwoShortExact_pairing_incl U hU) (indexTwoShortExact_pairing_proj U hU)
    n 0 x u
  rw [discreteTrivialF2_cup_one_right] at hcup
  dsimp only [S] at hcup
  simp only [Nat.add_zero] at hcup
  have hnat := P.cup_coeffMap (trivialF2TopPairing G)
    (eqToHom (ofDiscreteModule_trivialF2 G)) (eqToHom (ofDiscreteModule_trivialF2 G))
    (eqToHom (ofDiscreteModule_trivialF2 G))
    discreteTrivialF2_pairing_transport
    n 1 x ((S.delta 0).hom u)
  rw [ContinuousCohomology.coeffMap_eqToHom, ContinuousCohomology.coeffMap_eqToHom,
    ContinuousCohomology.coeffMap_eqToHom] at hnat
  -- Every mod-two class is its own negative, so the degree sign is invisible.
  obtain h | h := neg_one_pow_eq_or ℤ n
  · rw [h, one_smul] at hcup
    rw [hcup, hnat, indexTwoDelta0_one U hU]
  · rw [h, neg_one_zsmul] at hcup
    rw [hcup, map_neg, hnat, indexTwoDelta0_one U hU]
    exact ZModModule.neg_eq_self _

/-- **The index-two cup--restriction sequence is exact in every degree.** A class in
`Hⁿ⁺¹(G, 𝔽₂)` restricts to zero on `U` exactly when it is the cup product of a class in
`Hⁿ(G, 𝔽₂)` with the subgroup character. -/
theorem exact_cup_res_of_index_two (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    Function.Exact
      (fun x => (trivialF2TopPairing G).cup n 1 x (U.indexTwoCharacterClass hU))
      (trivialF2ResMap G U.toSubgroup (n + 1)) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  -- Eliminate the coefficient equality before transporting the long exact sequence.
  have key : ∀ (X : TopRep ℤ G) (hX : ofDiscreteModule ℤ G (trivialF2 G).V = X),
      Function.Exact
        (fun x => (eqToHom (congrArg (continuousCohomology (n + 1)) hX)).hom
          (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
            (trivialF2_two_nsmul_eq_zero G)).delta n).hom
            ((eqToHom (congrArg (continuousCohomology n) hX.symm)).hom x)))
        (fun x => (ContinuousCohomology.res U.toSubgroup X (n + 1)).hom x) := by
    rintro X rfl
    simpa only [eqToHom_refl, ConcreteCategory.id_apply] using
      (ContinuousCohomology.exact_delta_res_of_index_two U.toSubgroup U.isOpen'
        (trivialF2 G).V hU (trivialF2_two_nsmul_eq_zero G) n)
  have h := key (trivialF2 G) (ofDiscreteModule_trivialF2 G)
  have hf (x : cohomF2 G n) :
      (eqToHom (congrArg (continuousCohomology (n + 1))
          (ofDiscreteModule_trivialF2 G))).hom
        (((DiscreteCoind.indexTwoShortExact G U.toSubgroup (trivialF2 G).V hU U.isOpen'
          (trivialF2_two_nsmul_eq_zero G)).delta n).hom
            ((eqToHom (congrArg (continuousCohomology n)
              (ofDiscreteModule_trivialF2 G).symm)).hom x)) =
        (trivialF2TopPairing G).cup n 1 x (U.indexTwoCharacterClass hU) := by
    have hx : (eqToHom (congrArg (continuousCohomology n)
          (ofDiscreteModule_trivialF2 G))).hom
        ((eqToHom (congrArg (continuousCohomology n)
          (ofDiscreteModule_trivialF2 G).symm)).hom x) = x := by
      rw [← ConcreteCategory.comp_apply (eqToHom _) (eqToHom _), eqToHom_trans,
        eqToHom_refl, ConcreteCategory.id_apply]
    rw [indexTwoDelta_eq_cup_character U hU n, hx]
  intro y
  constructor
  · intro hy
    have hy' : (ContinuousCohomology.res U.toSubgroup (trivialF2 G) (n + 1)).hom y = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (eqToHom
        (congrArg (continuousCohomology (n + 1)) (res_trivialF2 G U.toSubgroup)))).injective
      simpa only [map_zero, trivialF2ResMap_def, ConcreteCategory.comp_apply] using hy
    obtain ⟨x, hxy⟩ := (h y).1 hy'
    exact ⟨x, (hf x).symm.trans hxy⟩
  · rintro ⟨x, hxy⟩
    have hy' := (h y).2 ⟨x, (hf x).trans hxy⟩
    simp only [trivialF2ResMap_def, ConcreteCategory.comp_apply, hy', map_zero]

/-- **The index-two corestriction--cup sequence is exact in every degree.** The kernel of
cupping with the subgroup character consists exactly of the corestrictions from `U`. -/
theorem exact_cor_cup_of_index_two (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2) (n : ℕ) :
    letI : U.toSubgroup.FiniteIndex := ⟨by omega⟩
    Function.Exact (trivialF2CorMap G U.toSubgroup U.isOpen' n)
      (fun x => (trivialF2TopPairing G).cup n 1 x (U.indexTwoCharacterClass hU)) := by
  let _ : U.toSubgroup.FiniteIndex := ⟨by omega⟩
  let e := (eqToIso (congrArg (continuousCohomology n)
    (ofDiscreteModule_trivialF2 G))).toContinuousLinearEquiv.toLinearEquiv
  let eU := (eqToIso (congrArg (continuousCohomology n)
    (ofDiscreteModule_subgroup_trivialF2 G U.toSubgroup))).toContinuousLinearEquiv.toLinearEquiv
  let e' := (eqToIso (congrArg (continuousCohomology (n + 1))
    (ofDiscreteModule_trivialF2 G))).toContinuousLinearEquiv.toLinearEquiv
  have h := ContinuousCohomology.exact_corestriction_delta_of_index_two U.toSubgroup U.isOpen'
    (trivialF2 G).V hU (trivialF2_two_nsmul_eq_zero G) n
  have h' := (LinearEquiv.conj_exact_iff_exact _ _ e).2 h
  have h'' := (LinearEquiv.precomp_exact_iff_exact (e := eU.symm)).2 h'
  have h''' := (LinearEquiv.postcomp_exact_iff_exact (e := e')).2 h''
  convert h''' using 1
  · ext x
    simp only [trivialF2CorMap_def, ConcreteCategory.comp_apply]
    -- The linear equivalences `e` and `eU.symm` apply the same coefficient transports.
    rfl
  · ext x
    have hx : (eqToHom (congrArg (continuousCohomology n)
        (ofDiscreteModule_trivialF2 G))).hom (e.symm x) = x :=
      e.apply_symm_apply x
    have hd := indexTwoDelta_eq_cup_character U hU n (e.symm x)
    rw [hx] at hd
    exact hd.symm

end OpenSubgroup
