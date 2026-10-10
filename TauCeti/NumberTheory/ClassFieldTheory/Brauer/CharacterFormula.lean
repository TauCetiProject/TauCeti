/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Character
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.FieldArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.CharacterCarry
import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
import TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation

/-!
# The character formula on carry classes

Let `K` be a field with absolute Galois group `G_K = Gal(Kˢ/K)`, let `χ : G_K → ℚ/ℤ` be a
character with open kernel and `a ∈ Kˣ`. The carry cocycle
`TauCeti.ContCohomology.characterCarryCocycle` of `χ` and `a` represents the Brauer class usually
written `a ∪ δχ`. This file proves the **character formula** for it: for a class formation on the
units formation of `K` whose invariant on every layer is a map `ι : Br K → ℚ/ℤ` after inflation,

```text
ι (a ∪ δχ) = χ (Art a),
```

where `Art` is the Artin map of the class formation
(`ClassFormation.apply_characterCarryCocycle_of_mk_eq_fieldArtinMap`). For a nonarchimedean local
field this is `inv_K (a ∪ δχ) = χ (Art_K a)` for the local invariant `invMap` and the absolute
local Artin map `artinMap` (`invMap_characterCarryCocycle_of_mk_eq_artinMap`), with no hypothesis
on the ramification of `χ`; at an infinite place it is the same formula for the archimedean
invariant `infiniteInvMap` and Artin map `infiniteArtinAt`
(`infiniteInvMap_characterCarryCocycle_of_mk_eq_infiniteArtinAt`).

The proof compares the carry class with the class `a₀ ∪ δχ` in the character formula
`ClassFormation.character_artinMap` of a finite layer. On the layer `V ◁ G_K` of an open normal
subgroup `V` on which `χ` vanishes, the cup product `a₀ ∪ δχ` is represented by the carry cocycle
of the character of `G_K / V` induced by `χ`
(`TauCeti.TateCohomology.cup_characterConnectingClass_eq_H2π`), whose inflation to `G_K` is the
carry cocycle of `χ` (`brInfl_artinCharacterCup`).

These are the local factors of a sum of local invariants of a global carry class: the global class
localizes to the carry classes of the restricted characters
(`TauCeti.ClassFieldTheory.ideleBrLocalization_characterCarryCocycle`), and the character formula
turns the sum of their invariants into the value of the character on a product of local Artin
symbols.

## Main results

* `TauCeti.ClassFieldTheory.brInfl_artinCharacterCup`: on the layer of an open normal subgroup,
  the inflation of `a₀ ∪ δχ` is the carry class of the character read on `G_K`.
* `TauCeti.ClassFieldTheory.ClassFormation.apply_characterCarryCocycle_of_mk_eq_fieldArtinMap`:
  the character formula on carry classes for a class formation on the units formation.
* `TauCeti.ClassFieldTheory.NormalLayer.artinCharacterCup_groundLevelEquiv_eq_H2π`: on any layer
  of any formation, `a₀ ∪ δχ` is the class of the carry cocycle of `χ` and `a`.
* `TauCeti.ClassFieldTheory.invMap_characterCarryCocycle_of_mk_eq_artinMap`: the local character
  formula `inv_K (a ∪ δχ) = χ (Art_K a)`.
* `TauCeti.ClassFieldTheory.infiniteInvMap_characterCarryCocycle_of_mk_eq_infiniteArtinAt`: the
  archimedean character formula `inv_w (a ∪ δχ) = χ (Art_w a)`.

## References

* J.-P. Serre, *Local Fields*, Chapter XI, §3, and Chapter XIV, §1.
* J. S. Milne, *Class Field Theory*, Chapter VII, §8.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory MonoidalCategory NormalLayer ContCohomology

variable {K : Type} [Field K]

/-! ### The character cup of a layer on cocycles -/

/-- **The Artin character cup is the carry class.** For a layer `V ◁ U` of a formation, an
invariant `x` of its coefficient module and a character `χ` of its abelianized Galois group, the
class `a₀ ∪ δχ ∈ H²(U/V, A^V)` of the character formula, for the ground-level element `a`
corresponding to `x`, is the class of the carry cocycle `(g, h) ↦ ⌊χ'(g) + χ'(h)⌋ • x`. -/
theorem NormalLayer.artinCharacterCup_groundLevelEquiv_eq_H2π {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (L : NormalLayer G) (F : Formation G) (x : (L.rep F).ρ.invariants)
    (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.artinCharacterCup F (L.groundLevelEquiv F x) χ =
      groupCohomology.H2π (L.rep F) (TauCeti.groupCohomology.characterCarryCocycles₂
        (χ.comp Abelianization.of.toAdditive) (L.rep F) x) := by
  rw [artinCharacterCup_apply, zeroTateClass_groundLevelEquiv, characterConnectingClass_def,
    TateCohomology.cup_characterConnectingClass_eq_H2π, ← Iso.app_inv, ← tateHIsoH_def]
  exact (L.tateHIsoH F 2).inv_hom_id_apply _

/-! ### The carry class on a layer of the units formation -/

section Layer

variable (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))

/-- The carry of a character `χ` of the layer `V ◁ G_K` at the images of `g, h ∈ G_K` is the carry
at `g, h` of a character `ψ` of `G_K` that reads `χ` through the projection `G_K → G_K ⧸ V`. -/
private theorem characterCarry_galOfOpenNormalEquiv_symm
    (χ : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ))
    (ψ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχψ : ∀ g : AbsoluteGaloisGroup K, ψ (.ofMul g) =
      χ (.ofMul (Abelianization.of
        ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))))
    (g h : AbsoluteGaloisGroup K) :
    characterCarry (χ.comp Abelianization.of.toAdditive)
        ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup))
        ((galOfOpenNormalEquiv V).symm (h : AbsoluteGaloisGroup K ⧸ V.toSubgroup)) =
      characterCarry ψ g h := by
  have hψ' : ψ = (χ.comp Abelianization.of.toAdditive).comp (MonoidHom.toAdditive
      ((galOfOpenNormalEquiv V).symm.toMonoidHom.comp (QuotientGroup.mk' V.toSubgroup))) :=
    AddMonoidHom.ext fun g ↦ hχψ g.toMul
  simp only [hψ', characterCarry_comp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]

/-- **The inflation of the Artin character cup is the carry class.** Let `χ` be a character of the
abelianized Galois group of the layer `V ◁ G_K`, and let `ψ : G_K → ℚ/ℤ` be the same character read
on `G_K`. Then for `a ∈ Kˣ` the inflation to `Br K` of the class `a₀ ∪ δχ` of the character formula
is the Brauer class of the carry cocycle of `ψ` and `a`. -/
theorem brInfl_artinCharacterCup
    (χ : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ))
    (ψ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hψ : IsOpen (ψ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (hχψ : ∀ g : AbsoluteGaloisGroup K, ψ (.ofMul g) =
      χ (.ofMul (Abelianization.of
        ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))))
    (a : Kˣ) :
    brInfl V ((ofOpenNormal V).artinCharacterCup (unitsFormation K)
        (localGroundEquiv K V (.ofMul a)) χ) =
      unitsRepH2Equiv K (characterCarryCocycle ψ hψ (baseUnitsEquivInvariants K (.ofMul a)) :
        H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) := by
  rw [← LinearEquiv.apply_symm_apply ((ofOpenNormal V).groundLevelEquiv (unitsFormation K))
      (localGroundEquiv K V (.ofMul a)),
    artinCharacterCup_groundLevelEquiv_eq_H2π (ofOpenNormal V) (unitsFormation K)]
  refine brInfl_H2π V _ (characterCarryCocycle ψ hψ (baseUnitsEquivInvariants K (.ofMul a)))
    fun g h ↦ ?_
  simp only [characterCarryCocycle_apply, TauCeti.groupCohomology.characterCarryCocycles₂_apply,
    characterCarry_galOfOpenNormalEquiv_symm V χ ψ hχψ g h, AddSubgroupClass.coe_zsmul,
    map_zsmul]
  congr 1
  rw [groundLevelEquiv_symm_apply_coe, localGroundEquiv_apply_coe, AddEquiv.symm_apply_apply]
  exact Additive.toMul.injective (Units.ext (by simp))

end Layer

/-! ### The character formula on carry classes -/

namespace ClassFormation

variable (cf : ClassFormation (unitsFormation K)) (ι : Br K →+ AddCircle (1 : ℚ))

/-- **The character formula on carry classes.** Let `cf` be a class formation on the units
formation of `K` whose invariant on the layer of every open normal subgroup `V` is `ι ∘ brInfl V`
for a homomorphism `ι : Br K → ℚ/ℤ`. Let `χ : G_K → ℚ/ℤ` be a character with open kernel and
`a ∈ Kˣ`. If `σ ∈ Gal(AlgebraicClosure K/K)` represents the Artin symbol `cf.fieldArtinMap a`, then
`ι (a ∪ δχ) = χ(σ)`, where `a ∪ δχ` is the Brauer class of the carry cocycle of `χ` and `a`. -/
theorem apply_characterCarryCocycle_of_mk_eq_fieldArtinMap
    (hι : ∀ (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
      (x : (ofOpenNormal V).H (unitsFormation K) 2),
      cf.inv (ofOpenNormal V) x = ι (brInfl V x))
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K)))) (a : Kˣ)
    (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = cf.fieldArtinMap a) :
    ι (unitsRepH2Equiv K (characterCarryCocycle χ hχ (baseUnitsEquivInvariants K (.ofMul a)) :
        H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))) =
      χ (.ofMul (absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K)) := by
  -- An open normal subgroup `V` of `G_K` on which `χ` vanishes, and the character `χ̄` of the
  -- abelianized Galois group of the layer `V ◁ G_K` that `χ` induces.
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hχ.preimage continuous_ofMul) (by simp)
  let χm : AbsoluteGaloisGroup K →* Multiplicative (AddCircle (1 : ℚ)) :=
    AddMonoidHom.toMultiplicativeRight χ
  have hVχ : V.toSubgroup ≤ χm.ker := fun g hg ↦ by
    simpa [χm] using hV hg
  let χbar : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ) :=
    MonoidHom.toAdditiveLeft (Abelianization.lift
      ((QuotientGroup.lift V.toSubgroup χm hVχ).comp (galOfOpenNormalEquiv V).toMonoidHom))
  have hχbar (g : AbsoluteGaloisGroup K) : χ (.ofMul g) = χbar (.ofMul (Abelianization.of
      ((galOfOpenNormalEquiv V).symm (g : AbsoluteGaloisGroup K ⧸ V.toSubgroup)))) := by
    simp [χbar, χm]
  -- The character formula of the layer, with the Artin symbol of the layer read off `σ`.
  have hmem : (absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K) ∈
      (ofOpenNormal V).ground := by
    simp
  have hsymm : (galOfOpenNormalEquiv V).symm
      (absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K ⧸ V.toSubgroup) =
      ((⟨_, hmem⟩ : (ofOpenNormal V).ground) : (ofOpenNormal V).Gal) := by
    rw [MulEquiv.symm_apply_eq, galOfOpenNormalEquiv_mk]
  rw [← brInfl_artinCharacterCup V χbar χ hχ hχbar a, ← hι, character_artinMap,
    ← groundEquivOfOpenNormal_unitsLevelEquiv, ← abelianizationRestrict_absoluteArtinMap,
    absoluteArtinMap_eq_of_mk_eq_fieldArtinMap cf a σ hσ, abelianizationRestrict_mk V ⟨_, hmem⟩,
    ← hsymm, ← hχbar]

end ClassFormation

/-- **The local character formula** `inv_K (a ∪ δχ) = χ (Art_K a)`. For a nonarchimedean local
field `K`, a character `χ : G_K → ℚ/ℤ` with open kernel and `a ∈ Kˣ`, if
`σ ∈ Gal(AlgebraicClosure K/K)` represents the absolute local Artin symbol `artinMap K a`, then the
local invariant of the Brauer class of the carry cocycle of `χ` and `a` is `χ(σ)`. -/
theorem invMap_characterCarryCocycle_of_mk_eq_artinMap [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K)))) (a : Kˣ)
    (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = artinMap K a) :
    invMap K (unitsRepH2Equiv K (characterCarryCocycle χ hχ
        (baseUnitsEquivInvariants K (.ofMul a)) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))) =
      χ (.ofMul (absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K)) :=
  (localClassFormation K).apply_characterCarryCocycle_of_mk_eq_fieldArtinMap (invMap K)
    (localClassFormation_inv K) χ hχ a σ
    (hσ.trans ((artinMap_apply K a).trans ((localClassFormation K).fieldArtinMap_apply a).symm))

/-- **The archimedean character formula** `inv_w (a ∪ δχ) = χ (Art_w a)`. For an infinite place
`w` of a field `K`, a character `χ : G_{K_w} → ℚ/ℤ` with open kernel and `a ∈ K_wˣ`, if
`σ ∈ Gal(AlgebraicClosure K_w/K_w)` represents the archimedean Artin symbol `infiniteArtinAt w a`,
then the archimedean invariant of the Brauer class of the carry cocycle of `χ` and `a` is `χ(σ)`. -/
theorem infiniteInvMap_characterCarryCocycle_of_mk_eq_infiniteArtinAt
    (w : NumberField.InfinitePlace K)
    (χ : Additive (AbsoluteGaloisGroup w.Completion) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup w.Completion))))
    (a : w.Completionˣ) (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w a) :
    infiniteInvMap w (unitsRepH2Equiv w.Completion (characterCarryCocycle χ hχ
        (baseUnitsEquivInvariants w.Completion (.ofMul a)) :
          H2 (AbsoluteGaloisGroup w.Completion) (UnitsCoeff w.Completion))) =
      χ (.ofMul (absoluteGaloisGroupRestrictEquiv w.Completion σ :
        AbsoluteGaloisGroup w.Completion)) :=
  (infiniteClassFormation w).apply_characterCarryCocycle_of_mk_eq_fieldArtinMap
    (infiniteInvMap w) (infiniteClassFormation_inv w) χ hχ a σ
    (hσ.trans ((infiniteArtinAt_apply w a).trans
      ((infiniteClassFormation w).fieldArtinMap_apply a).symm))

end TauCeti.ClassFieldTheory
