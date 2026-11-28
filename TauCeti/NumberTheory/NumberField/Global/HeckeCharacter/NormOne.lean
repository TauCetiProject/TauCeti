/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteComponent
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.CM
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue

/-!
# Hecke characters from the CM norm-one torus

`HeckeCharacter.ofNormOne` pulls an automorphic character of the CM norm-one torus back to
the idele class group along `ideleDivConj`.
`HeckeCharacter.conductorExponent_ofNormOne_eq_zero` gives unramifiedness away from the
tame support and its conjugate. The local calculation uses
`FiniteAdeleRing.unitsProj_star_eq_one_iff` to locate the two possible nontrivial coordinates.

This is the character calculation used in
`New.Data.charUnramifiedAt_rankTwist_of_N_mem` in
`grh/src/New/UpperBound/Objects/CharactersAtLevel.lean` of grh-lean at `72fead1`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public noncomputable section

open IsDedekindDomain NumberField NumberField.IsCMField
open FiniteAdeleRing
open scoped AdeleGaloisAction

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- Pull back a character of the CM norm-one ideles along `x ↦ x / conj x`.
Triviality on principal norm-one ideles makes this a Hecke character. -/
def ofNormOne (χ : cmNormOneIdeles E →ₜ* ℂˣ)
    (hχ : ∀ x : cmNormOneIdeles E, x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E → χ x = 1) :
    HeckeCharacter E :=
  let φ := χ.comp ideleDivConj
  { toMonoidHom := QuotientGroup.lift _ φ.toMonoidHom fun x hx ↦ hχ (ideleDivConj x) (by
      rw [coe_ideleDivConj_apply]
      exact (IdeleGroup.principalSubgroup (𝓞 E) E).div_mem hx (smul_mem_principalSubgroup _ hx))
    continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr φ.continuous }

/-- On an idele representative, the pullback evaluates at its quotient by its conjugate. -/
@[simp] theorem ofNormOne_apply_mk (χ : cmNormOneIdeles E →ₜ* ℂˣ) (hχ)
    (x : IdeleGroup (𝓞 E) E) :
    ofNormOne χ hχ (QuotientGroup.mk x) = χ (ideleDivConj x) := (rfl)

/-- Suppose the restriction of a norm-one character to integral finite ideles is trivial
whenever its reductions at the places of `Q` are all trivial. Then its Hecke pullback is
unramified at every place `v` for which both `v` and its conjugate are outside `Q`.
There is no restriction on the archimedean weight. -/
theorem conductorExponent_ofNormOne_eq_zero (χ : cmNormOneIdeles E →ₜ* ℂˣ) (hχ)
    {Q : Finset (HeightOneSpectrum (𝓞 E))} {v : HeightOneSpectrum (𝓞 E)}
    (hv : v ∉ Q) (hvc : v.conjPlace ∉ Q)
    (htame : ∀ (x : cmNormOneIdeles E) (a : integralUnits (𝓞 E) E),
      (x : IdeleGroup (𝓞 E) E) = IdeleGroup.ofFiniteIdele (𝓞 E) E a →
      (∀ w ∈ Q, w.integralUnitsReduction a = 1) → χ x = 1) :
    (ofNormOne χ hχ).conductorExponent v = 0 := by
  rw [conductorExponent_eq_zero_iff]
  intro u hu
  let a := unitsOfAdicCompletion E v u
  have ha : a ∈ integralUnits (𝓞 E) E := unitsOfAdicCompletion_mem_integralUnits_iff.mpr
    ((v.mem_unitFiltration_zero_adicCompletion_iff).mp hu)
  have hstar : star a ∈ integralUnits (𝓞 E) E := star_mem_integralUnits_iff.mpr ha
  let z : integralUnits (𝓞 E) E := ⟨a / star a, (integralUnits (𝓞 E) E).div_mem ha hstar⟩
  have hlocal : IdeleGroup.ofAdicCompletion (𝓞 E) E v u = IdeleGroup.ofFiniteIdele (𝓞 E) E a := by
    apply Units.ext
    rw [IdeleGroup.val_ofAdicCompletion_apply, IdeleGroup.coe_ofFiniteIdele,
      coe_unitsOfAdicCompletion_apply]
  have hconj : Units.map
      (finiteAdeleGaloisAction (maximalRealSubfield E) E (complexConj E) : _ →* _) a =
        star a := by
    apply Units.ext
    have heq := finiteAdeleGaloisAction_apply (maximalRealSubfield E) E (complexConj E)
      (a : FiniteAdeleRing (𝓞 E) E)
    simpa only [Units.coe_map, MonoidHom.coe_ofClass, ← finiteAdeleConj_def,
      finiteAdeleConj_apply, Units.coe_star] using heq
  -- At infinity the local idele and its conjugate are both trivial.
  have hz : (ideleDivConj (IdeleGroup.ofAdicCompletion (𝓞 E) E v u)).val =
      IdeleGroup.ofFiniteIdele (𝓞 E) E z := by
    rw [hlocal, coe_ideleDivConj_apply, ← ofFiniteIdele_map_finiteAdeleGaloisAction, hconj,
      ← map_div]
  have hred (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ Q) :
      w.integralUnitsReduction z = 1 := by
    have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    have hwc : w.conjPlace ≠ v :=
      fun h ↦ hvc ((w.conjPlace_conjPlace.symm.trans (congrArg HeightOneSpectrum.conjPlace h)) ▸ hw)
    have hleft : unitsProj E w a = 1 := unitsProj_unitsOfAdicCompletion_of_ne hwv u
    have hright : unitsProj E w (star a) = 1 :=
      unitsProj_star_eq_one_iff.mpr (unitsProj_unitsOfAdicCompletion_of_ne hwc u)
    have hproj : unitsProj E w z = 1 := by
      simp only [z, map_div, hleft, hright, div_one]
    simpa only [Subgroup.coe_one, map_one] using
      w.integralUnitsReduction_eq_of_unitsProj_eq z 1 hproj
  rw [finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply, ofNormOne_apply_mk]
  exact htame _ z hz hred

end TauCeti.GlobalNumberFields.HeckeCharacter
