/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep

/-!
# Roots-of-unity cohomology inside the Brauer group

For a field `F`, this file transports the Kummer-sequence inclusion

`H²(Gal(Fˢ/F), μₙ) → H²(Gal(Fˢ/F), (Fˢ)ˣ)`

to the coefficient objects for `Field.absoluteGaloisGroup F` used in local class field theory.
The resulting map `h2MuToBr` embeds `H²(G_F, muNRep n F)` into the cohomological Brauer group
`Br F`. When `n` is invertible in `F`, its image is exactly the `n`-torsion of `Br F`.

Thus a local invariant `Br F ≃+ ℚ/ℤ` restricts along `h2MuToBr` to an identification of
`H²(G_F, μₙ)` with the `n`-torsion of `ℚ/ℤ`, and hence with `ZMod n`.

## Main definitions

* `TauCeti.ClassFieldTheory.muNRepH2Equiv`: the degree-two coefficient transport from the
  separable-closure model to `muNRep n F`.
* `TauCeti.ClassFieldTheory.h2MuToBr`: the inclusion of roots-of-unity cohomology into `Br F`.

## Main results

* `TauCeti.ClassFieldTheory.h2MuToBr_injective`: the inclusion is injective.
* `TauCeti.ClassFieldTheory.h2MuToBr_range`: its image is the `n`-torsion of `Br F`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

attribute [local instance] TopRep.distribMulAction

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-- **`H²` of `μₙ` transported to `muNRep n F`.** This is pullback along
`absoluteGaloisGroupRestrictEquiv`, the coefficient dictionary
`kummerCoeffEquivMuNRep`, and the comparison between explicit and canonical continuous
cohomology. -/
def muNRepH2Equiv :
    H2 (AbsoluteGaloisGroup F) (KummerCoeff F n) ≃+
      continuousCohomology 2 (muNRep n F) :=
  (explicitMap2Equiv (AbsoluteGaloisGroup F) (KummerCoeff F n)
      (Field.absoluteGaloisGroup F) (muNRep n F).V
      (absoluteGaloisGroupRestrictEquiv F) (kummerCoeffEquivMuNRep n F)
      (continuous_kummerCoeffEquivMuNRep n F) (continuous_kummerCoeffEquivMuNRep_symm n F)
      fun g x => (kummerCoeffEquivMuNRep_smul n F g x).trans
        (TopRep.distribMulAction_smul _ g _).symm).trans <|
    (muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete

/-- `muNRepH2Equiv` is the degree-two explicit transport followed by the comparison with
Mathlib's canonical continuous cohomology. -/
theorem muNRepH2Equiv_apply (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    muNRepH2Equiv n F x =
      (muNRep n F).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 (AbsoluteGaloisGroup F) (KummerCoeff F n)
          (Field.absoluteGaloisGroup F) (muNRep n F).V
          (absoluteGaloisGroupRestrictEquiv F)
          (kummerCoeffEquivMuNRep n F).toAddMonoidHom
          (continuous_kummerCoeffEquivMuNRep n F)
          (fun g x => (kummerCoeffEquivMuNRep_smul n F g x).trans
            (TopRep.distribMulAction_smul _ g _).symm) x) := by
  rw [muNRepH2Equiv, AddEquiv.trans_apply, explicitMap2Equiv_apply]

/-- **The inclusion `H²(G_F, μₙ) → Br F`.** It is the Kummer-sequence coefficient map
on the separable-closure model, transported to `muNRep n F` and `unitsRep F`. -/
def h2MuToBr : continuousCohomology 2 (muNRep n F) →+ Br F :=
  let muEquiv :=
    (explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (KummerCoeff F n)).symm.trans (muNRepH2Equiv n F)
  let unitsEquiv :=
    (explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm.trans (unitsRepH2Equiv F)
  unitsEquiv.toAddMonoidHom.comp <|
    (h2KummerToUnits F n).hom.toAddMonoidHom.comp muEquiv.symm.toAddMonoidHom

/-- On a class in the separable-closure model, `h2MuToBr` is the Kummer-sequence map followed by
the coefficient transport to `Br F`. -/
theorem h2MuToBr_muNRepH2Equiv
    (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    h2MuToBr n F (muNRepH2Equiv n F x) =
      unitsRepH2Equiv F
        ((explicitH2AddEquivContinuousCohomology
          (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm
            ((h2KummerToUnits F n).hom
              (explicitH2AddEquivContinuousCohomology
                (AbsoluteGaloisGroup F) (KummerCoeff F n) x))) := by
  simp [h2MuToBr]

/-- **The map from roots-of-unity cohomology into the Brauer group is injective** when `n` is
invertible in `F`. -/
theorem h2MuToBr_injective (hn : IsUnit (n : F)) :
    Function.Injective (h2MuToBr n F) := by
  rw [h2MuToBr]
  exact
    ((explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm.trans
        (unitsRepH2Equiv F)).injective.comp <|
      (h2KummerToUnits_injective hn).comp <|
        ((explicitH2AddEquivContinuousCohomology
          (AbsoluteGaloisGroup F) (KummerCoeff F n)).symm.trans
            (muNRepH2Equiv n F)).symm.injective

/-- **The image of `H²(G_F, μₙ)` in `Br F` is the `n`-torsion**, when `n` is invertible in
`F`. -/
theorem h2MuToBr_range (hn : IsUnit (n : F)) (x : Br F) :
    (∃ y, h2MuToBr n F y = x) ↔ n • x = 0 := by
  let muEquiv :=
    (explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (KummerCoeff F n)).symm.trans (muNRepH2Equiv n F)
  let unitsEquiv :=
    (explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm.trans (unitsRepH2Equiv F)
  have h_apply (y : continuousCohomology 2 (muNRep n F)) :
      h2MuToBr n F y = unitsEquiv ((h2KummerToUnits F n).hom (muEquiv.symm y)) := by
    rfl
  constructor
  · rintro ⟨y, hy⟩
    have hz : n • (h2KummerToUnits F n).hom (muEquiv.symm y) = 0 :=
      (h2KummerToUnits_range hn _).mp ⟨muEquiv.symm y, rfl⟩
    rw [← hy, h_apply, ← map_nsmul, hz, map_zero]
  · intro hx
    have hz : n • unitsEquiv.symm x = 0 := by
      rw [← map_nsmul, hx, map_zero]
    obtain ⟨z, hz⟩ := (h2KummerToUnits_range hn (unitsEquiv.symm x)).mpr hz
    refine ⟨muEquiv z, ?_⟩
    rw [h_apply, muEquiv.symm_apply_apply, hz, unitsEquiv.apply_symm_apply]

end TauCeti.ClassFieldTheory
