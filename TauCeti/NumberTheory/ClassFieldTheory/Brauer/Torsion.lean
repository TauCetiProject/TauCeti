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

For a field `F`, this file transports the Kummer-sequence coefficient map

`H²(Gal(Fˢ/F), μₙ) → H²(Gal(Fˢ/F), (Fˢ)ˣ)`

to the coefficient objects for `Field.absoluteGaloisGroup F` used in local class field theory.
The result is a map `h2MuToBr` from `H²(G_F, muNRep n F)` to the cohomological Brauer group
`Br F`. When `n` is invertible in `F`, it is injective and its image is exactly the `n`-torsion of
`Br F`.

Thus a local invariant `Br F ≃+ ℚ/ℤ` restricts along `h2MuToBr` to an identification of
`H²(G_F, μₙ)` with the `n`-torsion of `ℚ/ℤ`, and hence with `ZMod n`.

## Main definitions

* `TauCeti.ClassFieldTheory.h2MuToBr`: the Kummer coefficient map from roots-of-unity cohomology
  to `Br F`.

## Main results

* `TauCeti.ClassFieldTheory.h2MuToBr_injective`: the map is injective when `n` is invertible
  in `F`.
* `TauCeti.ClassFieldTheory.h2MuToBr_range`: its image is then the `n`-torsion of `Br F`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-- **The Kummer coefficient map `H²(G_F, μₙ) → Br F`.** It is the Kummer-sequence coefficient
map on the separable-closure model, transported to `muNRep n F` and `unitsRep F`. It is injective
when `n` is invertible in `F` (`h2MuToBr_injective`). -/
def h2MuToBr : continuousCohomology 2 (muNRep n F) →+ Br F :=
  let muEquiv :=
    (explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (KummerCoeff F n)).symm.trans (muNRepH2Equiv n F)
  let unitsEquiv :=
    (explicitH2AddEquivContinuousCohomology
      (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm.trans (unitsRepH2Equiv F)
  unitsEquiv.toAddMonoidHom.comp <|
    (h2KummerToUnits F n).hom.toAddMonoidHom.comp muEquiv.symm.toAddMonoidHom

/-- `h2MuToBr` is the inverse coefficient transport to the separable-closure model, followed by
the Kummer-sequence map and the coefficient transport to `Br F`. -/
theorem h2MuToBr_apply (y : continuousCohomology 2 (muNRep n F)) :
    h2MuToBr n F y =
      unitsRepH2Equiv F
        ((explicitH2AddEquivContinuousCohomology
          (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm
            ((h2KummerToUnits F n).hom
              (explicitH2AddEquivContinuousCohomology
                (AbsoluteGaloisGroup F) (KummerCoeff F n) ((muNRepH2Equiv n F).symm y)))) := by
  rw [h2MuToBr]
  rfl

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
  rw [h2MuToBr_apply, AddEquiv.symm_apply_apply]

/-- On the explicit model, the Kummer-to-Brauer map is induced by the coefficient inclusion. -/
theorem h2MuToBr_muNRepH2Equiv_eq_explicitMap2
    (x : H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :
    h2MuToBr n F (muNRepH2Equiv n F x) =
      unitsRepH2Equiv F (explicitMap2 (AbsoluteGaloisGroup F) (KummerCoeff F n)
        (AbsoluteGaloisGroup F) (UnitsCoeff F) (ContinuousMonoidHom.id _)
        (kummerCoeffIncl F n) continuous_of_discreteTopology
        (fun g x ↦ by simpa only [ContinuousMonoidHom.coe_id, id_eq]
          using kummerCoeffIncl_equivariant F n g x) x) := by
  rw [h2MuToBr_muNRepH2Equiv, h2KummerToUnits_explicitH2AddEquivContinuousCohomology,
    AddEquiv.symm_apply_apply]

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
      h2MuToBr n F y = unitsEquiv ((h2KummerToUnits F n).hom (muEquiv.symm y)) :=
    h2MuToBr_apply n F y
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
