/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.Basic

/-!
# Base change of Kummer-cup Brauer classes

A primitive root of unity selects a pairing on Kummer coefficients. The cup product of two
Kummer classes, followed by the inclusion into the Brauer group, commutes with arbitrary field
extension, including extension to a completion. Thus the local symbols of a global pair are
invariants of the localizations of one global Brauer class.

The construction uses the existing Kummer map, explicit cup product and coefficient dictionaries;
it introduces no new cohomology carrier. The root of unity is transported along the field map,
so the statement preserves the chosen normalization.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1) and (1.5.3).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
variable (n : ℕ) (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- Base change commutes with the inclusion of roots-of-unity cohomology into the Brauer group,
read on the explicit roots-of-unity model. -/
theorem brBaseChange_h2MuToBr_muNRepH2Equiv
    (x : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :
    brBaseChange K L (h2MuToBr n K (muNRepH2Equiv n K x)) =
      h2MuToBr n L (muNRepH2Equiv n L
        (explicitMap2 (AbsoluteGaloisGroup K) (KummerCoeff K n) (AbsoluteGaloisGroup L)
          (KummerCoeff L n) (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange n τ)
          continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ) x)) := by
  rw [h2MuToBr_muNRepH2Equiv_eq_explicitCoeff2, h2MuToBr_muNRepH2Equiv_eq_explicitCoeff2,
    brBaseChange_apply K L τ, AddEquiv.symm_apply_apply]
  apply congrArg (unitsRepH2Equiv L)
  -- Use composition as a term to preserve the equivariance proofs of the bundled inclusions.
  have hleft := explicitMap2_comp (AbsoluteGaloisGroup K) (KummerCoeff K n)
    (AbsoluteGaloisGroup K) (UnitsCoeff K) (ContinuousMonoidHom.id _)
    (kummerCoeffInclHom K n).toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ (kummerCoeffInclHom K n).map_smul g m)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) (absoluteGaloisGroupMap τ)
    (unitsCoeffBaseChange τ) continuous_of_discreteTopology (unitsCoeffBaseChange_smul τ)
  have hright := explicitMap2_comp (AbsoluteGaloisGroup K) (KummerCoeff K n)
    (AbsoluteGaloisGroup L) (KummerCoeff L n) (absoluteGaloisGroupMap τ)
    (kummerCoeffBaseChange n τ) continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) (ContinuousMonoidHom.id _)
    (kummerCoeffInclHom L n).toAddMonoidHom continuous_of_discreteTopology
    (fun g m ↦ (kummerCoeffInclHom L n).map_smul g m)
  rw [explicitCoeff2_eq_explicitMap2, explicitCoeff2_eq_explicitMap2]
  refine DFunLike.congr_fun (hleft.symm.trans ((explicitMap2_congr_of_eq
    (AbsoluteGaloisGroup K) (KummerCoeff K n) (AbsoluteGaloisGroup L) (UnitsCoeff L)
    _ _ _ _ ?_ ?_).trans hright)) x
  · ext g
    simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_id, id_eq]
  · refine AddMonoidHom.ext fun y ↦ ?_
    apply Additive.toMul.injective
    simp only [AddMonoidHom.comp_apply, kummerCoeffInclHom_toAddMonoidHom,
      toMul_unitsCoeffBaseChange, toMul_kummerCoeffIncl, toMul_kummerCoeffBaseChange]

/-- Transporting roots of unity preserves the coefficient pairing selected by a primitive root,
provided that root is transported along the field map as well. -/
theorem kummerCoeffBaseChange_kummerCoeffPairing {n : ℕ} [NeZero n]
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (x y : KummerCoeff K n) :
    kummerCoeffBaseChange n τ (kummerCoeffPairing (kummerCupPairing ζ hζ) x y) =
      kummerCoeffPairing
        (kummerCupPairing (algebraMap K L ζ) (hζ.map_of_injective (algebraMap K L).injective))
        (kummerCoeffBaseChange n τ x) (kummerCoeffBaseChange n τ y) := by
  let hζL := hζ.map_of_injective (algebraMap K L).injective
  let i := kummerLog hζ x
  have hx := coe_toMul_eq_pow_kummerLog hζ x
  have hxL : (((kummerCoeffBaseChange n τ x).toMul : (SeparableClosure L)ˣ) :
      SeparableClosure L) = algebraMap L (SeparableClosure L) (algebraMap K L ζ) ^ i := by
    simp [hx, i, ← IsScalarTower.algebraMap_apply]
  rw [kummerCoeffPairing_kummerCupPairing_of_eq_pow ζ hζ (i := (i : ℤ))
      (by simpa only [zpow_natCast] using hx), map_zsmul,
    kummerCoeffPairing_kummerCupPairing_of_eq_pow _ hζL (i := (i : ℤ))
      (by simpa only [zpow_natCast] using hxL)]

variable {n} [NeZero n] (ζ : K) (hζ : IsPrimitiveRoot ζ n)

/-- Kummer-cup Brauer classes commute with arbitrary field extension. -/
theorem brBaseChange_kummerBrauerClass (a b : Kˣ) :
    brBaseChange K L (kummerBrauerClass ζ hζ a b) =
      kummerBrauerClass (algebraMap K L ζ)
        (hζ.map_of_injective (algebraMap K L).injective)
        (Units.map (algebraMap K L : K →* L) a) (Units.map (algebraMap K L : K →* L) b) := by
  let τ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  simp only [kummerBrauerClass_def, kummerClass_eq_muNRepH1Equiv_kummerMap,
    cup_muNRepH1Equiv]
  rw [brBaseChange_h2MuToBr_muNRepH2Equiv n τ]
  rw [explicitMap2_explicitCup11
    (G := AbsoluteGaloisGroup K) (M := KummerCoeff K n) (N := KummerCoeff K n)
    (P := KummerCoeff K n) (H := AbsoluteGaloisGroup L) (M' := KummerCoeff L n)
    (N' := KummerCoeff L n) (P' := KummerCoeff L n) (φ := absoluteGaloisGroupMap τ)
    (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
    (hcP := continuous_of_discreteTopology) (hfM := kummerCoeffBaseChange_smul n τ)
    (hfN := kummerCoeffBaseChange_smul n τ) (hfP := kummerCoeffBaseChange_smul n τ)
    (hpair := kummerCoeffBaseChange_kummerCoeffPairing τ ζ hζ),
    explicitMap1_kummerMap n τ, explicitMap1_kummerMap n τ]

end TauCeti.ClassFieldTheory
