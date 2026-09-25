/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.QuadraticCharacter
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The conductor of a quadratic field

Within `ℚ(ζ_|D|)`, a quadratic field of fundamental discriminant `D` cannot lie in a
cyclotomic subfield at a proper divisor level of `|D|`. This gives the divisor-level
minimality step for explicit Kronecker–Weber constructions of multiquadratic fields.
For the classical argument see D. A. Cox,
*Primes of the Form x² + ny²*, §3.B.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- If a cyclotomic subfield of `ℚ(ζ_|D|)` at level `m ∣ |D|` contains `ℚ(√D)`, then
`|D| ∣ m`; hence `m = |D|`. -/
theorem natAbs_dvd_of_adjoin_sqrt_le_cyclotomic (D : ℤ)
    (hD : IsFundamentalDiscriminant D) {m : ℕ} (hm : m ∣ D.natAbs)
    (F : IntermediateField ℚ (CyclotomicField D.natAbs ℚ))
    [IsCyclotomicExtension {m} ℚ F]
    {x : CyclotomicField D.natAbs ℚ} (hx : x ^ 2 = (D : CyclotomicField D.natAbs ℚ))
    (hfield : ℚ⟮x⟯ ≤ F) : D.natAbs ∣ m := by
  let _ : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
  let _ : NeZero (Monoid.exponent (ZMod D.natAbs)ˣ : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite (G := (ZMod D.natAbs)ˣ)⟩
  let _ : NeZero m := ⟨fun h => hD.ne_zero (Int.natAbs_eq_zero.mp
    (Nat.eq_zero_of_zero_dvd (h ▸ hm)))⟩
  let _ : IsGalois ℚ F := IsCyclotomicExtension.isGalois {m} ℚ F
  let _ : IsCyclotomicExtension {D.natAbs} ℚ (CyclotomicField D.natAbs ℚ) :=
    CyclotomicField.isCyclotomicExtension D.natAbs ℚ
  let _ : IsAbelianGalois ℚ (CyclotomicField D.natAbs ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {D.natAbs} ℚ _
  have hχ0 : (fundamentalDiscriminantChar D hD).ringHomComp (Int.castRingHom ℂ) ∈
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar D.natAbs
        (CyclotomicField D.natAbs ℚ) ℂ
        (ℚ⟮fundamentalDiscriminantGaussSum D hD⟯) := by
    rw [IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff]
    intro σ hσ
    have hker : σ ∈ fundamentalDiscriminantCharacterSubgroup D hD := by
      have hfix : σ ∈
          (fixedField (fundamentalDiscriminantCharacterSubgroup D hD)).fixingSubgroup := by
        rw [fixedField_fundamentalDiscriminantCharacterSubgroup]
        exact hσ
      simpa only [IntermediateField.fixingSubgroup_fixedField] using hfix
    have hval := (mem_fundamentalDiscriminantCharacterSubgroup_iff D hD σ).mp hker
    have hζ := IsCyclotomicExtension.zeta_spec D.natAbs ℚ (CyclotomicField D.natAbs ℚ)
    have hζ_eq : hζ.autToPow ℚ σ =
        IsCyclotomicExtension.Rat.galEquivZMod D.natAbs (CyclotomicField D.natAbs ℚ) σ := by
      simpa only [ZMod.unitsMap_self, MonoidHom.id_apply] using
        hζ.autToPow_eq_unitsMap_galEquivZMod (dvd_refl D.natAbs) σ
    rw [← hζ_eq]
    simpa only [MulChar.ringHomComp_apply, map_one] using
      congrArg (Int.castRingHom ℂ) hval
  have hbase : ℚ⟮fundamentalDiscriminantGaussSum D hD⟯ ≤ F := by
    rw [← fixedField_fundamentalDiscriminantCharacterSubgroup]
    exact (fixedField_fundamentalDiscriminantCharacterSubgroup_eq_adjoin_of_sq_eq D hD hx).trans_le
      hfield
  have hχ : (fundamentalDiscriminantChar D hD).ringHomComp (Int.castRingHom ℂ) ∈
      IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar D.natAbs
        (CyclotomicField D.natAbs ℚ) ℂ F :=
    (IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar D.natAbs
      (CyclotomicField D.natAbs ℚ) ℂ).monotone
      hbase hχ0
  have hcond :=
    (IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd
      D.natAbs (CyclotomicField D.natAbs ℚ) ℂ F hm
      ((fundamentalDiscriminantChar D hD).ringHomComp (Int.castRingHom ℂ))).mp hχ
  rw [DirichletCharacter.conductor_ringHomComp _ (Int.castRingHom ℂ)
    (Int.cast_injective), isPrimitive_fundamentalDiscriminantChar hD] at hcond
  exact hcond

end TauCeti.Multiquadratic
