/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Rational
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Henselian.Teichmuller.Character

/-!
# Checks for Teichmüller lifts of residual characters

For a prime `p`, let `χ_p : G_ℚ → ℤ_pˣ` be the `p`-adic cyclotomic character and
`ω = [χ_p mod p]` the Teichmüller lift of its reduction modulo `p`. Then `ω` reduces to
`χ_p mod p`, has order exactly `p - 1` (the mod `p` cyclotomic character of `G_ℚ` is surjective),
takes values in the `(p - 1)`-st roots of unity, and `χ_p = ω · ⟨χ_p⟩` with `⟨χ_p⟩` valued in the
principal units `1 + pℤ_p`. The lift of the trivial character is trivial.
-/

public section

namespace TauCeti.Examples.TeichmullerCharacter

open IsLocalRing

variable (p : ℕ) [Fact p.Prime]

/-- The reduction of the `p`-adic cyclotomic character of `G_ℚ` modulo `p`. -/
noncomputable abbrev modPCyclotomic : Field.absoluteGaloisGroup ℚ →* (ResidueField ℤ_[p])ˣ :=
  (Units.map (residue ℤ_[p] : ℤ_[p] →* ResidueField ℤ_[p])).comp (localCyclotomicCharacter p ℚ)

-- `ω = [χ_p mod p]` has order `p - 1`.
example : orderOf (teichmullerCharacter ℤ_[p] (modPCyclotomic p)) = p - 1 := by
  rw [orderOf_teichmullerCharacter_of_surjective, PadicInt.card_residueField]
  exact (surjective_units_map_of_local_ringHom _ (residue_surjective (R := ℤ_[p]))
    inferInstance).comp (surjective_localCyclotomicCharacter_rat p)

-- `ω` reduces to `χ_p mod p`.
example :
    (Units.map (residue ℤ_[p] : ℤ_[p] →* ResidueField ℤ_[p])).comp
      (teichmullerCharacter ℤ_[p] (modPCyclotomic p)) = modPCyclotomic p :=
  unitsMap_residue_comp_teichmullerCharacter _

-- `ω` takes values in the `(p - 1)`-st roots of unity.
example (σ : Field.absoluteGaloisGroup ℚ) :
    teichmullerCharacter ℤ_[p] (modPCyclotomic p) σ ^ (p - 1) = 1 := by
  simpa only [PadicInt.card_residueField] using
    teichmullerCharacter_apply_pow_card_sub_one (R := ℤ_[p]) (modPCyclotomic p) σ

-- `χ_p = ω · ⟨χ_p⟩`.
example :
    teichmullerCharacter ℤ_[p] (modPCyclotomic p) *
      principalUnitCharacter ℤ_[p] (localCyclotomicCharacter p ℚ) =
        localCyclotomicCharacter p ℚ :=
  teichmullerCharacter_mul_principalUnitCharacter _

-- `⟨χ_p⟩` takes values in the principal units `1 + pℤ_p`.
example (σ : Field.absoluteGaloisGroup ℚ) :
    residue ℤ_[p] (principalUnitCharacter ℤ_[p] (localCyclotomicCharacter p ℚ) σ : ℤ_[p]) = 1 :=
  residue_principalUnitCharacter_apply _ σ

-- `[1] = 1`.
example : teichmullerCharacter ℤ_[p] (1 : Field.absoluteGaloisGroup ℚ →* (ResidueField ℤ_[p])ˣ) =
    1 :=
  teichmullerCharacter_one _

end TauCeti.Examples.TeichmullerCharacter
