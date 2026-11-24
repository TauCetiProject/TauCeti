/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Modular.SplittingSystem

/-!
# Checks for the splitting modular system of a cyclotomic field

* `e = 1`: `F = ℚ`, and at every place over `p` the residue field is `𝔽_p`.
* `e = 3`, `p = 3`: `e' = 1`, and at every place over `3` the residue field has `3` elements.
* `e = 3`, `p = 2`: the residue field contains a primitive cube root of unity, the reduction of
  `complexRoot 3`, so it has at least `4` elements; `𝔽₂` contains no root of `X² + X + 1`.
-/

namespace TauCeti.Examples.SplittingSystem

open IsDedekindDomain NumberField IsLocalRing TauCeti.Cyclotomic

example : complexField 1 = ⊥ := by
  rw [complexField, IntermediateField.adjoin_simple_eq_bot_iff, complexRoot_def, Nat.cast_one,
    div_one, Complex.exp_two_pi_mul_I]
  exact one_mem _

example (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 (complexField 1)))
    (hv : (p : 𝓞 (complexField 1)) ∈ v.asIdeal) :
    Nat.card (ResidueField (v.adicCompletionIntegers (complexField 1))) = p :=
  natCard_residueField_of_ordCompl_eq_one v p hv (by simp)

example (v : HeightOneSpectrum (𝓞 (complexField 3)))
    (hv : (3 : 𝓞 (complexField 3)) ∈ v.asIdeal) :
    Nat.card (ResidueField (v.adicCompletionIntegers (complexField 3))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact natCard_residueField_of_ordCompl_eq_one v 3 (mod_cast hv)
    (by simp [Nat.Prime.factorization_self Nat.prime_three])

example (v : HeightOneSpectrum (𝓞 (complexField 3)))
    (hv : (2 : 𝓞 (complexField 3)) ∈ v.asIdeal) :
    4 ≤ Nat.card (ResidueField (v.adicCompletionIntegers (complexField 3))) := by
  set O := v.adicCompletionIntegers (complexField 3)
  have := v.charP_residueField_adicCompletionIntegers (K := complexField 3) 2 (mod_cast hv)
  have h3 : IsUnit ((3 : ℕ) : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    exact fun h ↦ by simpa using (CharP.cast_eq_zero_iff (ResidueField O) 2 3).1 h
  have hr := (isPrimitiveRoot_algebraMap_zetaInteger v).map_residue h3
  have hcard := hr.card_rootsOfUnity
  have hle : Nat.card (rootsOfUnity 3 (ResidueField O)) ≤ Nat.card (ResidueField O)ˣ :=
    Subgroup.card_le_card_group _
  rw [Nat.card_units] at hle
  omega

end TauCeti.Examples.SplittingSystem
