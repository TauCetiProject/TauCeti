/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.Completion

/-!
# Checks for the completions of `ℚ(ζ₃)` at the places over `7`

Since `7 ≡ 1 mod 3`, the polynomial `X² + X + 1` has the two roots `2` and `4` in `𝔽₇`, and
`F = ℚ(ζ₃) = complexField 3` has two places over `7`: the kernels of the ring homomorphisms
`𝓞 F → 𝔽₇` sending `complexRoot 3` to `2` and to `4`. These checks show:

* at every place `v` over `7` the reduction of `complexRoot 3` is `2` or `4`, and the residue
  field of `F_v` has `7` elements;
* there are two distinct places over `7`, at which `complexRoot 3` reduces to `2` and to `4`
  respectively, so a statement at one chosen place does not cover the other.
-/

public section

open IsDedekindDomain NumberField IsLocalRing HeightOneSpectrum TauCeti.Cyclotomic Polynomial

namespace TauCeti.Examples.CyclotomicCompletionSeven

local notation "F" => complexField 3
local notation "ζ" => complexField.zetaInteger 3

/-- The ring homomorphism `𝓞 F → 𝔽₇` sending `complexRoot 3` to a root `a` of `X² + X + 1`. -/
noncomputable def toZModSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) : 𝓞 F →+* ZMod 7 :=
  ((complexField.isPrimitiveRoot_zeta 3).integralPowerBasis.lift a <| by
    rw [IsPrimitiveRoot.integralPowerBasis_gen, ← NumberField.RingOfIntegers.minpoly_coe,
      IsPrimitiveRoot.coe_toInteger, ← cyclotomic_eq_minpoly (complexField.isPrimitiveRoot_zeta 3)
        (by norm_num), cyclotomic_three]
    simpa [add_assoc] using ha).toRingHom

/-- `toZModSeven a ha` sends `complexRoot 3` to `a`. -/
theorem toZModSeven_zeta (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) : toZModSeven a ha ζ = a := by
  rw [toZModSeven, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    complexField.zetaInteger_eq_toInteger, ← IsPrimitiveRoot.integralPowerBasis_gen,
    PowerBasis.lift_gen]

/-- The place of `F` cut out by `toZModSeven a ha`. -/
noncomputable def placeSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) : HeightOneSpectrum (𝓞 F) where
  asIdeal := RingHom.ker (toZModSeven a ha)
  isPrime := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact RingHom.ker_isPrime _
  ne_bot := fun h ↦ by
    have h7 : ((7 : ℕ) : 𝓞 F) ∈ RingHom.ker (toZModSeven a ha) := by
      rw [RingHom.mem_ker, map_natCast]; rfl
    rw [h, Ideal.mem_bot] at h7
    exact absurd h7 (by exact_mod_cast (show (7 : ℕ) ≠ 0 by norm_num))

/-- The place `placeSeven a ha` lies over `7`. -/
theorem seven_mem_placeSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) :
    ((7 : ℕ) : 𝓞 F) ∈ (placeSeven a ha).asIdeal := by
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker, map_natCast]; rfl

/-- At a place `v` of `F`, the reduction of `complexRoot 3` is the image of `n : ℕ` exactly when
`complexRoot 3 - n` lies in `v`. -/
theorem residue_zeta_eq_natCast_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) = n ↔
      ζ - n ∈ v.asIdeal := by
  rw [← v.under_maximalIdeal_adicCompletionIntegers (K := F), Ideal.mem_comap, map_sub,
    map_natCast, ← residue_eq_zero_iff, map_sub, map_natCast, sub_eq_zero]

/-- At each place over `7` the reduction of `complexRoot 3` is `2` or `4`. -/
theorem residue_zeta_eq_two_or_four (v : HeightOneSpectrum (𝓞 F))
    (hv : ((7 : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) = 2 ∨
      residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) =
        4 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hchar := v.charP_residueField_adicCompletionIntegers (K := F) 7 hv
  set ρ := residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ)
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    have := (complexField.isPrimitiveRoot_zetaInteger 3).geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using this
  have hρ : ρ ^ 2 + ρ + 1 = 0 := by
    simpa [ρ] using congrArg (fun x ↦ residue (v.adicCompletionIntegers F)
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F) x)) hζ
  have h7 : (7 : ResidueField (v.adicCompletionIntegers F)) = 0 := by
    exact_mod_cast CharP.cast_eq_zero _ 7
  have : (ρ - 2) * (ρ - 4) = 0 := by
    linear_combination hρ - (ρ - 1) * h7
  rcases mul_eq_zero.1 this with h | h
  · exact .inl (sub_eq_zero.1 h)
  · exact .inr (sub_eq_zero.1 h)

/-- At each place over `7` the residue field is `𝔽₇`. -/
example (v : HeightOneSpectrum (𝓞 F)) (hv : ((7 : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have := v.charP_residueField_adicCompletionIntegers (K := F) 7 hv
  let χ := ZMod.castHom (dvd_refl 7) (ResidueField (v.adicCompletionIntegers F))
  have hχ : Function.Bijective χ := by
    refine ⟨χ.injective, RingHom.range_eq_top.1 (eq_top_iff.2 ?_)⟩
    rw [← closure_residue_zetaInteger_eq_top v, Subring.closure_le, Set.singleton_subset_iff]
    rcases residue_zeta_eq_two_or_four v hv with h | h
    · exact ⟨2, by rw [h, map_ofNat]⟩
    · exact ⟨4, by rw [h, map_ofNat]⟩
  rw [← Nat.card_eq_of_bijective χ hχ, Nat.card_zmod]

/-- There are two places over `7`, at which `complexRoot 3` reduces to `2` and to `4`. -/
example : ∃ v w : HeightOneSpectrum (𝓞 F), v ≠ w ∧
    ((7 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ((7 : ℕ) : 𝓞 F) ∈ w.asIdeal ∧
    residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) = 2 ∧
    residue (w.adicCompletionIntegers F) (algebraMap (𝓞 F) (w.adicCompletionIntegers F) ζ) =
      4 := by
  have h2 : (2 : ZMod 7) ^ 2 + 2 + 1 = 0 := by decide
  have h4 : (4 : ZMod 7) ^ 2 + 4 + 1 = 0 := by decide
  have hmem (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) (n : ℕ) (hn : (n : ZMod 7) = a) :
      ζ - n ∈ (placeSeven a ha).asIdeal := by
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker, map_sub, toZModSeven_zeta, map_natCast, hn, sub_self]
  have hv := hmem 2 h2 2 rfl
  have hw := hmem 4 h4 4 rfl
  refine ⟨placeSeven 2 h2, placeSeven 4 h4, fun h ↦ ?_, seven_mem_placeSeven 2 h2,
    seven_mem_placeSeven 4 h4, (residue_zeta_eq_natCast_iff _ 2).2 hv,
    (residue_zeta_eq_natCast_iff _ 4).2 hw⟩
  rw [h] at hv
  have h1 : (1 : 𝓞 F) ∈ (placeSeven 4 h4).asIdeal := by
    have := (placeSeven 4 h4).asIdeal.sub_mem hv hw
    have h7 := seven_mem_placeSeven 4 h4
    have h3 := (placeSeven 4 h4).asIdeal.mul_mem_left 3 this
    have := (placeSeven 4 h4).asIdeal.sub_mem h7 h3
    convert this using 1
    push_cast
    ring
  exact (placeSeven 4 h4).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

end TauCeti.Examples.CyclotomicCompletionSeven
