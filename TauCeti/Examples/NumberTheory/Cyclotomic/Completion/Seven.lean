/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
public import TauCeti.NumberTheory.Cyclotomic.Completion
public import TauCeti.NumberTheory.Padics.AdicCompletion

/-!
# Checks for the completions of `ℚ(ζ₃)` at the places over `7`

Since `7 ≡ 1 mod 3`, the polynomial `X² + X + 1` has the two roots `2` and `4` in `𝔽₇`, and
`F = ℚ(ζ₃) = complexField 3` has two places over `7`: the kernels of the ring homomorphisms
`𝓞 F → 𝔽₇` sending `complexRoot 3` to `2` and to `4`. These checks show:

* at every place `v` over `7` the reduction of `complexRoot 3` is `2` or `4`, and the residue
  field of `F_v` has `7` elements;
* there are two distinct places over `7`, at which `complexRoot 3` reduces to `2` and to `4`
  respectively, so a statement at one chosen place does not cover the other;
* at every place `v` over `7` the local degree `[F_v : ℚ₇]` is `1`, the completion map from `ℚ₇`
  to `F_v` is bijective, and `F_v ≅ ℚ₇` as topological `ℚ`-algebras.
-/

public section

open IsDedekindDomain NumberField IsLocalRing HeightOneSpectrum TauCeti.Cyclotomic Polynomial
open Rat.HeightOneSpectrum (primesEquiv liesOver_asIdeal_primesEquiv_symm_iff)
open scoped AdicCompletionExtension

namespace TauCeti.Examples.CyclotomicCompletionSeven

local notation "F" => complexField 3
local notation "ζ" => complexField.zetaInteger 3

/-- Seven is prime, so `ZMod 7` is the field `𝔽₇`. -/
local instance instFactPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The ring homomorphism `𝓞 F → 𝔽₇` sending `complexRoot 3` to a root `a` of `X² + X + 1`. -/
private noncomputable def toZModSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) : 𝓞 F →+* ZMod 7 :=
  ((complexField.isPrimitiveRoot_zeta 3).integralPowerBasis.lift a <| by
    rw [IsPrimitiveRoot.integralPowerBasis_gen, ← NumberField.RingOfIntegers.minpoly_coe,
      IsPrimitiveRoot.coe_toInteger, ← cyclotomic_eq_minpoly (complexField.isPrimitiveRoot_zeta 3)
        (by norm_num), cyclotomic_three]
    simpa [add_assoc] using ha).toRingHom

/-- `toZModSeven a ha` sends `complexRoot 3` to `a`. -/
private theorem toZModSeven_zetaInteger (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) :
    toZModSeven a ha ζ = a := by
  rw [toZModSeven, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    complexField.zetaInteger_eq_toInteger, ← IsPrimitiveRoot.integralPowerBasis_gen,
    PowerBasis.lift_gen]

/-- `toZModSeven a ha` sends `7` to `0`. -/
private theorem toZModSeven_natCast_seven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) :
    toZModSeven a ha ((7 : ℕ) : 𝓞 F) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

/-- The place of `F` cut out by `toZModSeven a ha`. -/
private noncomputable def placeSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) :
    HeightOneSpectrum (𝓞 F) where
  asIdeal := RingHom.ker (toZModSeven a ha)
  isPrime := RingHom.ker_isPrime _
  ne_bot := fun h ↦ by
    have h7 := RingHom.mem_ker.2 (toZModSeven_natCast_seven a ha)
    rw [h, Ideal.mem_bot] at h7
    exact absurd h7 (by exact_mod_cast (show (7 : ℕ) ≠ 0 by norm_num))

/-- Membership in `placeSeven a ha` is vanishing under `toZModSeven a ha`. -/
private theorem mem_placeSeven_iff (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) {x : 𝓞 F} :
    x ∈ (placeSeven a ha).asIdeal ↔ toZModSeven a ha x = 0 :=
  RingHom.mem_ker

/-- The place `placeSeven a ha` lies over `7`. -/
private theorem seven_mem_placeSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0) :
    ((7 : ℕ) : 𝓞 F) ∈ (placeSeven a ha).asIdeal :=
  (mem_placeSeven_iff a ha).2 (toZModSeven_natCast_seven a ha)

/-- If `n : ℕ` reduces to `a` in `𝔽₇`, then `complexRoot 3 - n` lies in `placeSeven a ha`. -/
private theorem zetaInteger_sub_natCast_mem_placeSeven (a : ZMod 7) (ha : a ^ 2 + a + 1 = 0)
    (n : ℕ) (hn : (n : ZMod 7) = a) : ζ - n ∈ (placeSeven a ha).asIdeal := by
  rw [mem_placeSeven_iff, map_sub, toZModSeven_zetaInteger, map_natCast, hn, sub_self]

/-- At a place `v` of `F`, the reduction of `complexRoot 3` is the image of `n : ℕ` exactly when
`complexRoot 3 - n` lies in `v`. -/
private theorem residue_zetaInteger_eq_natCast_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) = n ↔
      ζ - n ∈ v.asIdeal := by
  rw [← v.residue_algebraMap_adicCompletionIntegers_eq_iff (K := F), map_natCast, map_natCast]

/-- At each place over `7` the reduction of `complexRoot 3` is `2` or `4`. -/
private theorem residue_zetaInteger_eq_two_or_four (v : HeightOneSpectrum (𝓞 F))
    (hv : ((7 : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) = 2 ∨
      residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) =
        4 := by
  have hchar := v.charP_residueField_adicCompletionIntegers (K := F) 7 hv
  set ρ := residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ)
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    rw [complexField.zetaInteger_eq_toInteger]
    exact IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
      (complexField.isPrimitiveRoot_zeta 3)
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
  have hpe : ordProj[7] 3 = 1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num), pow_zero]
  rcases residue_zetaInteger_eq_two_or_four v hv with h | h
  · exact natCard_residueField_of_residue_zetaInteger_pow_ordProj_eq_natCast v 7 hv (n := 2)
      (by rw [hpe, pow_one, h, Nat.cast_ofNat])
  · exact natCard_residueField_of_residue_zetaInteger_pow_ordProj_eq_natCast v 7 hv (n := 4)
      (by rw [hpe, pow_one, h, Nat.cast_ofNat])

/-- There are two places over `7`, at which `complexRoot 3` reduces to `2` and to `4`. -/
example : ∃ v w : HeightOneSpectrum (𝓞 F), v ≠ w ∧
    ((7 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ((7 : ℕ) : 𝓞 F) ∈ w.asIdeal ∧
    residue (v.adicCompletionIntegers F) (algebraMap (𝓞 F) (v.adicCompletionIntegers F) ζ) = 2 ∧
    residue (w.adicCompletionIntegers F) (algebraMap (𝓞 F) (w.adicCompletionIntegers F) ζ) =
      4 := by
  have h2 : (2 : ZMod 7) ^ 2 + 2 + 1 = 0 := by decide
  have h4 : (4 : ZMod 7) ^ 2 + 4 + 1 = 0 := by decide
  have hv := zetaInteger_sub_natCast_mem_placeSeven 2 h2 2 rfl
  have hw := zetaInteger_sub_natCast_mem_placeSeven 4 h4 4 rfl
  refine ⟨placeSeven 2 h2, placeSeven 4 h4, fun h ↦ ?_, seven_mem_placeSeven 2 h2,
    seven_mem_placeSeven 4 h4, (residue_zetaInteger_eq_natCast_iff _ 2).2 hv,
    (residue_zetaInteger_eq_natCast_iff _ 4).2 hw⟩
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

/-- At each place over `7` the local degree `[F_v : ℚ₇]` is `1`, since `7 ≡ 1 mod 3`. -/
example (v : HeightOneSpectrum (𝓞 F))
    [v.asIdeal.LiesOver ((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩).asIdeal] :
    Module.finrank (((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩).adicCompletion ℚ)
      (v.adicCompletion F) = 1 :=
  finrank_adicCompletion_eq_one v 7 (by decide)

/-- At each place over `7` the completion map from `ℚ₇` to `F_v` is bijective. -/
example (v : HeightOneSpectrum (𝓞 F))
    [v.asIdeal.LiesOver ((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩).asIdeal] :
    Function.Bijective (adicCompletionExtension ℚ F
      ((primesEquiv (R := ℤ)).symm ⟨7, Nat.prime_seven⟩) v) :=
  adicCompletionExtension_bijective v 7 (by decide)

/-- At each place over `7` the completion `F_v` is `ℚ₇`. -/
example (v : HeightOneSpectrum (𝓞 F)) (hv : ((7 : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nonempty (v.adicCompletion F ≃A[ℚ] ℚ_[7]) :=
  have := (liesOver_asIdeal_primesEquiv_symm_iff (R := ℤ) v.isPrime.ne_top ⟨7, Fact.out⟩).2 hv
  ⟨adicCompletionEquivPadic v 7 (finrank_adicCompletion_eq_one v 7 (by decide))⟩

end TauCeti.Examples.CyclotomicCompletionSeven
