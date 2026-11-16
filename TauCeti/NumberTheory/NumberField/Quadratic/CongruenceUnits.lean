/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits
import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# Unit congruences and residue-unit counts in quadratic fields

Let `K` be a quadratic number field (`finrank ℚ K = 2`) of discriminant `D = NumberField.discr K`.
This file supplies two arithmetic ingredients for ray class fields of quadratic fields:

1. **Global units congruent to one modulo `(N)` in imaginary quadratic fields.** Transporting
   `QuadraticAlgebra.ker_unitsMap_quotient_span_natCast` along a period-algebra presentation
   `𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-periodCoeffC D) (-periodCoeffB D)` shows that the kernel of
   `(𝓞 K)ˣ →* (𝓞 K ⧸ (N))ˣ` is `⊤` at `N = 1`, `Subgroup.zpowers (-1)` at `N = 2`, and `⊥` for
   `3 ≤ N` (`ker_unitsMap_ringOfIntegers_quotient_span_natCast`), uniformly for all imaginary
   quadratic discriminants including `-4` and `-3`.
2. **Explicit residue-unit counts at levels `2`, `3`, `6`, and `8`.** Specializing
   `card_units_quotient_span_natCast_of_prime` and `card_units_quotient_span_natCast_mul_prod`
   evaluates `#(𝓞 K ⧸ (N))ˣ` in closed form in terms of `χ_D(2)` and `χ_D(3)`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open Ideal Module NumberField
open scoped NumberField
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr)

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Kernel of `(𝓞 K)ˣ →* (𝓞 K ⧸ (N))ˣ` in an imaginary quadratic field**: for `N ≠ 0`, the
units of `𝓞 K` congruent to `1` modulo `(N)` form `⊤` at `N = 1`, `Subgroup.zpowers (-1)` at
`N = 2`, and `⊥` for `3 ≤ N`. -/
theorem ker_unitsMap_ringOfIntegers_quotient_span_natCast [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {N : ℕ} (hN : N ≠ 0) :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
        𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  obtain ⟨e⟩ := exists_ringOfIntegers_periodAlgEquiv hK
  have hd : QuadraticAlgebra.discr (-periodCoeffC (discr K)) (-periodCoeffB (discr K)) < 0 := by
    rw [discr_neg_periodCoeff (discr K) (isFundamentalDiscr_discr hK).emod_four_eq_zero_or_one]
    exact discr_lt_zero_of_isTotallyComplex hK
  have hker := QuadraticAlgebra.ker_unitsMap_quotient_span_natCast hd hN
  let A := QuadraticAlgebra ℤ (-periodCoeffC (discr K)) (-periodCoeffB (discr K))
  let eu : (𝓞 K)ˣ ≃* Aˣ := Units.mapEquiv e.toRingEquiv.toMulEquiv
  have hcomap :
      (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
          𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
        (Units.map (Ideal.Quotient.mk (Ideal.span {(N : A)}) :
          A →* A ⧸ Ideal.span {(N : A)})).ker.comap eu.toMonoidHom := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_one,
      ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun ⟨w, hw⟩ ↦ ?_⟩
    · refine ⟨e w, ?_⟩
      simpa [eu] using congrArg e hw
    · refine ⟨e.symm w, ?_⟩
      have := congrArg e.symm hw
      simpa [eu] using this
  rw [hcomap, hker]
  split_ifs with h1 h2
  · exact Subgroup.comap_top _
  · have heu : eu (-1) = -1 := Units.ext (by simp [eu])
    ext u
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ⟨k, eu.injective (by simpa [heu] using hk)⟩,
      fun ⟨k, hk⟩ ↦ ⟨k, by simpa [heu] using congrArg eu hk⟩⟩
  · exact MonoidHom.ker_eq_bot_iff _ |>.mpr eu.injective

/-- Explicit residue-unit count `#(𝓞 K ⧸ (2))ˣ = 2 - χ_D(2)` in a quadratic field. -/
theorem card_units_quotient_span_two (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(2 : 𝓞 K)})ˣ : ℤ) =
      2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 := by
  simpa using card_units_quotient_span_natCast_of_prime hK 2

/-- Explicit residue-unit count `#(𝓞 K ⧸ (3))ˣ = 2 * (3 - χ_D(3))` in a quadratic field. -/
theorem card_units_quotient_span_three (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(3 : 𝓞 K)})ˣ : ℤ) =
      2 * (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3) := by
  simpa using card_units_quotient_span_natCast_of_prime hK 3

/-- Explicit residue-unit count `#(𝓞 K ⧸ (6))ˣ = 2 * (2 - χ_D(2)) * (3 - χ_D(3))` in a quadratic
field. -/
theorem card_units_quotient_span_six (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(6 : 𝓞 K)})ˣ : ℤ) =
      2 * (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2) *
        (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3) := by
  have h := card_units_quotient_span_natCast_mul_prod hK (f := 6) (by decide)
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by decide) (by decide),
      Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [hpf, Finset.prod_pair (by decide), Finset.prod_pair (by decide)] at h
  push_cast at h
  linarith

/-- Explicit residue-unit count `#(𝓞 K ⧸ (8))ˣ = 16 * (2 - χ_D(2))` in a quadratic field. -/
theorem card_units_quotient_span_eight (hK : finrank ℚ K = 2) :
    (Nat.card (𝓞 K ⧸ span {(8 : 𝓞 K)})ˣ : ℤ) =
      16 * (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2) := by
  have h := card_units_quotient_span_natCast_mul_prod hK (f := 8) (by decide)
  have hpf : (8 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 3) (by decide) Nat.prime_two
  rw [hpf, Finset.prod_singleton, Finset.prod_singleton] at h
  push_cast at h
  linarith

end TauCeti.NumberField
