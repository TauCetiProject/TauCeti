/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.RingTheory.Polynomial.Cyclotomic.Derivative
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Real associates of cyclotomic derivative values

When the order is divisible by four, the value of the derivative of a cyclotomic polynomial
at a primitive root of unity can be made real by multiplication by a power of that root.
This lets one replace a cyclotomic generator of a relative different by a real associate,
without changing its absolute value at any infinite place.

See also `New.Parameters.exists_unit_mul_relDifferentGen_real` in `grh-lean`
(commit `72fead1`, `grh/src/New/Derivatives/Field/PrimeDecomposition.lean`).
-/

public section

open NumberField NumberField.IsCMField Polynomial

namespace IsPrimitiveRoot

/-- At a primitive `n`-th root in a CM field, if `4 ∣ n`, the value of `Φₙ′` has an
associate fixed by complex conjugation, obtained by multiplication by an integral root of
unity. -/
theorem exists_unit_mul_cyclotomic_derivative_real {K : Type*} [Field K] [CharZero K]
    [IsCMField K] [Algebra.IsIntegral ℚ K] {n : ℕ} {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ζ n) (h4 : 4 ∣ n) :
    ∃ c : (𝓞 K)ˣ, c ^ n = 1 ∧
      complexConj K ((c : K) * aeval (ζ : K) (cyclotomic n ℤ).derivative) =
        (c : K) * aeval (ζ : K) (cyclotomic n ℤ).derivative := by
  by_cases hn0 : n = 0
  · subst n
    exact ⟨1, by simp, by simp⟩
  have hn := Nat.pos_of_ne_zero hn0
  have hn2 : 2 < n := by omega
  let u := (hζ.isUnit hn0).unit
  have hu : (u : 𝓞 K) = ζ := (hζ.isUnit hn0).unit_spec
  have hun : u ^ n = 1 := by
    apply Units.ext
    simpa [hu] using hζ.pow_eq_one
  have hζK : IsPrimitiveRoot (ζ : K) n := hζ.map_of_injective RingOfIntegers.coe_injective
  have hζ0 := hζK.ne_zero hn.ne'
  have hconj : complexConj K (ζ : K) = (ζ : K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact mul_complexConj_eq_one_of_pow_eq hn0 hζK.pow_eq_one (by simp)
  obtain ⟨m, hm⟩ := Nat.totient_even hn2
  let k := m - 1
  have hdeg : n.totient - 2 = k + k := by omega
  have hrecip := eval_derivative_cyclotomic_inv_mul_pow (ζ := Units.mk0 (ζ : K) hζ0) hζK hn2
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, hdeg, pow_add] at hrecip
  -- The factor `ζ⁻ᵏ` compensates for the reciprocal power; the fourth root removes the sign.
  let i : K := (ζ : K) ^ (n / 4)
  have hi : i ^ 2 = -1 := (hζK.pow hn (by omega : n = n / 4 * 4)).sq_eq_neg_one
  refine ⟨u ^ (n / 4) * u⁻¹ ^ k, ?_, ?_⟩
  · rw [mul_pow, pow_right_comm u, pow_right_comm u⁻¹, inv_pow, hun]
    simp
  have hiConj : complexConj K i = -i := by
    rw [map_pow, hconj, inv_pow]
    exact (eq_inv_of_mul_eq_one_left (by linear_combination -hi)).symm
  have heval (z : K) : aeval z (cyclotomic n ℤ).derivative =
      (cyclotomic n K).derivative.eval z := by
    rw [← eval_map_algebraMap, ← derivative_map, map_cyclotomic]
  have hpConj : complexConj K (aeval (ζ : K) (cyclotomic n ℤ).derivative) =
      (cyclotomic n K).derivative.eval (ζ : K)⁻¹ := by
    rw [← heval, ← hconj]
    exact (aeval_algHom_apply ((complexConj K).restrictScalars ℤ) _ _).symm
  have hv : ((u ^ (n / 4) * u⁻¹ ^ k : (𝓞 K)ˣ) : K) = i * ((ζ : K)⁻¹ ^ k) := by
    simp [i, hu]
  rw [hv, map_mul, map_mul, hiConj, map_pow, map_inv₀, hconj, inv_inv, hpConj, heval]
  apply mul_right_cancel₀ (pow_ne_zero k hζ0)
  rw [inv_pow]
  field_simp
  simp only [one_div]
  linear_combination -i * hrecip

end IsPrimitiveRoot
