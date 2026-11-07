/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Transform
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import TauCeti.LinearAlgebra.Matrix.RationalVector

/-!
# Congruence invariance of powers of Siegel functions

For a row vector `r = a / N` with integral numerator, the power
`g_r ^ (12 * N / gcd(6, N))` is invariant under the principal congruence subgroup
`Γ(N)`. More generally, twelfth powers transform by the right matrix action on
`r`, and `g_r ^ (12 * k)` is unchanged by integral translations of `r` whenever
both coordinates of `6 * k * r` are integers.

These statements remove the root-of-unity ambiguity from the transformation law.
They provide the invariance needed to regard the indicated powers as modular
functions; they do not assert cusp meromorphy or a Fourier coefficient field.
The parameter is allowed to be integral, in which case the Siegel function vanishes.
For modular units one additionally excludes integral parameters.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.ModularForm

/-- Twelfth multiples of the Siegel function transform without a multiplier:
`g_r(γτ)^(12k) = g_(rγ)(τ)^(12k)`, with a right action on row vectors. -/
theorem siegelFunction_pow_twelve_mul_smul (r : Fin 2 → ℝ) (k : ℕ)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    siegelFunction r ↑(γ • τ) ^ (12 * k) =
      siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ ^
        (12 * k) := by
  obtain ⟨ε, hε, hγ⟩ := exists_siegelFunction_smul_eq_mul γ
  rw [hγ, mul_pow, pow_mul ε, hε, one_pow, one_mul]

/-- Integral translation does not change `g_r^(12k)` when the coordinates of
`6kr` are integral. This includes parameters that are themselves integral. -/
theorem siegelFunction_add_intCast_pow_twelve_mul (r : Fin 2 → ℝ) (s : Fin 2 → ℤ)
    (k : ℕ) (hr : ∀ i, ∃ a : ℤ, (6 * k : ℝ) * r i = a) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (r + fun i ↦ (s i : ℝ)) τ ^ (12 * k) =
      siegelFunction r τ ^ (12 * k) := by
  obtain ⟨a, ha⟩ := hr 0
  obtain ⟨b, hb⟩ := hr 1
  have ha' : (6 * k : ℂ) * (r 0 : ℂ) = a := by exact_mod_cast ha
  have hb' : (6 * k : ℂ) * (r 1 : ℂ) = b := by exact_mod_cast hb
  have hexp : cexp (-(π * I * (s 0 * r 1 - s 1 * r 0))) ^ (12 * k) = 1 := by
    rw [← Complex.exp_nat_mul]
    have heq : ((12 * k : ℕ) : ℂ) * (-(π * I * (s 0 * r 1 - s 1 * r 0))) =
        ((s 1 * a - s 0 * b : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      linear_combination 2 * π * I * ((s 1 : ℂ) * ha' - (s 0 : ℂ) * hb')
    rw [heq, Complex.exp_int_mul, exp_two_pi_mul_I, _root_.one_zpow]
  have hsign (z : ℤ) : ((-1 : ℂ) ^ z) ^ (12 * k) = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
    exact Even.neg_one_zpow ⟨z * (6 * k), by push_cast; ring⟩
  rw [siegelFunction_add_intCast r s hτ, mul_pow, mul_pow, hsign, hexp, one_mul, one_mul]

/-- For an integral numerator `a`, the power `g_(a/N)^(12k)` is invariant under
`Γ(N)` as soon as `N` divides `6k`. -/
theorem siegelFunction_div_pow_twelve_mul_smul {N : ℕ}
    (a : Fin 2 → ℤ) (k : ℕ) (hk : N ∣ 6 * k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * k) =
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k) := by
  rw [siegelFunction_pow_twelve_mul_smul]
  have hmap : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod N)) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_one,
      RingHom.mapMatrix_apply] using congrArg Subtype.val (CongruenceSubgroup.Gamma_mem'.mp hγ)
  obtain ⟨s, hs⟩ := (γ : Matrix (Fin 2) (Fin 2) ℤ).exists_vecMul_div_eq_add_intCast
    (K := ℝ) hmap a
  rw [hs]
  refine siegelFunction_add_intCast_pow_twelve_mul _ s k ?_ τ.im_pos
  intro i
  by_cases hN : N = 0
  · exact ⟨0, by simp [hN]⟩
  obtain ⟨m, hm⟩ := hk
  refine ⟨(m : ℤ) * a i, ?_⟩
  have hm' : (6 * k : ℝ) = N * m := by exact_mod_cast hm
  rw [hm']
  push_cast
  field_simp

/-- The standard exponent `12N / gcd(6,N)` kills both multipliers for a
level-`N` Siegel function. This is invariance under `Γ(N)`, not a claim about
its Fourier coefficients or its behavior at cusps. -/
theorem siegelFunction_div_pow_smul_of_mem_Gamma {N : ℕ}
    (a : Fin 2 → ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N / Nat.gcd 6 N) =
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N) := by
  have hg : Nat.gcd 6 N ∣ N := Nat.gcd_dvd_right 6 N
  have hexponent : 12 * N / Nat.gcd 6 N = 12 * (N / Nat.gcd 6 N) :=
    Nat.mul_div_assoc 12 hg
  rw [hexponent]
  refine siegelFunction_div_pow_twelve_mul_smul a _ ?_ hγ τ
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left 6 N
  refine ⟨m, ?_⟩
  calc
    6 * (N / Nat.gcd 6 N) = (Nat.gcd 6 N * m) * (N / Nat.gcd 6 N) :=
      congrArg (· * (N / Nat.gcd 6 N)) hm
    _ = (Nat.gcd 6 N * (N / Nat.gcd 6 N)) * m := by ring
    _ = N * m := by rw [Nat.mul_div_cancel' hg]

end TauCeti.ModularForm
