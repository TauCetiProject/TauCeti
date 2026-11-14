/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.KummerLaplace
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Asymptotics

/-!
# Recurrence and solution sequence for Legendre's incomplete Gamma continued fraction

For `z ∈ Complex.slitPlane`, Legendre's continued fraction for the normalized upper incomplete
Gamma combination `z^{-a} e^z Γ(a, z) = K(0, a - 1; z)` has head `0`, partial denominators
`b_n = 1`, and partial numerators `a₁ = z⁻¹`, `a_{2k} = (k - a) z⁻¹`, `a_{2k+1} = k z⁻¹`
(`k ≥ 1`; non-terminating when `a ∉ {1, 2, ...}`). In terms of the rotated Kummer-Laplace
integrals `Complex.kummerLaplace`, the sequence `(f_n)_{n ≥ 0}` defined by
* `f₀ = 1`,
* `f_{2k+1} = -(1 - a)_k z^{-k} K(k, a - 1 - k; z)`,
* `f_{2k+2} = (1 - a)_{k+1} z^{-(k+1)} K(k, a - 2 - k; z)`

satisfies the associated three-term recurrence `f_{n+2} = f_{n+1} + a_{n+1} f_n` on
`Complex.slitPlane` with initial values `f₀ = 1` and `f₁ = -K(0, a - 1; z)`. In Gautschi's
analysis of three-term recurrence relations, this sequence is constructed as the candidate minimal
solution used to apply Pincherle's theorem in the non-terminating regime `a ∉ {1, 2, ...}`; its
eventual nonvanishing follows from the saddle-point asymptotics in
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Asymptotics`.

## Main definitions

* `Complex.upperGammaContFracPartNum a z n` — the `n`-th partial numerator of Legendre's continued
  fraction for `z^{-a} e^z Γ(a, z)`.
* `Complex.upperGammaContFracSolution a z n` — the Kummer-Laplace solution sequence `f_n` of the
  associated three-term recurrence on `Complex.slitPlane`, normalized by `f₀ = 1`.

## Main results

* `Complex.upperGammaContFracPartNum_ne_zero_iff` — `upperGammaContFracPartNum a z n ≠ 0` iff
  `z ≠ 0` and `(Even n → a ≠ (n / 2 : ℕ))`.
* `Complex.upperGammaContFracSolution_zero`, `Complex.upperGammaContFracSolution_one` — initial
  values `f₀ = 1` and `f₁ = -kummerLaplace 0 (a - 1) z`.
* `Complex.upperGammaContFracSolution_add_two` — on `slitPlane`,
  `f (n + 2) = f (n + 1) + upperGammaContFracPartNum a z (n + 1) * f n`.
* `Complex.eventually_upperGammaContFracSolution_ne_zero` — for `z ∈ slitPlane` and `a ≠ m + 1`
  (`m : ℕ`), `upperGammaContFracSolution a z n ≠ 0` eventually as `n → ∞`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82.
-/

public section

noncomputable section

open Filter Polynomial

namespace Complex

/-- The `n`-th partial numerator of Legendre's continued fraction for `z^{-a} e^z Γ(a, z)`:
`a₁ = z⁻¹`, `a_{2k} = (k - a) * z⁻¹` (`k ≥ 1`), and `a_{2k+1} = k * z⁻¹` (`k ≥ 1`), paired with
partial denominators `b_n = 1` and head `b₀ = 0`. -/
def upperGammaContFracPartNum (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 1 then z⁻¹
  else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹
  else ((n / 2 : ℕ) : ℂ) * z⁻¹

/-- Defining formula for `Complex.upperGammaContFracPartNum`. -/
theorem upperGammaContFracPartNum_def (a z : ℂ) (n : ℕ) :
    upperGammaContFracPartNum a z n =
      if n = 1 then z⁻¹
      else if Even n then (((n / 2 : ℕ) : ℂ) - a) * z⁻¹
      else ((n / 2 : ℕ) : ℂ) * z⁻¹ := (rfl)

/-- Zeroth index evaluation `upperGammaContFracPartNum a z 0 = -a * z⁻¹`. -/
@[simp]
theorem upperGammaContFracPartNum_zero (a z : ℂ) :
    upperGammaContFracPartNum a z 0 = -a * z⁻¹ := by
  simp [upperGammaContFracPartNum]

/-- First partial numerator `a₁ = z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperGammaContFracPartNum_one (a z : ℂ) :
    upperGammaContFracPartNum a z 1 = z⁻¹ := by
  simp [upperGammaContFracPartNum]

/-- Even partial numerator `a_{2k+2} = (k + 1 - a) * z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperGammaContFracPartNum_two_mul_add_two (a z : ℂ) (k : ℕ) :
    upperGammaContFracPartNum a z (2 * k + 2) = ((k : ℂ) + 1 - a) * z⁻¹ := by
  have h1 : 2 * k + 2 ≠ 1 := by omega
  have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
  simp only [upperGammaContFracPartNum, h1, ↓reduceIte, hev, hdiv, Nat.cast_add, Nat.cast_one]

/-- Odd partial numerator `a_{2k+3} = (k + 1) * z⁻¹` of Legendre's continued fraction. -/
@[simp]
theorem upperGammaContFracPartNum_two_mul_add_three (a z : ℂ) (k : ℕ) :
    upperGammaContFracPartNum a z (2 * k + 3) = ((k : ℂ) + 1) * z⁻¹ := by
  have h1 : 2 * k + 3 ≠ 1 := by omega
  have hodd : ¬Even (2 * k + 3) := by simp [parity_simps]
  have hdiv : (2 * k + 3) / 2 = k + 1 := by omega
  simp only [upperGammaContFracPartNum, h1, ↓reduceIte, hodd, hdiv, Nat.cast_add, Nat.cast_one]

/-- Exact nonvanishing characterization of `upperGammaContFracPartNum a z n`: it is nonzero
if and only if `z ≠ 0` and, when `n` is even, `a ≠ (n / 2 : ℕ)`. -/
theorem upperGammaContFracPartNum_ne_zero_iff {a z : ℂ} {n : ℕ} :
    upperGammaContFracPartNum a z n ≠ 0 ↔ z ≠ 0 ∧ (Even n → a ≠ (n / 2 : ℕ)) := by
  rcases n with _ | _ | n
  · simp [and_comm]
  · simp
  · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
      have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
      rw [upperGammaContFracPartNum_two_mul_add_two, hdiv]
      simp [hev, sub_eq_zero, eq_comm (a := a), and_comm]
    · have hodd : ¬Even (2 * k + 3) := by simp [parity_simps]
      have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [show 2 * k + 1 + 2 = 2 * k + 3 by ring, upperGammaContFracPartNum_two_mul_add_three]
      simp [hodd, hk1]

/-- Explicit Kummer-Laplace solution sequence of the three-term recurrence
`f (n + 2) = f (n + 1) + upperGammaContFracPartNum a z (n + 1) * f n` on `Complex.slitPlane`
associated with Legendre's continued fraction for `z^{-a} e^z Γ(a, z)`, normalized by `f 0 = 1`:
* `f 0 = 1`,
* `f (2k + 1) = -(1 - a)_k * z⁻¹ ^ k * kummerLaplace k (a - 1 - k) z`,
* `f (2k + 2) = (1 - a)_{k+1} * z⁻¹ ^ (k + 1) * kummerLaplace k (a - 2 - k) z`. -/
def upperGammaContFracSolution (a z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
      if Even n then
        -(ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
          kummerLaplace (n / 2) (a - 1 - (n / 2 : ℕ)) z
      else
        (ascPochhammer ℂ (n / 2 + 1)).eval (1 - a) * z⁻¹ ^ (n / 2 + 1) *
          kummerLaplace (n / 2) (a - 2 - (n / 2 : ℕ)) z

/-- Normalization `f 0 = 1` of `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_zero (a z : ℂ) :
    upperGammaContFracSolution a z 0 = 1 := by rfl

/-- Successor formula for `Complex.upperGammaContFracSolution`. -/
theorem upperGammaContFracSolution_succ (a z : ℂ) (n : ℕ) :
    upperGammaContFracSolution a z (n + 1) =
      if Even n then
        -(ascPochhammer ℂ (n / 2)).eval (1 - a) * z⁻¹ ^ (n / 2) *
          kummerLaplace (n / 2) (a - 1 - (n / 2 : ℕ)) z
      else
        (ascPochhammer ℂ (n / 2 + 1)).eval (1 - a) * z⁻¹ ^ (n / 2 + 1) *
          kummerLaplace (n / 2) (a - 2 - (n / 2 : ℕ)) z := (rfl)

/-- Initial value `f 1 = -kummerLaplace 0 (a - 1) z` of `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_one (a z : ℂ) :
    upperGammaContFracSolution a z 1 = -kummerLaplace 0 (a - 1) z := by
  simp [upperGammaContFracSolution]

/-- Odd-index formula for `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_two_mul_add_one (a z : ℂ) (k : ℕ) :
    upperGammaContFracSolution a z (2 * k + 1) =
      -(ascPochhammer ℂ k).eval (1 - a) * z⁻¹ ^ k * kummerLaplace k (a - 1 - k) z := by
  have hev : Even (2 * k) := ⟨k, by ring⟩
  have hdiv : (2 * k) / 2 = k := by omega
  simp only [upperGammaContFracSolution, hev, ↓reduceIte, hdiv]

/-- Even-index formula for `upperGammaContFracSolution`. -/
@[simp]
theorem upperGammaContFracSolution_two_mul_add_two (a z : ℂ) (k : ℕ) :
    upperGammaContFracSolution a z (2 * k + 2) =
      (ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
        kummerLaplace k (a - 2 - k) z := by
  have hodd : ¬Even (2 * k + 1) := by simp [parity_simps]
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp only [upperGammaContFracSolution, hodd, ↓reduceIte, hdiv]

/-- **Three-term recurrence for Legendre's incomplete Gamma continued fraction.**
On `slitPlane`, `f := upperGammaContFracSolution a z` satisfies
`f (n + 2) = f (n + 1) + upperGammaContFracPartNum a z (n + 1) * f n` for every `n : ℕ`. -/
theorem upperGammaContFracSolution_add_two (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    upperGammaContFracSolution a z (n + 2) =
      upperGammaContFracSolution a z (n + 1) +
        upperGammaContFracPartNum a z (n + 1) * upperGammaContFracSolution a z n := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  rcases eq_or_ne n 0 with rfl | hn0
  · -- Base step `n = 0`: integration by parts at `c = 0`.
    have hibp := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_zero (a - 1) hz)
    simp only [← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_add, mul_one,
      show a - 1 - 1 = a - 2 by ring] at hibp
    have h2 : upperGammaContFracSolution a z 2 = (1 - a) * z⁻¹ * kummerLaplace 0 (a - 2) z := by
      simpa [ascPochhammer_one] using upperGammaContFracSolution_two_mul_add_two a z 0
    rw [h2, upperGammaContFracSolution_one, upperGammaContFracPartNum_one,
      upperGammaContFracSolution_zero, mul_one]
    linear_combination hibp
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
      ⟨(n - 1) / 2, by omega⟩
    · -- Odd step `n = 2k + 1`: contiguous difference in the middle parameter.
      have h3 : upperGammaContFracSolution a z (2 * k + 1 + 2) =
          -(ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
            kummerLaplace (k + 1) (a - 2 - k) z := by
        simpa [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring,
          show a - 1 - ((k : ℂ) + 1) = a - 2 - k by ring] using
          upperGammaContFracSolution_two_mul_add_one a z (k + 1)
      have hdiff := kummerLaplace_sub_kummerLaplace_sub_one k (a - 1 - k) hz
      rw [show a - 1 - (k : ℂ) - 1 = a - 2 - k by ring] at hdiff
      rw [h3, show 2 * k + 1 + 1 = 2 * k + 2 from rfl,
        upperGammaContFracSolution_two_mul_add_two, upperGammaContFracPartNum_two_mul_add_two,
        upperGammaContFracSolution_two_mul_add_one, ascPochhammer_succ_eval, pow_succ]
      linear_combination (ascPochhammer ℂ k).eval (1 - a) * (1 - a + (k : ℂ)) *
        (z⁻¹ ^ k * z⁻¹) * hdiff
    · -- Even step `n = 2k + 2`: integration by parts at `c = k + 1`.
      have h4 : upperGammaContFracSolution a z (2 * k + 2 + 2) =
          (ascPochhammer ℂ (k + 2)).eval (1 - a) * z⁻¹ ^ (k + 2) *
            kummerLaplace (k + 1) (a - 3 - k) z := by
        simpa [show 2 * (k + 1) + 2 = 2 * k + 2 + 2 by ring,
          show a - 2 - ((k : ℂ) + 1) = a - 3 - k by ring] using
          upperGammaContFracSolution_two_mul_add_two a z (k + 1)
      have h3 : upperGammaContFracSolution a z (2 * k + 2 + 1) =
          -(ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) *
            kummerLaplace (k + 1) (a - 2 - k) z := by
        simpa [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring,
          show a - 1 - ((k : ℂ) + 1) = a - 2 - k by ring] using
          upperGammaContFracSolution_two_mul_add_one a z (k + 1)
      have hibp := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_add_one k (a - 2 - k) hz)
      simp only [← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_add,
        show a - 2 - (k : ℂ) - 1 = a - 3 - k by ring] at hibp
      rw [h4, h3, show 2 * k + 2 + 1 = 2 * k + 3 from rfl,
        upperGammaContFracPartNum_two_mul_add_three, upperGammaContFracSolution_two_mul_add_two,
        show k + 2 = (k + 1) + 1 from rfl, ascPochhammer_succ_eval, Nat.cast_add, Nat.cast_one,
        pow_succ _ (k + 1)]
      linear_combination (ascPochhammer ℂ (k + 1)).eval (1 - a) * z⁻¹ ^ (k + 1) * hibp

/-- When `z ∈ slitPlane` and `a` is not a positive integer, the Kummer-Laplace recurrence
solution `upperGammaContFracSolution a z n` is eventually nonzero as `n → ∞`. -/
theorem eventually_upperGammaContFracSolution_ne_zero {a : ℂ} (ha : ∀ m : ℕ, a ≠ m + 1)
    {z : ℂ} (hz : z ∈ slitPlane) :
    ∀ᶠ n : ℕ in atTop, upperGammaContFracSolution a z n ≠ 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hp : ∀ k : ℕ, (ascPochhammer ℂ k).eval (1 - a) ≠ 0 := fun k => by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨m, _, hm⟩
    exact ha m (by linear_combination -hm)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_kummerLaplace_ne_zero a hz)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_kummerLaplace_ne_zero (a - 1) hz)
  refine eventually_atTop.mpr ⟨2 * max N₁ N₂ + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
    ⟨(n - 1) / 2, by omega⟩
  · rw [upperGammaContFracSolution_two_mul_add_one]
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (hp k)) (pow_ne_zero k (inv_ne_zero hz0)))
      (hN₁ k ?_)
    have : max N₁ N₂ ≤ k := by omega
    exact (le_max_left N₁ N₂).trans this
  · rw [upperGammaContFracSolution_two_mul_add_two]
    refine mul_ne_zero (mul_ne_zero (hp (k + 1)) (pow_ne_zero (k + 1) (inv_ne_zero hz0))) ?_
    have hk2 : N₂ ≤ k := (le_max_right N₁ N₂).trans (by omega)
    simpa [show a - 1 - 1 - (k : ℂ) = a - 2 - k by ring] using hN₂ k hk2

end Complex

end
