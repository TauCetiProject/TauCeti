/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi

/-!
# The recurrence of the continued fraction for Tricomi's function

For `a ∉ {−1, −2, …}`, DLMF 8.9.1 expands Tricomi's incomplete Gamma function as the continued
fraction
```
Γ(a + 1) e^z γ*(a, z) = 1/(1 − z/(a + 1 + z/(a + 2 − (a + 1) z/(a + 3 + 2z/(a + 4 − ⋯)))))
```
with head `0`, partial denominators `b₁ = 1`, `bₙ = a + n − 1` (`n ≥ 2`) and partial numerators
`a₁ = 1`, `a₂ = −z`, `a_{2k} = −(a + k − 1) z` (`k ≥ 2`), `a_{2k+1} = k z` (`k ≥ 1`). By
Pincherle's theorem, when all partial numerators are nonzero, such a fraction converges to
`−f(1) / f(0)` exactly when its three-term recurrence `y(n + 1) = bₙ y(n) + aₙ y(n − 1)` has a
minimal solution `f` with `f(0) ≠ 0`.

This file writes down an explicit solution of that recurrence in terms of the regularized Kummer
function `𝐌(α, β, z) = Complex.regularizedHGFun {α} {β} z`:
```
f(0) = 1 / Γ(a + 1),
f(2k + 1) = (−1)^{k+1} z^{2k} (a + 1)_{k−1} k! 𝐌(k + 1, a + 2k + 1, z),
f(2k + 2) = (−1)^{k+1} z^{2k+1} (a + 1)_k k! 𝐌(k + 1, a + 2k + 2, z),
```
where `(a + 1)_{−1}` is read as `1`. Normalizing by `f(0) = 1 / Γ(a + 1)` rather than
`f(0) = 1` makes the statements hold for every complex `a`, with `f(0) ≠ 0` exactly when
`a ∉ {−1, −2, …}`. The quotient `−f(1) / f(0)`, computed with Lean's convention `x / 0 = 0`,
is `Γ(a + 1) 𝐌(1, a + 1, z) = Γ(a + 1) e^z γ*(a, z)`, the candidate value of the fraction; this
file proves neither that `f` is minimal nor that the fraction converges. The recurrence reduces
to the two three-term relations of `𝐌` proved in
`TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric`.

## Main definitions

* `Complex.tricomiContFracPartNum a z n` — the partial numerator `aₙ` of DLMF 8.9.1.
* `Complex.tricomiContFracPartDen a n` — the partial denominator `bₙ` of DLMF 8.9.1.
* `Complex.tricomiContFracSolution a z n` — the solution `f(n)` above.

## Main results

* `Complex.tricomiContFracSolution_add_two` — `f` solves the three-term recurrence
  `f(n + 2) = b_{n+1} f(n + 1) + a_{n+1} f(n)` of DLMF 8.9.1, for all complex `a` and `z`.
* `Complex.neg_tricomiContFracSolution_one_div_zero` —
  `−f(1) / f(0) = Γ(a + 1) e^z γ*(a, z)`, where `f(0) ≠ 0` exactly for `a ∉ {−1, −2, …}`
  (`Complex.tricomiContFracSolution_zero_eq_zero_iff`).

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9) and
  [§13.3](https://dlmf.nist.gov/13.3).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967).
-/

public section

noncomputable section

open Complex
open scoped Nat

namespace Complex

/-- The partial numerators of the continued fraction DLMF 8.9.1 for `Γ(a + 1) e^z γ*(a, z)`:
`a₁ = 1`, `a₂ = −z`, `a_{2k} = −(a + k − 1) z` for `k ≥ 2` and `a_{2k+1} = k z` for `k ≥ 1`.
The value at `n = 0` is not used. -/
def tricomiContFracPartNum (a z : ℂ) (n : ℕ) : ℂ :=
  if n = 1 then 1
  else if n = 2 then -z
  else if Even n then -(a + (n / 2 : ℕ) - 1) * z
  else (n / 2 : ℕ) * z

/-- The partial denominators of the continued fraction DLMF 8.9.1 for `Γ(a + 1) e^z γ*(a, z)`:
`b₁ = 1` and `bₙ = a + n − 1` for `n ≥ 2`. The value at `n = 0` is not used. -/
def tricomiContFracPartDen (a : ℂ) (n : ℕ) : ℂ :=
  if n = 1 then 1 else a + n - 1

/-- The explicit solution of the three-term recurrence of the continued fraction DLMF 8.9.1:
`f(0) = 1 / Γ(a + 1)` and, for `n ≥ 1`,
`f(n) = (−1)^{⌈n/2⌉} z^{n−1} dₙ 𝐌(⌈n/2⌉, a + n, z)` with `d₁ = 1`,
`d_{2k} = (a + 1)_{k−1} (k − 1)!` and `d_{2k+1} = (a + 1)_{k−1} k!`, where
`𝐌(α, β, z) = Complex.regularizedHGFun {α} {β} z` is the regularized Kummer function. Its
characterizing values are `tricomiContFracSolution_zero`, `tricomiContFracSolution_one`,
`tricomiContFracSolution_two_mul_add_two` and `tricomiContFracSolution_two_mul_add_three`. -/
def tricomiContFracSolution (a z : ℂ) : ℕ → ℂ
  | 0 => (Gamma (a + 1))⁻¹
  | n + 1 => (-1) ^ ((n + 2) / 2) * z ^ n * (ascPochhammer ℂ ((n + 1) / 2 - 1)).eval (a + 1) *
      ((n / 2)! : ℂ) * regularizedHGFun {(((n + 2) / 2 : ℕ) : ℂ)} {a + n + 1} z

/-- The first partial numerator of DLMF 8.9.1 is `a₁ = 1`. -/
@[simp]
theorem tricomiContFracPartNum_one (a z : ℂ) : tricomiContFracPartNum a z 1 = 1 := by
  simp [tricomiContFracPartNum]

/-- The second partial numerator of DLMF 8.9.1 is `a₂ = −z`. -/
@[simp]
theorem tricomiContFracPartNum_two (a z : ℂ) : tricomiContFracPartNum a z 2 = -z := by
  simp [tricomiContFracPartNum]

/-- The odd partial numerators of DLMF 8.9.1 are `a_{2k+3} = (k + 1) z`. -/
@[simp]
theorem tricomiContFracPartNum_two_mul_add_three (a z : ℂ) (k : ℕ) :
    tricomiContFracPartNum a z (2 * k + 3) = (k + 1) * z := by
  have h : (2 * k + 3) / 2 = k + 1 := by omega
  simp [tricomiContFracPartNum, h, Nat.even_add, parity_simps]

/-- The even partial numerators of DLMF 8.9.1 beyond `a₂` are `a_{2k+4} = −(a + k + 1) z`. -/
@[simp]
theorem tricomiContFracPartNum_two_mul_add_four (a z : ℂ) (k : ℕ) :
    tricomiContFracPartNum a z (2 * k + 4) = -(a + k + 1) * z := by
  have h : (2 * k + 4) / 2 = k + 2 := by omega
  have he : Even (2 * k + 4) := ⟨k + 2, by ring⟩
  simp only [tricomiContFracPartNum, h, he, show 2 * k + 4 ≠ 1 by omega,
    show 2 * k + 4 ≠ 2 by omega, ↓reduceIte]
  push_cast
  ring

/-- The first partial denominator of DLMF 8.9.1 is `b₁ = 1`. -/
@[simp]
theorem tricomiContFracPartDen_one (a : ℂ) : tricomiContFracPartDen a 1 = 1 := by
  simp [tricomiContFracPartDen]

/-- The partial denominators of DLMF 8.9.1 other than `b₁` are `bₙ = a + n − 1`. -/
@[simp]
theorem tricomiContFracPartDen_of_ne_one (a : ℂ) {n : ℕ} (hn : n ≠ 1) :
    tricomiContFracPartDen a n = a + n - 1 := by
  simp [tricomiContFracPartDen, hn]

/-- The solution of the recurrence of DLMF 8.9.1 starts at `f(0) = 1 / Γ(a + 1)`. -/
@[simp]
theorem tricomiContFracSolution_zero (a z : ℂ) :
    tricomiContFracSolution a z 0 = (Gamma (a + 1))⁻¹ := (rfl)

/-- The initial value `f(0) = 1 / Γ(a + 1)` vanishes exactly at `a ∈ {−1, −2, …}`, the
parameters excluded in DLMF 8.9.1. -/
theorem tricomiContFracSolution_zero_eq_zero_iff (a z : ℂ) :
    tricomiContFracSolution a z 0 = 0 ↔ ∃ n : ℕ, a = -(n + 1) := by
  rw [tricomiContFracSolution_zero, inv_eq_zero, Gamma_eq_zero_iff]
  refine exists_congr fun n => ⟨fun h => ?_, fun h => ?_⟩ <;> linear_combination h

/-- The solution of the recurrence of DLMF 8.9.1 at `n = 1` is `f(1) = −𝐌(1, a + 1, z)`. -/
@[simp]
theorem tricomiContFracSolution_one (a z : ℂ) :
    tricomiContFracSolution a z 1 = -regularizedHGFun {1} {a + 1} z := by
  simp [tricomiContFracSolution]

/-- The solution of the recurrence of DLMF 8.9.1 at even indices:
`f(2k + 2) = (−1)^{k+1} z^{2k+1} (a + 1)_k k! 𝐌(k + 1, a + 2k + 2, z)`. -/
@[simp]
theorem tricomiContFracSolution_two_mul_add_two (a z : ℂ) (k : ℕ) :
    tricomiContFracSolution a z (2 * k + 2) = (-1) ^ (k + 1) * z ^ (2 * k + 1) *
      (ascPochhammer ℂ k).eval (a + 1) * (k ! : ℂ) *
      regularizedHGFun {(k : ℂ) + 1} {a + 2 * k + 2} z := by
  have h₁ : (2 * k + 1 + 2) / 2 = k + 1 := by omega
  have h₂ : (2 * k + 1 + 1) / 2 - 1 = k := by omega
  have h₃ : (2 * k + 1) / 2 = k := by omega
  simp only [tricomiContFracSolution, h₁, h₂, h₃]
  push_cast
  ring_nf

/-- The solution of the recurrence of DLMF 8.9.1 at odd indices from `3` on:
`f(2k + 3) = (−1)^k z^{2k+2} (a + 1)_k (k + 1)! 𝐌(k + 2, a + 2k + 3, z)`. -/
@[simp]
theorem tricomiContFracSolution_two_mul_add_three (a z : ℂ) (k : ℕ) :
    tricomiContFracSolution a z (2 * k + 3) = (-1) ^ k * z ^ (2 * k + 2) *
      (ascPochhammer ℂ k).eval (a + 1) * ((k + 1)! : ℂ) *
      regularizedHGFun {(k : ℂ) + 2} {a + 2 * k + 3} z := by
  have h₁ : (2 * k + 2 + 2) / 2 = k + 2 := by omega
  have h₂ : (2 * k + 2 + 1) / 2 - 1 = k := by omega
  have h₃ : (2 * k + 2) / 2 = k + 1 := by omega
  simp only [tricomiContFracSolution, h₁, h₂, h₃]
  push_cast
  ring_nf

/-- The recurrence of DLMF 8.9.1 at `n = 2k + 2`, from
`Complex.regularizedHGFun_singleton_eq_mul_sub_mul`. -/
private theorem tricomiContFracSolution_add_two_two_mul_add_two (a z : ℂ) (k : ℕ) :
    tricomiContFracSolution a z (2 * k + 4) = tricomiContFracPartDen a (2 * k + 3) *
      tricomiContFracSolution a z (2 * k + 3) +
      tricomiContFracPartNum a z (2 * k + 3) * tricomiContFracSolution a z (2 * k + 2) := by
  have hR : regularizedHGFun {(k : ℂ) + 1} {a + 2 * k + 2} z =
      (a + 2 * k + 2) * regularizedHGFun {(k : ℂ) + 2} {a + 2 * k + 3} z -
        (a + k + 1) * z * regularizedHGFun {(k : ℂ) + 2} {a + 2 * k + 4} z := by
    rw [regularizedHGFun_singleton_eq_mul_sub_mul]
    ring_nf
  rw [show 2 * k + 4 = 2 * (k + 1) + 2 by ring, tricomiContFracSolution_two_mul_add_two,
    tricomiContFracSolution_two_mul_add_three, tricomiContFracSolution_two_mul_add_two,
    tricomiContFracPartNum_two_mul_add_three, tricomiContFracPartDen_of_ne_one _ (by omega)]
  push_cast
  rw [show (k : ℂ) + 1 + 1 = k + 2 by ring, show a + 2 * ((k : ℂ) + 1) + 2 = a + 2 * k + 4 by
    ring, ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  linear_combination (-1) ^ k * z ^ (2 * k + 2) * (ascPochhammer ℂ k).eval (a + 1) *
    ((k + 1) * (k ! : ℂ)) * hR

/-- The recurrence of DLMF 8.9.1 at `n = 2k + 3`, from
`Complex.regularizedHGFun_singleton_eq_mul_add_mul`. -/
private theorem tricomiContFracSolution_add_two_two_mul_add_three (a z : ℂ) (k : ℕ) :
    tricomiContFracSolution a z (2 * k + 5) = tricomiContFracPartDen a (2 * k + 4) *
      tricomiContFracSolution a z (2 * k + 4) +
      tricomiContFracPartNum a z (2 * k + 4) * tricomiContFracSolution a z (2 * k + 3) := by
  have hR : regularizedHGFun {(k : ℂ) + 2} {a + 2 * k + 3} z =
      (a + 2 * k + 3) * regularizedHGFun {(k : ℂ) + 2} {a + 2 * k + 4} z +
        (k + 2) * z * regularizedHGFun {(k : ℂ) + 3} {a + 2 * k + 5} z := by
    rw [regularizedHGFun_singleton_eq_mul_add_mul]
    ring_nf
  rw [show 2 * k + 5 = 2 * (k + 1) + 3 by ring, tricomiContFracSolution_two_mul_add_three,
    tricomiContFracPartNum_two_mul_add_four, tricomiContFracPartDen_of_ne_one _ (by omega),
    show 2 * k + 4 = 2 * (k + 1) + 2 by ring, tricomiContFracSolution_two_mul_add_two,
    tricomiContFracSolution_two_mul_add_three]
  push_cast
  rw [show (k : ℂ) + 1 + 2 = k + 3 by ring, show (k : ℂ) + 1 + 1 = k + 2 by ring,
    show a + 2 * ((k : ℂ) + 1) + 3 = a + 2 * k + 5 by ring,
    show a + 2 * ((k : ℂ) + 1) + 2 = a + 2 * k + 4 by ring, ascPochhammer_succ_eval,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  linear_combination (-1) ^ k * z ^ (2 * k + 3) * (ascPochhammer ℂ k).eval (a + 1) *
    (a + 1 + k) * ((k + 1) * (k ! : ℂ)) * hR

/-- The solution `tricomiContFracSolution` satisfies the three-term recurrence
`f(n + 2) = b_{n+1} f(n + 1) + a_{n+1} f(n)` of the continued fraction DLMF 8.9.1, for all complex
`a` and `z`. -/
theorem tricomiContFracSolution_add_two (a z : ℂ) (n : ℕ) :
    tricomiContFracSolution a z (n + 2) = tricomiContFracPartDen a (n + 1) *
      tricomiContFracSolution a z (n + 1) +
      tricomiContFracPartNum a z (n + 1) * tricomiContFracSolution a z n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases k with _ | k
    · -- `n = 0`: the recurrence of `γ*` in its parameter
      have hT := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z
      simp only [tricomiIncompleteGamma_def, add_assoc, one_add_one_eq_two] at hT
      rw [tricomiContFracSolution_two_mul_add_two]
      simp only [Nat.cast_zero, mul_zero, zero_add, add_zero, pow_one, ascPochhammer_zero,
        Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one, tricomiContFracSolution_one,
        tricomiContFracSolution_zero, tricomiContFracPartDen_one,
        tricomiContFracPartNum_one]
      apply mul_left_cancel₀ (Complex.exp_ne_zero (-z))
      linear_combination hT
    · rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring,
        show 2 * (k + 1) = 2 * k + 2 by ring]
      exact tricomiContFracSolution_add_two_two_mul_add_two a z k
  · rcases k with _ | k
    · -- `n = 1`: the relation `regularizedHGFun_singleton_eq_mul_add_mul`
      have hR : regularizedHGFun {1} {a + 1} z = (a + 1) * regularizedHGFun {1} {a + 2} z +
          z * regularizedHGFun {2} {a + 3} z := by
        rw [regularizedHGFun_singleton_eq_mul_add_mul]
        ring_nf
      rw [tricomiContFracSolution_two_mul_add_three, tricomiContFracSolution_two_mul_add_two,
        show 2 * 0 + 1 + 1 = 2 by rfl, tricomiContFracPartNum_two]
      simp only [Nat.cast_zero, mul_zero, zero_add, add_zero, pow_zero, pow_one,
        ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero, Nat.factorial_one,
        Nat.cast_one, tricomiContFracSolution_one,
        tricomiContFracPartDen_of_ne_one a (show 2 ≠ 1 by omega)]
      push_cast
      linear_combination -z * hR
    · rw [show 2 * (k + 1) + 1 + 2 = 2 * k + 5 by ring,
        show 2 * (k + 1) + 1 + 1 = 2 * k + 4 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
      exact tricomiContFracSolution_add_two_two_mul_add_three a z k

/-- The quotient `−f(1) / f(0)` of the solution `tricomiContFracSolution` is
`Γ(a + 1) e^z γ*(a, z)`, the candidate value of the continued fraction DLMF 8.9.1. Both sides
vanish when `f(0) = 0`, that is for `a ∈ {−1, −2, …}`; neither convergence of the fraction nor
minimality of `f` is asserted. -/
theorem neg_tricomiContFracSolution_one_div_zero (a z : ℂ) :
    -tricomiContFracSolution a z 1 / tricomiContFracSolution a z 0 =
      Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z := by
  rw [tricomiContFracSolution_one, tricomiContFracSolution_zero, tricomiIncompleteGamma_def,
    Complex.exp_neg]
  field_simp

end Complex
