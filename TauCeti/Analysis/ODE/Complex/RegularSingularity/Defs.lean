/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Indicial polynomial and formal coefficient recurrences at a regular singularity

For a second-order complex linear differential equation

`w''(z) + f(z) w'(z) + g(z) w(z) = 0`

around a point `z₀` where `(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and
`(z - z₀)² g(z) = ∑ g_s (z - z₀)^s`, the leading exponents at `z₀` are the roots `α₁`, `α₂`
(`Re α₂ ≤ Re α₁`) of the **indicial polynomial**

`Q(α) = α(α - 1) + f₀ α + g₀ = (α - α₁)(α - α₂)`.

This file defines `TauCeti.indicialPoly` together with the canonical normalized formal coefficient
sequences of NIST DLMF §2.7(ii):
* `TauCeti.regularSingularCoeff`: the sequence `a_s` (`a₀ = 1`) solving
  `Q(ρ + s) a_s = -∑_{k < s} ((ρ + k) f_{s - k} + g_{s - k}) a_k` (DLMF 2.7.5);
* `TauCeti.regularSingularLogMultiplier`: the logarithmic multiplier `c` in DLMF 2.7.6 when
  `α₁ - α₂ = N ∈ ℕ` (`c = 1` for `N = 0`, and cancelling the resonant sum at `s = N` for `N ≥ 1`);
* `TauCeti.regularSingularSecondCoeff`: the second-solution coefficient sequence `b_s` in
  DLMF 2.7.6, normalized by `b_N = 0` and `b₀ = 1` for `N ≥ 1`.

Analytic convergence on the full disc `‖z - z₀‖ < r`, solutionhood on the slit punctured disc,
uniqueness, and Wronskian nonvanishing are proved in
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Basic`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.7(ii), formulas 2.7.2–2.7.6,
  <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Finset

namespace TauCeti

/-! ### Indicial polynomial and roots -/

/-- The indicial polynomial `Q(α) = α(α - 1) + f₀ α + g₀` of `w'' + f w' + g w = 0` at a regular
singularity with leading Taylor coefficients `f₀` of `(z - z₀) f(z)` and `g₀` of
`(z - z₀)² g(z)`. -/
def indicialPoly (f₀ g₀ α : ℂ) : ℂ :=
  α * (α - 1) + f₀ * α + g₀

/-- Explicit formula for `indicialPoly`. -/
theorem indicialPoly_def (f₀ g₀ α : ℂ) :
    indicialPoly f₀ g₀ α = α * (α - 1) + f₀ * α + g₀ := (rfl)

@[simp]
theorem indicialPoly_zero (f₀ g₀ : ℂ) : indicialPoly f₀ g₀ 0 = g₀ := by
  simp [indicialPoly]

/-- Shifting the argument of `indicialPoly` expands quadratically in the shift. -/
theorem indicialPoly_add (f₀ g₀ α β : ℂ) :
    indicialPoly f₀ g₀ (α + β) = indicialPoly f₀ g₀ α + β * (β + (2 * α + f₀ - 1)) := by
  simp only [indicialPoly]
  ring

/-- Factorization of `indicialPoly f₀ g₀` into `(α - α₁)(α - α₂)` is equivalent to Vieta's
relations `α₁ + α₂ = 1 - f₀` and `α₁ α₂ = g₀`. -/
theorem indicialPoly_eq_mul_sub_iff {f₀ g₀ α₁ α₂ : ℂ} :
    (∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂)) ↔
      α₁ + α₂ = 1 - f₀ ∧ α₁ * α₂ = g₀ := by
  refine ⟨fun h => ?_, fun ⟨hsum, hprod⟩ α => ?_⟩
  · have h0 := h 0
    have h1 := h 1
    simp only [indicialPoly] at h0 h1
    refine ⟨?_, by linear_combination -h0⟩
    linear_combination h1 - h0
  · simp only [indicialPoly, ← hprod]
    linear_combination α * hsum

/-- Every complex indicial polynomial factors as `(α - α₁)(α - α₂)` with `Re α₂ ≤ Re α₁`. -/
theorem exists_indicialPoly_roots (f₀ g₀ : ℂ) :
    ∃ α₁ α₂ : ℂ, α₂.re ≤ α₁.re ∧ ∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂) := by
  set Δ : ℂ := (1 - f₀) ^ 2 - 4 * g₀
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d ^ 2 = Δ := by
    rcases eq_or_ne Δ 0 with h0 | hne
    · exact ⟨0, by simp [h0]⟩
    · refine ⟨Δ ^ (1 / 2 : ℂ), ?_⟩
      rw [sq, ← Complex.cpow_add _ _ hne]
      norm_num
  set r₁ : ℂ := (1 - f₀ + d) / 2
  set r₂ : ℂ := (1 - f₀ - d) / 2
  have hfact : ∀ α, indicialPoly f₀ g₀ α = (α - r₁) * (α - r₂) := fun α => by
    simp only [indicialPoly, r₁, r₂]
    linear_combination (1 / 4 : ℂ) * hd
  rcases le_total r₂.re r₁.re with hle | hle
  · exact ⟨r₁, r₂, hle, hfact⟩
  · exact ⟨r₂, r₁, hle, fun α => by rw [mul_comm]; exact hfact α⟩

/-- For the root `α₁` of `indicialPoly` with `Re α₂ ≤ Re α₁`, no positive integer shift `α₁ + s`
is a root of `indicialPoly`. -/
theorem indicialPoly_add_nat_ne_zero_of_re_le {f₀ g₀ α₁ α₂ : ℂ}
    (hfact : ∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂)) (hre : α₂.re ≤ α₁.re)
    {s : ℕ} (hs : 1 ≤ s) :
    indicialPoly f₀ g₀ (α₁ + s) ≠ 0 := by
  rw [hfact]
  have hs0 : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiff : α₁ + (s : ℂ) - α₂ ≠ 0 := by
    intro h
    have hre0 := congrArg Complex.re h
    simp only [add_re, sub_re, natCast_re, zero_re] at hre0
    have hs_pos : (1 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  simpa [add_sub_cancel_left] using mul_ne_zero hs0 hdiff

/-- If `α₁ - α₂` is never a natural number, then no positive integer shift `α₂ + s` is a root
of `indicialPoly`. -/
theorem indicialPoly_add_nat_ne_zero_of_sub_ne_nat {f₀ g₀ α₁ α₂ : ℂ}
    (hfact : ∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂)) (hnat : ∀ N : ℕ, α₁ - α₂ ≠ N)
    {s : ℕ} (hs : 1 ≤ s) :
    indicialPoly f₀ g₀ (α₂ + s) ≠ 0 := by
  rw [hfact]
  have hs0 : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiff : α₂ + (s : ℂ) - α₁ ≠ 0 := fun h => hnat s (by linear_combination -h)
  simpa [add_sub_cancel_left] using mul_ne_zero hdiff hs0

/-- In the resonant case `α₁ = α₂ + N`, `indicialPoly f₀ g₀ (α₂ + s) ≠ 0` whenever `s ≠ 0` and
`s ≠ N`. -/
theorem indicialPoly_add_nat_ne_zero_of_ne {f₀ g₀ α₂ : ℂ} {N s : ℕ}
    (hfact : ∀ α, indicialPoly f₀ g₀ α = (α - (α₂ + N)) * (α - α₂))
    (hs0 : s ≠ 0) (hsN : s ≠ N) :
    indicialPoly f₀ g₀ (α₂ + s) ≠ 0 := by
  rw [hfact]
  have h1 : α₂ + (s : ℂ) - (α₂ + (N : ℂ)) ≠ 0 := by
    have hne : (s : ℂ) ≠ (N : ℂ) := by exact_mod_cast hsN
    exact fun h => hne (by linear_combination h)
  have h2 : α₂ + (s : ℂ) - α₂ ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr hs0 : (s : ℂ) ≠ 0)
  exact mul_ne_zero h1 h2

/-! ### Recursive coefficient sequences -/

/-- The normalized series coefficients `a_s` (`a₀ = 1`) attached to an indicial root `ρ` via
`Q(ρ + s) a_s = -∑_{k < s} ((ρ + k) f_{s - k} + g_{s - k}) a_k` (DLMF 2.7.5). -/
def regularSingularCoeff (fs gs : ℕ → ℂ) (ρ : ℂ) (s : ℕ) : ℂ :=
  if s = 0 then 1
  else -(indicialPoly (fs 0) (gs 0) (ρ + s))⁻¹ *
    ∑ k ∈ (range s).attach,
      ((ρ + k.1) * fs (s - k.1) + gs (s - k.1)) * regularSingularCoeff fs gs ρ k.1
termination_by s
decreasing_by exact mem_range.mp k.2

@[simp]
theorem regularSingularCoeff_zero (fs gs : ℕ → ℂ) (ρ : ℂ) :
    regularSingularCoeff fs gs ρ 0 = 1 := by
  rw [regularSingularCoeff]
  simp

/-- Unfolding formula for `regularSingularCoeff` at positive indices. -/
theorem regularSingularCoeff_of_ne_zero (fs gs : ℕ → ℂ) (ρ : ℂ) {s : ℕ} (hs : s ≠ 0) :
    regularSingularCoeff fs gs ρ s =
      -(indicialPoly (fs 0) (gs 0) (ρ + s))⁻¹ *
        ∑ k ∈ range s,
          ((ρ + k) * fs (s - k) + gs (s - k)) * regularSingularCoeff fs gs ρ k := by
  conv_lhs => rw [regularSingularCoeff]
  simp only [hs, ↓reduceIte]
  rw [Finset.sum_attach (range s) fun k =>
    ((ρ + (k : ℂ)) * fs (s - k) + gs (s - k)) * regularSingularCoeff fs gs ρ k]

/-- When `Q(ρ + s) ≠ 0`, `regularSingularCoeff` satisfies the linear indicial recursion
(DLMF 2.7.5). -/
theorem indicialPoly_mul_regularSingularCoeff {fs gs : ℕ → ℂ} {ρ : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hQ : indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0) :
    indicialPoly (fs 0) (gs 0) (ρ + s) * regularSingularCoeff fs gs ρ s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * regularSingularCoeff fs gs ρ k := by
  rw [regularSingularCoeff_of_ne_zero fs gs ρ (by omega)]
  field_simp [hQ]

/-- Any sequence `a` with `a 0 = 1` satisfying the non-resonant indicial recursion coincides with
`regularSingularCoeff`. -/
theorem eq_regularSingularCoeff_of_rec {fs gs a : ℕ → ℂ} {ρ : ℂ}
    (hres : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0)
    (ha0 : a 0 = 1)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
    a = regularSingularCoeff fs gs ρ := by
  ext s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    rcases eq_or_ne s 0 with rfl | hs
    · simp [ha0]
    · have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs
      have hQ := hres s hs1
      apply mul_left_cancel₀ hQ
      rw [ha s hs1, indicialPoly_mul_regularSingularCoeff hs1 hQ]
      congr 1
      exact sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk)]

/-- The logarithmic multiplier `c` in the second solution
`(z - z₀)^{α₂} ∑_{s ≠ N} b_s (z - z₀)^s + c w₁(z) log(z - z₀)` when `α₁ - α₂ = N ∈ ℕ`
(DLMF 2.7.6): `c = 1` for `N = 0` (double root), and for `N ≥ 1` it cancels the resonant
obstruction at index `N`. -/
def regularSingularLogMultiplier (fs gs : ℕ → ℂ) (α₂ : ℂ) (N : ℕ) : ℂ :=
  if N = 0 then 1
  else -(N : ℂ)⁻¹ *
    ∑ k ∈ range N, ((α₂ + k) * fs (N - k) + gs (N - k)) * regularSingularCoeff fs gs α₂ k

@[simp]
theorem regularSingularLogMultiplier_zero (fs gs : ℕ → ℂ) (α₂ : ℂ) :
    regularSingularLogMultiplier fs gs α₂ 0 = 1 := by
  simp [regularSingularLogMultiplier]

/-- Unfolding formula for `regularSingularLogMultiplier` when `N ≠ 0`. -/
theorem regularSingularLogMultiplier_of_ne_zero (fs gs : ℕ → ℂ) (α₂ : ℂ) {N : ℕ} (hN : N ≠ 0) :
    regularSingularLogMultiplier fs gs α₂ N =
      -(N : ℂ)⁻¹ * ∑ k ∈ range N,
        ((α₂ + k) * fs (N - k) + gs (N - k)) * regularSingularCoeff fs gs α₂ k := by
  simp [regularSingularLogMultiplier, hN]

/-- Cancellation identity `N * c = -∑_{k < N} ((α₂ + k) f_{N - k} + g_{N - k}) a_k` for `1 ≤ N`. -/
theorem natCast_mul_regularSingularLogMultiplier (fs gs : ℕ → ℂ) (α₂ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℂ) * regularSingularLogMultiplier fs gs α₂ N =
      -∑ k ∈ range N,
        ((α₂ + k) * fs (N - k) + gs (N - k)) * regularSingularCoeff fs gs α₂ k := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [regularSingularLogMultiplier_of_ne_zero fs gs α₂ (by omega)]
  field_simp [hN0]

/-- The series coefficients `b_s` of the second solution when `α₁ - α₂ = N ∈ ℕ` (DLMF 2.7.6),
normalized by `b_N = 0` (omitting the resonant term) and `b₀ = 1` when `N ≥ 1`. -/
def regularSingularSecondCoeff (fs gs : ℕ → ℂ) (α₂ : ℂ) (N s : ℕ) : ℂ :=
  if s = N then 0
  else if s = 0 then 1
  else if s < N then
    -(indicialPoly (fs 0) (gs 0) (α₂ + s))⁻¹ *
      ∑ k ∈ (range s).attach,
        ((α₂ + k.1) * fs (s - k.1) + gs (s - k.1)) *
          regularSingularSecondCoeff fs gs α₂ N k.1
  else
    -(indicialPoly (fs 0) (gs 0) (α₂ + s))⁻¹ *
      ((∑ k ∈ (range s).attach,
          ((α₂ + k.1) * fs (s - k.1) + gs (s - k.1)) *
            regularSingularSecondCoeff fs gs α₂ N k.1) +
        regularSingularLogMultiplier fs gs α₂ N *
          ((2 * (α₂ + s) + fs 0 - 1) * regularSingularCoeff fs gs (α₂ + N) (s - N) +
            ∑ k ∈ range (s - N), fs (s - N - k) * regularSingularCoeff fs gs (α₂ + N) k))
termination_by s
decreasing_by all_goals exact mem_range.mp k.2

@[simp]
theorem regularSingularSecondCoeff_self (fs gs : ℕ → ℂ) (α₂ : ℂ) (N : ℕ) :
    regularSingularSecondCoeff fs gs α₂ N N = 0 := by
  rw [regularSingularSecondCoeff]
  simp

@[simp]
theorem regularSingularSecondCoeff_zero_of_pos (fs gs : ℕ → ℂ) (α₂ : ℂ) {N : ℕ} (hN : 0 < N) :
    regularSingularSecondCoeff fs gs α₂ N 0 = 1 := by
  rw [regularSingularSecondCoeff]
  have : (0 : ℕ) ≠ N := by omega
  simp [this]

/-- Below the resonant index `N`, `regularSingularSecondCoeff` agrees with
`regularSingularCoeff`. -/
theorem regularSingularSecondCoeff_eq_regularSingularCoeff_of_lt (fs gs : ℕ → ℂ) (α₂ : ℂ)
    {N s : ℕ} (hs : s < N) :
    regularSingularSecondCoeff fs gs α₂ N s = regularSingularCoeff fs gs α₂ s := by
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    rcases eq_or_ne s 0 with rfl | hs0
    · simp [regularSingularSecondCoeff_zero_of_pos fs gs α₂ hs]
    · conv_lhs => rw [regularSingularSecondCoeff]
      have hne : s ≠ N := by omega
      simp only [hne, hs0, hs, ↓reduceIte]
      rw [Finset.sum_attach (range s) fun k =>
        ((α₂ + (k : ℂ)) * fs (s - k) + gs (s - k)) * regularSingularSecondCoeff fs gs α₂ N k,
        regularSingularCoeff_of_ne_zero fs gs α₂ hs0]
      congr 1
      exact sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk) ((mem_range.mp hk).trans hs)]

/-- Recursion for `regularSingularSecondCoeff` at indices `1 ≤ s < N`. -/
theorem indicialPoly_mul_regularSingularSecondCoeff_of_lt {fs gs : ℕ → ℂ} {α₂ : ℂ} {N s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < N) (hQ : indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    indicialPoly (fs 0) (gs 0) (α₂ + s) * regularSingularSecondCoeff fs gs α₂ N s =
      -∑ k ∈ range s,
        ((α₂ + k) * fs (s - k) + gs (s - k)) * regularSingularSecondCoeff fs gs α₂ N k := by
  conv_lhs => rw [regularSingularSecondCoeff]
  have hne : s ≠ N := by omega
  have hs0 : s ≠ 0 := by omega
  simp only [hne, hs0, hsN, ↓reduceIte]
  rw [Finset.sum_attach (range s) fun k =>
    ((α₂ + (k : ℂ)) * fs (s - k) + gs (s - k)) * regularSingularSecondCoeff fs gs α₂ N k]
  field_simp [hQ]

/-- Unfolding formula for `regularSingularSecondCoeff` above the resonant index `N < s`. -/
theorem regularSingularSecondCoeff_of_gt (fs gs : ℕ → ℂ) (α₂ : ℂ) {N s : ℕ} (hsN : N < s) :
    regularSingularSecondCoeff fs gs α₂ N s =
      -(indicialPoly (fs 0) (gs 0) (α₂ + s))⁻¹ *
        ((∑ k ∈ range s,
            ((α₂ + k) * fs (s - k) + gs (s - k)) * regularSingularSecondCoeff fs gs α₂ N k) +
          regularSingularLogMultiplier fs gs α₂ N *
            ((2 * (α₂ + s) + fs 0 - 1) * regularSingularCoeff fs gs (α₂ + N) (s - N) +
              ∑ k ∈ range (s - N), fs (s - N - k) * regularSingularCoeff fs gs (α₂ + N) k)) := by
  conv_lhs => rw [regularSingularSecondCoeff]
  have hne : s ≠ N := by omega
  have hs0 : s ≠ 0 := by omega
  have hnlt : ¬s < N := by omega
  simp only [hne, hs0, hnlt, ↓reduceIte]
  rw [Finset.sum_attach (range s) fun k =>
    ((α₂ + (k : ℂ)) * fs (s - k) + gs (s - k)) * regularSingularSecondCoeff fs gs α₂ N k]

/-- Recursion for `regularSingularSecondCoeff` above the resonant index `N < s`. -/
theorem indicialPoly_mul_regularSingularSecondCoeff_of_gt {fs gs : ℕ → ℂ} {α₂ : ℂ} {N s : ℕ}
    (hsN : N < s) (hQ : indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    indicialPoly (fs 0) (gs 0) (α₂ + s) * regularSingularSecondCoeff fs gs α₂ N s =
      -(∑ k ∈ range s,
          ((α₂ + k) * fs (s - k) + gs (s - k)) * regularSingularSecondCoeff fs gs α₂ N k) -
        regularSingularLogMultiplier fs gs α₂ N *
          ((2 * (α₂ + s) + fs 0 - 1) * regularSingularCoeff fs gs (α₂ + N) (s - N) +
            ∑ k ∈ range (s - N), fs (s - N - k) * regularSingularCoeff fs gs (α₂ + N) k) := by
  rw [regularSingularSecondCoeff_of_gt fs gs α₂ hsN]
  field_simp [hQ]
  ring

/-- Any pair `(b', c')` satisfying `b' N = 0`, the normalization `(N = 0 → c' = 1)`,
`(1 ≤ N → b' 0 = 1)`, and the resonant indicial recursion coincides with
`(regularSingularSecondCoeff fs gs α₂ N, regularSingularLogMultiplier fs gs α₂ N)`. -/
theorem eq_regularSingularSecondCoeff_of_rec {fs gs b' : ℕ → ℂ} {α₂ c' : ℂ} {N : ℕ}
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂))
    (hb'N : b' N = 0)
    (hc'0 : N = 0 → c' = 1)
    (hb'0 : 1 ≤ N → b' 0 = 1)
    (hrec : ∀ s : ℕ,
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) +
      c' * (if s < N then 0
        else (2 * (α₂ + s) + fs 0 - 1) * regularSingularCoeff fs gs (α₂ + N) (s - N) +
          ∑ k ∈ range (s - N), fs (s - N - k) * regularSingularCoeff fs gs (α₂ + N) k) = 0) :
    b' = regularSingularSecondCoeff fs gs α₂ N ∧
      c' = regularSingularLogMultiplier fs gs α₂ N := by
  set a := regularSingularCoeff fs gs (α₂ + N)
  have hb'_lt : ∀ s < N, b' s = regularSingularCoeff fs gs α₂ s := by
    intro s hs
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      rcases eq_or_ne s 0 with rfl | hs0
      · simp [hb'0 hs]
      · have hQ := indicialPoly_add_nat_ne_zero_of_ne hfact hs0 hs.ne
        have hDs := hrec s
        simp only [hs, ↓reduceIte, mul_zero, add_zero] at hDs
        apply mul_left_cancel₀ hQ
        rw [indicialPoly_mul_regularSingularCoeff (Nat.pos_of_ne_zero hs0) hQ]
        have hsum_eq : (∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) =
            ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) *
              regularSingularCoeff fs gs α₂ k :=
          sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk) ((mem_range.mp hk).trans hs)]
        linear_combination hDs - hsum_eq
  have hc'_eq : c' = regularSingularLogMultiplier fs gs α₂ N := by
    rcases eq_or_ne N 0 with rfl | hN0
    · simp [hc'0 rfl]
    · have hDN := hrec N
      have hQN : indicialPoly (fs 0) (gs 0) (α₂ + N) = 0 := by simp [hfact]
      have ha0_eq : a 0 = 1 := regularSingularCoeff_zero fs gs (α₂ + N)
      have hvieta := (indicialPoly_eq_mul_sub_iff.mp hfact).1
      have h2N : 2 * (α₂ + (N : ℂ)) + fs 0 - 1 = N := by linear_combination hvieta
      simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, Finset.range_zero, Finset.sum_empty,
        add_zero, hQN, zero_mul, zero_add, ha0_eq, mul_one, h2N] at hDN
      have hsum_eq : (∑ k ∈ range N, ((α₂ + k) * fs (N - k) + gs (N - k)) * b' k) =
          ∑ k ∈ range N, ((α₂ + k) * fs (N - k) + gs (N - k)) *
            regularSingularCoeff fs gs α₂ k :=
        sum_congr rfl fun k hk => by rw [hb'_lt k (mem_range.mp hk)]
      rw [hsum_eq] at hDN
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hN0 : (N : ℂ) ≠ 0)
      rw [natCast_mul_regularSingularLogMultiplier fs gs α₂ (Nat.pos_of_ne_zero hN0)]
      linear_combination hDN
  refine ⟨?_, hc'_eq⟩
  ext s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    rcases lt_trichotomy s N with hsN | rfl | hsN
    · rw [hb'_lt s hsN, regularSingularSecondCoeff_eq_regularSingularCoeff_of_lt fs gs α₂ hsN]
    · simp [hb'N]
    · have hQ := indicialPoly_add_nat_ne_zero_of_ne hfact (by omega) hsN.ne'
      have hDs := hrec s
      have hnlt : ¬s < N := by omega
      simp only [hnlt, ↓reduceIte] at hDs
      rw [hc'_eq] at hDs
      apply mul_left_cancel₀ hQ
      rw [indicialPoly_mul_regularSingularSecondCoeff_of_gt hsN hQ]
      have hsum_eq : (∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) =
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) *
            regularSingularSecondCoeff fs gs α₂ N k :=
        sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk)]
      linear_combination hDs - hsum_eq

end TauCeti
