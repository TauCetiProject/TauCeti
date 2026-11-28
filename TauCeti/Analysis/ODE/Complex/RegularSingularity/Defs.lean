/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Range

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Indicial polynomial and formal coefficient recurrences at a regular singularity

For `w''(z) + f(z) w'(z) + g(z) w(z) = 0` around `z₀` with `(z - z₀) f(z) = ∑ f_s (z - z₀)^s` and
`(z - z₀)² g(z) = ∑ g_s (z - z₀)^s`, the leading exponents at `z₀` are the roots `α₁`, `α₂`
(`Re α₂ ≤ Re α₁`) of the **indicial polynomial**
`Q(α) = α(α - 1) + f₀ α + g₀ = (α - α₁)(α - α₂)` (`TauCeti.indicialPoly`).

This file defines `TauCeti.indicialPoly` and the canonical coefficient sequences (DLMF §2.7(ii)):
* `TauCeti.regularSingularCoeff`: `a_s` normalized by `a₀ = 1`, and for `s ≥ 1` given by
  `a_s = -Q(ρ + s)⁻¹ ∑_{k < s} ((ρ + k) f_{s - k} + g_{s - k}) a_k`, which solves
  `Q(ρ + s) a_s = -∑_{k < s} ((ρ + k) f_{s - k} + g_{s - k}) a_k` whenever `Q(ρ + s) ≠ 0`
  (DLMF 2.7.5), and evaluates to `0` at any resonant index `s ≥ 1` with `Q(ρ + s) = 0`.
* `TauCeti.regularSingularLogMultiplier`: the logarithmic multiplier `c` when `α₁ - α₂ = N ∈ ℕ`
  (`c = 1` for `N = 0`, cancelling the resonant obstruction at `s = N` for `N ≥ 1`).
* `TauCeti.regularSingularLogCoeff`: forced second-solution coefficients `b_s` for arbitrary
  primary coefficients `a` and multiplier `c` (`b_N = 0`, and `b₀ = 1` for `N ≥ 1`), with
  specialization `TauCeti.regularSingularSecondCoeff` for `a = regularSingularCoeff fs gs (α₂ + N)`
  and `c = regularSingularLogMultiplier fs gs α₂ N` (DLMF 2.7.6).

Convergence, solutionhood, and uniqueness are in
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Basic`; Wronskians and fundamental pairs are in
`TauCeti.Analysis.ODE.Complex.RegularSingularity.Wronskian`.

## References
* NIST DLMF §2.7(ii), 2.7.2–2.7.6, <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
-/

public noncomputable section

open Complex Finset

namespace TauCeti

/-! ### Indicial polynomial and roots -/

/-- The indicial polynomial `Q(α) = α(α - 1) + f₀ α + g₀` of `w'' + f w' + g w = 0` at a regular
singularity with leading Taylor coefficients `f₀` of `(z - z₀) f(z)` and `g₀` of
`(z - z₀)² g(z)`. -/
def indicialPoly {𝕜 : Type*} [Ring 𝕜] (f₀ g₀ α : 𝕜) : 𝕜 :=
  α * (α - 1) + f₀ * α + g₀

/-- Explicit formula for `indicialPoly`. -/
theorem indicialPoly_def {𝕜 : Type*} [Ring 𝕜] (f₀ g₀ α : 𝕜) :
    indicialPoly f₀ g₀ α = α * (α - 1) + f₀ * α + g₀ := (rfl)

@[simp]
theorem indicialPoly_zero {𝕜 : Type*} [Ring 𝕜] (f₀ g₀ : 𝕜) : indicialPoly f₀ g₀ 0 = g₀ := by
  simp [indicialPoly]

/-- Shifting the argument of `indicialPoly` expands quadratically in the shift. -/
theorem indicialPoly_add {𝕜 : Type*} [CommRing 𝕜] (f₀ g₀ α β : 𝕜) :
    indicialPoly f₀ g₀ (α + β) = indicialPoly f₀ g₀ α + β * (β + (2 * α + f₀ - 1)) := by
  simp only [indicialPoly]; ring

/-- Factorization of `indicialPoly f₀ g₀` into `(α - α₁)(α - α₂)` is equivalent to Vieta's
relations `α₁ + α₂ = 1 - f₀` and `α₁ α₂ = g₀`. -/
theorem forall_indicialPoly_eq_sub_mul_sub_iff {f₀ g₀ α₁ α₂ : ℂ} :
    (∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂)) ↔
      α₁ + α₂ = 1 - f₀ ∧ α₁ * α₂ = g₀ := by
  refine ⟨fun h => ?_, fun ⟨hsum, hprod⟩ α => by
    simp only [indicialPoly, ← hprod]; linear_combination α * hsum⟩
  have h0 := h 0; have h1 := h 1; simp only [indicialPoly] at h0 h1
  exact ⟨by linear_combination h1 - h0, by linear_combination -h0⟩

/-- Every complex indicial polynomial factors as `(α - α₁)(α - α₂)` with `Re α₂ ≤ Re α₁`. -/
theorem exists_indicialPoly_roots (f₀ g₀ : ℂ) :
    ∃ α₁ α₂ : ℂ, α₂.re ≤ α₁.re ∧ ∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂) := by
  obtain ⟨r₁, hr₁⟩ := exists_quadratic_eq_zero (one_ne_zero : (1 : ℂ) ≠ 0)
    (Complex.isSquare (discrim 1 (f₀ - 1) g₀))
  obtain ⟨r₂, -, hsum, hprod⟩ :=
    vieta_formula_quadratic (by linear_combination hr₁ : r₁ * r₁ - (1 - f₀) * r₁ + g₀ = 0)
  have hfact := forall_indicialPoly_eq_sub_mul_sub_iff.mpr ⟨hsum, hprod⟩
  rcases le_total r₂.re r₁.re with hle | hle
  · exact ⟨r₁, r₂, hle, hfact⟩
  · exact ⟨r₂, r₁, hle, fun α => by rw [mul_comm]; exact hfact α⟩

/-- For a factored indicial polynomial `Q(α) = (α - α₁)(α - α₂)`, the shifted value `Q(α₂ + s)`
is nonzero iff `s ≠ 0` and `α₁ - α₂ ≠ s`. -/
theorem indicialPoly_add_nat_ne_zero_iff {f₀ g₀ α₁ α₂ : ℂ}
    (hfact : ∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂)) {s : ℕ} :
    indicialPoly f₀ g₀ (α₂ + s) ≠ 0 ↔ s ≠ 0 ∧ α₁ - α₂ ≠ s := by
  rw [hfact, mul_ne_zero_iff, sub_ne_zero, add_sub_cancel_left, Nat.cast_ne_zero, and_comm]
  exact and_congr_right fun _ ↦
    ⟨fun h heq ↦ h (by linear_combination -heq), fun h heq ↦ h (by linear_combination -heq)⟩

/-- For the root `α₁` of `indicialPoly` with `Re α₂ ≤ Re α₁`, no positive integer shift `α₁ + s`
is a root of `indicialPoly`. -/
theorem indicialPoly_add_nat_ne_zero_of_re_le {f₀ g₀ α₁ α₂ : ℂ}
    (hfact : ∀ α, indicialPoly f₀ g₀ α = (α - α₁) * (α - α₂)) (hre : α₂.re ≤ α₁.re)
    {s : ℕ} (hs : 1 ≤ s) :
    indicialPoly f₀ g₀ (α₁ + s) ≠ 0 := by
  refine (indicialPoly_add_nat_ne_zero_iff (fun α ↦ by rw [hfact, mul_comm])).mpr
    ⟨by omega, fun h ↦ ?_⟩
  have hre0 := congrArg Complex.re h
  simp only [sub_re, natCast_re] at hre0
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- In the resonant case `α₁ = α₂ + N`, `indicialPoly f₀ g₀ (α₂ + s) ≠ 0` whenever `s ≠ 0` and
`s ≠ N`. -/
theorem indicialPoly_add_nat_ne_zero_of_ne {f₀ g₀ α₂ : ℂ} {N s : ℕ}
    (hfact : ∀ α, indicialPoly f₀ g₀ α = (α - (α₂ + N)) * (α - α₂))
    (hs0 : s ≠ 0) (hsN : s ≠ N) :
    indicialPoly f₀ g₀ (α₂ + s) ≠ 0 := by
  have hNs : (N : ℂ) ≠ s := by exact_mod_cast hsN.symm
  exact (indicialPoly_add_nat_ne_zero_iff hfact).mpr ⟨hs0, by simpa [add_sub_cancel_left] using hNs⟩

/-! ### Recursive coefficient sequences -/

/-- The normalized series coefficients `a_s` attached to an indicial exponent `ρ`, defined by
`a₀ = 1` and, for `s ≥ 1`,
`a_s = -Q(ρ + s)⁻¹ ∑_{k < s} ((ρ + k) f_{s - k} + g_{s - k}) a_k`. Whenever `s ≥ 1` and
`Q(ρ + s) ≠ 0`, this solves `Q(ρ + s) a_s = -∑_{k < s} ((ρ + k) f_{s - k} + g_{s - k}) a_k`
(DLMF 2.7.5); at any resonant index `s ≥ 1` with `Q(ρ + s) = 0`, Lean's totalized inverse sets
`a_s = 0` without enforcing the recurrence. -/
def regularSingularCoeff (fs gs : ℕ → ℂ) (ρ : ℂ) (s : ℕ) : ℂ :=
  if s = 0 then 1
  else -(indicialPoly (fs 0) (gs 0) (ρ + s))⁻¹ *
    ∑ k ∈ (range s).attach,
      ((ρ + k.val) * fs (s - k.val) + gs (s - k.val)) * regularSingularCoeff fs gs ρ k.val
termination_by s
decreasing_by exact mem_range.mp k.property

@[simp]
theorem regularSingularCoeff_zero (fs gs : ℕ → ℂ) (ρ : ℂ) :
    regularSingularCoeff fs gs ρ 0 = 1 := by
  rw [regularSingularCoeff]; simp

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

/-- At any positive resonant index `s ≠ 0` where `Q(ρ + s) = 0`, `regularSingularCoeff` evaluates
to `0` via Lean's totalized inverse. -/
@[simp]
theorem regularSingularCoeff_of_indicialPoly_eq_zero {fs gs : ℕ → ℂ} {ρ : ℂ} {s : ℕ}
    (hs : s ≠ 0) (hQ : indicialPoly (fs 0) (gs 0) (ρ + s) = 0) :
    regularSingularCoeff fs gs ρ s = 0 := by
  rw [regularSingularCoeff_of_ne_zero fs gs ρ hs, hQ, inv_zero, neg_zero, zero_mul]

/-- For `s ≥ 1` with `Q(ρ + s) ≠ 0`, `regularSingularCoeff` satisfies the linear indicial recursion
(DLMF 2.7.5). -/
theorem indicialPoly_mul_regularSingularCoeff {fs gs : ℕ → ℂ} {ρ : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hQ : indicialPoly (fs 0) (gs 0) (ρ + s) ≠ 0) :
    indicialPoly (fs 0) (gs 0) (ρ + s) * regularSingularCoeff fs gs ρ s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * regularSingularCoeff fs gs ρ k := by
  rw [regularSingularCoeff_of_ne_zero fs gs ρ (by omega)]; field_simp [hQ]

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
    · have hs1 := Nat.pos_of_ne_zero hs; have hQ := hres s hs1
      refine mul_left_cancel₀ hQ ?_
      rw [ha s hs1, indicialPoly_mul_regularSingularCoeff hs1 hQ]
      exact congrArg (- ·) <| sum_congr rfl fun k hk => by rw [ih k (mem_range.mp hk)]

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
    regularSingularLogMultiplier fs gs α₂ 0 = 1 := by simp [regularSingularLogMultiplier]

/-- Unfolding formula for `regularSingularLogMultiplier` when `N ≠ 0`. -/
theorem regularSingularLogMultiplier_of_ne_zero (fs gs : ℕ → ℂ) (α₂ : ℂ) {N : ℕ} (hN : N ≠ 0) :
    regularSingularLogMultiplier fs gs α₂ N =
      -(N : ℂ)⁻¹ * ∑ k ∈ range N,
        ((α₂ + k) * fs (N - k) + gs (N - k)) * regularSingularCoeff fs gs α₂ k := by
  simp [regularSingularLogMultiplier, hN]

/-- Cancellation identity `N * c = -∑_{k < N} ((α₂ + k) f_{N - k} + g_{N - k}) a_k` for `1 ≤ N`,
where `a_k = regularSingularCoeff fs gs α₂ k`. -/
theorem natCast_mul_regularSingularLogMultiplier (fs gs : ℕ → ℂ) (α₂ : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℂ) * regularSingularLogMultiplier fs gs α₂ N =
      -∑ k ∈ range N,
        ((α₂ + k) * fs (N - k) + gs (N - k)) * regularSingularCoeff fs gs α₂ k := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [regularSingularLogMultiplier_of_ne_zero fs gs α₂ (by omega)]; field_simp [hN0]

/-- Shifted logarithmic forcing coefficients for `α₁ = α₂ + N` and primary series coefficients `a`
(DLMF 2.7.6): `0` for `s < N`, and
`(2 (α₂ + s) + f₀ - 1) a_{s - N} + ∑_{k < s - N} f_{s - N - k} a_k` for `N ≤ s`. -/
def regularSingularLogForcing (fs a : ℕ → ℂ) (α₂ : ℂ) (N s : ℕ) : ℂ :=
  if s < N then 0
  else (2 * (α₂ + s) + fs 0 - 1) * a (s - N) + ∑ k ∈ range (s - N), fs (s - N - k) * a k

@[simp]
theorem regularSingularLogForcing_of_lt (fs a : ℕ → ℂ) (α₂ : ℂ) {N s : ℕ} (hs : s < N) :
    regularSingularLogForcing fs a α₂ N s = 0 := by
  simp [regularSingularLogForcing, hs]

/-- Unfolding formula for `regularSingularLogForcing` at or above the resonant index `N ≤ s`. -/
theorem regularSingularLogForcing_of_le (fs a : ℕ → ℂ) (α₂ : ℂ) {N s : ℕ} (hs : N ≤ s) :
    regularSingularLogForcing fs a α₂ N s =
      (2 * (α₂ + s) + fs 0 - 1) * a (s - N) + ∑ k ∈ range (s - N), fs (s - N - k) * a k := by
  simp [regularSingularLogForcing, not_lt_of_ge hs]

/-- Boundary value of `regularSingularLogForcing` at the resonant index `s = N`. -/
theorem regularSingularLogForcing_self (fs a : ℕ → ℂ) (α₂ : ℂ) (N : ℕ) :
    regularSingularLogForcing fs a α₂ N N = (2 * (α₂ + N) + fs 0 - 1) * a 0 := by
  simp [regularSingularLogForcing]

/-- At the resonant index `s = N` of a factored indicial polynomial `α₁ = α₂ + N`, the logarithmic
forcing equals `(N : ℂ) * a 0`. -/
theorem regularSingularLogForcing_self_eq {fs gs : ℕ → ℂ} {α₂ : ℂ} {N : ℕ}
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂)) (a : ℕ → ℂ) :
    regularSingularLogForcing fs a α₂ N N = (N : ℂ) * a 0 := by
  have h2N : 2 * (α₂ + (N : ℂ)) + fs 0 - 1 = N := by
    linear_combination (forall_indicialPoly_eq_sub_mul_sub_iff.mp hfact).1
  rw [regularSingularLogForcing_self, h2N]

/-- At the resonant index `s = N` of a factored indicial polynomial `α₁ = α₂ + N`, the canonical
logarithmic forcing equals `(N : ℂ)`. -/
@[simp]
theorem regularSingularLogForcing_regularSingularCoeff_self {fs gs : ℕ → ℂ} {α₂ : ℂ} {N : ℕ}
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂)) :
    regularSingularLogForcing fs (regularSingularCoeff fs gs (α₂ + N)) α₂ N N = (N : ℂ) := by
  rw [regularSingularLogForcing_self_eq hfact, regularSingularCoeff_zero, mul_one]

/-- Forced second-solution series coefficients `b_s` when `α₁ - α₂ = N ∈ ℕ` for general primary
coefficients `a` and logarithmic multiplier `c`, normalized by `b_N = 0` and `b₀ = 1` when
`N ≥ 1`. -/
def regularSingularLogCoeff (fs gs a : ℕ → ℂ) (α₂ c : ℂ) (N s : ℕ) : ℂ :=
  if s = N then 0
  else if s = 0 then 1
  else
    -(indicialPoly (fs 0) (gs 0) (α₂ + s))⁻¹ *
      ((∑ k ∈ (range s).attach,
          ((α₂ + k.val) * fs (s - k.val) + gs (s - k.val)) *
            regularSingularLogCoeff fs gs a α₂ c N k.val) +
        c * regularSingularLogForcing fs a α₂ N s)
termination_by s
decreasing_by exact mem_range.mp k.property

@[simp]
theorem regularSingularLogCoeff_self (fs gs a : ℕ → ℂ) (α₂ c : ℂ) (N : ℕ) :
    regularSingularLogCoeff fs gs a α₂ c N N = 0 := by
  rw [regularSingularLogCoeff]; simp

@[simp]
theorem regularSingularLogCoeff_zero_of_pos (fs gs a : ℕ → ℂ) (α₂ c : ℂ) {N : ℕ} (hN : 0 < N) :
    regularSingularLogCoeff fs gs a α₂ c N 0 = 1 := by
  rw [regularSingularLogCoeff]; simp [hN.ne]

/-- Below the resonant index `N`, `regularSingularLogCoeff` agrees with `regularSingularCoeff`. -/
theorem regularSingularLogCoeff_eq_regularSingularCoeff_of_lt (fs gs a : ℕ → ℂ) (α₂ c : ℂ)
    {N s : ℕ} (hs : s < N) :
    regularSingularLogCoeff fs gs a α₂ c N s = regularSingularCoeff fs gs α₂ s := by
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    rcases eq_or_ne s 0 with rfl | hs0
    · simp [regularSingularLogCoeff_zero_of_pos fs gs a α₂ c hs]
    · conv_lhs => rw [regularSingularLogCoeff]
      simp only [hs.ne, hs0, regularSingularLogForcing_of_lt _ _ _ hs, mul_zero, add_zero,
        ↓reduceIte]
      rw [Finset.sum_attach (range s) fun k =>
        ((α₂ + (k : ℂ)) * fs (s - k) + gs (s - k)) * regularSingularLogCoeff fs gs a α₂ c N k,
        regularSingularCoeff_of_ne_zero fs gs α₂ hs0]
      exact congrArg _ <| sum_congr rfl fun k hk => by
        rw [ih k (mem_range.mp hk) ((mem_range.mp hk).trans hs)]

/-- Recursion for `regularSingularLogCoeff` at indices `1 ≤ s < N` when `Q(α₂ + s) ≠ 0`. -/
theorem indicialPoly_mul_regularSingularLogCoeff_of_lt {fs gs a : ℕ → ℂ} {α₂ c : ℂ} {N s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < N) (hQ : indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    indicialPoly (fs 0) (gs 0) (α₂ + s) * regularSingularLogCoeff fs gs a α₂ c N s =
      -∑ k ∈ range s,
        ((α₂ + k) * fs (s - k) + gs (s - k)) * regularSingularLogCoeff fs gs a α₂ c N k := by
  rw [regularSingularLogCoeff_eq_regularSingularCoeff_of_lt fs gs a α₂ c hsN,
    indicialPoly_mul_regularSingularCoeff hs1 hQ]
  exact congrArg (- ·) <| sum_congr rfl fun k hk => by
    rw [regularSingularLogCoeff_eq_regularSingularCoeff_of_lt fs gs a α₂ c
      ((mem_range.mp hk).trans hsN)]

/-- Unfolding formula for `regularSingularLogCoeff` above the resonant index `N < s`. -/
theorem regularSingularLogCoeff_of_gt (fs gs a : ℕ → ℂ) (α₂ c : ℂ) {N s : ℕ} (hsN : N < s) :
    regularSingularLogCoeff fs gs a α₂ c N s =
      -(indicialPoly (fs 0) (gs 0) (α₂ + s))⁻¹ *
        ((∑ k ∈ range s,
            ((α₂ + k) * fs (s - k) + gs (s - k)) * regularSingularLogCoeff fs gs a α₂ c N k) +
          c * regularSingularLogForcing fs a α₂ N s) := by
  conv_lhs => rw [regularSingularLogCoeff]
  have hs0 : s ≠ 0 := by omega
  simp only [hsN.ne', hs0, ↓reduceIte]
  rw [Finset.sum_attach (range s) fun k =>
    ((α₂ + (k : ℂ)) * fs (s - k) + gs (s - k)) * regularSingularLogCoeff fs gs a α₂ c N k]

/-- Recursion for `regularSingularLogCoeff` above the resonant index `N < s` when
`Q(α₂ + s) ≠ 0`. -/
theorem indicialPoly_mul_regularSingularLogCoeff_of_gt {fs gs a : ℕ → ℂ} {α₂ c : ℂ} {N s : ℕ}
    (hsN : N < s) (hQ : indicialPoly (fs 0) (gs 0) (α₂ + s) ≠ 0) :
    indicialPoly (fs 0) (gs 0) (α₂ + s) * regularSingularLogCoeff fs gs a α₂ c N s =
      -(∑ k ∈ range s,
          ((α₂ + k) * fs (s - k) + gs (s - k)) * regularSingularLogCoeff fs gs a α₂ c N k) -
        c * regularSingularLogForcing fs a α₂ N s := by
  rw [regularSingularLogCoeff_of_gt fs gs a α₂ c hsN]; field_simp [hQ]; ring

/-- Whenever `1 ≤ N → c * a 0 = regularSingularLogMultiplier fs gs α₂ N`,
`regularSingularLogCoeff fs gs a α₂ c N` satisfies the unified resonant indicial recursion for
every `s : ℕ`. -/
theorem regularSingularLogCoeff_rec {fs gs a : ℕ → ℂ} {α₂ c : ℂ} {N : ℕ}
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂))
    (hc : 1 ≤ N → c * a 0 = regularSingularLogMultiplier fs gs α₂ N) (s : ℕ) :
    (indicialPoly (fs 0) (gs 0) (α₂ + s) * regularSingularLogCoeff fs gs a α₂ c N s +
      ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) *
        regularSingularLogCoeff fs gs a α₂ c N k) +
    c * regularSingularLogForcing fs a α₂ N s = 0 := by
  rcases lt_trichotomy s N with hsN | rfl | hsN
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp [regularSingularLogForcing_of_lt _ _ _ hsN, hfact]
    · have h := indicialPoly_mul_regularSingularLogCoeff_of_lt (a := a) (c := c)
        (Nat.pos_of_ne_zero hs0) hsN (indicialPoly_add_nat_ne_zero_of_ne hfact hs0 hsN.ne)
      rw [regularSingularLogForcing_of_lt _ _ _ hsN, mul_zero, add_zero]
      linear_combination h
  · rw [regularSingularLogCoeff_self, mul_zero, zero_add,
      regularSingularLogForcing_self_eq hfact]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · have hsum_eq : (∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) *
            regularSingularLogCoeff fs gs a α₂ c s k) =
          ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) *
            regularSingularCoeff fs gs α₂ k := sum_congr rfl fun k hk => by
        rw [regularSingularLogCoeff_eq_regularSingularCoeff_of_lt fs gs a α₂ c (mem_range.mp hk)]
      have hca : c * ((s : ℂ) * a 0) = (s : ℂ) * regularSingularLogMultiplier fs gs α₂ s := by
        linear_combination (s : ℂ) * hc (Nat.pos_of_ne_zero hs0)
      rw [hsum_eq, hca]
      linear_combination natCast_mul_regularSingularLogMultiplier fs gs α₂ (Nat.pos_of_ne_zero hs0)
  · have h := indicialPoly_mul_regularSingularLogCoeff_of_gt (a := a) (c := c) hsN
      (indicialPoly_add_nat_ne_zero_of_ne hfact (by omega) hsN.ne')
    linear_combination h

/-- Any pair `(b', c')` satisfying `b' N = 0`, `(N = 0 → c' = c)`, `(1 ≤ N → b' 0 = 1)`, and the
resonant indicial recursion with primary coefficients `a` (`a 0 ≠ 0`) coincides with
`(regularSingularLogCoeff fs gs a α₂ c N, c)` provided
`1 ≤ N → c * a 0 = regularSingularLogMultiplier fs gs α₂ N`. -/
theorem eq_regularSingularLogCoeff_of_rec {fs gs a b' : ℕ → ℂ} {α₂ c c' : ℂ} {N : ℕ}
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂))
    (ha₀ : a 0 ≠ 0)
    (hc : 1 ≤ N → c * a 0 = regularSingularLogMultiplier fs gs α₂ N)
    (hb'N : b' N = 0)
    (hc'0 : N = 0 → c' = c)
    (hb'0 : 1 ≤ N → b' 0 = 1)
    (hrec : ∀ s : ℕ,
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b' s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b' k) +
      c' * regularSingularLogForcing fs a α₂ N s = 0) :
    b' = regularSingularLogCoeff fs gs a α₂ c N ∧ c' = c := by
  set b := regularSingularLogCoeff fs gs a α₂ c N
  have hsum_congr : ∀ m, (∀ k < m, b' k = b k) →
      (∑ k ∈ range m, ((α₂ + k) * fs (m - k) + gs (m - k)) * b' k) =
        ∑ k ∈ range m, ((α₂ + k) * fs (m - k) + gs (m - k)) * b k := fun m h =>
    sum_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]
  have hstep : ∀ s, s ≠ 0 → s ≠ N → (∀ k < s, b' k = b k) →
      c' * regularSingularLogForcing fs a α₂ N s =
        c * regularSingularLogForcing fs a α₂ N s →
      b' s = b s := by
    intro s hs0 hsN hk_eq hF
    have hdiff := sub_eq_zero.mpr ((hrec s).trans (regularSingularLogCoeff_rec hfact hc s).symm)
    rw [hsum_congr s hk_eq, hF] at hdiff
    exact mul_left_cancel₀ (indicialPoly_add_nat_ne_zero_of_ne hfact hs0 hsN)
      (by linear_combination hdiff)
  have hb'_lt : ∀ s < N, b' s = b s := by
    intro s hs; induction s using Nat.strong_induction_on with | ind s ih =>
      rcases eq_or_ne s 0 with rfl | hs0
      · simp [b, hb'0 hs, hs]
      · refine hstep s hs0 hs.ne (fun k hk => ih k hk (hk.trans hs)) ?_
        simp [regularSingularLogForcing_of_lt _ _ _ hs]
  have hc'_eq : c' = c := by
    rcases eq_or_ne N 0 with rfl | hN0
    · exact hc'0 rfl
    · have hN_eq := (hrec N).trans (regularSingularLogCoeff_rec hfact hc N).symm
      rw [hb'N, regularSingularLogCoeff_self, mul_zero, zero_add,
        hsum_congr N hb'_lt, regularSingularLogForcing_self_eq hfact] at hN_eq
      exact mul_right_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr hN0) ha₀)
        (by linear_combination hN_eq)
  refine ⟨?_, hc'_eq⟩
  ext s; induction s using Nat.strong_induction_on with | ind s ih =>
    rcases lt_trichotomy s N with hsN | rfl | hsN
    · exact hb'_lt s hsN
    · simp [b, hb'N]
    · exact hstep s (by omega) hsN.ne' ih (by rw [hc'_eq])

/-- Equivalence between the unified resonant indicial recursion for `(b, c)` at all `s : ℕ`
and the split form below and from the resonant index `N` (DLMF 2.7.6). -/
theorem forall_regularSingularLogForcing_rec_iff {fs gs a b : ℕ → ℂ} {α₁ α₂ c : ℂ} {N : ℕ}
    (hN : α₁ = α₂ + N) :
    (∀ s : ℕ,
      (indicialPoly (fs 0) (gs 0) (α₂ + s) * b s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) +
      c * regularSingularLogForcing fs a α₂ N s = 0) ↔
      (∀ s < N, indicialPoly (fs 0) (gs 0) (α₂ + s) * b s =
        -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) ∧
      ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (α₁ + s) * b (s + N) =
        -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * b k -
          c * regularSingularLogForcing fs a α₂ N (s + N) := by
  subst hN
  refine ⟨fun h => ⟨fun s hs => ?_, fun s => ?_⟩, fun ⟨hlt, hge⟩ s => ?_⟩
  · have hs' := h s
    rw [regularSingularLogForcing_of_lt _ _ _ hs, mul_zero, add_zero] at hs'
    linear_combination hs'
  · have hs' := h (s + N)
    rw [show α₂ + ((s + N : ℕ) : ℂ) = (α₂ + N) + s by push_cast; ring] at hs'
    linear_combination hs'
  · rcases lt_or_ge s N with hs | hs
    · rw [regularSingularLogForcing_of_lt _ _ _ hs, mul_zero, add_zero]
      linear_combination hlt s hs
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + N := ⟨s - N, by omega⟩
      have hj := hge j
      rw [show (α₂ + (N : ℂ)) + (j : ℂ) = α₂ + ((j + N : ℕ) : ℂ) by push_cast; ring] at hj
      linear_combination hj

/-- The series coefficients `b_s` of the second solution when `α₁ - α₂ = N ∈ ℕ` (DLMF 2.7.6),
normalized by `b_N = 0` (omitting the resonant term) and `b₀ = 1` when `N ≥ 1`. -/
def regularSingularSecondCoeff (fs gs : ℕ → ℂ) (α₂ : ℂ) (N s : ℕ) : ℂ :=
  regularSingularLogCoeff fs gs (regularSingularCoeff fs gs (α₂ + N)) α₂
    (regularSingularLogMultiplier fs gs α₂ N) N s

@[simp]
theorem regularSingularSecondCoeff_self (fs gs : ℕ → ℂ) (α₂ : ℂ) (N : ℕ) :
    regularSingularSecondCoeff fs gs α₂ N N = 0 :=
  regularSingularLogCoeff_self fs gs _ α₂ _ N

@[simp]
theorem regularSingularSecondCoeff_zero_of_pos (fs gs : ℕ → ℂ) (α₂ : ℂ) {N : ℕ} (hN : 0 < N) :
    regularSingularSecondCoeff fs gs α₂ N 0 = 1 :=
  regularSingularLogCoeff_zero_of_pos fs gs _ α₂ _ hN

/-- The canonical resonant pair `(regularSingularSecondCoeff, regularSingularLogMultiplier)`
satisfies the unified resonant indicial recursion for every `s : ℕ`. -/
theorem regularSingularSecondCoeff_rec {fs gs : ℕ → ℂ} {α₂ : ℂ} {N : ℕ}
    (hfact : ∀ α, indicialPoly (fs 0) (gs 0) α = (α - (α₂ + N)) * (α - α₂)) (s : ℕ) :
    (indicialPoly (fs 0) (gs 0) (α₂ + s) * regularSingularSecondCoeff fs gs α₂ N s +
      ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) *
        regularSingularSecondCoeff fs gs α₂ N k) +
    regularSingularLogMultiplier fs gs α₂ N *
      regularSingularLogForcing fs (regularSingularCoeff fs gs (α₂ + N)) α₂ N s = 0 :=
  regularSingularLogCoeff_rec hfact (fun _ => by simp) s

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
      c' * regularSingularLogForcing fs (regularSingularCoeff fs gs (α₂ + N)) α₂ N s = 0) :
    b' = regularSingularSecondCoeff fs gs α₂ N ∧
      c' = regularSingularLogMultiplier fs gs α₂ N :=
  eq_regularSingularLogCoeff_of_rec hfact (by simp) (fun _ => by simp) hb'N
    (fun hN0 => (hc'0 hN0).trans (by simp [hN0])) hb'0 hrec

end TauCeti
