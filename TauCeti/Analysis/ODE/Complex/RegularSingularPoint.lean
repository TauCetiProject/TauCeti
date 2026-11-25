/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Data.Nat.Choose.Sum

/-!
# Frobenius series solutions at a regular singularity

Consider the equation `w'' + f(z) w' + g(z) w = 0` near a point `z₀` at which `f` has at most a
simple pole and `g` at most a double pole, so that on a punctured disc `0 < |z - z₀| < r`

* `(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and
* `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ`,

with both series convergent there. Its indicial polynomial is `Q(α) = α (α - 1) + f₀ α + g₀`.
Let `ρ` be a root of `Q`, and let

`Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`

(DLMF 2.7.5). Then the series `∑ aₛ (z - z₀)ˢ` converges on the whole disc `|z - z₀| < r`
(`TauCeti.le_radius_ofScalars_of_regularSingular`), and the Frobenius series
`w(z) = (z - z₀)^ρ ∑ aₛ (z - z₀)ˢ`, with the principal power, is holomorphic and solves the equation
on the slit punctured disc `{z | z - z₀ ∈ slitPlane, |z - z₀| < r}` (DLMF 2.7.4;
`TauCeti.regularSingular_solution`).

The recursion determines `aₛ` from `a₀` whenever no `ρ + s` with `s ≥ 1` is a root of `Q`. This
holds for the root of larger real part, and for the other root when the two roots do not differ
by an integer. The normalization `a₀ = 1` is customary; the statements hold for every `a₀`. For
example, Bessel's equation, with `f(z) = 1/z` and `g(z) = 1 - ν²/z²` at `z₀ = 0`, has the
indicial roots `±ν`, and when `2ν` is not a negative integer the solution at `ρ = ν` is a constant
multiple of the Bessel function `J_ν`.

When the roots differ by an integer, `α₁ = α₂ + N` with `N ∈ ℕ`, the second solution has the
form (DLMF 2.7.6)

`w(z) = (z - z₀)^{α₂} ∑ bₛ (z - z₀)ˢ + c w₁(z) log (z - z₀)`,

where `w₁` is the Frobenius solution at `α₁`. Substituting it into the equation gives the
recursion for the `bₛ` at `α₂`, forced from the index `N` on by `c dₛ`, where
`dₛ = (2 (α₁ + s) - 1) aₛ + ∑_{k ≤ s} f_{s-k} aₖ` are the coefficients of the terms of the equation
applied to `c w₁ log (z - z₀)` that do not involve the logarithm. Every solution of this recursion
gives a convergent series and a solution of the equation (`TauCeti.regularSingular_log_solution`),
and with DLMF's normalization (`c = 1` and `b₀ = 0` when `N = 0`, `b₀ = 1` and `b_N = 0` when
`N ≥ 1`) the recursion has exactly one solution
(`TauCeti.existsUnique_regularSingular_log_coeff`).

## Implementation notes

Convergence is proved by a majorant argument, for the recursion with a forcing term `eₛ`.
Since `Q(ρ + s) = s² + (2ρ - 1 + f₀) s + Q(ρ)`, `|Q(ρ + s)| ≥ s² / 2` for all large `s`; no
condition on `ρ` is needed. For `t` below the radii of convergence of the series of the `fₛ`,
`gₛ` and `eₛ`, `|aₛ| tˢ` is then bounded by a constant times the binomial coefficient
`C(s + m, m)` for a fixed `m`. The equation is verified on coefficients: in terms of the Euler
operator `ζ d/dζ`, `(z - z₀)^{2 - ρ}` times the left-hand side is the power series whose
coefficient of index `s` is `Q(ρ + s) aₛ + ∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ`, a Cauchy
product of absolutely convergent series. For the logarithmic solution,
`(u log)'' + f (u log)' + g u log = (u'' + f u' + g u) log + 2 u' / ζ + (f - 1 / ζ) u`, and for
`u = w₁` the last two terms are `ζ^{α₁ - 2} ∑ dₛ ζˢ`.

## References

* NIST Digital Library of Mathematical Functions, §2.7(i), equations (2.7.2)–(2.7.6),
  <https://dlmf.nist.gov/2.7.i>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 4, §§3–4.
-/

public section

open Complex Filter Finset FormalMultilinearSeries Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Convergence of the Frobenius series -/

/-- The indicial polynomial at `ρ + s`, expanded in powers of `s`. -/
private theorem indicial_add_eq (ρ f₀ g₀ s : ℂ) :
    (ρ + s) * (ρ + s - 1) + f₀ * (ρ + s) + g₀ =
      s ^ 2 + (2 * ρ - 1 + f₀) * s + (ρ * (ρ - 1) + f₀ * ρ + g₀) := by
  ring

/-- A monic quadratic `s² + β s + γ` has norm at least `s² / 2` once `s ≥ 2 (‖β‖ + ‖γ‖) + 1`. -/
private theorem sq_div_two_le_norm {β γ : ℂ} {s : ℕ} (hs : 2 * (‖β‖ + ‖γ‖) + 1 ≤ s) :
    (s : ℝ) ^ 2 / 2 ≤ ‖(s : ℂ) ^ 2 + β * s + γ‖ := by
  have hlin : ‖β * s + γ‖ ≤ ‖β‖ * s + ‖γ‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast]
  have hsub := norm_sub_norm_le ((s : ℂ) ^ 2) (-(β * s + γ))
  rw [norm_neg, sub_neg_eq_add, ← add_assoc, norm_pow, Complex.norm_natCast] at hsub
  have hs1 : (1 : ℝ) ≤ s := by linarith [norm_nonneg β, norm_nonneg γ]
  nlinarith [norm_nonneg β, norm_nonneg γ]

/-- A term of the recursion at index `n + 1`, bounded through the bound `|aₖ| tᵏ ≤ Bₖ` on the
earlier coefficients, when `fₛ tˢ` and `gₛ tˢ` are bounded by `M`. -/
private theorem norm_recursion_term_mul_pow_le {ρ : ℂ} {fs gs a : ℕ → ℂ} {t M B : ℝ} {n k : ℕ}
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hfs : ∀ n, ‖fs n‖ * t ^ n ≤ M) (hgs : ∀ n, ‖gs n‖ * t ^ n ≤ M)
    (hkn : k ≤ n) (hak : ‖a k‖ * t ^ k ≤ B) :
    ‖((ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)) * a k‖ * t ^ (n + 1) ≤
      (‖ρ‖ + 1) * (n + 1) * M * B := by
  have hB : 0 ≤ B := (by positivity : 0 ≤ ‖a k‖ * t ^ k).trans hak
  have hρk : ‖ρ + k‖ + 1 ≤ (‖ρ‖ + 1) * (n + 1) := by
    have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have := norm_add_le ρ (k : ℂ)
    rw [Complex.norm_natCast] at this
    nlinarith [norm_nonneg ρ]
  rw [← pow_sub_mul_pow t (by omega : k ≤ n + 1), norm_mul]
  calc ‖(ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)‖ * ‖a k‖ * (t ^ (n + 1 - k) * t ^ k)
      ≤ (‖ρ + k‖ * ‖fs (n + 1 - k)‖ + ‖gs (n + 1 - k)‖) * ‖a k‖ *
          (t ^ (n + 1 - k) * t ^ k) := by
        gcongr
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ = (‖ρ + k‖ * (‖fs (n + 1 - k)‖ * t ^ (n + 1 - k)) +
          ‖gs (n + 1 - k)‖ * t ^ (n + 1 - k)) * (‖a k‖ * t ^ k) := by ring
    _ ≤ (‖ρ + k‖ * M + M) * B :=
        mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left (hfs _) (norm_nonneg _)) (hgs _))
          hak (by positivity) (add_nonneg (mul_nonneg (norm_nonneg _) hM) hM)
    _ ≤ (‖ρ‖ + 1) * (n + 1) * M * B := by
        gcongr
        nlinarith

/-- The majorant bound. Suppose that from an index `s₀ ≥ 1` on, `qₛ aₛ + ∑_{k < s} ((ρ + k)
f_{s-k} + g_{s-k}) aₖ + eₛ = 0` with `|qₛ| ≥ s² / 2`, and that `fₛ tˢ` and `gₛ tˢ` are bounded by
`M` and `eₛ tˢ` by `Mₑ`. Then `|aₛ| tˢ ≤ B C(s + m, m)` for all `s`, as soon as
`2 (|ρ| + 1) M ≤ m`, `2 Mₑ ≤ B` and `B` bounds `|aₖ| tᵏ` for `k < s₀`. -/
private theorem norm_mul_pow_le_mul_choose {ρ : ℂ} {q fs gs es a : ℕ → ℂ} {t M Me B : ℝ}
    {m s₀ : ℕ} (ht : 0 ≤ t) (hs₀ : 1 ≤ s₀) (hq : ∀ s, s₀ ≤ s → (s : ℝ) ^ 2 / 2 ≤ ‖q s‖)
    (hfs : ∀ n, ‖fs n‖ * t ^ n ≤ M) (hgs : ∀ n, ‖gs n‖ * t ^ n ≤ M)
    (hes : ∀ n, ‖es n‖ * t ^ n ≤ Me) (hm : 2 * ((‖ρ‖ + 1) * M) ≤ m) (hMe : 2 * Me ≤ B)
    (hB : ∀ k < s₀, ‖a k‖ * t ^ k ≤ B)
    (ha : ∀ s, s₀ ≤ s →
      q s * a s + ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k + es s = 0)
    (n : ℕ) :
    ‖a n‖ * t ^ n ≤ B * (n + m).choose m := by
  have hM : 0 ≤ M := (by positivity : 0 ≤ ‖fs 0‖ * t ^ 0).trans (hfs 0)
  have hMe0 : 0 ≤ Me := (by positivity : 0 ≤ ‖es 0‖ * t ^ 0).trans (hes 0)
  have hB0 : 0 ≤ B := by linarith
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n s₀ with hn | hn
    · exact (hB n hn).trans
        (le_mul_of_one_le_right hB0 (by exact_mod_cast Nat.choose_pos (by omega)))
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hbinom : (1 : ℝ) + m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ) ≤
        (n + 1) * ((n + 1 + m).choose m : ℝ) := mod_cast Nat.one_add_mul_sum_range_add_choose_le n m
    have hstep : ‖q (n + 1)‖ * ‖a (n + 1)‖ ≤ ∑ k ∈ range (n + 1),
        ‖((ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)) * a k‖ + ‖es (n + 1)‖ := by
      rw [← norm_mul, show q (n + 1) * a (n + 1) = -(∑ k ∈ range (n + 1),
        ((ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)) * a k + es (n + 1)) by
          linear_combination ha (n + 1) hn, norm_neg]
      exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
    -- bound `(n + 1)² |a_{n+1}| t^{n+1} / 2` through the recursion and the hockey-stick identity
    have hkey : (n + 1) * ((n + 1) * (‖a (n + 1)‖ * t ^ (n + 1))) ≤
        (n + 1) * ((n + 1) * (B * ((n + 1 + m).choose m : ℝ))) := by
      calc (n + 1 : ℝ) * ((n + 1) * (‖a (n + 1)‖ * t ^ (n + 1)))
          = 2 * (((n + 1 : ℕ) : ℝ) ^ 2 / 2 * ‖a (n + 1)‖) * t ^ (n + 1) := by
            push_cast
            ring
        _ ≤ 2 * (∑ k ∈ range (n + 1), ‖((ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)) * a k‖ +
              ‖es (n + 1)‖) * t ^ (n + 1) := by
            gcongr
            exact (mul_le_mul_of_nonneg_right (hq (n + 1) hn) (norm_nonneg _)).trans hstep
        _ = 2 * (∑ k ∈ range (n + 1), ‖((ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)) * a k‖ *
              t ^ (n + 1) + ‖es (n + 1)‖ * t ^ (n + 1)) := by
            rw [← sum_mul]
            ring
        _ ≤ 2 * (∑ k ∈ range (n + 1), (‖ρ‖ + 1) * (n + 1) * M * (B * ((k + m).choose m : ℝ)) +
              Me) := by
            gcongr 2 * (?_ + ?_)
            · exact sum_le_sum fun k hk ↦ norm_recursion_term_mul_pow_le ht hM hfs hgs
                (mem_range_succ_iff.1 hk) (ih k (mem_range.1 hk))
            · exact hes (n + 1)
        _ = (n + 1) * B * (2 * ((‖ρ‖ + 1) * M) * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) +
              2 * Me := by
            rw [← mul_sum, ← mul_sum]
            ring
        _ ≤ (n + 1) * B * (m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) + (n + 1) * B := by
            have hsum0 : 0 ≤ ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ) := by positivity
            refine add_le_add (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hm hsum0) (by positivity)) ?_
            nlinarith
        _ = (n + 1) * B * (1 + m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) := by ring
        _ ≤ (n + 1) * B * ((n + 1) * ((n + 1 + m).choose m : ℝ)) := by gcongr
        _ = (n + 1) * ((n + 1) * (B * ((n + 1 + m).choose m : ℝ))) := by ring
    simpa [add_right_comm n 1 m] using
      le_of_mul_le_mul_left (le_of_mul_le_mul_left hkey (by positivity)) (by positivity)

/-- **Convergence of the Frobenius series.** Let `Q(α) = α (α - 1) + f₀ α + g₀` be the indicial
polynomial, and let the coefficients `aₛ` satisfy, from some index `s₀` on, the recursion
`Q(ρ + s) aₛ + ∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ + eₛ = 0` (DLMF 2.7.5, with a forcing
term `eₛ`). Then the radius of convergence of `∑ aₛ zˢ` is at least every `r` that bounds from
below the radii of convergence of `∑ fₛ zˢ`, `∑ gₛ zˢ` and `∑ eₛ zˢ`.

No condition on `ρ` is needed: since `Q(ρ + s)` grows like `s²`, it vanishes for only finitely
many `s`, and finitely many coefficients do not affect convergence. -/
theorem le_radius_ofScalars_of_regularSingular {ρ : ℂ} {fs gs es a : ℕ → ℂ} {r : ℝ≥0∞}
    {s₀ : ℕ} (hfs : r ≤ (ofScalars ℂ fs).radius) (hgs : r ≤ (ofScalars ℂ gs).radius)
    (hes : r ≤ (ofScalars ℂ es).radius)
    (ha : ∀ s : ℕ, s₀ ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k + es s = 0) :
    r ≤ (ofScalars ℂ a).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_
  rcases eq_or_ne R 0 with rfl | hR0
  · simp
  obtain ⟨t, hRt_coe, htr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hRr
  have hRt : (R : ℝ) < t := ENNReal.coe_lt_coe.mp hRt_coe
  have hR : (0 : ℝ) < R := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hR0)
  have ht : (0 : ℝ) < t := hR.trans hRt
  obtain ⟨Mf, -, hMf⟩ := (ofScalars ℂ fs).norm_mul_pow_le_of_lt_radius (htr.trans_le hfs)
  obtain ⟨Mg, -, hMg⟩ := (ofScalars ℂ gs).norm_mul_pow_le_of_lt_radius (htr.trans_le hgs)
  obtain ⟨Me, -, hMe⟩ := (ofScalars ℂ es).norm_mul_pow_le_of_lt_radius (htr.trans_le hes)
  simp only [ofScalars_norm] at hMf hMg hMe
  -- from `s₁` on, `|Q(ρ + s)| ≥ s² / 2`
  set β : ℂ := 2 * ρ - 1 + fs 0
  set γ : ℂ := ρ * (ρ - 1) + fs 0 * ρ + gs 0
  obtain ⟨s₁, hs₁⟩ := exists_nat_ge (2 * (‖β‖ + ‖γ‖) + 1)
  set s₂ := max s₀ (max s₁ 1)
  have hq (s : ℕ) (hs : s₂ ≤ s) :
      (s : ℝ) ^ 2 / 2 ≤ ‖(ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0‖ := by
    have hs' : s₁ ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
    rw [indicial_add_eq]
    exact sq_div_two_le_norm (hs₁.trans (by exact_mod_cast hs'))
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * ((‖ρ‖ + 1) * max Mf Mg))
  set B : ℝ := 2 * Me + ∑ k ∈ range s₂, ‖a k‖ * t ^ k
  have hB (k : ℕ) (hk : k < s₂) : ‖a k‖ * t ^ k ≤ B := by
    have hMe0 : 0 ≤ Me := (by positivity : 0 ≤ ‖es 0‖ * (t : ℝ) ^ 0).trans (hMe 0)
    have := single_le_sum (f := fun k ↦ ‖a k‖ * (t : ℝ) ^ k) (fun _ _ ↦ by positivity)
      (mem_range.2 hk)
    linarith
  have hbound := norm_mul_pow_le_mul_choose (a := a) (q := fun s ↦
      (ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) t.property
    (le_max_of_le_right (le_max_right _ _)) hq
    (fun n ↦ (hMf n).trans (le_max_left _ _)) (fun n ↦ (hMg n).trans (le_max_right _ _)) hMe hm
    (by simp only [B]; linarith [sum_nonneg fun k (_ : k ∈ range s₂) ↦
      (by positivity : 0 ≤ ‖a k‖ * (t : ℝ) ^ k)]) hB
    (fun s hs ↦ ha s ((le_max_left _ _).trans hs))
  -- compare with `B ∑ C(n + m, m) qⁿ` for `q = R / t < 1`
  set q : ℝ := R / t
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_lt_one ht).mpr hRt
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
    ((summable_choose_mul_geometric_of_norm_lt_one m hq1).mul_left B)
  rw [ofScalars_norm, show (R : ℝ) = t * q from (mul_div_cancel₀ _ ht.ne').symm, mul_pow,
    ← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)

/-! ### The Frobenius series solves the equation -/

/-- The coefficient of `ζⁿ` in the Euler-operator form of the equation, with the forcing term
`eₙ ζⁿ`, vanishes by the recursion. -/
private theorem euler_form_coeff_eq_zero {ρ ζ : ℂ} {fs gs es a : ℕ → ℂ}
    (ha : ∀ s : ℕ, ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k + es s = 0) (n : ℕ) :
    ρ * (ρ - 1) * (a n * ζ ^ n) + 2 * ρ * (n * a n * ζ ^ n) + n * (n - 1) * a n * ζ ^ n +
        ∑ k ∈ range (n + 1), (ρ + k) * a k * ζ ^ k * (fs (n - k) * ζ ^ (n - k)) +
      ∑ k ∈ range (n + 1), a k * ζ ^ k * (gs (n - k) * ζ ^ (n - k)) + es n * ζ ^ n = 0 := by
  have hsum (u v : ℕ → ℂ) : ∑ k ∈ range (n + 1), u k * ζ ^ k * (v (n - k) * ζ ^ (n - k)) =
      ζ ^ n * ∑ k ∈ range (n + 1), u k * v (n - k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [← pow_mul_pow_sub ζ (mem_range_succ_iff.mp hk)]
    ring
  have hrec := ha n
  have hsplit : ∑ k ∈ range n, ((ρ + k) * fs (n - k) + gs (n - k)) * a k =
      ∑ k ∈ range n, (ρ + k) * a k * fs (n - k) + ∑ k ∈ range n, a k * gs (n - k) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  rw [hsplit] at hrec
  rw [hsum (fun k ↦ (ρ + k) * a k), hsum a, sum_range_succ, sum_range_succ, Nat.sub_self]
  linear_combination ζ ^ n * hrec

/-- The Euler-operator form of the equation, at a point `ζ` of the disc: with `S = ∑ aₛ ζˢ`,
`F = ∑ fₛ ζˢ`, `G = ∑ gₛ ζˢ` and `E = ∑ eₛ ζˢ`, the expression below, which is `ζ^{2 - ρ}` times
the left-hand side of the equation applied to `ζ^ρ S` plus `E`, vanishes. -/
private theorem euler_form_eq_zero {ρ ζ F G E : ℂ} {fs gs es a : ℕ → ℂ} {S : ℂ → ℂ} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius) (hζg : ‖ζ‖ₑ < (ofScalars ℂ gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) (hG : HasSum (fun s ↦ gs s * ζ ^ s) G)
    (hE : HasSum (fun s ↦ es s * ζ ^ s) E)
    (ha : ∀ s : ℕ, ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k + es s = 0) :
    ρ * (ρ - 1) * S ζ + 2 * ρ * (ζ * deriv S ζ) + ζ ^ 2 * deriv (deriv S) ζ +
      F * (ρ * S ζ + ζ * deriv S ζ) + G * S ζ + E = 0 := by
  -- the series of `S`, of `ζ S'` and of `ζ² S''`
  have h0 : HasSum (fun n ↦ a n * ζ ^ n) (S ζ) := by
    simpa [ofScalars_apply_eq, mul_comm] using hS.hasSum (mem_eball_zero_iff.mpr hζ)
  have h1 := hS.hasSum_mul_deriv_ofScalars hζ
  have h2 := hS.hasSum_sq_mul_deriv_deriv_ofScalars hζ
  -- absolute convergence of the factors of the two Cauchy products
  have hA := summable_norm_mul_pow_of_lt_radius a (hζ.trans_le hS.r_le)
  have hP : Summable fun n : ℕ ↦ ‖(ρ + n) * a n * ζ ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((hA.mul_left ‖ρ‖).add (summable_norm_natCast_mul_ofScalars a
        (hζ.trans_le hS.r_le)))
    rw [add_mul, add_mul]
    refine (norm_add_le _ _).trans_eq ?_
    rw [mul_assoc ρ, norm_mul]
  have hfN := summable_norm_mul_pow_of_lt_radius fs hζf
  have hgN := summable_norm_mul_pow_of_lt_radius gs hζg
  have hPsum : HasSum (fun n : ℕ ↦ (ρ + n) * a n * ζ ^ n) (ρ * S ζ + ζ * deriv S ζ) := by
    convert (h0.mul_left ρ).add h1 using 1
    ext n
    ring
  have hC1 := hasSum_sum_range_mul_of_summable_norm hP hfN
  have hC2 := hasSum_sum_range_mul_of_summable_norm hA hgN
  rw [hPsum.tsum_eq, hF.tsum_eq] at hC1
  rw [h0.tsum_eq, hG.tsum_eq] at hC2
  -- the combined series has all coefficients zero
  have htotal := (((((h0.mul_left (ρ * (ρ - 1))).add (h1.mul_left (2 * ρ))).add h2).add
    hC1).add hC2).add hE
  rw [mul_comm (ρ * S ζ + ζ * deriv S ζ) F, mul_comm (S ζ) G] at htotal
  exact htotal.unique ((hasSum_zero).congr_fun fun n ↦ euler_form_coeff_eq_zero (ζ := ζ) ha n)

/-- The derivative of `y ↦ y ^ ρ * S y` on the slit disc of convergence of `S`. -/
private theorem hasDerivAt_cpow_mul {ρ y : ℂ} {S : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {R : ℝ≥0∞} (hS : HasFPowerSeriesOnBall S p 0 R) (hy : y ∈ slitPlane) (hyR : ‖y‖ₑ < R) :
    HasDerivAt (fun y ↦ y ^ ρ * S y) (ρ * y ^ (ρ - 1) * S y + y ^ ρ * deriv S y) y := by
  have hSd := (hS.differentiableOn.differentiableAt
    (Metric.isOpen_eball.mem_nhds (mem_eball_zero_iff.mpr hyR))).hasDerivAt
  simpa using ((hasDerivAt_id' y).cpow_const (c := ρ) hy).fun_mul hSd

/-- The equation at a point `ζ` of the slit disc, for the Frobenius series about the origin with a
forcing term: `w(ζ) = ζ ^ ρ S(ζ)` with `S = ∑ aₛ ζˢ`, where `ζ fζ = ∑ fₛ ζˢ`, `ζ² gζ = ∑ gₛ ζˢ`
and `E = ∑ eₛ ζˢ`, satisfies `w'' + fζ w' + gζ w + ζ^{ρ - 2} E = 0`. -/
private theorem deriv_deriv_cpow_mul_add_eq_zero {ρ ζ fζ gζ E : ℂ} {fs gs es a : ℕ → ℂ}
    {S : ℂ → ℂ} {R : ℝ≥0∞} (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R)
    (hζs : ζ ∈ slitPlane) (hζ : ‖ζ‖ₑ < R) (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius)
    (hζg : ‖ζ‖ₑ < (ofScalars ℂ gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) (ζ * fζ)) (hG : HasSum (fun s ↦ gs s * ζ ^ s) (ζ ^ 2 * gζ))
    (hE : HasSum (fun s ↦ es s * ζ ^ s) E)
    (ha : ∀ s : ℕ, ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k + es s = 0) :
    deriv (deriv fun y ↦ y ^ ρ * S y) ζ + fζ * deriv (fun y ↦ y ^ ρ * S y) ζ +
      gζ * (ζ ^ ρ * S ζ) + ζ ^ (ρ - 1 - 1) * E = 0 := by
  -- `deriv w` agrees near `ζ` with the formula of `hasDerivAt_cpow_mul`, which we differentiate
  have hU : IsOpen (slitPlane ∩ Metric.eball (0 : ℂ) R) :=
    isOpen_slitPlane.inter Metric.isOpen_eball
  have hζU : ζ ∈ slitPlane ∩ Metric.eball (0 : ℂ) R := ⟨hζs, mem_eball_zero_iff.mpr hζ⟩
  have hderiv : deriv (fun y ↦ y ^ ρ * S y) =ᶠ[𝓝 ζ]
      fun y ↦ ρ * y ^ (ρ - 1) * S y + y ^ ρ * deriv S y :=
    Filter.eventually_of_mem (hU.mem_nhds hζU) fun y hy ↦
      (hasDerivAt_cpow_mul hS hy.1 (mem_eball_zero_iff.mp hy.2)).deriv
  have hd1 := hasDerivAt_cpow_mul (ρ := ρ - 1) hS hζs hζ
  have hd2 := hasDerivAt_cpow_mul (ρ := ρ) hS.deriv_ofScalars hζs hζ
  have hd : HasDerivAt (fun y ↦ ρ * y ^ (ρ - 1) * S y + y ^ ρ * deriv S y)
      (ρ * ((ρ - 1) * ζ ^ (ρ - 1 - 1) * S ζ + ζ ^ (ρ - 1) * deriv S ζ) +
        (ρ * ζ ^ (ρ - 1) * deriv S ζ + ζ ^ ρ * deriv (deriv S) ζ)) ζ := by
    convert (hd1.const_mul ρ).fun_add hd2 using 1
    ext y
    ring
  rw [hderiv.deriv_eq, hd.deriv, (hasDerivAt_cpow_mul hS hζs hζ).deriv]
  have hζ0 : ζ ≠ 0 := slitPlane_ne_zero hζs
  have e1 : ζ ^ (ρ - 1) = ζ ^ (ρ - 1 - 1) * ζ := by
    conv_lhs => rw [show ρ - 1 = ρ - 1 - 1 + 1 by ring, cpow_add _ _ hζ0, cpow_one]
  have e2 : ζ ^ ρ = ζ ^ (ρ - 1) * ζ := by
    conv_lhs => rw [show ρ = ρ - 1 + 1 by ring, cpow_add _ _ hζ0, cpow_one]
  rw [e2, e1]
  linear_combination ζ ^ (ρ - 1 - 1) * euler_form_eq_zero hS hζ hζf hζg hF hG hE ha

private theorem enorm_lt_ofReal_iff {ζ : ℂ} {r : ℝ} : ‖ζ‖ₑ < ENNReal.ofReal r ↔ ‖ζ‖ < r := by
  simpa using edist_lt_ofReal (x := ζ) (y := 0)

/-- A series in powers of `z - z₀` converging on the punctured disc `0 < ‖z - z₀‖ < r` has radius
of convergence at least `r`. -/
private theorem le_radius_of_hasSum_sub {z₀ : ℂ} {r : ℝ} {fs : ℕ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → HasSum (fun s ↦ fs s * (z - z₀) ^ s) (F z)) :
    ENNReal.ofReal r ≤ (ofScalars ℂ fs).radius :=
  le_radius_ofScalars_of_summable fs fun ζ hζ0 hζ ↦ by
    simpa using (hf (ζ + z₀) (by simpa using hζ0)
      (by simpa using enorm_lt_ofReal_iff.1 hζ)).summable

/-- The sum `∑ pₛ ζˢ` of a series of radius at least `r > 0` has it as power series on the disc
of radius `r`. -/
private theorem hasFPowerSeriesOnBall_tsum {p : ℕ → ℂ} {r : ℝ}
    (hp : ENNReal.ofReal r ≤ (ofScalars ℂ p).radius) (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun ζ ↦ ∑' s, p s * ζ ^ s) (ofScalars ℂ p) 0 (ENNReal.ofReal r) := by
  have hr' := ENNReal.ofReal_pos.mpr hr
  simpa [ofScalars_sum_eq] using
    (hasFPowerSeriesOnBall_ofScalarsSum_sub p (0 : ℂ) (hr'.trans_le hp)).mono hr' hp

/-- The recursion of the Frobenius series, with the indicial equation as its case `s = 0`, in the
uniform form with zero forcing term. -/
private theorem regularSingular_recursion {ρ : ℂ} {fs gs a : ℕ → ℂ}
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) (s : ℕ) :
    ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s +
      ∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k + (0 : ℕ → ℂ) s = 0 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simpa using congrArg (· * a 0) hρ
  · rw [ha s hs, Pi.zero_apply]
    ring

/-- **The Frobenius series solution at a regular singularity** (DLMF 2.7.2–2.7.5). Suppose that
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ` on the punctured disc
`0 < ‖z - z₀‖ < r`. Let `ρ` be a root of the indicial polynomial `Q(α) = α (α - 1) + f₀ α + g₀`,
and let `Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`. Then
`∑ aₛ (z - z₀)ˢ` converges on the disc `‖z - z₀‖ < r`, and `w(z) = (z - z₀) ^ ρ ∑ aₛ (z - z₀)ˢ` is
holomorphic on the slit punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}` and solves
`w'' + f w' + g w = 0` there.

The recursion determines `aₛ` from the earlier coefficients whenever `Q(ρ + s) ≠ 0`, which holds
for all `s ≥ 1` when `ρ` is the root of larger real part. At an index with `Q(ρ + s) = 0` it is
instead a condition on the earlier coefficients, and `aₛ` is arbitrary; the theorem holds in
either case. The usual normalization `a₀ = 1` is not needed. -/
theorem regularSingular_solution {z₀ ρ : ℂ} {r : ℝ} {f g w : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k)
    (hw : w = fun z ↦ (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  -- the three series converge on the disc of radius `r` about the origin
  have hfr := le_radius_of_hasSum_sub hf
  have hgr := le_radius_of_hasSum_sub hg
  have har := le_radius_ofScalars_of_regularSingular (s₀ := 0) hfr hgr (by simp)
    fun s _ ↦ regularSingular_recursion hρ ha s
  have hlt {z : ℂ} (hz : ‖z - z₀‖ < r) := enorm_lt_ofReal_iff.2 hz
  refine ⟨fun z hz ↦ (summable_norm_mul_pow_of_lt_radius a ((hlt hz).trans_le har)).of_norm, ?_⟩
  -- `w` as a translate of `W(ζ) = ζ ^ ρ S(ζ)`, where `S` is the sum of the series
  set S : ℂ → ℂ := fun ζ ↦ ∑' s, a s * ζ ^ s
  have hS {z : ℂ} (hz : ‖z - z₀‖ < r) :=
    hasFPowerSeriesOnBall_tsum har ((norm_nonneg _).trans_lt hz)
  have hwW : w = fun z ↦ (fun ζ ↦ ζ ^ ρ * S ζ) (z - z₀) := hw
  have hd1 : deriv w = fun z ↦ deriv (fun ζ ↦ ζ ^ ρ * S ζ) (z - z₀) := by
    rw [hwW]
    exact funext fun z ↦ deriv_comp_sub_const (fun ζ ↦ ζ ^ ρ * S ζ) z₀ z
  have hd2 : deriv (deriv w) = fun z ↦ deriv (deriv fun ζ ↦ ζ ^ ρ * S ζ) (z - z₀) := by
    rw [hd1]
    exact funext fun z ↦ deriv_comp_sub_const (deriv fun ζ ↦ ζ ^ ρ * S ζ) z₀ z
  refine ⟨fun z hz ↦ ?_, fun z hzs hz ↦ ?_⟩
  · rw [hwW]
    exact ((hasDerivAt_cpow_mul (hS hz.2) hz.1 (hlt hz.2)).comp_sub_const z z₀
      |>.differentiableAt.differentiableWithinAt)
  · have h0 : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hzs)
    rw [hd2, hd1, hwW]
    have := deriv_deriv_cpow_mul_add_eq_zero (hS hz) hzs (hlt hz)
      ((hlt hz).trans_le hfr) ((hlt hz).trans_le hgr) (hf z h0 hz) (hg z h0 hz)
      (by simp only [Pi.zero_apply, zero_mul]; exact hasSum_zero)
      (regularSingular_recursion hρ ha)
    rwa [mul_zero, add_zero] at this

/-- A check of the hypotheses: for `w'' - 2 z⁻² w = 0` at `z₀ = 0` the indicial roots are `2` and
`-1`, and at `ρ = 2` the recursion gives `a₀ = 1` and `aₛ = 0` for `s ≥ 1`, so the Frobenius series
is `z ^ 2`. -/
example {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv fun z ↦ z ^ (2 : ℂ) * ∑' s, (if s = 0 then 1 else 0) * z ^ s) z +
        0 * deriv (fun z ↦ z ^ (2 : ℂ) * ∑' s, (if s = 0 then 1 else 0) * z ^ s) z +
      -2 / z ^ 2 * (z ^ (2 : ℂ) * ∑' s, (if s = 0 then 1 else 0) * z ^ s) = 0 := by
  have hgs (y : ℂ) (hy : y ≠ 0) :
      HasSum (fun s ↦ (if s = 0 then -2 else 0) * y ^ s) (y ^ 2 * (-2 / y ^ 2)) := by
    convert hasSum_ite_eq 0 (-2 : ℂ) using 1
    · ext s
      split_ifs <;> simp_all
    · field_simp
  refine (regularSingular_solution (z₀ := 0) (ρ := 2) (r := ‖z‖ + 1) (f := 0)
    (g := fun y ↦ -2 / y ^ 2) (fs := 0) (gs := fun s ↦ if s = 0 then -2 else 0)
    (a := fun s ↦ if s = 0 then 1 else 0) (fun y _ _ ↦ by simp [hasSum_zero])
    (fun y hy _ ↦ by simpa using hgs y (by simpa using hy)) (by norm_num)
    (fun s hs ↦ ?_) (by simp)).2.2 z (by simpa using hz) (by simp)
  have hs0 : s ≠ 0 := by omega
  simp only [hs0, ↓reduceIte, mul_zero]
  rw [eq_comm, neg_eq_zero]
  exact sum_eq_zero fun k hk ↦ by simp [Nat.sub_ne_zero_of_lt (mem_range.1 hk)]

/-! ### The logarithmic solution -/

/-- The first two derivatives of `u * log` on an open subset of the slit plane on which `u` is
holomorphic. -/
private theorem deriv_mul_log {u : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUs : U ⊆ slitPlane)
    (hu : DifferentiableOn ℂ u U) {ζ : ℂ} (hζ : ζ ∈ U) :
    deriv (fun y ↦ u y * log y) ζ = deriv u ζ * log ζ + u ζ * ζ⁻¹ ∧
      deriv (deriv fun y ↦ u y * log y) ζ =
        deriv (deriv u) ζ * log ζ + 2 * deriv u ζ * ζ⁻¹ - u ζ * (ζ ^ 2)⁻¹ := by
  have h1 {y : ℂ} (hy : y ∈ U) :
      HasDerivAt (fun y ↦ u y * log y) (deriv u y * log y + u y * y⁻¹) y :=
    (hu.differentiableAt (hU.mem_nhds hy)).hasDerivAt.mul (hasDerivAt_log (hUs hy))
  refine ⟨(h1 hζ).deriv, ?_⟩
  have hev : deriv (fun y ↦ u y * log y) =ᶠ[𝓝 ζ] fun y ↦ deriv u y * log y + u y * y⁻¹ :=
    Filter.eventually_of_mem (hU.mem_nhds hζ) fun y hy ↦ (h1 hy).deriv
  have hd := (((hu.deriv hU).differentiableAt (hU.mem_nhds hζ)).hasDerivAt.fun_mul
    (hasDerivAt_log (hUs hζ))).fun_add ((hu.differentiableAt (hU.mem_nhds hζ)).hasDerivAt.fun_mul
    (hasDerivAt_inv (slitPlane_ne_zero (hUs hζ))))
  rw [hev.deriv_eq, hd.deriv]
  ring

/-- With `S = ∑ aₛ ζˢ` and `F = ∑ fₛ ζˢ`, the function `2 α S + 2 ζ S' - S + F S` has the
coefficients `dₛ = (2 (α + s) - 1) aₛ + ∑_{k ≤ s} f_{s-k} aₖ`. For `w = ζ^α S` it is
`ζ^{2 - α} (2 w' / ζ + (F - 1) w / ζ²)`, the part of the equation applied to `w log ζ` that does
not involve `log ζ`. -/
private theorem hasSum_log_coeff {α ζ F : ℂ} {fs a : ℕ → ℂ} {S : ℂ → ℂ} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius) (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) :
    HasSum (fun n ↦ ((2 * (α + n) - 1) * a n + ∑ k ∈ range (n + 1), fs (n - k) * a k) * ζ ^ n)
      (2 * α * S ζ + 2 * (ζ * deriv S ζ) - S ζ + F * S ζ) := by
  have h0 : HasSum (fun n ↦ a n * ζ ^ n) (S ζ) := by
    simpa [ofScalars_apply_eq, mul_comm] using hS.hasSum (mem_eball_zero_iff.mpr hζ)
  have h1 := hS.hasSum_mul_deriv_ofScalars hζ
  have hC := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_mul_pow_of_lt_radius a (hζ.trans_le hS.r_le))
    (summable_norm_mul_pow_of_lt_radius fs hζf)
  rw [h0.tsum_eq, hF.tsum_eq, mul_comm] at hC
  convert (((h0.mul_left (2 * α)).add (h1.mul_left 2)).sub h0).add hC using 1
  ext n
  have hsum : ∑ k ∈ range (n + 1), a k * ζ ^ k * (fs (n - k) * ζ ^ (n - k)) =
      (∑ k ∈ range (n + 1), fs (n - k) * a k) * ζ ^ n := by
    rw [sum_mul]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [← pow_mul_pow_sub ζ (mem_range_succ_iff.mp hk)]
    ring
  rw [hsum]
  ring

/-- The forcing term `c ζᴺ D` of the logarithmic solution, as a power series: its coefficients
vanish below `N` and are `c d_{s-N}` from `N` on. -/
private theorem hasSum_log_forcing {α c ζ D : ℂ} {N : ℕ} {fs a : ℕ → ℂ}
    (hD : HasSum (fun n ↦ ((2 * (α + n) - 1) * a n +
      ∑ k ∈ range (n + 1), fs (n - k) * a k) * ζ ^ n) D) :
    HasSum (fun s ↦ (if s < N then 0 else c * ((2 * (α + (s - N : ℕ)) - 1) * a (s - N) +
      ∑ k ∈ range (s - N + 1), fs (s - N - k) * a k)) * ζ ^ s) (c * ζ ^ N * D) := by
  refine (hasSum_nat_add_iff' N).mp ?_
  rw [sum_eq_zero fun i hi ↦ by simp [mem_range.1 hi], sub_zero]
  convert hD.mul_left (c * ζ ^ N) using 1
  ext n
  simp only [show ¬n + N < N by omega, ↓reduceIte, Nat.add_sub_cancel]
  ring

/-- The two recursions of the logarithmic solution combine into one recursion for all `s`, with
the forcing term `eₛ = c d_{s-N}` for `s ≥ N` and `eₛ = 0` for `s < N`. -/
private theorem log_recursion_iff {α₁ α₂ c : ℂ} {N : ℕ} {fs gs a b : ℕ → ℂ}
    (hN : α₁ = α₂ + N) :
    ((∀ s < N, ((α₂ + s) * (α₂ + s - 1) + fs 0 * (α₂ + s) + gs 0) * b s =
        -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k) ∧
      ∀ s : ℕ, ((α₁ + s) * (α₁ + s - 1) + fs 0 * (α₁ + s) + gs 0) * b (s + N) =
        -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * b k -
          c * ((2 * (α₁ + s) - 1) * a s + ∑ k ∈ range (s + 1), fs (s - k) * a k)) ↔
      ∀ s : ℕ, ((α₂ + s) * (α₂ + s - 1) + fs 0 * (α₂ + s) + gs 0) * b s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k +
        (if s < N then 0 else c * ((2 * (α₁ + (s - N : ℕ)) - 1) * a (s - N) +
          ∑ k ∈ range (s - N + 1), fs (s - N - k) * a k)) = 0 := by
  subst hN
  constructor
  · rintro ⟨hlt, hge⟩ s
    rcases lt_or_ge s N with hs | hs
    · simp only [hs, ↓reduceIte]
      linear_combination hlt s hs
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + N := ⟨s - N, by omega⟩
      simp only [show ¬j + N < N by omega, ↓reduceIte, Nat.add_sub_cancel]
      push_cast
      linear_combination hge j
  · intro h
    refine ⟨fun s hs ↦ ?_, fun s ↦ ?_⟩
    · have := h s
      simp only [hs, ↓reduceIte] at this
      linear_combination this
    · have := h (s + N)
      simp only [show ¬s + N < N by omega, ↓reduceIte, Nat.add_sub_cancel] at this
      push_cast at this
      linear_combination this

/-- The equation at a point `ζ` of the slit disc, for the logarithmic solution about the origin:
`w(ζ) = ζ^{α₂} T(ζ) + c ζ^{α₁} S(ζ) log ζ`, where `ζ^{α₁} S` is a Frobenius solution and the
coefficients of `T` satisfy the recursion forced by `c ζ^{α₁ - α₂} D`. -/
private theorem deriv_deriv_log_add_eq_zero {α₁ α₂ c ζ fζ gζ : ℂ} {N : ℕ} {fs gs a b : ℕ → ℂ}
    {S T w : ℂ → ℂ} {R : ℝ≥0∞} (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R)
    (hT : HasFPowerSeriesOnBall T (ofScalars ℂ b) 0 R) (hζs : ζ ∈ slitPlane) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius) (hζg : ‖ζ‖ₑ < (ofScalars ℂ gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) (ζ * fζ)) (hG : HasSum (fun s ↦ gs s * ζ ^ s) (ζ ^ 2 * gζ))
    (hN : α₁ = α₂ + N)
    (ha : ∀ s : ℕ, ((α₁ + s) * (α₁ + s - 1) + fs 0 * (α₁ + s) + gs 0) * a s +
      ∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k + (0 : ℕ → ℂ) s = 0)
    (hb : ∀ s : ℕ, ((α₂ + s) * (α₂ + s - 1) + fs 0 * (α₂ + s) + gs 0) * b s +
        ∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k +
        (if s < N then 0 else c * ((2 * (α₁ + (s - N : ℕ)) - 1) * a (s - N) +
          ∑ k ∈ range (s - N + 1), fs (s - N - k) * a k)) = 0)
    (hw : w = fun y ↦ y ^ α₂ * T y + c * (y ^ α₁ * S y * log y)) :
    deriv (deriv w) ζ + fζ * deriv w ζ + gζ * w ζ = 0 := by
  have hζ0 : ζ ≠ 0 := slitPlane_ne_zero hζs
  set U := slitPlane ∩ Metric.eball (0 : ℂ) R
  have hU : IsOpen U := isOpen_slitPlane.inter Metric.isOpen_eball
  have hζU : ζ ∈ U := ⟨hζs, mem_eball_zero_iff.mpr hζ⟩
  have hUn : U ∈ 𝓝 ζ := hU.mem_nhds hζU
  have hdiff {ρ : ℂ} {V : ℂ → ℂ} {p : ℕ → ℂ} (hV : HasFPowerSeriesOnBall V (ofScalars ℂ p) 0 R) :
      DifferentiableOn ℂ (fun y ↦ y ^ ρ * V y) U := fun y hy ↦
    (hasDerivAt_cpow_mul hV hy.1 (mem_eball_zero_iff.mp hy.2)).differentiableAt
      |>.differentiableWithinAt
  set W₁ : ℂ → ℂ := fun y ↦ y ^ α₁ * S y
  set W₂ : ℂ → ℂ := fun y ↦ y ^ α₂ * T y
  set L : ℂ → ℂ := fun y ↦ W₁ y * log y
  have h1 : DifferentiableOn ℂ W₁ U := hdiff hS
  have h2 : DifferentiableOn ℂ W₂ U := hdiff hT
  have hL : DifferentiableOn ℂ L U := h1.mul fun y hy ↦
    (differentiableAt_log hy.1).differentiableWithinAt
  -- the equations for `W₁` and `W₂`, and the derivatives of `W₁ log`
  have eq1 := deriv_deriv_cpow_mul_add_eq_zero hS hζs hζ hζf hζg hF hG
    (by simp only [Pi.zero_apply, zero_mul]; exact hasSum_zero) ha
  have eq2 := deriv_deriv_cpow_mul_add_eq_zero hT hζs hζ hζf hζg hF hG
    (hasSum_log_forcing (c := c) (N := N) (hasSum_log_coeff (α := α₁) hS hζ hζf hF)) hb
  obtain ⟨hL1, hL2⟩ := deriv_mul_log hU (fun y hy ↦ hy.1) h1 hζU
  have hW₁ : deriv W₁ ζ = α₁ * ζ ^ (α₁ - 1) * S ζ + ζ ^ α₁ * deriv S ζ :=
    (hasDerivAt_cpow_mul hS hζs hζ).deriv
  -- `w = W₂ + c L`, so its derivatives split
  have hw' : w = fun y ↦ W₂ y + c * L y := hw
  have hdw {y : ℂ} (hy : y ∈ U) : deriv w y = deriv W₂ y + c * deriv L y := by
    rw [hw']
    exact ((h2.differentiableAt (hU.mem_nhds hy)).hasDerivAt.add
      ((hL.differentiableAt (hU.mem_nhds hy)).hasDerivAt.const_mul c)).deriv
  have hddw : deriv (deriv w) ζ = deriv (deriv W₂) ζ + c * deriv (deriv L) ζ := by
    have hev : deriv w =ᶠ[𝓝 ζ] fun y ↦ deriv W₂ y + c * deriv L y :=
      Filter.eventually_of_mem hUn fun y hy ↦ hdw hy
    rw [hev.deriv_eq]
    exact ((((h2.deriv hU).differentiableAt hUn).hasDerivAt).add
      ((((hL.deriv hU).differentiableAt hUn).hasDerivAt).const_mul c)).deriv
  rw [hddw, hdw hζU, hL2, hL1, hw']
  simp only [W₁, W₂, L] at eq1 eq2 hW₁ ⊢
  rw [hW₁] at eq1 ⊢
  -- write the powers of `ζ` through `P = ζ^{α₂ - 2}`
  have e1 : ζ ^ (α₁ - 1) = ζ ^ (α₂ - 1 - 1) * ζ ^ N * ζ := by
    rw [hN, show α₂ + N - 1 = α₂ - 1 - 1 + N + 1 by ring, cpow_add _ _ hζ0, cpow_add _ _ hζ0,
      cpow_natCast, cpow_one]
  have e2 : ζ ^ α₁ = ζ ^ (α₂ - 1 - 1) * ζ ^ N * ζ ^ 2 := by
    rw [hN, show α₂ + N = α₂ - 1 - 1 + N + 2 by ring, cpow_add _ _ hζ0, cpow_add _ _ hζ0,
      cpow_natCast, show (2 : ℂ) = (2 : ℕ) by norm_num, cpow_natCast]
  rw [e1, e2] at eq1 ⊢
  have hinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  linear_combination eq2 + c * log ζ * eq1 + c * ζ ^ (α₂ - 1 - 1) * ζ ^ N *
    (2 * α₁ * S ζ + 2 * ζ * deriv S ζ + fζ * ζ * S ζ - S ζ * (ζ * ζ⁻¹ + 1)) * hinv

/-- **The logarithmic solution at a regular singularity** (DLMF 2.7.6). Suppose that
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ` on the punctured disc
`0 < ‖z - z₀‖ < r`, let `Q(α) = α (α - 1) + f₀ α + g₀` be the indicial polynomial, and let
`w₁(z) = (z - z₀)^{α₁} ∑ aₛ (z - z₀)ˢ` be the Frobenius solution at a root `α₁` of `Q`
(`TauCeti.regularSingular_solution`). Let `α₂ = α₁ - N` for a natural number `N`, put
`dₛ = (2 (α₁ + s) - 1) aₛ + ∑_{k ≤ s} f_{s-k} aₖ`, and let `c` and the `bₛ` satisfy

* `Q(α₂ + s) bₛ = -∑_{k < s} ((α₂ + k) f_{s-k} + g_{s-k}) bₖ` for `s < N`, and
* `Q(α₁ + s) b_{s+N} = -∑_{k < s + N} ((α₂ + k) f_{s+N-k} + g_{s+N-k}) bₖ - c dₛ` for all `s`.

Then `∑ bₛ (z - z₀)ˢ` converges on the disc `‖z - z₀‖ < r`, and
`w(z) = (z - z₀)^{α₂} ∑ bₛ (z - z₀)ˢ + c w₁(z) log (z - z₀)`, with the principal power and
logarithm, is holomorphic on the slit punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`
and solves `w'' + f w' + g w = 0` there.

The theorem does not need `α₂` to be a root of `Q`. When `α₂` is the second root, so that
`Q(α) = (α - α₁)(α - α₂)`, coefficients with the normalizations of DLMF 2.7.6 exist and are unique
(`TauCeti.existsUnique_regularSingular_log_coeff`). -/
theorem regularSingular_log_solution {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ} {f g w : ℂ → ℂ}
    {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hα₁ : α₁ * (α₁ - 1) + fs 0 * α₁ + gs 0 = 0) (hN : α₁ = α₂ + N)
    (ha : ∀ s : ℕ, 1 ≤ s → ((α₁ + s) * (α₁ + s - 1) + fs 0 * (α₁ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k)
    (hb : ∀ s < N, ((α₂ + s) * (α₂ + s - 1) + fs 0 * (α₂ + s) + gs 0) * b s =
      -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k)
    (hb' : ∀ s : ℕ, ((α₁ + s) * (α₁ + s - 1) + fs 0 * (α₁ + s) + gs 0) * b (s + N) =
      -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * b k -
        c * ((2 * (α₁ + s) - 1) * a s + ∑ k ∈ range (s + 1), fs (s - k) * a k))
    (hw : w = fun z ↦ (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) +
      c * ((z - z₀) ^ α₁ * (∑' s, a s * (z - z₀) ^ s) * log (z - z₀))) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s ↦ b s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  -- the series of `a` converges on the disc of radius `r` about the origin
  have hfr := le_radius_of_hasSum_sub hf
  have hgr := le_radius_of_hasSum_sub hg
  have hrecA := regularSingular_recursion hα₁ ha
  have har := le_radius_ofScalars_of_regularSingular (s₀ := 0) hfr hgr (by simp)
    fun s _ ↦ hrecA s
  have hr {ζ : ℂ} (hζ : ‖ζ‖ₑ < ENNReal.ofReal r) : 0 < r :=
    ENNReal.ofReal_pos.mp ((zero_le).trans_lt hζ)
  -- the series of the forcing term converges on the disc, hence so does that of the `bₛ`
  have hes := le_radius_ofScalars_of_summable _ fun ζ _ hζ ↦
    (hasSum_log_forcing (c := c) (N := N) (hasSum_log_coeff (α := α₁)
      (hasFPowerSeriesOnBall_tsum har (hr hζ)) hζ (hζ.trans_le hfr)
      (summable_norm_mul_pow_of_lt_radius fs (hζ.trans_le hfr)).of_norm.hasSum)).summable
  have hrecB := (log_recursion_iff hN).1 ⟨hb, hb'⟩
  have hbr := le_radius_ofScalars_of_regularSingular (s₀ := 0) hfr hgr hes fun s _ ↦ hrecB s
  have hlt {z : ℂ} (hz : ‖z - z₀‖ < r) := enorm_lt_ofReal_iff.2 hz
  refine ⟨fun z hz ↦ (summable_norm_mul_pow_of_lt_radius b ((hlt hz).trans_le hbr)).of_norm, ?_⟩
  -- `w` as a translate of `W(ζ) = ζ ^ α₂ T(ζ) + c ζ ^ α₁ S(ζ) log ζ`
  set S : ℂ → ℂ := fun ζ ↦ ∑' s, a s * ζ ^ s
  set T : ℂ → ℂ := fun ζ ↦ ∑' s, b s * ζ ^ s
  set W : ℂ → ℂ := fun y ↦ y ^ α₂ * T y + c * (y ^ α₁ * S y * log y)
  have hwW : w = fun z ↦ W (z - z₀) := hw
  have hd1 : deriv w = fun z ↦ deriv W (z - z₀) := by
    rw [hwW]
    exact funext fun z ↦ deriv_comp_sub_const W z₀ z
  have hd2 : deriv (deriv w) = fun z ↦ deriv (deriv W) (z - z₀) := by
    rw [hd1]
    exact funext fun z ↦ deriv_comp_sub_const (deriv W) z₀ z
  refine ⟨fun z hz ↦ ?_, fun z hzs hz ↦ ?_⟩
  · have hz' := hlt hz.2
    have hW : DifferentiableAt ℂ W (z - z₀) :=
      (hasDerivAt_cpow_mul (hasFPowerSeriesOnBall_tsum hbr (hr hz')) hz.1 hz').differentiableAt.add
        (((hasDerivAt_cpow_mul (hasFPowerSeriesOnBall_tsum har (hr hz')) hz.1
          hz').differentiableAt.mul
          (differentiableAt_log hz.1)).const_mul c)
    rw [hwW]
    exact (hW.hasDerivAt.comp_sub_const z z₀).differentiableAt.differentiableWithinAt
  · have h0 : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hzs)
    have hz' := hlt hz
    rw [hd2, hd1, hwW]
    exact deriv_deriv_log_add_eq_zero (hasFPowerSeriesOnBall_tsum har (hr hz'))
      (hasFPowerSeriesOnBall_tsum hbr (hr hz')) hzs hz'
      (hz'.trans_le hfr) (hz'.trans_le hgr) (hf z h0 hz) (hg z h0 hz) hN hrecA hrecB rfl

/-! ### The coefficients of the logarithmic solution -/

/-- The solution of the triangular system `qₛ bₛ + ∑_{k < s} K s k bₖ + eₛ = 0` at the indices
with `qₛ ≠ 0`, taking the prescribed value `vₛ` at the indices with `qₛ = 0`. -/
private noncomputable def triangularSolve (q : ℕ → ℂ) (K : ℕ → ℕ → ℂ) (e v : ℕ → ℂ) (s : ℕ) :
    ℂ :=
  if q s = 0 then v s else -(∑ k : Fin s, K s k * triangularSolve q K e v k + e s) / q s
termination_by s
decreasing_by exact k.isLt

private theorem triangularSolve_eq (q : ℕ → ℂ) (K : ℕ → ℕ → ℂ) (e v : ℕ → ℂ) (s : ℕ) :
    triangularSolve q K e v s = if q s = 0 then v s else
      -(∑ k ∈ range s, K s k * triangularSolve q K e v k + e s) / q s := by
  rw [triangularSolve, Fin.sum_univ_eq_sum_range (fun k ↦ K s k * triangularSolve q K e v k)]

private theorem triangularSolve_of_eq_zero {q : ℕ → ℂ} (K : ℕ → ℕ → ℂ) (e v : ℕ → ℂ) {s : ℕ}
    (hq : q s = 0) : triangularSolve q K e v s = v s := by
  rw [triangularSolve_eq]
  simp [hq]

private theorem triangularSolve_spec {q : ℕ → ℂ} (K : ℕ → ℕ → ℂ) (e v : ℕ → ℂ) {s : ℕ}
    (hq : q s ≠ 0) : q s * triangularSolve q K e v s +
      ∑ k ∈ range s, K s k * triangularSolve q K e v k + e s = 0 := by
  rw [triangularSolve_eq q K e v s]
  simp only [hq, ↓reduceIte]
  field_simp
  ring

/-- Two solutions of a triangular system, with forcing terms that agree below `n`, agree below
`n` as soon as they agree at the indices `j < n` with `qⱼ = 0`. -/
private theorem eq_of_triangular {q : ℕ → ℂ} {K : ℕ → ℕ → ℂ} {e e' x y : ℕ → ℂ} {n : ℕ}
    (hx : ∀ j < n, q j ≠ 0 → q j * x j + ∑ k ∈ range j, K j k * x k + e j = 0)
    (hy : ∀ j < n, q j ≠ 0 → q j * y j + ∑ k ∈ range j, K j k * y k + e' j = 0)
    (he : ∀ j < n, e j = e' j) (hxy : ∀ j < n, q j = 0 → x j = y j) :
    ∀ j < n, x j = y j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hq : q j = 0
    · exact hxy j hj hq
    · have hs : ∑ k ∈ range j, K j k * x k = ∑ k ∈ range j, K j k * y k :=
        sum_congr rfl fun k hk ↦ by rw [ih k (mem_range.1 hk) ((mem_range.1 hk).trans hj)]
      apply mul_left_cancel₀ hq
      linear_combination hx j hj hq - hy j hj hq - hs - he j hj

/-- Existence for the triangular system of the logarithmic solution, whose forcing term is
`c d_{s-N}` from the index `N` on and whose diagonal `q` vanishes exactly at `0` and `N`: the
values at those indices are prescribed by `v`, `c = 1` when `N = 0`, and otherwise `c` is fixed by
the equation at index `N`. -/
private theorem exists_log_triangular {q : ℕ → ℂ} {K : ℕ → ℕ → ℂ} {d v : ℕ → ℂ} {N : ℕ}
    (hq : ∀ s, q s = 0 ↔ s = 0 ∨ s = N) (hd₀ : N = 0 → d 0 = 0) (hd₀' : N ≠ 0 → d 0 ≠ 0) :
    ∃ (b : ℕ → ℂ) (c : ℂ), (N = 0 → c = 1) ∧ (∀ s, q s = 0 → b s = v s) ∧
      ∀ s, q s * b s + ∑ k ∈ range s, K s k * b k +
        (if s < N then 0 else c * d (s - N)) = 0 := by
  set e : ℂ → ℕ → ℂ := fun c s ↦ if s < N then 0 else c * d (s - N)
  -- below `N` the forcing term vanishes, so `c` may be read off a solution with `c = 0`
  set b₀ := triangularSolve q K (e 0) v
  set c : ℂ := if N = 0 then 1 else -(∑ k ∈ range N, K N k * b₀ k) / d 0
  set b := triangularSolve q K (e c) v
  have hbb₀ : ∀ j < N, b j = b₀ j :=
    eq_of_triangular (fun j _ hq ↦ triangularSolve_spec K (e c) v hq)
      (fun j _ hq ↦ triangularSolve_spec K (e 0) v hq) (fun j hj ↦ by simp [e, hj])
      (fun j _ hq ↦ by
        simp only [b, b₀]
        rw [triangularSolve_of_eq_zero K _ v hq, triangularSolve_of_eq_zero K _ v hq])
  refine ⟨b, c, fun hN0 ↦ by simp [c, hN0], fun s hs ↦ triangularSolve_of_eq_zero K _ v hs,
    fun s ↦ ?_⟩
  by_cases hqs : q s = 0
  · -- the equation at `s = 0` and `s = N`, where `q s = 0`
    rw [hqs, zero_mul, zero_add]
    rcases eq_or_ne N 0 with hN0 | hN0
    · obtain rfl : s = 0 := by simpa [hN0] using (hq s).1 hqs
      simp [hN0, hd₀ hN0]
    · rcases (hq s).1 hqs with h | h
      · simp [h, Nat.pos_of_ne_zero hN0]
      · rw [h]
        have hsum : ∑ k ∈ range N, K N k * b k = ∑ k ∈ range N, K N k * b₀ k :=
          sum_congr rfl fun k hk ↦ by rw [hbb₀ k (mem_range.1 hk)]
        have := hd₀' hN0
        simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, c, hN0, hsum]
        field_simp
        ring
  · exact triangularSolve_spec K (e c) v hqs

/-- Uniqueness for the triangular system of `exists_log_triangular`: two solutions that agree at
the zeros `0` and `N` of `q`, and whose constants `c` agree when `N = 0`, are equal. -/
private theorem log_triangular_unique {q : ℕ → ℂ} {K : ℕ → ℕ → ℂ} {d b b' : ℕ → ℂ} {c c' : ℂ}
    {N : ℕ} (hq : ∀ s, q s = 0 ↔ s = 0 ∨ s = N) (hd₀' : N ≠ 0 → d 0 ≠ 0)
    (hb : ∀ s, q s * b s + ∑ k ∈ range s, K s k * b k +
      (if s < N then 0 else c * d (s - N)) = 0)
    (hb' : ∀ s, q s * b' s + ∑ k ∈ range s, K s k * b' k +
      (if s < N then 0 else c' * d (s - N)) = 0)
    (hbb' : ∀ s, q s = 0 → b s = b' s) (hc : N = 0 → c = c') :
    b = b' ∧ c = c' := by
  -- first below `N`, where the forcing term vanishes, then `c`, then everywhere
  have hlow : ∀ j < N, b j = b' j :=
    eq_of_triangular (fun j _ _ ↦ hb j) (fun j _ _ ↦ hb' j) (fun j hj ↦ by simp [hj])
      (fun j _ hq ↦ hbb' j hq)
  obtain rfl : c = c' := by
    rcases eq_or_ne N 0 with hN0 | hN0
    · exact hc hN0
    · have hsum : ∑ k ∈ range N, K N k * b k = ∑ k ∈ range N, K N k * b' k :=
        sum_congr rfl fun k hk ↦ by rw [hlow k (mem_range.1 hk)]
      have e₁ := hb N
      have e₂ := hb' N
      simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, (hq N).2 (Or.inr rfl), zero_mul,
        zero_add, hsum] at e₁ e₂
      exact mul_right_cancel₀ (hd₀' hN0) (by linear_combination e₁ - e₂)
  exact ⟨funext fun j ↦ eq_of_triangular (fun j _ _ ↦ hb j) (fun j _ _ ↦ hb' j)
    (fun _ _ ↦ rfl) (fun j _ hq ↦ hbb' j hq) j j.lt_succ_self, rfl⟩

/-- **The coefficients of the logarithmic solution** (DLMF 2.7.6). Let `α₁` and `α₂` be the roots
of the indicial polynomial, `Q(α) = α (α - 1) + f₀ α + g₀ = (α - α₁)(α - α₂)`, with
`α₁ = α₂ + N` for a natural number `N`, and let `a₀ ≠ 0`. Put
`dₛ = (2 (α₁ + s) - 1) aₛ + ∑_{k ≤ s} f_{s-k} aₖ`. Then the recursions of
`TauCeti.regularSingular_log_solution`,

* `Q(α₂ + s) bₛ = -∑_{k < s} ((α₂ + k) f_{s-k} + g_{s-k}) bₖ` for `s < N`, and
* `Q(α₁ + s) b_{s+N} = -∑_{k < s + N} ((α₂ + k) f_{s+N-k} + g_{s+N-k}) bₖ - c dₛ` for all `s`,

have exactly one solution `(b, c)` with DLMF's normalization: `c = 1` and `b₀ = 0` when `N = 0`,
and `b₀ = 1` and `b_N = 0` when `N ≥ 1`.

The recursion determines `bₛ` whenever `Q(α₂ + s) = s (s - N)` is nonzero, that is for
`s ∉ {0, N}`. At `s = 0` and `s = N` the normalization fixes `b₀` and `b_N`, and when `N ≥ 1`
the recursion at index `N` determines `c`, since `d₀ = N a₀`. -/
theorem existsUnique_regularSingular_log_coeff {α₁ α₂ : ℂ} {N : ℕ} {fs gs a : ℕ → ℂ}
    (hQ : ∀ α : ℂ, α * (α - 1) + fs 0 * α + gs 0 = (α - α₁) * (α - α₂)) (hN : α₁ = α₂ + N)
    (ha₀ : a 0 ≠ 0) :
    ∃! bc : (ℕ → ℂ) × ℂ, (N = 0 → bc.2 = 1 ∧ bc.1 0 = 0) ∧ (N ≠ 0 → bc.1 0 = 1 ∧ bc.1 N = 0) ∧
      (∀ s < N, ((α₂ + s) * (α₂ + s - 1) + fs 0 * (α₂ + s) + gs 0) * bc.1 s =
        -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * bc.1 k) ∧
      ∀ s : ℕ, ((α₁ + s) * (α₁ + s - 1) + fs 0 * (α₁ + s) + gs 0) * bc.1 (s + N) =
        -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * bc.1 k -
          bc.2 * ((2 * (α₁ + s) - 1) * a s + ∑ k ∈ range (s + 1), fs (s - k) * a k) := by
  -- `f₀ = 1 - α₁ - α₂`, and `Q(α₂ + s) = s (s - N)` vanishes exactly at `s = 0` and `s = N`
  have hf₀ : fs 0 = 1 - α₁ - α₂ := by linear_combination hQ 1 - hQ 0
  have hq0 (s : ℕ) : (α₂ + s) * (α₂ + s - 1) + fs 0 * (α₂ + s) + gs 0 = 0 ↔ s = 0 ∨ s = N := by
    rw [hQ, hN, show α₂ + s - (α₂ + N) = s - N by ring, add_sub_cancel_left, mul_eq_zero,
      sub_eq_zero, or_comm]
    norm_cast
  set d : ℕ → ℂ := fun j ↦ (2 * (α₁ + j) - 1) * a j + ∑ k ∈ range (j + 1), fs (j - k) * a k
  have hd₀ : d 0 = N * a 0 := by
    simp only [d, CharP.cast_eq_zero, add_zero, zero_add, range_one, sum_singleton, Nat.sub_self]
    rw [hf₀, hN]
    ring
  have hd₀' (hN0 : N ≠ 0) : (N : ℂ) * a 0 ≠ 0 := mul_ne_zero (by exact_mod_cast hN0) ha₀
  -- DLMF's normalization prescribes the values at `0` and `N`, and `c` when `N = 0`
  set v : ℕ → ℂ := fun s ↦ if s = 0 ∧ N ≠ 0 then 1 else 0
  have hnorm {b : ℕ → ℂ} {c : ℂ} (h₁ : N = 0 → c = 1 ∧ b 0 = 0) (h₂ : N ≠ 0 → b 0 = 1 ∧ b N = 0)
      (s : ℕ) (hs : s = 0 ∨ s = N) : b s = v s := by
    rcases eq_or_ne N 0 with hN0 | hN0
    · obtain rfl : s = 0 := by omega
      simp [v, hN0, (h₁ hN0).2]
    · rcases hs with rfl | rfl
      · simp [v, hN0, (h₂ hN0).1]
      · simp [v, hN0, (h₂ hN0).2]
  obtain ⟨b, c, hc, hbv, hrec⟩ := exists_log_triangular (K := fun s k ↦ (α₂ + k) * fs (s - k) +
    gs (s - k)) (d := d) (v := v) (fun s ↦ hq0 s) (fun hN0 ↦ by rw [hd₀, hN0]; simp) fun hN0 ↦ by
      rw [hd₀]; exact hd₀' hN0
  have hbv' (s : ℕ) (hs : s = 0 ∨ s = N) : b s = v s := hbv s ((hq0 s).2 hs)
  refine ⟨(b, c), ⟨fun hN0 ↦ ⟨hc hN0, ?_⟩, fun hN0 ↦ ?_, (log_recursion_iff hN).2 hrec⟩, ?_⟩
  · simp [hbv' 0 (Or.inl rfl), v, hN0]
  · simp [hbv' 0 (Or.inl rfl), hbv' N (Or.inr rfl), v, hN0]
  rintro ⟨b', c'⟩ ⟨h₁, h₂, h₃⟩
  obtain ⟨rfl, rfl⟩ := log_triangular_unique (fun s ↦ hq0 s) (fun hN0 ↦ by
    rw [hd₀]; exact hd₀' hN0) ((log_recursion_iff hN).1 h₃) hrec
    (fun s hs ↦ (hnorm h₁ h₂ s ((hq0 s).1 hs)).trans (hbv' s ((hq0 s).1 hs)).symm)
    (fun hN0 ↦ (h₁ hN0).1.trans (hc hN0).symm)
  rfl

/-- A check of the hypotheses with coincident indicial roots: `z² w'' + z w' = 0`, that is
`f(z) = 1/z` and `g = 0` at `z₀ = 0`, has the double indicial root `0`, the Frobenius solution
`w₁ = 1`, and the logarithmic solution `log z` (`bₛ = 0`, `c = 1`). -/
example {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv fun z ↦ z ^ (0 : ℂ) * (∑' s, (0 : ℕ → ℂ) s * z ^ s) +
        1 * (z ^ (0 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) * log z)) z +
      z⁻¹ * deriv (fun z ↦ z ^ (0 : ℂ) * (∑' s, (0 : ℕ → ℂ) s * z ^ s) +
        1 * (z ^ (0 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) * log z)) z +
      0 * (z ^ (0 : ℂ) * (∑' s, (0 : ℕ → ℂ) s * z ^ s) +
        1 * (z ^ (0 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) * log z)) = 0 := by
  have hfs (y : ℂ) (hy : y ≠ 0) :
      HasSum (fun s ↦ (if s = 0 then 1 else 0) * y ^ s) (y * y⁻¹) := by
    convert hasSum_ite_eq 0 (1 : ℂ) using 1
    · ext s
      split_ifs <;> simp_all
    · field_simp
  refine (regularSingular_log_solution (z₀ := 0) (α₁ := 0) (α₂ := 0) (c := 1) (N := 0)
    (r := ‖z‖ + 1) (f := fun y ↦ y⁻¹) (g := 0) (fs := fun s ↦ if s = 0 then 1 else 0) (gs := 0)
    (a := fun s ↦ if s = 0 then 1 else 0) (b := 0)
    (fun y hy _ ↦ by simpa using hfs y (by simpa using hy)) (fun y _ _ ↦ by simp [hasSum_zero])
    (by simp) (by simp) (fun s hs ↦ ?_) (fun s hs ↦ by omega) (fun s ↦ ?_)
    (by simp)).2.2 z (by simpa using hz) (by simp)
  · have hs0 : s ≠ 0 := by omega
    simp only [hs0, ↓reduceIte, mul_zero]
    rw [eq_comm, neg_eq_zero]
    exact sum_eq_zero fun k hk ↦ by simp [Nat.sub_ne_zero_of_lt (mem_range.1 hk)]
  · rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · have hs0 : s ≠ 0 := by omega
      simp only [hs0, ↓reduceIte, Pi.zero_apply, mul_zero, sum_const_zero, neg_zero, zero_sub,
        add_zero, one_mul, zero_add]
      rw [sum_eq_single_of_mem s (mem_range.2 s.lt_succ_self) fun k hk hks ↦ ?_]
      · simp [hs0]
      · simp [Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (mem_range_succ_iff.1 hk) hks)]

/-- A check of the hypotheses with indicial roots differing by an integer: for `w'' - 2 z⁻² w = 0`
at `z₀ = 0` the roots are `α₁ = 2` and `α₂ = -1` (`N = 3`), the Frobenius solution is `z²`, and
the second solution is `z⁻¹` itself, with `b₀ = 1`, `bₛ = 0` for `s ≥ 1`, and no logarithmic
term (`c = 0`). -/
example {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv fun z ↦ z ^ (-1 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) +
        0 * (z ^ (2 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) * log z)) z +
      0 * deriv (fun z ↦ z ^ (-1 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) +
        0 * (z ^ (2 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) * log z)) z +
      -2 / z ^ 2 * (z ^ (-1 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) +
        0 * (z ^ (2 : ℂ) * (∑' s, (if s = 0 then 1 else 0) * z ^ s) * log z)) = 0 := by
  have hgs (y : ℂ) (hy : y ≠ 0) :
      HasSum (fun s ↦ (if s = 0 then -2 else 0) * y ^ s) (y ^ 2 * (-2 / y ^ 2)) := by
    convert hasSum_ite_eq 0 (-2 : ℂ) using 1
    · ext s
      split_ifs <;> simp_all
    · field_simp
  -- every term of the recursion sums vanishes: `g_{s-k} bₖ = 0` unless `k = 0 = s`
  have hsum (s : ℕ) (hs : s ≠ 0) (u : ℕ → ℂ) : ∑ k ∈ range s,
      (u k * (0 : ℕ → ℂ) (s - k) + (if s - k = 0 then -2 else 0)) *
        (if k = 0 then 1 else 0) = 0 :=
    sum_eq_zero fun k hk ↦ by rcases eq_or_ne k 0 with rfl | hk0 <;> simp [*]
  refine (regularSingular_log_solution (z₀ := 0) (α₁ := 2) (α₂ := -1) (c := 0) (N := 3)
    (r := ‖z‖ + 1) (f := 0) (g := fun y ↦ -2 / y ^ 2) (fs := 0)
    (gs := fun s ↦ if s = 0 then -2 else 0) (a := fun s ↦ if s = 0 then 1 else 0)
    (b := fun s ↦ if s = 0 then 1 else 0) (fun y _ _ ↦ by simp [hasSum_zero])
    (fun y hy _ ↦ by simpa using hgs y (by simpa using hy)) (by norm_num) (by norm_num)
    (fun s hs ↦ ?_) (fun s hs ↦ ?_) (fun s ↦ ?_) (by simp)).2.2 z (by simpa using hz) (by simp)
  · rw [hsum s (by omega)]
    simp [show s ≠ 0 by omega]
  · rcases eq_or_ne s 0 with rfl | hs0
    · norm_num
    · rw [hsum s hs0]
      simp [hs0]
  · rw [hsum (s + 3) (by omega)]
    simp

end TauCeti
