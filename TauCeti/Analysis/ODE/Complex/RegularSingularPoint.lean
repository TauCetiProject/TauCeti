/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.ODE.Complex.RegularSingularity.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Complex.PowerSeries.BranchCut
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.ODE.Complex.RegularSingularity.Primary
import TauCeti.Data.Nat.Choose.Sum

/-!
# Frobenius series solutions at a regular singularity

Consider the equation `w'' + f(z) w' + g(z) w = 0` near a point `z₀` at which `f` has at most a
simple pole and `g` at most a double pole, so that on a punctured disc `0 < |z - z₀| < r`

* `(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and
* `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ`,

with both series convergent there. Its indicial polynomial is
`Q(α) = TauCeti.indicialPoly (fs 0) (gs 0) α = α (α - 1) + f₀ α + g₀`.
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
`d_{s + N} = TauCeti.regularSingularLogForcing fs a α₂ N (s + N)` are the coefficients of the
terms of the equation applied to `c w₁ log (z - z₀)` that do not involve the logarithm. Every
solution of this recursion gives a convergent series and a solution of the equation
(`TauCeti.regularSingular_log_solution`); the Frobenius solution is its case `c = 0`, `N = 0`. With
DLMF's normalization (`c = 1` when `N = 0`; `b₀ = 1` and `b_N = 0` when `N ≥ 1`), together with
the additional convention `b₀ = 0` when `N = 0`, which fixes the free multiple of `w₁`, the
recursion has exactly one solution (`TauCeti.existsUnique_regularSingular_log_coeff`).

By Abel's identity, the Wronskian `w₁ w₂' - w₁' w₂` of any two
solutions on the slit punctured disc is `C (z - z₀)^{-f₀} exp(-∑_{s ≥ 1} fₛ (z - z₀)ˢ / s)` for a
constant `C` (`TauCeti.exists_wronskian_eq_of_regularSingular`). For two Frobenius solutions at
the roots `α₁` and `α₂` the constant is `(α₂ - α₁) a₀ b₀` (`TauCeti.regularSingular_wronskian`),
and for the Frobenius solution at `α₁` together with the logarithmic solution it is `c a₀²` when
`N = 0` and `-N a₀ b₀` when `N ≥ 1` (`TauCeti.regularSingular_log_wronskian`). The Wronskian
therefore vanishes nowhere on the slit punctured disc for two Frobenius solutions with
`α₁ ≠ α₂` and `a₀, b₀ ≠ 0` (`TauCeti.regularSingular_wronskian_ne_zero`), and for the Frobenius
solution with `a₀ ≠ 0` together with the logarithmic solution with `c ≠ 0` when `N = 0` and
`b₀ ≠ 0` when `N ≥ 1`, as in DLMF's normalization
(`TauCeti.regularSingular_log_wronskian_ne_zero`).

## Implementation notes

Convergence is proved by a majorant argument, for the recursion with a forcing term `eₛ`.
Since `Q(ρ + s) = s² + (2ρ - 1 + f₀) s + Q(ρ)`, `|Q(ρ + s)| ≥ s² / 2` for all large `s`; no
condition on `ρ` is needed. For `t` below the radii of convergence of the series of the `fₛ`,
`gₛ` and `eₛ`, `|aₛ| tˢ` is then bounded by a constant times the binomial coefficient
`C(s + m, m)` for a fixed `m`. The equation is verified using the Euler–Frobenius operator
identities (`TauCeti.deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum` and
`TauCeti.deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum_add_log`).

For the Wronskian, write `f = f₀ / ζ + Φ'` with `Φ = ∑_{s ≥ 1} fₛ ζˢ / s`, holomorphic on the
whole disc. Abel's identity `W' = -f W` makes `ζ^{f₀} exp(Φ) W` constant on the slit punctured
disc, which is star-shaped. Since `f₀ = 1 - α₁ - α₂`, a direct computation gives
`W = ζ^{α₁ + α₂ - 1} H(ζ)` for the two solutions above, with `H` holomorphic on the disc, so the
constant is `H(0)`, the limit along `ζ → 0+`.

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

/-- The arithmetic of the majorant step: when `2 K M ≤ m` and `2 Mₑ ≤ B`, the bound that the
recursion gives at index `n + 1` is at most `(n + 1)² B C(n + 1 + m, m)`, by the hockey-stick
identity. -/
private theorem two_mul_sum_choose_add_le {K M Me B : ℝ} {m n : ℕ} (hB : 0 ≤ B)
    (hm : 2 * (K * M) ≤ m) (hMe : 2 * Me ≤ B) :
    2 * (∑ k ∈ range (n + 1), K * (n + 1) * M * (B * ((k + m).choose m : ℝ)) + Me) ≤
      (n + 1) * ((n + 1) * (B * ((n + 1 + m).choose m : ℝ))) := by
  have hbinom : (1 : ℝ) + m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ) ≤
      (n + 1) * ((n + 1 + m).choose m : ℝ) := mod_cast Nat.one_add_mul_sum_range_add_choose_le n m
  have hsum0 : 0 ≤ ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ) := by positivity
  calc 2 * (∑ k ∈ range (n + 1), K * (n + 1) * M * (B * ((k + m).choose m : ℝ)) + Me)
      = (n + 1) * B * (2 * (K * M) * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) + 2 * Me := by
        rw [← mul_sum, ← mul_sum]
        ring
    _ ≤ (n + 1) * B * (m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) + (n + 1) * B := by
        refine add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hm hsum0) (by positivity)) ?_
        nlinarith
    _ = (n + 1) * B * (1 + m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) := by ring
    _ ≤ (n + 1) * B * ((n + 1) * ((n + 1 + m).choose m : ℝ)) := by gcongr
    _ = (n + 1) * ((n + 1) * (B * ((n + 1 + m).choose m : ℝ))) := by ring

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
  have hB0 : 0 ≤ B := by linarith [(by positivity : 0 ≤ ‖es 0‖ * t ^ 0).trans (hes 0)]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_or_ge n s₀ with hn | hn
    · exact (hB n hn).trans
        (le_mul_of_one_le_right hB0 (by exact_mod_cast Nat.choose_pos (by omega)))
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
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
        _ ≤ (n + 1) * ((n + 1) * (B * ((n + 1 + m).choose m : ℝ))) :=
            two_mul_sum_choose_add_le hB0 hm hMe
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
    (ha : ∀ s : ℕ, s₀ ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s +
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
  set γ : ℂ := indicialPoly (fs 0) (gs 0) ρ
  obtain ⟨s₁, hs₁⟩ := exists_nat_ge (2 * (‖β‖ + ‖γ‖) + 1)
  set s₂ := max s₀ (max s₁ 1)
  have hq (s : ℕ) (hs : s₂ ≤ s) :
      (s : ℝ) ^ 2 / 2 ≤ ‖indicialPoly (fs 0) (gs 0) (ρ + s)‖ := by
    have hs' : s₁ ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
    have heq : indicialPoly (fs 0) (gs 0) (ρ + s) = (s : ℂ) ^ 2 + β * s + γ := by
      rw [indicialPoly_add]; dsimp [β, γ]; ring
    rw [heq]
    exact sq_div_two_le_norm (hs₁.trans (by exact_mod_cast hs'))
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * ((‖ρ‖ + 1) * max Mf Mg))
  set B : ℝ := 2 * Me + ∑ k ∈ range s₂, ‖a k‖ * t ^ k
  have hB (k : ℕ) (hk : k < s₂) : ‖a k‖ * t ^ k ≤ B := by
    have hMe0 : 0 ≤ Me := (by positivity : 0 ≤ ‖es 0‖ * (t : ℝ) ^ 0).trans (hMe 0)
    have := single_le_sum (f := fun k ↦ ‖a k‖ * (t : ℝ) ^ k) (fun _ _ ↦ by positivity)
      (mem_range.2 hk)
    linarith
  have hbound := norm_mul_pow_le_mul_choose (a := a)
    (q := fun s ↦ indicialPoly (fs 0) (gs 0) (ρ + s)) t.property
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

/-! ### The Frobenius and logarithmic solutions -/

/-- **The logarithmic solution at a regular singularity** (DLMF 2.7.6). Suppose that
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ` on the punctured disc
`0 < ‖z - z₀‖ < r`, let `Q(α) = indicialPoly (fs 0) (gs 0) α` be the indicial polynomial, and
let `w₁(z) = (z - z₀)^{α₁} ∑ aₛ (z - z₀)ˢ` be the Frobenius solution at a root `α₁` of `Q`
(`TauCeti.regularSingular_solution`). Let `α₂ = α₁ - N` for a natural number `N`, let `c` and the
`bₛ` satisfy

* `Q(α₂ + s) bₛ = -∑_{k < s} ((α₂ + k) f_{s-k} + g_{s-k}) bₖ` for `s < N`, and
* `Q(α₁ + s) b_{s+N} = -∑_{k < s + N} ((α₂ + k) f_{s+N-k} + g_{s+N-k}) bₖ -`
  `c * regularSingularLogForcing fs a α₂ N (s + N)` for all `s`.

Then `∑ bₛ (z - z₀)ˢ` converges on the disc `‖z - z₀‖ < r`, and
`w(z) = (z - z₀)^{α₂} ∑ bₛ (z - z₀)ˢ + c w₁(z) log (z - z₀)`, with the principal power and
logarithm, is holomorphic on the slit punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`
and solves `w'' + f w' + g w = 0` there.

The theorem does not need `α₂` to be a root of `Q`. When `α₂` is the second root, so that
`Q(α) = (α - α₁)(α - α₂)`, coefficients with the normalization of DLMF 2.7.6, and `b₀ = 0` when
`N = 0`, exist and are unique (`TauCeti.existsUnique_regularSingular_log_coeff`). -/
theorem regularSingular_log_solution {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ} {f g w : ℂ → ℂ}
    {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hα₁ : indicialPoly (fs 0) (gs 0) α₁ = 0) (hN : α₁ = α₂ + N)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) * a s =
      -∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k)
    (hb : ∀ s < N, indicialPoly (fs 0) (gs 0) (α₂ + s) * b s =
      -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k)
    (hb' : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (α₁ + s) * b (s + N) =
      -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * b k -
        c * regularSingularLogForcing fs a α₂ N (s + N))
    (hw : w = fun z ↦ (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) +
      c * ((z - z₀) ^ α₁ * (∑' s, a s * (z - z₀) ^ s) * log (z - z₀))) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s ↦ b s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  subst hN
  have hfr := le_radius_ofScalars_of_summable_sub fs fun z h0 hz ↦ (hf z h0 hz).summable
  have hgr := le_radius_ofScalars_of_summable_sub gs fun z h0 hz ↦ (hg z h0 hz).summable
  have hrecA : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) ((α₂ + N) + s) * a s +
      ∑ k ∈ range s, (((α₂ + (N : ℂ)) + k) * fs (s - k) + gs (s - k)) * a k = 0 := by
    intro s
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simpa using congrArg (· * a 0) hα₁
    · rw [ha s hs]; ring
  have har := le_radius_ofScalars_of_regularSingular (s₀ := 0) (es := 0) hfr hgr (by simp)
    fun s _ ↦ by simpa only [Pi.zero_apply, add_zero] using hrecA s
  have hrecB := (forall_regularSingularLogForcing_rec_iff rfl).mpr ⟨hb, hb'⟩
  have hr {ζ : ℂ} (hζ : ‖ζ‖ₑ < ENNReal.ofReal r) : 0 < ENNReal.ofReal r := zero_le.trans_lt hζ
  have hes := le_radius_ofScalars_of_summable _ fun ζ _ hζ ↦
    (hasSum_regularSingularLogForcing_ofScalars (α₂ := α₂) (c := c) (N := N)
      (hasFPowerSeriesOnBall_tsum_mul_pow a (hr hζ) har) hζ (hζ.trans_le hfr)
      (summable_norm_mul_pow_of_lt_radius fs (hζ.trans_le hfr)).of_norm.hasSum).summable
  have hbr := le_radius_ofScalars_of_regularSingular (s₀ := 0) hfr hgr hes fun s _ ↦ hrecB s
  have hlt {z : ℂ} (hz : ‖z - z₀‖ < r) := eNorm_lt_ofReal_iff.2 hz
  have ha_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s := fun z hz ↦
    (summable_norm_mul_pow_of_lt_radius a ((hlt hz).trans_le har)).of_norm
  have hb_sum : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ b s * (z - z₀) ^ s := fun z hz ↦
    (summable_norm_mul_pow_of_lt_radius b ((hlt hz).trans_le hbr)).of_norm
  have hw₁_op : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv fun w ↦ (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s) z +
        f z * deriv (fun w ↦ (w - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (w - z₀) ^ s) z +
        g z * ((z - z₀) ^ (α₂ + (N : ℂ)) * ∑' s, a s * (z - z₀) ^ s) = 0 := by
    intro z hzs hzb
    rw [deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum hf hg ha_sum hzs hzb]
    simp [hrecA]
  obtain ⟨hw_diff, _, hw_op⟩ := deriv_deriv_add_mul_deriv_add_mul_cpow_mul_tsum_add_log
    (c := c) hf hg ha_sum hb_sum hw₁_op
  refine ⟨hb_sum, by rw [hw]; exact hw_diff, fun z hzs hzb ↦ ?_⟩
  rw [hw, hw_op z hzs hzb]
  simp [hrecB]

/-! ### The Frobenius solution -/

/-- **The Frobenius series solution at a regular singularity** (DLMF 2.7.2–2.7.5). Suppose that
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ` on the punctured disc
`0 < ‖z - z₀‖ < r`. Let `ρ` be a root of the indicial polynomial
`Q(α) = indicialPoly (fs 0) (gs 0) α`, and let
`Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`. Then
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
    (hρ : indicialPoly (fs 0) (gs 0) ρ = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (ρ + s) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k)
    (hw : w = fun z ↦ (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  -- the case `c = 0`, `N = 0`, `α₂ = ρ`, `b = a` of the logarithmic solution
  refine regularSingular_log_solution (c := 0) (N := 0) (α₂ := ρ) (b := a) hf hg hρ (by simp) ha
    (fun s hs ↦ absurd hs (Nat.not_lt_zero s)) (fun s ↦ ?_) (by simp [hw])
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simpa using congrArg (· * a 0) hρ
  · simpa using ha s hs

/-! ### The coefficients of the logarithmic solution -/

/-- **The coefficients of the logarithmic solution** (DLMF 2.7.6). Let `α₁` and `α₂` be the roots
of the indicial polynomial, `Q(α) = indicialPoly (fs 0) (gs 0) α = (α - α₁)(α - α₂)`, with
`α₁ = α₂ + N` for a natural number `N`, and let `a₀ ≠ 0`. Then the recursions of
`TauCeti.regularSingular_log_solution`,

* `Q(α₂ + s) bₛ = -∑_{k < s} ((α₂ + k) f_{s-k} + g_{s-k}) bₖ` for `s < N`, and
* `Q(α₁ + s) b_{s+N} = -∑_{k < s + N} ((α₂ + k) f_{s+N-k} + g_{s+N-k}) bₖ -`
  `c * regularSingularLogForcing fs a α₂ N (s + N)` for all `s`,

have exactly one solution `(b, c)` with DLMF's normalization (`c = 1` when `N = 0`; `b₀ = 1` and
`b_N = 0` when `N ≥ 1`), together with the additional convention `b₀ = 0` when `N = 0`, which
fixes the free multiple of `w₁`. -/
theorem existsUnique_regularSingular_log_coeff {α₁ α₂ : ℂ} {N : ℕ} {fs gs a : ℕ → ℂ}
    (hQ : ∀ α : ℂ, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂)) (hN : α₁ = α₂ + N)
    (ha₀ : a 0 ≠ 0) :
    ∃! bc : (ℕ → ℂ) × ℂ, (N = 0 → bc.2 = 1 ∧ bc.1 0 = 0) ∧ (N ≠ 0 → bc.1 0 = 1 ∧ bc.1 N = 0) ∧
      (∀ s < N, indicialPoly (fs 0) (gs 0) (α₂ + s) * bc.1 s =
        -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * bc.1 k) ∧
      ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (α₁ + s) * bc.1 (s + N) =
        -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * bc.1 k -
          bc.2 * regularSingularLogForcing fs a α₂ N (s + N) := by
  subst hN
  set c : ℂ := if N = 0 then 1 else (a 0)⁻¹ * regularSingularLogMultiplier fs gs α₂ N
  have hc : 1 ≤ N → c * a 0 = regularSingularLogMultiplier fs gs α₂ N := fun hN1 ↦ by
    simp only [c, show N ≠ 0 by omega, ↓reduceIte]
    rw [mul_right_comm, inv_mul_cancel₀ ha₀, one_mul]
  set b := regularSingularLogCoeff fs gs a α₂ c N
  have hrec := regularSingularLogCoeff_rec hQ hc
  refine ⟨(b, c), ?_, ?_⟩
  · exact ⟨fun hN0 ↦ ⟨by simp [c, hN0], by simp [b, hN0]⟩,
      fun hN0 ↦ ⟨regularSingularLogCoeff_zero_of_pos fs gs a α₂ c (Nat.pos_of_ne_zero hN0),
        regularSingularLogCoeff_self fs gs a α₂ c N⟩,
      (forall_regularSingularLogForcing_rec_iff rfl).mp hrec⟩
  · rintro ⟨b', c'⟩ ⟨h0, hne, hlt, hge⟩
    have hb'N : b' N = 0 := by
      rcases eq_or_ne N 0 with rfl | hN0
      · exact (h0 rfl).2
      · exact (hne hN0).2
    obtain ⟨rfl, rfl⟩ := eq_regularSingularLogCoeff_of_rec hQ ha₀ hc hb'N
      (fun hN0 ↦ by simp only [c, hN0, ↓reduceIte]; exact (h0 hN0).1)
      (fun hN1 ↦ (hne (by omega)).1) ((forall_regularSingularLogForcing_rec_iff rfl).mpr ⟨hlt, hge⟩)
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
    (by simp [indicialPoly_def]) (by simp) (fun s hs ↦ ?_) (fun s hs ↦ by omega) (fun s ↦ ?_)
    (by simp)).2.2 z (by simpa using hz) (by simp)
  · have hs0 : s ≠ 0 := by omega
    simp only [hs0, ↓reduceIte, mul_zero]
    rw [eq_comm, neg_eq_zero]
    exact sum_eq_zero fun k hk ↦ by simp [Nat.sub_ne_zero_of_lt (mem_range.1 hk)]
  · rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [indicialPoly_def, regularSingularLogForcing_self]
    · have hs0 : s ≠ 0 := by omega
      simp only [Nat.add_zero, regularSingularLogForcing_of_le _ _ _ (Nat.zero_le s),
        Nat.sub_zero, hs0, ↓reduceIte, Pi.zero_apply, mul_zero, sum_const_zero, neg_zero,
        zero_sub, one_mul, zero_add]
      rw [eq_comm, neg_eq_zero]
      refine sum_eq_zero fun k hk ↦ ?_
      rcases eq_or_ne k 0 with rfl | hk0
      · simp [hs0]
      · simp [hk0]

/-! ### The Wronskian -/

/-- The points `z₀ + t` with `0 < t < r` lie in the slit punctured disc. -/
private theorem add_ofReal_mem_slitDisc {z₀ : ℂ} {t r : ℝ} (ht : 0 < t) (htr : t < r) :
    z₀ + t ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} := by
  refine ⟨by simpa using ofReal_mem_slitPlane.2 ht, ?_⟩
  rwa [add_sub_cancel_left, norm_real, Real.norm_of_nonneg ht.le]

/-- **Abel's identity with its integrating factor.** In the setting of
`TauCeti.exists_wronskian_eq_of_regularSingular`, the product of the Wronskian `W = w₁ w₂' - w₁' w₂`
with `(z - z₀)^{f₀} exp(Φ(z - z₀))`, where `Φ(ζ) = ∑_{s ≥ 1} fₛ ζˢ / s`, has derivative zero at
every point of the slit punctured disc: `W' = -f W` and `f = f₀ / ζ + Φ'(ζ)`. -/
private theorem hasDerivAt_abelExponent_mul_wronskian {z₀ x : ℂ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ}
    {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hd₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hd₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (he₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (he₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0)
    (hx : x ∈ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}) :
    HasDerivAt (fun z ↦ (z - z₀) ^ fs 0 *
      cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) *
      (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)) 0 x := by
  have hDo := isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  have hfr := le_radius_ofScalars_of_summable_sub fs fun z h0 hz ↦ (hf z h0 hz).summable
  have hU := hDo.mem_nhds hx
  obtain ⟨hx, hxr⟩ := hx
  have hx0 : x - z₀ ≠ 0 := slitPlane_ne_zero hx
  have h1 := (hd₁.differentiableAt hU).hasDerivAt
  have h2 := (hd₂.differentiableAt hU).hasDerivAt
  have h1' := ((hd₁.deriv hDo).differentiableAt hU).hasDerivAt
  have h2' := ((hd₂.deriv hDo).differentiableAt hU).hasDerivAt
  have hp := ((hasDerivAt_id' x).sub_const z₀).cpow_const (c := fs 0) hx
  have hE := ((hasDerivAt_tsum_div_mul_pow_succ hx0 ((eNorm_lt_ofReal_iff.2 hxr).trans_le hfr)
    (hf x (norm_pos_iff.2 hx0) hxr)).comp_sub_const x z₀).cexp
  convert (hp.fun_mul hE).fun_mul ((h1.fun_mul h2').fun_sub (h1'.fun_mul h2)) using 1
  have ep : (x - z₀) ^ (fs 0 - 1) = (x - z₀) ^ fs 0 * (x - z₀)⁻¹ := by
    rw [cpow_sub _ _ hx0, cpow_one, div_eq_mul_inv]
  rw [ep]
  -- `W' = w₁ w₂'' - w₁'' w₂ = -f W` by the equation, and the factor contributes
  -- `(f₀ / ζ + Φ'(ζ)) = f` times itself, with `Φ'(ζ) = (ζ f - f₀) / ζ`
  linear_combination
    (-((x - z₀) ^ fs 0 * cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (x - z₀) ^ (s + 1)))) *
    (w₁ x * he₂ x hx hxr - w₂ x * he₁ x hx hxr +
      f x * (w₁ x * deriv w₂ x - deriv w₁ x * w₂ x) * mul_inv_cancel₀ hx0)

/-- **Abel's formula at a regular singularity.** Suppose that `(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` on
the punctured disc `0 < ‖z - z₀‖ < r`, and let `w₁` and `w₂` be holomorphic solutions of
`w'' + f w' + g w = 0` on the slit punctured disc `{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`. Then
there is a constant `C` such that on the slit punctured disc their Wronskian is
`w₁ w₂' - w₁' w₂ = C (z - z₀)^{-f₀} exp(-∑_{s ≥ 1} fₛ (z - z₀)ˢ / s)`, with the principal
power. -/
theorem exists_wronskian_eq_of_regularSingular {z₀ : ℂ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ}
    {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hd₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hd₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (he₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (he₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) :
    ∃ C : ℂ, ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z =
        C * (z - z₀) ^ (-fs 0) * cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  set D := {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨0, fun z _ hz ↦ absurd ((norm_nonneg _).trans_lt hz) hr.not_gt⟩
  have hz₁ : z₀ + ((r / 2 : ℝ) : ℂ) ∈ D := add_ofReal_mem_slitDisc (by positivity) (by linarith)
  have hDc : IsPreconnected D := isPreconnected_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r
  -- `K = (z - z₀)^{f₀} exp(Φ(z - z₀)) W` has derivative zero on `D`, by Abel's identity
  set K : ℂ → ℂ := fun z ↦ (z - z₀) ^ fs 0 *
    cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) *
    (w₁ z * deriv w₂ z - deriv w₁ z * w₂ z)
  have hK (x : ℂ) (hx : x ∈ D) : HasDerivAt K 0 x :=
    hasDerivAt_abelExponent_mul_wronskian hf hd₁ hd₂ he₁ he₂ hx
  refine ⟨K (z₀ + ((r / 2 : ℝ) : ℂ)), fun z hz hzr ↦ ?_⟩
  rw [← (isOpen_setOf_sub_mem_slitPlane_and_norm_sub_lt z₀ r).is_const_of_deriv_eq_zero hDc
    (fun x hx ↦ (hK x hx).differentiableAt.differentiableWithinAt) (fun x hx ↦ (hK x hx).deriv)
    ⟨hz, hzr⟩ hz₁]
  simp only [K]
  have hz0 : z - z₀ ≠ 0 := slitPlane_ne_zero hz
  have hp0 : (z - z₀) ^ fs 0 ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hz0)
  rw [cpow_neg, Complex.exp_neg]
  field_simp

/-- Abel's formula with its constant identified: if the Wronskian of two solutions is
`(z - z₀)^{-f₀} H(z - z₀)` on the slit punctured disc, with `H` continuous at `0`, then the constant
of `TauCeti.exists_wronskian_eq_of_regularSingular` is `H(0)`. -/
private theorem wronskian_eq_of_regularSingular_of_continuousAt {z₀ : ℂ} {r : ℝ}
    {f g w₁ w₂ H : ℂ → ℂ} {fs : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hd₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hd₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (he₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (he₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0) (hH : ContinuousAt H 0)
    (hW : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      w₁ z * deriv w₂ z - deriv w₁ z * w₂ z = (z - z₀) ^ (-fs 0) * H (z - z₀))
    {z : ℂ} (hz : z - z₀ ∈ slitPlane) (hzr : ‖z - z₀‖ < r) :
    w₁ z * deriv w₂ z - deriv w₁ z * w₂ z =
      H 0 * (z - z₀) ^ (-fs 0) * cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hzr
  obtain ⟨C, hC⟩ := exists_wronskian_eq_of_regularSingular hf hd₁ hd₂ he₁ he₂
  have hΦ := hasFPowerSeriesOnBall_tsum_div_mul_pow_succ fs (ENNReal.ofReal_pos.2 hr)
    (le_radius_ofScalars_of_summable_sub fs fun z h0 hz ↦ (hf z h0 hz).summable)
  -- along `z = z₀ + t`, `t → 0+`, the constant `C` is `H(t) exp(Φ(t)) → H(0)`
  have hlim : Tendsto (fun t : ℝ ↦ H t * cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (t : ℂ) ^ (s + 1)))
      (𝓝[>] 0) (𝓝 (H 0)) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    simpa [Function.comp_def] using (hH.mul hΦ.analyticAt.continuousAt.cexp).tendsto.comp
      (continuous_ofReal.tendsto' 0 0 ofReal_zero)
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      C = H t * cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (t : ℂ) ^ (s + 1)) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    obtain ⟨ht', htr⟩ := add_ofReal_mem_slitDisc (z₀ := z₀) ht.1 ht.2
    have h := (hW _ ht' htr).symm.trans (hC _ ht' htr)
    rw [add_sub_cancel_left] at h
    have hp0 : (t : ℂ) ^ (-fs 0) ≠ 0 :=
      cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 ht.1.ne'))
    rw [Complex.exp_neg] at h
    generalize hE : cexp (∑' s : ℕ, fs (s + 1) / (s + 1) * (t : ℂ) ^ (s + 1)) = E at h ⊢
    have hE0 : E ≠ 0 := hE ▸ Complex.exp_ne_zero _
    field_simp at h
    linear_combination -h
  obtain rfl := tendsto_nhds_unique (tendsto_const_nhds.congr' heq) hlim
  exact hC z hz hzr

/-- The Wronskian of `w₁(z) = (z - z₀)^{α₁} ∑ aₛ (z - z₀)ˢ` and
`w₂(z) = (z - z₀)^{α₂} ∑ bₛ (z - z₀)ˢ + c w₁(z) log (z - z₀)`, two solutions whose series converge
on the disc, where `-f₀ = α₁ + α₂ - 1` and `c = 0` or `α₁ = α₂ + N`: on the slit punctured disc,
`w₁ w₂' - w₁' w₂ = ((α₂ - α₁) a₀ b₀ + c 0ᴺ a₀²) (z - z₀)^{-f₀} exp(-∑_{s ≥ 1} fₛ (z - z₀)ˢ / s)`.
-/
private theorem wronskian_eq_of_regularSingular_of_tsum {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ}
    {f g w₁ w₂ : ℂ → ℂ} {fs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hd₁ : DifferentiableOn ℂ w₁ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (hd₂ : DifferentiableOn ℂ w₂ {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r})
    (he₁ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z = 0)
    (he₂ : ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z = 0)
    (hf₀ : -fs 0 = α₁ + α₂ - 1) (hc : c = 0 ∨ α₁ = α₂ + N)
    (hsa : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s)
    (hsb : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ b s * (z - z₀) ^ s)
    (hw₁ : w₁ = fun z ↦ (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s)
    (hw₂ : w₂ = fun z ↦ (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) +
      c * ((z - z₀) ^ α₁ * (∑' s, a s * (z - z₀) ^ s) * log (z - z₀)))
    {z : ℂ} (hz : z - z₀ ∈ slitPlane) (hzr : ‖z - z₀‖ < r) :
    w₁ z * deriv w₂ z - deriv w₁ z * w₂ z = ((α₂ - α₁) * a 0 * b 0 + c * 0 ^ N * a 0 ^ 2) *
      (z - z₀) ^ (-fs 0) * cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hzr
  -- the two series as functions on the disc of radius `r` about the origin
  set S : ℂ → ℂ := fun y ↦ ∑' s, a s * y ^ s
  set T : ℂ → ℂ := fun y ↦ ∑' s, b s * y ^ s
  have hS := hasFPowerSeriesOnBall_tsum_mul_pow a (ENNReal.ofReal_pos.2 hr)
    (le_radius_ofScalars_of_summable_sub a fun z _ hz ↦ hsa z hz)
  have hT := hasFPowerSeriesOnBall_tsum_mul_pow b (ENNReal.ofReal_pos.2 hr)
    (le_radius_ofScalars_of_summable_sub b fun z _ hz ↦ hsb z hz)
  have hcS := hS.analyticAt.continuousAt
  have hcT := hT.analyticAt.continuousAt
  have hcS' := hS.analyticAt.deriv.continuousAt
  have hcT' := hT.analyticAt.deriv.continuousAt
  -- the Wronskian is `(z - z₀)^{-f₀} H(z - z₀)` with `H` continuous at `0`
  have hH : ContinuousAt (fun y ↦ (α₂ - α₁) * S y * T y +
      y * (S y * deriv T y - deriv S y * T y) + c * y ^ N * S y ^ 2) 0 := by
    fun_prop
  refine (wronskian_eq_of_regularSingular_of_continuousAt hf hd₁ hd₂ he₁ he₂ hH
    (fun x hx hxr ↦ ?_) hz hzr).trans ?_
  · have hd₁ : deriv w₁ x = deriv (fun y ↦ y ^ α₁ * S y) (x - z₀) := by
      rw [hw₁]
      exact deriv_comp_sub_const (fun y ↦ y ^ α₁ * S y) z₀ x
    have hd₂ : deriv w₂ x =
        deriv (fun y ↦ y ^ α₂ * T y + c * (y ^ α₁ * S y * log y)) (x - z₀) := by
      rw [hw₂]
      exact deriv_comp_sub_const (fun y ↦ y ^ α₂ * T y + c * (y ^ α₁ * S y * log y)) z₀ x
    rw [hd₁, hd₂, hw₁, hw₂]
    dsimp only
    rw [wronskian_cpow_mul_log_eq (fun u hu ↦ by simpa using hsa (z₀ + u) (by simpa using hu))
      (fun u hu ↦ by simpa using hsb (z₀ + u) (by simpa using hu)) hc hx hxr, hf₀]
  · have hS0 : S 0 = a 0 := by simpa using (hS.coeff_zero ![]).symm
    have hT0 : T 0 = b 0 := by simpa using (hT.coeff_zero ![]).symm
    simp only [hS0, hT0, zero_mul, add_zero]

/-- **The Wronskian of the logarithmic solution** (DLMF 2.7.6). In the setting of
`TauCeti.regularSingular_log_solution`, let `α₁` and `α₂ = α₁ - N` be the two roots of the
indicial polynomial, `Q(α) = indicialPoly (fs 0) (gs 0) α = (α - α₁)(α - α₂)`, let
`w₁(z) = (z - z₀)^{α₁} ∑ aₛ (z - z₀)ˢ` be the Frobenius solution at `α₁`, and let
`w₂(z) = (z - z₀)^{α₂} ∑ bₛ (z - z₀)ˢ + c w₁(z) log (z - z₀)` be the logarithmic solution. Then on
the slit punctured disc

`w₁ w₂' - w₁' w₂ = (c 0ᴺ a₀ - N b₀) a₀ (z - z₀)^{-f₀} exp(-∑_{s ≥ 1} fₛ (z - z₀)ˢ / s)`,

that is `c a₀²` times the exponential factor when `N = 0`, and `-N a₀ b₀` times it when `N ≥ 1`. -/
theorem regularSingular_log_wronskian {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ}
    {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hQ : ∀ α : ℂ, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂)) (hN : α₁ = α₂ + N)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) * a s =
      -∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k)
    (hb : ∀ s < N, indicialPoly (fs 0) (gs 0) (α₂ + s) * b s =
      -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k)
    (hb' : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (α₁ + s) * b (s + N) =
      -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * b k -
        c * regularSingularLogForcing fs a α₂ N (s + N))
    (hw₁ : w₁ = fun z ↦ (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s)
    (hw₂ : w₂ = fun z ↦ (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) +
      c * ((z - z₀) ^ α₁ * (∑' s, a s * (z - z₀) ^ s) * log (z - z₀)))
    {z : ℂ} (hz : z - z₀ ∈ slitPlane) (hzr : ‖z - z₀‖ < r) :
    w₁ z * deriv w₂ z - deriv w₁ z * w₂ z = (c * 0 ^ N * a 0 - N * b 0) * a 0 *
      (z - z₀) ^ (-fs 0) * cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  have hα₁ : indicialPoly (fs 0) (gs 0) α₁ = 0 := by rw [hQ, sub_self, zero_mul]
  have hf₀ : -fs 0 = α₁ + α₂ - 1 := by
    linear_combination -(forall_indicialPoly_eq_sub_mul_sub_iff.mp hQ).1
  obtain ⟨hsa, hd₁, he₁⟩ := regularSingular_solution hf hg hα₁ ha hw₁
  obtain ⟨hsb, hd₂, he₂⟩ := regularSingular_log_solution hf hg hα₁ hN ha hb hb' hw₂
  rw [wronskian_eq_of_regularSingular_of_tsum hf hd₁ hd₂ he₁ he₂ hf₀ (.inr hN) hsa hsb hw₁ hw₂
    hz hzr, hN]
  ring

/-- **The Wronskian of the logarithmic solution vanishes nowhere.** In the setting of
`TauCeti.regularSingular_log_wronskian`, if `a₀ ≠ 0`, and `c ≠ 0` when `N = 0` and `b₀ ≠ 0` when
`N ≥ 1` (as for DLMF's normalization `c = 1`, respectively `b₀ = 1`), the Wronskian
`w₁ w₂' - w₁' w₂` is nonzero at every point of the slit punctured disc. -/
theorem regularSingular_log_wronskian_ne_zero {z₀ α₁ α₂ c : ℂ} {N : ℕ} {r : ℝ}
    {f g w₁ w₂ : ℂ → ℂ} {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hQ : ∀ α : ℂ, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂)) (hN : α₁ = α₂ + N)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) * a s =
      -∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k)
    (hb : ∀ s < N, indicialPoly (fs 0) (gs 0) (α₂ + s) * b s =
      -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k)
    (hb' : ∀ s : ℕ, indicialPoly (fs 0) (gs 0) (α₁ + s) * b (s + N) =
      -∑ k ∈ range (s + N), ((α₂ + k) * fs (s + N - k) + gs (s + N - k)) * b k -
        c * regularSingularLogForcing fs a α₂ N (s + N))
    (ha₀ : a 0 ≠ 0) (hc : N = 0 → c ≠ 0) (hb₀ : N ≠ 0 → b 0 ≠ 0)
    (hw₁ : w₁ = fun z ↦ (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s)
    (hw₂ : w₂ = fun z ↦ (z - z₀) ^ α₂ * (∑' s, b s * (z - z₀) ^ s) +
      c * ((z - z₀) ^ α₁ * (∑' s, a s * (z - z₀) ^ s) * log (z - z₀)))
    {z : ℂ} (hz : z - z₀ ∈ slitPlane) (hzr : ‖z - z₀‖ < r) :
    w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  rw [regularSingular_log_wronskian hf hg hQ hN ha hb hb' hw₁ hw₂ hz hzr]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ha₀)
    (cpow_ne_zero_iff.2 (Or.inl (slitPlane_ne_zero hz)))) (Complex.exp_ne_zero _)
  rcases eq_or_ne N 0 with rfl | hN0
  · simpa using mul_ne_zero (hc rfl) ha₀
  · simpa [hN0] using hb₀ hN0

/-- **The Wronskian of two Frobenius solutions** (DLMF 2.7.4). In the setting of
`TauCeti.regularSingular_solution`, let `α₁` and `α₂` be the two roots of the indicial polynomial,
`Q(α) = indicialPoly (fs 0) (gs 0) α = (α - α₁)(α - α₂)`, and let
`w₁(z) = (z - z₀)^{α₁} ∑ aₛ (z - z₀)ˢ` and `w₂(z) = (z - z₀)^{α₂} ∑ bₛ (z - z₀)ˢ` be Frobenius
solutions at `α₁` and at `α₂`. Then on the slit punctured disc

`w₁ w₂' - w₁' w₂ = (α₂ - α₁) a₀ b₀ (z - z₀)^{-f₀} exp(-∑_{s ≥ 1} fₛ (z - z₀)ˢ / s)`. -/
theorem regularSingular_wronskian {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ}
    {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hQ : ∀ α : ℂ, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂))
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) * a s =
      -∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k)
    (hb : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) * b s =
      -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k)
    (hw₁ : w₁ = fun z ↦ (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s)
    (hw₂ : w₂ = fun z ↦ (z - z₀) ^ α₂ * ∑' s, b s * (z - z₀) ^ s)
    {z : ℂ} (hz : z - z₀ ∈ slitPlane) (hzr : ‖z - z₀‖ < r) :
    w₁ z * deriv w₂ z - deriv w₁ z * w₂ z = (α₂ - α₁) * a 0 * b 0 * (z - z₀) ^ (-fs 0) *
      cexp (-∑' s : ℕ, fs (s + 1) / (s + 1) * (z - z₀) ^ (s + 1)) := by
  have hf₀ : -fs 0 = α₁ + α₂ - 1 := by
    linear_combination -(forall_indicialPoly_eq_sub_mul_sub_iff.mp hQ).1
  obtain ⟨hsa, hd₁, he₁⟩ := regularSingular_solution hf hg (by rw [hQ, sub_self, zero_mul]) ha hw₁
  obtain ⟨hsb, hd₂, he₂⟩ := regularSingular_solution hf hg (by rw [hQ, sub_self, mul_zero]) hb hw₂
  -- the case `c = 0` of the logarithmic solution
  rw [wronskian_eq_of_regularSingular_of_tsum (c := 0) (N := 0) hf hd₁ hd₂ he₁ he₂ hf₀
    (.inl rfl) hsa hsb hw₁ (by simpa using hw₂) hz hzr]
  ring

/-- **The Wronskian of two Frobenius solutions vanishes nowhere.** In the setting of
`TauCeti.regularSingular_wronskian`, if the roots `α₁ ≠ α₂` are distinct and `a₀ ≠ 0 ≠ b₀`, the
Wronskian `w₁ w₂' - w₁' w₂` is nonzero at every point of the slit punctured disc. -/
theorem regularSingular_wronskian_ne_zero {z₀ α₁ α₂ : ℂ} {r : ℝ} {f g w₁ w₂ : ℂ → ℂ}
    {fs gs a b : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hQ : ∀ α : ℂ, indicialPoly (fs 0) (gs 0) α = (α - α₁) * (α - α₂)) (hα : α₁ ≠ α₂)
    (ha : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₁ + s) * a s =
      -∑ k ∈ range s, ((α₁ + k) * fs (s - k) + gs (s - k)) * a k)
    (hb : ∀ s : ℕ, 1 ≤ s → indicialPoly (fs 0) (gs 0) (α₂ + s) * b s =
      -∑ k ∈ range s, ((α₂ + k) * fs (s - k) + gs (s - k)) * b k)
    (ha₀ : a 0 ≠ 0) (hb₀ : b 0 ≠ 0)
    (hw₁ : w₁ = fun z ↦ (z - z₀) ^ α₁ * ∑' s, a s * (z - z₀) ^ s)
    (hw₂ : w₂ = fun z ↦ (z - z₀) ^ α₂ * ∑' s, b s * (z - z₀) ^ s)
    {z : ℂ} (hz : z - z₀ ∈ slitPlane) (hzr : ‖z - z₀‖ < r) :
    w₁ z * deriv w₂ z - deriv w₁ z * w₂ z ≠ 0 := by
  rw [regularSingular_wronskian hf hg hQ ha hb hw₁ hw₂ hz hzr]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hα.symm) ha₀) hb₀)
    (cpow_ne_zero_iff.2 (Or.inl (slitPlane_ne_zero hz)))) (Complex.exp_ne_zero _)

end TauCeti
