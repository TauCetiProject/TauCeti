/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import TauCeti.Data.Nat.Choose.Sum

/-!
# Frobenius series solutions at a regular singularity

Consider the equation `w'' + f(z) w' + g(z) w = 0` near a point `z₀` at which `f` has at most a
simple pole and `g` at most a double pole, so that on a punctured disc `0 < |z - z₀| < r`

* `(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and
* `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ`,

with both series convergent there. Its indicial polynomial is `Q(α) = α (α - 1) + f₀ α + g₀`.
Let `ρ` be a root of `Q` such that no `ρ + s` with `s ≥ 1` is a root, and let `a₀ = 1` and

`Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`

(DLMF 2.7.5). Then the series `∑ aₛ (z - z₀)ˢ` converges on the whole disc `|z - z₀| < r`
(`TauCeti.le_radius_ofScalars_of_regularSingular`), and the Frobenius series
`w(z) = (z - z₀)^ρ ∑ aₛ (z - z₀)ˢ`, with the principal power, is holomorphic and solves the equation
on the slit punctured disc `{z | z - z₀ ∈ slitPlane, |z - z₀| < r}` (DLMF 2.7.4;
`TauCeti.regularSingular_solution`).

The root `ρ` always qualifies when it is the root of larger real part, and so does the other root
when the two roots do not differ by an integer. The normalization `a₀ = 1` is customary; the
statements hold for every `a₀`. For example, Bessel's equation, with `f(z) = 1/z` and
`g(z) = 1 - ν²/z²` at `z₀ = 0`, has the indicial roots `±ν`, and when `2ν` is not a negative
integer the solution at `ρ = ν` is a constant multiple of the Bessel function `J_ν`.

## Implementation notes

Convergence is proved by a majorant argument. Since `Q(ρ) = 0`, `Q(ρ + s) = s (s + β)` with
`β = 2ρ - 1 + f₀`, and `|s + β| ≥ c s` for some `c > 0` and all `s ≥ 1`. For `t` below the radius
of convergence of the coefficient series, `|aₛ| tˢ` is then bounded by `|a₀|` times the binomial
coefficient `C(s + m, m)` for a fixed `m`. The equation is verified on coefficients: in terms of
the Euler operator `ζ d/dζ`, `(z - z₀)^{2 - ρ}` times the left-hand side is the power series whose
coefficient of index `s` is `Q(ρ + s) aₛ + ∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ`, a Cauchy
product of absolutely convergent series.

## References

* NIST Digital Library of Mathematical Functions, §2.7(i), equations (2.7.2)–(2.7.5),
  <https://dlmf.nist.gov/2.7.i>.
* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §§4–5.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 4, §§3–4.
-/

public section

open Complex Filter Finset FormalMultilinearSeries Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Convergence of the Frobenius series -/

/-- At a root `ρ` of the indicial polynomial, `Q(ρ + s) = s (s + (2ρ - 1 + f₀))`. -/
private theorem indicial_add_eq_mul {ρ f₀ g₀ : ℂ} (hρ : ρ * (ρ - 1) + f₀ * ρ + g₀ = 0) (s : ℂ) :
    (ρ + s) * (ρ + s - 1) + f₀ * (ρ + s) + g₀ = s * (s + (2 * ρ - 1 + f₀)) := by
  linear_combination hρ

/-- If `s + β` never vanishes for `s ≥ 1`, then `|s + β|` is bounded below by a positive multiple
of `s` for all `s ≥ 1`. -/
private theorem exists_pos_mul_le_norm_natCast_add {β : ℂ}
    (hβ : ∀ s : ℕ, 1 ≤ s → (s : ℂ) + β ≠ 0) :
    ∃ c > 0, ∀ s : ℕ, 1 ≤ s → c * s ≤ ‖(s : ℂ) + β‖ := by
  -- beyond `N` the bound `c = 1/2` holds; below it, take the least ratio `|s + β| / s`
  set N := ⌈2 * ‖β‖⌉₊ + 1
  obtain ⟨s₀, hs₀, hmin⟩ := (Icc 1 N).exists_min_image (fun s : ℕ ↦ ‖(s : ℂ) + β‖ / s)
    ⟨1, mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hs₀1 : (0 : ℝ) < s₀ := by exact_mod_cast (mem_Icc.1 hs₀).1
  have hpos : 0 < ‖(s₀ : ℂ) + β‖ / s₀ :=
    div_pos (norm_pos_iff.2 (hβ s₀ (mem_Icc.1 hs₀).1)) hs₀1
  refine ⟨min (1 / 2) (‖(s₀ : ℂ) + β‖ / s₀), lt_min (by norm_num) hpos, fun s hs ↦ ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases hsN : s ≤ N
  · calc min (1 / 2) (‖(s₀ : ℂ) + β‖ / s₀) * s ≤ (‖(s : ℂ) + β‖ / s) * s := by
          gcongr
          exact (min_le_right _ _).trans (hmin s (mem_Icc.2 ⟨hs, hsN⟩))
      _ = ‖(s : ℂ) + β‖ := div_mul_cancel₀ _ hs'.ne'
  · have hceil : 2 * ‖β‖ ≤ s := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : _ ≤ s))
    have htri : (s : ℝ) ≤ ‖(s : ℂ) + β‖ + ‖β‖ := by
      simpa using norm_sub_le ((s : ℂ) + β) β
    calc min (1 / 2) (‖(s₀ : ℂ) + β‖ / s₀) * s ≤ 1 / 2 * s := by
          gcongr
          exact min_le_left _ _
      _ ≤ ‖(s : ℂ) + β‖ := by linarith

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

/-- The majorant bound: if `|s + β| ≥ c s` for `s ≥ 1` and the coefficients `fₛ tˢ`, `gₛ tˢ` are
bounded by `M`, then `|aₛ| tˢ ≤ |a₀| C(s + m, m)` as soon as `(|ρ| + 1) M ≤ c m`. -/
private theorem norm_mul_pow_le_mul_choose {ρ β : ℂ} {fs gs a : ℕ → ℂ} {t M c : ℝ} {m : ℕ}
    (ht : 0 ≤ t) (hc : 0 < c) (hcs : ∀ s : ℕ, 1 ≤ s → c * s ≤ ‖(s : ℂ) + β‖)
    (hfs : ∀ n, ‖fs n‖ * t ^ n ≤ M) (hgs : ∀ n, ‖gs n‖ * t ^ n ≤ M)
    (hm : (‖ρ‖ + 1) * M ≤ c * m)
    (ha : ∀ s : ℕ, 1 ≤ s → (s * (s + β)) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) (n : ℕ) :
    ‖a n‖ * t ^ n ≤ ‖a 0‖ * (n + m).choose m := by
  have hM : 0 ≤ M := (by positivity : 0 ≤ ‖fs 0‖ * t ^ 0).trans (hfs 0)
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · simp
    have hbinom : (1 : ℝ) + m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ) ≤
        (n + 1) * ((n + 1 + m).choose m : ℝ) := by
      exact_mod_cast Nat.one_add_mul_sum_range_add_choose_le n m
    have hcn : c * (n + 1) ≤ ‖((n + 1 : ℕ) : ℂ) + β‖ := by exact_mod_cast hcs (n + 1) (by omega)
    -- bound `c (n + 1)² |a_{n+1}| t^{n+1}` through the recursion and the hockey-stick identity
    have hkey : c * (n + 1) * ((n + 1) * (‖a (n + 1)‖ * t ^ (n + 1))) ≤
        c * (n + 1) * ((n + 1) * (‖a 0‖ * ((n + 1 + m).choose m : ℝ))) := by
      calc c * (n + 1) * ((n + 1) * (‖a (n + 1)‖ * t ^ (n + 1)))
          ≤ ‖(((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) + β)) * a (n + 1)‖ * t ^ (n + 1) := by
            have hX := mul_nonneg (norm_nonneg (a (n + 1))) (pow_nonneg ht (n + 1))
            have := mul_le_mul_of_nonneg_right hcn (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) hX)
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            push_cast at this ⊢
            linarith
        _ ≤ ∑ k ∈ range (n + 1),
              ‖((ρ + k) * fs (n + 1 - k) + gs (n + 1 - k)) * a k‖ * t ^ (n + 1) := by
            rw [ha (n + 1) (by omega), norm_neg, ← sum_mul]
            gcongr
            exact norm_sum_le _ _
        _ ≤ ∑ k ∈ range (n + 1), (‖ρ‖ + 1) * (n + 1) * M * (‖a 0‖ * ((k + m).choose m : ℝ)) :=
            sum_le_sum fun k hk ↦ norm_recursion_term_mul_pow_le ht hM hfs hgs
              (mem_range_succ_iff.1 hk) (ih k (by simp at hk; omega))
        _ = (n + 1) * ‖a 0‖ * ((‖ρ‖ + 1) * M * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)) := by
            rw [← mul_sum, ← mul_sum]
            ring
        _ ≤ (n + 1) * ‖a 0‖ * (c * ((n + 1) * ((n + 1 + m).choose m : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc (‖ρ‖ + 1) * M * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ)
                ≤ c * m * ∑ k ∈ range (n + 1), ((k + m).choose m : ℝ) := by gcongr
              _ ≤ c * ((n + 1) * ((n + 1 + m).choose m : ℝ)) := by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left (by linarith) hc.le
        _ = c * (n + 1) * ((n + 1) * (‖a 0‖ * ((n + 1 + m).choose m : ℝ))) := by ring
    have h := le_of_mul_le_mul_left (le_of_mul_le_mul_left hkey (by positivity)) (by positivity)
    simpa [add_right_comm n 1 m] using h

/-- **Convergence of the Frobenius series.** Let `ρ` be a root of the indicial polynomial
`Q(α) = α (α - 1) + f₀ α + g₀` such that no `ρ + s` with `s ≥ 1` is a root, and let the
coefficients `aₛ` satisfy `Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} + g_{s-k}) aₖ` for `s ≥ 1`
(DLMF 2.7.5). Then the radius of convergence of `∑ aₛ zˢ` is at least every `r` that bounds
from below the radii of convergence of both `∑ fₛ zˢ` and `∑ gₛ zˢ`. -/
theorem le_radius_ofScalars_of_regularSingular {ρ : ℂ} {fs gs a : ℕ → ℂ} {r : ℝ≥0∞}
    (hfs : r ≤ (ofScalars ℂ fs).radius) (hgs : r ≤ (ofScalars ℂ gs).radius)
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → (ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0 ≠ 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
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
  simp only [ofScalars_norm] at hMf hMg
  set β : ℂ := 2 * ρ - 1 + fs 0
  have hQ (s : ℕ) : (ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0 = s * (s + β) :=
    indicial_add_eq_mul hρ s
  obtain ⟨c, hc, hcs⟩ := exists_pos_mul_le_norm_natCast_add (β := β) fun s hs ↦
    (mul_ne_zero_iff.mp (hQ s ▸ hres s hs)).2
  obtain ⟨m, hm⟩ := exists_nat_ge ((‖ρ‖ + 1) * max Mf Mg / c)
  have hm' : (‖ρ‖ + 1) * max Mf Mg ≤ c * m := by
    rw [div_le_iff₀ hc] at hm
    linarith
  have hbound := norm_mul_pow_le_mul_choose (a := a) t.property hc hcs
    (fun n ↦ (hMf n).trans (le_max_left _ _)) (fun n ↦ (hMg n).trans (le_max_right _ _)) hm'
    (fun s hs ↦ hQ s ▸ ha s hs)
  -- compare with `‖a₀‖ ∑ C(n + m, m) qⁿ` for `q = R / t < 1`
  set q : ℝ := R / t
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact (div_lt_one ht).mpr hRt
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
    ((summable_choose_mul_geometric_of_norm_lt_one m hq).mul_left ‖a 0‖)
  rw [ofScalars_norm, show (R : ℝ) = t * q from (mul_div_cancel₀ _ ht.ne').symm, mul_pow,
    ← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)

/-! ### The Frobenius series solves the equation -/

/-- The coefficient of `ζⁿ` in the Euler-operator form of the equation vanishes, by the
recursion and, for `n = 0`, by the indicial equation. -/
private theorem euler_form_coeff_eq_zero {ρ ζ : ℂ} {fs gs a : ℕ → ℂ}
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) (n : ℕ) :
    ρ * (ρ - 1) * (a n * ζ ^ n) + 2 * ρ * (n * a n * ζ ^ n) + n * (n - 1) * a n * ζ ^ n +
        ∑ k ∈ range (n + 1), (ρ + k) * a k * ζ ^ k * (fs (n - k) * ζ ^ (n - k)) +
      ∑ k ∈ range (n + 1), a k * ζ ^ k * (gs (n - k) * ζ ^ (n - k)) = 0 := by
  have hsum (u v : ℕ → ℂ) : ∑ k ∈ range (n + 1), u k * ζ ^ k * (v (n - k) * ζ ^ (n - k)) =
      ζ ^ n * ∑ k ∈ range (n + 1), u k * v (n - k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [← pow_mul_pow_sub ζ (mem_range_succ_iff.mp hk)]
    ring
  have hrec : ((ρ + n) * (ρ + n - 1) + fs 0 * (ρ + n) + gs 0) * a n +
      ∑ k ∈ range n, ((ρ + k) * fs (n - k) + gs (n - k)) * a k = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using congrArg (· * a 0) hρ
    · rw [ha n hn, neg_add_cancel]
  have hsplit : ∑ k ∈ range n, ((ρ + k) * fs (n - k) + gs (n - k)) * a k =
      ∑ k ∈ range n, (ρ + k) * a k * fs (n - k) + ∑ k ∈ range n, a k * gs (n - k) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  rw [hsplit] at hrec
  rw [hsum (fun k ↦ (ρ + k) * a k), hsum a, sum_range_succ, sum_range_succ, Nat.sub_self]
  linear_combination ζ ^ n * hrec

/-- The Euler-operator form of the equation, at a point `ζ` of the disc: with `S = ∑ aₛ ζˢ`,
`F = ∑ fₛ ζˢ` and `G = ∑ gₛ ζˢ`, the expression below, which is `ζ^{2 - ρ}` times the left-hand
side of the equation applied to `ζ^ρ S`, vanishes. -/
private theorem euler_form_eq_zero {ρ ζ F G : ℂ} {fs gs a : ℕ → ℂ} {S : ℂ → ℂ} {R : ℝ≥0∞}
    (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R) (hζ : ‖ζ‖ₑ < R)
    (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius) (hζg : ‖ζ‖ₑ < (ofScalars ℂ gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) F) (hG : HasSum (fun s ↦ gs s * ζ ^ s) G)
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
    ρ * (ρ - 1) * S ζ + 2 * ρ * (ζ * deriv S ζ) + ζ ^ 2 * deriv (deriv S) ζ +
      F * (ρ * S ζ + ζ * deriv S ζ) + G * S ζ = 0 := by
  -- the series of `S`, of `ζ S'` and of `ζ² S''`
  have h0 : HasSum (fun n ↦ a n * ζ ^ n) (S ζ) := by
    simpa [ofScalars_apply_eq, mul_comm] using hS.hasSum (mem_eball_zero_iff.mpr hζ)
  have h1 := hS.hasSum_mul_deriv_ofScalars hζ
  have h2 := hS.hasSum_sq_mul_deriv_deriv_ofScalars hζ
  -- absolute convergence of the factors of the two Cauchy products
  have hA : Summable fun n ↦ ‖a n * ζ ^ n‖ := by
    simpa [ofScalars_apply_eq, mul_comm] using
      (ofScalars ℂ a).summable_norm_apply (mem_eball_zero_iff.mpr (hζ.trans_le hS.r_le))
  have hP : Summable fun n : ℕ ↦ ‖(ρ + n) * a n * ζ ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((hA.mul_left ‖ρ‖).add (hS.summable_norm_natCast_mul_ofScalars hζ))
    rw [add_mul, add_mul]
    refine (norm_add_le _ _).trans_eq ?_
    rw [mul_assoc ρ, norm_mul]
  have hfN : Summable fun n ↦ ‖fs n * ζ ^ n‖ := by
    simpa [ofScalars_apply_eq, mul_comm] using
      (ofScalars ℂ fs).summable_norm_apply (mem_eball_zero_iff.mpr hζf)
  have hgN : Summable fun n ↦ ‖gs n * ζ ^ n‖ := by
    simpa [ofScalars_apply_eq, mul_comm] using
      (ofScalars ℂ gs).summable_norm_apply (mem_eball_zero_iff.mpr hζg)
  have hPsum : HasSum (fun n : ℕ ↦ (ρ + n) * a n * ζ ^ n) (ρ * S ζ + ζ * deriv S ζ) := by
    convert (h0.mul_left ρ).add h1 using 1
    ext n
    ring
  have hC1 := hasSum_sum_range_mul_of_summable_norm hP hfN
  have hC2 := hasSum_sum_range_mul_of_summable_norm hA hgN
  rw [hPsum.tsum_eq, hF.tsum_eq] at hC1
  rw [h0.tsum_eq, hG.tsum_eq] at hC2
  -- the combined series has all coefficients zero
  have htotal := ((((h0.mul_left (ρ * (ρ - 1))).add (h1.mul_left (2 * ρ))).add h2).add hC1).add hC2
  rw [mul_comm (ρ * S ζ + ζ * deriv S ζ) F, mul_comm (S ζ) G] at htotal
  exact htotal.unique ((hasSum_zero).congr_fun fun n ↦ euler_form_coeff_eq_zero (ζ := ζ) hρ ha n)

/-- The derivative of `y ↦ y ^ ρ * S y` on the slit disc of convergence of `S`. -/
private theorem hasDerivAt_cpow_mul {ρ y : ℂ} {S : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {R : ℝ≥0∞} (hS : HasFPowerSeriesOnBall S p 0 R) (hy : y ∈ slitPlane) (hyR : ‖y‖ₑ < R) :
    HasDerivAt (fun y ↦ y ^ ρ * S y) (ρ * y ^ (ρ - 1) * S y + y ^ ρ * deriv S y) y := by
  have hSd := (hS.differentiableOn.differentiableAt
    (Metric.isOpen_eball.mem_nhds (mem_eball_zero_iff.mpr hyR))).hasDerivAt
  simpa using ((hasDerivAt_id' y).cpow_const (c := ρ) hy).fun_mul hSd

/-- The equation at a point `ζ` of the slit disc, for the Frobenius series about the origin:
`w(ζ) = ζ ^ ρ S(ζ)` with `S = ∑ aₛ ζˢ`, where `ζ fζ = ∑ fₛ ζˢ` and `ζ² gζ = ∑ gₛ ζˢ`. -/
private theorem deriv_deriv_cpow_mul_add_eq_zero {ρ ζ fζ gζ : ℂ} {fs gs a : ℕ → ℂ} {S : ℂ → ℂ}
    {R : ℝ≥0∞} (hS : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 R) (hζs : ζ ∈ slitPlane)
    (hζ : ‖ζ‖ₑ < R) (hζf : ‖ζ‖ₑ < (ofScalars ℂ fs).radius)
    (hζg : ‖ζ‖ₑ < (ofScalars ℂ gs).radius)
    (hF : HasSum (fun s ↦ fs s * ζ ^ s) (ζ * fζ)) (hG : HasSum (fun s ↦ gs s * ζ ^ s) (ζ ^ 2 * gζ))
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k) :
    deriv (deriv fun y ↦ y ^ ρ * S y) ζ + fζ * deriv (fun y ↦ y ^ ρ * S y) ζ +
      gζ * (ζ ^ ρ * S ζ) = 0 := by
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
  linear_combination ζ ^ (ρ - 1 - 1) * euler_form_eq_zero hS hζ hζf hζg hF hG hρ ha

/-- **The Frobenius series solution at a regular singularity** (DLMF 2.7.2–2.7.5). Suppose that
`(z - z₀) f(z) = ∑ fₛ (z - z₀)ˢ` and `(z - z₀)² g(z) = ∑ gₛ (z - z₀)ˢ` on the punctured disc
`0 < ‖z - z₀‖ < r`. Let `ρ` be a root of the indicial polynomial `Q(α) = α (α - 1) + f₀ α + g₀`
such that no `ρ + s` with `s ≥ 1` is a root, and let `Q(ρ + s) aₛ = -∑_{k < s} ((ρ + k) f_{s-k} +
g_{s-k}) aₖ` for `s ≥ 1`. Then `∑ aₛ (z - z₀)ˢ` converges on the disc `‖z - z₀‖ < r`, and
`w(z) = (z - z₀) ^ ρ ∑ aₛ (z - z₀)ˢ` is holomorphic on the slit punctured disc
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}` and solves `w'' + f w' + g w = 0` there. The usual
normalization `a₀ = 1` is not needed. -/
theorem regularSingular_solution {z₀ ρ : ℂ} {r : ℝ} {f g w : ℂ → ℂ} {fs gs a : ℕ → ℂ}
    (hf : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ fs s * (z - z₀) ^ s) ((z - z₀) * f z))
    (hg : ∀ z, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun s ↦ gs s * (z - z₀) ^ s) ((z - z₀) ^ 2 * g z))
    (hρ : ρ * (ρ - 1) + fs 0 * ρ + gs 0 = 0)
    (hres : ∀ s : ℕ, 1 ≤ s → (ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0 ≠ 0)
    (ha : ∀ s : ℕ, 1 ≤ s → ((ρ + s) * (ρ + s - 1) + fs 0 * (ρ + s) + gs 0) * a s =
      -∑ k ∈ range s, ((ρ + k) * fs (s - k) + gs (s - k)) * a k)
    (hw : w = fun z ↦ (z - z₀) ^ ρ * ∑' s, a s * (z - z₀) ^ s) :
    (∀ z, ‖z - z₀‖ < r → Summable fun s ↦ a s * (z - z₀) ^ s) ∧
      DifferentiableOn ℂ w {z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r} ∧
      ∀ z, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
        deriv (deriv w) z + f z * deriv w z + g z * w z = 0 := by
  -- the three series converge on the disc of radius `r` about the origin
  have hlt {ζ : ℂ} (hζ : ‖ζ‖ < r) : ‖ζ‖ₑ < ENNReal.ofReal r := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hζ, (norm_nonneg _).trans_lt hζ⟩
  have hlt' {ζ : ℂ} (hζ : ‖ζ‖ₑ < ENNReal.ofReal r) : ‖ζ‖ < r := by
    rw [← ofReal_norm] at hζ
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp hζ).1
  have hfr := le_radius_ofScalars_of_summable fs fun ζ hζ0 hζ ↦ by
    simpa using (hf (ζ + z₀) (by simpa using hζ0) (by simpa using hlt' hζ)).summable
  have hgr := le_radius_ofScalars_of_summable gs fun ζ hζ0 hζ ↦ by
    simpa using (hg (ζ + z₀) (by simpa using hζ0) (by simpa using hlt' hζ)).summable
  have har := le_radius_ofScalars_of_regularSingular hfr hgr hρ hres ha
  have hsum {ζ : ℂ} (hζ : ‖ζ‖ₑ < (ofScalars ℂ a).radius) : Summable fun s ↦ a s * ζ ^ s := by
    simpa [ofScalars_apply_eq, mul_comm] using
      ((ofScalars ℂ a).summable_norm_apply (mem_eball_zero_iff.mpr hζ)).of_norm
  refine ⟨fun z hz ↦ hsum ((hlt hz).trans_le har), ?_⟩
  -- the sum `S` of the series, and `w` as a translate of `W(ζ) = ζ ^ ρ S(ζ)`
  set S : ℂ → ℂ := fun ζ ↦ ∑' s, a s * ζ ^ s
  have hS (hr : 0 < r) : HasFPowerSeriesOnBall S (ofScalars ℂ a) 0 (ENNReal.ofReal r) := by
    refine ⟨har, ENNReal.ofReal_pos.mpr hr, fun {ζ} hζ ↦ ?_⟩
    rw [zero_add]
    simpa [S, ofScalars_apply_eq, mul_comm] using
      (hsum ((mem_eball_zero_iff.mp hζ).trans_le har)).hasSum
  have hwW : w = fun z ↦ (fun ζ ↦ ζ ^ ρ * S ζ) (z - z₀) := hw
  have hd1 : deriv w = fun z ↦ deriv (fun ζ ↦ ζ ^ ρ * S ζ) (z - z₀) := by
    rw [hwW]
    exact funext fun z ↦ deriv_comp_sub_const (fun ζ ↦ ζ ^ ρ * S ζ) z₀ z
  have hd2 : deriv (deriv w) = fun z ↦ deriv (deriv fun ζ ↦ ζ ^ ρ * S ζ) (z - z₀) := by
    rw [hd1]
    exact funext fun z ↦ deriv_comp_sub_const (deriv fun ζ ↦ ζ ^ ρ * S ζ) z₀ z
  have hr {z : ℂ} (hz : ‖z - z₀‖ < r) : 0 < r := (norm_nonneg _).trans_lt hz
  refine ⟨fun z hz ↦ ?_, fun z hzs hz ↦ ?_⟩
  · rw [hwW]
    exact ((hasDerivAt_cpow_mul (hS (hr hz.2)) hz.1 (hlt hz.2)).comp_sub_const z z₀
      |>.differentiableAt.differentiableWithinAt)
  · have h0 : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hzs)
    rw [hd2, hd1, hwW]
    exact deriv_deriv_cpow_mul_add_eq_zero (hS (hr hz)) hzs (hlt hz) ((hlt hz).trans_le hfr)
      ((hlt hz).trans_le hgr) (hf z h0 hz) (hg z h0 hz) hρ ha

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
    (fun y hy _ ↦ by simpa using hgs y (by simpa using hy)) (by norm_num) (fun s hs ↦ ?_)
    (fun s hs ↦ ?_) (by simp)).2.2 z (by simpa using hz) (by simp)
  · have h1 : (s : ℂ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
    have h2 : (s : ℂ) + 3 ≠ 0 := by exact_mod_cast (by omega : s + 3 ≠ 0)
    convert mul_ne_zero h1 h2 using 1
    simp
    ring
  · have hs0 : s ≠ 0 := by omega
    simp only [hs0, ↓reduceIte, mul_zero]
    rw [eq_comm, neg_eq_zero]
    exact sum_eq_zero fun k hk ↦ by simp [show s - k ≠ 0 by simp at hk; omega]

end TauCeti
