/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Data.Nat.Factorial.SuperFactorial
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The Barnes G-function

The Barnes G-function is the entire function fixed by its canonical Weierstrass product
(DLMF 5.17.3)

`G(w + 1) = (2π)^{w/2} exp(-w(w + 1)/2 - γ w²/2) ∏_{k ≥ 1} (1 + w/k)^k exp(-w + w²/(2k))`,

where `γ` is the Euler–Mascheroni constant. Its `k`-th factor is the `k`-th power of the genus-two
Weierstrass elementary factor at `-w/k`, so it differs from one by `O(|w|³/k²)` uniformly on
bounded sets and the product converges locally uniformly on the whole plane.

The recurrence `G(z + 1) = Γ(z) G(z)` together with `G(1) = 1` does not determine `G`: the
function `G(z) (1 + sin²(π z))` satisfies both. The canonical product is the normalization. The
recurrence is proved by comparing the partial products at `w` and `w - 1`, which telescope, with
Euler's limit formula for `Γ`; Stirling's formula and the limit `H_n - log n → γ` account for the
prefactor `(2π)^{w/2} exp(-γ w²/2)`.

Mathlib's `Complex.Gamma` vanishes at its poles, so the pointwise recurrence fails exactly at
`z = 0`, where `G(1) = 1` but `Γ(0) G(0) = 0`. At every other nonpositive integer both sides
vanish.

## Main results

* `Complex.barnesG`: the Barnes G-function, defined by its canonical product, whose `k`-th factor
  is `Complex.barnesGFactor k`.
* `Complex.differentiable_barnesG`: `G` is entire.
* `Complex.barnesG_one`: `G(1) = 1`.
* `Complex.barnesG_add_one`: `G(z + 1) = Γ(z) G(z)` for every `z ≠ 0`.
* `Complex.barnesG_natCast_add_two`: `G(n + 2) = 1! 2! ⋯ n!`, the superfactorial of `n`.
* `Complex.barnesG_eq_zero_iff`, `Complex.barnesG_neg_natCast`: the zeros of `G` are the
  nonpositive integers.
* `Complex.analyticOrderAt_barnesG_neg_natCast`: the zero at `-n` has order `n + 1`.
* `Complex.barnesG_ofReal_im`, `Complex.barnesG_ofReal_re_pos`: `G` is real on the real axis
  and positive on the positive real axis.
* `Complex.hasDerivAt_barnesG_one`, `Complex.logDeriv_barnesG_one`: `G'(1) = log(2π)/2 - 1/2`.

## References

* NIST Digital Library of Mathematical Functions, §5.17, equations 5.17.1–5.17.3.
* V. S. Adamchik, *Contributions to the theory of the Barnes function*, arXiv:math/0308086,
  the canonical product (20) and Proposition 3.1.
-/

public section

open Filter Topology Real
open Complex hiding exp log
open scoped BigOperators Nat

namespace Complex

/-! ### The factors of the canonical product -/

/-- The factor `(1 + w/(k + 1))^(k + 1) exp(-w + w²/(2(k + 1)))` of the canonical product of
the Barnes G-function, indexed from `k = 0`. -/
noncomputable def barnesGFactor (k : ℕ) (w : ℂ) : ℂ :=
  (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1)))

/-- The defining formula of a Barnes factor. -/
theorem barnesGFactor_def (k : ℕ) (w : ℂ) :
    barnesGFactor k w = (1 + w / (k + 1)) ^ (k + 1) * Complex.exp (-w + w ^ 2 / (2 * (k + 1))) := by
  rfl

/-- Each factor of the Barnes product is a power of the genus-two elementary factor. -/
theorem barnesGFactor_eq_weierstrassFactor_pow (k : ℕ) (w : ℂ) :
    barnesGFactor k w = weierstrassFactor 2 (-w / (k + 1)) ^ (k + 1) := by
  have hk : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [barnesGFactor_def, weierstrassFactor_eq_mul_exp_sum, mul_pow, ← Complex.exp_natCast_mul]
  congr 2
  · ring
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    field_simp
    ring

/-- Every Barnes factor is normalized to one at the origin. -/
@[simp]
theorem barnesGFactor_zero (k : ℕ) : barnesGFactor k 0 = 1 := by
  simp [barnesGFactor_def]

/-- The only zero of the `k`-th Barnes factor is `-(k + 1)`. -/
theorem barnesGFactor_eq_zero_iff {k : ℕ} {w : ℂ} : barnesGFactor k w = 0 ↔ w = -(k + 1) := by
  have hk : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [barnesGFactor_def, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), pow_eq_zero_iff
    (Nat.succ_ne_zero k), add_div_eq_mul_add_div _ _ hk, div_eq_zero_iff, or_iff_left hk]
  constructor <;> intro h <;> linear_combination h

/-- The derivative of a Barnes factor, `(1 + w/m)^(m - 1) exp(-w + w²/(2m)) w²/m²` with
`m = k + 1`; it vanishes to second order at the origin. -/
theorem hasDerivAt_barnesGFactor (k : ℕ) (w : ℂ) :
    HasDerivAt (barnesGFactor k)
      ((1 + w / (k + 1)) ^ k * Complex.exp (-w + w ^ 2 / (2 * (k + 1))) *
        (w ^ 2 / (k + 1) ^ 2)) w := by
  have hk : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
  have h1 := (((hasDerivAt_id w).div_const ((k : ℂ) + 1)).const_add 1).pow (k + 1)
  have h2 := (hasDerivAt_id w).neg.add ((hasDerivAt_pow 2 w).div_const (2 * ((k : ℂ) + 1)))
  convert h1.mul h2.cexp using 1
  · ext x
    simp [barnesGFactor_def]
  · simp only [Pi.pow_apply, Pi.add_apply, Pi.neg_apply, id_eq, Nat.add_sub_cancel,
      pow_succ (1 + w / ((k : ℂ) + 1)) k]
    generalize (1 + w / ((k : ℂ) + 1)) ^ k = A
    generalize Complex.exp (-w + w ^ 2 / (2 * ((k : ℂ) + 1))) = E
    push_cast
    field_simp
    ring

/-- Every Barnes factor is entire. -/
@[fun_prop]
theorem differentiable_barnesGFactor (k : ℕ) : Differentiable ℂ (barnesGFactor k) :=
  fun w ↦ (hasDerivAt_barnesGFactor k w).differentiableAt

/-- The `k`-th Barnes factor differs from one by at most `2‖w‖³/(k + 1)²` as soon as
`‖w‖³ ≤ (k + 1)²`. -/
theorem norm_barnesGFactor_sub_one_le {k : ℕ} {w : ℂ} (hw' : ‖w‖ ^ 3 ≤ (k + 1) ^ 2) :
    ‖barnesGFactor k w - 1‖ ≤ 2 * ‖w‖ ^ 3 / (k + 1) ^ 2 := by
  have hk : (0 : ℝ) < k + 1 := Nat.cast_add_one_pos k
  have hw : ‖w‖ ≤ k + 1 := by
    refine le_of_pow_le_pow_left₀ three_ne_zero hk.le (hw'.trans ?_)
    exact pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg k)) (by norm_num)
  set e := weierstrassFactor 2 (-w / (k + 1)) - 1 with he_def
  have hz : ‖-w / (k + 1)‖ = ‖w‖ / (k + 1) := by
    rw [norm_div, norm_neg]
    norm_cast
  have he : ‖e‖ ≤ ‖w‖ ^ 3 / (k + 1) ^ 3 := by
    have h := norm_weierstrassFactor_sub_one_le 2 (z := -w / (k + 1))
      (by rw [hz, div_le_one hk]; exact hw)
    rwa [hz, div_pow] at h
  have hke : (k + 1 : ℝ) * ‖e‖ ≤ 1 := by
    calc (k + 1 : ℝ) * ‖e‖ ≤ (k + 1) * (‖w‖ ^ 3 / (k + 1) ^ 3) := by gcongr
      _ = ‖w‖ ^ 3 / (k + 1) ^ 2 := by field_simp
      _ ≤ 1 := by rwa [div_le_one (by positivity)]
  rw [barnesGFactor_eq_weierstrassFactor_pow, show weierstrassFactor 2 (-w / (k + 1)) = 1 + e by
    rw [he_def]; ring]
  calc ‖(1 + e) ^ (k + 1) - 1‖ ≤ Real.exp ((k + 1 : ℕ) * ‖e‖) - 1 := by
        simpa using Finset.norm_prod_one_add_sub_one_le (Finset.range (k + 1)) fun _ ↦ e
    _ ≤ 2 * ((k + 1) * ‖e‖) := by
        have hx : 0 ≤ ((k + 1 : ℕ) : ℝ) * ‖e‖ := by positivity
        have h := Real.abs_exp_sub_one_le (x := ((k + 1 : ℕ) : ℝ) * ‖e‖)
          (by rw [abs_of_nonneg hx]; push_cast; exact hke)
        rw [abs_of_nonneg hx] at h
        push_cast at h ⊢
        exact (le_abs_self _).trans h
    _ ≤ 2 * ((k + 1) * (‖w‖ ^ 3 / (k + 1) ^ 3)) := by gcongr
    _ = 2 * ‖w‖ ^ 3 / (k + 1) ^ 2 := by field_simp

/-- On a set of norm at most `C`, the Barnes factors are eventually within a summable bound of
one. -/
private theorem summable_and_eventually_norm_barnesGFactor_sub_one_le (C : ℝ) :
    Summable (fun k : ℕ ↦ 2 * max C 1 ^ 3 * (1 / ((k : ℝ) + 1) ^ 2)) ∧
    ∀ᶠ k : ℕ in cofinite, ∀ w : ℂ, ‖w‖ ≤ C →
      ‖barnesGFactor k w - 1‖ ≤ 2 * max C 1 ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
  refine ⟨Summable.mul_left _ ?_, ?_⟩
  · simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop ⌈max C 1 ^ 3⌉₊] with k hk w hw
  rw [mul_one_div]
  have hk' : max C 1 ^ 3 ≤ k + 1 := by
    have := (Nat.ceil_le).mp hk
    linarith
  have hw3 : ‖w‖ ^ 3 ≤ max C 1 ^ 3 := by
    have : ‖w‖ ≤ max C 1 := hw.trans (le_max_left _ _)
    gcongr
  have hkpos : (1 : ℝ) ≤ k + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc ‖barnesGFactor k w - 1‖ ≤ 2 * ‖w‖ ^ 3 / (k + 1) ^ 2 := by
        apply norm_barnesGFactor_sub_one_le
        calc ‖w‖ ^ 3 ≤ k + 1 := hw3.trans hk'
          _ ≤ (k + 1) ^ 2 := le_self_pow₀ hkpos (by norm_num)
    _ ≤ 2 * max C 1 ^ 3 / (k + 1) ^ 2 := by gcongr

/-- A product whose factors are closer to one than the Barnes factors converges uniformly on
every bounded set. -/
private theorem hasProdUniformlyOn_of_norm_sub_one_le {g : ℕ → ℂ → ℂ}
    (hg : ∀ k w, ‖g k w - 1‖ ≤ ‖barnesGFactor k w - 1‖) (hcts : ∀ k, Continuous (g k))
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn g (fun w ↦ ∏' k, g k w) K := by
  obtain ⟨C, hC⟩ := hK.isCompact_closure.exists_bound_of_continuousOn
    continuous_id.continuousOn
  obtain ⟨hu, hev⟩ := summable_and_eventually_norm_barnesGFactor_sub_one_le C
  have hbound : ∀ᶠ k : ℕ in cofinite, ∀ w ∈ closure K,
      ‖g k w - 1‖ ≤ 2 * max C 1 ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
    filter_upwards [hev] with k hk w hw
    exact (hg k w).trans (hk w (hC w hw))
  have h := Summable.hasProdUniformlyOn_one_add hK.isCompact_closure hu hbound
    fun k ↦ ((hcts k).sub continuous_const).continuousOn
  simpa only [add_sub_cancel] using h.mono subset_closure

/-- A product whose factors are entire and closer to one than the Barnes factors is entire. -/
private theorem differentiable_tprod_of_norm_sub_one_le {g : ℕ → ℂ → ℂ}
    (hg : ∀ k w, ‖g k w - 1‖ ≤ ‖barnesGFactor k w - 1‖) (hd : ∀ k, Differentiable ℂ (g k)) :
    Differentiable ℂ (fun w ↦ ∏' k, g k w) := by
  rw [← differentiableOn_univ]
  refine (hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_of_norm_sub_one_le hg (fun k ↦ (hd k).continuous)
      hK.isBounded).differentiableOn
    (Eventually.of_forall fun s ↦ ?_) isOpen_univ
  exact (Differentiable.fun_finsetProd fun k _ ↦ hd k).differentiableOn

/-- A product whose factors are nonzero and closer to one than the Barnes factors is nonzero. -/
private theorem tprod_ne_zero_of_norm_sub_one_le {g : ℕ → ℂ → ℂ}
    (hg : ∀ k w, ‖g k w - 1‖ ≤ ‖barnesGFactor k w - 1‖) {w : ℂ} (hw : ∀ k, g k w ≠ 0) :
    ∏' k, g k w ≠ 0 := by
  have hne : ∀ k, 1 + (g k w - 1) ≠ 0 := fun k ↦ by rw [add_sub_cancel]; exact hw k
  obtain ⟨hu, hev⟩ := summable_and_eventually_norm_barnesGFactor_sub_one_le ‖w‖
  have hs : Summable (fun k : ℕ ↦ ‖g k w - 1‖) :=
    Summable.of_norm_bounded_eventually hu (by
      filter_upwards [hev] with k hk
      rw [norm_norm]
      exact (hg k w).trans (hk w le_rfl))
  simpa only [add_sub_cancel] using tprod_one_add_ne_zero_of_summable hne hs

/-- The Barnes product converges uniformly on every bounded set. -/
theorem hasProdUniformlyOn_barnesGFactor {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn barnesGFactor (fun w ↦ ∏' k, barnesGFactor k w) K :=
  hasProdUniformlyOn_of_norm_sub_one_le (fun _ _ ↦ le_rfl)
    (fun k ↦ (differentiable_barnesGFactor k).continuous) hK

/-- The Barnes product converges locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_barnesGFactor :
    HasProdLocallyUniformlyOn barnesGFactor (fun w ↦ ∏' k, barnesGFactor k w) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    fun _ _ hK ↦ hasProdUniformlyOn_barnesGFactor hK.isBounded

/-- The Barnes product converges at every point. -/
theorem hasProd_barnesGFactor (w : ℂ) : HasProd (barnesGFactor · w) (∏' k, barnesGFactor k w) :=
  hasProdLocallyUniformlyOn_barnesGFactor.hasProd (Set.mem_univ w)

/-- The Barnes product is entire. -/
theorem differentiable_tprod_barnesGFactor :
    Differentiable ℂ (fun w ↦ ∏' k, barnesGFactor k w) :=
  differentiable_tprod_of_norm_sub_one_le (fun _ _ ↦ le_rfl) differentiable_barnesGFactor

/-- The Barnes product vanishes exactly at the negative integers. -/
theorem tprod_barnesGFactor_eq_zero_iff (w : ℂ) :
    ∏' k, barnesGFactor k w = 0 ↔ ∃ k : ℕ, w = -(k + 1) := by
  constructor
  · intro h
    by_contra! hne
    exact tprod_ne_zero_of_norm_sub_one_le (fun _ _ ↦ le_rfl)
      (fun k h0 ↦ hne k (barnesGFactor_eq_zero_iff.mp h0)) h
  · rintro ⟨k, rfl⟩
    exact tprod_of_exists_eq_zero ⟨k, barnesGFactor_eq_zero_iff.mpr rfl⟩

/-! ### The Barnes G-function -/

/-- The Barnes G-function, defined by its canonical Weierstrass product
`G(z) = (2π)^{w/2} exp(-w(w + 1)/2 - γ w²/2) ∏_{k ≥ 1} (1 + w/k)^k exp(-w + w²/(2k))` with
`w = z - 1` (DLMF 5.17.3). -/
noncomputable def barnesG (z : ℂ) : ℂ :=
  (2 * π : ℂ) ^ ((z - 1) / 2) *
    Complex.exp (-((z - 1) * z) / 2 - eulerMascheroniConstant * (z - 1) ^ 2 / 2) *
    ∏' k, barnesGFactor k (z - 1)

/-- The defining formula of the Barnes G-function. -/
theorem barnesG_def (z : ℂ) :
    barnesG z = (2 * π : ℂ) ^ ((z - 1) / 2) *
      Complex.exp (-((z - 1) * z) / 2 - eulerMascheroniConstant * (z - 1) ^ 2 / 2) *
      ∏' k, barnesGFactor k (z - 1) := by
  rfl

/-- The canonical product, written at `w + 1`. -/
theorem barnesG_add_one_eq_tprod (w : ℂ) :
    barnesG (w + 1) = (2 * π : ℂ) ^ (w / 2) *
      Complex.exp (-(w * (w + 1)) / 2 - eulerMascheroniConstant * w ^ 2 / 2) *
      ∏' k, barnesGFactor k w := by
  simp only [barnesG_def, add_sub_cancel_right]

/-- The elementary prefactor `(2π)^{(z - 1)/2} exp(-(z - 1)z/2 - γ (z - 1)²/2)` of `G(z)`. -/
private noncomputable def barnesGPrefactor (z : ℂ) : ℂ :=
  (2 * π : ℂ) ^ ((z - 1) / 2) *
    Complex.exp (-((z - 1) * z) / 2 - eulerMascheroniConstant * (z - 1) ^ 2 / 2)

/-- `G` is its prefactor times the Barnes product. -/
private theorem barnesG_eq_barnesGPrefactor_mul (z : ℂ) :
    barnesG z = barnesGPrefactor z * ∏' k, barnesGFactor k (z - 1) := by
  rfl

/-- `2π ≠ 0` in `ℂ`, so that the complex powers of `2π` are well behaved. -/
private theorem two_pi_ne_zero : (2 * π : ℂ) ≠ 0 := by
  exact_mod_cast two_pi_pos.ne'

/-- The prefactor of `G` never vanishes. -/
private theorem barnesGPrefactor_ne_zero (z : ℂ) : barnesGPrefactor z ≠ 0 :=
  mul_ne_zero (by simp [cpow_eq_zero_iff]) (Complex.exp_ne_zero _)

/-- The prefactor of `G` is entire. -/
@[fun_prop]
private theorem differentiable_barnesGPrefactor : Differentiable ℂ barnesGPrefactor := by
  unfold barnesGPrefactor
  refine (Differentiable.const_cpow ?_ (Or.inl two_pi_ne_zero)).mul ?_ <;> fun_prop

/-- Shifting the prefactor by one multiplies it by `(2π)^{1/2} exp(-z - γ (z - 1/2))`. -/
private theorem barnesGPrefactor_add_one (z : ℂ) :
    barnesGPrefactor (z + 1) = (2 * π : ℂ) ^ (1 / 2 : ℂ) *
      Complex.exp (-z - eulerMascheroniConstant * (z - 1 / 2)) * barnesGPrefactor z := by
  have hpow : (2 * π : ℂ) ^ ((z + 1 - 1) / 2) =
      (2 * π : ℂ) ^ (1 / 2 : ℂ) * (2 * π : ℂ) ^ ((z - 1) / 2) := by
    rw [← Complex.cpow_add _ _ two_pi_ne_zero]
    congr 1
    ring
  have hexp : Complex.exp (-((z + 1 - 1) * (z + 1)) / 2 -
        eulerMascheroniConstant * (z + 1 - 1) ^ 2 / 2) =
      Complex.exp (-z - eulerMascheroniConstant * (z - 1 / 2)) *
        Complex.exp (-((z - 1) * z) / 2 - eulerMascheroniConstant * (z - 1) ^ 2 / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [barnesGPrefactor, hpow, hexp, barnesGPrefactor]
  ring

/-- The Barnes G-function is entire. -/
@[fun_prop]
theorem differentiable_barnesG : Differentiable ℂ barnesG := by
  have hP : Differentiable ℂ (fun z : ℂ ↦ ∏' k, barnesGFactor k (z - 1)) :=
    differentiable_tprod_barnesGFactor.comp (differentiable_id.sub_const 1)
  rw [funext barnesG_eq_barnesGPrefactor_mul]
  exact differentiable_barnesGPrefactor.mul hP

/-- The normalization `G(1) = 1`. -/
@[simp]
theorem barnesG_one : barnesG 1 = 1 := by
  simp [barnesG]

/-- The zeros of the Barnes G-function are the nonpositive integers. -/
theorem barnesG_eq_zero_iff {z : ℂ} : barnesG z = 0 ↔ ∃ n : ℕ, z = -n := by
  simp only [barnesG_eq_barnesGPrefactor_mul, mul_eq_zero, barnesGPrefactor_ne_zero, false_or,
    tprod_barnesGFactor_eq_zero_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by linear_combination hn⟩

/-- `G` vanishes at the nonpositive integers. -/
@[simp]
theorem barnesG_neg_natCast (n : ℕ) : barnesG (-n) = 0 :=
  barnesG_eq_zero_iff.mpr ⟨n, rfl⟩

/-- `G` vanishes at the origin. -/
@[simp]
theorem barnesG_zero : barnesG 0 = 0 := by
  simpa using barnesG_neg_natCast 0

/-- The zero of the Barnes G-function at `-n` has order `n + 1`. -/
theorem analyticOrderAt_barnesG_neg_natCast (n : ℕ) :
    analyticOrderAt barnesG (-n) = n + 1 := by
  classical
  have hn : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  -- Remove the vanishing factor `k = n`; the remaining product is entire and nonzero at `-n`.
  set g : ℕ → ℂ → ℂ := fun k w ↦ if k = n then 1 else barnesGFactor k w
  have hg : ∀ k w, ‖g k w - 1‖ ≤ ‖barnesGFactor k w - 1‖ := fun k w ↦ by
    by_cases hk : k = n <;> simp [g, hk]
  have hgd : ∀ k, Differentiable ℂ (g k) := fun k ↦ by
    by_cases hk : k = n <;> simp only [g, hk, ite_true, ite_false] <;> fun_prop
  have hQ : Differentiable ℂ (fun z : ℂ ↦ ∏' k, g k (z - 1)) :=
    (differentiable_tprod_of_norm_sub_one_le hg hgd).comp (differentiable_id.sub_const 1)
  have hQne : ∏' k, g k (-n - 1) ≠ 0 := by
    refine tprod_ne_zero_of_norm_sub_one_le hg fun k ↦ ?_
    by_cases hk : k = n
    · simp [g, hk]
    · simp only [g, hk, ite_false, ne_eq, barnesGFactor_eq_zero_iff]
      intro h
      exact hk (by exact_mod_cast (show (k : ℂ) = n by linear_combination h))
  rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by norm_cast,
    (differentiable_barnesG.analyticAt _).analyticOrderAt_eq_natCast]
  refine ⟨fun z ↦ barnesGPrefactor z *
      ((1 / (n + 1)) ^ (n + 1) * Complex.exp (-(z - 1) + (z - 1) ^ 2 / (2 * (n + 1)))) *
      ∏' k, g k (z - 1), ?_, ?_, Eventually.of_forall fun z ↦ ?_⟩
  · exact (Differentiable.mul (by fun_prop) hQ).analyticAt _
  · simp only [ne_eq, mul_eq_zero, barnesGPrefactor_ne_zero, Complex.exp_ne_zero, or_false,
      pow_eq_zero_iff (Nat.succ_ne_zero n), one_div, inv_eq_zero, hn, false_or]
    exact hQne
  · have hgm : Multipliable (Function.update (barnesGFactor · (z - 1)) n 1) := by
      have h := (hasProdUniformlyOn_of_norm_sub_one_le hg (fun k ↦ (hgd k).continuous)
        Bornology.isBounded_singleton).hasProd (Set.mem_singleton (z - 1))
      convert h.multipliable using 1
      ext k
      by_cases hk : k = n <;> simp [g, hk]
    rw [barnesG_eq_barnesGPrefactor_mul, Multipliable.tprod_eq_mul_tprod_ite' n hgm,
      barnesGFactor_def, smul_eq_mul]
    simp only [g]
    rw [show (1 + (z - 1) / (n + 1)) = (z - -n) * (1 / (n + 1)) by field_simp; ring, mul_pow]
    ring

/-! ### The Gamma recurrence -/

/-- Shifting the argument of a Barnes factor by one: `f_k(w) (k + w)^(k+1)` equals
`f_k(w - 1) (k + 1 + w)^(k+1) exp(-1 + (w - 1/2)/(k + 1))`. -/
private theorem barnesGFactor_mul_pow (k : ℕ) (w : ℂ) :
    barnesGFactor k w * (k + w) ^ (k + 1) = barnesGFactor k (w - 1) * (k + 1 + w) ^ (k + 1) *
      Complex.exp (-1 + (w - 1 / 2) / (k + 1)) := by
  have hk : (k + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hbase : (1 + w / (k + 1)) * (k + w) = (1 + (w - 1) / (k + 1)) * (k + 1 + w) := by
    field_simp
    ring
  have hexp : -w + w ^ 2 / (2 * (k + 1)) =
      (-(w - 1) + (w - 1) ^ 2 / (2 * (k + 1))) + (-1 + (w - 1 / 2) / (k + 1)) := by
    field_simp
    ring
  rw [barnesGFactor_def, barnesGFactor_def, mul_right_comm, ← mul_pow, hbase, hexp,
    Complex.exp_add, mul_pow]
  ring

/-- The partial Barnes products at `w` and `w - 1` differ by an explicit factor, after clearing
the Pochhammer symbol `w (w + 1) ⋯ (w + n - 1)`. -/
private theorem prod_add_mul_prod_barnesGFactor (w : ℂ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (w + j)) * ∏ k ∈ Finset.range n, barnesGFactor k w =
      (n + w) ^ n * Complex.exp (-n + (w - 1 / 2) * harmonic n) *
        ∏ k ∈ Finset.range n, barnesGFactor k (w - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hE : Complex.exp (-((n + 1 : ℕ) : ℂ) + (w - 1 / 2) * (harmonic (n + 1) : ℂ)) =
        Complex.exp (-n + (w - 1 / 2) * harmonic n) *
          Complex.exp (-1 + (w - 1 / 2) / (n + 1)) := by
      rw [← Complex.exp_add, harmonic_succ]
      push_cast
      congr 1
      ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, hE]
    push_cast
    linear_combination (w + n) * barnesGFactor n w * ih +
      Complex.exp (-n + (w - 1 / 2) * harmonic n) *
        (∏ k ∈ Finset.range n, barnesGFactor k (w - 1)) * barnesGFactor_mul_pow n w

private theorem two_pi_cpow_one_half : (2 * π : ℂ) ^ (1 / 2 : ℂ) = (√2 : ℂ) * √π := by
  rw [show (√2 : ℂ) * √π = ((√(2 * π) : ℝ) : ℂ) by rw [Real.sqrt_mul zero_le_two]; push_cast; ring,
    Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1

/-- `n ^ w = n ^ (w - 1/2) √n` for a positive integer `n`, with the power written through the
logarithm. -/
private theorem natCast_cpow_eq_exp_mul_sqrt {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    (n : ℂ) ^ w = Complex.exp (Complex.log n * (w - 1 / 2)) * √(n : ℝ) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsq : ((√(n : ℝ) : ℝ) : ℂ) = Complex.exp (Complex.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnr, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.natCast_log]
    push_cast
    rw [mul_one_div]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), hsq, ← Complex.exp_add]
  congr 1
  ring

/-- The Pochhammer symbol `w (w + 1) ⋯ (w + n - 1)` does not vanish away from the nonpositive
integers. -/
private theorem prod_range_add_ne_zero {w : ℂ} (hw : ∀ m : ℕ, w ≠ -m) (n : ℕ) :
    ∏ j ∈ Finset.range n, (w + j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ h ↦ hw j (eq_neg_of_add_eq_zero_left h)

/-- The exponentials in `barnesG_ratio_eq`: the Euler-limit, harmonic-limit and `n ^ (w - 1/2)`
factors on the right combine to the prefactor ratio, the harmonic factor and `e^n`. -/
private theorem exp_barnesG_ratio (w : ℂ) (n : ℕ) :
    Complex.exp (-w) * Complex.exp ((w - 1 / 2) *
        ((harmonic n : ℂ) - Complex.log n - eulerMascheroniConstant)) *
        Complex.exp (Complex.log n * (w - 1 / 2)) =
      Complex.exp (-w - eulerMascheroniConstant * (w - 1 / 2)) *
        Complex.exp (-n + (w - 1 / 2) * harmonic n) * Complex.exp n := by
  simp only [← Complex.exp_add]
  congr 1
  ring

/-- The explicit factor relating the partial products, including the ratio
`(2π)^{1/2} exp(-w - γ (w - 1/2))` of the prefactors of `G(w + 1)` and `G(w)`, factored into
pieces with known limits. -/
private theorem barnesG_ratio_eq {w : ℂ} (hw : ∀ m : ℕ, w ≠ -m) {n : ℕ} (hn : n ≠ 0) :
    (2 * π : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-w - eulerMascheroniConstant * (w - 1 / 2)) *
        ((n + w) ^ n * Complex.exp (-n + (w - 1 / 2) * harmonic n)) /
          ∏ j ∈ Finset.range n, (w + j) =
      Complex.exp (-w) * (1 + w / n) ^ n *
        Complex.exp ((w - 1 / 2) *
          ((harmonic n - Real.log n - eulerMascheroniConstant : ℝ) : ℂ)) *
        ((√π / Stirling.stirlingSeq n : ℝ) : ℂ) * (GammaSeq w n * ((w + n) / n)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hD := prod_range_add_ne_zero hw n
  have hwn : w + n ≠ 0 := fun h ↦ hw n (eq_neg_of_add_eq_zero_left h)
  have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h2n : ((√(2 * n) : ℝ) : ℂ) = √2 * √(n : ℝ) := by
    rw [Real.sqrt_mul zero_le_two]
    push_cast
    ring
  have hsq2 : ((√(n : ℝ) : ℝ) : ℂ) ^ 2 = n := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    push_cast
    ring
  have hexp1 : Complex.exp 1 ^ n = Complex.exp n := by
    rw [← Complex.exp_natCast_mul, mul_one]
  have hX := exp_barnesG_ratio w n
  -- Unfold `GammaSeq` and `stirlingSeq`, write `n ^ w = n ^ (w - 1/2) √n` and `(2π)^{1/2}` and
  -- `√(2n)` through `√2`, `√π` and `√n`, and turn `(1 + w/n)^n` into `(n + w)^n / n^n`.
  rw [GammaSeq, Finset.prod_range_succ, natCast_cpow_eq_exp_mul_sqrt hn, Stirling.stirlingSeq,
    two_pi_cpow_one_half]
  push_cast
  rw [h2n, one_add_div hn', div_pow, div_pow, hexp1]
  -- Name the six exponentials, so that `field_simp` treats them as atoms and `hX` is the only
  -- relation among them; `e^n` appears in a denominator, so keep that it is nonzero.
  generalize Complex.exp (-w) = e3 at hX ⊢
  generalize Complex.exp ((w - 1 / 2) *
    ((harmonic n : ℂ) - Complex.log n - eulerMascheroniConstant)) = e4 at hX ⊢
  generalize Complex.exp (Complex.log n * (w - 1 / 2)) = e5 at hX ⊢
  generalize Complex.exp (-w - eulerMascheroniConstant * (w - 1 / 2)) = e1 at hX ⊢
  generalize Complex.exp (-n + (w - 1 / 2) * harmonic n) = e2 at hX ⊢
  have he6 : Complex.exp n ≠ 0 := Complex.exp_ne_zero _
  generalize Complex.exp n = e6 at hX he6 ⊢
  -- Clearing denominators leaves `e₁ n (n + w)^n e₂ e₆ = (n + w)^n e₃ e₄ (√n)² e₅`, which is
  -- `hX` multiplied by `n (n + w)^n` once `(√n)² = n`.
  field_simp
  rw [hsq2]
  linear_combination (-(n : ℂ) * (n + w) ^ n) * hX

/-- Euler's limit formula for `Γ`, combined with Stirling's formula and `H_n - log n → γ`: the
factor relating the partial products at `w` and `w - 1` tends to `Γ(w)`. -/
private theorem tendsto_barnesG_ratio {w : ℂ} (hw : ∀ m : ℕ, w ≠ -m) :
    Tendsto (fun n : ℕ ↦ (2 * π : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-w - eulerMascheroniConstant * (w - 1 / 2)) *
        ((n + w) ^ n * Complex.exp (-n + (w - 1 / 2) * harmonic n)) /
          ∏ j ∈ Finset.range n, (w + j)) atTop (𝓝 (Gamma w)) := by
  have h1 : Tendsto (fun n : ℕ ↦ Complex.exp (-w) * (1 + w / n) ^ n) atTop (𝓝 1) := by
    simpa [← Complex.exp_add] using (tendsto_one_add_div_pow_exp w).const_mul (Complex.exp (-w))
  have h2 : Tendsto (fun n : ℕ ↦ Complex.exp ((w - 1 / 2) *
      ((harmonic n - Real.log n - eulerMascheroniConstant : ℝ) : ℂ))) atTop (𝓝 1) := by
    have h := (tendsto_harmonic_sub_log.sub_const eulerMascheroniConstant)
    rw [sub_self] at h
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp h).const_mul (w - 1 / 2) |>.cexp
  have h3 : Tendsto (fun n : ℕ ↦ ((√π / Stirling.stirlingSeq n : ℝ) : ℂ)) atTop (𝓝 1) := by
    have h := tendsto_const_nhds (x := √π).div Stirling.tendsto_stirlingSeq_sqrt_pi
      (Real.sqrt_pos.mpr pi_pos).ne'
    rw [div_self (Real.sqrt_pos.mpr pi_pos).ne'] at h
    have h' := (Complex.continuous_ofReal.tendsto 1).comp h
    rwa [Complex.ofReal_one] at h'
  have h4 : Tendsto (fun n : ℕ ↦ GammaSeq w n * ((w + n) / n)) atTop (𝓝 (Gamma w)) := by
    have h : Tendsto (fun n : ℕ ↦ w / n + 1) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat w).add_const 1
    have h' : Tendsto (fun n : ℕ ↦ (w + n) / n) atTop (𝓝 1) := by
      refine h.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      rw [add_div, div_self (Nat.cast_ne_zero.mpr hn)]
    simpa using (GammaSeq_tendsto_Gamma w).mul h'
  have h := ((h1.mul h2).mul h3).mul h4
  rw [one_mul, one_mul, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [barnesG_ratio_eq hw hn]

/-- The recurrence `G(z + 1) = Γ(z) G(z)` away from the nonpositive integers. -/
private theorem barnesG_add_one_of_ne_neg_natCast {z : ℂ} (hz : ∀ m : ℕ, z ≠ -m) :
    barnesG (z + 1) = Gamma z * barnesG z := by
  have hlim₁ : Tendsto (fun n : ℕ ↦
      barnesGPrefactor (z + 1) * ∏ k ∈ Finset.range n, barnesGFactor k z) atTop
      (𝓝 (barnesG (z + 1))) := by
    rw [barnesG_eq_barnesGPrefactor_mul, add_sub_cancel_right]
    exact (hasProd_barnesGFactor z).tendsto_prod_nat.const_mul _
  have hlim₀ := (tendsto_barnesG_ratio hz).mul
    ((hasProd_barnesGFactor (z - 1)).tendsto_prod_nat.const_mul (barnesGPrefactor z))
  rw [← barnesG_eq_barnesGPrefactor_mul] at hlim₀
  refine tendsto_nhds_unique hlim₁ (hlim₀.congr fun n ↦ ?_)
  rw [barnesGPrefactor_add_one, div_mul_eq_mul_div, div_eq_iff (prod_range_add_ne_zero hz n)]
  linear_combination -(2 * π : ℂ) ^ (1 / 2 : ℂ) *
    Complex.exp (-z - eulerMascheroniConstant * (z - 1 / 2)) * barnesGPrefactor z *
      prod_add_mul_prod_barnesGFactor z n

/-- **Gamma recurrence** of the Barnes G-function: `G(z + 1) = Γ(z) G(z)` for every `z ≠ 0`.
At a negative integer both sides vanish. At `z = 0` the recurrence fails for Mathlib's
totalized `Γ`, since `G(1) = 1` while `Γ(0) = 0`. -/
theorem barnesG_add_one {z : ℂ} (hz : z ≠ 0) : barnesG (z + 1) = Gamma z * barnesG z := by
  by_cases h : ∃ m : ℕ, z = -m
  · obtain ⟨m, rfl⟩ := h
    have hm : m ≠ 0 := by rintro rfl; simp at hz
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [barnesG_eq_zero_iff.mpr ⟨m + 1, rfl⟩, mul_zero, barnesG_eq_zero_iff]
    exact ⟨m, by push_cast; ring⟩
  · simp only [not_exists] at h
    exact barnesG_add_one_of_ne_neg_natCast h

/-- `G(2) = Γ(1) G(1) = 1`. -/
@[simp]
theorem barnesG_two : barnesG 2 = 1 := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, barnesG_add_one one_ne_zero, Gamma_one, barnesG_one,
    mul_one]

/-- The values at the positive integers are superfactorials: `G(n + 2) = 1! 2! ⋯ n!`. -/
theorem barnesG_natCast_add_two (n : ℕ) : barnesG (n + 2) = n.superFactorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : (n + 1 : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    rw [show ((n + 1 : ℕ) : ℂ) + 2 = (n + 1 + 1 : ℂ) + 1 by push_cast; ring,
      barnesG_add_one hne, show (n + 1 + 1 : ℂ) = n + 2 by ring, ih,
      show (n + 2 : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial,
      Nat.superFactorial_succ]
    push_cast
    ring

/-! ### Values on the real axis -/

private theorem barnesGFactor_ofReal (k : ℕ) (x : ℝ) :
    barnesGFactor k x =
      ((1 + x / (k + 1)) ^ (k + 1) * Real.exp (-x + x ^ 2 / (2 * (k + 1))) : ℝ) := by
  rw [barnesGFactor_def]
  push_cast
  ring

/-- On the real axis the Barnes product is real, and it is nonnegative to the right of `-1`. -/
private theorem tprod_barnesGFactor_ofReal (x : ℝ) :
    (∏' k, barnesGFactor k x).im = 0 ∧ (-1 < x → 0 ≤ (∏' k, barnesGFactor k x).re) := by
  have h := (hasProd_barnesGFactor x).tendsto_prod_nat
  have hreal : ∀ n : ℕ, ∏ k ∈ Finset.range n, barnesGFactor k x =
      ((∏ k ∈ Finset.range n, (1 + x / (k + 1)) ^ (k + 1) *
        Real.exp (-x + x ^ 2 / (2 * (k + 1))) : ℝ) : ℂ) := fun n ↦ by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun k _ ↦ barnesGFactor_ofReal k x
  refine ⟨(isClosed_eq continuous_im continuous_const).mem_of_tendsto h
    (Eventually.of_forall fun n ↦ by rw [Set.mem_ofPred_eq, hreal n, ofReal_im]), fun hx ↦ ?_⟩
  refine (isClosed_le continuous_const continuous_re).mem_of_tendsto h
    (Eventually.of_forall fun n ↦ ?_)
  rw [Set.mem_ofPred_eq, hreal n, ofReal_re]
  refine Finset.prod_nonneg fun k _ ↦ mul_nonneg (pow_nonneg ?_ _) (Real.exp_pos _).le
  have hk : (0 : ℝ) < k + 1 := Nat.cast_add_one_pos k
  rw [one_add_div hk.ne']
  exact div_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hk.le

/-- On the real axis, `G` is the product of a positive real prefactor and the Barnes product. -/
private theorem barnesG_ofReal_eq (x : ℝ) :
    barnesG x = ((2 * π) ^ ((x - 1) / 2) *
      Real.exp (-((x - 1) * x) / 2 - eulerMascheroniConstant * (x - 1) ^ 2 / 2) : ℝ) *
        ∏' k, barnesGFactor k (x - 1 : ℝ) := by
  rw [barnesG, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
  push_cast
  ring

/-- The Barnes G-function is real on the real axis. -/
theorem barnesG_ofReal_im (x : ℝ) : (barnesG x).im = 0 := by
  rw [barnesG_ofReal_eq, im_ofReal_mul, (tprod_barnesGFactor_ofReal _).1, mul_zero]

/-- The Barnes G-function is positive on the positive real axis. -/
theorem barnesG_ofReal_re_pos {x : ℝ} (hx : 0 < x) : 0 < (barnesG x).re := by
  obtain ⟨him, hre⟩ := tprod_barnesGFactor_ofReal (x - 1)
  have hne : ∏' k, barnesGFactor k (x - 1 : ℝ) ≠ 0 := by
    rw [ne_eq, tprod_barnesGFactor_eq_zero_iff]
    rintro ⟨k, hk⟩
    have h := congrArg re hk
    simp only [ofReal_re, neg_re, add_re, natCast_re, one_re] at h
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hre' : (∏' k, barnesGFactor k (x - 1 : ℝ)).re ≠ 0 := fun h ↦ hne (Complex.ext h him)
  rw [barnesG_ofReal_eq, re_ofReal_mul]
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _))
    (lt_of_le_of_ne (hre (by linarith)) hre'.symm)

/-! ### The derivative at one -/

/-- The Barnes product is stationary at the origin. -/
private theorem hasDerivAt_tprod_barnesGFactor_zero :
    HasDerivAt (fun w ↦ ∏' k, barnesGFactor k w) 0 0 := by
  classical
  have hd := (differentiable_tprod_barnesGFactor 0).hasDerivAt
  suffices deriv (fun w ↦ ∏' k, barnesGFactor k w) 0 = 0 by rwa [this] at hd
  have h := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    hasProdLocallyUniformlyOn_barnesGFactor).deriv
    (Eventually.of_forall fun s ↦ (by fun_prop : Differentiable ℂ _).differentiableOn)
    isOpen_univ |>.tendsto_at (Set.mem_univ 0)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr fun s ↦ ?_)
  rw [Function.comp_apply,
    (HasDerivAt.fun_finsetProd fun k _ ↦ hasDerivAt_barnesGFactor k 0).deriv]
  simp

/-- The prefactor of `G` has derivative `log(2π)/2 - 1/2` at one. -/
private theorem hasDerivAt_barnesGPrefactor_one :
    HasDerivAt barnesGPrefactor (Real.log (2 * π) / 2 - 1 / 2 : ℝ) 1 := by
  -- Both factors of the prefactor equal one at one.
  have hpow1 : (2 * π : ℂ) ^ (((1 : ℂ) - 1) / 2) = 1 := by
    rw [sub_self, zero_div, cpow_zero]
  have hexp1 : Complex.exp (-(((1 : ℂ) - 1) * 1) / 2 -
      eulerMascheroniConstant * ((1 : ℂ) - 1) ^ 2 / 2) = 1 := by
    simp
  have hpow : HasDerivAt (fun z : ℂ ↦ (2 * π : ℂ) ^ ((z - 1) / 2))
      (Complex.log (2 * π) / 2) 1 := by
    convert (((hasDerivAt_id' (1 : ℂ)).sub_const 1).div_const 2).const_cpow
      (Or.inl two_pi_ne_zero) using 1
    rw [hpow1, one_mul, mul_one_div]
  have hexp : HasDerivAt (fun z : ℂ ↦
      Complex.exp (-((z - 1) * z) / 2 - eulerMascheroniConstant * (z - 1) ^ 2 / 2)) (-1 / 2) 1 := by
    have h1 := ((hasDerivAt_id (1 : ℂ)).sub_const 1).mul (hasDerivAt_id (1 : ℂ))
    have h2 := (((hasDerivAt_id (1 : ℂ)).sub_const 1).pow 2).const_mul
      (eulerMascheroniConstant : ℂ)
    convert ((h1.neg.div_const 2).sub (h2.div_const 2)).cexp using 1
    · ext z
      simp
    · simp
  have hlog : Complex.log (2 * π) = Real.log (2 * π) := by
    rw [Complex.ofReal_log two_pi_pos.le]
    push_cast
    ring
  convert hpow.mul hexp using 1
  · rfl
  rw [hpow1, hexp1, hlog]
  push_cast
  ring

/-- The derivative of the Barnes G-function at one is `log(2π)/2 - 1/2`. Substituting Mathlib's
totalized digamma value at zero into the logarithmic-derivative formula would instead give
`log(2π)/2 + 1/2`. -/
theorem hasDerivAt_barnesG_one :
    HasDerivAt barnesG (Real.log (2 * π) / 2 - 1 / 2 : ℝ) 1 := by
  have hprod := HasDerivAt.comp_sub_const (1 : ℂ) 1 (by
    rw [sub_self]; exact hasDerivAt_tprod_barnesGFactor_zero)
  convert hasDerivAt_barnesGPrefactor_one.mul hprod using 1
  · ext z
    exact barnesG_eq_barnesGPrefactor_mul z
  · simp only [sub_self, barnesGFactor_zero, tprod_one, mul_one, mul_zero, add_zero]

/-- The logarithmic derivative of the Barnes G-function at one. -/
theorem logDeriv_barnesG_one : logDeriv barnesG 1 = (Real.log (2 * π) / 2 - 1 / 2 : ℝ) := by
  rw [logDeriv_apply, hasDerivAt_barnesG_one.deriv, barnesG_one, div_one]

end Complex
