/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Asymptotics.Fourier.Endpoint
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds

/-!
# The Fourier analogue of Watson's lemma

Let `α : ℕ → ℂ` have `Re α_s > 0`, let `c : ℕ → ℂ`, and let `q : ℝ → ℂ` be smooth on `(0, ∞)`
with an expansion at `0+` that may be differentiated termwise: for all `k` and `N`,

`q^{(k)}(t) - ∑_{s<N} c_s (α_s - 1)(α_s - 2)⋯(α_s - k) t^{α_s - 1 - k} = O(t^{Re α_N - 1 - k})`

as `t → 0+`. If every `∫ e^{ixt} q^{(k)}(t) dt` converges at `∞` uniformly for all large `x`,
then the improper integral `∫₀^∞ e^{ixt} q(t) dt` exists for all large `x`, and

`∫₀^∞ e^{ixt} q(t) dt ∼ ∑ e^{iπα_s/2} Γ(α_s) c_s x^{-α_s}`   as `x → +∞`

(DLMF 2.3.19–2.3.20, where `α_s = (s + λ)/μ`). The conclusion is an
`Asymptotics.HasAsymptoticExpansion` in the scale `x^{-α_s}`: for every `N` the remainder after
`N` terms is `O(x^{-Re α_N})`. It is an asymptotic expansion in DLMF's sense when `Re α_s` is
strictly increasing. This is the Fourier counterpart of Watson's lemma
`Asymptotics.hasAsymptoticExpansion_laplace`. Unlike a Laplace integral, the Fourier integral of
a single term `t^{α-1}` diverges at `∞` once `Re α ≥ 1`, so the terms cannot be integrated
separately over `(0, ∞)`.

## Main results

* `Asymptotics.hasAsymptoticExpansion_fourier`: the expansion.

The improper integral exists under the same hypotheses, at every large `x`
(`Asymptotics.exists_tendsto_integral_cexp_smul_of_isBigO`, in
`TauCeti.Analysis.Asymptotics.Fourier.Endpoint`).

## Implementation notes

Fix `N`, an integer `n` exceeding `Re α_s` for `s ≤ N`, and `b > 0` such that the remainders
`R_k` of the expansions of the derivatives satisfy `‖R_k(t)‖ ≤ C t^{Re α_N - 1 - k}` on `(0, b]`
for `k ≤ n`. The integral over `(b, ∞)` has the endpoint expansion at `b` of DLMF 2.3.5
(`Asymptotics.hasAsymptoticExpansion_of_tendsto_integral_cexp_smul`). The integral over `(0, b)` is
split at `1/x` and integrated by parts `n` times over `(1/x, b)`, and its endpoint terms at `b`
cancel those of the integral over `(b, ∞)`. For the remainders every resulting piece is
`O(x^{-Re α_N})`. For a model term `t^{α-1}` the pieces, with the last integral taken over
`(1/x, ∞)`, are exactly `e^{iπα/2} Γ(α) x^{-α}`: they are the value at `z = -ix` of the Gamma
integral `∫₀^∞ t^{α-1} e^{-zt} dt = Γ(α) z^{-α}` for `Re z > 0`
(`Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`), split and integrated by parts in the
same way, which is continuous up to `Re z = 0` (`Complex.integral_cpow_mul_exp_mul_I_add_sum_eq`).

## References

* DLMF §2.3(iii), <https://dlmf.nist.gov/2.3.iii>.
-/

public section

noncomputable section

open Complex Filter Finset MeasureTheory Set intervalIntegral
open scoped ContDiff Real Topology

namespace Asymptotics

section Remainder

/-- The part near `0` of the Fourier integral of a family `g` of successive derivatives: the
integral of `e^{ixt} g₀(t)` over `(0, δ)`, the first `n` endpoint terms at `δ`, and the integral
of `e^{ixt} gₙ(t)` over `(δ, b)` left after `n` integrations by parts. -/
private def nearZero (x δ b : ℝ) (n : ℕ) (g : ℕ → ℝ → ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..δ, cexp (((x * t : ℝ) : ℂ) * I) * g 0 t) +
    ∑ k ∈ range n, (I / x) ^ (k + 1) * (cexp (((x * δ : ℝ) : ℂ) * I) * g k δ) +
    (I / x) ^ n * ∫ t in δ..b, cexp (((x * t : ℝ) : ℂ) * I) * g n t

/-- Splitting `(0, b)` at `δ` and integrating by parts `n` times on `(δ, b)`. -/
private theorem integral_eq_nearZero_sub {g : ℕ → ℝ → ℂ} {x δ b : ℝ} (hx : x ≠ 0) (hδb : δ ≤ b)
    {n : ℕ} (hcont : ∀ i ≤ n, ContinuousOn (g i) (Icc δ b))
    (hderiv : ∀ i < n, ∀ t ∈ Ioo δ b, HasDerivAt (g i) (g (i + 1) t) t)
    (h0 : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g 0 t) volume 0 δ) :
    ∫ t in (0 : ℝ)..b, cexp (((x * t : ℝ) : ℂ) * I) * g 0 t =
      nearZero x δ b n g -
        ∑ k ∈ range n, (I / x) ^ (k + 1) * (cexp (((x * b : ℝ) : ℂ) * I) * g k b) := by
  have hδ : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g 0 t) volume δ b :=
    (((by fun_prop : Continuous fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I))).continuousOn.mul
      (hcont 0 (Nat.zero_le n))).intervalIntegrable_of_Icc hδb
  have h := integral_cexp_smul_eq_sum_add_of_hasDerivAt hδb hx (fun i hi => hcont i hi.le)
    hderiv ((hcont n le_rfl).intervalIntegrable_of_Icc hδb)
  simp only [smul_eq_mul] at h
  rw [← integral_add_adjacent_intervals h0 hδ, h, nearZero]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- `nearZero` is linear in the family. -/
private theorem nearZero_add_sum {g : ℕ → ℝ → ℂ} {m : ℕ → ℕ → ℝ → ℂ} (c : ℕ → ℂ)
    {x δ b : ℝ} {n : ℕ} (N : ℕ)
    (hg0 : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g 0 t) volume 0 δ)
    (hgn : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g n t) volume δ b)
    (hm0 : ∀ s ∈ range N,
      IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * m s 0 t) volume 0 δ)
    (hmn : ∀ s ∈ range N,
      IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * m s n t) volume δ b) :
    nearZero x δ b n (fun k t => g k t + ∑ s ∈ range N, c s * m s k t) =
      nearZero x δ b n g + ∑ s ∈ range N, c s * nearZero x δ b n (m s) := by
  have hsum : ∀ {u v : ℝ} (k : ℕ),
      IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g k t) volume u v →
      (∀ s ∈ range N,
        IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * m s k t) volume u v) →
      ∫ t in u..v, cexp (((x * t : ℝ) : ℂ) * I) * (g k t + ∑ s ∈ range N, c s * m s k t) =
        (∫ t in u..v, cexp (((x * t : ℝ) : ℂ) * I) * g k t) +
          ∑ s ∈ range N, c s * ∫ t in u..v, cexp (((x * t : ℝ) : ℂ) * I) * m s k t := by
    intro u v k hg hm
    have hm' : ∀ s ∈ range N, IntervalIntegrable
        (fun t => c s * (cexp (((x * t : ℝ) : ℂ) * I) * m s k t)) volume u v :=
      fun s hs => (hm s hs).const_mul (c s)
    simp_rw [← intervalIntegral.integral_const_mul]
    have hs : IntervalIntegrable
        (fun t => ∑ s ∈ range N, c s * (cexp (((x * t : ℝ) : ℂ) * I) * m s k t)) volume u v := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum (range N) hm'
    rw [← intervalIntegral.integral_finsetSum hm', ← intervalIntegral.integral_add hg hs]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [mul_add, mul_sum]
    congr 1
    exact sum_congr rfl fun s _ => by ring
  simp only [nearZero]
  rw [hsum 0 hg0 hm0, hsum n hgn hmn]
  simp only [mul_add, sum_add_distrib]
  have hmid : ∑ k ∈ range n, (I / x) ^ (k + 1) * (cexp (((x * δ : ℝ) : ℂ) * I) *
      ∑ s ∈ range N, c s * m s k δ) = ∑ s ∈ range N, c s * ∑ k ∈ range n, (I / x) ^ (k + 1) *
        (cexp (((x * δ : ℝ) : ℂ) * I) * m s k δ) := by
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun s _ => sum_congr rfl fun k _ => by ring
  have hlast : (I / x) ^ n * ∑ s ∈ range N, c s * ∫ t in δ..b, cexp (((x * t : ℝ) : ℂ) * I) *
      m s n t = ∑ s ∈ range N, c s * ((I / x) ^ n * ∫ t in δ..b, cexp (((x * t : ℝ) : ℂ) * I) *
        m s n t) := by
    rw [mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [hmid, hlast]
  ring

/-- If `‖gₖ(t)‖ ≤ C t^{β-1-k}` on `(0, b]` for `k ≤ n`, with `0 < β < n`, then at `x = δ⁻¹` the
part of the Fourier integral near `0` is `O(δ^β)`. -/
private theorem norm_nearZero_inv_le {g : ℕ → ℝ → ℂ} {δ b β C : ℝ} {n : ℕ} (hβ : 0 < β)
    (hβn : β < n) (hδ : 0 < δ) (hδb : δ ≤ b)
    (hg : ∀ k ≤ n, ∀ t ∈ Ioc 0 b, ‖g k t‖ ≤ C * t ^ (β - 1 - k)) :
    ‖nearZero δ⁻¹ δ b n g‖ ≤ C * (β⁻¹ + n + (n - β)⁻¹) * δ ^ β := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hg 0 (Nat.zero_le n) δ ⟨hδ, hδb⟩)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hnorm : ∀ (t : ℝ) (z : ℂ), ‖cexp (((δ⁻¹ * t : ℝ) : ℂ) * I) * z‖ = ‖z‖ := fun t z => by
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
  have hI : ∀ k : ℕ, ‖(I / ((δ⁻¹ : ℝ) : ℂ)) ^ k‖ = δ ^ k := fun k => by
    rw [norm_pow, norm_div, norm_I, norm_real, Real.norm_of_nonneg (inv_nonneg.2 hδ.le), one_div,
      inv_inv]
  -- the integral over `(0, δ)`
  have h1 : ‖∫ t in (0 : ℝ)..δ, cexp (((δ⁻¹ * t : ℝ) : ℂ) * I) * g 0 t‖ ≤ C * β⁻¹ * δ ^ β := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hδ.le (g := fun t => C * t ^ (β - 1))
      (Eventually.of_forall fun t ht => ?_)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C)).trans_eq ?_
    · rw [hnorm]
      simpa using hg 0 (Nat.zero_le n) t ⟨ht.1, ht.2.trans hδb⟩
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        sub_add_cancel, Real.zero_rpow hβ.ne']
      ring
  -- the endpoint terms at `δ`
  have h2 : ‖∑ k ∈ range n, (I / ((δ⁻¹ : ℝ) : ℂ)) ^ (k + 1) *
      (cexp (((δ⁻¹ * δ : ℝ) : ℂ) * I) * g k δ)‖ ≤ n * (C * δ ^ β) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun k hk => ?_).trans_eq (by rw [sum_const, card_range, nsmul_eq_mul])
    rw [norm_mul, hI, hnorm]
    calc δ ^ (k + 1) * ‖g k δ‖ ≤ δ ^ (k + 1) * (C * δ ^ (β - 1 - k)) :=
          mul_le_mul_of_nonneg_left (hg k (mem_range.1 hk).le δ ⟨hδ, hδb⟩) (by positivity)
      _ = C * δ ^ β := by
          -- `Real.rpow_sub_natCast` splits off `δ^{k+1}` once the exponent is `β - ↑(k + 1)`.
          have hk : β - 1 - k = β - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
          rw [mul_left_comm, hk, Real.rpow_sub_natCast hδ.ne',
            mul_div_cancel₀ _ (pow_ne_zero _ hδ.ne')]
  -- the integral over `(δ, b)` after `n` integrations by parts
  have h3 : ‖(I / ((δ⁻¹ : ℝ) : ℂ)) ^ n * ∫ t in δ..b, cexp (((δ⁻¹ * t : ℝ) : ℂ) * I) * g n t‖ ≤
      C * (n - β)⁻¹ * δ ^ β := by
    rw [norm_mul, hI]
    calc δ ^ n * ‖∫ t in δ..b, cexp (((δ⁻¹ * t : ℝ) : ℂ) * I) * g n t‖
        ≤ δ ^ n * (C * (-δ ^ (β - 1 - n + 1) / (β - 1 - n + 1))) := by
          gcongr
          exact TauCeti.intervalIntegral.norm_integral_le_of_norm_le_mul_rpow_of_lt_neg_one
            (by linarith) hδ hδb hC (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
              (hnorm t _).trans_le (hg n le_rfl t ⟨hδ.trans ht.1, ht.2⟩))
      _ = C * (n - β)⁻¹ * δ ^ β := by
          have hne : (n : ℝ) - β ≠ 0 := by linarith
          -- Integrating `t^{β-1-n}` gave exponent `β - 1 - n + 1 = β - n`; split off `δ^n`.
          have hβ1 : β - 1 - n + 1 = β - n := by ring
          rw [hβ1, Real.rpow_sub_natCast hδ.ne', neg_div, ← div_neg, neg_sub]
          field_simp
  calc _ ≤ _ := norm_add₃_le
    _ ≤ C * β⁻¹ * δ ^ β + n * (C * δ ^ β) + C * (n - β)⁻¹ * δ ^ β := add_le_add_three h1 h2 h3
    _ = _ := by ring

/-- The part near `0` of the Fourier integral of the model family `t^{α-1}` and its
derivatives: the model value `e^{iπα/2} Γ(α) x^{-α}` minus the tail over `(b, ∞)` after `n`
integrations by parts. -/
private theorem nearZero_cpow_eq {α : ℂ} (hα : 0 < α.re) {n : ℕ} (hn : α.re < n) {x δ b : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδb : δ ≤ b) :
    nearZero x δ b n (fun k t => (descPochhammer ℂ k).eval (α - 1) * (t : ℂ) ^ (α - 1 - k)) =
      cexp (π * I * α / 2) * Gamma α * (x : ℂ) ^ (-α) -
        (I / x) ^ n * ((descPochhammer ℂ n).eval (α - 1) *
          ∫ t in Ioi b, (t : ℂ) ^ (α - 1 - n) * cexp (((x * t : ℝ) : ℂ) * I)) := by
  have hint := integrableOn_cpow_mul_exp_mul_I_Ioi (γ := α - 1 - n)
    (by simp only [sub_re, one_re, natCast_re]; linarith) x hδ
  rw [eq_sub_iff_add_eq, ← integral_cpow_mul_exp_mul_I_add_sum_eq hα hn hx hδ,
    ← Ioc_union_Ioi_eq_Ioi hδb,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hδb)),
    ← intervalIntegral.integral_of_le hδb]
  have h0 : ∫ t in (0 : ℝ)..δ, cexp (((x * t : ℝ) : ℂ) * I) *
      ((descPochhammer ℂ 0).eval (α - 1) * (t : ℂ) ^ (α - 1 - ((0 : ℕ) : ℂ))) =
      ∫ t in (0 : ℝ)..δ, (t : ℂ) ^ (α - 1) * cexp (((x * t : ℝ) : ℂ) * I) :=
    intervalIntegral.integral_congr fun t _ => by simp [mul_comm]
  have hn' : ∫ t in δ..b, cexp (((x * t : ℝ) : ℂ) * I) *
      ((descPochhammer ℂ n).eval (α - 1) * (t : ℂ) ^ (α - 1 - n)) =
      (descPochhammer ℂ n).eval (α - 1) *
        ∫ t in δ..b, (t : ℂ) ^ (α - 1 - n) * cexp (((x * t : ℝ) : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  have hk : ∑ k ∈ range n, (I / x) ^ (k + 1) * (cexp (((x * δ : ℝ) : ℂ) * I) *
      ((descPochhammer ℂ k).eval (α - 1) * (δ : ℂ) ^ (α - 1 - k))) =
      ∑ k ∈ range n, (I / x) ^ (k + 1) * ((descPochhammer ℂ k).eval (α - 1) *
        ((δ : ℂ) ^ (α - 1 - k) * cexp (((x * δ : ℝ) : ℂ) * I))) :=
    sum_congr rfl fun k _ => by ring
  simp only [nearZero, h0, hn', hk]
  ring

end Remainder

section Expansion

/-- The part beyond `b > 0` of the Fourier integral: if `F(x) = ∫₀^∞ e^{ixt} q(t) dt` for all
large `x` and `e^{ixt} q(t)` is integrable on `(0, b)`, then
`F(x) - ∫₀^b e^{ixt} q(t) dt = ∫_b^∞ e^{ixt} q(t) dt` minus its first `n` endpoint terms at `b`
is `O(x^{-β})` for `β ≤ n + 1`, by DLMF 2.3.5. -/
private theorem isBigO_sub_sum_of_tendsto_integral_Ioi {q : ℝ → ℂ} {F : ℝ → ℂ}
    (hq : ContDiffOn ℝ ∞ q (Ioi 0)) {b : ℝ} (hb : 0 < b)
    (hunif : ∀ k : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ T₀ : ℝ, ∀ x ≥ x₀, ∀ T ≥ T₀, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) * iteratedDerivWithin k q (Ioi 0) t‖ ≤ ε)
    (hint : ∀ x : ℝ, IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * q t) volume 0 b)
    (hF : ∀ᶠ x : ℝ in atTop, Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (((x * t : ℝ) : ℂ) * I) * q t) atTop (𝓝 (F x)))
    (n : ℕ) {β : ℝ} (hβ : β ≤ n + 1) :
    (fun x : ℝ => (F x - ∫ t in (0 : ℝ)..b, cexp (((x * t : ℝ) : ℂ) * I) * q t) -
      ∑ k ∈ range n, (I / x) ^ (k + 1) *
        (cexp (((x * b : ℝ) : ℂ) * I) * iteratedDerivWithin k q (Ioi 0) b))
      =O[atTop] fun x => x ^ (-β) := by
  have hqb : ContDiffOn ℝ ∞ q (Ici b) := hq.mono fun t (ht : b ≤ t) => hb.trans_le ht
  have hder : ∀ k : ℕ, ∀ t ∈ Ici b,
      iteratedDerivWithin k q (Ici b) t = iteratedDerivWithin k q (Ioi 0) t := fun k t ht =>
    hq.iteratedDerivWithin_eq_of_isOpen (by exact_mod_cast le_top) isOpen_Ioi (uniqueDiffOn_Ici b)
      (hb.trans_le ht) ht
  have hunif' : ∀ k : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ T₀ : ℝ, ∀ x ≥ x₀, ∀ T ≥ T₀, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin k q (Ici b) t‖ ≤ ε :=
    fun k => by
      obtain ⟨x₀, h⟩ := hunif k
      refine ⟨x₀, fun ε hε => ?_⟩
      obtain ⟨T₀, hT₀⟩ := h ε hε
      refine ⟨max T₀ b, fun x hx T hT T' hT' => ?_⟩
      rw [intervalIntegral.integral_congr fun t ht => ?_]
      · exact hT₀ x hx T (le_of_max_le_left hT) T' hT'
      · rw [uIcc_of_le hT'] at ht
        simp only [smul_eq_mul, hder k t ((le_of_max_le_right hT).trans ht.1)]
  -- the integral over `(b, ∞)`
  have hF' : ∀ᶠ x : ℝ in atTop, Tendsto
      (fun T : ℝ => ∫ t in b..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop
      (𝓝 (F x - ∫ t in (0 : ℝ)..b, cexp (((x * t : ℝ) : ℂ) * I) * q t)) := by
    filter_upwards [hF] with x hx
    simpa only [smul_eq_mul] using tendsto_integral_cexp_smul_sub hqb.continuousOn
      (by simpa only [smul_eq_mul] using hint x) (by simpa only [smul_eq_mul] using hx)
  have h := (hasAsymptoticExpansion_of_tendsto_integral_cexp_smul hqb hunif' hF').isBigO n
  refine (h.congr_left fun x => ?_).trans <| IsBigO.trans ?_
    (isBigO_const_div_pow_rpow_neg_atTop I (n := n + 1)
      (by push_cast; linarith))
  · refine congrArg _ (sum_congr rfl fun k _ => ?_)
    rw [smul_eq_mul, hder k b self_mem_Ici]
    ring
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]

/-- The tail `(i/x)^n P ∫_b^∞ e^{ixt} t^{α-1-n} dt` of a model term is `O(x^{-β})` for `β ≤ n`. -/
private theorem isBigO_tail {α : ℂ} {n : ℕ} (hn : α.re < n) {b β : ℝ} (hb : 0 < b)
    (hβ : β ≤ n) (P : ℂ) :
    (fun x : ℝ => (I / x) ^ n * (P * ∫ t in Ioi b, (t : ℂ) ^ (α - 1 - n) *
      cexp (((x * t : ℝ) : ℂ) * I))) =O[atTop] fun x => x ^ (-β) := by
  refine IsBigO.trans (g := fun x : ℝ => (I / (x : ℂ)) ^ n) ?_
    (isBigO_const_div_pow_rpow_neg_atTop I hβ)
  refine IsBigO.of_bound (‖P‖ * ∫ t in Ioi b, t ^ (α.re - 1 - n))
    (Eventually.of_forall fun x => ?_)
  have hK : ‖∫ t in Ioi b, (t : ℂ) ^ (α - 1 - n) * cexp (((x * t : ℝ) : ℂ) * I)‖ ≤
      ∫ t in Ioi b, t ^ (α.re - 1 - n) := by
    refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt (by linarith) hb) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : b < t)
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_cpow_eq_rpow_re_of_pos (hb.trans ht)]
    simp
  rw [norm_mul, norm_mul, mul_comm]
  gcongr

/-- If `‖gₖ(t)‖ ≤ C t^{β-1-k}` on `(0, b]` for `k ≤ n`, with `0 < β < n`, the part near `0` of
the Fourier integral, split at `1/x`, is `O(x^{-β})`. -/
private theorem isBigO_nearZero_inv {g : ℕ → ℝ → ℂ} {b β C : ℝ} {n : ℕ} (hβ : 0 < β)
    (hβn : β < n) (hb : 0 < b) (hg : ∀ k ≤ n, ∀ t ∈ Ioc 0 b, ‖g k t‖ ≤ C * t ^ (β - 1 - k)) :
    (fun x : ℝ => nearZero x x⁻¹ b n g) =O[atTop] fun x => x ^ (-β) := by
  refine IsBigO.of_bound (C * (β⁻¹ + n + (n - β)⁻¹)) ?_
  filter_upwards [eventually_gt_atTop b⁻¹] with x hx
  have hx0 : 0 < x := (inv_pos.2 hb).trans hx
  have h := norm_nearZero_inv_le hβ hβn (inv_pos.2 hx0) ((inv_lt_comm₀ hx0 hb).2 hx).le hg
  rwa [inv_inv, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le,
    ← Real.norm_of_nonneg (Real.rpow_nonneg hx0.le (-β))] at h

/-- The undifferentiated model term `t^{α - 1}`, `Re α > 0`, has integrable Fourier integrand on
`(0, b)`. Its derivatives are integrated only over intervals bounded away from `0`. -/
private theorem intervalIntegrable_cexp_mul_cpow {α : ℂ} (hα : 0 < α.re) (x : ℝ) {b : ℝ}
    (hb : 0 ≤ b) : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) *
      ((descPochhammer ℂ 0).eval (α - 1) * (t : ℂ) ^ (α - 1 - ((0 : ℕ) : ℂ)))) volume 0 b :=
  TauCeti.intervalIntegral.intervalIntegrable_of_norm_le_mul_sub_rpow_right (K := 1)
    (u := α.re - 1) (by linarith) hb (by fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
      simp [norm_cpow_eq_rpow_re_of_pos ht.1])

/-- The remainder after `N` terms of the expansion of the `k`-th derivative is continuous on
`(0, ∞)`. -/
private theorem continuousOn_iteratedDerivWithin_sub_sum {q : ℝ → ℂ}
    (hq : ContDiffOn ℝ ∞ q (Ioi 0)) (c α : ℕ → ℂ) (N k : ℕ) :
    ContinuousOn (fun t : ℝ => iteratedDerivWithin k q (Ioi 0) t - ∑ s ∈ range N,
      c s * ((descPochhammer ℂ k).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - k))) (Ioi 0) :=
  (hq.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) (uniqueDiffOn_Ioi 0)).sub
    (continuousOn_finsetSum _ fun s _ => continuousOn_const.mul fun t ht =>
      ((continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).const_mul
        _).continuousWithinAt)

/-- If the derivatives of `q` are `gₖ + ∑_{s<N} c_s (d/dt)^k t^{α_s - 1}` with `Re α_s > 0` and
`e^{ixt} g₀(t)` is integrable on `(0, b)`, then so is `e^{ixt} q(t)`. -/
private theorem intervalIntegrable_cexp_mul_of_eq_add_sum {q : ℝ → ℂ} {α c : ℕ → ℂ} {N n : ℕ}
    (hα : ∀ s < N, 0 < (α s).re ∧ (α s).re < n) {g : ℕ → ℝ → ℂ}
    (hg : ∀ k t, iteratedDerivWithin k q (Ioi 0) t = g k t + ∑ s ∈ range N,
      c s * ((descPochhammer ℂ k).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - k))) {b x : ℝ}
    (hb : 0 ≤ b)
    (hg0 : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g 0 t) volume 0 b) :
    IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * q t) volume 0 b := by
  have h := hg0.add (IntervalIntegrable.sum (range N) fun s hs =>
    (intervalIntegrable_cexp_mul_cpow (hα s (mem_range.1 hs)).1 x hb).const_mul (c s))
  refine h.congr_ae (Eventually.of_forall fun t => ?_)
  have hq0 := hg 0 t
  rw [iteratedDerivWithin_zero] at hq0
  simp only [Finset.sum_apply, hq0, mul_add, mul_sum]
  exact congrArg _ (sum_congr rfl fun s _ => by ring)

/-- The decomposition of the Fourier integral over `(0, b)`, for `x > 1/b`. Write the
derivatives of `q` as `gₖ + ∑_{s<N} c_s (d/dt)^k t^{α_s - 1}`. Split at `1/x` and integrate by
parts `n` times on `(1/x, b)`: the integral is the part of `g` near `0`, plus the model terms
`e^{iπα_s/2} Γ(α_s) c_s x^{-α_s}` less their tails over `(b, ∞)`, minus the endpoint terms at
`b`. -/
private theorem integral_eq_nearZero_add_sum {q : ℝ → ℂ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {α c : ℕ → ℂ} {N n : ℕ} (hα : ∀ s < N, 0 < (α s).re ∧ (α s).re < n) {g : ℕ → ℝ → ℂ}
    (hg : ∀ k t, iteratedDerivWithin k q (Ioi 0) t = g k t + ∑ s ∈ range N,
      c s * ((descPochhammer ℂ k).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - k)))
    (hgc : ∀ k, ContinuousOn (g k) (Ioi 0)) {b x : ℝ} (hb : 0 < b) (hx : b⁻¹ < x)
    (hg0 : IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * g 0 t) volume 0 b) :
    ∫ t in (0 : ℝ)..b, cexp (((x * t : ℝ) : ℂ) * I) * q t =
      nearZero x x⁻¹ b n g + ∑ s ∈ range N,
        ((x : ℂ) ^ (-α s) • (cexp (π * I * α s / 2) * Gamma (α s) * c s) -
          c s * ((I / x) ^ n * ((descPochhammer ℂ n).eval (α s - 1) *
            ∫ t in Ioi b, (t : ℂ) ^ (α s - 1 - n) * cexp (((x * t : ℝ) : ℂ) * I)))) -
      ∑ k ∈ range n, (I / x) ^ (k + 1) *
        (cexp (((x * b : ℝ) : ℂ) * I) * iteratedDerivWithin k q (Ioi 0) b) := by
  have hx0 : 0 < x := (inv_pos.2 hb).trans hx
  have hδ : 0 < x⁻¹ := inv_pos.2 hx0
  have hδb : x⁻¹ ≤ b := (inv_lt_comm₀ hx0 hb).2 hx |>.le
  have hsub : uIcc 0 x⁻¹ ⊆ uIcc 0 b := uIcc_subset_uIcc_left (mem_uIcc_of_le hδ.le hδb)
  have hIcc : Icc x⁻¹ b ⊆ Ioi 0 := fun t ht => hδ.trans_le ht.1
  have hcont : ∀ f : ℝ → ℂ, ContinuousOn f (Ioi 0) → IntervalIntegrable
      (fun t => cexp (((x * t : ℝ) : ℂ) * I) * f t) volume x⁻¹ b := fun f hf =>
    (((by fun_prop : Continuous fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I))).continuousOn.mul
      (hf.mono hIcc)).intervalIntegrable_of_Icc hδb
  have hmc : ∀ s k, ContinuousOn (fun t : ℝ => (descPochhammer ℂ k).eval (α s - 1) *
      (t : ℂ) ^ (α s - 1 - k)) (Ioi 0) := fun s k t ht =>
    ((continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).const_mul _).continuousWithinAt
  have hm0 : ∀ s ∈ range N, IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) *
      ((descPochhammer ℂ 0).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - ((0 : ℕ) : ℂ)))) volume 0 b :=
    fun s hs => intervalIntegrable_cexp_mul_cpow (hα s (mem_range.1 hs)).1 x hb.le
  have hA := integral_eq_nearZero_sub (g := fun k => iteratedDerivWithin k q (Ioi 0)) hx0.ne'
    hδb (n := n) (fun i _ => (hq.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top)
      (uniqueDiffOn_Ioi 0)).mono hIcc)
    (fun i _ t ht => hq.hasDerivAt_iteratedDerivWithin (by exact_mod_cast ENat.natCast_lt_top i)
      (Ioi_mem_nhds (hδ.trans ht.1)))
    (by simpa using (intervalIntegrable_cexp_mul_of_eq_add_sum hα hg hb.le hg0).mono_set hsub)
  have hB := nearZero_add_sum (m := fun s k t => (descPochhammer ℂ k).eval (α s - 1) *
    (t : ℂ) ^ (α s - 1 - k)) c N (hg0.mono_set hsub) (hcont _ (hgc n))
    (fun s hs => (hm0 s hs).mono_set hsub) (fun s _ => hcont _ (hmc s n))
  have hfam : (fun k t => g k t + ∑ s ∈ range N, c s * ((descPochhammer ℂ k).eval (α s - 1) *
      (t : ℂ) ^ (α s - 1 - k))) = fun k => iteratedDerivWithin k q (Ioi 0) := by
    funext k t; rw [hg]
  rw [hfam] at hB
  simp only [iteratedDerivWithin_zero] at hA
  rw [hA, hB]
  congr 2
  exact sum_congr rfl fun s hs => by
    rw [nearZero_cpow_eq (hα s (mem_range.1 hs)).1 (hα s (mem_range.1 hs)).2 hx0 hδ hδb,
      smul_eq_mul]
    ring

/-- **The Fourier analogue of Watson's lemma** (DLMF 2.3.20). Let `Re α_s > 0` for all `s`, and
let `q` be smooth on `(0, ∞)` with, for all `k` and `N`,
`q^{(k)}(t) - ∑_{s<N} c_s (α_s - 1)⋯(α_s - k) t^{α_s - 1 - k} = O(t^{Re α_N - 1 - k})` as
`t → 0+`, the derivatives taken within `(0, ∞)`. Suppose each `∫ e^{ixt} q^{(k)}(t) dt` converges
at `∞` uniformly for all large `x`. If `F x` is the improper integral `∫₀^∞ e^{ixt} q(t) dt` for
all large `x` (under these hypotheses it exists at every large `x` by
`Asymptotics.exists_tendsto_integral_cexp_smul_of_isBigO`), then
`F x ∼ ∑ e^{iπα_s/2} Γ(α_s) c_s x^{-α_s}` as `x → +∞`, in the sense of `HasAsymptoticExpansion`:
for every `N` the remainder after `N` terms is `O(x^{-Re α_N})`. -/
theorem hasAsymptoticExpansion_fourier {q : ℝ → ℂ} {α c : ℕ → ℂ} {F : ℝ → ℂ}
    (hα : ∀ s, 0 < (α s).re) (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    (hexp : ∀ k N, (fun t : ℝ => iteratedDerivWithin k q (Ioi 0) t -
        ∑ s ∈ range N, c s * (descPochhammer ℂ k).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - k))
      =O[𝓝[>] 0] fun t => t ^ ((α N).re - 1 - k))
    (hunif : ∀ k : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ T₀ : ℝ, ∀ x ≥ x₀, ∀ T ≥ T₀, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) * iteratedDerivWithin k q (Ioi 0) t‖ ≤ ε)
    (hF : ∀ᶠ x : ℝ in atTop, Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (((x * t : ℝ) : ℂ) * I) * q t) atTop (𝓝 (F x))) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (x : ℂ) ^ (-α s))
      (fun s => cexp (π * I * α s / 2) * Gamma (α s) * c s) F := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  set β := (α N).re
  -- the number `n` of integrations by parts exceeds the real parts of the exponents up to `N`
  obtain ⟨n, hn⟩ := exists_nat_gt (∑ s ∈ range (N + 1), (α s).re)
  have hαn : ∀ s ≤ N, (α s).re < n := fun s hs => (Finset.single_le_sum
    (fun j _ => (hα j).le) (mem_range.2 (Nat.lt_succ_of_le hs))).trans_lt hn
  -- the remainders `R k` of the expansions of the derivatives, bounded on some `(0, b]`
  set R : ℕ → ℝ → ℂ := fun k t => iteratedDerivWithin k q (Ioi 0) t - ∑ s ∈ range N,
    c s * ((descPochhammer ℂ k).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - k)) with hRdef
  obtain ⟨C, b, hb, hRb⟩ := exists_forall_norm_le_mul_rpow_of_isBigO (f := R)
    (e := fun k => β - 1 - k) n fun k _ =>
    (hexp k N).congr_left fun t => by simp only [hRdef, mul_assoc]
  have hRc : ∀ k, ContinuousOn (R k) (Ioi 0) := fun k =>
    continuousOn_iteratedDerivWithin_sub_sum hq c α N k
  have hR0 : ∀ x : ℝ, IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) * R 0 t)
      volume 0 b := fun x =>
    (TauCeti.intervalIntegral.intervalIntegrable_of_norm_le_mul_sub_rpow_right (u := β - 1)
      (by linarith [hα N]) hb.le (((hRc 0).mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
          simpa using hRb 0 (Nat.zero_le n) t ht)).continuousOn_mul
      (by fun_prop : Continuous fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I)).continuousOn
  have hg : ∀ k t, iteratedDerivWithin k q (Ioi 0) t = R k t + ∑ s ∈ range N,
      c s * ((descPochhammer ℂ k).eval (α s - 1) * (t : ℂ) ^ (α s - 1 - k)) := fun k t =>
    (sub_add_cancel _ _).symm
  have hαN : ∀ s < N, 0 < (α s).re ∧ (α s).re < n := fun s hs => ⟨hα s, hαn s hs.le⟩
  -- the decomposition, and the bound `O(x^{-β})` on each part
  have hdec : ∀ᶠ x : ℝ in atTop, F x - ∑ s ∈ range N,
      (x : ℂ) ^ (-α s) • (cexp (π * I * α s / 2) * Gamma (α s) * c s) =
      nearZero x x⁻¹ b n R - ∑ s ∈ range N, c s * ((I / x) ^ n * ((descPochhammer ℂ n).eval
        (α s - 1) * ∫ t in Ioi b, (t : ℂ) ^ (α s - 1 - n) * cexp (((x * t : ℝ) : ℂ) * I))) +
      ((F x - ∫ t in (0 : ℝ)..b, cexp (((x * t : ℝ) : ℂ) * I) * q t) -
        ∑ k ∈ range n, (I / x) ^ (k + 1) *
          (cexp (((x * b : ℝ) : ℂ) * I) * iteratedDerivWithin k q (Ioi 0) b)) := by
    filter_upwards [eventually_gt_atTop b⁻¹] with x hx
    rw [integral_eq_nearZero_add_sum hq hαN hg hRc hb hx (hR0 x), sum_sub_distrib]
    ring
  have hT := IsBigO.fun_sum fun s hs => (isBigO_tail (hαn s (mem_range.1 hs).le) hb
    (hαn N le_rfl).le ((descPochhammer ℂ n).eval (α s - 1))).const_mul_left (c s)
  -- the part of the integral beyond `b`
  have hE := isBigO_sub_sum_of_tendsto_integral_Ioi hq hb hunif
    (fun x => intervalIntegrable_cexp_mul_of_eq_add_sum hαN hg hb.le (hR0 x)) hF n (β := β)
    (by linarith [hαn N le_rfl])
  have hnorm : (fun x : ℝ => x ^ (-β)) =ᶠ[atTop] fun x => ‖(x : ℂ) ^ (-α N)‖ := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  exact isBigO_norm_right.mp (((((isBigO_nearZero_inv (hα N) (hαn N le_rfl) hb hRb).sub
    hT).add hE).congr' (hdec.mono fun x hx => hx.symm) EventuallyEq.rfl).congr'
      EventuallyEq.rfl hnorm)

end Expansion

end Asymptotics
