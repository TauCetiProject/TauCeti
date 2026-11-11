/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Analysis.Analytic.Order

/-!
# Dividing an analytic function by prescribed zeros

If an analytic function `f` vanishes to order at least `k x` at each point `x` of a finite set
`s`, then `f` factors globally as `f z = (∏ x ∈ s, (z - x) ^ k x) • g z`, where `g` is analytic
wherever `f` is. The quotient `g` is obtained by repeatedly taking divided differences
`dslope · x`, each of which lowers the order of vanishing at `x` by one
(`AnalyticAt.analyticOrderAt_dslope_add_one`).

Over `ℂ` this is the factorization of an entire function with zeros of prescribed multiplicities
used in transcendence proofs, where `g` is then estimated by the maximum modulus principle. The
order hypotheses may be given as vanishing of derivatives through Mathlib's
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`.

## Main results

* `HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff`: the iterated divided differences of `f` at
  `a` take the Taylor coefficients of `f` at `a` as their values at `a`.
* `TauCeti.iterate_dslope_apply_eq_zero_of_lt`: if `f` vanishes to order at least `n` at `a`,
  then the first `n` iterated divided differences of `f` at `a` vanish at `a`.
* `AnalyticOnNhd.exists_eq_prod_pow_smul`: an analytic function with zeros of orders at least
  `k x` at the points `x ∈ s` is `∏ x ∈ s, (z - x) ^ k x` times an analytic function.
* `TauCeti.differentiableAt_of_eventuallyEq_div`: the removable singularity of a quotient `A / B`
  of two functions analytic and vanishing at `a`, with `deriv B a = b ≠ 0` and
  `deriv A a = c * b`, is differentiable once filled by the value `c`.

## References

* J.-H. Evertse, *Diophantine approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.24.
-/

public section

open Function Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : 𝕜}

/-- Iterated divided differences at `a` preserve analyticity at every point where `f` is
analytic. -/
theorem AnalyticAt.iterate_dslope {z : 𝕜} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 ((swap dslope a)^[n] f) z := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [iterate_succ_apply']; exact ih.dslope a

/-- The `n`-th iterated divided difference at `z₀` of a function with power series `p` at `z₀`
takes the value `p.coeff n` at `z₀`: these values are the Taylor coefficients. -/
theorem HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff {p : FormalMultilinearSeries 𝕜 𝕜 E}
    {z₀ : 𝕜} (hp : HasFPowerSeriesAt f p z₀) (n : ℕ) : (swap dslope z₀)^[n] f z₀ = p.coeff n := by
  rw [← (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1,
    ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]

namespace TauCeti

/-- **Removable singularity of a quotient of analytic functions with a simple zero.** If `A` and
`B` are analytic and vanish at `a`, with `deriv A a = c * b` and `deriv B a = b ≠ 0`, then every
function `H` with `H a = c` that equals `A / B` on a punctured neighbourhood of `a` is
differentiable at `a`. -/
theorem differentiableAt_of_eventuallyEq_div {A B H : 𝕜 → 𝕜} {c b : 𝕜}
    (hA : AnalyticAt 𝕜 A a) (hB : AnalyticAt 𝕜 B a) (hA₀ : A a = 0) (hB₀ : B a = 0)
    (hdA : HasDerivAt A (c * b) a) (hdB : HasDerivAt B b a) (hb : b ≠ 0) (hHa : H a = c)
    (hH : ∀ᶠ x in 𝓝[≠] a, H x = A x / B x) : DifferentiableAt 𝕜 H a := by
  have hBd : dslope B a a ≠ 0 := by
    rwa [dslope_same, hdB.deriv]
  refine ((hA.dslope a).differentiableAt.div (hB.dslope a).differentiableAt
    hBd).congr_of_eventuallyEq ?_
  filter_upwards [eventually_nhdsWithin_iff.mp hH] with x hx
  by_cases hx₀ : x = a
  · subst hx₀
    simp only [hHa, Pi.div_apply, dslope_same, hdA.deriv, hdB.deriv]
    exact (mul_div_cancel_right₀ c hb).symm
  · rw [hx hx₀, Pi.div_apply, dslope_of_ne _ hx₀, dslope_of_ne _ hx₀, slope_def_field,
      slope_def_field, hA₀, hB₀, sub_zero, sub_zero,
      div_div_div_cancel_right₀ (sub_ne_zero.mpr hx₀)]

/-- If `f` vanishes to order at least `n` at `a`, then each of the first `n` iterated divided
differences `(swap dslope a)^[k] f`, `k < n`, vanishes at `a`. -/
theorem iterate_dslope_apply_eq_zero_of_lt {n k : ℕ} (hn : (n : ℕ∞) ≤ analyticOrderAt f a)
    (hk : k < n) : (swap dslope a)^[k] f a = 0 := by
  induction k generalizing f n with
  | zero => exact apply_eq_zero_of_analyticOrderAt_ne_zero (lt_of_lt_of_le (mod_cast hk) hn).ne'
  | succ k ih =>
    obtain ⟨hfa, ha⟩ := analyticOrderAt_ne_zero.mp
      (lt_of_lt_of_le (mod_cast Nat.zero_lt_of_lt hk) hn).ne'
    rw [iterate_succ_apply]
    refine ih (n := n - 1) ?_ (by lia)
    -- `n` is positive, so its cast is `↑(n - 1) + 1`; cancelling the `+ 1` against the order
    -- `analyticOrderAt (dslope f a) a + 1` of `f` gives the hypothesis for the next divided
    -- difference.
    have hn₁ : (n : ℕ∞) = ((n - 1 : ℕ) : ℕ∞) + 1 := by norm_cast; lia
    rw [← hfa.analyticOrderAt_dslope_add_one ha, hn₁] at hn
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp hn

end TauCeti

/-- **Division by prescribed zeros.** If `f` is analytic on a neighbourhood of `U` and vanishes
to order at least `k x` at each point `x` of a finite set `s`, then
`f z = (∏ x ∈ s, (z - x) ^ k x) • g z` for all `z` and some `g` analytic on a neighbourhood of
`U`. -/
theorem AnalyticOnNhd.exists_eq_prod_pow_smul {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (s : Finset 𝕜) (k : 𝕜 → ℕ) (hk : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt f x) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ ∀ z, f z = (∏ x ∈ s, (z - x) ^ k x) • g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp⟩
  | insert a s ha ih =>
    set g₁ := (swap dslope a)^[k a] f
    have hfg₁ (z : 𝕜) : f z = (z - a) ^ k a • g₁ z :=
      (pow_sub_smul_iterate_dslope_of_zero (k a)
        (fun j hj ↦ TauCeti.iterate_dslope_apply_eq_zero_of_lt
          (hk a (Finset.mem_insert_self a s)) hj)
        z).symm
    have hk₁ : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt g₁ x := by
      intro x hx
      rcases eq_or_ne (k x) 0 with h0 | h0
      · simp [h0]
      have hkx := hk x (Finset.mem_insert_of_mem hx)
      have hfx : AnalyticAt 𝕜 f x :=
        (analyticOrderAt_ne_zero.mp (lt_of_lt_of_le (mod_cast Nat.pos_of_ne_zero h0) hkx).ne').1
      have hxa : x ≠ a := fun h ↦ ha (h ▸ hx)
      have hpow : analyticOrderAt (fun z ↦ (z - a) ^ k a) x = 0 :=
        analyticOrderAt_eq_zero.mpr (.inr (pow_ne_zero _ (sub_ne_zero.mpr hxa)))
      have hfeq : f = (fun z ↦ (z - a) ^ k a) • g₁ := funext hfg₁
      rwa [hfeq, analyticOrderAt_smul (by fun_prop) (hfx.iterate_dslope (k a)), hpow,
        zero_add] at hkx
    obtain ⟨g, hg, hg₁⟩ := ih (f := g₁) (fun z hz ↦ (hf z hz).iterate_dslope (k a)) hk₁
    refine ⟨g, hg, fun z ↦ ?_⟩
    rw [hfg₁, hg₁, Finset.prod_insert ha, mul_smul]
