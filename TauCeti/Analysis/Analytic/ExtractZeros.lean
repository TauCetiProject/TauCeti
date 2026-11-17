/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.RingTheory.Polynomial.HermiteInterpolation

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
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`, and in characteristic zero prescribed
finite jets at a finite set of nodes can first be interpolated by an entire polynomial map
(`TauCeti.exists_analyticOnNhd_iteratedDeriv_eq`) built from `TauCeti.hermiteBasis`.

## Main results

* `HasFPowerSeriesAt.iterate_dslope_apply_eq_coeff`: the iterated divided differences of `f` at
  `a` take the Taylor coefficients of `f` at `a` as their values at `a`.
* `TauCeti.iterate_dslope_apply_eq_zero_of_lt`: if `f` vanishes to order at least `n` at `a`,
  then the first `n` iterated divided differences of `f` at `a` vanish at `a`.
* `TauCeti.exists_analyticOnNhd_iteratedDeriv_eq`: vector-valued Hermite interpolation by an
  entire map matching prescribed iterated derivatives on a finite set of nodes.
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
open scoped Nat Polynomial

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

/-- **Vector-valued Hermite interpolation.** Over a normed field `𝕜` of characteristic zero,
for any finite set of nodes `s`, multiplicities `m : 𝕜 → ℕ`, and target values `c : 𝕜 → ℕ → E` in
a normed `𝕜`-vector space `E`, there is an entire (polynomial-combination) map `P : 𝕜 → E` with
`iteratedDeriv k P a = c a k` for all `a ∈ s` and `k < m a`. -/
theorem exists_analyticOnNhd_iteratedDeriv_eq [CharZero 𝕜]
    (s : Finset 𝕜) (m : 𝕜 → ℕ) (c : 𝕜 → ℕ → E) :
    ∃ P : 𝕜 → E, AnalyticOnNhd 𝕜 P Set.univ ∧
      ∀ a ∈ s, ∀ k < m a, iteratedDeriv k P a = c a k := by
  classical
  let m' : s → ℕ := fun i ↦ m i
  let b := hermiteBasis m' Subtype.val_injective
  let P : 𝕜 → E := fun z ↦
    ∑ x : (i : s) × Fin (m' i),
      ((b x : 𝕜[X]).eval z) • (((x.2 : ℕ)! : 𝕜)⁻¹ • c x.1 x.2)
  refine ⟨P, Finset.analyticOnNhd_fun_sum _ fun x _ ↦
      (AnalyticOnNhd.eval_polynomial _).smul analyticOnNhd_const, fun a ha k hk ↦ ?_⟩
  have hpoly (p : 𝕜[X]) : ContDiffAt 𝕜 k (fun z ↦ p.eval z) a := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
      (p.contDiff_aeval (𝕜 := 𝕜) k).contDiffAt (x := a)
  have hterm (x : (i : s) × Fin (m' i)) :
      ContDiffAt 𝕜 k
        (fun z ↦ ((b x : 𝕜[X]).eval z) • (((x.2 : ℕ)! : 𝕜)⁻¹ • c x.1 x.2)) a :=
    (hpoly _).smul contDiffAt_const
  dsimp only [P]
  rw [iteratedDeriv_fun_sum fun x _ ↦ hterm x]
  let x₀ : (i : s) × Fin (m' i) := ⟨⟨a, ha⟩, ⟨k, hk⟩⟩
  rw [Finset.sum_eq_single x₀]
  · rw [iteratedDeriv_smul_const (hpoly _),
      Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv]
    have hjet : (Polynomial.hasseDeriv k (b x₀ : 𝕜[X])).eval a = 1 := by
      have h := congr_fun (congr_fun (hermiteJet_hermiteBasis m' Subtype.val_injective x₀) x₀.1)
        x₀.2
      simp only [hermiteJet_apply, Pi.single_eq_same, x₀, m'] at h
      exact h
    rw [hjet, mul_one, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)), one_smul]
  · intro x _ hne
    rw [iteratedDeriv_smul_const (hpoly _),
      Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv]
    have hjet : (Polynomial.hasseDeriv k (b x : 𝕜[X])).eval a = 0 := by
      have h := congr_fun (congr_fun (hermiteJet_hermiteBasis m' Subtype.val_injective x) x₀.1)
        x₀.2
      simp only [hermiteJet_apply, x₀, m'] at h
      rw [h]
      cases x with
      | mk xi xk =>
        by_cases h1 : xi = ⟨a, ha⟩
        · subst h1
          have h2 : xk ≠ ⟨k, hk⟩ := fun hEq ↦ hne (by subst hEq; rfl)
          simp [Pi.single_eq_same, Pi.single_eq_of_ne' h2]
        · simp [Pi.single_eq_of_ne' h1]
    rw [hjet, mul_zero, zero_smul]
  · simp

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
