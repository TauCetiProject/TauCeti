/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.Binomial
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Finite-order power-series expansions along a filter

Let `w` tend to `0` along a filter `l`. A function `F` has the expansion `P : PowerSeries 𝕜` to
order `N` along `w` when `F - (trunc N P).eval ∘ w = O(w ^ N)`. Such expansions are needed when
a function is only known to finitely many orders, so that `Asymptotics.HasAsymptoticExpansion`
with the scale `wⁿ` does not apply. This file shows that they are compatible with polynomials,
sums and products.

## Main results

* `Polynomial.isBigO_eval_of_X_pow_dvd`: if `X ^ N ∣ p`, then `p.eval ∘ w = O(w ^ N)`.
* `Polynomial.isBigO_eval_sub_eval_trunc_coe`: a polynomial has itself as expansion to every
  order.
* `PowerSeries.isBigO_add_sub_eval_trunc_add`, `PowerSeries.isBigO_sum_sub_eval_trunc_sum`,
  `PowerSeries.isBigO_mul_sub_eval_trunc_mul`: expansions add and multiply.
* `PowerSeries.isBigO_one_of_isBigO_sub_eval_trunc`: a function with an expansion is bounded.
* `TauCeti.isBigO_one_add_mul_cpow_sub_eval_trunc`: `(1 + j w)^c` has the binomial series
  `∑ C(c, m) jᵐ Xᵐ` as expansion to every order along `w → 0`.
-/

public section

open Filter Finset Asymptotics
open scoped Topology

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

namespace Polynomial

/-- If `X ^ N` divides `p` and `w → 0`, then `p (w) = O(w ^ N)`. -/
theorem isBigO_eval_of_X_pow_dvd (hw : Tendsto w l (𝓝 0)) {N : ℕ} {p : 𝕜[X]}
    (hp : X ^ N ∣ p) : (fun i ↦ p.eval (w i)) =O[l] fun i ↦ w i ^ N := by
  obtain ⟨q, rfl⟩ := hp
  simpa using (isBigO_refl (fun i ↦ w i ^ N) l).mul
    (((q.continuous.tendsto 0).comp hw).isBigO_one 𝕜)

/-- A polynomial has itself as expansion to every order. -/
theorem isBigO_eval_sub_eval_trunc_coe (hw : Tendsto w l (𝓝 0)) (N : ℕ) (p : 𝕜[X]) :
    (fun i ↦ p.eval (w i) - (PowerSeries.trunc N (p : PowerSeries 𝕜)).eval (w i)) =O[l]
      fun i ↦ w i ^ N := by
  refine (isBigO_eval_of_X_pow_dvd hw (p := p - PowerSeries.trunc N (p : PowerSeries 𝕜))
    (X_pow_dvd_iff.2 fun d hd ↦ ?_)).congr_left fun i ↦ by simp
  simp [PowerSeries.coeff_trunc, hd]

end Polynomial

namespace PowerSeries

variable {N : ℕ} {F G : α → 𝕜} {P Q : PowerSeries 𝕜}

/-- If `F` and `G` have the expansions `P` and `Q` to order `N` along `w`, then `F + G` has the
expansion `P + Q`. -/
theorem isBigO_add_sub_eval_trunc_add
    (hF : (fun i ↦ F i - (trunc N P).eval (w i)) =O[l] fun i ↦ w i ^ N)
    (hG : (fun i ↦ G i - (trunc N Q).eval (w i)) =O[l] fun i ↦ w i ^ N) :
    (fun i ↦ F i + G i - (trunc N (P + Q)).eval (w i)) =O[l] fun i ↦ w i ^ N :=
  (hF.add hG).congr_left fun i ↦ by simp only [map_add, Polynomial.eval_add]; ring

/-- If each `F k` has the expansion `P k` to order `N` along `w`, then `∑ k ∈ s, F k` has the
expansion `∑ k ∈ s, P k`. -/
theorem isBigO_sum_sub_eval_trunc_sum {κ : Type*} (s : Finset κ) {F : κ → α → 𝕜}
    {P : κ → PowerSeries 𝕜}
    (h : ∀ k ∈ s, (fun i ↦ F k i - (trunc N (P k)).eval (w i)) =O[l] fun i ↦ w i ^ N) :
    (fun i ↦ ∑ k ∈ s, F k i - (trunc N (∑ k ∈ s, P k)).eval (w i)) =O[l] fun i ↦ w i ^ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBigO_zero (fun i ↦ w i ^ N) l
  | insert k s hk ih =>
    simp only [sum_insert hk]
    exact isBigO_add_sub_eval_trunc_add (h k (mem_insert_self k s))
      (ih fun k' hk' ↦ h k' (mem_insert_of_mem hk'))

/-- A function with an expansion along `w → 0` is bounded. -/
theorem isBigO_one_of_isBigO_sub_eval_trunc (hw : Tendsto w l (𝓝 0))
    (hF : (fun i ↦ F i - (trunc N P).eval (w i)) =O[l] fun i ↦ w i ^ N) :
    F =O[l] fun _ ↦ (1 : 𝕜) := by
  have hpow : (fun i ↦ w i ^ N) =O[l] fun _ ↦ (1 : 𝕜) :=
    (((continuous_pow N).tendsto 0).comp hw).isBigO_one 𝕜
  exact ((hF.trans hpow).add ((((trunc N P).continuous.tendsto 0).comp hw).isBigO_one 𝕜))
    |>.congr_left fun i ↦ by simp

/-- If `F` and `G` have the expansions `P` and `Q` to order `N` along `w → 0`, then `F * G` has
the expansion `P * Q`. -/
theorem isBigO_mul_sub_eval_trunc_mul (hw : Tendsto w l (𝓝 0))
    (hF : (fun i ↦ F i - (trunc N P).eval (w i)) =O[l] fun i ↦ w i ^ N)
    (hG : (fun i ↦ G i - (trunc N Q).eval (w i)) =O[l] fun i ↦ w i ^ N) :
    (fun i ↦ F i * G i - (trunc N (P * Q)).eval (w i)) =O[l] fun i ↦ w i ^ N := by
  -- the product of the truncations agrees with the truncated product below degree `N`
  have hdvd : Polynomial.X ^ N ∣ trunc N P * trunc N Q - trunc N (P * Q) := by
    refine Polynomial.X_pow_dvd_iff.2 fun d hd ↦ ?_
    rw [Polynomial.coeff_sub, ← trunc_trunc_mul_trunc, coeff_trunc, ← Polynomial.coe_mul,
      Polynomial.coeff_coe]
    simp [hd]
  have h1 := (hF.mul (isBigO_one_of_isBigO_sub_eval_trunc hw hG)).congr_right fun i ↦ mul_one _
  have h2 := (((((trunc N P).continuous.tendsto 0).comp hw).isBigO_one 𝕜).mul hG).congr_right
    fun i ↦ one_mul _
  refine ((h1.add h2).add (Polynomial.isBigO_eval_of_X_pow_dvd hw hdvd)).congr_left fun i ↦ ?_
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_mul]
  ring

end PowerSeries

namespace TauCeti

/-- The binomial expansion `(1 + j w)^c = ∑_{m < K} C(c, m) jᵐ wᵐ + O(w^K)` along `w → 0`: the
function `(1 + j w)^c` has the binomial series `∑ C(c, m) jᵐ Xᵐ` as expansion to order `K`. -/
theorem isBigO_one_add_mul_cpow_sub_eval_trunc {w : α → ℂ} (hw : Tendsto w l (𝓝 0)) (j c : ℂ)
    (K : ℕ) :
    (fun i ↦ (1 + j * w i) ^ c -
      (PowerSeries.trunc K (PowerSeries.mk fun m ↦ Ring.choose c m * j ^ m)).eval (w i)) =O[l]
      fun i ↦ w i ^ K := by
  have hjw : Tendsto (fun i ↦ j * w i) l (𝓝 0) := by simpa using hw.const_mul j
  have hscale : (fun i ↦ (j * w i) ^ K) =O[l] fun i ↦ w i ^ K :=
    ((isBigO_refl _ _).const_mul_left (j ^ K)).congr_left fun i ↦ (mul_pow _ _ _).symm
  refine (((isBigO_one_add_cpow_sub_sum c K).comp_tendsto hjw).trans hscale).congr_left
    fun i ↦ ?_
  simp only [Function.comp_apply, PowerSeries.eval_trunc, PowerSeries.coeff_mk, sub_right_inj]
  exact sum_congr rfl fun _ _ ↦ by ring

end TauCeti
