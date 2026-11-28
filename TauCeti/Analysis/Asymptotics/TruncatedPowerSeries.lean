/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.Binomial
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Finite-order power-series expansions along a filter

Let `w` tend to `0` along a filter `l`. A function `F` has the expansion `P : PowerSeries 𝕜` to
order `N` along `w` when `F - (trunc N P).eval ∘ w = O(w ^ N)`. Such expansions are needed when
a function is only known to finitely many orders, so that `Asymptotics.HasAsymptoticExpansion`
with the scale `wⁿ` does not apply. This file shows that they are compatible with polynomials,
sums and products, and that finite power expansions at `0` are unique: a polynomial with vector
coefficients that is `O(hᵐ)` as `h → 0` has no terms of degree below `m`.

## Main results

* `Polynomial.isBigO_eval_of_X_pow_dvd`: if `X ^ N ∣ p`, then `p.eval ∘ w = O(w ^ N)`.
* `Polynomial.isBigO_eval_pow_of_coeff_eq_zero`: if `p` has zero coefficients below degree `N`,
  then `p.eval ∘ w = O(w ^ N)`.
* `Polynomial.isBigO_eval_sub_eval_trunc_coe`: a polynomial has itself as expansion to every
  order.
* `PowerSeries.isBigO_add_sub_eval_trunc_add`, `PowerSeries.isBigO_sum_sub_eval_trunc_sum`,
  `PowerSeries.isBigO_mul_trunc_eval_sub`, `PowerSeries.isBigO_mul_sub_eval_trunc_mul`:
  expansions add and multiply.
* `PowerSeries.isBigO_trunc_eval_one`, `PowerSeries.isBigO_one_of_isBigO_sub_eval_trunc`: a
  truncation or function with an expansion is bounded.
* `PowerSeries.isBigO_trunc_eval_sub_sub_linear`: remainder estimate for evaluating a truncated
  power series at two `O(w)` functions differing by `O(w ^ M)`.
* `PowerSeries.isBigO_sum_trunc_substInv`: remainder estimate for substituting a truncated
  formal inverse `Q` into a truncated power series `P` when `P.subst Q = X`.
* `PowerSeries.isBigO_sub_eval_trunc_mk_of_isBigO_sub_sum_inv_pow`: an expansion
  `F = ∑_{q < K} f_q x^{-q} + O(x^{-K})` in inverse powers of `x` is an expansion along `w = x⁻¹`.
* `TauCeti.eq_zero_of_isBigO_sum_pow_smul`: a polynomial `∑_{k < m} hᵏ bₖ` that is `O(hᵐ)` as
  `h → 0` has zero coefficients.
* `TauCeti.isBigO_one_add_mul_cpow_sub_eval_trunc`: `(1 + j w)^c` has the binomial series
  `∑ C(c, m) jᵐ Xᵐ` as expansion to every order along `w → 0`.
-/

public section

open Filter Finset Asymptotics
open scoped Polynomial Topology

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {w : α → 𝕜}

namespace Polynomial

/-- If `X ^ N` divides `p` and `w → 0`, then `p (w) = O(w ^ N)`. -/
theorem isBigO_eval_of_X_pow_dvd (hw : Tendsto w l (𝓝 0)) {N : ℕ} {p : 𝕜[X]}
    (hp : X ^ N ∣ p) : (fun i ↦ p.eval (w i)) =O[l] fun i ↦ w i ^ N := by
  obtain ⟨q, rfl⟩ := hp
  simpa using (isBigO_refl (fun i ↦ w i ^ N) l).mul
    (((q.continuous.tendsto 0).comp hw).isBigO_one 𝕜)

/-- A polynomial whose coefficients below degree `N` vanish is `O(w ^ N)` when evaluated at
`w → 0`. -/
theorem isBigO_eval_pow_of_coeff_eq_zero {N : ℕ} (hw : Tendsto w l (𝓝 0))
    (p : 𝕜[X]) (h : ∀ k < N, p.coeff k = 0) :
    (fun i ↦ p.eval (w i)) =O[l] fun i ↦ w i ^ N :=
  isBigO_eval_of_X_pow_dvd hw (X_pow_dvd_iff.mpr h)

/-- A polynomial has itself as expansion to every order. -/
theorem isBigO_eval_sub_eval_trunc_coe (hw : Tendsto w l (𝓝 0)) (N : ℕ) (p : 𝕜[X]) :
    (fun i ↦ p.eval (w i) - (PowerSeries.trunc N (p : PowerSeries 𝕜)).eval (w i)) =O[l]
      fun i ↦ w i ^ N := by
  refine (isBigO_eval_pow_of_coeff_eq_zero hw
    (p - PowerSeries.trunc N (p : PowerSeries 𝕜)) fun d hd ↦ ?_).congr_left fun i ↦ by simp
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

/-- The `N`-th truncation `(trunc N P).eval (w x)` is `O(1)` when `w → 0`. -/
theorem isBigO_trunc_eval_one (hw : Tendsto w l (𝓝 0)) (P : 𝕜⟦X⟧) (N : ℕ) :
    (fun i ↦ (trunc N P).eval (w i)) =O[l] fun _ ↦ (1 : 𝕜) :=
  (((trunc N P).continuous.tendsto 0).comp hw).isBigO_one 𝕜

/-- A function with an expansion along `w → 0` is bounded. -/
theorem isBigO_one_of_isBigO_sub_eval_trunc (hw : Tendsto w l (𝓝 0))
    (hF : (fun i ↦ F i - (trunc N P).eval (w i)) =O[l] fun i ↦ w i ^ N) :
    F =O[l] fun _ ↦ (1 : 𝕜) := by
  have hpow : (fun i ↦ w i ^ N) =O[l] fun _ ↦ (1 : 𝕜) :=
    (((continuous_pow N).tendsto 0).comp hw).isBigO_one 𝕜
  exact ((hF.trans hpow).add (isBigO_trunc_eval_one hw P N)).congr_left fun i ↦ by simp

/-- An expansion `F = ∑_{q < K} f_q x^{-q} + O(x^{-K})` in inverse powers of `x`, in the component
form used by `Asymptotics.HasAsymptoticExpansion` with the scale `fun q i ↦ (x i ^ q)⁻¹`, is an
expansion `F - (trunc K (mk fs)).eval x⁻¹ = O(x⁻¹ ^ K)` to order `K` along `x⁻¹`. -/
theorem isBigO_sub_eval_trunc_mk_of_isBigO_sub_sum_inv_pow {x : α → 𝕜} {fs : ℕ → 𝕜} {K : ℕ}
    (hF : (fun i ↦ F i - ∑ q ∈ range K, (x i ^ q)⁻¹ • fs q) =O[l] fun i ↦ (x i ^ K)⁻¹) :
    (fun i ↦ F i - (trunc K (mk fs)).eval (x i)⁻¹) =O[l] fun i ↦ (x i)⁻¹ ^ K :=
  (hF.congr_left fun i ↦ by simp [eval_trunc, mul_comm]).congr_right
    fun i ↦ (inv_pow _ _).symm

/-- Multiplying two `N`-th truncations agrees with the `N`-th truncation of the product up to
`O(w ^ N)` when `w → 0`. -/
theorem isBigO_mul_trunc_eval_sub (hw : Tendsto w l (𝓝 0)) (P Q : 𝕜⟦X⟧) (N : ℕ) :
    (fun i ↦ (trunc N P).eval (w i) * (trunc N Q).eval (w i) -
      (trunc N (P * Q)).eval (w i)) =O[l] fun i ↦ w i ^ N := by
  -- the product of the truncations agrees with the truncated product below degree `N`
  have hdvd : Polynomial.X ^ N ∣ trunc N P * trunc N Q - trunc N (P * Q) := by
    refine Polynomial.X_pow_dvd_iff.2 fun d hd ↦ ?_
    rw [Polynomial.coeff_sub, ← trunc_trunc_mul_trunc, coeff_trunc, ← Polynomial.coe_mul,
      Polynomial.coeff_coe]
    simp [hd]
  refine (Polynomial.isBigO_eval_of_X_pow_dvd hw hdvd).congr_left fun i ↦ ?_
  simp [Polynomial.eval_sub, Polynomial.eval_mul]

/-- If `F` and `G` have the expansions `P` and `Q` to order `N` along `w → 0`, then `F * G` has
the expansion `P * Q`. -/
theorem isBigO_mul_sub_eval_trunc_mul (hw : Tendsto w l (𝓝 0))
    (hF : (fun i ↦ F i - (trunc N P).eval (w i)) =O[l] fun i ↦ w i ^ N)
    (hG : (fun i ↦ G i - (trunc N Q).eval (w i)) =O[l] fun i ↦ w i ^ N) :
    (fun i ↦ F i * G i - (trunc N (P * Q)).eval (w i)) =O[l] fun i ↦ w i ^ N := by
  have h1 := (hF.mul (isBigO_one_of_isBigO_sub_eval_trunc hw hG)).congr_right fun i ↦ mul_one _
  have h2 := ((isBigO_trunc_eval_one hw P N).mul hG).congr_right fun i ↦ one_mul _
  refine ((h1.add h2).add (isBigO_mul_trunc_eval_sub hw P Q N)).congr_left fun i ↦ ?_
  ring

/-- Remainder estimate for evaluating a truncated power series at two `O(w)` functions differing
by `O(w ^ M)`. -/
theorem isBigO_trunc_eval_sub_sub_linear {s q : α → 𝕜} {M : ℕ}
    (hw0 : Tendsto w l (𝓝 0)) (P : 𝕜⟦X⟧) (hM : 1 ≤ M)
    (hsO : s =O[l] w) (hqO : q =O[l] w) (hrM : (fun x ↦ s x - q x) =O[l] fun x ↦ w x ^ M) :
    (fun x ↦ ((trunc (M + 1) P).eval (s x) -
        (trunc (M + 1) P).eval (q x)) - (s x - q x) * coeff 1 P) =O[l]
      fun x ↦ w x ^ (M + 1) := by
  simp_rw [eval_trunc]
  have hrew : ∀ x : α,
      (∑ k ∈ range (M + 1), coeff k P * s x ^ k -
        ∑ k ∈ range (M + 1), coeff k P * q x ^ k) - (s x - q x) * coeff 1 P =
      ∑ k ∈ Ico 2 (M + 1), (s x ^ k - q x ^ k) * coeff k P := fun x ↦ by
    rw [← sum_sub_distrib]
    have h2le : 2 ≤ M + 1 := by omega
    have hsplit := sum_range_add_sum_Ico
      (f := fun k ↦ coeff k P * s x ^ k - coeff k P * q x ^ k) h2le
    rw [← hsplit]
    have h01 : ∑ k ∈ range 2, (coeff k P * s x ^ k - coeff k P * q x ^ k) =
        (s x - q x) * coeff 1 P := by
      simp only [sum_range_succ, range_zero, sum_empty, zero_add, pow_zero, pow_one]
      ring
    rw [h01, add_sub_cancel_left]
    refine sum_congr rfl fun k _ ↦ by ring
  simp_rw [hrew]
  refine IsBigO.fun_sum fun k hk ↦ ?_
  have hk2 : 2 ≤ k := (mem_Ico.mp hk).1
  have hfac : (fun x ↦ ∑ j ∈ range k, s x ^ j * q x ^ (k - 1 - j)) =O[l] w := by
    refine IsBigO.fun_sum fun j hj ↦ ?_
    have hjk : j < k := mem_range.mp hj
    have hadd : j + (k - 1 - j) = k - 1 := by omega
    have hprod : (fun x ↦ s x ^ j * q x ^ (k - 1 - j)) =O[l] fun x ↦ w x ^ (k - 1) := by
      have h := (hsO.pow j).mul (hqO.pow (k - 1 - j))
      refine h.congr' EventuallyEq.rfl (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      rw [← pow_add, hadd]
    have hpow : (fun x ↦ w x ^ (k - 1)) =O[l] w := by
      have h1 : (fun x ↦ w x ^ (k - 2)) =O[l] fun _ ↦ (1 : 𝕜) :=
        (((continuous_pow (k - 2)).tendsto 0).comp hw0).isBigO_one 𝕜
      refine (h1.mul (isBigO_refl w l)).congr' (Eventually.of_forall fun x ↦ ?_)
        (Eventually.of_forall fun _ ↦ one_mul _)
      dsimp only
      rw [← pow_succ, show k - 2 + 1 = k - 1 by omega]
    exact hprod.trans hpow
  have hdiff_k : (fun x ↦ s x ^ k - q x ^ k) =O[l] fun x ↦ w x ^ (M + 1) := by
    have h := hfac.mul hrM
    refine h.congr' (Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · exact geom_sum₂_mul (s x) (q x) k
    · exact (pow_succ' (w x) M).symm
  have hc := hdiff_k.const_mul_left (coeff k P)
  exact hc.congr' (Eventually.of_forall fun x ↦ mul_comm _ _) EventuallyEq.rfl

/-- If `P.subst Q = X` with `constantCoeff Q = 0`, then substituting the `N`-th truncation of
`Q` into the `N`-th truncation of `P` matches `w` up to `O(w ^ N)` along `w → 0`. -/
theorem isBigO_sum_trunc_substInv (hw0 : Tendsto w l (𝓝 0))
    (hQ0 : constantCoeff Q = 0) (hPQ : P.subst Q = X) :
    (fun x ↦ (∑ k ∈ range N, (trunc N Q).eval (w x) ^ k * coeff k P) - w x) =O[l]
      fun x ↦ w x ^ N := by
  set R : 𝕜[X] := (trunc N P).comp (trunc N Q) - Polynomial.X
  have hcoeff : ∀ k < N, R.coeff k = 0 := fun k hk ↦ by
    rw [← Polynomial.coeff_coe]
    simp only [R, Polynomial.coeff_coe, Polynomial.coeff_sub,
      coeff_trunc_comp_trunc P hQ0 hk hk, hPQ, coeff_X, Polynomial.coeff_X]
    split_ifs <;> first | exact sub_self _ | omega
  refine (Polynomial.isBigO_eval_pow_of_coeff_eq_zero hw0 R hcoeff).congr'
    (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
  simp only [R, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X, eval_trunc,
    mul_comm]

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

/-- **Uniqueness of finite power expansions.** If the polynomial `∑_{k < m} hᵏ bₖ` is `O(hᵐ)` as
`h → 0`, `h ≠ 0`, then all its coefficients vanish. -/
theorem eq_zero_of_isBigO_sum_pow_smul {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {m : ℕ} {b : ℕ → E}
    (hb : (fun h : 𝕜 ↦ ∑ k ∈ range m, h ^ k • b k) =O[𝓝[≠] 0] fun h ↦ h ^ m) :
    ∀ k < m, b k = 0 := by
  induction m generalizing b with
  | zero => exact fun k hk ↦ absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
    -- The constant coefficient is the value at `0` of a continuous function tending to `0`.
    have hb0 : b 0 = 0 := by
      have hcont : Continuous fun h : 𝕜 ↦ ∑ k ∈ range (m + 1), h ^ k • b k := by fun_prop
      have hpow : Tendsto (fun h : 𝕜 ↦ h ^ (m + 1)) (𝓝[≠] 0) (𝓝 0) := by
        simpa using ((continuous_pow (m + 1)).tendsto (0 : 𝕜)).mono_left nhdsWithin_le_nhds
      have := tendsto_nhds_unique ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds)
        (hb.trans_tendsto hpow)
      simpa [sum_range_succ'] using this
    -- Dividing by `h` lowers the order of the remaining coefficients by one.
    have hshift (h : 𝕜) :
        ∑ k ∈ range (m + 1), h ^ k • b k = h • ∑ k ∈ range m, h ^ k • b (k + 1) := by
      simp [sum_range_succ', hb0, smul_sum, pow_succ', mul_smul]
    have htail : (fun h : 𝕜 ↦ ∑ k ∈ range m, h ^ k • b (k + 1)) =O[𝓝[≠] 0] fun h ↦ h ^ m := by
      refine ((isBigO_refl (fun h : 𝕜 ↦ h⁻¹) (𝓝[≠] 0)).smul hb).congr' ?_ ?_ <;>
        filter_upwards [self_mem_nhdsWithin] with h (hh : h ≠ 0)
      · rw [hshift, smul_smul, inv_mul_cancel₀ hh, one_smul]
      · rw [smul_eq_mul, pow_succ', ← mul_assoc, inv_mul_cancel₀ hh, one_mul]
    rintro (_ | k) hk
    · exact hb0
    · exact ih htail k (Nat.succ_lt_succ_iff.1 hk)

end TauCeti
