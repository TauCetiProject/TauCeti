/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries

import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Data.Nat.Factorial.NatCast

/-!
# Scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block. It also evaluates the change-of-origin series of a scalar series on constant vectors, and
uses this to prove that the iterated derivatives of a scalar power series over a complete
nontrivially normed field, at any point `x + y` of its ball of convergence, are the sums of the
termwise differentiated series (`HasFPowerSeriesOnBall.hasSum_descFactorial_mul_pow_sub`, with
`y ^ n`-rescaled companion
`HasFPowerSeriesOnBall.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv` and center-`0` `tsum`
corollary `HasFPowerSeriesOnBall.iteratedDeriv_eq_tsum_descFactorial_mul_pow`); both the unscaled
and rescaled termwise differentiated series are absolutely summable inside the disk of convergence
(`FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_sub_of_lt_ofScalars_radius`,
`FormalMultilinearSeries.summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius`,
`FormalMultilinearSeries.summable_norm_natCast_mul_ofScalars`,
`FormalMultilinearSeries.summable_norm_mul_pow_of_lt_radius`, and
`HasFPowerSeriesOnBall.summable_norm_mul_pow_ofScalars`), and at zero the `n`-th iterated
derivative equals `n! * c n` (`FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero`),
recovering `c n` when `(n.factorial : 𝕜) ≠ 0`. Termwise differentiation of a scalar series
represents the derivative on the same ball (`HasFPowerSeriesOnBall.deriv_ofScalars`), and gives
the Euler operators `y * f' y = ∑ n * c n * y ^ n`
(`HasFPowerSeriesOnBall.hasSum_mul_deriv_ofScalars`) and
`y ^ 2 * f'' y = ∑ n * (n - 1) * c n * y ^ n`
(`HasFPowerSeriesOnBall.hasSum_sq_mul_deriv_deriv_ofScalars`).

It also proves coefficient uniqueness for scalar power series vanishing near a point of a
preconnected ball (`HasFPowerSeriesOnBall.ofScalars_eq_zero_of_eventuallyEq_zero`), proving over
any complete nontrivially normed field with `[NormedAlgebra ℝ 𝕜]` that the series with
coefficients divided by `n` for `n ≥ 1` (`FormalMultilinearSeries.le_radius_ofScalars_div_natCast`,
`FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_div_natCast`) is a primitive of
`(f (x + y) - c 0) / y` away from the center `x`
(`HasFPowerSeriesOnBall.hasDerivAt_tsum_div_natCast`), and computes the scalar series of
`z ↦ f (z ^ m)` on a ball of radius at most `1` from that of `f`, in any normed algebra with
`‖1‖ = 1`. Over a densely normed field, summability on a punctured disk about the origin bounds the
convergence radius below (`FormalMultilinearSeries.le_radius_ofScalars_of_summable`) and yields a
`HasFPowerSeriesOnBall` representation without assuming completeness
(`FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_summable`), together with
translated punctured-disc variants
(`FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt`,
`FormalMultilinearSeries.analyticOnNhd_tsum_ofScalars_of_norm_sub_lt`,
`FormalMultilinearSeries.analyticOnNhd_of_hasSum_ofScalars_of_norm_sub_lt`,
`FormalMultilinearSeries.summable_norm_mul_pow_of_norm_sub_lt`,
`FormalMultilinearSeries.exists_norm_mul_pow_le_of_norm_sub_lt`); in particular, a scalar series
whose sum has no zero in a disk about the origin converges on that disk, because the sum is `0`
wherever the series diverges.

In any normed `𝕜`-algebra `A` with summable geometric series (not necessarily commutative), the
higher geometric series `∑ₙ C(n + k, k) xⁿ` has convergence radius at least `1`
(`TauCeti.one_le_ofScalars_choose_radius`) and represents `(1 - x)⁻¹ʳ ^ (k + 1)` on the open unit
ball (`TauCeti.hasFPowerSeriesOnBall_inverse_one_sub_pow`), extending Mathlib's
`hasFPowerSeriesOnBall_inverse_one_sub` (`k = 0`). Every one-variable scalar-valued formal
multilinear series is `ofScalars` of its `coeff` sequence
(`FormalMultilinearSeries.ofScalars_coeff`). Over a topological field `𝕜`, the scalar series
`FormalMultilinearSeries.ofScalars 𝕜 c` agrees with `TauCeti.mkPiRingSeries 𝕜 c`
(`TauCeti.mkPiRingSeries_eq_ofScalars`). Shifting a scalar power series around a base point `z₀`
in a complete normed algebra yields a `HasFPowerSeriesOnBall` expansion around `z₀` whenever the
convergence radius is positive (`TauCeti.hasFPowerSeriesOnBall_ofScalarsSum_sub`), and yields
analyticity on the shifted open ball of convergence unconditionally, even when that ball is empty
(`TauCeti.analyticOnNhd_ofScalarsSum_sub`).
-/

public section

open scoped BigOperators ENNReal NNReal Topology

namespace FormalMultilinearSeries

/-- Every one-variable scalar-valued formal multilinear series equals `ofScalars` applied to its
scalar coefficient sequence. -/
@[simp]
theorem ofScalars_coeff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) : ofScalars 𝕜 p.coeff = p := by
  ext n
  simp [ofScalars, mul_comm]

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E] [IsTopologicalRing E]

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions. This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) =
      ofScalars E fun n ↦ ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i) := by
  have prod_ofFn_smul {m : ℕ} (a : Fin m → 𝕜) (b : Fin m → E) :
      (List.ofFn fun i ↦ a i • b i).prod = (∏ i, a i) • (List.ofFn b).prod := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, Fin.prod_univ_succ]
      simp only [List.prod_cons, ih]
      exact smul_mul_smul_comm _ _ _ _
  ext n v
  simp only [FormalMultilinearSeries.comp, ofScalars]
  rw [sum_apply, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hprod :
      (List.ofFn fun i : Fin p.length ↦ (ofScalars E d).applyComposition p v i).prod =
        (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
    simp only [applyComposition, ofScalars, _root_.smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    rw [prod_ofFn_smul]
    congr 1
    have hblocks :
        List.ofFn (fun i : Fin p.length ↦ (List.ofFn (v ∘ p.embedding i)).prod) =
          ((List.ofFn v).splitWrtComposition p).map List.prod := by
      refine List.ext_getElem (by simp) fun i hi₁ hi₂ ↦ ?_
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_splitWrtComposition]
      refine congrArg List.prod (List.ext_getElem ?_ fun j hj₁ hj₂ ↦ by
        simpa using congrArg v (Fin.ext (p.coe_embedding _ _)))
      simpa [p.sizeUpTo_le] using
        (Nat.sub_eq_of_eq_add' (p.sizeUpTo_succ' ⟨i, by simpa using hi₁⟩)).symm
    rw [hblocks, ← List.prod_flatten, List.splitWrtComposition,
      List.flatten_splitWrtCompositionAux (by simp)]
  simp only [compAlongComposition_apply, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [hprod, smul_smul]

/-- Evaluating a term of the change-of-origin series of a scalar series at two constant vectors
produces the corresponding binomial coefficient. -/
theorem changeOriginSeries_ofScalars_apply {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedCommRing R] [NormedAlgebra 𝕂 R] (c : ℕ → 𝕂) (x y : R) (n l : ℕ) :
    (((ofScalars R c).changeOriginSeries n l) (fun _ ↦ x)) (fun _ ↦ y) =
      Nat.choose (n + l) l • (c (n + l) • (x ^ l * y ^ n)) := by
  -- The change-of-origin API exposes this coefficient through its defining finite sum. After
  -- unfolding it, each summand places `x` at the `l` indices of its finset and `y` elsewhere.
  rw [changeOriginSeries]
  simp only [_root_.sum_apply]
  simp_rw [changeOriginSeriesTerm_apply]
  have hx (s : {s : Finset (Fin (n + l)) // s.card = l}) :
      ofScalars R c (n + l) (s.val.piecewise (fun _ ↦ x) (fun _ ↦ y)) =
        c (n + l) • (x ^ l * y ^ n) := by
    simp only [ofScalars, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.prod_ofFn, Finset.prod_piecewise, Finset.univ_inter, Finset.prod_const,
      Finset.card_univ_sdiff, Fintype.card_fin, s.property, Nat.add_sub_cancel]
  simp_rw [hx]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]

private theorem factorial_mul_changeOriginSeries_ofScalars_one
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] (c : ℕ → 𝕂) (y : 𝕂) (n l : ℕ) :
    (n.factorial : 𝕂) * (((ofScalars 𝕂 c).changeOriginSeries n l fun _ ↦ y) fun _ ↦ 1) =
      ((l + n).descFactorial n : 𝕂) * c (l + n) * y ^ l := by
  simp only [changeOriginSeries_ofScalars_apply, add_comm l n,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, nsmul_eq_mul, smul_eq_mul,
    one_pow, mul_one]
  rw [Nat.choose_symm_add]
  ring

/-- Inside its ball of convergence, the `n`-th iterated derivative of a scalar power series at
`x + y` is the sum of the termwise differentiated series
`∑ k, k.descFactorial n * c k * y ^ (k - n)`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_descFactorial_mul_pow_sub
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]
    {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {x : 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) x r) {y : 𝕂} (hy : ‖y‖ₑ < r) (n : ℕ) :
    HasSum (fun k : ℕ ↦ (k.descFactorial n : 𝕂) * c k * y ^ (k - n))
      (iteratedDeriv n f (x + y)) := by
  set p := ofScalars 𝕂 c
  -- the `n`-th derivative at `x + y` is `n!` times the `n`-th coefficient of the series recentred
  -- at `y`, and that coefficient is the sum of the change-of-origin series
  have hderiv : iteratedDeriv n f (x + y) = (n.factorial : 𝕂) * p.changeOrigin y n fun _ ↦ 1 := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    simpa only [nsmul_eq_mul] using ((hf.changeOrigin hy).factorial_smul 1 n).symm
  have hsum := ContinuousMultilinearMap.hasSum_eval
    ((p.hasFPowerSeriesOnBall_changeOrigin n (hf.r_pos.trans_le hf.r_le)).hasSum
      (mem_eball_zero_iff.mpr (hy.trans_le hf.r_le))) fun _ ↦ (1 : 𝕂)
  rw [zero_add] at hsum
  -- reindex along `l ↦ l + n`: the terms with `k < n` vanish since `k.descFactorial n = 0`
  rw [hderiv]
  refine ((add_left_injective n).hasSum_iff fun k hk ↦ ?_).mp
    ((hsum.mul_left _).congr_fun fun l ↦ ?_)
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp fun h ↦ hk ⟨k - n, Nat.sub_add_cancel h⟩)]
  · simpa only [Function.comp_apply, p, Nat.add_sub_cancel] using
      (factorial_mul_changeOriginSeries_ofScalars_one c y n l).symm

/-- Inside its ball of convergence, the iterated derivatives of a scalar power series centered at
`0` are given by the termwise differentiated series. -/
theorem _root_.HasFPowerSeriesOnBall.iteratedDeriv_eq_tsum_descFactorial_mul_pow
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]
    {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) (n : ℕ) :
    iteratedDeriv n f y = ∑' k : ℕ, (k.descFactorial n : 𝕂) * c k * y ^ (k - n) := by
  simpa only [zero_add] using (hf.hasSum_descFactorial_mul_pow_sub hy n).tsum_eq.symm

/-- Inside its ball of convergence, `y ^ n * iteratedDeriv n f (x + y)` is the sum of the rescaled
termwise differentiated series `∑ k, k.descFactorial n * c k * y ^ k`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]
    {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {x : 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) x r) {y : 𝕂} (hy : ‖y‖ₑ < r) (n : ℕ) :
    HasSum (fun k : ℕ ↦ (k.descFactorial n : 𝕂) * c k * y ^ k)
      (y ^ n * iteratedDeriv n f (x + y)) :=
  ((hf.hasSum_descFactorial_mul_pow_sub hy n).mul_left (y ^ n)).congr_fun fun k ↦ by
    calc (k.descFactorial n : 𝕂) * c k * y ^ k
        = ((k.descFactorial n : 𝕂) * y ^ k) * c k := by ring
      _ = (y ^ n * ((k.descFactorial n : 𝕂) * y ^ (k - n))) * c k := by
          rw [Nat.cast_descFactorial_mul_pow]
      _ = y ^ n * ((k.descFactorial n : 𝕂) * c k * y ^ (k - n)) := by ring

/-- **The Euler operator on a scalar power series.** If `f` is the sum of the scalar power series
`∑ c n * z ^ n` on the ball of radius `r` about `0`, then for `y` in that ball,
`y * f' y = ∑ n * c n * y ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_mul_deriv_ofScalars {𝕂 : Type*}
    [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) :
    HasSum (fun n : ℕ ↦ n * c n * y ^ n) (y * deriv f y) := by
  simpa [iteratedDeriv_one, zero_add, Nat.descFactorial_one] using
    hf.hasSum_descFactorial_mul_pow_eq_pow_mul_iteratedDeriv hy 1

/-- Inside the convergence disk of `ofScalars 𝕂 c`, the termwise differentiated series
`∑ k, k.descFactorial n * c k * y ^ (k - n)` is absolutely summable. -/
theorem summable_norm_descFactorial_mul_pow_sub_of_lt_ofScalars_radius
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] (c : ℕ → 𝕂) {y : 𝕂}
    (hy : ‖y‖ₑ < (ofScalars 𝕂 c).radius) (n : ℕ) :
    Summable fun k : ℕ ↦ ‖(k.descFactorial n : 𝕂) * c k * y ^ (k - n)‖ := by
  set p := ofScalars 𝕂 c
  have hsum : Summable fun l : ℕ ↦
      ‖(n.factorial : 𝕂)‖ * ‖(p.changeOriginSeries n l) fun _ ↦ y‖ :=
    ((p.changeOriginSeries n).summable_norm_apply
      (mem_eball_zero_iff.mpr (hy.trans_le (p.le_changeOriginSeries_radius n)))).mul_left _
  have hbound : Summable fun l : ℕ ↦
      ‖((l + n).descFactorial n : 𝕂) * c (l + n) * y ^ l‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun l ↦ ?_) hsum
    have hunit : ‖fun _ : Fin n ↦ (1 : 𝕂)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ norm_one.le
    calc ‖((l + n).descFactorial n : 𝕂) * c (l + n) * y ^ l‖
        = ‖(n.factorial : 𝕂) * (((p.changeOriginSeries n l) fun _ ↦ y) fun _ ↦ 1)‖ :=
            congrArg norm (factorial_mul_changeOriginSeries_ofScalars_one c y n l).symm
      _ = ‖(n.factorial : 𝕂)‖ * ‖((p.changeOriginSeries n l) fun _ ↦ y) fun _ ↦ 1‖ :=
            norm_mul _ _
      _ ≤ ‖(n.factorial : 𝕂)‖ * ‖(p.changeOriginSeries n l) fun _ ↦ y‖ :=
            mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.unit_le_opNorm _ hunit)
              (norm_nonneg _)
  rw [← summable_nat_add_iff n]
  simpa only [Nat.add_sub_cancel] using hbound

/-- Inside the convergence disk of `ofScalars 𝕂 c`, the rescaled termwise differentiated series
`∑ k, k.descFactorial n * c k * y ^ k` is absolutely summable. -/
theorem summable_norm_descFactorial_mul_pow_of_lt_ofScalars_radius
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] (c : ℕ → 𝕂) {y : 𝕂}
    (hy : ‖y‖ₑ < (ofScalars 𝕂 c).radius) (n : ℕ) :
    Summable fun k : ℕ ↦ ‖(k.descFactorial n : 𝕂) * c k * y ^ k‖ := by
  refine ((summable_norm_descFactorial_mul_pow_sub_of_lt_ofScalars_radius c hy n).mul_left
    (‖y‖ ^ n)).congr fun k ↦ ?_
  have hpow : y ^ n * ((k.descFactorial n : 𝕂) * c k * y ^ (k - n)) =
      (k.descFactorial n : 𝕂) * c k * y ^ k := by
    calc y ^ n * ((k.descFactorial n : 𝕂) * c k * y ^ (k - n))
        = (y ^ n * ((k.descFactorial n : 𝕂) * y ^ (k - n))) * c k := by ring
      _ = (k.descFactorial n : 𝕂) * y ^ k * c k := by rw [Nat.cast_descFactorial_mul_pow]
      _ = (k.descFactorial n : 𝕂) * c k * y ^ k := by ring
  simpa only [norm_mul, norm_pow] using congrArg norm hpow

/-- Inside its ball of convergence, a scalar power series `∑ c n * y ^ n` is absolutely
summable. -/
theorem _root_.HasFPowerSeriesOnBall.summable_norm_mul_pow_ofScalars
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {c : ℕ → 𝕜} {x y : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕜 c) x r) (hy : ‖y‖ₑ < r) :
    Summable fun n : ℕ ↦ ‖c n * y ^ n‖ := by
  simpa [ofScalars_apply_eq, norm_mul, mul_comm] using
    (ofScalars 𝕜 c).summable_norm_apply (mem_eball_zero_iff.mpr (hy.trans_le hf.r_le))

/-- Over a complete nontrivially normed field, the `n`-th iterated derivative at zero of
`ofScalarsSum (E := 𝕜) c` equals `(n.factorial : 𝕜) * c n`, recovering `c n` whenever
`(n.factorial : 𝕜) ≠ 0`. -/
theorem iteratedDeriv_ofScalarsSum_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (c : ℕ → 𝕜) (hc : 0 < (ofScalars 𝕜 c).radius) (n : ℕ) :
    iteratedDeriv n (ofScalarsSum (E := 𝕜) c) 0 = n.factorial * c n := by
  have h := ((ofScalars 𝕜 c).hasFPowerSeriesOnBall hc).iteratedDeriv_eq_tsum_descFactorial_mul_pow
    (y := 0) (by simpa using hc) n
  rw [ofScalarsSum, h, tsum_eq_single n fun k hk ↦ ?_]
  · simp [Nat.descFactorial_self]
  · rcases hk.lt_or_gt with hk | hk
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hk]
    · simp [zero_pow (Nat.sub_ne_zero_of_lt hk)]

/-- If a scalar power series `ofScalars 𝕜 c` represents `f` on a preconnected ball
`Metric.eball x r` and `f` vanishes in a neighborhood of some point `y ∈ Metric.eball x r`,
then `c = 0`. -/
theorem _root_.HasFPowerSeriesOnBall.ofScalars_eq_zero_of_eventuallyEq_zero
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {f : 𝕜 → 𝕜} {c : ℕ → 𝕜} {x y : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕜 c) x r)
    (hconn : IsPreconnected (Metric.eball x r))
    (hy : y ∈ Metric.eball x r) (hzero : f =ᶠ[𝓝 y] 0) :
    c = 0 := by
  have heq : Set.EqOn f 0 (Metric.eball x r) :=
    hf.analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hy hzero
  have hzero_x : f =ᶠ[𝓝 x] 0 :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Metric.eball x r, Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hf.r_pos), heq⟩
  exact (ofScalars_series_eq_zero (E := 𝕜)).mp (hf.hasFPowerSeriesAt.eq_zero_of_eventually hzero_x)

/-- Dividing the `n`-th coefficient of a scalar power series by `n` (for `n ≥ 1`, with constant
term `0`) does not shrink its radius of convergence. -/
theorem le_radius_ofScalars_div_natCast {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] (c : ℕ → 𝕜) :
    (ofScalars 𝕜 c).radius ≤
      (ofScalars 𝕜 fun n : ℕ ↦ if n = 0 then 0 else c n / (n : 𝕜)).radius := by
  refine radius_le_of_le fun n ↦ ?_
  rw [ofScalars_norm, ofScalars_norm]
  split_ifs with hn
  · simp
  · have hn_norm : (1 : ℝ) ≤ ‖(n : 𝕜)‖ := by
      rw [← map_natCast (algebraMap ℝ 𝕜) n, norm_algebraMap']
      simpa using (Nat.one_le_iff_ne_zero.mpr hn : 1 ≤ n)
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hn_norm

/-- On any open ball `Metric.eball x r` within the convergence radius of `ofScalars 𝕜 c`, the
termwise divided series `z ↦ ∑' n, (if n = 0 then 0 else c n / n) * (z - x) ^ n` is represented by
its scalar formal power series. -/
theorem hasFPowerSeriesOnBall_tsum_ofScalars_div_natCast
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
    (c : ℕ → 𝕜) (x : 𝕜) {r : ℝ≥0∞} (hr : 0 < r) (hr_le : r ≤ (ofScalars 𝕜 c).radius) :
    HasFPowerSeriesOnBall
      (fun z : 𝕜 ↦ ∑' n : ℕ, (if n = 0 then 0 else c n / (n : 𝕜)) * (z - x) ^ n)
      (ofScalars 𝕜 fun n : ℕ ↦ if n = 0 then 0 else c n / (n : 𝕜)) x r := by
  set d : ℕ → 𝕜 := fun n ↦ if n = 0 then 0 else c n / (n : 𝕜)
  have hd_rad : r ≤ (ofScalars 𝕜 d).radius := hr_le.trans (le_radius_ofScalars_div_natCast c)
  have h0 := ((ofScalars 𝕜 d).hasFPowerSeriesOnBall (hr.trans_le hd_rad)).mono hr hd_rad
  simpa only [zero_add, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul, d,
    ite_mul, zero_mul] using h0.comp_sub x

/-- If `f` is represented by `ofScalars 𝕜 c` on `Metric.eball x r`, then for every nonzero `y`
with `‖y‖ₑ < r`, the termwise divided series
`z ↦ ∑' n, (if n = 0 then 0 else c n / n) * (z - x) ^ n` has derivative `(f (x + y) - c 0) / y`
at `x + y`. -/
theorem _root_.HasFPowerSeriesOnBall.hasDerivAt_tsum_div_natCast
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
    {f : 𝕜 → 𝕜} {c : ℕ → 𝕜} {x y : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕜 c) x r)
    (hy0 : y ≠ 0) (hy : ‖y‖ₑ < r) :
    HasDerivAt (fun z : 𝕜 ↦ ∑' n : ℕ, (if n = 0 then 0 else c n / (n : 𝕜)) * (z - x) ^ n)
      ((f (x + y) - c 0) / y) (x + y) := by
  set d : ℕ → 𝕜 := fun n ↦ if n = 0 then 0 else c n / (n : 𝕜)
  set H₀ : 𝕜 → 𝕜 := fun u ↦ ∑' n : ℕ, d n * u ^ n
  have hpH₀ : HasFPowerSeriesOnBall H₀ (ofScalars 𝕜 d) 0 r := by
    simpa only [sub_zero] using
      hasFPowerSeriesOnBall_tsum_ofScalars_div_natCast c 0 hf.r_pos hf.r_le
  have hH₀_diff : HasDerivAt H₀ (deriv H₀ y) y :=
    (hpH₀.analyticAt_of_mem
      (by simpa [Metric.mem_eball, edist_zero_right] using hy)).differentiableAt.hasDerivAt
  have hsum1 : HasSum (fun n : ℕ ↦ (n : 𝕜) * d n * y ^ n) (y * deriv H₀ y) :=
    hpH₀.hasSum_mul_deriv_ofScalars hy
  have hsum2 : HasSum (fun n : ℕ ↦ if n = 0 then (0 : 𝕜) else c n * y ^ n) (f (x + y) - c 0) := by
    have hsum_f : HasSum (fun n : ℕ ↦ c n * y ^ n) (f (x + y)) := by
      simpa only [ofScalars_apply_eq, smul_eq_mul] using hf.hasSum (mem_eball_zero_iff.mpr hy)
    refine (hsum_f.sub (hasSum_ite_eq (0 : ℕ) (c 0))).congr_fun fun n ↦ ?_
    by_cases hn : n = 0 <;> simp [hn]
  have hfun : (fun n : ℕ ↦ (n : 𝕜) * d n * y ^ n) =
      fun n : ℕ ↦ if n = 0 then (0 : 𝕜) else c n * y ^ n := by
    ext n
    by_cases hn : n = 0
    · simp [d, hn]
    · have hn0 : (n : 𝕜) ≠ 0 := by
        rw [← map_natCast (algebraMap ℝ 𝕜) n]
        simpa using (algebraMap ℝ 𝕜).injective.ne (Nat.cast_ne_zero.mpr hn)
      simp [d, hn, mul_div_cancel₀ _ hn0]
  have hval : y * deriv H₀ y = f (x + y) - c 0 :=
    hsum1.unique (hfun ▸ hsum2)
  have hH_diff : HasDerivAt H₀ ((f (x + y) - c 0) / y) (x + y - x) := by
    rw [add_sub_cancel_left]
    exact hH₀_diff.congr_deriv (eq_div_of_mul_eq hy0 (by rw [mul_comm, hval]))
  simpa [H₀, d] using hH_diff.comp_sub_const (x + y) x

/-- **Termwise differentiation of a scalar power series.** If `f` is the sum of the scalar power
series `∑ c n * (z - x) ^ n` on the ball of radius `r` about `x`, then `deriv f` is the sum on
the same ball of the termwise differentiated series `∑ (n + 1) * c (n + 1) * (z - x) ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.deriv_ofScalars {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {x : 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) x r) :
    HasFPowerSeriesOnBall (deriv f) (ofScalars 𝕂 fun n ↦ (n + 1) * c (n + 1)) x r := by
  have h := (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)).comp_hasFPowerSeriesOnBall hf.fderiv
  convert h using 1
  · ext y
    exact fderiv_apply_one_eq_deriv.symm
  · -- both series are scalar, so it suffices to compare their coefficients
    ext n : 1
    ext
    rw [apply_eq_prod_smul_coeff, coeff_ofScalars, apply_eq_prod_smul_coeff]
    congr 1
    have h1 := derivSeries_coeff_one (ofScalars 𝕂 c) n
    rw [coeff_ofScalars, nsmul_eq_mul, Nat.cast_succ] at h1
    rw [← h1, coeff, coeff, ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.apply_apply]

/-- **The second Euler operator on a scalar power series.** If `f` is the sum of the scalar power
series `∑ c n * z ^ n` on the ball of radius `r` about `0`, then for `y` in that ball,
`y ^ 2 * f'' y = ∑ n * (n - 1) * c n * y ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_sq_mul_deriv_deriv_ofScalars {𝕂 : Type*}
    [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) :
    HasSum (fun n : ℕ ↦ n * (n - 1) * c n * y ^ n) (y ^ 2 * deriv (deriv f) y) := by
  have h := (hf.deriv_ofScalars.deriv_ofScalars.hasSum (mem_eball_zero_iff.mpr hy)).mul_left
    (y ^ 2)
  -- the terms of index `0` and `1` vanish, and the others are those of `h` shifted by two
  refine (hasSum_nat_add_iff' 2).mp ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, zero_mul,
    sub_self, mul_zero, zero_add, sub_zero]
  convert h using 1
  · ext n
    simp only [ofScalars_apply_eq, smul_eq_mul]
    push_cast
    ring
  · simp

/-- Inside the disc of convergence of a scalar series `∑ c n * z ^ n`, the series converges
absolutely. -/
theorem summable_norm_mul_pow_of_lt_radius {𝕂 : Type*} [NontriviallyNormedField 𝕂] (c : ℕ → 𝕂)
    {y : 𝕂} (hy : ‖y‖ₑ < (ofScalars 𝕂 c).radius) : Summable fun n : ℕ ↦ ‖c n * y ^ n‖ := by
  refine ((ofScalars 𝕂 c).summable_norm_mul_pow hy).congr fun n ↦ ?_
  rw [ofScalars_norm, coe_nnNorm, norm_mul, norm_pow]

/-- Inside the disc of convergence of a scalar series `∑ c n * z ^ n`, the series
`∑ n * c n * y ^ n` of the Euler operator converges absolutely. -/
theorem summable_norm_natCast_mul_ofScalars {𝕂 : Type*} [NontriviallyNormedField 𝕂] (c : ℕ → 𝕂)
    {y : 𝕂} (hy : ‖y‖ₑ < (ofScalars 𝕂 c).radius) :
    Summable fun n : ℕ ↦ ‖(n : 𝕂) * c n * y ^ n‖ := by
  obtain ⟨a, ha, C, -, hC⟩ := (ofScalars 𝕂 c).norm_mul_pow_le_mul_pow_of_lt_radius hy
  -- compare with `C ∑ n * aⁿ` for the geometric ratio `a < 1` given by the radius
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_pow_mul_geometric_of_norm_lt_one 1 (r := a)
      (by rw [Real.norm_of_nonneg ha.1.le]; exact ha.2)).mul_left C)
  have hn := hC n
  rw [ofScalars_norm, coe_nnNorm] at hn
  calc ‖(n : 𝕂) * c n * y ^ n‖ = ‖(n : 𝕂)‖ * (‖c n‖ * ‖y‖ ^ n) := by
        rw [norm_mul, norm_mul, norm_pow, mul_assoc]
    _ ≤ n * (C * a ^ n) := by
        gcongr
        exact (Nat.norm_cast_le n).trans_eq (by rw [norm_one, mul_one])
    _ = C * (n ^ 1 * a ^ n) := by ring

/-- **Substituting `z ^ m` into a scalar power series.** Let `A` be a normed algebra over `𝕂`
with `‖1‖ = 1`, for instance `𝕂` itself. If `f` is the sum of the scalar power series
`∑ c k • z ^ k` on the ball of radius `r ≤ 1` about `0` in `A`, then for `0 < m` the function
`z ↦ f (z ^ m)` is the sum on the same ball of the scalar power series with coefficient `c k` at
the exponent `m * k`, and coefficient `0` at the exponents not divisible by `m`. -/
theorem _root_.HasFPowerSeriesOnBall.comp_pow_ofScalars {𝕂 A : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing A] [NormOneClass A] [NormedAlgebra 𝕂 A] {f : A → A} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars A c) 0 r) (hr : r ≤ 1) {m : ℕ} (hm : 0 < m) :
    HasFPowerSeriesOnBall (fun z ↦ f (z ^ m))
      (ofScalars A fun n ↦ if m ∣ n then c (n / m) else 0) 0 r := by
  have hinj : Function.Injective fun k : ℕ ↦ m * k := fun _ _ e ↦ Nat.eq_of_mul_eq_mul_left hm e
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_, hf.r_pos, fun {y} hy ↦ ?_⟩
  · -- the expanded series is dominated termwise by the original one, as `ρ < r ≤ 1`
    obtain ⟨C, -, hC⟩ := (ofScalars A c).norm_mul_pow_le_of_lt_radius (hρ.trans_le hf.r_le)
    have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast (hρ.trans_le hr).le
    refine le_radius_of_bound _ C fun n ↦ ?_
    rw [ofScalars_norm]
    split_ifs with hn
    · obtain ⟨k, rfl⟩ := hn
      have hk := hC k
      rw [ofScalars_norm] at hk
      rw [Nat.mul_div_cancel_left _ hm]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ρ.property hρ1
          (Nat.le_mul_of_pos_left k hm))
        (norm_nonneg _)).trans hk
    · simpa using (mul_nonneg (norm_nonneg _) (pow_nonneg ρ.property 0)).trans (hC 0)
  · -- the series of `f` at `y ^ m`, reindexed along the multiples of `m`
    have hy1 : ‖y‖ₑ ≤ 1 := (mem_eball_zero_iff.mp hy).le.trans hr
    have hym : y ^ m ∈ Metric.eball (0 : A) r := by
      rw [mem_eball_zero_iff]
      calc ‖y ^ m‖ₑ ≤ ‖y‖ₑ ^ m := by simpa [eNorm_eq_nnNorm] using mod_cast nnNorm_pow_le y m
        _ ≤ ‖y‖ₑ := pow_le_of_le_one zero_le hy1 hm.ne'
        _ < r := mem_eball_zero_iff.mp hy
    have hs := hf.hasSum hym
    simp only [ofScalars_apply_eq, zero_add] at hs ⊢
    refine (hinj.hasSum_iff fun n hn ↦ ?_).mp (hs.congr_fun fun k ↦ ?_)
    · split_ifs with h
      · exact absurd ⟨n / m, Nat.mul_div_cancel' h⟩ hn
      · exact zero_smul _ _
    · simp [Nat.mul_div_cancel_left _ hm, ← pow_mul]

/-- **Convergence on a punctured disk bounds the radius.** Over a densely normed field, a scalar
series that converges at every nonzero point of a disk about the origin has radius of convergence
at least the radius of that disk. -/
theorem le_radius_ofScalars_of_summable {𝕜 : Type*} [DenselyNormedField 𝕜] (a : ℕ → 𝕜)
    {r : ℝ≥0∞} (h : ∀ z : 𝕜, z ≠ 0 → ‖z‖ₑ < r → Summable fun n : ℕ ↦ a n * z ^ n) :
    r ≤ (ofScalars 𝕜 a).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun t ht ↦ ?_
  obtain ⟨u, htu, hur⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ht
  obtain ⟨z, htz, hzu⟩ := NormedField.exists_lt_nnNorm_lt 𝕜 (ENNReal.coe_lt_coe.mp htu)
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at htz
  have hsum := h z hz0 ((eNorm_lt_coe.mpr hzu).trans hur)
  refine (ENNReal.coe_le_coe.mpr htz.le).trans (le_radius_of_tendsto _ (l := 0) ?_)
  simpa [ofScalars_norm] using hsum.tendsto_atTop_zero.norm

/-- Over a densely normed field, if `∑ a n * z ^ n` is summable at every nonzero point of the open
disk `‖z‖ₑ < r` (`0 < r`), then `fun z ↦ ∑' n, a n * z ^ n` has formal power series
`ofScalars 𝕜 a` on `eball 0 r`. -/
theorem hasFPowerSeriesOnBall_tsum_ofScalars_of_summable {𝕜 : Type*} [DenselyNormedField 𝕜]
    (a : ℕ → 𝕜) {r : ℝ≥0∞} (hr : 0 < r)
    (hsum : ∀ z : 𝕜, z ≠ 0 → ‖z‖ₑ < r → Summable fun n : ℕ ↦ a n * z ^ n) :
    HasFPowerSeriesOnBall (fun z : 𝕜 ↦ ∑' n : ℕ, a n * z ^ n) (ofScalars 𝕜 a) 0 r where
  r_le := le_radius_ofScalars_of_summable a hsum
  r_pos := hr
  hasSum {y} hy := by
    simp only [ofScalars_apply_eq, smul_eq_mul, zero_add]
    rcases eq_or_ne y 0 with rfl | hy0
    · exact (summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by
        simp [zero_pow (Finset.mem_singleton.not.mp hn)]).hasSum
    · exact (hsum y hy0 (mem_eball_zero_iff.mp hy)).hasSum

/-- Over a densely normed field, if `∑ c n * (z - z₀) ^ n` is summable on the punctured open disc
`0 < ‖z - z₀‖ < r` (`0 < r`), then `fun u ↦ ∑' n, c n * u ^ n` has formal power series
`ofScalars 𝕜 c` on `eball 0 (ENNReal.ofReal r)`. -/
theorem hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt {𝕜 : Type*} [DenselyNormedField 𝕜]
    (c : ℕ → 𝕜) (z₀ : 𝕜) {r : ℝ} (hr : 0 < r)
    (hc : ∀ z : 𝕜, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun n : ℕ ↦ c n * (z - z₀) ^ n) :
    HasFPowerSeriesOnBall (fun u : 𝕜 ↦ ∑' n : ℕ, c n * u ^ n) (ofScalars 𝕜 c) 0
      (ENNReal.ofReal r) :=
  hasFPowerSeriesOnBall_tsum_ofScalars_of_summable c (ENNReal.ofReal_pos.mpr hr)
    fun u hu0 hur ↦ by
      simpa using hc (z₀ + u) (by simpa using hu0)
        (by simpa using TauCeti.eNorm_lt_ofReal_iff.mp hur)

/-- Over a densely normed field, if `∑ c n * (z - z₀) ^ n` is summable on the punctured open disc
`0 < ‖z - z₀‖ < r` (`0 < r`), then `fun u ↦ ∑' n, c n * u ^ n` is analytic on
`Metric.ball 0 r`. -/
theorem analyticOnNhd_tsum_ofScalars_of_norm_sub_lt {𝕜 : Type*} [DenselyNormedField 𝕜]
    [CompleteSpace 𝕜] (c : ℕ → 𝕜) (z₀ : 𝕜) {r : ℝ} (hr : 0 < r)
    (hc : ∀ z : 𝕜, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun n : ℕ ↦ c n * (z - z₀) ^ n) :
    AnalyticOnNhd 𝕜 (fun u : 𝕜 ↦ ∑' n : ℕ, c n * u ^ n) (Metric.ball 0 r) :=
  Metric.eball_ofReal (x := (0 : 𝕜)) (ε := r) ▸
    (hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt c z₀ hr hc).analyticOnNhd

/-- Over a complete densely normed field, if `(z - z₀) ^ k * f z` equals the sum of the scalar
power series `∑ c n * (z - z₀) ^ n` on the punctured disc `0 < ‖z - z₀‖ < r`, then `f` is
analytic on `Metric.ball z₀ r \ {z₀}`. -/
theorem analyticOnNhd_of_hasSum_ofScalars_of_norm_sub_lt {𝕜 : Type*} [DenselyNormedField 𝕜]
    [CompleteSpace 𝕜] {f : 𝕜 → 𝕜} {c : ℕ → 𝕜} (z₀ : 𝕜) {r : ℝ} {k : ℕ}
    (hf : ∀ z : 𝕜, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
      HasSum (fun n : ℕ ↦ c n * (z - z₀) ^ n) ((z - z₀) ^ k * f z)) :
    AnalyticOnNhd 𝕜 f (Metric.ball z₀ r \ {z₀}) := by
  by_cases hr : 0 < r
  · have han := analyticOnNhd_tsum_ofScalars_of_norm_sub_lt c z₀ hr
      fun w hw0 hwr ↦ (hf w hw0 hwr).summable
    have hq : AnalyticOnNhd 𝕜 (fun w : 𝕜 ↦ ((w - z₀) ^ k)⁻¹ * ∑' n : ℕ, c n * (w - z₀) ^ n)
        (Metric.ball z₀ r \ {z₀}) := fun w hw ↦ by
      have hsub : AnalyticAt 𝕜 (fun u : 𝕜 ↦ u - z₀) w := analyticAt_id.sub analyticAt_const
      have hcomp : AnalyticAt 𝕜 (fun u : 𝕜 ↦ ∑' n : ℕ, c n * (u - z₀) ^ n) w :=
        (han (w - z₀) (by simpa [Metric.mem_ball, dist_eq_norm] using hw.1)).comp
          (f := fun u : 𝕜 ↦ u - z₀) (x := w) hsub
      exact (((analyticAt_id.sub analyticAt_const).pow k).inv
        (pow_ne_zero k (sub_ne_zero.mpr hw.2))).mul hcomp
    refine hq.congr (Metric.isOpen_ball.sdiff isClosed_singleton) fun w hw ↦ ?_
    have hw0 : w - z₀ ≠ 0 := sub_ne_zero.mpr hw.2
    have hwr : ‖w - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw.1
    rw [(hf w (norm_pos_iff.mpr hw0) hwr).tsum_eq, inv_mul_cancel_left₀ (pow_ne_zero k hw0)]
  · have hemp : Metric.ball z₀ r \ {z₀} = ∅ := by
      simp [Metric.ball_eq_empty.mpr (not_lt.mp hr)]
    rw [hemp]
    exact fun _ hx ↦ False.elim hx

/-- Over a densely normed field, if `∑ c n * (z - z₀) ^ n` is summable on the punctured open disc
`0 < ‖z - z₀‖ < r`, then `∑ c n * u ^ n` is absolutely summable for `‖u‖ < r`. -/
theorem summable_norm_mul_pow_of_norm_sub_lt {𝕜 : Type*} [DenselyNormedField 𝕜]
    (c : ℕ → 𝕜) (z₀ : 𝕜) {r : ℝ}
    (hc : ∀ z : 𝕜, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun n : ℕ ↦ c n * (z - z₀) ^ n)
    {u : 𝕜} (hu : ‖u‖ < r) : Summable fun n : ℕ ↦ ‖c n * u ^ n‖ :=
  (hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt c z₀ ((norm_nonneg u).trans_lt hu)
    hc).summable_norm_mul_pow_ofScalars (TauCeti.eNorm_lt_ofReal_iff.mpr hu)

/-- Over a densely normed field, if `∑ c n * (z - z₀) ^ n` is summable on the punctured open disc
`0 < ‖z - z₀‖ < r`, then `‖c n‖ * ρ ^ n` is uniformly bounded for every `0 ≤ ρ < r`. -/
theorem exists_norm_mul_pow_le_of_norm_sub_lt {𝕜 : Type*} [DenselyNormedField 𝕜]
    (c : ℕ → 𝕜) (z₀ : 𝕜) {r ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρr : ρ < r)
    (hc : ∀ z : 𝕜, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r → Summable fun n : ℕ ↦ c n * (z - z₀) ^ n) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ‖c n‖ * ρ ^ n ≤ M := by
  have hrad := (hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt c z₀ (hρ0.trans_lt hρr) hc).r_le
  lift ρ to ℝ≥0 using hρ0
  obtain ⟨M, hM, hMb⟩ := (ofScalars 𝕜 c).norm_mul_pow_le_of_lt_radius
    ((ENNReal.coe_lt_ofReal.mpr hρr).trans_le hrad)
  exact ⟨M, hM, fun n ↦ by simpa [ofScalars_norm] using hMb n⟩

/-- **Zero-freeness of the analytic sum forces the disk into the disk of convergence.** Over a
densely normed field, if the sum of a scalar series, which is `0` where the series does not
converge, has no zero in a disk about the origin, then that disk lies in the disk of convergence. -/
theorem le_radius_ofScalars_of_ofScalarsSum_ne_zero {𝕜 : Type*} [DenselyNormedField 𝕜]
    (a : ℕ → 𝕜) {r : ℝ≥0∞} (hne : ∀ z : 𝕜, ‖z‖ₑ < r → ofScalarsSum (E := 𝕜) a z ≠ 0) :
    r ≤ (ofScalars 𝕜 a).radius := by
  refine le_radius_ofScalars_of_summable a fun z _ hz ↦ ?_
  by_contra h
  refine hne z hz ?_
  simpa only [ofScalarsSum_eq_tsum, smul_eq_mul] using tsum_eq_zero_of_not_summable h

end FormalMultilinearSeries

namespace TauCeti

open scoped NNReal Ring

/-- The scalar multilinear series `∑ₙ C(n + k, k) xⁿ` in any normed `𝕜`-algebra `A` has radius of
convergence at least `1`. -/
theorem one_le_ofScalars_choose_radius (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] (k : ℕ) :
    1 ≤ (FormalMultilinearSeries.ofScalars A fun n : ℕ ↦ ((n + k).choose k : 𝕜)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [ENNReal.coe_lt_one_iff] at hr
  apply FormalMultilinearSeries.le_radius_of_summable
  rw [← summable_nat_add_iff 1]
  have hmaj : Summable fun n : ℕ ↦ (((n + 1 + k).choose k : ℕ) : ℝ) * (r : ℝ) ^ (n + 1) :=
    (summable_nat_add_iff (f := fun m : ℕ ↦ (((m + k).choose k : ℕ) : ℝ) * (r : ℝ) ^ m) 1).2
      (summable_choose_mul_geometric_of_norm_lt_one k (by simpa using hr))
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hmaj
  gcongr
  refine (FormalMultilinearSeries.ofScalars_norm_le A _ (n + 1) (Nat.succ_pos n)).trans ?_
  simpa using Nat.norm_cast_le (α := 𝕜) ((n + 1 + k).choose k)

/-- In a normed `𝕜`-algebra `A` with summable geometric series, `(1 - x)⁻¹ʳ ^ (k + 1)` is
represented on the open unit ball by the scalar series `∑ₙ C(n + k, k) xⁿ`. -/
theorem hasFPowerSeriesOnBall_inverse_one_sub_pow (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] (k : ℕ) :
    HasFPowerSeriesOnBall (fun x : A ↦ (1 - x)⁻¹ʳ ^ (k + 1))
      (FormalMultilinearSeries.ofScalars A fun n : ℕ ↦ ((n + k).choose k : 𝕜)) 0 1 where
  r_le := one_le_ofScalars_choose_radius 𝕜 A k
  r_pos := zero_lt_one
  hasSum {y} hy := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] at hy
    rw [zero_add]
    convert hasSum_choose_mul_geometric_of_norm_lt_one' k hy using 1
    ext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- Over any topological field `𝕜`, the one-variable series `TauCeti.mkPiRingSeries 𝕜 c` coincides
with `FormalMultilinearSeries.ofScalars 𝕜 c`. -/
theorem mkPiRingSeries_eq_ofScalars {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (c : ℕ → 𝕜) :
    mkPiRingSeries 𝕜 c = FormalMultilinearSeries.ofScalars 𝕜 c := by
  ext1 n
  rw [mkPiRingSeries_def, ← (FormalMultilinearSeries.ofScalars 𝕜 c n).mkPiRing_apply_one_eq_self]
  simp [FormalMultilinearSeries.ofScalars]

/-- Shifting a scalar power series `FormalMultilinearSeries.ofScalarsSum c` by `z₀` gives a
`HasFPowerSeriesOnBall` expansion around `z₀`, provided its convergence radius is positive. -/
theorem hasFPowerSeriesOnBall_ofScalarsSum_sub {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing E] [NormedAlgebra 𝕜 E] [CompleteSpace E] (c : ℕ → 𝕜) (z₀ : E)
    (hr : 0 < (FormalMultilinearSeries.ofScalars E c).radius) :
    HasFPowerSeriesOnBall (fun z : E ↦ FormalMultilinearSeries.ofScalarsSum c (z - z₀))
      (FormalMultilinearSeries.ofScalars E c) z₀
      (FormalMultilinearSeries.ofScalars E c).radius := by
  simpa only [FormalMultilinearSeries.ofScalarsSum, zero_add] using
    ((FormalMultilinearSeries.ofScalars E c).hasFPowerSeriesOnBall hr).comp_sub z₀

/-- A shifted scalar power series `z ↦ FormalMultilinearSeries.ofScalarsSum c (z - z₀)` is analytic
on its open ball of convergence around `z₀`. -/
theorem analyticOnNhd_ofScalarsSum_sub {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing E] [NormedAlgebra 𝕜 E] [CompleteSpace E] (c : ℕ → 𝕜) (z₀ : E) :
    AnalyticOnNhd 𝕜 (fun z : E ↦ FormalMultilinearSeries.ofScalarsSum c (z - z₀))
      (Metric.eball z₀ (FormalMultilinearSeries.ofScalars E c).radius) :=
  (FormalMultilinearSeries.ofScalars E c).analyticOnNhd.comp
    (analyticOnNhd_id.sub analyticOnNhd_const) fun z hz ↦ by
      simpa [Metric.mem_eball, edist_zero_right, eDist_eq_eNorm_sub] using hz

end TauCeti
