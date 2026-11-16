/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix.Basic

/-!
# Substitution of a restricted power series into a vector-valued null sequence

Let `R` be an ultrametric normed ring and `E` a complete ultrametric normed `R`-module. A sequence
`b ∈ C₀(ℕ, E)` is the coefficient vector of the convergent series `z ↦ ∑' n, z ^ n • b n` on the
closed unit disc `‖z‖ ≤ 1` of `R` (when `R` is commutative). Given a scalar power series `g ∈ R⟦X⟧`
restricted at the radius `1` whose coefficients satisfy `‖coeff k g‖ ≤ 1` for all `k`, substituting
`z = g(w)` re-expands `∑' n, g(w) ^ n • b n` in powers of `w`:

```text
c_k = ∑' n, coeff k (g ^ n) • b n,    ∑' k, w ^ k • c_k = ∑' n, (g.evalAt w) ^ n • b n  (‖w‖ ≤ 1).
```

Because `R` is ultrametric, every positive power `g ^ n` again has coefficients of norm at most
`1` and is restricted at `1`. At `n = 0` the series `g ^ 0 = 1` acts on `b 0` by `1 • b 0 = b 0`,
so neither `NormOneClass R` nor nontriviality of `R` is needed. Using `Matrix.toZeroAtInftySMulCLM`
on the matrix `(coeff k (g ^ n))_{k, n}`, the re-expanded coefficients form a continuous linear
operator `TauCeti.PowerSeries.compNullSeq` of norm at most `1` on `C₀(ℕ, E)`, linear over every
scalar semiring `S` commuting with the `R`-action on `E`. When `g` has zero constant coefficient,
`c_0 = b 0` and every higher coefficient `c_k` (`k ≠ 0`) depends only on `b n` for `n ≠ 0`. Over a
commutative ring, `compNullSeq` is contravariantly functorial under `PowerSeries.subst` of series
with zero constant term.

## Main definitions

* `TauCeti.PowerSeries.compNullSeq`: the pullback `C₀(ℕ, E) →L[S] C₀(ℕ, E)` sending `b` to
  `k ↦ ∑' n, coeff k (g ^ n) • b n`.

## Main results

* `TauCeti.PowerSeries.norm_coeff_mul_le`, `TauCeti.PowerSeries.norm_coeff_pow_le`,
  `TauCeti.PowerSeries.norm_coeff_pow_le_one`: ultrametric uniform coefficient bounds for products
  and positive powers of power series over a seminormed ring.
* `TauCeti.PowerSeries.hasSum_compNullSeq_apply`, `TauCeti.PowerSeries.compNullSeq_apply`,
  `TauCeti.PowerSeries.compNullSeq_single_apply`, `TauCeti.PowerSeries.compNullSeq_X`,
  `TauCeti.PowerSeries.compNullSeq_zero`, `TauCeti.PowerSeries.compLeft_compNullSeq`: coefficient
  summation, basis action, behavior at `X` and `0`, and naturality under continuous `R`-linear maps.
* `TauCeti.PowerSeries.norm_compNullSeq_le`, `TauCeti.PowerSeries.opNorm_compNullSeq_le_one`:
  `compNullSeq` does not increase the sup norm and has operator norm at most `1`.
* `TauCeti.PowerSeries.compNullSeq_apply_zero_of_constantCoeff_eq_zero`: when
  `constantCoeff g = 0`, the constant term is `b 0`.
* `TauCeti.PowerSeries.norm_compNullSeq_apply_le_of_ne_zero`: every positive-degree coefficient is
  bounded by any nonnegative bound on `b n` for `n ≠ 0`.
* `TauCeti.PowerSeries.norm_coeff_subst_le_one`, `TauCeti.PowerSeries.isRestricted_subst_one`,
  `TauCeti.PowerSeries.compNullSeq_subst`: restrictedness and contravariant functoriality under
  formal power-series substitution.
* `TauCeti.PowerSeries.hasSum_pow_smul_compNullSeq`,
  `TauCeti.PowerSeries.tsum_pow_smul_compNullSeq`: when `R` is commutative and complete, evaluating
  the pulled-back series at any `w` with `‖w‖ ≤ 1` gives `∑' n, (g.evalAt w) ^ n • b n`.
-/

public section

open Filter Topology
open scoped PowerSeries ZeroAtInfty

namespace TauCeti.PowerSeries

open _root_.PowerSeries

section CoeffBounds

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]

/-- Over an ultrametric seminormed ring, uniform bounds `r` and `s` on the coefficients of `f` and
`g` bound every coefficient of `f * g` by `r * s`. -/
theorem norm_coeff_mul_le {f g : R⟦X⟧} {r s : ℝ} (hf : ∀ k, ‖coeff k f‖ ≤ r)
    (hg : ∀ k, ‖coeff k g‖ ≤ s) (k : ℕ) :
    ‖coeff k (f * g)‖ ≤ r * s := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hf 0)
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hg 0)
  rw [coeff_mul]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr0 hs0) fun p _ ↦
    (norm_mul_le _ _).trans (mul_le_mul (hf p.1) (hg p.2) (norm_nonneg _) hr0)

/-- Over an ultrametric seminormed ring, if every coefficient of `g` has norm at most `r`, then
every coefficient of a positive power `g ^ n` (`n ≠ 0`) has norm at most `r ^ n`. -/
theorem norm_coeff_pow_le {g : R⟦X⟧} {r : ℝ} (hgn : ∀ k, ‖coeff k g‖ ≤ r) {n : ℕ} (hn : n ≠ 0)
    (k : ℕ) :
    ‖coeff k (g ^ n)‖ ≤ r ^ n := by
  induction n generalizing k with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simpa using hgn k
    · rw [pow_succ, pow_succ]
      exact norm_coeff_mul_le (ih hn0) hgn k

/-- Over an ultrametric seminormed ring, every positive power of a power series whose coefficients
have norm at most `1` also has coefficients of norm at most `1`. -/
theorem norm_coeff_pow_le_one {g : R⟦X⟧} (hgn : ∀ k, ‖coeff k g‖ ≤ 1) {n : ℕ} (hn : n ≠ 0)
    (k : ℕ) :
    ‖coeff k (g ^ n)‖ ≤ 1 := by
  simpa only [one_pow] using norm_coeff_pow_le hgn hn k

end CoeffBounds

section Operator

variable {R E : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] {g : R⟦X⟧}

-- Acting on `e : E` by a coefficient of `g ^ n` never increases its norm, including at `n = 0`
-- where `(1 : R) • e = e` without needing `NormOneClass R`.
private theorem norm_coeff_pow_smul_le (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (e : E) (n k : ℕ) :
    ‖coeff k (g ^ n) • e‖ ≤ ‖e‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [coeff_one, hk]
  · exact (norm_smul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg e) (norm_coeff_pow_le_one hgn hn k))

private theorem tendsto_coeff_pow_cofinite (hg : g.IsRestricted 1) (n : ℕ) :
    Tendsto (fun k ↦ coeff k (g ^ n)) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  have hp : (g ^ n).IsRestricted 1 := (IsRestricted.subring (R := R) 1).pow_mem hg n
  simpa [tendsto_zero_iff_norm_tendsto_zero] using (isRestricted_iff' 1 (g ^ n)).mp hp

private theorem norm_coeff_pow_le_max_one (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (k n : ℕ) :
    ‖coeff k (g ^ n)‖ ≤ max 1 ‖(1 : R)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [coeff_one, hk]
  · exact (norm_coeff_pow_le_one hgn hn k).trans (le_max_left 1 ‖(1 : R)‖)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- **Pullback of a null sequence along a restricted series.** For `g : R⟦X⟧` restricted at `1`
with `‖coeff k g‖ ≤ 1`, `compNullSeq` sends `b ∈ C₀(ℕ, E)` to `k ↦ ∑' n, coeff k (g ^ n) • b n`.
It is linear over any scalar semiring `S` commuting with the `R`-action on `E` and is contractive
without requiring `NormOneClass R`. -/
noncomputable def compNullSeq (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) :
    C₀(ℕ, E) →L[S] C₀(ℕ, E) :=
  Matrix.toZeroAtInftySMulCLM S (Matrix.of fun k n ↦ coeff k (g ^ n))
    (tendsto_coeff_pow_cofinite hg) ⟨max 1 ‖(1 : R)‖, norm_coeff_pow_le_max_one hgn⟩

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

/-- The `k`-th entry of `compNullSeq` is the unconditional sum `∑ n, coeff k (g ^ n) • b n`. -/
theorem hasSum_compNullSeq_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) (k : ℕ) :
    HasSum (fun n ↦ coeff k (g ^ n) • b n) (compNullSeq S hg hgn b k) :=
  Matrix.hasSum_toZeroAtInftySMulCLM_apply S (Matrix.of fun k n ↦ coeff k (g ^ n)) _ _ b k

/-- The `k`-th entry of `compNullSeq` is `∑' n, coeff k (g ^ n) • b n`. -/
theorem compNullSeq_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E))
    (k : ℕ) : compNullSeq S hg hgn b k = ∑' n, coeff k (g ^ n) • b n :=
  (hasSum_compNullSeq_apply S hg hgn b k).tsum_eq.symm

/-- `compNullSeq` sends the basis element `single m e` to `k ↦ coeff k (g ^ m) • e`. -/
@[simp]
theorem compNullSeq_single_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (m : ℕ) (e : E) (k : ℕ) :
    compNullSeq S hg hgn (ZeroAtInftyContinuousMap.single m e) k = coeff k (g ^ m) • e :=
  Matrix.toZeroAtInftySMulCLM_single_apply S (Matrix.of fun k n ↦ coeff k (g ^ n)) _ _ m e k

/-- Pulling back along `X` is the identity on `C₀(ℕ, E)`. -/
@[simp]
theorem compNullSeq_X (hX : (X : R⟦X⟧).IsRestricted 1) (hXn : ∀ k, ‖coeff k (X : R⟦X⟧)‖ ≤ 1) :
    compNullSeq S hX hXn = ContinuousLinearMap.id S C₀(ℕ, E) := by
  ext b k
  rw [compNullSeq_apply, ContinuousLinearMap.id_apply, tsum_eq_single k]
  · simp
  · intro n hn
    simp [coeff_X_pow, hn.symm]

/-- Pulling back along `0 : R⟦X⟧` retains only the constant term `single 0 (b 0)`. -/
theorem compNullSeq_zero (h0 : (0 : R⟦X⟧).IsRestricted 1) (h0n : ∀ k, ‖coeff k (0 : R⟦X⟧)‖ ≤ 1)
    (b : C₀(ℕ, E)) :
    compNullSeq S h0 h0n b = ZeroAtInftyContinuousMap.single 0 (b 0) := by
  ext k
  rw [compNullSeq_apply, tsum_eq_single 0]
  · rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [coeff_one, hk]
  · intro n hn
    simp [zero_pow hn]

/-- `compNullSeq` commutes with postcomposition by any uniformly bounded continuous `R`-linear map.
-/
theorem compLeft_compNullSeq {F : Type*} [NormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]
    [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass R S' F]
    (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E)) :
    ZeroAtInftyContinuousMap.compLeft u hu (compNullSeq S hg hgn b) =
      compNullSeq S' hg hgn (ZeroAtInftyContinuousMap.compLeft u hu b) := by
  ext k
  rw [ZeroAtInftyContinuousMap.compLeft_apply]
  refine ((hasSum_compNullSeq_apply S hg hgn b k).mapL u).unique ?_
  simpa [Function.comp_def] using
    hasSum_compNullSeq_apply S' hg hgn (ZeroAtInftyContinuousMap.compLeft u hu b) k

/-- Pulling back a null sequence along a unit-ball restricted series does not increase its norm. -/
theorem norm_compNullSeq_le (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E)) :
    ‖compNullSeq S hg hgn b‖ ≤ ‖b‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg b)).mpr fun k ↦ by
    rw [compNullSeq_apply]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg b) fun n ↦
      (norm_coeff_pow_smul_le hgn (b n) n k).trans (b.norm_coe_le_norm n)

/-- Over a nontrivially normed scalar field, `compNullSeq` has operator norm at most `1`. -/
theorem opNorm_compNullSeq_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass R 𝕜 E] (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) :
    ‖(compNullSeq 𝕜 hg hgn : C₀(ℕ, E) →L[𝕜] C₀(ℕ, E))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b ↦ by
    simpa using norm_compNullSeq_le 𝕜 hg hgn b

/-- When `g` has zero constant coefficient, the `0`-th term of the pulled-back sequence is `b 0`. -/
@[simp]
theorem compNullSeq_apply_zero_of_constantCoeff_eq_zero (hg : g.IsRestricted 1)
    (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (hg0 : constantCoeff g = 0) (b : C₀(ℕ, E)) :
    compNullSeq S hg hgn b 0 = b 0 := by
  rw [compNullSeq_apply, tsum_eq_single 0]
  · simp
  · intro n hn
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hg0, zero_pow hn, zero_smul]

/-- Since `g ^ 0 = 1` contributes nothing in positive degrees, every coefficient
`compNullSeq S hg hgn b k` (`k ≠ 0`) is bounded by any bound `B ≥ 0` on `‖b n‖` for `n ≠ 0`. -/
theorem norm_compNullSeq_apply_le_of_ne_zero (hg : g.IsRestricted 1)
    (hgn : ∀ k, ‖coeff k g‖ ≤ 1) {b : C₀(ℕ, E)} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n ≠ 0, ‖b n‖ ≤ B) {k : ℕ} (hk : k ≠ 0) :
    ‖compNullSeq S hg hgn b k‖ ≤ B := by
  rw [compNullSeq_apply]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB0 fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_one, hk, hB0]
  · exact (norm_coeff_pow_smul_le hgn (b n) n k).trans (hB n hn)

end Operator

section Subst

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {f g : R⟦X⟧}

/-- Substituting a unit-ball series `f` with zero constant term into a unit-ball series `g`
preserves the unit-ball coefficient bound (without needing `NormOneClass R`). -/
theorem norm_coeff_subst_le_one (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (hfn : ∀ k, ‖coeff k f‖ ≤ 1)
    (hf0 : constantCoeff f = 0) (k : ℕ) :
    ‖coeff k (g.subst f)‖ ≤ 1 := by
  rw [coeff_subst_eq_sum_range g hf0 k]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm
  · rcases eq_or_ne k 0 with rfl | hk
    · simpa using hgn 0
    · simp [coeff_one, hk]
  · rw [smul_eq_mul]
    exact (norm_mul_le _ _).trans <|
      (mul_le_mul (hgn m) (norm_coeff_pow_le_one hfn hm k) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)

/-- Substituting a restricted unit-ball series `f` with zero constant term into a series `g`
restricted at radius `1` yields a series restricted at radius `1`. -/
theorem isRestricted_subst_one (hg : g.IsRestricted 1) (hf : f.IsRestricted 1)
    (hfn : ∀ k, ‖coeff k f‖ ≤ 1) (hf0 : constantCoeff f = 0) :
    PowerSeries.IsRestricted 1 (g.subst f) := by
  rw [isRestricted_iff']
  simp only [one_pow, mul_one]
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  have hg_lim : Tendsto (fun m ↦ ‖coeff m g‖) atTop (𝓝 0) := by
    simpa only [one_pow, mul_one] using (isRestricted_iff' 1 g).mp hg
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hg_lim (ε / 2) (half_pos hε)
  have hhead : ∀ m ∈ Finset.range (M + 1),
      ∀ᶠ k in atTop, ‖coeff m g * coeff k (f ^ m)‖ < ε / 2 := fun m _ ↦ by
    have hfm : Tendsto (fun k ↦ coeff k (f ^ m)) atTop (𝓝 0) := by
      simpa only [Nat.cofinite_eq_atTop] using tendsto_coeff_pow_cofinite hf m
    have hm_lim : Tendsto (fun k ↦ coeff m g * coeff k (f ^ m)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hfm.const_mul (coeff m g)
    exact NormedAddGroup.tendsto_nhds_zero.mp hm_lim (ε / 2) (half_pos hε)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((Finset.range (M + 1)).eventually_all.mpr hhead)
  refine ⟨K, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_norm, coeff_subst_eq_sum_range g hf0 k]
  refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hε).le
    fun m _ ↦ ?_).trans_lt (half_lt_self hε)
  rcases lt_or_ge m (M + 1) with hm | hm
  · rw [smul_eq_mul]
    exact (hK k hk m (Finset.mem_range.mpr hm)).le
  · have hm0 : m ≠ 0 := by omega
    have hgm : ‖coeff m g‖ < ε / 2 := by
      simpa [Real.dist_eq, abs_norm] using hM m (by omega)
    rw [smul_eq_mul]
    exact (norm_mul_le _ _).trans <|
      (mul_le_of_le_one_right (norm_nonneg _) (norm_coeff_pow_le_one hfn hm0 k)).trans hgm.le

/-- **Contravariant functoriality of `compNullSeq` under formal substitution.** When `f` has zero
constant coefficient, pulling back along `g` and then along `f` equals pulling back along
`g.subst f`. -/
theorem compNullSeq_subst {E : Type*} [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
    [IsUltrametricDist E] [CompleteSpace E]
    (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]
    (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (hf : f.IsRestricted 1) (hfn : ∀ k, ‖coeff k f‖ ≤ 1) (hf0 : constantCoeff f = 0)
    (b : C₀(ℕ, E)) :
    compNullSeq S hf hfn (compNullSeq S hg hgn b) =
      compNullSeq S (isRestricted_subst_one hg hf hfn hf0) (norm_coeff_subst_le_one hgn hfn hf0)
        b := by
  have hsub_f : HasSubst f := .of_constantCoeff_zero' hf0
  ext k
  have hfin : compNullSeq S hf hfn (compNullSeq S hg hgn b) k =
      ∑ m ∈ Finset.range (k + 1), coeff k (f ^ m) • compNullSeq S hg hgn b m := by
    rw [compNullSeq_apply]
    refine tsum_eq_sum fun m hm ↦ ?_
    rw [Finset.mem_range, not_lt] at hm
    have hlt : (k : ENat) < (f ^ m).order :=
      (Nat.cast_lt.mpr (by omega : k < m)).trans_le (le_order_pow_of_constantCoeff_eq_zero m hf0)
    rw [coeff_of_lt_order k hlt, zero_smul]
  rw [hfin]
  have hsum : HasSum
      (fun n ↦ ∑ m ∈ Finset.range (k + 1), coeff k (f ^ m) • (coeff m (g ^ n) • b n))
      (∑ m ∈ Finset.range (k + 1), coeff k (f ^ m) • compNullSeq S hg hgn b m) :=
    hasSum_sum fun m _ ↦ (hasSum_compNullSeq_apply S hg hgn b m).const_smul (coeff k (f ^ m))
  have heq (n : ℕ) :
      coeff k ((g.subst f) ^ n) • b n =
        ∑ m ∈ Finset.range (k + 1), coeff k (f ^ m) • (coeff m (g ^ n) • b n) := by
    symm
    calc ∑ m ∈ Finset.range (k + 1), coeff k (f ^ m) • (coeff m (g ^ n) • b n)
        = (∑ m ∈ Finset.range (k + 1), coeff m (g ^ n) • coeff k (f ^ m)) • b n := by
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun m _ ↦ by rw [smul_smul, smul_eq_mul, mul_comm]
      _ = coeff k ((g.subst f) ^ n) • b n := by
          rw [← coeff_subst_eq_sum_range (g ^ n) hf0 k, subst_pow hsub_f]
  exact (hsum.congr_fun heq).unique (hasSum_compNullSeq_apply S _ _ b k)

end Subst

section Eval

variable {R E : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] {g : R⟦X⟧}

private theorem norm_pow_smul_coeff_pow_smul_le (hgn : ∀ k, ‖coeff k g‖ ≤ 1) {w : R}
    (hw : ‖w‖ ≤ 1) (e : E) (k n : ℕ) :
    ‖w ^ k • (coeff k (g ^ n) • e)‖ ≤ ‖e‖ := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using norm_coeff_pow_smul_le hgn e n 0
  · refine (norm_smul_le _ _).trans ?_
    have hwk : ‖w ^ k‖ ≤ 1 :=
      (norm_pow_le' w (Nat.pos_of_ne_zero hk)).trans (pow_le_one₀ (norm_nonneg w) hw)
    exact (mul_le_of_le_one_left (norm_nonneg _) hwk).trans (norm_coeff_pow_smul_le hgn e n k)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- Every bivariate term `w ^ k • (coeff k (g ^ n) • b n)` is dominated by `‖b n‖` and vanishes
in `k` for each fixed `n`, so packaging the `n`-indexed rows via
`ZeroAtInftyContinuousMap.curryEquiv` shows that the uncurried family is summable. -/
private theorem summable_uncurry_pow_smul (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    Summable (Function.uncurry fun k n ↦ w ^ k • (coeff k (g ^ n) • b n)) := by
  let row (n : ℕ) : C₀(ℕ, E) :=
    ZeroAtInftyContinuousMap.mkOfDiscrete (fun k ↦ w ^ k • (coeff k (g ^ n) • b n)) <| by
      have hp : (g ^ n).IsRestricted 1 := (IsRestricted.subring (R := R) 1).pow_mem hg n
      have h0 : Tendsto (fun k ↦ (coeff k (g ^ n) • w ^ k) • b n) cofinite (𝓝 0) := by
        simpa using (hp.tendsto_smul_pow hw).smul_const (b n)
      exact h0.congr fun k ↦ by rw [smul_eq_mul, mul_comm, mul_smul]
  have hrow_le (n : ℕ) : ‖row n‖ ≤ ‖b n‖ :=
    (ZeroAtInftyContinuousMap.norm_le (norm_nonneg (b n))).mpr fun k ↦ by
      simpa [row] using norm_pow_smul_coeff_pow_smul_le hgn hw (b n) k n
  let rows : C₀(ℕ, C₀(ℕ, E)) :=
    ZeroAtInftyContinuousMap.mkOfDiscrete row <|
      squeeze_zero_norm hrow_le (tendsto_zero_iff_norm_tendsto_zero.mp b.tendsto_cofinite)
  have hsum_swap : Summable (Function.uncurry fun n k ↦ w ^ k • (coeff k (g ^ n) • b n)) := by
    have hs := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      ((ZeroAtInftyContinuousMap.curryEquiv ℕ E).symm rows).tendsto_cofinite
    exact hs.congr fun ⟨n, k⟩ ↦ by simp [rows, row]
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mp hsum_swap

variable [CompleteSpace R]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

/-- At any `w : R` with `‖w‖ ≤ 1`, the pulled-back sequence `compNullSeq S hg hgn b` sums to
`∑' n, (g.evalAt w) ^ n • b n`. -/
theorem hasSum_pow_smul_compNullSeq (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    HasSum (fun k ↦ w ^ k • compNullSeq S hg hgn b k) (∑' n, (g.evalAt w) ^ n • b n) := by
  have hF := summable_uncurry_pow_smul hg hgn b hw
  have hcol (n : ℕ) :
      HasSum (fun k ↦ w ^ k • (coeff k (g ^ n) • b n)) ((g.evalAt w) ^ n • b n) := by
    have hp : (g ^ n).IsRestricted 1 := (IsRestricted.subring (R := R) 1).pow_mem hg n
    have hev : (g ^ n).evalAt w = (g.evalAt w) ^ n := by
      simpa using (IsRestricted.evalAtHom R hw).map_pow ⟨g, hg⟩ n
    have hs := (hp.hasSum_evalAt (b := w) hw).smul_const (b n)
    rw [hev] at hs
    exact hs.congr_fun fun k ↦ by rw [smul_eq_mul, mul_comm, mul_smul]
  have hrow (k : ℕ) :
      HasSum (fun n ↦ w ^ k • (coeff k (g ^ n) • b n)) (w ^ k • compNullSeq S hg hgn b k) :=
    (hasSum_compNullSeq_apply S hg hgn b k).const_smul (w ^ k)
  rw [(((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hF.hasSum).prod_fiberwise hcol).tsum_eq]
  exact hF.hasSum.prod_fiberwise hrow

/-- **Evaluation of a pulled-back null sequence.** When `R` is complete, for every `w : R` with
`‖w‖ ≤ 1`, `∑' k, w ^ k • compNullSeq S hg hgn b k = ∑' n, (g.evalAt w) ^ n • b n`. -/
theorem tsum_pow_smul_compNullSeq (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    ∑' k, w ^ k • compNullSeq S hg hgn b k = ∑' n, (g.evalAt w) ^ n • b n :=
  (hasSum_pow_smul_compNullSeq S hg hgn b hw).tsum_eq

end Eval

end TauCeti.PowerSeries
