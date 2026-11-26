/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Restricted.Substitution
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.RingTheory.PowerSeries.Restricted
import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix.Basic

/-!
# Substitution of a restricted power series into a vector-valued null sequence

Let `R` be an ultrametric normed ring and `E` a complete ultrametric normed `R`-module. A sequence
`b ∈ C₀(ℕ, E)` gives the coefficients of `z ↦ ∑' n, z ^ n • b n` on `‖z‖ ≤ 1`. Given `g ∈ R⟦X⟧`
restricted at radius `1` with `‖coeff k g‖ ≤ 1`, substituting `z = g(w)` re-expands the series as

```text
c_k = ∑' n, coeff k (g ^ n) • b n,    ∑' k, w ^ k • c_k = ∑' n, (g.evalAt w) ^ n • b n  (‖w‖ ≤ 1).
```

Built via `Matrix.toZeroAtInftySMulCLM` on `(coeff k (g ^ n))_{k, n}` without requiring
`NormOneClass R`, the pullback `PowerSeries.compNullSeq` is a contractive continuous `S`-linear
operator on `C₀(ℕ, E)` for any scalar semiring `S` commuting with `R`. When `constantCoeff g = 0`,
`c_0 = b 0` and each higher `c_k` depends only on `b n` (`n ≠ 0`). Over a commutative ring,
`compNullSeq` is contravariantly functorial under `PowerSeries.subst` of series with zero constant
term, and evaluates as above when `R` is complete.

## Main definitions

* `PowerSeries.compNullSeq`: pullback `C₀(ℕ, E) →L[S] C₀(ℕ, E)` sending `b` to
  `k ↦ ∑' n, coeff k (g ^ n) • b n`.

## Main results

* `PowerSeries.hasSum_compNullSeq_apply`, `PowerSeries.compNullSeq_apply`,
  `PowerSeries.compNullSeq_single_apply`, `PowerSeries.compNullSeq_X`,
  `PowerSeries.compNullSeq_zero`, `PowerSeries.compLeft_compNullSeq`: summation, basis action,
  values at `X` and `0`, and naturality under continuous `R`-linear maps.
* `PowerSeries.norm_compNullSeq_le`, `PowerSeries.opNorm_compNullSeq_le_one`: contractivity.
* `PowerSeries.compNullSeq_apply_zero_of_constantCoeff_eq_zero`,
  `PowerSeries.norm_compNullSeq_apply_le_of_ne_zero`: constant and positive-degree bounds.
* `PowerSeries.compNullSeq_subst`: contravariant functoriality under `PowerSeries.subst`.
* `PowerSeries.hasSum_pow_smul_compNullSeq`, `PowerSeries.tsum_pow_smul_compNullSeq`: evaluation
  at `w : R` with `‖w‖ ≤ 1`.
-/

public section

open Filter Topology
open scoped PowerSeries ZeroAtInfty

namespace PowerSeries

section Operator

variable {R E : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] {g : R⟦X⟧}

-- Acting on `e : E` by a coefficient of `g ^ n` never increases its norm, including at `n = 0`
-- where `(1 : R) • e = e` without needing `NormOneClass R`.
private theorem norm_coeff_pow_smul_le (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (e : E) (n k : ℕ) :
    ‖coeff k (g ^ n) • e‖ ≤ ‖e‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne k 0 with rfl | hk <;> simp [coeff_one, *]
  · exact (norm_smul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg e) (norm_coeff_pow_le_one hgn hn k))

private theorem norm_coeff_pow_le_max_one (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (k n : ℕ) :
    ‖coeff k (g ^ n)‖ ≤ max 1 ‖(1 : R)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne k 0 with rfl | hk <;> simp [coeff_one, *]
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
    (fun n ↦ tendsto_coeff_cofinite_iff_isRestricted_one.mpr (hg.pow n))
    ⟨max 1 ‖(1 : R)‖, norm_coeff_pow_le_max_one hgn⟩

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

/-- The `k`-th entry of `compNullSeq` is the unconditional sum `∑ n, coeff k (g ^ n) • b n`. -/
theorem hasSum_compNullSeq_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) (k : ℕ) : HasSum (fun n ↦ coeff k (g ^ n) • b n) (compNullSeq S hg hgn b k) :=
  Matrix.hasSum_toZeroAtInftySMulCLM_apply S (Matrix.of fun k n ↦ coeff k (g ^ n)) _ _ b k

/-- The `k`-th entry of `compNullSeq` is `∑' n, coeff k (g ^ n) • b n`. -/
theorem compNullSeq_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E))
    (k : ℕ) : compNullSeq S hg hgn b k = ∑' n, coeff k (g ^ n) • b n :=
  (hasSum_compNullSeq_apply S hg hgn b k).tsum_eq.symm

/-- `compNullSeq` sends the basis element `single m e` to `k ↦ coeff k (g ^ m) • e`. -/
@[simp] theorem compNullSeq_single_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (m : ℕ) (e : E) (k : ℕ) :
    compNullSeq S hg hgn (ZeroAtInftyContinuousMap.single m e) k = coeff k (g ^ m) • e :=
  Matrix.toZeroAtInftySMulCLM_single_apply S (Matrix.of fun k n ↦ coeff k (g ^ n)) _ _ m e k

/-- Pulling back along `X` is the identity on `C₀(ℕ, E)`. -/
@[simp] theorem compNullSeq_X (hX : (X : R⟦X⟧).IsRestricted 1)
    (hXn : ∀ k, ‖coeff k (X : R⟦X⟧)‖ ≤ 1) :
    compNullSeq S hX hXn = ContinuousLinearMap.id S C₀(ℕ, E) := by
  ext b k
  rw [compNullSeq_apply, ContinuousLinearMap.id_apply,
    tsum_eq_single k fun n hn ↦ by simp [coeff_X_pow, hn.symm]]
  simp

/-- Pulling back along `0 : R⟦X⟧` retains only the constant term `single 0 (b 0)`. -/
theorem compNullSeq_zero (h0 : (0 : R⟦X⟧).IsRestricted 1) (h0n : ∀ k, ‖coeff k (0 : R⟦X⟧)‖ ≤ 1)
    (b : C₀(ℕ, E)) : compNullSeq S h0 h0n b = ZeroAtInftyContinuousMap.single 0 (b 0) := by
  ext k
  rw [compNullSeq_apply, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  rcases eq_or_ne k 0 with rfl | hk <;> simp [coeff_one, *]

/-- `compNullSeq` commutes with postcomposition by a uniformly bounded continuous `R`-linear map. -/
theorem compLeft_compNullSeq {F : Type*} [NormedAddCommGroup F] [Module R F] [IsBoundedSMul R F]
    [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass R S' F]
    (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E)) :
    ZeroAtInftyContinuousMap.compLeft u hu (compNullSeq S hg hgn b) =
      compNullSeq S' hg hgn (ZeroAtInftyContinuousMap.compLeft u hu b) := by
  ext k; rw [ZeroAtInftyContinuousMap.compLeft_apply]
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
@[simp] theorem compNullSeq_apply_zero_of_constantCoeff_eq_zero (hg : g.IsRestricted 1)
    (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (hg0 : constantCoeff g = 0) (b : C₀(ℕ, E)) :
    compNullSeq S hg hgn b 0 = b 0 := by
  rw [compNullSeq_apply, tsum_eq_single 0 fun n hn ↦ by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hg0, zero_pow hn, zero_smul]]
  simp

/-- Since `g ^ 0 = 1` contributes nothing in positive degrees, every coefficient
`compNullSeq S hg hgn b k` (`k ≠ 0`) is bounded by any bound `B ≥ 0` on `‖b n‖` for `n ≠ 0`. -/
theorem norm_compNullSeq_apply_le_of_ne_zero (hg : g.IsRestricted 1)
    (hgn : ∀ k, ‖coeff k g‖ ≤ 1) {b : C₀(ℕ, E)} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n ≠ 0, ‖b n‖ ≤ B) {k : ℕ} (hk : k ≠ 0) : ‖compNullSeq S hg hgn b k‖ ≤ B := by
  rw [compNullSeq_apply]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB0 fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_one, hk, hB0]
  · exact (norm_coeff_pow_smul_le hgn (b n) n k).trans (hB n hn)

end Operator

section CommRing

variable {R E : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] {f g : R⟦X⟧}

private theorem norm_pow_smul_coeff_pow_smul_le (hgn : ∀ k, ‖coeff k g‖ ≤ 1) {w : R}
    (hw : ‖w‖ ≤ 1) (e : E) (k n : ℕ) : ‖w ^ k • (coeff k (g ^ n) • e)‖ ≤ ‖e‖ := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using norm_coeff_pow_smul_le hgn e n 0
  · refine (norm_smul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      (norm_coeff_pow_smul_le hgn e n k)
    exact (norm_pow_le' w (Nat.pos_of_ne_zero hk)).trans (pow_le_one₀ (norm_nonneg w) hw)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- **Contravariant functoriality of `compNullSeq` under formal substitution.** When `f` has zero
constant coefficient, pulling back along `g` and then along `f` equals pulling back along
`g.subst f`. -/
theorem compNullSeq_subst (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (hf : f.IsRestricted 1) (hfn : ∀ k, ‖coeff k f‖ ≤ 1) (hf0 : constantCoeff f = 0)
    (b : C₀(ℕ, E)) :
    compNullSeq S hf hfn (compNullSeq S hg hgn b) =
      compNullSeq S (hg.subst_one hf hfn hf0) (norm_coeff_subst_le hgn hfn hf0) b := by
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
  have heq (n : ℕ) : coeff k ((g.subst f) ^ n) • b n =
      ∑ m ∈ Finset.range (k + 1), coeff k (f ^ m) • (coeff m (g ^ n) • b n) := by
    rw [← subst_pow (.of_constantCoeff_zero' hf0), coeff_subst_eq_sum_range (g ^ n) hf0 k,
      Finset.sum_smul]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [smul_smul, smul_eq_mul, mul_comm]
  exact (hsum.congr_fun heq).unique (hasSum_compNullSeq_apply S _ _ b k)

/-- Every bivariate term `w ^ k • (coeff k (g ^ n) • b n)` is dominated by `‖b n‖` and vanishes
in `k` for each fixed `n`, so packaging the `n`-indexed rows via
`ZeroAtInftyContinuousMap.curryEquiv` shows that the uncurried family is summable. -/
private theorem summable_uncurry_pow_smul (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    Summable (Function.uncurry fun k n ↦ w ^ k • (coeff k (g ^ n) • b n)) := by
  let row (n : ℕ) : C₀(ℕ, E) :=
    ZeroAtInftyContinuousMap.mkOfDiscrete (fun k ↦ w ^ k • (coeff k (g ^ n) • b n)) <| by
      have hp : (g ^ n).IsRestricted 1 := (IsRestricted.subring (R := R) 1).pow_mem hg n
      exact ((by simpa using (hp.tendsto_smul_pow hw).smul_const (b n) :
        Tendsto (fun k ↦ (coeff k (g ^ n) • w ^ k) • b n) cofinite (𝓝 0))).congr
        fun k ↦ by rw [smul_eq_mul, mul_comm, mul_smul]
  have hrow_le (n : ℕ) : ‖row n‖ ≤ ‖b n‖ :=
    (ZeroAtInftyContinuousMap.norm_le (norm_nonneg (b n))).mpr fun k ↦ by
      simpa [row] using norm_pow_smul_coeff_pow_smul_le hgn hw (b n) k n
  let rows : C₀(ℕ, C₀(ℕ, E)) := ZeroAtInftyContinuousMap.mkOfDiscrete row <|
    squeeze_zero_norm hrow_le (tendsto_zero_iff_norm_tendsto_zero.mp b.tendsto_cofinite)
  exact (Equiv.prodComm ℕ ℕ).summable_iff.mp <|
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      ((ZeroAtInftyContinuousMap.curryEquiv ℕ E).symm rows).tendsto_cofinite).congr
      fun ⟨n, k⟩ ↦ by simp [rows, row]

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
    have hs := (hp.hasSum_evalAt (b := w) hw).smul_const (b n)
    rw [show (g ^ n).evalAt w = (g.evalAt w) ^ n by
      simpa using (IsRestricted.evalAtHom R hw).map_pow ⟨g, hg⟩ n] at hs
    exact hs.congr_fun fun k ↦ by rw [smul_eq_mul, mul_comm, mul_smul]
  rw [(((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hF.hasSum).prod_fiberwise hcol).tsum_eq]
  exact hF.hasSum.prod_fiberwise fun k ↦ (hasSum_compNullSeq_apply S hg hgn b k).const_smul (w ^ k)

/-- **Evaluation of a pulled-back null sequence.** When `R` is complete, for every `w : R` with
`‖w‖ ≤ 1`, `∑' k, w ^ k • compNullSeq S hg hgn b k = ∑' n, (g.evalAt w) ^ n • b n`. -/
theorem tsum_pow_smul_compNullSeq (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    ∑' k, w ^ k • compNullSeq S hg hgn b k = ∑' n, (g.evalAt w) ^ n • b n :=
  (hasSum_pow_smul_compNullSeq S hg hgn b hw).tsum_eq

end CommRing

end PowerSeries
