/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Substitution of a restricted power series into a vector-valued null sequence

Let `R` be an ultrametric normed commutative ring and `E` a complete ultrametric normed
`R`-module. A sequence `b ∈ C₀(ℕ, E)` is the coefficient vector of the convergent series
`z ↦ ∑' n, z ^ n • b n` on the closed unit disc `‖z‖ ≤ 1` of `R`. Given a scalar power series
`g ∈ R⟦X⟧` restricted at the radius `1` whose coefficients satisfy `‖coeff k g‖ ≤ 1` for all `k`,
substituting `z = g(w)` re-expands `∑' n, g(w) ^ n • b n` in powers of `w`:

```text
c_k = ∑' n, coeff k (g ^ n) • b n,    ∑' k, w ^ k • c_k = ∑' n, (g.evalAt w) ^ n • b n  (‖w‖ ≤ 1).
```

Because `R` is ultrametric, every positive power `g ^ n` again has coefficients of norm at most
`1` and is restricted at `1`. At `n = 0` the series `g ^ 0 = 1` acts on `b 0` by `1 • b 0 = b 0`,
so neither `NormOneClass R` nor nontriviality of `R` is needed. The re-expanded coefficients form
a continuous linear operator `PowerSeries.IsRestricted.compNullSeq` of norm at most `1` on
`C₀(ℕ, E)`, linear over every scalar semiring `S` commuting with the `R`-action on `E`. When `g`
has zero constant coefficient, `c_0 = b 0` and every higher coefficient `c_k` (`k ≠ 0`) depends
only on `b n` for `n ≠ 0`.

## Main definitions

* `PowerSeries.IsRestricted.compNullSeq`: the pullback `C₀(ℕ, E) →L[S] C₀(ℕ, E)` sending `b` to
  `k ↦ ∑' n, coeff k (g ^ n) • b n`.

## Main results

* `PowerSeries.norm_coeff_pow_le_one`: over an ultrametric normed commutative ring, positive powers
  of a series with coefficients in the closed unit ball retain coefficients in the closed unit ball.
* `PowerSeries.IsRestricted.compNullSeq_apply`: coefficient formula for `compNullSeq`.
* `PowerSeries.IsRestricted.norm_compNullSeq_le`,
  `PowerSeries.IsRestricted.opNorm_compNullSeq_le_one`: `compNullSeq` does not increase the sup
  norm and has operator norm at most `1`.
* `PowerSeries.IsRestricted.compNullSeq_apply_zero_of_constantCoeff_eq_zero`: when
  `constantCoeff g = 0`, the constant term is `b 0`.
* `PowerSeries.IsRestricted.norm_compNullSeq_apply_le_of_ne_zero`: every positive-degree
  coefficient is bounded by any nonnegative bound on `b n` for `n ≠ 0`.
* `PowerSeries.IsRestricted.hasSum_pow_smul_compNullSeq`,
  `PowerSeries.IsRestricted.tsum_pow_smul_compNullSeq`: when `R` is complete, evaluating the
  pulled-back series at any `w` with `‖w‖ ≤ 1` gives `∑' n, (g.evalAt w) ^ n • b n`.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace PowerSeries

/-- Over an ultrametric normed commutative ring, every positive power of a power series whose
coefficients have norm at most `1` also has coefficients of norm at most `1`. -/
theorem norm_coeff_pow_le_one {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {g : R⟦X⟧}
    (hgn : ∀ k, ‖coeff k g‖ ≤ 1) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    ‖coeff k (g ^ n)‖ ≤ 1 := by
  induction n generalizing k with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simpa using hgn k
    · rw [pow_succ, coeff_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ ↦ ?_
      exact (norm_mul_le _ _).trans <|
        (mul_le_mul (ih hn0 p.1) (hgn p.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

namespace IsRestricted

section Operator

variable {R E : Type*} [NormedCommRing R] [IsUltrametricDist R]
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

private theorem tendsto_coeff_pow_atTop (hg : g.IsRestricted 1) (n : ℕ) :
    Tendsto (fun k ↦ coeff k (g ^ n)) atTop (𝓝 0) := by
  have hp : (g ^ n).IsRestricted 1 := (IsRestricted.subring (R := R) 1).pow_mem hg n
  simpa [tendsto_zero_iff_norm_tendsto_zero] using (isRestricted_iff' 1 (g ^ n)).mp hp

private noncomputable def compNullSeqCoeff (g : R⟦X⟧) (b : C₀(ℕ, E)) (k : ℕ) : E :=
  ∑' n, coeff k (g ^ n) • b n

variable [IsUltrametricDist E]

private theorem norm_compNullSeqCoeff_le (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E)) (k : ℕ) :
    ‖compNullSeqCoeff g b k‖ ≤ ‖b‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg b) fun n ↦
    (norm_coeff_pow_smul_le hgn (b n) n k).trans (b.norm_coe_le_norm n)

private theorem tendsto_compNullSeqCoeff (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) : Tendsto (compNullSeqCoeff g b) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  have hb : Tendsto b atTop (𝓝 0) := by simpa [Nat.cofinite_eq_atTop] using b.tendsto_cofinite
  obtain ⟨N, hN⟩ := eventually_atTop.mp (NormedAddGroup.tendsto_nhds_zero.mp hb (ε / 2)
    (half_pos hε))
  have hhead : ∀ n ∈ Finset.range N,
      ∀ᶠ k in atTop, ‖coeff k (g ^ n) • b n‖ < ε / 2 := fun n _ ↦ by
    have h0 : Tendsto (fun k ↦ coeff k (g ^ n) • b n) atTop (𝓝 0) := by
      simpa using (tendsto_coeff_pow_atTop hg n).smul_const (b n)
    exact NormedAddGroup.tendsto_nhds_zero.mp h0 (ε / 2) (half_pos hε)
  filter_upwards [(Finset.range N).eventually_all.mpr hhead] with k hk
  refine (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le
    fun n ↦ ?_).trans_lt (half_lt_self hε)
  rcases lt_or_ge n N with hn | hn
  · exact (hk n (Finset.mem_range.mpr hn)).le
  · exact (norm_coeff_pow_smul_le hgn (b n) n k).trans (hN n hn).le

variable [CompleteSpace E]

private theorem summable_coeff_pow_smul (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E)) (k : ℕ) :
    Summable fun n ↦ coeff k (g ^ n) • b n :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    squeeze_zero_norm (fun n ↦ norm_coeff_pow_smul_le hgn (b n) n k)
      (tendsto_zero_iff_norm_tendsto_zero.mp b.tendsto_cofinite)

/-- **Pullback of a null sequence along a restricted series.** For `g : R⟦X⟧` restricted at `1`
with `‖coeff k g‖ ≤ 1`, `compNullSeq` sends `b ∈ C₀(ℕ, E)` to `k ↦ ∑' n, coeff k (g ^ n) • b n`,
the coefficient sequence of `w ↦ ∑' n, (g.evalAt w) ^ n • b n`. It is linear over any scalar
semiring `S` commuting with the `R`-action on `E` and has operator norm at most `1`. -/
noncomputable def compNullSeq (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) :
    C₀(ℕ, E) →L[S] C₀(ℕ, E) :=
  let L : C₀(ℕ, E) →ₗ[S] C₀(ℕ, E) :=
    { toFun b := ZeroAtInftyContinuousMap.mkOfDiscrete (compNullSeqCoeff g b)
        (tendsto_compNullSeqCoeff hg hgn b)
      map_add' b c := by
        ext k
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, compNullSeqCoeff,
          FunLike.coe_add, Pi.add_apply, smul_add]
        exact (summable_coeff_pow_smul hgn b k).tsum_add (summable_coeff_pow_smul hgn c k)
      map_smul' s b := by
        ext k
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, compNullSeqCoeff,
          FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_comm _ s]
        exact (summable_coeff_pow_smul hgn b k).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun b ↦ by
      rw [one_mul]
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg b)).mpr fun k ↦ ?_
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk,
        ZeroAtInftyContinuousMap.coe_mkOfDiscrete] using norm_compNullSeqCoeff_le hgn b k }

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

private theorem coe_compNullSeq (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) : ⇑(compNullSeq S hg hgn b) = compNullSeqCoeff g b :=
  ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _

/-- The `k`-th entry of `compNullSeq` is `∑' n, coeff k (g ^ n) • b n`. -/
theorem compNullSeq_apply (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E))
    (k : ℕ) : compNullSeq S hg hgn b k = ∑' n, coeff k (g ^ n) • b n := by
  rw [coe_compNullSeq]
  rfl

/-- Pulling back a null sequence along a unit-ball restricted series does not increase its norm. -/
theorem norm_compNullSeq_le (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1) (b : C₀(ℕ, E)) :
    ‖compNullSeq S hg hgn b‖ ≤ ‖b‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg b)).mpr fun k ↦
    compNullSeq_apply S hg hgn b k ▸ norm_compNullSeqCoeff_le hgn b k

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
in `k` for each fixed `n`, so the uncurried family is summable. -/
private theorem summable_uncurry_pow_smul (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    Summable (Function.uncurry fun k n ↦ w ^ k • (coeff k (g ^ n) • b n)) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ eventually_cofinite.mpr ?_
  have hA : {n : ℕ | ¬‖b n‖ < ε}.Finite :=
    eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp b.tendsto_cofinite ε hε)
  have hB (n : ℕ) : {k : ℕ | ¬‖w ^ k • (coeff k (g ^ n) • b n)‖ < ε}.Finite := by
    have hp : (g ^ n).IsRestricted 1 := (IsRestricted.subring (R := R) 1).pow_mem hg n
    have h0 : Tendsto (fun k ↦ (coeff k (g ^ n) • w ^ k) • b n) cofinite (𝓝 0) := by
      simpa using (hp.tendsto_smul_pow hw).smul_const (b n)
    have hlim : Tendsto (fun k ↦ w ^ k • (coeff k (g ^ n) • b n)) cofinite (𝓝 0) :=
      h0.congr fun k ↦ by rw [smul_eq_mul, mul_comm, mul_smul]
    exact eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp hlim ε hε)
  refine ((hA.biUnion fun n _ ↦ hB n).prod hA).subset fun p hp ↦ ?_
  have hp2 : p.2 ∈ {n : ℕ | ¬‖b n‖ < ε} := fun h ↦
    hp ((norm_pow_smul_coeff_pow_smul_le hgn hw (b p.2) p.1 p.2).trans_lt h)
  exact ⟨Set.mem_biUnion hp2 hp, hp2⟩

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
      HasSum (fun n ↦ w ^ k • (coeff k (g ^ n) • b n)) (w ^ k • compNullSeq S hg hgn b k) := by
    rw [compNullSeq_apply]
    exact (summable_coeff_pow_smul hgn b k).hasSum.const_smul (w ^ k)
  have hsum_n : Summable fun n ↦ (g.evalAt w) ^ n • b n :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
      squeeze_zero_norm
        (fun n ↦ by
          rw [← (hcol n).tsum_eq]
          exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg (b n))
            fun k ↦ norm_pow_smul_coeff_pow_smul_le hgn hw (b n) k n)
        (tendsto_zero_iff_norm_tendsto_zero.mp b.tendsto_cofinite)
  have htot : HasSum (Function.uncurry fun k n ↦ w ^ k • (coeff k (g ^ n) • b n))
      (∑' n, (g.evalAt w) ^ n • b n) :=
    (((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hF.hasSum).prod_fiberwise hcol).unique hsum_n.hasSum ▸
      hF.hasSum
  exact htot.prod_fiberwise hrow

/-- **Evaluation of a pulled-back null sequence.** When `R` is complete, for every `w : R` with
`‖w‖ ≤ 1`, `∑' k, w ^ k • compNullSeq S hg hgn b k = ∑' n, (g.evalAt w) ^ n • b n`. -/
theorem tsum_pow_smul_compNullSeq (hg : g.IsRestricted 1) (hgn : ∀ k, ‖coeff k g‖ ≤ 1)
    (b : C₀(ℕ, E)) {w : R} (hw : ‖w‖ ≤ 1) :
    ∑' k, w ^ k • compNullSeq S hg hgn b k = ∑' n, (g.evalAt w) ^ n • b n :=
  (hasSum_pow_smul_compNullSeq S hg hgn b hw).tsum_eq

end Eval

end IsRestricted

end PowerSeries
