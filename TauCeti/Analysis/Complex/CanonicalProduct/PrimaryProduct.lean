/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Complex.InfiniteProd
import TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn
import TauCeti.Topology.Algebra.InfiniteSum.Real
import TauCeti.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Weierstrass canonical products of arbitrary genus and entire factorization

Given an arbitrary index family `a : ι → ℂ` (possibly repeated according to multiplicity) and
genera `p : ι → ℕ` such that `∑' i, (R / ‖a i‖) ^ (p i + 1) < ∞` for every `R > 0`, the unordered
primary product `∏' i, Complex.weierstrassFactor (p i) (z / a i)` converges uniformly on compact
sets and locally uniformly on `ℂ` to an entire function normalized to `1` at `0`. With total
division `z / 0 = 0`, indices with `a i = 0` contribute the unit factor `1`, so its zeros are
precisely the nonzero values `a i`, and at every `z : ℂ` its analytic order of vanishing equals
`{i | a i ≠ 0 ∧ a i = z}.ncard`; both `‖a i‖ → ∞` along `Filter.cofinite` (when `∀ i, a i ≠ 0`)
and finiteness of each active fiber follow automatically from the summability hypothesis, with no
countability assumption on `ι`.

Reindexing by an equivalence `κ ≃ ι` and grouping finite multiplicity fibers `m : ι → ℕ` under
`∑' i, m i * (R / ‖a i‖) ^ (p i + 1) < ∞` preserve the product and its compact-uniform convergence
(via `HasProdUniformlyOn.sigma_of_finite`, whence locally uniform convergence follows by
`hasProdLocallyUniformlyOn_of_forall_compact`).

Combining variable-genus products with `Filter.Tendsto.exists_summable_mul_div_pow` and
`Differentiable.exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq` yields Weierstrass's
general factorization theorem: every nonzero entire function `f : ℂ → ℂ` admits admissible genera
`p` on its set of nonzero zeros and an entire function `g` (unique up to `2πiℤ`) such that
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`,
without any growth hypothesis on `f`.

## Main results

* `Complex.tendsto_norm_cofinite_atTop_of_summable_div_pow`: summability of
  `(R / ‖a i‖) ^ (p i + 1)` for all `R > 0` (with `a i ≠ 0`) forces `‖a i‖ → ∞` along
  `Filter.cofinite`.
* `Complex.hasProdUniformlyOn_weierstrassFactor_div`,
  `Complex.hasProdLocallyUniformlyOn_weierstrassFactor_div`,
  `Complex.differentiable_tprod_weierstrassFactor_div`: compact-uniform and locally uniform
  convergence and entirety of `∏' i, weierstrassFactor (p i) (z / a i)`.
* `Complex.analyticOrderAt_tprod_weierstrassFactor_div`,
  `Complex.divisor_tprod_weierstrassFactor_div`: exact zero-order and whole-plane divisor formulas
  in terms of active fiber cardinalities `{i | a i ≠ 0 ∧ a i = z}.ncard`.
* `Complex.hasProdUniformlyOn_weierstrassFactor_div_pow`,
  `Complex.hasProdLocallyUniformlyOn_weierstrassFactor_div_pow`,
  `Complex.analyticOrderAt_tprod_weierstrassFactor_div_pow_of_injective`,
  `Complex.divisor_tprod_weierstrassFactor_div_pow`: grouped finite multiplicity fibers.
* `Differentiable.analyticOrderAt_pow_mul_tprod_weierstrassFactor_div_pow`: exact analytic-order
  comparison between a nonzero entire function and its origin-plus-zero-subtype Weierstrass product.
* `Differentiable.exists_eq_pow_mul_exp_mul_tprod_weierstrassFactor_div_pow_of_summable`:
  exponential factorization of an entire function against any admissible genus assignment `p`.
* `Differentiable.exists_eq_pow_mul_exp_mul_tprod_weierstrassFactor_div_pow`: Weierstrass's entire
  factorization theorem for an arbitrary nonzero entire function without growth hypotheses.

## Provenance

* Compact-uniform convergence, zero characterization, and root-fiber finiteness build on
  `HasSumUniformlyOn.of_norm_le_summable_eventually` (Mathlib) together with
  `SummableUniformlyOn.hasProdUniformlyOn_one_add_of_isCompact`,
  `SummableUniformlyOn.tprod_one_add_eq_zero_iff`, and
  `SummableUniformlyOn.finite_setOf_exists_mem_one_add_eq_zero` in
  `TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn`, plus
  `hasProdLocallyUniformlyOn_of_forall_compact` (Mathlib).
* Holomorphy and order additivity of the primary product are supplied by
  `TauCeti.differentiableOn_tprod_one_add` and `TauCeti.analyticOrderAt_tprod_one_add` in
  `TauCeti.Analysis.Complex.InfiniteProd`, with whole-plane divisor translation via
  `Differentiable.divisor_univ_eq_analyticOrderNatAt` in
  `TauCeti.Analysis.Complex.DivisorFactorization`.
* The weighted sigma-fiber construction and multiplicity proofs generalize the genus-one
  formalization in `TauCeti.Analysis.Complex.CanonicalProduct.Convergence` using
  `TauCeti.summable_sigma_fin_iff` (`TauCeti.Topology.Algebra.InfiniteSum.Real`) and
  `HasProdUniformlyOn.sigma_of_finite` (`TauCeti.Topology.Algebra.InfiniteSum.UniformOn`).
* Weierstrass's general entire factorization combines these products with
  `AnalyticOnNhd.finite_setOf_mem_and_eq_zero_of_isCompact`
  (`TauCeti.Analysis.Analytic.IsolatedZeros`), `Filter.Tendsto.exists_summable_mul_div_pow`
  (`TauCeti.Topology.Algebra.InfiniteSum.Real`), and
  `Differentiable.exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq`
  (`TauCeti.Analysis.Complex.DivisorFactorization`).

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorems 15.9 and 15.10.
* Z. Yun, W. Zhang, *Shtukas and the Taylor expansion of L-functions*, *Ann. of Math.* (2) **186**
  (2017), no. 3, 767–911, Appendix B.1 (fixed-genus Hadamard canonical products).
-/

public section

open Complex Filter Function Metric Set Topology
open scoped BigOperators

namespace Complex

private theorem divisor_univ_eq_of_analyticOrderAt_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} {n : ℕ} (hord : analyticOrderAt f z = n) :
    MeromorphicOn.divisor f Set.univ z = (n : ℤ) := by
  rw [hf.divisor_univ_eq_analyticOrderNatAt z, analyticOrderNatAt, hord, ENat.toNat_natCast]

section Unweighted

variable {ι : Type*} {a : ι → ℂ} {p : ι → ℕ}

/-- Summability of `(R / ‖a i‖) ^ (p i + 1)` for all `R > 0` (with `a i ≠ 0`) forces `‖a i‖ → ∞`
along the cofinite filter; finite and empty index types satisfy this vacuously. -/
theorem tendsto_norm_cofinite_atTop_of_summable_div_pow (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    Tendsto (fun i ↦ ‖a i‖) cofinite atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  let R : ℝ := max B 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  filter_upwards [(hsum R hR).tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)]
    with i hi
  by_contra! hlt
  have ha_pos : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
  have h1 : 1 ≤ R / ‖a i‖ :=
    (one_le_div ha_pos).mpr (hlt.le.trans (le_max_left B 1))
  exact lt_irrefl (1 : ℝ) ((one_le_pow₀ h1).trans_lt hi)

private theorem summableUniformlyOn_norm_weierstrassFactor_div_sub_one
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    SummableUniformlyOn (fun i z ↦ ‖weierstrassFactor (p i) (z / a i) - 1‖) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  refine (HasSumUniformlyOn.of_norm_le_summable_eventually (hsum R hR) ?_).summableUniformlyOn
  filter_upwards [(hsum R hR).tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)]
    with i hi z hz
  rw [norm_norm]
  by_cases hai : a i = 0
  · simp [hai]
  · have hzR : ‖z‖ ≤ R := (hM z hz).trans (le_max_left M 1)
    have ha_pos : 0 < ‖a i‖ := norm_pos_iff.mpr hai
    have hRle : R / ‖a i‖ ≤ 1 := by
      by_contra! hgt
      exact lt_irrefl (1 : ℝ) ((one_le_pow₀ hgt.le).trans_lt hi)
    have hquot_le : ‖z / a i‖ ≤ R / ‖a i‖ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_right hzR ha_pos.le
    exact (norm_weierstrassFactor_sub_one_le (p i) (hquot_le.trans hRle)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hquot_le _)

/-- On every compact set `K ⊆ ℂ`, the variable-genus primary product
`∏' i, weierstrassFactor (p i) (z / a i)` converges uniformly. -/
theorem hasProdUniformlyOn_weierstrassFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor (p i) (z / a i))
      (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i)) K := by
  have htail := summableUniformlyOn_norm_weierstrassFactor_div_sub_one hsum hK
  have hcts : ∀ i, ContinuousOn (fun z ↦ weierstrassFactor (p i) (z / a i) - 1) K := fun i ↦
    (by fun_prop :
      Differentiable ℂ fun z ↦ weierstrassFactor (p i) (z / a i) - 1).continuous.continuousOn
  simpa only [add_sub_cancel] using htail.hasProdUniformlyOn_one_add_of_isCompact hK hcts

/-- The variable-genus primary product converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor (p i) (z / a i))
      (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i)) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_weierstrassFactor_div hsum hK

/-- A variable-genus Weierstrass primary product is entire. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i)) := by
  rw [← differentiableOn_univ]
  have h := TauCeti.differentiableOn_tprod_one_add isOpen_univ
    (u := fun i z ↦ weierstrassFactor (p i) (z / a i) - 1) (fun i ↦ by fun_prop)
    (fun _ _ hK ↦ summableUniformlyOn_norm_weierstrassFactor_div_sub_one hsum hK)
  simpa only [add_sub_cancel] using h

/-- At each `z : ℂ`, the deviations `‖weierstrassFactor (p i) (z / a i) - 1‖` are summable. -/
theorem summable_norm_weierstrassFactor_div_sub_one
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    Summable fun i ↦ ‖weierstrassFactor (p i) (z / a i) - 1‖ :=
  (summableUniformlyOn_norm_weierstrassFactor_div_sub_one hsum isCompact_singleton).summable
    (mem_singleton z)

private theorem weierstrassFactor_div_eq_zero_iff (p : ℕ) (a z : ℂ) :
    weierstrassFactor p (z / a) = 0 ↔ a ≠ 0 ∧ a = z := by
  rw [weierstrassFactor_eq_zero_iff]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha, div_eq_one_iff_eq ha, eq_comm]

/-- The primary product vanishes at `z` if and only if `z` occurs as a nonzero value in the root
family `a`. -/
theorem tprod_weierstrassFactor_div_eq_zero_iff
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, weierstrassFactor (p i) (z / a i)) = 0 ↔ ∃ i, a i ≠ 0 ∧ a i = z := by
  have h := (summableUniformlyOn_norm_weierstrassFactor_div_sub_one hsum
    (isCompact_singleton (x := z))).tprod_one_add_eq_zero_iff (mem_singleton z)
  simp only [add_sub_cancel, weierstrassFactor_div_eq_zero_iff] at h
  exact h

/-- Each point `z : ℂ` occurs at most finitely many times as a nonzero value in the root family
`a`. -/
theorem finite_setOf_ne_zero_and_eq_of_summable_div_pow
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    {i | a i ≠ 0 ∧ a i = z}.Finite := by
  have hf := (summableUniformlyOn_norm_weierstrassFactor_div_sub_one hsum
    (isCompact_singleton (x := z))).finite_setOf_exists_mem_one_add_eq_zero
  refine hf.subset fun i hi ↦ ⟨z, mem_singleton z, ?_⟩
  simp only [add_sub_cancel, weierstrassFactor_div_eq_zero_iff]
  exact hi

/-- **Exact zero multiplicities of variable-genus primary products.** At every `z : ℂ`, the
analytic order of `∏' i, weierstrassFactor (p i) (w / a i)` equals
`{i | a i ≠ 0 ∧ a i = z}.ncard`. -/
theorem analyticOrderAt_tprod_weierstrassFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactor (p i) (w / a i)) z =
      ({i | a i ≠ 0 ∧ a i = z}.ncard : ℕ∞) := by
  have hord := TauCeti.analyticOrderAt_tprod_one_add isOpen_univ
    (u := fun i w ↦ weierstrassFactor (p i) (w / a i) - 1) (fun i ↦ by fun_prop)
    (fun _ _ hK ↦ summableUniformlyOn_norm_weierstrassFactor_div_sub_one hsum hK) (mem_univ z)
  simp only [add_sub_cancel] at hord
  rw [hord]
  let s : Set ι := {i | a i ≠ 0 ∧ a i = z}
  have hf : s.Finite := finite_setOf_ne_zero_and_eq_of_summable_div_pow hsum z
  have hcongr : (∑' i, analyticOrderAt (fun w ↦ weierstrassFactor (p i) (w / a i)) z) =
      ∑' i, s.indicator (fun _ ↦ (1 : ℕ∞)) i := by
    refine tsum_congr fun i ↦ ?_
    by_cases hai : a i = 0
    · simp [s, hai]
    · rw [analyticOrderAt_weierstrassFactor_div (p i) hai z]
      simp [s, hai, Set.indicator_apply, eq_comm]
  have : Fintype s := hf.fintype
  rw [hcongr, ← tsum_subtype, tsum_fintype]
  simp [s, Set.fintypeCard_eq_ncard]

/-- Whole-plane divisor of a variable-genus Weierstrass primary product. -/
theorem divisor_tprod_weierstrassFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' i, weierstrassFactor (p i) (w / a i)) Set.univ z =
      ({i | a i ≠ 0 ∧ a i = z}.ncard : ℤ) :=
  divisor_univ_eq_of_analyticOrderAt_eq (differentiable_tprod_weierstrassFactor_div hsum)
    (analyticOrderAt_tprod_weierstrassFactor_div hsum z)

end Unweighted

section Weighted

variable {ι : Type*} {a : ι → ℂ} {p m : ι → ℕ}

private theorem summable_sigma_div_pow (m : ι → ℕ)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    ∀ R : ℝ, 0 < R → Summable fun q : Σ i, Fin (m i) ↦ (R / ‖a q.1‖) ^ (p q.1 + 1) :=
  fun R hR ↦ (TauCeti.summable_sigma_fin_iff
    (fun i ↦ pow_nonneg (div_nonneg hR.le (norm_nonneg (a i))) _) m).mpr (hm R hR)

private theorem hasProdUniformlyOn_weierstrassFactor_div_pow_sigma
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' q : Σ i, Fin (m i), weierstrassFactor (p q.1) (z / a q.1)) K := by
  have h := (hasProdUniformlyOn_weierstrassFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (summable_sigma_div_pow m hm) hK).sigma_of_finite
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- Grouping finite multiplicity fibers `Fin (m i)` over `Σ i, Fin (m i)` preserves the value of
the primary product. -/
theorem tprod_weierstrassFactor_div_pow_eq_sigma
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, weierstrassFactor (p i) (z / a i) ^ m i) =
      ∏' q : Σ i, Fin (m i), weierstrassFactor (p q.1) (z / a q.1) :=
  ((hasProdUniformlyOn_weierstrassFactor_div_pow_sigma hm
    (isCompact_singleton (x := z))).hasProd (mem_singleton z)).tprod_eq

/-- Weighted primary products with natural multiplicities converge uniformly on compact sets. -/
theorem hasProdUniformlyOn_weierstrassFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i) ^ m i) K :=
  (hasProdUniformlyOn_weierstrassFactor_div_pow_sigma hm
    hK).multipliableUniformlyOn.hasProdUniformlyOn

/-- Weighted primary products with natural multiplicities converge locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i) ^ m i) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_weierstrassFactor_div_pow hm hK

/-- A weighted variable-genus primary product is entire. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i) ^ m i) := by
  have heq : (fun z ↦ ∏' i, weierstrassFactor (p i) (z / a i) ^ m i) =
      fun z ↦ ∏' q : Σ i, Fin (m i), weierstrassFactor (p q.1) (z / a q.1) :=
    funext (tprod_weierstrassFactor_div_pow_eq_sigma hm)
  rw [heq]
  exact differentiable_tprod_weierstrassFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (summable_sigma_div_pow m hm)

/-- A weighted primary product vanishes at `z` if and only if some nonzero root `a i = z` has
nonzero multiplicity `m i`. -/
theorem tprod_weierstrassFactor_div_pow_eq_zero_iff
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, weierstrassFactor (p i) (z / a i) ^ m i) = 0 ↔
      ∃ i, m i ≠ 0 ∧ a i ≠ 0 ∧ a i = z := by
  rw [tprod_weierstrassFactor_div_pow_eq_sigma hm,
    tprod_weierstrassFactor_div_eq_zero_iff (summable_sigma_div_pow m hm)]
  constructor
  · rintro ⟨⟨i, k⟩, hai, hi⟩
    exact ⟨i, Nat.ne_zero_of_lt k.isLt, hai, hi⟩
  · rintro ⟨i, hmi, hai, hi⟩
    exact ⟨⟨i, ⟨0, Nat.pos_of_ne_zero hmi⟩⟩, hai, hi⟩

/-- Analytic order of a weighted primary product in terms of its sigma multiplicity fiber. -/
theorem analyticOrderAt_tprod_weierstrassFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor (p j) (w / a j) ^ m j) z =
      ({q : Σ j, Fin (m j) | a q.1 ≠ 0 ∧ a q.1 = z}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' j, weierstrassFactor (p j) (w / a j) ^ m j) =
      fun w ↦ ∏' q : Σ j, Fin (m j), weierstrassFactor (p q.1) (w / a q.1) :=
    funext (tprod_weierstrassFactor_div_pow_eq_sigma hm)
  rw [heq]
  exact analyticOrderAt_tprod_weierstrassFactor_div (summable_sigma_div_pow m hm) z

/-- When `a` is injective and `a i ≠ 0` whenever `m i ≠ 0`, the analytic order of the weighted
primary product at `a i` is the prescribed multiplicity `m i`. -/
theorem analyticOrderAt_tprod_weierstrassFactor_div_pow_of_injective (i : ι)
    (ha : m i ≠ 0 → a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1))
    (hinj : Function.Injective a) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor (p j) (w / a j) ^ m j) (a i) = m i := by
  have hset : {q : Σ j, Fin (m j) | a q.1 ≠ 0 ∧ a q.1 = a i} = Set.range (Sigma.mk i) := by
    rw [Set.range_sigmaMk]
    ext ⟨j, k⟩
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ⟨_, hq⟩ ↦ hinj hq, fun hq ↦ ?_⟩
    subst hq
    exact ⟨ha (Nat.ne_zero_of_lt k.isLt), rfl⟩
  rw [analyticOrderAt_tprod_weierstrassFactor_div_pow hm (a i), hset,
    Set.ncard_range_of_injective sigma_mk_injective, Nat.card_fin]

/-- Outside the active roots (`∀ j, m j ≠ 0 → a j ≠ 0 → a j ≠ z`), a weighted primary product has
analytic order `0`. -/
theorem analyticOrderAt_tprod_weierstrassFactor_div_pow_eq_zero
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) {z : ℂ}
    (hz : ∀ j, m j ≠ 0 → a j ≠ 0 → a j ≠ z) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor (p j) (w / a j) ^ m j) z = 0 := by
  refine ((differentiable_tprod_weierstrassFactor_div_pow hm).analyticAt
    z).analyticOrderAt_eq_zero.mpr ?_
  rw [ne_eq, tprod_weierstrassFactor_div_pow_eq_zero_iff hm]
  rintro ⟨j, hmj, haj, hja⟩
  exact hz j hmj haj hja

/-- Whole-plane divisor of a weighted variable-genus primary product. -/
theorem divisor_tprod_weierstrassFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' j, weierstrassFactor (p j) (w / a j) ^ m j) Set.univ z =
      ({q : Σ j, Fin (m j) | a q.1 ≠ 0 ∧ a q.1 = z}.ncard : ℤ) :=
  divisor_univ_eq_of_analyticOrderAt_eq (differentiable_tprod_weierstrassFactor_div_pow hm)
    (analyticOrderAt_tprod_weierstrassFactor_div_pow hm z)

/-- When `a` is injective and `a i ≠ 0` whenever `m i ≠ 0`, the whole-plane divisor of the
weighted primary product at `a i` is the prescribed multiplicity `m i`. -/
theorem divisor_tprod_weierstrassFactor_div_pow_of_injective (i : ι)
    (ha : m i ≠ 0 → a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1))
    (hinj : Function.Injective a) :
    MeromorphicOn.divisor (fun w ↦ ∏' j, weierstrassFactor (p j) (w / a j) ^ m j) Set.univ (a i) =
      (m i : ℤ) :=
  divisor_univ_eq_of_analyticOrderAt_eq (differentiable_tprod_weierstrassFactor_div_pow hm)
    (analyticOrderAt_tprod_weierstrassFactor_div_pow_of_injective i ha hm hinj)

end Weighted

end Complex

namespace Differentiable

/-- For a nonzero entire function `f` and any admissible genus assignment `p`, the zero-subtype
weighted primary product with its origin factor `w ^ analyticOrderNatAt f 0` has the same
`analyticOrderAt` as `f` at every complex point `z`. -/
theorem analyticOrderAt_pow_mul_tprod_weierstrassFactor_div_pow {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) {p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ}
    (hm_sum : ∀ R : ℝ, 0 < R → Summable fun a : {a : ℂ // a ≠ 0 ∧ f a = 0} ↦
      (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ w ^ analyticOrderNatAt f 0 *
      ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
        weierstrassFactor (p a) (w / a) ^ analyticOrderNatAt f a) z =
      analyticOrderAt f z := by
  obtain ⟨z₀, hz₀⟩ := hf0
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  set m₀ := analyticOrderNatAt f 0
  let Z := {a : ℂ // a ≠ 0 ∧ f a = 0}
  let P : ℂ → ℂ := fun w ↦
    ∏' a : Z, weierstrassFactor (p a) (w / a) ^ analyticOrderNatAt f a
  have hP_diff : Differentiable ℂ P := differentiable_tprod_weierstrassFactor_div_pow hm_sum
  have hft_ne_top : analyticOrderAt f z ≠ ⊤ :=
    hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀) (mem_univ z)
      (by simp [(hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hz₀])
  have hF_split : analyticOrderAt (fun w ↦ w ^ m₀ * P w) z =
      analyticOrderAt (fun w : ℂ ↦ w ^ m₀) z + analyticOrderAt P z :=
    analyticOrderAt_mul (analyticAt_id.pow m₀) (hP_diff.analyticAt z)
  rw [hF_split, ← Nat.cast_analyticOrderNatAt hft_ne_top]
  by_cases hz : z = 0
  · subst z
    have hpow0 : analyticOrderAt (fun w : ℂ ↦ w ^ m₀) 0 = m₀ := by
      have heq : (fun w : ℂ ↦ w ^ m₀) = (· - (0 : ℂ)) ^ m₀ := by ext w; simp
      rw [heq]
      exact analyticOrderAt_centeredMonomial
    rw [hpow0, (hP_diff.analyticAt 0).analyticOrderAt_eq_zero.mpr (by simp [P]), add_zero]
  · have hpow_z : analyticOrderAt (fun w : ℂ ↦ w ^ m₀) z = 0 :=
      (analyticAt_id.pow m₀).analyticOrderAt_eq_zero.mpr (pow_ne_zero m₀ hz)
    rw [hpow_z, zero_add]
    by_cases hfz : f z = 0
    · let a₀ : Z := ⟨z, hz, hfz⟩
      simpa [P, a₀] using analyticOrderAt_tprod_weierstrassFactor_div_pow_of_injective a₀
        (fun _ ↦ a₀.property.1) hm_sum Subtype.val_injective
    · have hPz : analyticOrderAt P z = 0 :=
        analyticOrderAt_tprod_weierstrassFactor_div_pow_eq_zero hm_sum
          fun a _ _ ha ↦ hfz (ha ▸ a.property.2)
      rw [hPz, analyticOrderNatAt, (hf.analyticAt z).analyticOrderAt_eq_zero.mpr hfz,
        ENat.toNat_zero, Nat.cast_zero]

/-- Given a nonzero entire function `f` and any admissible genus assignment
`p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ` whose weighted primary product converges, there exists an
entire function `g` (unique up to `2 * π * I * ℤ`) such that
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`
for all `z : ℂ`. -/
theorem exists_eq_pow_mul_exp_mul_tprod_weierstrassFactor_div_pow_of_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) {p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ}
    (hm_sum : ∀ R : ℝ, 0 < R → Summable fun a : {a : ℂ // a ≠ 0 ∧ f a = 0} ↦
      (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g z) *
        ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' →
        (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g' z) *
          ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
            weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  let F : ℂ → ℂ := fun z ↦ z ^ analyticOrderNatAt f 0 *
    ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
      weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a
  have hF_diff : Differentiable ℂ F :=
    (differentiable_id.pow _).mul (differentiable_tprod_weierstrassFactor_div_pow hm_sum)
  obtain ⟨g, hg, hfg, huniq⟩ :=
    hf.exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq hF_diff hf0
      fun z ↦ (hf.analyticOrderAt_pow_mul_tprod_weierstrassFactor_div_pow hf0 hm_sum z).symm
  refine ⟨g, hg, fun z ↦ ?_, fun g' hg' hfg' ↦ huniq g' hg' fun z ↦ ?_⟩
  · simpa only [F, mul_left_comm (Complex.exp (g z)), mul_assoc] using hfg z
  · simpa only [F, mul_left_comm (Complex.exp (g' z)), mul_assoc] using hfg' z

/-- **Weierstrass's entire factorization theorem** (Rudin, Theorem 15.10). Every entire function
`f : ℂ → ℂ` that is not identically zero admits admissible genera
`p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ` and an entire function `g : ℂ → ℂ` (unique up to `2πiℤ`)
such that the weighted primary product over its nonzero zeros converges locally uniformly on `ℂ`
and
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`
for all `z : ℂ`, with no growth hypothesis on `f`. -/
theorem exists_eq_pow_mul_exp_mul_tprod_weierstrassFactor_div_pow {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) :
    ∃ (p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ) (g : ℂ → ℂ),
      (∀ R : ℝ, 0 < R → Summable fun a : {a : ℂ // a ≠ 0 ∧ f a = 0} ↦
        (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1)) ∧
      HasProdLocallyUniformlyOn
        (fun (a : {a : ℂ // a ≠ 0 ∧ f a = 0}) z ↦
          weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a)
        (fun z ↦ ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a) Set.univ ∧
      Differentiable ℂ g ∧
      (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g z) *
        ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' →
        (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g' z) *
          ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
            weierstrassFactor (p a) (z / a) ^ analyticOrderNatAt f a) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  obtain ⟨z₀, hz₀⟩ := hf0
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  have hnorm_atTop :
      Tendsto (fun a : {a : ℂ // a ≠ 0 ∧ f a = 0} ↦ ‖(a : ℂ)‖) cofinite atTop := by
    rw [Filter.tendsto_atTop]
    intro R
    have hfin : {a : {a : ℂ // a ≠ 0 ∧ f a = 0} | ‖(a : ℂ)‖ ≤ R}.Finite := by
      refine (Set.finite_image_iff Subtype.val_injective.injOn).mp ?_
      exact (hfa.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (mem_univ z₀) hz₀
        (isCompact_closedBall 0 R) (subset_univ _)).subset fun w ⟨a, haR, hwa⟩ ↦
          ⟨mem_closedBall_zero_iff.mpr (hwa ▸ haR), hwa ▸ a.property.2⟩
    have hlt : ∀ᶠ a : {a : ℂ // a ≠ 0 ∧ f a = 0} in cofinite, R < ‖(a : ℂ)‖ := by
      simpa only [eventually_cofinite, not_lt] using hfin
    exact hlt.mono fun _ h ↦ h.le
  obtain ⟨p, hm_sum⟩ := hnorm_atTop.exists_summable_mul_div_pow fun a ↦ analyticOrderNatAt f a
  obtain ⟨g, hg, hfg, huniq⟩ :=
    hf.exists_eq_pow_mul_exp_mul_tprod_weierstrassFactor_div_pow_of_summable ⟨z₀, hz₀⟩ hm_sum
  exact ⟨p, g, hm_sum, hasProdLocallyUniformlyOn_weierstrassFactor_div_pow hm_sum, hg, hfg, huniq⟩

end Differentiable

/-! ### Examples -/

/-- Two genus-zero factors at the same root `a = 1` multiply to `(1 - z) ^ 2` and produce
analytic order `2` at `1` (the fiber cardinality of `Fin 2`, rather than the cardinality `1` of
the distinct support). -/
example :
    (∀ z : ℂ, (∏' _i : Fin 2, weierstrassFactor 0 (z / 1)) = (1 - z) ^ 2) ∧
      analyticOrderAt (fun z : ℂ ↦ ∏' _i : Fin 2, weierstrassFactor 0 (z / 1)) 1 = 2 := by
  have hsum : ∀ R : ℝ, 0 < R → Summable fun _i : Fin 2 ↦ (R / ‖(1 : ℂ)‖) ^ (0 + 1) :=
    fun _ _ ↦ Summable.of_finite
  refine ⟨fun z ↦ ?_, ?_⟩
  · rw [tprod_fintype]
    simp [sq]
  · simpa using analyticOrderAt_tprod_weierstrassFactor_div hsum 1
