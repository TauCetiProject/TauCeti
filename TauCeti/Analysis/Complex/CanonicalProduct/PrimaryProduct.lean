/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import TauCeti.Analysis.Complex.CanonicalProduct.WeierstrassFactor
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Complex.InfiniteProduct
import TauCeti.Analysis.Normed.Module.MultipliableUniformlyOn
import TauCeti.Topology.Algebra.InfiniteSum.Real
import TauCeti.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Weierstrass canonical products of arbitrary genus and entire factorization

Given an arbitrary index family `a : ι → ℂ` (possibly repeated according to multiplicity) and
genera `p : ι → ℕ` such that `∑' i, (R / ‖a i‖) ^ (p i + 1) < ∞` for every `R > 0`, the unordered
primary product `∏' i, Complex.elementaryFactor (p i) (z / a i)` converges uniformly on compact
sets and locally uniformly on `ℂ` to an entire function normalized to `1` at `0`. When every
`a i ≠ 0`, its zeros are precisely the values `a i`, and at every `z : ℂ` its analytic order of
vanishing equals `{i | a i = z}.ncard`; both `‖a i‖ → ∞` along `Filter.cofinite` and finiteness of
each fiber follow automatically from the summability hypothesis, with no countability assumption on
`ι`.

Reindexing by an equivalence `κ ≃ ι` and grouping finite multiplicity fibers `m : ι → ℕ` under
`∑' i, m i * (R / ‖a i‖) ^ (p i + 1) < ∞` preserve the product and its locally uniform
convergence (via `Equiv.hasProdLocallyUniformlyOn_iff` and
`HasProdLocallyUniformlyOn.sigma_of_finite`). The weighted sigma-fiber construction and
multiplicity proofs generalize the genus-one formalization in
`TauCeti.Analysis.Complex.CanonicalProduct.Convergence`.

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
* `Complex.hasProdUniformlyOn_elementaryFactor_div`,
  `Complex.hasProdLocallyUniformlyOn_elementaryFactor_div`,
  `Complex.differentiable_tprod_elementaryFactor_div`: compact-uniform and locally uniform
  convergence and entirety of `∏' i, elementaryFactor (p i) (z / a i)`.
* `Complex.analyticOrderAt_tprod_elementaryFactor_div`,
  `Complex.divisor_tprod_elementaryFactor_div`: exact zero-order and whole-plane divisor formulas
  in terms of fiber cardinalities `{i | a i = z}.ncard`.
* `Complex.hasProdLocallyUniformlyOn_elementaryFactor_div_comp_equiv`,
  `Complex.hasProdUniformlyOn_elementaryFactor_div_pow`,
  `Complex.hasProdLocallyUniformlyOn_elementaryFactor_div_pow`,
  `Complex.analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective`,
  `Complex.divisor_tprod_elementaryFactor_div_pow_eq_zero`: invariance under equivalences and
  grouped finite multiplicity fibers.
* `Differentiable.exists_eq_pow_mul_exp_mul_tprod_elementaryFactor_div_pow_of_summable`:
  exponential factorization of an entire function against any admissible genus assignment `p`.
* `Differentiable.exists_eq_pow_mul_exp_mul_tprod_elementaryFactor_div_pow`: Weierstrass's entire
  factorization theorem for an arbitrary nonzero entire function without growth hypotheses.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorems 15.9 and 15.10.
* Z. Yun, W. Zhang, *Shtukas and the Taylor expansion of L-functions*, *Ann. of Math.* (2) **186**
  (2017), no. 3, 767–911, Appendix B.1 (fixed-genus Hadamard canonical products).
-/

public section

open Complex Filter Function Metric Set Topology
open scoped BigOperators

namespace Complex

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

private theorem exists_summable_cofinite_elementaryFactor_div_sub_one
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    ∀ K ⊆ (Set.univ : Set ℂ), IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖elementaryFactor (p i) (z / a i) - 1‖ ≤ v i := by
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  refine ⟨fun i ↦ (R / ‖a i‖) ^ (p i + 1), hsum R hR, ?_⟩
  filter_upwards [(hsum R hR).tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)]
    with i hi z hz
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
    exact (norm_elementaryFactor_sub_one_le (p i) (hquot_le.trans hRle)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hquot_le _)

/-- On every compact set `K ⊆ ℂ`, the variable-genus primary product
`∏' i, elementaryFactor (p i) (z / a i)` converges uniformly. -/
theorem hasProdUniformlyOn_elementaryFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i))
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) K := by
  obtain ⟨v, hv, hbound⟩ :=
    exists_summable_cofinite_elementaryFactor_div_sub_one hsum K (subset_univ K) hK
  have hcts : ∀ i, ContinuousOn (fun z ↦ elementaryFactor (p i) (z / a i) - 1) K := fun i ↦
    (by fun_prop :
      Differentiable ℂ fun z ↦ elementaryFactor (p i) (z / a i) - 1).continuous.continuousOn
  simpa only [add_sub_cancel] using hv.hasProdUniformlyOn_one_add hK hbound hcts

/-- The variable-genus primary product converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_elementaryFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i))
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_elementaryFactor_div hsum hK

/-- Reindexing by an equivalence preserves locally uniform convergence of the primary product to
the same limit function on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_elementaryFactor_div_comp_equiv {κ : Type*} (e : κ ≃ ι)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun k z ↦ elementaryFactor (p (e k)) (z / a (e k)))
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) Set.univ :=
  e.hasProdLocallyUniformlyOn_iff.mpr (hasProdLocallyUniformlyOn_elementaryFactor_div hsum)

/-- A variable-genus Weierstrass primary product is entire. -/
@[fun_prop]
theorem differentiable_tprod_elementaryFactor_div
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    Differentiable ℂ (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) := by
  rw [← differentiableOn_univ]
  have h := TauCeti.differentiableOn_tprod_one_add isOpen_univ
    (u := fun i z ↦ elementaryFactor (p i) (z / a i) - 1) (fun i ↦ by fun_prop)
    (exists_summable_cofinite_elementaryFactor_div_sub_one hsum)
  simpa only [add_sub_cancel] using h

/-- At each `z : ℂ`, the deviations `‖elementaryFactor (p i) (z / a i) - 1‖` are summable. -/
theorem summable_norm_elementaryFactor_div_sub_one
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    Summable fun i ↦ ‖elementaryFactor (p i) (z / a i) - 1‖ :=
  TauCeti.summable_norm_of_forall_compact
    (exists_summable_cofinite_elementaryFactor_div_sub_one hsum) (mem_univ z)

/-- The primary product vanishes at `z` if and only if `z` occurs in the root family `a`. -/
theorem tprod_elementaryFactor_div_eq_zero_iff (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, elementaryFactor (p i) (z / a i)) = 0 ↔ ∃ i, a i = z := by
  have h := TauCeti.tprod_one_add_eq_zero_iff
    (exists_summable_cofinite_elementaryFactor_div_sub_one hsum) (mem_univ z)
  simp only [add_sub_cancel, elementaryFactor_eq_zero_iff] at h
  refine h.trans (exists_congr fun i ↦ ?_)
  rw [div_eq_one_iff_eq (ha i), eq_comm]

/-- Each point `z : ℂ` occurs at most finitely many times in the root family `a`. -/
theorem finite_setOf_eq_of_summable_div_pow (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    {i | a i = z}.Finite := by
  have hf := TauCeti.finite_one_add_eq_zero
    (exists_summable_cofinite_elementaryFactor_div_sub_one hsum) (mem_univ z)
  refine hf.subset fun i hi ↦ ?_
  simp only [mem_ofPred_eq, add_sub_cancel, elementaryFactor_eq_zero_iff]
  rw [div_eq_one_iff_eq (ha i)]
  exact hi.symm

/-- **Exact zero multiplicities of variable-genus primary products.** At every `z : ℂ`, the
analytic order of `∏' i, elementaryFactor (p i) (w / a i)` equals `{i | a i = z}.ncard`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, elementaryFactor (p i) (w / a i)) z =
      ({i | a i = z}.ncard : ℕ∞) := by
  have hord := TauCeti.analyticOrderAt_tprod_one_add isOpen_univ
    (u := fun i w ↦ elementaryFactor (p i) (w / a i) - 1) (fun i ↦ by fun_prop)
    (exists_summable_cofinite_elementaryFactor_div_sub_one hsum) (mem_univ z)
  simp only [add_sub_cancel] at hord
  rw [hord]
  have hf := finite_setOf_eq_of_summable_div_pow ha hsum z
  have hcongr : (∑ᶠ i, analyticOrderAt (fun w ↦ elementaryFactor (p i) (w / a i)) z) =
      ∑ᶠ i, (if a i = z then (1 : ℕ∞) else 0) := by
    refine finsum_congr fun i ↦ ?_
    rw [analyticOrderAt_elementaryFactor_div (p i) (ha i) z]
    simp only [eq_comm]
  rw [hcongr, finsum_eq_sum_of_support_subset _ fun i hi ↦ hf.mem_toFinset.mpr ?_]
  · have hsum_one : (∑ i ∈ hf.toFinset, if a i = z then (1 : ℕ∞) else 0) = hf.toFinset.card := by
      calc
        _ = ∑ _i ∈ hf.toFinset, (1 : ℕ∞) :=
            Finset.sum_congr rfl fun i hi ↦ by
              have hiz : a i = z := hf.mem_toFinset.mp hi
              simp [hiz]
        _ = hf.toFinset.card := by simp
    rw [hsum_one, ← Set.ncard_eq_toFinset_card _ hf]
  · simpa using hi

/-- Whole-plane divisor of a variable-genus Weierstrass primary product. -/
theorem divisor_tprod_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' i, elementaryFactor (p i) (w / a i)) Set.univ z =
      ({i | a i = z}.ncard : ℤ) := by
  have hd := differentiable_tprod_elementaryFactor_div hsum
  have hana : AnalyticOnNhd ℂ (fun w ↦ ∏' i, elementaryFactor (p i) (w / a i)) Set.univ :=
    fun w _ ↦ hd.analyticAt w
  rw [hana.meromorphicOn.divisor_eq_analyticOrderNatAt (hd.analyticAt z) (mem_univ z),
    analyticOrderNatAt, analyticOrderAt_tprod_elementaryFactor_div ha hsum z, ENat.toNat_natCast]

end Unweighted

section Weighted

variable {ι : Type*} {a : ι → ℂ} {p m : ι → ℕ}

private theorem summable_sigma_div_pow (m : ι → ℕ)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    ∀ R : ℝ, 0 < R → Summable fun q : Σ i, Fin (m i) ↦ (R / ‖a q.1‖) ^ (p q.1 + 1) :=
  fun R hR ↦ (TauCeti.summable_sigma_fin_iff
    (fun i ↦ pow_nonneg (div_nonneg hR.le (norm_nonneg (a i))) _) m).mpr (hm R hR)

/-- Grouping finite multiplicity fibers `Fin (m i)` over `Σ i, Fin (m i)` preserves the value of
the primary product. -/
theorem tprod_elementaryFactor_div_pow_eq_sigma
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, elementaryFactor (p i) (z / a i) ^ m i) =
      ∏' q : Σ i, Fin (m i), elementaryFactor (p q.1) (z / a q.1) := by
  have hσ := summable_sigma_div_pow m hm
  have hp : Multipliable (fun q : Σ i, Fin (m i) ↦ elementaryFactor (p q.1) (z / a q.1)) :=
    ((hasProdUniformlyOn_elementaryFactor_div
      (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
      hσ isCompact_singleton).hasProd (mem_singleton z)).multipliable
  rw [hp.tprod_sigma' fun _ ↦ Multipliable.of_finite]
  simp [tprod_fintype]

/-- Weighted primary products with natural multiplicities converge uniformly on compact sets. -/
theorem hasProdUniformlyOn_elementaryFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) K := by
  have h := (hasProdUniformlyOn_elementaryFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (summable_sigma_div_pow m hm) hK).sigma_of_finite
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← tprod_elementaryFactor_div_pow_eq_sigma hm] using h

/-- Weighted primary products with natural multiplicities converge locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_elementaryFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) Set.univ := by
  have h := (hasProdLocallyUniformlyOn_elementaryFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (summable_sigma_div_pow m hm)).sigma_of_finite
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← tprod_elementaryFactor_div_pow_eq_sigma hm] using h

/-- A weighted variable-genus primary product is entire. -/
@[fun_prop]
theorem differentiable_tprod_elementaryFactor_div_pow
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    Differentiable ℂ (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) := by
  have heq : (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) =
      fun z ↦ ∏' q : Σ i, Fin (m i), elementaryFactor (p q.1) (z / a q.1) :=
    funext (tprod_elementaryFactor_div_pow_eq_sigma hm)
  rw [heq]
  exact differentiable_tprod_elementaryFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (summable_sigma_div_pow m hm)

/-- A weighted primary product vanishes at `z` if and only if some root `a i = z` has nonzero
multiplicity `m i`. -/
theorem tprod_elementaryFactor_div_pow_eq_zero_iff (ha : ∀ i, m i ≠ 0 → a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, elementaryFactor (p i) (z / a i) ^ m i) = 0 ↔ ∃ i, m i ≠ 0 ∧ a i = z := by
  rw [tprod_elementaryFactor_div_pow_eq_sigma hm,
    tprod_elementaryFactor_div_eq_zero_iff
      (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
      (fun q ↦ ha q.1 (Nat.ne_zero_of_lt q.2.isLt)) (summable_sigma_div_pow m hm)]
  constructor
  · rintro ⟨⟨i, k⟩, hi⟩
    exact ⟨i, Nat.ne_zero_of_lt k.isLt, hi⟩
  · rintro ⟨i, hmi, hi⟩
    exact ⟨⟨i, ⟨0, Nat.pos_of_ne_zero hmi⟩⟩, hi⟩

/-- Analytic order of a weighted primary product in terms of its sigma multiplicity fiber. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_pow (ha : ∀ i, m i ≠ 0 → a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) z =
      ({q : Σ j, Fin (m j) | a q.1 = z}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) =
      fun w ↦ ∏' q : Σ j, Fin (m j), elementaryFactor (p q.1) (w / a q.1) :=
    funext (tprod_elementaryFactor_div_pow_eq_sigma hm)
  rw [heq]
  exact analyticOrderAt_tprod_elementaryFactor_div
    (a := fun q : Σ j, Fin (m j) ↦ a q.1) (p := fun q : Σ j, Fin (m j) ↦ p q.1)
    (fun q ↦ ha q.1 (Nat.ne_zero_of_lt q.2.isLt)) (summable_sigma_div_pow m hm) z

/-- When `a` is injective and `a i ≠ 0` whenever `m i ≠ 0`, the analytic order of the weighted
primary product at `a i` is the prescribed multiplicity `m i`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1))
    (hinj : Function.Injective a) {i : ι} (hai : m i ≠ 0 → a i ≠ 0) :
    analyticOrderAt (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) (a i) = m i := by
  classical
  have heq : (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) =
      fun w ↦ ∏' q : Σ j, Fin (m j), elementaryFactor (p q.1) (w / a q.1) :=
    funext (tprod_elementaryFactor_div_pow_eq_sigma hm)
  have hord := TauCeti.analyticOrderAt_tprod_one_add isOpen_univ
    (u := fun (q : Σ j, Fin (m j)) w ↦ elementaryFactor (p q.1) (w / a q.1) - 1)
    (fun _ ↦ by fun_prop)
    (exists_summable_cofinite_elementaryFactor_div_sub_one
      (a := fun q : Σ j, Fin (m j) ↦ a q.1) (p := fun q : Σ j, Fin (m j) ↦ p q.1)
      (summable_sigma_div_pow m hm)) (mem_univ (a i))
  simp only [add_sub_cancel] at hord
  rw [heq, hord]
  have hterm (q : Σ j, Fin (m j)) :
      analyticOrderAt (fun w ↦ elementaryFactor (p q.1) (w / a q.1)) (a i) =
        if q.1 = i then 1 else 0 := by
    have hmul : (fun w ↦ elementaryFactor (p q.1) (w / a q.1)) =
        fun w ↦ elementaryFactor (p q.1) ((a q.1)⁻¹ * w) := by
      ext w; rw [div_eq_inv_mul]
    rw [hmul, analyticOrderAt_elementaryFactor_mul]
    refine if_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ rfl rfl
    · have haq : a q.1 ≠ 0 := fun ha0 ↦ by simp [ha0] at h
      exact hinj ((inv_mul_eq_one₀ haq).mp h)
    · rw [h]
      exact inv_mul_cancel₀ (hai (h ▸ Nat.ne_zero_of_lt q.2.isLt))
  let s : Finset (Σ j, Fin (m j)) := Finset.univ.map ⟨Sigma.mk i, sigma_mk_injective⟩
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_]
  · calc
      (∑ q ∈ s, if q.1 = i then (1 : ℕ∞) else 0) = ∑ _q ∈ s, (1 : ℕ∞) :=
        Finset.sum_congr rfl fun q hq ↦ by
          obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hq
          simp
      _ = m i := by simp [s]
  · have hqi : q.1 = i := by simpa using hq
    exact Finset.mem_map.mpr ⟨hqi ▸ q.2, Finset.mem_univ _, by cases q; cases hqi; rfl⟩

/-- Outside the active roots (`∀ j, m j ≠ 0 → a j ≠ z`), a weighted primary product has analytic
order `0`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_pow_eq_zero
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) {z : ℂ}
    (hz : ∀ j, m j ≠ 0 → a j ≠ z) :
    analyticOrderAt (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) z = 0 := by
  have h0 : (∏' j, elementaryFactor (p j) (z / a j) ^ m j) ≠ 0 := by
    rw [tprod_elementaryFactor_div_pow_eq_sigma hm]
    have h := TauCeti.tprod_one_add_eq_zero_iff
      (u := fun (q : Σ j, Fin (m j)) w ↦ elementaryFactor (p q.1) (w / a q.1) - 1)
      (exists_summable_cofinite_elementaryFactor_div_sub_one
        (a := fun q : Σ j, Fin (m j) ↦ a q.1) (p := fun q : Σ j, Fin (m j) ↦ p q.1)
        (summable_sigma_div_pow m hm)) (mem_univ z)
    simp only [add_sub_cancel, elementaryFactor_eq_zero_iff] at h
    rw [ne_eq, h]
    rintro ⟨⟨j, k⟩, hj⟩
    have haj : a j ≠ 0 := fun ha0 ↦ by simp [ha0] at hj
    exact hz j (Nat.ne_zero_of_lt k.isLt) ((div_eq_one_iff_eq haj).mp hj).symm
  exact ((differentiable_tprod_elementaryFactor_div_pow hm).analyticAt
    z).analyticOrderAt_eq_zero.mpr h0

/-- Whole-plane divisor of a weighted variable-genus primary product. -/
theorem divisor_tprod_elementaryFactor_div_pow (ha : ∀ j, m j ≠ 0 → a j ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ z =
      ({q : Σ j, Fin (m j) | a q.1 = z}.ncard : ℤ) := by
  have hd := differentiable_tprod_elementaryFactor_div_pow hm
  have hana : AnalyticOnNhd ℂ (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ :=
    fun w _ ↦ hd.analyticAt w
  rw [hana.meromorphicOn.divisor_eq_analyticOrderNatAt (hd.analyticAt z) (mem_univ z),
    analyticOrderNatAt, analyticOrderAt_tprod_elementaryFactor_div_pow ha hm z,
    ENat.toNat_natCast]

/-- When `a` is injective and `a i ≠ 0` whenever `m i ≠ 0`, the whole-plane divisor of the
weighted primary product at `a i` is the prescribed multiplicity `m i`. -/
theorem divisor_tprod_elementaryFactor_div_pow_of_injective
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1))
    (hinj : Function.Injective a) {i : ι} (hai : m i ≠ 0 → a i ≠ 0) :
    MeromorphicOn.divisor (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ (a i) =
      (m i : ℤ) := by
  have hd := differentiable_tprod_elementaryFactor_div_pow hm
  have hana : AnalyticOnNhd ℂ (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ :=
    fun w _ ↦ hd.analyticAt w
  rw [hana.meromorphicOn.divisor_eq_analyticOrderNatAt (hd.analyticAt (a i)) (mem_univ (a i)),
    analyticOrderNatAt, analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective hm hinj hai,
    ENat.toNat_natCast]

/-- Outside the active roots (`∀ j, m j ≠ 0 → a j ≠ z`), a weighted primary product has
whole-plane divisor `0`. -/
theorem divisor_tprod_elementaryFactor_div_pow_eq_zero
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) {z : ℂ}
    (hz : ∀ j, m j ≠ 0 → a j ≠ z) :
    MeromorphicOn.divisor
      (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ z = 0 := by
  have hd := differentiable_tprod_elementaryFactor_div_pow hm
  have hana : AnalyticOnNhd ℂ (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ :=
    fun w _ ↦ hd.analyticAt w
  rw [hana.meromorphicOn.divisor_eq_analyticOrderNatAt (hd.analyticAt z) (mem_univ z),
    analyticOrderNatAt, analyticOrderAt_tprod_elementaryFactor_div_pow_eq_zero hm hz,
    ENat.toNat_zero, Nat.cast_zero]

end Weighted

end Complex

namespace Differentiable

/-- Given a nonzero entire function `f` and any admissible genus assignment
`p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ` whose weighted primary product converges, there exists an
entire function `g` (unique up to `2 * π * I * ℤ`) such that
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`
for all `z : ℂ`. -/
theorem exists_eq_pow_mul_exp_mul_tprod_elementaryFactor_div_pow_of_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) {p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ}
    (hm_sum : ∀ R : ℝ, 0 < R → Summable fun a : {a : ℂ // a ≠ 0 ∧ f a = 0} ↦
      (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g z) *
        ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' →
        (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g' z) *
          ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
            elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  obtain ⟨z₀, hz₀⟩ := hf0
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  set m₀ := analyticOrderNatAt f 0
  let Z := {a : ℂ // a ≠ 0 ∧ f a = 0}
  let P : ℂ → ℂ := fun z ↦ ∏' a : Z, elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a
  have hP_diff : Differentiable ℂ P := differentiable_tprod_elementaryFactor_div_pow hm_sum
  let F : ℂ → ℂ := fun z ↦ z ^ m₀ * P z
  have hF_diff : Differentiable ℂ F := (differentiable_id.pow m₀).mul hP_diff
  have hft_ne_top (z : ℂ) : analyticOrderAt f z ≠ ⊤ :=
    hfa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀) (mem_univ z)
      (by simp [(hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hz₀])
  have hord (z : ℂ) : analyticOrderAt f z = analyticOrderAt F z := by
    have hF_split : analyticOrderAt F z =
        analyticOrderAt (fun w : ℂ ↦ w ^ m₀) z + analyticOrderAt P z :=
      analyticOrderAt_mul (analyticAt_id.pow m₀) (hP_diff.analyticAt z)
    rw [hF_split, ← Nat.cast_analyticOrderNatAt (hft_ne_top z)]
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
        simpa [P, a₀] using (analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective
          hm_sum Subtype.val_injective (i := a₀) fun _ ↦ a₀.2.1).symm
      · have hPz : analyticOrderAt P z = 0 :=
          analyticOrderAt_tprod_elementaryFactor_div_pow_eq_zero hm_sum fun a _ ha ↦
            hfz (ha ▸ a.2.2)
        rw [hPz, analyticOrderNatAt, (hf.analyticAt z).analyticOrderAt_eq_zero.mpr hfz,
          ENat.toNat_zero, Nat.cast_zero]
  obtain ⟨g, hg, hfg, huniq⟩ :=
    hf.exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq hF_diff ⟨z₀, hz₀⟩ hord
  refine ⟨g, hg, fun z ↦ ?_, fun g' hg' hfg' ↦ huniq g' hg' fun z ↦ ?_⟩
  · simpa only [F, P, m₀, mul_left_comm (Complex.exp (g z)), mul_assoc] using hfg z
  · simpa only [F, P, m₀, mul_left_comm (Complex.exp (g' z)), mul_assoc] using hfg' z

/-- **Weierstrass's entire factorization theorem** (Rudin, Theorem 15.10). Every entire function
`f : ℂ → ℂ` that is not identically zero admits admissible genera
`p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ` and an entire function `g : ℂ → ℂ` (unique up to `2πiℤ`)
such that the weighted primary product over its nonzero zeros converges locally uniformly on `ℂ`
and
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`
for all `z : ℂ`, with no growth hypothesis on `f`. -/
theorem exists_eq_pow_mul_exp_mul_tprod_elementaryFactor_div_pow {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) :
    ∃ (p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ) (g : ℂ → ℂ),
      (∀ R : ℝ, 0 < R → Summable fun a : {a : ℂ // a ≠ 0 ∧ f a = 0} ↦
        (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1)) ∧
      HasProdLocallyUniformlyOn
        (fun (a : {a : ℂ // a ≠ 0 ∧ f a = 0}) z ↦
          elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a)
        (fun z ↦ ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) Set.univ ∧
      Differentiable ℂ g ∧
      (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g z) *
        ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' →
        (∀ z, f z = z ^ analyticOrderNatAt f 0 * Complex.exp (g' z) *
          ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
            elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) →
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
          ⟨mem_closedBall_zero_iff.mpr (hwa ▸ haR), hwa ▸ a.2.2⟩
    have hlt : ∀ᶠ a : {a : ℂ // a ≠ 0 ∧ f a = 0} in cofinite, R < ‖(a : ℂ)‖ := by
      simpa only [eventually_cofinite, not_lt] using hfin
    exact hlt.mono fun _ h ↦ h.le
  obtain ⟨p, hm_sum⟩ := hnorm_atTop.exists_summable_mul_div_pow fun a ↦ analyticOrderNatAt f a
  obtain ⟨g, hg, hfg, huniq⟩ :=
    hf.exists_eq_pow_mul_exp_mul_tprod_elementaryFactor_div_pow_of_summable ⟨z₀, hz₀⟩ hm_sum
  exact ⟨p, g, hm_sum, hasProdLocallyUniformlyOn_elementaryFactor_div_pow hm_sum, hg, hfg, huniq⟩

end Differentiable

/-! ### Examples -/

/-- Two genus-zero factors at the same root `a = 1` multiply to `(1 - z) ^ 2` and produce
analytic order `2` at `1` (the fiber cardinality of `Fin 2`, rather than the cardinality `1` of
the distinct support). -/
example :
    (∀ z : ℂ, (∏' _i : Fin 2, elementaryFactor 0 (z / 1)) = (1 - z) ^ 2) ∧
      analyticOrderAt (fun z : ℂ ↦ ∏' _i : Fin 2, elementaryFactor 0 (z / 1)) 1 = 2 := by
  have ha : ∀ _i : Fin 2, (1 : ℂ) ≠ 0 := fun _ ↦ one_ne_zero
  have hsum : ∀ R : ℝ, 0 < R → Summable fun _i : Fin 2 ↦ (R / ‖(1 : ℂ)‖) ^ (0 + 1) :=
    fun _ _ ↦ Summable.of_finite
  refine ⟨fun z ↦ ?_, ?_⟩
  · rw [tprod_fintype]
    simp [sq]
  · simpa using analyticOrderAt_tprod_elementaryFactor_div ha hsum 1
