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
import TauCeti.Order.Filter.AtTopBot.Finset
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Weierstrass canonical products of arbitrary genus and entire factorization

Given an arbitrary index family `a : ι → ℂ` of nonzero complex numbers (possibly repeated according
to multiplicity) and genera `p : ι → ℕ` such that `∑' i, (R / ‖a i‖) ^ (p i + 1) < ∞` for every
`R > 0`, the unordered primary product
`∏' i, Complex.elementaryFactor (p i) (z / a i)`
converges uniformly on compact sets and locally uniformly on `ℂ` to an entire function normalized
to `1` at `0`. Its zeros are precisely the values `a i`, and at every `z : ℂ` its analytic order of
vanishing equals the fiber cardinality `Nat.card {i // a i = z}` (`{i | a i = z}.ncard`). Both
`‖a i‖ → ∞` along `Filter.cofinite` and finiteness of each fiber follow automatically from the
summability hypothesis, and no countability assumption on `ι` is required.

Reindexing by an equivalence `κ ≃ ι` and grouping finite multiplicity fibers `m : ι → ℕ` under
`∑' i, m i * (R / ‖a i‖) ^ (p i + 1) < ∞` preserve the product and its locally uniform
convergence. Combining variable-genus products with
`TauCeti.exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq` yields Weierstrass's general
factorization theorem: every nonzero entire function `f : ℂ → ℂ` admits admissible genera `p` on
its set of nonzero zeros and an entire function `g` (unique up to `2πiℤ`) such that
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`,
without any growth hypothesis on `f`.

## Main results

* `Complex.tendsto_norm_cofinite_atTop_of_summable_div_pow`: summability of
  `(R / ‖a i‖) ^ (p i + 1)` for all `R > 0` forces `‖a i‖ → ∞` along `Filter.cofinite`.
* `Complex.hasProdUniformlyOn_elementaryFactor_div`,
  `Complex.hasProdLocallyUniformlyOn_elementaryFactor_div`,
  `Complex.differentiable_tprod_elementaryFactor_div`: compact-uniform and locally uniform
  convergence and entirety of `∏' i, elementaryFactor (p i) (z / a i)`.
* `Complex.analyticOrderAt_tprod_elementaryFactor_div`,
  `Complex.divisor_tprod_elementaryFactor_div`: exact zero-order and whole-plane divisor formulas
  in terms of fiber cardinalities.
* `Complex.tprod_elementaryFactor_div_comp_equiv`,
  `Complex.hasProdLocallyUniformlyOn_elementaryFactor_div_pow`,
  `Complex.analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective`: invariance under
  equivalences and grouped finite multiplicity fibers.
* `TauCeti.exists_differentiable_hasProdLocallyUniformlyOn_elementaryFactor_div`: packaged
  existence, locally uniform convergence, normalization, and exact zero orders of variable-genus
  primary products.
* `TauCeti.exists_differentiable_weierstrass_factorization`: Weierstrass's entire factorization
  theorem for an arbitrary nonzero entire function without growth hypotheses.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorems 15.9 and 15.10.
* Z. Yun, W. Zhang, *Shtukas and the Taylor expansion of L-functions*, J. Amer. Math. Soc. **30**
  (2017), Appendix B.1.
-/

public section

open Complex Filter Function Metric Set Topology
open scoped BigOperators

namespace Complex

section Unweighted

variable {ι : Type*} {a : ι → ℂ} {p : ι → ℕ}

/-- Every variable-genus primary product is normalized to `1` at the origin. -/
theorem tprod_elementaryFactor_div_zero (a : ι → ℂ) (p : ι → ℕ) :
    (∏' i, elementaryFactor (p i) ((0 : ℂ) / a i)) = 1 := by
  simp

/-- Reindexing by an equivalence preserves `∏' i, elementaryFactor (p i) (z / a i)`. -/
theorem tprod_elementaryFactor_div_comp_equiv {κ : Type*} (e : κ ≃ ι) (a : ι → ℂ) (p : ι → ℕ)
    (z : ℂ) :
    (∏' k, elementaryFactor (p (e k)) (z / a (e k))) =
      ∏' i, elementaryFactor (p i) (z / a i) :=
  e.tprod_eq fun i ↦ elementaryFactor (p i) (z / a i)

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

private theorem exists_summable_cofinite_elementaryFactor_div_sub_one (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    ∀ K ⊆ (Set.univ : Set ℂ), IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ z ∈ K, ‖elementaryFactor (p i) (z / a i) - 1‖ ≤ v i := by
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  refine ⟨fun i ↦ (R / ‖a i‖) ^ (p i + 1), hsum R hR, ?_⟩
  filter_upwards [(tendsto_norm_cofinite_atTop_of_summable_div_pow ha hsum).eventually_ge_atTop R]
    with i hi z hz
  have hzR : ‖z‖ ≤ R := (hM z hz).trans (le_max_left M 1)
  have ha_pos : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
  have hquot_le : ‖z / a i‖ ≤ R / ‖a i‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right hzR ha_pos.le
  have hz1 : ‖z / a i‖ ≤ 1 := hquot_le.trans ((div_le_one ha_pos).mpr hi)
  exact (norm_elementaryFactor_sub_one_le (p i) hz1).trans
    (pow_le_pow_left₀ (norm_nonneg _) hquot_le _)

/-- On every compact set `K ⊆ ℂ`, the variable-genus primary product
`∏' i, elementaryFactor (p i) (z / a i)` converges uniformly. -/
theorem hasProdUniformlyOn_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i))
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) K := by
  obtain ⟨v, hv, hbound⟩ :=
    exists_summable_cofinite_elementaryFactor_div_sub_one ha hsum K (subset_univ K) hK
  have hcts : ∀ i, ContinuousOn (fun z ↦ elementaryFactor (p i) (z / a i) - 1) K := fun i ↦
    (by fun_prop : Continuous fun z ↦ elementaryFactor (p i) (z / a i) - 1).continuousOn
  simpa only [add_sub_cancel] using hv.hasProdUniformlyOn_one_add hK hbound hcts

/-- The variable-genus primary product converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i))
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_elementaryFactor_div ha hsum hK

/-- Reindexing by an equivalence preserves locally uniform convergence of the primary product to
the same limit function on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_elementaryFactor_div_comp_equiv {κ : Type*} (e : κ ≃ ι)
    (ha : ∀ i, a i ≠ 0) (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun k z ↦ elementaryFactor (p (e k)) (z / a (e k)))
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) Set.univ := by
  have h := hasProdLocallyUniformlyOn_elementaryFactor_div (fun k ↦ ha (e k))
    (fun R hR ↦ e.summable_iff.mpr (hsum R hR))
  exact h.congr_right fun z _ ↦ tprod_elementaryFactor_div_comp_equiv e a p z

/-- A variable-genus Weierstrass primary product is entire. -/
@[fun_prop]
theorem differentiable_tprod_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    Differentiable ℂ (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i)) := by
  rw [← differentiableOn_univ]
  have h := TauCeti.differentiableOn_tprod_one_add isOpen_univ
    (u := fun i z ↦ elementaryFactor (p i) (z / a i) - 1) (fun i ↦ by fun_prop)
    (exists_summable_cofinite_elementaryFactor_div_sub_one ha hsum)
  simpa only [add_sub_cancel] using h

/-- At each `z : ℂ`, the deviations `‖elementaryFactor (p i) (z / a i) - 1‖` are summable. -/
theorem summable_norm_elementaryFactor_div_sub_one (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    Summable fun i ↦ ‖elementaryFactor (p i) (z / a i) - 1‖ :=
  TauCeti.summable_norm_of_forall_compact
    (exists_summable_cofinite_elementaryFactor_div_sub_one ha hsum) (mem_univ z)

/-- The primary product vanishes at `z` if and only if `z` occurs in the root family `a`. -/
theorem tprod_elementaryFactor_div_eq_zero_iff (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, elementaryFactor (p i) (z / a i)) = 0 ↔ ∃ i, a i = z := by
  have h := TauCeti.tprod_one_add_eq_zero_iff
    (exists_summable_cofinite_elementaryFactor_div_sub_one ha hsum) (mem_univ z)
  simp only [add_sub_cancel, elementaryFactor_eq_zero_iff] at h
  refine h.trans (exists_congr fun i ↦ ?_)
  rw [div_eq_one_iff_eq (ha i), eq_comm]

/-- Each point `z : ℂ` occurs at most finitely many times in the root family `a`. -/
theorem finite_eq_of_summable_div_pow (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    {i | a i = z}.Finite := by
  have hf := TauCeti.finite_one_add_eq_zero
    (exists_summable_cofinite_elementaryFactor_div_sub_one ha hsum) (mem_univ z)
  refine hf.subset fun i hi ↦ ?_
  simp only [mem_ofPred_eq, add_sub_cancel, elementaryFactor_eq_zero_iff]
  rw [div_eq_one_iff_eq (ha i)]
  exact hi.symm

/-- **Exact zero multiplicities of variable-genus primary products.** At every `z : ℂ`, the
analytic order of `∏' i, elementaryFactor (p i) (w / a i)` equals `Nat.card {i // a i = z}`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, elementaryFactor (p i) (w / a i)) z =
      (Nat.card {i // a i = z} : ℕ∞) := by
  have hord := TauCeti.analyticOrderAt_tprod_one_add isOpen_univ
    (u := fun i w ↦ elementaryFactor (p i) (w / a i) - 1) (fun i ↦ by fun_prop)
    (exists_summable_cofinite_elementaryFactor_div_sub_one ha hsum) (mem_univ z)
  simp only [add_sub_cancel] at hord
  rw [hord]
  have hf := finite_eq_of_summable_div_pow ha hsum z
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
    rw [hsum_one, ← Set.ncard_eq_toFinset_card _ hf, Set.ncard_ofPred]
  · simpa using hi

/-- Set-cardinality form of `analyticOrderAt_tprod_elementaryFactor_div`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_eq_ncard (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, elementaryFactor (p i) (w / a i)) z =
      ({i | a i = z}.ncard : ℕ∞) := by
  rw [Set.ncard_ofPred]
  exact analyticOrderAt_tprod_elementaryFactor_div ha hsum z

/-- Whole-plane divisor of a variable-genus Weierstrass primary product. -/
theorem divisor_tprod_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' i, elementaryFactor (p i) (w / a i)) Set.univ z =
      (Nat.card {i // a i = z} : ℤ) := by
  have hd := differentiable_tprod_elementaryFactor_div ha hsum
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
theorem tprod_elementaryFactor_div_pow_eq_sigma (ha : ∀ i, a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, elementaryFactor (p i) (z / a i) ^ m i) =
      ∏' q : Σ i, Fin (m i), elementaryFactor (p q.1) (z / a q.1) := by
  have hσ := summable_sigma_div_pow m hm
  have hp : Multipliable (fun q : Σ i, Fin (m i) ↦ elementaryFactor (p q.1) (z / a q.1)) :=
    ((hasProdUniformlyOn_elementaryFactor_div
      (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
      (fun q ↦ ha q.1) hσ isCompact_singleton).hasProd (mem_singleton z)).multipliable
  rw [hp.tprod_sigma' fun _ ↦ Multipliable.of_finite]
  simp [tprod_fintype]

/-- Weighted primary products with natural multiplicities converge uniformly on compact sets. -/
theorem hasProdUniformlyOn_elementaryFactor_div_pow (ha : ∀ i, a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1))
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) K := by
  have h0 := (hasProdUniformlyOn_elementaryFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (fun q ↦ ha q.1) (summable_sigma_div_pow m hm) hK).tendstoUniformlyOn
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  intro u hu
  filter_upwards [(TauCeti.tendsto_finset_sigma_univ_atTop (κ := fun i ↦ Fin (m i))).eventually
    (h0 u hu)] with s hs z hz
  have hsz := hs z hz
  simpa only [← tprod_elementaryFactor_div_pow_eq_sigma ha hm,
    Finset.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hsz

/-- Weighted primary products with natural multiplicities converge locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_elementaryFactor_div_pow (ha : ∀ i, a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    HasProdLocallyUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i) ^ m i)
      (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) Set.univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun _ _ hK ↦
    hasProdUniformlyOn_elementaryFactor_div_pow ha hm hK

/-- A weighted variable-genus primary product is entire. -/
@[fun_prop]
theorem differentiable_tprod_elementaryFactor_div_pow (ha : ∀ i, a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) :
    Differentiable ℂ (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) := by
  have heq : (fun z ↦ ∏' i, elementaryFactor (p i) (z / a i) ^ m i) =
      fun z ↦ ∏' q : Σ i, Fin (m i), elementaryFactor (p q.1) (z / a q.1) :=
    funext (tprod_elementaryFactor_div_pow_eq_sigma ha hm)
  rw [heq]
  exact differentiable_tprod_elementaryFactor_div
    (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
    (fun q ↦ ha q.1) (summable_sigma_div_pow m hm)

/-- A weighted primary product vanishes at `z` if and only if some root `a i = z` has nonzero
multiplicity `m i`. -/
theorem tprod_elementaryFactor_div_pow_eq_zero_iff (ha : ∀ i, a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    (∏' i, elementaryFactor (p i) (z / a i) ^ m i) = 0 ↔ ∃ i, m i ≠ 0 ∧ a i = z := by
  rw [tprod_elementaryFactor_div_pow_eq_sigma ha hm,
    tprod_elementaryFactor_div_eq_zero_iff
      (a := fun q : Σ i, Fin (m i) ↦ a q.1) (p := fun q : Σ i, Fin (m i) ↦ p q.1)
      (fun q ↦ ha q.1) (summable_sigma_div_pow m hm)]
  constructor
  · rintro ⟨⟨i, k⟩, hi⟩
    exact ⟨i, Nat.ne_zero_of_lt k.isLt, hi⟩
  · rintro ⟨i, hmi, hi⟩
    exact ⟨⟨i, ⟨0, Nat.pos_of_ne_zero hmi⟩⟩, hi⟩

/-- Analytic order of a weighted primary product in terms of its sigma multiplicity fiber. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_pow (ha : ∀ i, a i ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun i ↦ (m i : ℝ) * (R / ‖a i‖) ^ (p i + 1)) (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) z =
      ({q : Σ j, Fin (m j) | a q.1 = z}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) =
      fun w ↦ ∏' q : Σ j, Fin (m j), elementaryFactor (p q.1) (w / a q.1) :=
    funext (tprod_elementaryFactor_div_pow_eq_sigma ha hm)
  rw [heq]
  exact analyticOrderAt_tprod_elementaryFactor_div_eq_ncard
    (a := fun q : Σ j, Fin (m j) ↦ a q.1) (p := fun q : Σ j, Fin (m j) ↦ p q.1)
    (fun q ↦ ha q.1) (summable_sigma_div_pow m hm) z

/-- When `a` is injective, the analytic order of the weighted primary product at `a i` is the
prescribed multiplicity `m i`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective (ha : ∀ j, a j ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1))
    (hinj : Function.Injective a) (i : ι) :
    analyticOrderAt (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) (a i) = m i := by
  classical
  let s : Finset (Σ j, Fin (m j)) := Finset.univ.map ⟨Sigma.mk i, sigma_mk_injective⟩
  have hset : {q : Σ j, Fin (m j) | a q.1 = a i} = (s : Set (Σ j, Fin (m j))) := by
    ext ⟨j, k⟩
    simp only [mem_ofPred_eq, Finset.mem_coe, s, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hj
      cases hinj hj
      exact ⟨k, rfl⟩
    · rintro ⟨_, hq⟩
      cases hq
      rfl
  rw [analyticOrderAt_tprod_elementaryFactor_div_pow ha hm (a i), hset, Set.ncard_coe_finset]
  simp [s]

/-- Outside the root family (`∀ j, a j ≠ z`), a weighted primary product has analytic order `0`. -/
theorem analyticOrderAt_tprod_elementaryFactor_div_pow_eq_zero (ha : ∀ j, a j ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) {z : ℂ}
    (hz : ∀ j, a j ≠ z) :
    analyticOrderAt (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) z = 0 := by
  have h0 : (∏' j, elementaryFactor (p j) (z / a j) ^ m j) ≠ 0 := by
    rw [ne_eq, tprod_elementaryFactor_div_pow_eq_zero_iff ha hm]
    rintro ⟨j, _, hj⟩
    exact hz j hj
  exact ((differentiable_tprod_elementaryFactor_div_pow ha hm).analyticAt
    z).analyticOrderAt_eq_zero.mpr h0

/-- Whole-plane divisor of a weighted variable-genus primary product. -/
theorem divisor_tprod_elementaryFactor_div_pow (ha : ∀ j, a j ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1)) (z : ℂ) :
    MeromorphicOn.divisor (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ z =
      ({q : Σ j, Fin (m j) | a q.1 = z}.ncard : ℤ) := by
  have hd := differentiable_tprod_elementaryFactor_div_pow ha hm
  have hana : AnalyticOnNhd ℂ (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ :=
    fun w _ ↦ hd.analyticAt w
  rw [hana.meromorphicOn.divisor_eq_analyticOrderNatAt (hd.analyticAt z) (mem_univ z),
    analyticOrderNatAt, analyticOrderAt_tprod_elementaryFactor_div_pow ha hm z,
    ENat.toNat_natCast]

/-- When `a` is injective, the whole-plane divisor of the weighted primary product at `a i` is the
prescribed multiplicity `m i`. -/
theorem divisor_tprod_elementaryFactor_div_pow_of_injective (ha : ∀ j, a j ≠ 0)
    (hm : ∀ R : ℝ, 0 < R → Summable fun j ↦ (m j : ℝ) * (R / ‖a j‖) ^ (p j + 1))
    (hinj : Function.Injective a) (i : ι) :
    MeromorphicOn.divisor (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ (a i) =
      (m i : ℤ) := by
  have hd := differentiable_tprod_elementaryFactor_div_pow ha hm
  have hana : AnalyticOnNhd ℂ (fun w ↦ ∏' j, elementaryFactor (p j) (w / a j) ^ m j) Set.univ :=
    fun w _ ↦ hd.analyticAt w
  rw [hana.meromorphicOn.divisor_eq_analyticOrderNatAt (hd.analyticAt (a i)) (mem_univ (a i)),
    analyticOrderNatAt, analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective ha hm hinj i,
    ENat.toNat_natCast]

end Weighted

end Complex

namespace TauCeti

/-- **Variable-genus Weierstrass primary product theorem.** For any index family `a : ι → ℂ` of
nonzero points and genera `p : ι → ℕ` satisfying `∑' i, (R / ‖a i‖) ^ (p i + 1) < ∞` for all
`R > 0`, the product `∏' i, elementaryFactor (p i) (z / a i)` converges locally uniformly on `ℂ`
to an entire function `F` with `F 0 = 1` and exact zero multiplicities
`analyticOrderAt F z = Nat.card {i // a i = z}`. -/
theorem exists_differentiable_hasProdLocallyUniformlyOn_elementaryFactor_div {ι : Type*}
    (a : ι → ℂ) (p : ι → ℕ) (ha : ∀ i, a i ≠ 0)
    (hsum : ∀ R : ℝ, 0 < R → Summable fun i ↦ (R / ‖a i‖) ^ (p i + 1)) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      HasProdLocallyUniformlyOn (fun i z ↦ elementaryFactor (p i) (z / a i)) F Set.univ ∧
      F 0 = 1 ∧
      ∀ z, analyticOrderAt F z = (Nat.card {i // a i = z} : ℕ∞) :=
  ⟨fun z ↦ ∏' i, elementaryFactor (p i) (z / a i),
    differentiable_tprod_elementaryFactor_div ha hsum,
    hasProdLocallyUniformlyOn_elementaryFactor_div ha hsum,
    tprod_elementaryFactor_div_zero a p,
    analyticOrderAt_tprod_elementaryFactor_div ha hsum⟩

/-- **Weierstrass's entire factorization theorem** (Rudin, Theorem 15.10). Every entire function
`f : ℂ → ℂ` that is not identically zero admits admissible genera
`p : {a : ℂ // a ≠ 0 ∧ f a = 0} → ℕ` and an entire function `g : ℂ → ℂ` (unique up to `2πiℤ`)
such that the weighted primary product over its nonzero zeros converges locally uniformly on `ℂ`
and
`f z = z ^ (analyticOrderNatAt f 0) * exp (g z) * ∏' a, E_{p a}(z / a) ^ (analyticOrderNatAt f a)`
for all `z : ℂ`, with no growth hypothesis on `f`. -/
theorem exists_differentiable_weierstrass_factorization {f : ℂ → ℂ}
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
      (∀ z, f z = z ^ analyticOrderNatAt f 0 * exp (g z) *
        ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
          elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) ∧
      ∀ g' : ℂ → ℂ, Differentiable ℂ g' →
        (∀ z, f z = z ^ analyticOrderNatAt f 0 * exp (g' z) *
          ∏' a : {a : ℂ // a ≠ 0 ∧ f a = 0},
            elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a) →
        ∃ k : ℤ, ∀ z, g' z = g z + k * (2 * Real.pi * I) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hf0
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun w _ ↦ hf.analyticAt w
  -- Every closed ball contains finitely many zeros of `f`, so the nonzero zero set is countable.
  have hball_fin (R : ℝ) : {z ∈ closedBall (0 : ℂ) R | f z = 0}.Finite :=
    hfa.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (mem_univ z₀) hz₀
      (isCompact_closedBall 0 R) (subset_univ _)
  let Z := {a : ℂ // a ≠ 0 ∧ f a = 0}
  have hZ_set_count : {a : ℂ | a ≠ 0 ∧ f a = 0}.Countable := by
    refine (countable_iUnion fun n : ℕ ↦ (hball_fin n).countable).mono fun a ha ↦ ?_
    exact mem_iUnion.mpr ⟨⌈‖a‖⌉₊, mem_closedBall_zero_iff.mpr (Nat.le_ceil ‖a‖), ha.2⟩
  have := hZ_set_count.to_subtype
  have : Countable Z := Function.Injective.countable
    (f := fun a : Z ↦ (⟨a.1, a.2⟩ : {a : ℂ | a ≠ 0 ∧ f a = 0}))
    fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h)
  obtain ⟨idx, hidx⟩ := Countable.exists_injective_nat Z
  let p : Z → ℕ := fun a ↦ idx a + analyticOrderNatAt f a
  have ha_ne (a : Z) : (a : ℂ) ≠ 0 := a.2.1
  -- Weighted summability for every `R > 0`: once `‖a‖ > 2 R`,
  -- `m * (1 / 2) ^ (k + m + 1) ≤ (1 / 2) ^ (k + 1)`.
  have hm_sum (R : ℝ) (hR : 0 < R) :
      Summable fun a : Z ↦ (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1) := by
    have hfin_sub : {a : Z | ‖(a : ℂ)‖ ≤ 2 * R}.Finite := by
      refine (Set.finite_image_iff Subtype.val_injective.injOn).mp ?_
      exact (hball_fin (2 * R)).subset fun w ⟨a, haR, hwa⟩ ↦
        ⟨mem_closedBall_zero_iff.mpr (hwa ▸ haR), hwa ▸ a.2.2⟩
    have hgeom : Summable fun a : Z ↦ (1 / 2 : ℝ) ^ (idx a + 1) :=
      ((summable_nat_add_iff 1).mpr summable_geometric_two).comp_injective hidx
    refine hgeom.of_norm_bounded_eventually ?_
    have hev : ∀ᶠ a : Z in cofinite, 2 * R < ‖(a : ℂ)‖ := by
      simpa only [Filter.Eventually, mem_cofinite, Set.compl_ofPred, not_lt] using hfin_sub
    filter_upwards [hev] with a haR
    have ha_pos : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.2.1
    have hhalf : R / ‖(a : ℂ)‖ ≤ 1 / 2 := by
      rw [div_le_iff₀ ha_pos]
      linarith
    have hnonneg : 0 ≤ (analyticOrderNatAt f a : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hR.le ha_pos.le) _)
    rw [Real.norm_of_nonneg hnonneg]
    set m := analyticOrderNatAt f a
    have hm_two : (m : ℝ) * (1 / 2 : ℝ) ^ m ≤ 1 := by
      have hlt : (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast m.lt_two_pow_self.le
      calc (m : ℝ) * (1 / 2 : ℝ) ^ m ≤ (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m :=
            mul_le_mul_of_nonneg_right hlt (by positivity)
        _ = 1 := by rw [← mul_pow]; norm_num
    calc
      (m : ℝ) * (R / ‖(a : ℂ)‖) ^ (p a + 1)
        ≤ (m : ℝ) * (1 / 2 : ℝ) ^ (idx a + m + 1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (div_nonneg hR.le ha_pos.le) hhalf _) (Nat.cast_nonneg _)
      _ = ((m : ℝ) * (1 / 2 : ℝ) ^ m) * (1 / 2 : ℝ) ^ (idx a + 1) := by
          rw [show idx a + m + 1 = m + (idx a + 1) by omega, pow_add]
          ring
      _ ≤ 1 * (1 / 2 : ℝ) ^ (idx a + 1) :=
          mul_le_mul_of_nonneg_right hm_two (by positivity)
      _ = (1 / 2 : ℝ) ^ (idx a + 1) := one_mul _
  -- Construct `F z = z ^ m₀ * P z` and match its analytic order to `f` at every `z : ℂ`.
  set m₀ := analyticOrderNatAt f 0
  let P : ℂ → ℂ := fun z ↦ ∏' a : Z, elementaryFactor (p a) (z / a) ^ analyticOrderNatAt f a
  have hP_diff : Differentiable ℂ P :=
    differentiable_tprod_elementaryFactor_div_pow ha_ne hm_sum
  let F : ℂ → ℂ := fun z ↦ z ^ m₀ * P z
  have hF_diff : Differentiable ℂ F := (differentiable_id.pow m₀).mul hP_diff
  have hP_ne_of_f_ne {z : ℂ} (hfz : f z ≠ 0) : P z ≠ 0 := by
    rw [ne_eq, tprod_elementaryFactor_div_pow_eq_zero_iff ha_ne hm_sum]
    rintro ⟨a, _, rfl⟩
    exact hfz a.2.2
  have hFz₀ : F z₀ ≠ 0 := by
    refine mul_ne_zero ?_ (hP_ne_of_f_ne hz₀)
    by_cases hm₀0 : m₀ = 0
    · simp [hm₀0]
    · refine pow_ne_zero m₀ ?_
      rintro rfl
      exact hm₀0 (by simp [m₀, (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hz₀,
        analyticOrderNatAt])
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
      have hP0 : P 0 ≠ 0 := by simp [P]
      have hpow0 : analyticOrderAt (fun w : ℂ ↦ w ^ m₀) 0 = m₀ := by
        have heq : (fun w : ℂ ↦ w ^ m₀) = (· - (0 : ℂ)) ^ m₀ := by ext w; simp
        rw [heq]
        exact analyticOrderAt_centeredMonomial
      rw [hpow0, (hP_diff.analyticAt 0).analyticOrderAt_eq_zero.mpr hP0, add_zero]
    · have hpow_z : analyticOrderAt (fun w : ℂ ↦ w ^ m₀) z = 0 :=
        (analyticAt_id.pow m₀).analyticOrderAt_eq_zero.mpr (pow_ne_zero m₀ hz)
      rw [hpow_z, zero_add]
      by_cases hfz : f z = 0
      · let a₀ : Z := ⟨z, hz, hfz⟩
        simpa [P, a₀] using (analyticOrderAt_tprod_elementaryFactor_div_pow_of_injective
          ha_ne hm_sum Subtype.val_injective a₀).symm
      · rw [(hP_diff.analyticAt z).analyticOrderAt_eq_zero.mpr (hP_ne_of_f_ne hfz),
          analyticOrderNatAt, (hf.analyticAt z).analyticOrderAt_eq_zero.mpr hfz,
          ENat.toNat_zero, Nat.cast_zero]
  obtain ⟨g, hg, hfg, huniq⟩ := exists_differentiable_eq_exp_mul_of_analyticOrderAt_eq
    hf hF_diff ⟨z₀, hz₀⟩ ⟨z₀, hFz₀⟩ hord
  refine ⟨p, g, hm_sum, hasProdLocallyUniformlyOn_elementaryFactor_div_pow ha_ne hm_sum, hg,
    fun z ↦ ?_, fun g' hg' hfg' ↦ huniq g' hg' fun z ↦ ?_⟩
  · simpa only [F, P, m₀, mul_left_comm (exp (g z)), mul_assoc] using hfg z
  · simpa only [F, P, m₀, mul_left_comm (exp (g' z)), mul_assoc] using hfg' z

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

end TauCeti
