/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import TauCeti.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Analytic.Order
import TauCeti.Order.Filter.AtTopBot.Finset

/-!
# Convergence and multiplicities of genus-one canonical products

If the complex slopes `a i` have summable squared norms, the unordered product
`∏' i, Complex.weierstrassFactor 1 (a i * z)` converges uniformly on compact sets and
defines an entire function. Its zeros are exactly the roots of its factors, and its analytic
order counts the factors vanishing there. No enumeration or countability assumption on the
index type is needed.

Natural multiplicities are allowed under the weighted condition `∑ i, m i * ‖a i‖² < ∞`.
The grouped product of the powers `E₁(a i * z) ^ m i` and the repeated-index product over
`Σ i, Fin (m i)` converge locally uniformly to the same entire function.
The analytic order counts the repeated vanishing factors; for injective slopes this is exactly
the prescribed multiplicity.
These are the convergence and divisor ingredients of Hadamard factorization at order one.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (ha : Summable (fun i ↦ ‖a i‖ ^ 2))

include ha

/-- Square-summable slopes give uniform convergence of the genus-one product on every bounded
set. -/
theorem hasProdUniformlyOn_weierstrassFactor_one {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z))
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z)) K := by
  obtain ⟨M, hM⟩ := hK.isCompact_closure.exists_bound_of_continuousOn continuous_id.continuousOn
  let C : ℝ := max M 1
  have hu : Summable (fun i ↦ (C ^ 2) * ‖a i‖ ^ 2) := ha.mul_left _
  have hbound : ∀ᶠ i in cofinite, ∀ z ∈ closure K,
      ‖weierstrassFactor 1 (a i * z) - 1‖ ≤ (C ^ 2) * ‖a i‖ ^ 2 := by
    filter_upwards [TauCeti.eventually_mul_le_one_of_summable_sq ha C] with i hsmall z hz
    have hzC : ‖z‖ ≤ C := (hM z hz).trans (le_max_left _ _)
    have hzsmall : ‖a i * z‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hzC (norm_nonneg _)).trans hsmall
    calc
      _ ≤ ‖a i * z‖ ^ 2 := norm_weierstrassFactor_sub_one_le 1 hzsmall
      _ ≤ (‖a i‖ * C) ^ 2 := by
        rw [norm_mul]
        gcongr
      _ = (C ^ 2) * ‖a i‖ ^ 2 := by ring
  have hcts : ∀ i, ContinuousOn (fun z ↦ weierstrassFactor 1 (a i * z) - 1) (closure K) := by
    intro i
    exact (((differentiable_weierstrassFactor 1).continuous.comp
      (continuous_const.mul continuous_id)).sub continuous_const).continuousOn
  have h := Summable.hasProdUniformlyOn_one_add hK.isCompact_closure hu hbound hcts
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h.mono subset_closure

/-- The genus-one product converges locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_one :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z))
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z)) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasProdUniformlyOn_weierstrassFactor_one a ha hK.isBounded

/-- A genus-one product with square-summable slopes is entire. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_one :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z)) := by
  rw [← differentiableOn_univ]
  apply (hasProdLocallyUniformlyOn_weierstrassFactor_one a ha).differentiableOn _ isOpen_univ
  apply Eventually.of_forall
  intro s
  apply Differentiable.differentiableOn
  fun_prop

/-- The deviations of the factors from one form an absolutely summable family at each point. -/
theorem summable_norm_weierstrassFactor_one_sub_one (z : ℂ) :
    Summable (fun i ↦ ‖weierstrassFactor 1 (a i * z) - 1‖) := by
  have hz : Summable (fun i ↦ ‖a i * z‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using ha.mul_right (‖z‖ ^ 2)
  apply hz.of_norm_bounded_eventually
  filter_upwards [hz.tendsto_cofinite_zero.eventually (ge_mem_nhds zero_lt_one)] with i hi
  rw [Real.norm_eq_abs, abs_norm]
  apply norm_weierstrassFactor_sub_one_le 1
  nlinarith [norm_nonneg (a i * z)]

/-- The genus-one product vanishes exactly at a zero of one of its factors. -/
theorem tprod_weierstrassFactor_one_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z)) = 0 ↔ ∃ i, a i * z = 1 := by
  constructor
  · intro h
    by_contra! hn
    have hne : ∀ i, 1 + (weierstrassFactor 1 (a i * z) - 1) ≠ 0 := by
      intro i
      simp only [← add_sub_assoc, add_sub_cancel_left]
      exact fun hzero ↦ hn i ((weierstrassFactor_eq_zero_iff 1).mp hzero)
    have hp := tprod_one_add_ne_zero_of_summable hne
      (summable_norm_weierstrassFactor_one_sub_one a ha z)
    simp only [← add_sub_assoc, add_sub_cancel_left] at hp
    exact hp h
  · rintro ⟨i, hi⟩
    exact tprod_of_exists_eq_zero ⟨i, (weierstrassFactor_eq_zero_iff 1).mpr hi⟩

/-- Only finitely many factors can vanish at a fixed point. -/
theorem finite_weierstrassFactor_one_roots (z : ℂ) :
    {i | a i * z = 1}.Finite := by
  have hz : Summable (fun i ↦ ‖a i * z‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using ha.mul_right (‖z‖ ^ 2)
  have he : ∀ᶠ i in cofinite, a i * z ≠ 1 := by
    filter_upwards [hz.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)] with i hi
    intro h
    simp only [h, norm_one, one_pow, lt_self_iff_false] at hi
  simpa only [Filter.Eventually, mem_cofinite, Set.compl_ofPred, not_not] using he

omit ha in
private theorem analyticOrderAt_finsetProd_weierstrassFactor_one {z : ℂ}
    (s : Finset ι) (hs : ∀ i ∈ s, a i * z = 1) :
    analyticOrderAt (fun w ↦ ∏ i ∈ s, weierstrassFactor 1 (a i * w)) z = s.card := by
  have heq : (fun w ↦ ∏ i ∈ s, weierstrassFactor 1 (a i * w)) =
      ∏ i ∈ s, (fun w ↦ weierstrassFactor 1 (a i * w)) := by ext w; simp
  rw [heq, TauCeti.analyticOrderAt_prod (fun _ _ ↦ by fun_prop)]
  calc
    _ = ∑ _i ∈ s, (1 : ℕ∞) := Finset.sum_congr rfl fun i hi ↦
      analyticOrderAt_weierstrassFactor_mul 1 (hs i hi)
    _ = _ := by simp

/-- The product order is the cardinality of any finite set containing exactly its vanishing
factors. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_of_finset {z : ℂ} (s : Finset ι)
    (hs : ∀ i, a i * z = 1 ↔ i ∈ s) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) z = s.card := by
  classical
  have htail := differentiable_tprod_weierstrassFactor_one
    (fun i : {i // i ∉ s} ↦ a i) (ha.subtype _)
  have htailAnalytic := htail.analyticAt z
  have htailNe : (∏' i : {i // i ∉ s}, weierstrassFactor 1 (a i * z)) ≠ 0 := by
    rw [ne_eq, tprod_weierstrassFactor_one_eq_zero_iff _ (ha.subtype _) z]
    rintro ⟨i, hi⟩
    exact i.property ((hs i).mp hi)
  have hprodAnalytic : AnalyticAt ℂ
      (fun w ↦ ∏ i ∈ s, weierstrassFactor 1 (a i * w)) z := by fun_prop
  -- Isolate the finitely many vanishing factors; the complementary product is a unit.
  have heq : (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) =
      (fun w ↦ ∏ i ∈ s, weierstrassFactor 1 (a i * w)) *
      (fun w ↦ ∏' i : {i // i ∉ s}, weierstrassFactor 1 (a i * w)) := by
    funext w
    have htailProd : Multipliable
        (fun i : {i // i ∉ s} ↦ weierstrassFactor 1 (a i * w)) :=
      ((hasProdLocallyUniformlyOn_weierstrassFactor_one
        (fun i : {i // i ∉ s} ↦ a i) (ha.subtype _)).hasProd (Set.mem_univ w)).multipliable
    have hsplit := Multipliable.tprod_mul_tprod_compl
      (s := (s : Set ι)) (f := fun i ↦ weierstrassFactor 1 (a i * w))
      Multipliable.of_finite htailProd
    rw [s.tprod_subtype' (fun i ↦ weierstrassFactor 1 (a i * w))] at hsplit
    exact hsplit.symm
  rw [heq, analyticOrderAt_mul hprodAnalytic htailAnalytic,
    analyticOrderAt_finsetProd_weierstrassFactor_one a s (fun i hi ↦ (hs i).mpr hi),
    htailAnalytic.analyticOrderAt_eq_zero.mpr htailNe, add_zero]

/-- The order of the product counts all factors vanishing at that point. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactor 1 (a i * w)) z =
      ({i | a i * z = 1}.ncard : ℕ∞) := by
  have hf := finite_weierstrassFactor_one_roots a ha z
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact analyticOrderAt_tprod_weierstrassFactor_one_of_finset a ha hf.toFinset
    (fun i ↦ hf.mem_toFinset.symm)

end Complex

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
  (hm : Summable (fun i ↦ (m i : ℝ) * ‖a i‖ ^ 2))

include hm

private theorem summable_sigma_norm_sq_weierstrass :
    Summable (fun p : Σ i, Fin (m i) ↦ ‖a p.1‖ ^ 2) :=
  (TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm

/-- The product with natural multiplicities is the product over the repeated index
`Σ i, Fin (m i)`, in which the slope `a i` occurs `m i` times. -/
theorem tprod_weierstrassFactor_one_pow_eq_tprod_sigma (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z) ^ m i) =
      ∏' p : Σ i, Fin (m i), weierstrassFactor 1 (a p.1 * z) := by
  have hσ := summable_sigma_norm_sq_weierstrass a m hm
  have hp := ((hasProdLocallyUniformlyOn_weierstrassFactor_one
    (fun p : Σ i, Fin (m i) ↦ a p.1) hσ).hasProd (Set.mem_univ z)).multipliable
  rw [Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) hp]
  simp

/-- A product with natural multiplicities is entire under weighted square summability. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactor_one_pow :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) := by
  have heq : (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) =
      (fun z ↦ ∏' p : Σ i, Fin (m i), weierstrassFactor 1 (a p.1 * z)) :=
    funext (tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm)
  rw [heq]
  exact differentiable_tprod_weierstrassFactor_one _
    (summable_sigma_norm_sq_weierstrass a m hm)

/-- With arbitrary repeated slopes, the order counts the vanishing factors with their
natural multiplicities, represented by the finite fibers of the multiplicity family. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_pow (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) z =
      ({p : Σ j, Fin (m j) | a p.1 * z = 1}.ncard : ℕ∞) := by
  have heq : (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) =
      (fun w ↦ ∏' p : Σ j, Fin (m j), weierstrassFactor 1 (a p.1 * w)) :=
    funext (tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm)
  rw [heq]
  exact analyticOrderAt_tprod_weierstrassFactor_one _
    (summable_sigma_norm_sq_weierstrass a m hm) z

/-- For distinct slopes, the prescribed multiplicity is the exact order at the corresponding
root. -/
theorem analyticOrderAt_tprod_weierstrassFactor_one_pow_of_injective {z : ℂ} {i : ι}
    (ha : Function.Injective a) (hi : a i * z = 1) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactor 1 (a j * w) ^ m j) z = m i := by
  classical
  have hz : z ≠ 0 := by intro hz; simp [hz] at hi
  let s : Finset (Σ j, Fin (m j)) := Finset.univ.map
    ⟨Sigma.mk i, sigma_mk_injective⟩
  have hs : ∀ p : Σ j, Fin (m j), a p.1 * z = 1 ↔ p ∈ s := by
    rintro ⟨j, k⟩
    simp only [s, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · intro hj
      have hji : j = i := ha (mul_right_cancel₀ hz (hj.trans hi.symm))
      subst j
      exact ⟨k, rfl⟩
    · rintro ⟨l, heq⟩
      cases heq
      exact hi
  rw [analyticOrderAt_tprod_weierstrassFactor_one_pow a m hm z]
  have hset : {p : Σ j, Fin (m j) | a p.1 * z = 1} = (s : Set (Σ j, Fin (m j))) := by
    ext p
    exact hs p
  rw [hset, Set.ncard_coe_finset]
  simp [s]

/-- Products with natural multiplicities converge uniformly on every bounded set. -/
theorem hasProdUniformlyOn_weierstrassFactor_one_pow {K : Set ℂ} (hK : Bornology.IsBounded K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) K := by
  have h0 := HasProdUniformlyOn.tendstoUniformlyOn
    (hasProdUniformlyOn_weierstrassFactor_one
      (fun p : Σ i, Fin (m i) ↦ a p.1) (summable_sigma_norm_sq_weierstrass a m hm) hK)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  intro u hu
  filter_upwards [(TauCeti.tendsto_finset_sigma_univ_atTop (κ := fun i ↦ Fin (m i))).eventually
    (h0 u hu)] with s hs z hz
  have hsz := hs z hz
  simpa only [← tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm,
    Finset.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hsz

/-- Products with natural multiplicities converge locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactor_one_pow :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactor 1 (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasProdUniformlyOn_weierstrassFactor_one_pow a m hm hK.isBounded

/-- The repeated-index product, in which the slope `a i` occurs `m i` times, converges locally
uniformly on the whole plane to the product with natural multiplicities. -/
theorem hasProdLocallyUniformlyOn_sigma_weierstrassFactor_one :
    HasProdLocallyUniformlyOn (fun (p : Σ i, Fin (m i)) z ↦ weierstrassFactor 1 (a p.1 * z))
      (fun z ↦ ∏' i, weierstrassFactor 1 (a i * z) ^ m i) Set.univ := by
  rw [funext (tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm)]
  exact hasProdLocallyUniformlyOn_weierstrassFactor_one _
    (summable_sigma_norm_sq_weierstrass a m hm)

/-- The weighted product vanishes exactly at a root whose prescribed multiplicity is nonzero. -/
theorem tprod_weierstrassFactor_one_pow_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactor 1 (a i * z) ^ m i) = 0 ↔
      ∃ i, m i ≠ 0 ∧ a i * z = 1 := by
  rw [tprod_weierstrassFactor_one_pow_eq_tprod_sigma a m hm,
    tprod_weierstrassFactor_one_eq_zero_iff _ (summable_sigma_norm_sq_weierstrass a m hm)]
  constructor
  · rintro ⟨⟨i, k⟩, hi⟩
    exact ⟨i, Nat.ne_zero_of_lt k.isLt, hi⟩
  · rintro ⟨i, hmi, hi⟩
    exact ⟨⟨i, ⟨0, Nat.pos_of_ne_zero hmi⟩⟩, hi⟩

end Complex

