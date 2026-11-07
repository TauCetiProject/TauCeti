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
public import Mathlib.Analysis.Analytic.Order

/-!
# Convergence and multiplicities of genus-one canonical products

If the complex slopes `a i` have summable squared norms, the unordered product
`∏' i, Complex.weierstrassFactorOne (a i * z)` converges uniformly on compact sets and
defines an entire function. Its zeros are exactly the roots of its factors, and its analytic
order counts the factors vanishing there. No enumeration or countability assumption on the
index type is needed.

Natural multiplicities are allowed under the weighted condition `∑ i, m i * ‖a i‖² < ∞`.
For injective slopes, the analytic order at each root is exactly its prescribed multiplicity.
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

/-- Square-summable slopes give uniform convergence of the genus-one product on every compact
set. -/
theorem hasProdUniformlyOn_weierstrassFactorOne {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactorOne (a i * z))
      (fun z ↦ ∏' i, weierstrassFactorOne (a i * z)) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let C : ℝ := max M 1
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hu : Summable (fun i ↦ (3 * C ^ 2) * ‖a i‖ ^ 2) := ha.mul_left _
  have he : ∀ᶠ i in cofinite, ‖a i‖ ^ 2 ≤ (C ^ 2 + 1)⁻¹ :=
    ha.tendsto_cofinite_zero.eventually (ge_mem_nhds (by positivity))
  have hbound : ∀ᶠ i in cofinite, ∀ z ∈ K,
      ‖weierstrassFactorOne (a i * z) - 1‖ ≤ (3 * C ^ 2) * ‖a i‖ ^ 2 := by
    filter_upwards [he] with i hi z hz
    have hzC : ‖z‖ ≤ C := (hM z hz).trans (le_max_left _ _)
    have hsmall : ‖a i‖ * C ≤ 1 := by
      have hp := mul_le_mul_of_nonneg_right hi (sq_nonneg C)
      have hp' : (‖a i‖ * C) ^ 2 ≤ 1 := by
        calc
          _ = (‖a i‖ ^ 2) * C ^ 2 := by ring
          _ ≤ (C ^ 2 + 1)⁻¹ * C ^ 2 := hp
          _ ≤ 1 := by
            rw [inv_mul_le_iff₀ (by positivity)]
            linarith
      nlinarith [mul_nonneg (norm_nonneg (a i)) hC]
    have hzsmall : ‖a i * z‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hzC (norm_nonneg _)).trans hsmall
    calc
      _ ≤ 3 * ‖a i * z‖ ^ 2 := norm_weierstrassFactorOne_sub_one_le hzsmall
      _ ≤ 3 * (‖a i‖ * C) ^ 2 := by
        rw [norm_mul]
        gcongr
      _ = (3 * C ^ 2) * ‖a i‖ ^ 2 := by ring
  have hcts : ∀ i, ContinuousOn (fun z ↦ weierstrassFactorOne (a i * z) - 1) K := by
    intro i
    exact ((differentiable_weierstrassFactorOne.continuous.comp
      (continuous_const.mul continuous_id)).sub continuous_const).continuousOn
  have h := Summable.hasProdUniformlyOn_one_add hK hu hbound hcts
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- The genus-one product converges locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactorOne :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactorOne (a i * z))
      (fun z ↦ ∏' i, weierstrassFactorOne (a i * z)) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasProdUniformlyOn_weierstrassFactorOne a ha hK

/-- A genus-one product with square-summable slopes is entire. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactorOne :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactorOne (a i * z)) := by
  rw [← differentiableOn_univ]
  apply (hasProdLocallyUniformlyOn_weierstrassFactorOne a ha).differentiableOn _ isOpen_univ
  apply Eventually.of_forall
  intro s
  apply Differentiable.differentiableOn
  fun_prop

/-- The deviations of the factors from one form an absolutely summable family at each point. -/
theorem summable_norm_weierstrassFactorOne_sub_one (z : ℂ) :
    Summable (fun i ↦ ‖weierstrassFactorOne (a i * z) - 1‖) := by
  have hz : Summable (fun i ↦ ‖a i * z‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using ha.mul_right (‖z‖ ^ 2)
  apply (hz.mul_left 3).of_norm_bounded_eventually
  filter_upwards [hz.tendsto_cofinite_zero.eventually (ge_mem_nhds zero_lt_one)] with i hi
  rw [Real.norm_eq_abs, abs_norm]
  apply norm_weierstrassFactorOne_sub_one_le
  nlinarith [norm_nonneg (a i * z)]

/-- The genus-one product vanishes exactly at a zero of one of its factors. -/
theorem tprod_weierstrassFactorOne_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactorOne (a i * z)) = 0 ↔ ∃ i, a i * z = 1 := by
  constructor
  · intro h
    by_contra! hn
    have hne : ∀ i, 1 + (weierstrassFactorOne (a i * z) - 1) ≠ 0 := by
      intro i
      simp only [← add_sub_assoc, add_sub_cancel_left]
      exact fun hzero ↦ hn i (weierstrassFactorOne_eq_zero_iff.mp hzero)
    have hp := tprod_one_add_ne_zero_of_summable hne
      (summable_norm_weierstrassFactorOne_sub_one a ha z)
    simp only [← add_sub_assoc, add_sub_cancel_left] at hp
    exact hp h
  · rintro ⟨i, hi⟩
    exact tprod_of_exists_eq_zero ⟨i, weierstrassFactorOne_eq_zero_iff.mpr hi⟩

/-- Only finitely many factors can vanish at a fixed point. -/
theorem finite_weierstrassFactorOne_roots (z : ℂ) :
    {i | a i * z = 1}.Finite := by
  have hz : Summable (fun i ↦ ‖a i * z‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using ha.mul_right (‖z‖ ^ 2)
  have he : ∀ᶠ i in cofinite, a i * z ≠ 1 := by
    filter_upwards [hz.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)] with i hi
    intro h
    simp only [h, norm_one, one_pow, lt_self_iff_false] at hi
  simpa only [Filter.Eventually, mem_cofinite, Set.compl_ofPred, not_not] using he

omit ha in
private theorem analyticOrderAt_finsetProd_weierstrassFactorOne {z : ℂ}
    (s : Finset ι) (hs : ∀ i ∈ s, a i * z = 1) :
    analyticOrderAt (fun w ↦ ∏ i ∈ s, weierstrassFactorOne (a i * w)) z = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | @insert i s hi ih =>
    have heq : (fun w ↦ ∏ j ∈ insert i s, weierstrassFactorOne (a j * w)) =
        (fun w ↦ weierstrassFactorOne (a i * w)) *
        (fun w ↦ ∏ j ∈ s, weierstrassFactorOne (a j * w)) := by
      funext w
      simp [Finset.prod_insert hi]
    have h1 : AnalyticAt ℂ (fun w ↦ weierstrassFactorOne (a i * w)) z := by fun_prop
    have h2 : AnalyticAt ℂ (fun w ↦ ∏ j ∈ s, weierstrassFactorOne (a j * w)) z := by
      fun_prop
    rw [heq, analyticOrderAt_mul h1 h2,
      analyticOrderAt_weierstrassFactorOne_mul (hs i (Finset.mem_insert_self _ _)),
      ih (fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)), Finset.card_insert_of_notMem hi]
    simp [add_comm]

/-- The product order is the cardinality of any finite set containing exactly its vanishing
factors. -/
theorem analyticOrderAt_tprod_weierstrassFactorOne_of_finset {z : ℂ} (s : Finset ι)
    (hs : ∀ i, a i * z = 1 ↔ i ∈ s) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactorOne (a i * w)) z = s.card := by
  classical
  have htail := differentiable_tprod_weierstrassFactorOne
    (fun i : {i // i ∉ s} ↦ a i) (ha.subtype _)
  have htailAnalytic := htail.analyticAt z
  have htailNe : (∏' i : {i // i ∉ s}, weierstrassFactorOne (a i * z)) ≠ 0 := by
    rw [ne_eq, tprod_weierstrassFactorOne_eq_zero_iff _ (ha.subtype _) z]
    rintro ⟨i, hi⟩
    exact i.property ((hs i).mp hi)
  have hprodAnalytic : AnalyticAt ℂ
      (fun w ↦ ∏ i ∈ s, weierstrassFactorOne (a i * w)) z := by fun_prop
  -- Isolate the finitely many vanishing factors; the complementary product is a unit.
  have heq : (fun w ↦ ∏' i, weierstrassFactorOne (a i * w)) =
      (fun w ↦ ∏ i ∈ s, weierstrassFactorOne (a i * w)) *
      (fun w ↦ ∏' i : {i // i ∉ s}, weierstrassFactorOne (a i * w)) := by
    funext w
    have htailProd : Multipliable
        (fun i : {i // i ∉ s} ↦ weierstrassFactorOne (a i * w)) :=
      ((hasProdLocallyUniformlyOn_weierstrassFactorOne
        (fun i : {i // i ∉ s} ↦ a i) (ha.subtype _)).hasProd (Set.mem_univ w)).multipliable
    have hsplit := Multipliable.tprod_mul_tprod_compl
      (s := (s : Set ι)) (f := fun i ↦ weierstrassFactorOne (a i * w))
      Multipliable.of_finite htailProd
    rw [s.tprod_subtype' (fun i ↦ weierstrassFactorOne (a i * w))] at hsplit
    exact hsplit.symm
  rw [heq, analyticOrderAt_mul hprodAnalytic htailAnalytic,
    analyticOrderAt_finsetProd_weierstrassFactorOne a s (fun i hi ↦ (hs i).mpr hi),
    htailAnalytic.analyticOrderAt_eq_zero.mpr htailNe, add_zero]

/-- The order of the product counts all factors vanishing at that point. -/
theorem analyticOrderAt_tprod_weierstrassFactorOne (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, weierstrassFactorOne (a i * w)) z =
      ({i | a i * z = 1}.ncard : ℕ∞) := by
  have hf := finite_weierstrassFactorOne_roots a ha z
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact analyticOrderAt_tprod_weierstrassFactorOne_of_finset a ha hf.toFinset
    (fun i ↦ hf.mem_toFinset.symm)

end Complex

namespace Complex

variable {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
  (hm : Summable (fun i ↦ (m i : ℝ) * ‖a i‖ ^ 2))

include hm

private theorem summable_sigma_norm_sq_weierstrass :
    Summable (fun p : Σ i, Fin (m i) ↦ ‖a p.1‖ ^ 2) :=
  (summable_sigma_fin_iff (fun i ↦ sq_nonneg ‖a i‖) m).mpr hm

private theorem tprod_weierstrassFactorOne_pow_eq_sigma (z : ℂ) :
    (∏' i, weierstrassFactorOne (a i * z) ^ m i) =
      ∏' p : Σ i, Fin (m i), weierstrassFactorOne (a p.1 * z) := by
  have hσ := summable_sigma_norm_sq_weierstrass a m hm
  have hp := ((hasProdLocallyUniformlyOn_weierstrassFactorOne
    (fun p : Σ i, Fin (m i) ↦ a p.1) hσ).hasProd (Set.mem_univ z)).multipliable
  rw [Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) hp]
  simp

/-- A product with natural multiplicities is entire under weighted square summability. -/
@[fun_prop]
theorem differentiable_tprod_weierstrassFactorOne_pow :
    Differentiable ℂ (fun z ↦ ∏' i, weierstrassFactorOne (a i * z) ^ m i) := by
  have heq : (fun z ↦ ∏' i, weierstrassFactorOne (a i * z) ^ m i) =
      (fun z ↦ ∏' p : Σ i, Fin (m i), weierstrassFactorOne (a p.1 * z)) :=
    funext (tprod_weierstrassFactorOne_pow_eq_sigma a m hm)
  rw [heq]
  exact differentiable_tprod_weierstrassFactorOne _
    (summable_sigma_norm_sq_weierstrass a m hm)

/-- For distinct slopes, the prescribed multiplicity is the exact order at the corresponding
root. -/
theorem analyticOrderAt_tprod_weierstrassFactorOne_pow {z : ℂ} {i : ι}
    (ha : Function.Injective a) (hi : a i * z = 1) :
    analyticOrderAt (fun w ↦ ∏' j, weierstrassFactorOne (a j * w) ^ m j) z = m i := by
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
  have heq : (fun w ↦ ∏' j, weierstrassFactorOne (a j * w) ^ m j) =
      (fun w ↦ ∏' p : Σ j, Fin (m j), weierstrassFactorOne (a p.1 * w)) :=
    funext (tprod_weierstrassFactorOne_pow_eq_sigma a m hm)
  rw [heq, analyticOrderAt_tprod_weierstrassFactorOne_of_finset _
    (summable_sigma_norm_sq_weierstrass a m hm) s hs]
  simp [s]

/-- Products with natural multiplicities converge uniformly on every compact set. -/
theorem hasProdUniformlyOn_weierstrassFactorOne_pow {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ weierstrassFactorOne (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactorOne (a i * z) ^ m i) K := by
  classical
  have ht : Tendsto (fun s : Finset ι ↦ s.sigma (fun i ↦ Finset.univ : ∀ i, Finset (Fin (m i))))
      atTop atTop := by
    refine tendsto_atTop.mpr fun t ↦ eventually_atTop.mpr ⟨t.image Sigma.fst, ?_⟩
    intro s hs p hp
    exact Finset.mem_sigma.mpr ⟨hs (Finset.mem_image.mpr ⟨p, hp, rfl⟩), Finset.mem_univ _⟩
  have h0 := HasProdUniformlyOn.tendstoUniformlyOn
    (hasProdUniformlyOn_weierstrassFactorOne
      (fun p : Σ i, Fin (m i) ↦ a p.1) (summable_sigma_norm_sq_weierstrass a m hm) hK)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  intro u hu
  filter_upwards [ht.eventually (h0 u hu)] with s hs z hz
  have hsz := hs z hz
  simpa only [← tprod_weierstrassFactorOne_pow_eq_sigma a m hm,
    Finset.prod_sigma, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hsz

/-- Products with natural multiplicities converge locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_weierstrassFactorOne_pow :
    HasProdLocallyUniformlyOn (fun i z ↦ weierstrassFactorOne (a i * z) ^ m i)
      (fun z ↦ ∏' i, weierstrassFactorOne (a i * z) ^ m i) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasProdUniformlyOn_weierstrassFactorOne_pow a m hm hK

/-- The weighted product vanishes exactly at a root whose prescribed multiplicity is nonzero. -/
theorem tprod_weierstrassFactorOne_pow_eq_zero_iff (z : ℂ) :
    (∏' i, weierstrassFactorOne (a i * z) ^ m i) = 0 ↔
      ∃ i, m i ≠ 0 ∧ a i * z = 1 := by
  rw [tprod_weierstrassFactorOne_pow_eq_sigma a m hm,
    tprod_weierstrassFactorOne_eq_zero_iff _ (summable_sigma_norm_sq_weierstrass a m hm)]
  constructor
  · rintro ⟨⟨i, k⟩, hi⟩
    exact ⟨i, Nat.ne_zero_of_lt k.isLt, hi⟩
  · rintro ⟨i, hmi, hi⟩
    exact ⟨⟨i, ⟨0, Nat.pos_of_ne_zero hmi⟩⟩, hi⟩

end Complex

