/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import TauCeti.RingTheory.HahnSeries.Valuation
public import TauCeti.RingTheory.LaurentSeries.Convergence
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic

import TauCeti.RingTheory.LaurentSeries.Cartier
import TauCeti.RingTheory.Valuation.Integral.Basic

/-!
# The valuation and topology of the Puiseux field

The Puiseux field `puiseuxField K ⊆ HahnSeries ℚ K` inherits from the rational Hahn series the
additive valuation `ord = orderTop` with values in `WithTop ℚ`, and the multiplicative valuation
`exp (-ord)` with values in `ℚᵐ⁰`. This file restricts both to the Puiseux field and gives it the
resulting valuation topology, through a `Valued` instance.

On the level-`n` copy of `K⸨X⸩`, embedded by `X ↦ t ^ (1 / n)`, the Puiseux order is the integer
order of the Laurent series divided by `n`. Consequently each level embedding is a topological
embedding, that is, a homeomorphism onto its image. Neighbourhoods of zero are described by
orders: `{x | q ≤ ord x}` for `q ∈ ℚ` form a basis, and a family converges to `x` exactly when
the order of its difference with `x` eventually exceeds every rational bound.

Under the `K⟦X⟧`-algebra structure from `Puiseux/Basic.lean`, the integral closure of `K⟦X⟧` in
`puiseuxField K` coincides with the valuation ring `{x | valuation K x ≤ 1}` (equivalently, the
series of nonnegative rational order).

Unlike each level, the Puiseux field is not complete. The partial sums of
`∑ j, t ^ ((j + 1) + 1 / (j + 2))` form a Cauchy sequence, since the orders of the terms tend to
infinity. A limit would have every monomial of this series in its support, by comparing
coefficients, but the denominators `j + 2` of these exponents are unbounded, so no Puiseux series
has them all in its support.

## Main definitions

* `TauCeti.puiseuxField.addVal K`: the additive valuation `ord` on the Puiseux field.
* `TauCeti.puiseuxField.valuation K`: the multiplicative valuation `exp (-ord)`, which defines the
  `Valued` instance on `puiseuxField K`.

## Main results

* `TauCeti.puiseuxField.valuation_lt_one_iff`, `TauCeti.puiseuxField.valuation_le_one_iff`:
  equivalence between valuation bounds at `1` and sign of the rational order.
* `TauCeti.puiseuxField.addVal_levelEmbedding`: on level `n`, the order is the integer order
  divided by `n`.
* `TauCeti.puiseuxField.hasBasis_nhds_zero`: the order balls form a basis of neighbourhoods of
  zero, and `TauCeti.puiseuxField.tendsto_iff_addVal_sub` is the resulting convergence criterion.
* `TauCeti.puiseuxField.isEmbedding_levelEmbedding`: every level embedding is a topological
  embedding.
* `TauCeti.puiseuxField.isIntegral_powerSeries_iff`,
  `TauCeti.puiseuxField.isIntegral_powerSeries_iff_addVal_nonneg`: a Puiseux series is integral
  over `K⟦X⟧` if and only if it lies in the valuation ring.
* `TauCeti.puiseuxField.addVal_sub_algebraMap_coeff_zero_pos_of_addVal_nonneg`: subtracting the
  constant term from a series of nonnegative order gives strictly positive order.
* `TauCeti.puiseuxField.cauchySeq_sum_single`: partial sums of monomials with exponents tending to
  infinity are Cauchy.
* `TauCeti.puiseuxField.not_tendsto_sum_single`: such partial sums have no limit when the
  denominators of the exponents are unbounded.
* `TauCeti.puiseuxField.not_completeSpace`: the Puiseux field is not complete.
-/

public section

open Filter HahnSeries LaurentSeries Topology WithZero
open scoped LaurentSeries PowerSeries

namespace TauCeti

namespace puiseuxField

variable (K : Type*) [Field K]

/-! ### The valuations -/

/-- The additive valuation `ord = orderTop` on the Puiseux field, with values in `WithTop ℚ`. -/
noncomputable def addVal : AddValuation (puiseuxField K) (WithTop ℚ) :=
  (HahnSeries.addVal ℚ K).comap (puiseuxField K).val.toRingHom

/-- The multiplicative valuation on the Puiseux field, sending a nonzero series of order `q` to
`exp (-q)`. -/
noncomputable def valuation : Valuation (puiseuxField K) ℚᵐ⁰ :=
  (HahnSeries.valuation ℚ K).comap (puiseuxField K).val.toRingHom

/-- The Puiseux field carries the valuation topology of `TauCeti.puiseuxField.valuation`. -/
noncomputable instance : Valued (puiseuxField K) ℚᵐ⁰ :=
  Valued.mk' (valuation K)

variable {K}

/-- The additive valuation of a Puiseux series is its order as a rational Hahn series. -/
@[simp]
theorem addVal_apply (x : puiseuxField K) : addVal K x = (x : HahnSeries ℚ K).orderTop :=
  HahnSeries.addVal_apply

/-- The multiplicative valuation of a Puiseux series is its valuation as a rational Hahn series. -/
@[simp]
theorem valuation_apply (x : puiseuxField K) :
    valuation K x = HahnSeries.valuation ℚ K (x : HahnSeries ℚ K) :=
  (rfl)

/-- The valuation of the `Valued` instance is `TauCeti.puiseuxField.valuation`. -/
@[simp]
theorem v_eq_valuation : (Valued.v : Valuation (puiseuxField K) ℚᵐ⁰) = valuation K :=
  (rfl)

/-- The valuation of `x` is below `exp (-q)` exactly when the order of `x` exceeds `q`. -/
theorem valuation_lt_exp_neg_iff (q : ℚ) {x : puiseuxField K} :
    valuation K x < exp (-q) ↔ (q : WithTop ℚ) < addVal K x := by
  rw [valuation_apply, addVal_apply, HahnSeries.valuation_lt_exp_neg_iff]

/-- The valuation of `x` is at most `exp (-q)` exactly when the order of `x` is at least `q`. -/
theorem valuation_le_exp_neg_iff (q : ℚ) {x : puiseuxField K} :
    valuation K x ≤ exp (-q) ↔ (q : WithTop ℚ) ≤ addVal K x := by
  rw [valuation_apply, addVal_apply, HahnSeries.valuation_le_exp_neg_iff]

/-- The valuation of `x` is strictly below `1` exactly when its order is strictly positive. -/
theorem valuation_lt_one_iff {x : puiseuxField K} :
    valuation K x < 1 ↔ 0 < addVal K x := by
  simpa using valuation_lt_exp_neg_iff (K := K) 0 (x := x)

/-- The valuation of `x` is at most `1` exactly when its order is nonnegative. -/
theorem valuation_le_one_iff {x : puiseuxField K} :
    valuation K x ≤ 1 ↔ 0 ≤ addVal K x := by
  simpa using valuation_le_exp_neg_iff (K := K) 0 (x := x)

/-- The monomial `a t ^ q`, for `a ≠ 0`, has order `q`. -/
theorem addVal_single (q : ℚ) {a : K} (ha : a ≠ 0) : addVal K (single K q a) = q := by
  rw [addVal_apply, coe_single, orderTop_single ha]

/-- The monomial `a t ^ q`, for `a ≠ 0`, has valuation `exp (-q)`. -/
theorem valuation_single (q : ℚ) {a : K} (ha : a ≠ 0) :
    valuation K (single K q a) = exp (-q) := by
  rw [valuation_apply, coe_single, HahnSeries.valuation_single q ha]

/-- On level `n`, the order of the Puiseux field is the integer order of `K⸨X⸩` divided by `n`. -/
theorem addVal_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    addVal K (levelEmbedding K n f) = f.orderTop.map fun k : ℤ ↦ (k : ℚ) / n := by
  rw [addVal_apply, coe_levelEmbedding, orderTop_ramifiedEmbedding]

/-- On level `n`, a nonzero Laurent series of order `k` has Puiseux valuation `exp (-(k / n))`. -/
theorem valuation_levelEmbedding (n : ℕ+) {f : K⸨X⸩} (hf : f ≠ 0) :
    valuation K (levelEmbedding K n f) = exp (-((f.order : ℚ) / n)) := by
  have hι : ramifiedEmbedding K n f ≠ 0 :=
    (map_ne_zero_iff _ (ramifiedEmbedding_injective n)).mpr hf
  have hord : (ramifiedEmbedding K n f).order = (f.order : ℚ) / n := by
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero hι, orderTop_ramifiedEmbedding,
      ← order_eq_orderTop_of_ne_zero hf, WithTop.map_coe]
  rw [valuation_apply, coe_levelEmbedding, valuation_eq_exp_neg_order hι, hord]

/-- On level `n`, the order bound `k / n ≤ ord` in the Puiseux field is the integer order bound
`k ≤ ord` in `K⸨X⸩`. -/
theorem div_le_addVal_levelEmbedding_iff (n : ℕ+) (f : K⸨X⸩) (k : ℤ) :
    (((k : ℚ) / n : ℚ) : WithTop ℚ) ≤ addVal K (levelEmbedding K n f) ↔
      (k : WithTop ℤ) ≤ f.orderTop := by
  rw [addVal_levelEmbedding]
  cases f.orderTop with
  | top => simp
  | coe m =>
    rw [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_le_coe,
      div_le_div_iff_of_pos_right (by positivity), Int.cast_le]

/-! ### The valuation topology -/

/-- The order balls `{x | q ≤ ord x}`, for `q ∈ ℚ`, form a basis of neighbourhoods of zero in the
Puiseux field. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : puiseuxField K)).HasBasis (fun _ : ℚ ↦ True)
      fun q ↦ {x | (q : WithTop ℚ) ≤ addVal K x} := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨q, _, hq⟩ ↦ ?_⟩⟩
  · obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
    obtain ⟨k, hk⟩ : ∃ k : ℚ, MonoidWithZeroHom.ValueGroup₀.embedding γ.val = exp (-k) :=
      ⟨-log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val), by
        rw [neg_neg, exp_log (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)]⟩
    refine ⟨k + 1, trivial, fun x hx ↦ hγ ?_⟩
    rw [Set.mem_ofPred_eq, Valued.v.restrict_lt_iff_lt_embedding, hk, v_eq_valuation,
      valuation_lt_exp_neg_iff]
    exact (WithTop.coe_lt_coe.mpr (lt_add_one k)).trans_le hx
  · -- The ball `{x | v x < v (t ^ q)}` is a neighbourhood of zero inside the order ball.
    have hball : {x : puiseuxField K | Valued.v x < Valued.v (single K q 1)} ∈ 𝓝 0 :=
      Valued.mem_nhds_zero.mpr ⟨Units.mk0 (Valued.v.restrict (single K q 1))
        (by simp), fun _ hx ↦ Valued.v.restrict_lt_iff.mp hx⟩
    refine mem_of_superset hball fun x hx ↦ hq ?_
    rw [Set.mem_ofPred_eq, v_eq_valuation, valuation_single q one_ne_zero,
      valuation_lt_exp_neg_iff] at hx
    exact hx.le

/-- **Convergence criterion**: a family of Puiseux series converges to `x` exactly when the order
of its difference with `x` eventually exceeds every rational bound. -/
theorem tendsto_iff_addVal_sub {ι : Type*} {l : Filter ι} (f : ι → puiseuxField K)
    (x : puiseuxField K) :
    Tendsto f l (𝓝 x) ↔ ∀ q : ℚ, ∀ᶠ i in l, (q : WithTop ℚ) ≤ addVal K (f i - x) := by
  rw [← tendsto_sub_nhds_zero_iff, hasBasis_nhds_zero.tendsto_right_iff]
  simp only [forall_const, Set.mem_ofPred_eq]

/-- Every level embedding is continuous. -/
theorem continuous_levelEmbedding (n : ℕ+) : Continuous (levelEmbedding K n) := by
  refine continuous_of_continuousAt_zero (levelEmbedding K n) ?_
  rw [ContinuousAt, map_zero, hasBasis_nhds_zero.tendsto_right_iff]
  intro q _
  filter_upwards [(tendsto_laurentSeries_iff_orderTop_sub id 0).mp tendsto_id ⌈q * n⌉] with f hf
  rw [id, sub_zero] at hf
  refine le_trans ?_ ((div_le_addVal_levelEmbedding_iff n f _).mpr hf)
  exact WithTop.coe_le_coe.mpr ((le_div_iff₀ (by positivity)).mpr (Int.le_ceil _))

/-- The `K⸨X⸩`-algebra map into the Puiseux field is continuous. -/
theorem continuous_algebraMap_laurentSeries : Continuous (algebraMap K⸨X⸩ (puiseuxField K)) := by
  have h : (algebraMap K⸨X⸩ (puiseuxField K) : K⸨X⸩ → puiseuxField K) = levelEmbedding K 1 :=
    funext algebraMap_laurentSeries_apply
  rw [h]
  exact continuous_levelEmbedding 1

/-- Every level embedding is a topological embedding: `K⸨X⸩` is homeomorphic to its level-`n`
image in the Puiseux field. -/
theorem isEmbedding_levelEmbedding (n : ℕ+) : IsEmbedding (levelEmbedding K n) := by
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm ?_ ?_),
    (levelEmbedding K n).toRingHom.injective⟩
  · exact ((continuous_levelEmbedding n).tendsto' 0 0 (map_zero _)).le_comap
  · refine tendsto_id'.mp ((tendsto_laurentSeries_iff_orderTop_sub id 0).mpr fun k ↦ ?_)
    refine eventually_comap.mpr (hasBasis_nhds_zero.eventually_iff.mpr ⟨k / n, trivial, ?_⟩)
    rintro _ hy f rfl
    rw [id, sub_zero]
    exact (div_le_addVal_levelEmbedding_iff n f k).mp hy

/-! ### The valuation ring and integral closure of `K⟦X⟧` -/

/-- Every power series has nonnegative additive valuation in the Puiseux field. -/
theorem addVal_algebraMap_powerSeries_nonneg (f : K⟦X⟧) :
    0 ≤ addVal K (algebraMap K⟦X⟧ (puiseuxField K) f) := by
  rw [algebraMap_powerSeries_apply, algebraMap_laurentSeries_apply]
  have h0 : (0 : WithTop ℤ) ≤ (f : K⸨X⸩).orderTop := by
    rw [PowerSeries.orderTop_coe]
    cases f.order with
    | top => simp
    | coe n => exact WithTop.coe_le_coe.mpr (Nat.cast_nonneg n)
  simpa using (div_le_addVal_levelEmbedding_iff 1 (f : K⸨X⸩) 0).mpr h0

/-- Every power series maps into the valuation ring `{x | valuation K x ≤ 1}` of the Puiseux
field. -/
theorem valuation_algebraMap_powerSeries_le_one (f : K⟦X⟧) :
    valuation K (algebraMap K⟦X⟧ (puiseuxField K) f) ≤ 1 :=
  valuation_le_one_iff.mpr (addVal_algebraMap_powerSeries_nonneg f)

/-- **Integral closure of `K⟦X⟧` in the Puiseux field**: a Puiseux series is integral over `K⟦X⟧`
if and only if its multiplicative valuation is at most `1`. -/
theorem isIntegral_powerSeries_iff {x : puiseuxField K} :
    IsIntegral K⟦X⟧ x ↔ valuation K x ≤ 1 := by
  refine ⟨fun hx ↦ (Subring.integralClosure_le_iff (T := (valuation K).integer)).mpr
      valuation_algebraMap_powerSeries_le_one hx, fun hv ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  have hord : (0 : WithTop ℤ) ≤ f.orderTop :=
    (div_le_addVal_levelEmbedding_iff n f 0).mp (by simpa using valuation_le_one_iff.mp hv)
  obtain ⟨g, rfl⟩ : f ∈ Set.range (ofPowerSeries ℤ K) :=
    TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff.mpr fun k hk ↦
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hk).trans_le hord)
  set u : puiseuxField K := levelEmbedding K n (HahnSeries.single 1 1)
  have hu : IsIntegral K⟦X⟧ u := by
    refine IsIntegral.of_pow n.pos ?_
    rw [← map_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one,
      levelEmbedding_single_self, ← algebraMap_powerSeries_X]
    exact isIntegral_algebraMap
  have hdecomp : levelEmbedding K n (g : K⸨X⸩) =
      ∑ r : Fin n, u ^ (r : ℕ) *
        algebraMap K⟦X⟧ (puiseuxField K) (PowerSeries.cartier K n r g) := by
    conv_lhs => rw [← sum_single_mul_expand_contract n (g : K⸨X⸩)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [map_mul, contract_coe, levelEmbedding_expand_self, ← algebraMap_powerSeries_apply,
      RatFunc.single_zpow, zpow_natCast, map_pow]
  rw [hdecomp]
  exact IsIntegral.sum _ fun r _ ↦ (hu.pow r).mul isIntegral_algebraMap

/-- Additive-valuation form of `isIntegral_powerSeries_iff`: a Puiseux series is integral over
`K⟦X⟧` if and only if its rational order is nonnegative. -/
theorem isIntegral_powerSeries_iff_addVal_nonneg {x : puiseuxField K} :
    IsIntegral K⟦X⟧ x ↔ 0 ≤ addVal K x := by
  rw [isIntegral_powerSeries_iff, valuation_le_one_iff]

/-- Subtracting the constant term from a Puiseux series of nonnegative additive valuation yields a
series of strictly positive additive valuation. -/
theorem addVal_sub_algebraMap_coeff_zero_pos_of_addVal_nonneg {x : puiseuxField K}
    (hx : 0 ≤ addVal K x) :
    0 < addVal K (x - algebraMap K (puiseuxField K) ((x : HahnSeries ℚ K).coeff 0)) := by
  set c : K := (x : HahnSeries ℚ K).coeff 0 with hc_def
  by_cases hsub : x - algebraMap K (puiseuxField K) c = 0
  · simp [hsub]
  have hsub' : ((x - algebraMap K (puiseuxField K) c : puiseuxField K) : HahnSeries ℚ K) ≠ 0 :=
    ZeroMemClass.coe_eq_zero.not.mpr hsub
  rw [addVal_apply, ← order_eq_orderTop_of_ne_zero hsub', WithTop.coe_pos]
  set q := ((x - algebraMap K (puiseuxField K) c : puiseuxField K) : HahnSeries ℚ K).order
  have hq_ne : ((x - algebraMap K (puiseuxField K) c : puiseuxField K) :
      HahnSeries ℚ K).coeff q ≠ 0 := by
    rw [← leadingCoeff_eq]
    exact leadingCoeff_ne_zero.mpr hsub'
  by_contra hle
  rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | hq0
  · have h1 : (x : HahnSeries ℚ K).coeff q = 0 :=
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hlt).trans_le (addVal_apply x ▸ hx))
    have h2 : (algebraMap K (puiseuxField K) c : HahnSeries ℚ K).coeff q = 0 := by
      rw [algebraMap_eq_single, coe_single]
      exact coeff_single_of_ne hlt.ne
    exact hq_ne (by rw [AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, h1, h2, sub_zero])
  · refine hq_ne ?_
    rw [hq0, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub]
    have h2 : (algebraMap K (puiseuxField K) c : HahnSeries ℚ K).coeff 0 = c := by
      rw [algebraMap_eq_single, coe_single]
      exact coeff_single_same 0 c
    rw [h2, ← hc_def, sub_self]

/-! ### Non-completeness -/

/-- Partial sums of monomials whose exponents tend to infinity form a Cauchy sequence. -/
theorem cauchySeq_sum_single {e : ℕ → ℚ} (he : Tendsto e atTop atTop) (c : ℕ → K) :
    CauchySeq fun N : ℕ ↦ ∑ j ∈ Finset.range N, single K (e j) (c j) := by
  refine CauchySeq.comp_tendsto (cauchySeq_finset_iff_sum_vanishing.mpr fun U hU ↦ ?_)
    tendsto_finset_range
  obtain ⟨q, -, hq⟩ := hasBasis_nhds_zero.mem_iff.mp hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually_ge_atTop q)
  refine ⟨Finset.range N, fun t ht ↦ hq ?_⟩
  refine AddValuation.map_le_sum (addVal K) fun j hj ↦ ?_
  have hjN : N ≤ j := by simpa using Finset.disjoint_left.mp ht hj
  rw [addVal_apply, coe_single]
  exact (WithTop.coe_le_coe.mpr (hN j hjN)).trans orderTop_single_le

/-- If the exponents `e j` are distinct and their denominators are not all divisors of a single
positive integer, then partial sums of the monomials `c j t ^ (e j)`, with `c j ≠ 0`, converge to
no Puiseux series: a limit would contain every exponent `e j` in its support. -/
theorem not_tendsto_sum_single {e : ℕ → ℚ} (he : Function.Injective e)
    (hden : ∀ n : ℕ+, ∃ j, ¬ (e j).den ∣ n) {c : ℕ → K} (hc : ∀ j, c j ≠ 0)
    (x : puiseuxField K) :
    ¬ Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.range N, single K (e j) (c j)) atTop (𝓝 x) := by
  intro h
  have hcoeff (j : ℕ) : (x : HahnSeries ℚ K).coeff (e j) = c j := by
    -- Eventually the partial sum contains `c j t ^ (e j)` and agrees with `x` beyond `e j`.
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (((tendsto_iff_addVal_sub _ x).mp h (e j + 1)).and (eventually_gt_atTop j))
    obtain ⟨hord, hjN⟩ := hN N le_rfl
    rw [addVal_apply] at hord
    have h0 := coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr (lt_add_one (e j))).trans_le hord)
    rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, coeff_sub, coeff_sum,
      sub_eq_zero] at h0
    simp_rw [coe_single, coeff_single, he.eq_iff] at h0
    simp [← h0, hjN]
  obtain ⟨n, hn⟩ := mem_puiseuxField_iff_exists_den_dvd.mp x.property
  obtain ⟨j, hj⟩ := hden n
  exact hj (hn (e j) (by rw [mem_support, hcoeff j]; exact hc j))

variable (K) in
/-- **The Puiseux field is not complete.** The partial sums of `∑ j, t ^ ((j + 1) + 1 / (j + 2))`
form a Cauchy sequence without a limit. -/
theorem not_completeSpace : ¬ CompleteSpace (puiseuxField K) := by
  intro _
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_sum_single (K := K) tendsto_unboundedDenExponent fun _ ↦ 1)
  exact not_tendsto_sum_single strictMono_unboundedDenExponent.injective
    (fun n ↦ ⟨n, not_den_unboundedDenExponent_dvd n⟩) (fun _ ↦ one_ne_zero) x hx

end puiseuxField

end TauCeti
