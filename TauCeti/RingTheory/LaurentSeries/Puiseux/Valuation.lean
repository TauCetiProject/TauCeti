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

import Mathlib.RingTheory.PowerSeries.Trunc

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

Unlike each level, the Puiseux field is not complete. The partial sums of
`∑ j, t ^ ((j + 1) + 1 / (j + 2))` form a Cauchy sequence, since the orders of the terms tend to
infinity. A limit would have every monomial of this series in its support, by comparing
coefficients, but the denominators `j + 2` of these exponents are unbounded, so no Puiseux series
has them all in its support.

Finally, any ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` sending `K⟦X⟧` into the
valuation ring multiplies every order by the rational order `q ≥ 0` of `ρ t`: on each ramified
level `K⸨u⸩` with `u ^ d = t`, decomposing power series in `u` into congruence classes modulo `d`
shows they map into the valuation ring, so units map to order zero and powers of `u` determine all
orders. When `q > 0`, `ρ` is a topological embedding. For a `K`-algebra endomorphism `ρ` of
`puiseuxField K`, mapping `K⟦X⟧` into the valuation ring forces `q > 0` because `X - c` is a unit
of `K⟦X⟧` for every `c ≠ 0`; conversely continuity implies that polynomial truncations of any
power series converge under `ρ`, characterizing continuous `K`-algebra endomorphisms as those
mapping `K⟦X⟧` (equivalently the Puiseux valuation ring) into the valuation ring.

## Main definitions

* `TauCeti.puiseuxField.addVal K`: the additive valuation `ord` on the Puiseux field.
* `TauCeti.puiseuxField.valuation K`: the multiplicative valuation `exp (-ord)`, which defines the
  `Valued` instance on `puiseuxField K`.

## Main results

* `TauCeti.puiseuxField.addVal_levelEmbedding`: on level `n`, the order is the integer order
  divided by `n`.
* `TauCeti.puiseuxField.hasBasis_nhds_zero`: the order balls form a basis of neighbourhoods of
  zero, and `TauCeti.puiseuxField.tendsto_iff_addVal_sub` is the resulting convergence criterion.
* `TauCeti.puiseuxField.isEmbedding_levelEmbedding`: every level embedding is a topological
  embedding.
* `TauCeti.puiseuxField.cauchySeq_sum_single`: partial sums of monomials with exponents tending to
  infinity are Cauchy.
* `TauCeti.puiseuxField.not_tendsto_sum_single`: such partial sums have no limit when the
  denominators of the exponents are unbounded.
* `TauCeti.puiseuxField.not_completeSpace`: the Puiseux field is not complete.
* `TauCeti.puiseuxField.addVal_ringHom_apply` and
  `TauCeti.puiseuxField.isEmbedding_of_order_ringHom_single_one_pos`: a ring homomorphism
  nonnegative on `K⟦X⟧` multiplies orders by `ord (ρ t)` and is a topological embedding when
  `ord (ρ t) > 0`.
* `TauCeti.puiseuxField.continuous_algHom_iff`,
  `TauCeti.puiseuxField.continuous_algHom_iff_addVal_nonneg`, and
  `TauCeti.puiseuxField.isEmbedding_of_continuous_algHom`: continuous `K`-algebra endomorphisms of
  `puiseuxField K` are characterized by preserving nonnegative orders and are topological
  embeddings.
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
    obtain ⟨k, hk⟩ : ∃ k : ℚ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp (-k) :=
      ⟨-log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1), by
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
  obtain ⟨n, hn⟩ := mem_puiseuxField_iff_exists_den_dvd.mp x.2
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

/-! ### Valuation scaling and continuity of homomorphisms -/

/-- A Puiseux series lies in the valuation ring `v x ≤ 1` exactly when its order is nonnegative. -/
theorem valuation_le_one_iff {x : puiseuxField K} : valuation K x ≤ 1 ↔ 0 ≤ addVal K x := by
  simpa using valuation_le_exp_neg_iff (K := K) 0 (x := x)

/-- The order of a constant `algebraMap K (puiseuxField K) c` is nonnegative. -/
theorem addVal_algebraMap_nonneg (c : K) : 0 ≤ addVal K (algebraMap K (puiseuxField K) c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h : algebraMap K (puiseuxField K) c = single K 0 c :=
      Subtype.ext (by simp [HahnSeries.algebraMap_apply'])
    rw [h, addVal_single 0 hc]
    rfl

/-- Raising a nonzero Puiseux series to an integer power multiplies its order by that integer. -/
theorem addVal_zpow {x : puiseuxField K} (hx : x ≠ 0) (k : ℤ) :
    addVal K (x ^ k) = (((x : HahnSeries ℚ K).order * k : ℚ) : WithTop ℚ) := by
  have hx0 : (x : HahnSeries ℚ K) ≠ 0 := by exact_mod_cast hx
  have hxk0 : ((x ^ k : puiseuxField K) : HahnSeries ℚ K) ≠ 0 := by
    exact_mod_cast zpow_ne_zero k hx
  have hv : valuation K (x ^ k) = exp (-((k : ℚ) * (x : HahnSeries ℚ K).order)) := by
    rw [map_zpow₀, valuation_apply, valuation_eq_exp_neg_order hx0, ← exp_zsmul, smul_neg,
      zsmul_eq_mul]
  rw [valuation_apply, valuation_eq_exp_neg_order hxk0, exp_inj, neg_inj] at hv
  rw [addVal_apply, ← order_eq_orderTop_of_ne_zero hxk0, hv, mul_comm]

section RingHom

variable {L : Type*} [Field L] (ρ : puiseuxField K →+* puiseuxField L)

/-- A ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` sending `K⟦X⟧` into the valuation
ring sends the parameter `t` to a series of nonnegative rational order. -/
theorem order_ringHom_single_one_nonneg
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩)))) :
    0 ≤ (ρ (single K 1 1) : HahnSeries ℚ L).order := by
  have ht : algebraMap K⸨X⸩ (puiseuxField K) ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) = single K 1 1 := by
    rw [ofPowerSeries_X, algebraMap_laurentSeries_apply]
    exact levelEmbedding_single_self 1
  have hs0 : (ρ (single K 1 1) : HahnSeries ℚ L) ≠ 0 := by
    exact_mod_cast (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  have h := hρ PowerSeries.X
  rwa [ht, addVal_apply, ← order_eq_orderTop_of_ne_zero hs0, ← WithTop.coe_zero,
    WithTop.coe_le_coe] at h

/-- If a ring homomorphism maps all power series on level `d` to nonnegative order, then it maps
every unit power series on level `d` to order zero. -/
private theorem addVal_ringHom_levelEmbedding_coe_of_isUnit {d : ℕ+}
    (hd : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (levelEmbedding K d (f : K⸨X⸩)))) {u : K⟦X⟧}
    (hu : IsUnit u) :
    addVal L (ρ (levelEmbedding K d (u : K⸨X⸩))) = 0 := by
  obtain ⟨v, rfl⟩ := hu
  have h1 := hd v
  have h2 := hd ↑v⁻¹
  have hmul : addVal L (ρ (levelEmbedding K d (v : K⸨X⸩))) +
      addVal L (ρ (levelEmbedding K d ((↑v⁻¹ : K⟦X⟧) : K⸨X⸩))) = 0 := by
    rw [← (addVal L).map_mul, ← map_mul, ← map_mul, ← PowerSeries.coe_mul, Units.mul_inv,
      PowerSeries.coe_one, map_one, map_one, (addVal L).map_one]
  cases ha : addVal L (ρ (levelEmbedding K d (v : K⸨X⸩))) with
  | top => rw [ha] at hmul; exact absurd hmul (by simp)
  | coe a =>
    cases hb : addVal L (ρ (levelEmbedding K d ((↑v⁻¹ : K⟦X⟧) : K⸨X⸩))) with
    | top => rw [ha, hb] at hmul; exact absurd hmul (by simp)
    | coe b =>
      rw [ha, ← WithTop.coe_zero, WithTop.coe_le_coe] at h1
      rw [hb, ← WithTop.coe_zero, WithTop.coe_le_coe] at h2
      rw [ha, hb, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hmul
      exact WithTop.coe_eq_coe.mpr (by linarith)

private theorem map_levelEmbedding_single_one_ne_zero (d : ℕ+) :
    ρ (levelEmbedding K d (HahnSeries.single 1 1)) ≠ 0 :=
  (map_ne_zero_iff ρ ρ.injective).mpr <|
    (map_ne_zero_iff _ (levelEmbedding K d).injective).mpr
      (HahnSeries.single_eq_zero_iff.not.mpr one_ne_zero)

private theorem order_ringHom_levelEmbedding_single_one (d : ℕ+) :
    (ρ (levelEmbedding K d (HahnSeries.single 1 1)) : HahnSeries ℚ L).order =
      (ρ (single K 1 1) : HahnSeries ℚ L).order / d := by
  have hud : levelEmbedding K d (HahnSeries.single 1 1) ^ (d : ℕ) = single K 1 1 := by
    rw [← map_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one,
      levelEmbedding_single_self]
  rw [← hud, map_pow, IntermediateField.coe_pow, HahnSeries.order_pow, nsmul_eq_mul,
    mul_div_cancel_left₀ _ (by exact_mod_cast d.ne_zero)]

/-- If `ρ` sends `K⟦X⟧` into the valuation ring, then it sends power series on every ramified level
into the valuation ring. -/
private theorem addVal_ringHom_levelEmbedding_coe_nonneg
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    (d : ℕ+) (f : K⟦X⟧) :
    0 ≤ addVal L (ρ (levelEmbedding K d (f : K⸨X⸩))) := by
  have hqu : 0 ≤ (ρ (levelEmbedding K d (HahnSeries.single 1 1)) : HahnSeries ℚ L).order := by
    rw [order_ringHom_levelEmbedding_single_one]
    exact div_nonneg (order_ringHom_single_one_nonneg ρ hρ) (by positivity)
  rw [← sum_single_mul_expand_contract d (f : K⸨X⸩), map_sum, map_sum]
  refine AddValuation.map_le_sum (addVal L) fun r _ ↦ ?_
  obtain ⟨g, hg⟩ : contract d (f : K⸨X⸩) r ∈ Set.range (ofPowerSeries ℤ K) := by
    rw [TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff]
    intro k hk
    have hidx : (d : ℤ) * k + r < 0 := by
      have hrd : (r : ℤ) < d := by exact_mod_cast r.isLt
      have : (1 : ℤ) ≤ d := by exact_mod_cast d.pos
      nlinarith
    simp [coeff_contract, PowerSeries.coeff_coe, hidx]
  rw [map_mul, map_mul, (addVal L).map_mul, RatFunc.single_zpow, map_zpow₀, map_zpow₀,
    addVal_zpow (map_levelEmbedding_single_one_ne_zero ρ d), levelEmbedding_expand_self, ← hg]
  exact add_nonneg (WithTop.coe_le_coe.mpr (mul_nonneg hqu (by positivity))) (hρ g)

/-- **Valuation scaling for ring homomorphisms.** Any ring homomorphism
`ρ : puiseuxField K →+* puiseuxField L` sending `K⟦X⟧` into the valuation ring multiplies the order
of every Puiseux series by `ord (ρ t)`. -/
theorem addVal_ringHom_apply
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    (x : puiseuxField K) :
    addVal L (ρ x) = (addVal K x).map ((ρ (single K 1 1) : HahnSeries ℚ L).order * ·) := by
  obtain ⟨d, f, hf⟩ := exists_mem_range_levelEmbedding x
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
  subst hf
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hunit := addVal_ringHom_levelEmbedding_coe_of_isUnit ρ
    (addVal_ringHom_levelEmbedding_coe_nonneg ρ hρ d)
    (TauCeti.LaurentSeries.isUnit_powerSeriesPart hf)
  have hdecomp : levelEmbedding K d f = levelEmbedding K d (HahnSeries.single 1 1) ^ f.order *
      levelEmbedding K d (f.powerSeriesPart : K⸨X⸩) := by
    conv_lhs => rw [← f.single_order_mul_powerSeriesPart]
    rw [map_mul, RatFunc.single_zpow, map_zpow₀]
  rw [hdecomp, map_mul, (addVal L).map_mul, hunit, add_zero, map_zpow₀,
    addVal_zpow (map_levelEmbedding_single_one_ne_zero ρ d),
    order_ringHom_levelEmbedding_single_one, ← hdecomp, addVal_levelEmbedding,
    ← order_eq_orderTop_of_ne_zero hf, WithTop.map_coe, WithTop.map_coe, div_mul_eq_mul_div,
    mul_div_assoc]

/-- Any ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` sending `K⟦X⟧` into the valuation
ring multiplies rational orders by `ord (ρ t)`. -/
theorem order_ringHom_apply
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ L).order =
      (ρ (single K 1 1) : HahnSeries ℚ L).order * (x : HahnSeries ℚ K).order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx0 : (x : HahnSeries ℚ K) ≠ 0 := by exact_mod_cast hx
  have hrx0 : (ρ x : HahnSeries ℚ L) ≠ 0 := by
    exact_mod_cast (map_ne_zero_iff ρ ρ.injective).mpr hx
  have h := addVal_ringHom_apply ρ hρ x
  rwa [addVal_apply, addVal_apply, ← order_eq_orderTop_of_ne_zero hx0,
    ← order_eq_orderTop_of_ne_zero hrx0, WithTop.map_coe, WithTop.coe_eq_coe] at h

/-- Any ring homomorphism sending `K⟦X⟧` into the valuation ring preserves nonnegative orders on
the whole Puiseux field. -/
theorem addVal_ringHom_nonneg
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    {x : puiseuxField K} (hx : 0 ≤ addVal K x) :
    0 ≤ addVal L (ρ x) := by
  rw [addVal_ringHom_apply ρ hρ]
  cases h : addVal K x with
  | top => simp
  | coe r =>
    rw [h, ← WithTop.coe_zero, WithTop.coe_le_coe] at hx
    exact WithTop.coe_le_coe.mpr (mul_nonneg (order_ringHom_single_one_nonneg ρ hρ) hx)

/-- Any ring homomorphism sending `K⟦X⟧` into the valuation ring maps the Puiseux valuation ring
into the target valuation ring. -/
theorem valuation_ringHom_le_one
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    {x : puiseuxField K} (hx : valuation K x ≤ 1) :
    valuation L (ρ x) ≤ 1 := by
  rw [valuation_le_one_iff] at hx ⊢
  exact addVal_ringHom_nonneg ρ hρ hx

/-- A ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` sending `K⟦X⟧` into the valuation
ring and `t` to a series of strictly positive order is a topological embedding. -/
theorem isEmbedding_of_order_ringHom_single_one_pos
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    (hq : 0 < (ρ (single K 1 1) : HahnSeries ℚ L).order) :
    IsEmbedding ρ := by
  set q := (ρ (single K 1 1) : HahnSeries ℚ L).order
  have hcont : Continuous ρ := by
    refine continuous_of_continuousAt_zero ρ ?_
    rw [ContinuousAt, map_zero, hasBasis_nhds_zero.tendsto_right_iff]
    intro r _
    filter_upwards [hasBasis_nhds_zero.mem_of_mem (i := r / q) trivial] with x hx
    rw [addVal_ringHom_apply ρ hρ]
    cases h : addVal K x with
    | top => simp
    | coe s =>
      rw [h, WithTop.coe_le_coe, div_le_iff₀' hq] at hx
      exact WithTop.map_coe _ _ ▸ WithTop.coe_le_coe.mpr hx
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm ?_ ?_), ρ.injective⟩
  · exact (hcont.tendsto' 0 0 (map_zero ρ)).le_comap
  · intro U hU
    obtain ⟨r, -, hr⟩ := hasBasis_nhds_zero.mem_iff.mp hU
    refine mem_comap.mpr ⟨{y | ((q * r : ℚ) : WithTop ℚ) ≤ addVal L y},
      hasBasis_nhds_zero.mem_of_mem trivial, fun x hx ↦ hr ?_⟩
    rw [Set.mem_ofPred_eq]
    rw [Set.mem_preimage, Set.mem_ofPred_eq, addVal_ringHom_apply ρ hρ] at hx
    cases h : addVal K x with
    | top => exact le_top
    | coe s =>
      rw [h, WithTop.map_coe, WithTop.coe_le_coe, mul_le_mul_iff_right₀ hq] at hx
      exact WithTop.coe_le_coe.mpr hx

/-- A ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` sending `K⟦X⟧` into the valuation
ring and `t` to a series of strictly positive order is continuous. -/
theorem continuous_of_order_ringHom_single_one_pos
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))))
    (hq : 0 < (ρ (single K 1 1) : HahnSeries ℚ L).order) :
    Continuous ρ :=
  (isEmbedding_of_order_ringHom_single_one_pos ρ hρ hq).continuous

end RingHom

section AlgHom

/-- If a `K`-algebra endomorphism `ρ` of `puiseuxField K` sends `K⟦X⟧` into the valuation ring,
then `ρ t` has strictly positive rational order: if `ord (ρ t) = 0`, subtracting its nonzero
constant term `c` would give a series of positive order that is the image of the unit `X - c` of
`K⟦X⟧`. -/
private theorem order_algHom_single_one_pos_of_addVal_coe_nonneg
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal K (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩)))) :
    0 < (ρ (single K 1 1) : HahnSeries ℚ K).order := by
  refine lt_of_le_of_ne (order_ringHom_single_one_nonneg ρ.toRingHom hρ) fun h0 ↦ ?_
  set s := ρ (single K 1 1)
  have hs0 : (s : HahnSeries ℚ K) ≠ 0 := by
    exact_mod_cast (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  set c := (s : HahnSeries ℚ K).coeff 0
  have hc : c ≠ 0 := by
    have hord : (s : HahnSeries ℚ K).order = 0 := h0.symm
    simpa [c, hord] using coeff_order_eq_zero.not.mpr hs0
  have hu : IsUnit (PowerSeries.X - PowerSeries.C c) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_X,
      PowerSeries.constantCoeff_C, zero_sub, IsUnit.neg_iff, isUnit_iff_ne_zero]
    exact hc
  have hunit := addVal_ringHom_levelEmbedding_coe_of_isUnit ρ.toRingHom hρ hu
  have hmap : ρ (levelEmbedding K 1 ((PowerSeries.X - PowerSeries.C c : K⟦X⟧) : K⸨X⸩)) =
      s - algebraMap K (puiseuxField K) c := by
    rw [← algebraMap_laurentSeries_apply, PowerSeries.coe_sub, ofPowerSeries_X, ofPowerSeries_C,
      ← _root_.LaurentSeries.algebraMap_apply, map_sub, ← IsScalarTower.algebraMap_apply,
      map_sub, AlgHom.commutes]
    exact congrArg (· - _) (congrArg ρ (levelEmbedding_single_self 1))
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hmap] at hunit
  -- Every coefficient of `s - c` at exponents `≤ 0` vanishes, contradicting `ord (s - c) = 0`.
  have hpos : (0 : WithTop ℚ) < addVal K (s - algebraMap K (puiseuxField K) c) := by
    rw [addVal_apply]
    refine lt_of_le_of_ne (le_orderTop_iff_forall.mpr fun r hr ↦ ?_) fun htop ↦ ?_
    · rw [← WithTop.coe_zero, WithTop.coe_lt_coe] at hr
      have hc0 : (algebraMap K (puiseuxField K) c : HahnSeries ℚ K).coeff r = 0 := by
        simp [HahnSeries.algebraMap_apply', hr.ne]
      rw [AddSubgroupClass.coe_sub, coeff_sub, hc0, sub_zero]
      exact coeff_eq_zero_of_lt_order (by linarith [h0])
    · refine orderTop_ne_of_coeff_eq_zero ?_ htop.symm
      rw [AddSubgroupClass.coe_sub, coeff_sub, IntermediateField.coe_algebraMap_apply,
        HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, ofPowerSeries_C, C_apply,
        coeff_single_same]
      exact sub_self _
  exact hpos.ne' hunit

/-- A continuous `K`-algebra endomorphism of `puiseuxField K` sends `t` to a series of nonnegative
order, since `X ^ n → 0` in `K⸨X⸩`. -/
private theorem addVal_algHom_single_one_nonneg_of_continuous
    {ρ : puiseuxField K →ₐ[K] puiseuxField K} (hρ : Continuous ρ) :
    0 ≤ addVal K (ρ (single K 1 1)) := by
  by_contra! hlt
  have hX : Tendsto (fun n : ℕ ↦ (HahnSeries.single 1 1 : K⸨X⸩) ^ n) atTop (𝓝 0) := by
    rw [tendsto_laurentSeries_iff_orderTop_sub]
    intro k
    filter_upwards [eventually_ge_atTop k.toNat] with n hn
    rw [sub_zero, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one,
      orderTop_single one_ne_zero, WithTop.coe_le_coe]
    omega
  have ht : Tendsto (fun n : ℕ ↦ ρ (single K 1 1) ^ n) atTop (𝓝 0) := by
    refine (((hρ.comp (continuous_levelEmbedding 1)).tendsto' 0 0 (by simp)).comp hX).congr
      fun n ↦ ?_
    dsimp only [Function.comp_def]
    rw [map_pow, map_pow]
    exact congrArg (fun z ↦ ρ z ^ n) (levelEmbedding_single_self 1)
  obtain ⟨n, hn⟩ := eventually_atTop.mp (((tendsto_iff_addVal_sub _ 0).mp ht 0).and
    (eventually_ge_atTop 1))
  obtain ⟨hord, -⟩ := hn (max n 1) (le_max_left _ _)
  rw [sub_zero] at hord
  have hs0 : ρ (single K 1 1) ≠ 0 :=
    (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  have hsq : (ρ (single K 1 1) : HahnSeries ℚ K).order < 0 := by
    have hs0' : (ρ (single K 1 1) : HahnSeries ℚ K) ≠ 0 := by exact_mod_cast hs0
    rwa [addVal_apply, ← order_eq_orderTop_of_ne_zero hs0', ← WithTop.coe_zero,
      WithTop.coe_lt_coe] at hlt
  have hpow := addVal_zpow hs0 (max n 1 : ℕ)
  rw [zpow_natCast] at hpow
  have hle := WithTop.coe_le_coe.mp (hpow ▸ hord)
  rw [Int.cast_natCast] at hle
  have hpos : (0 : ℚ) < (max n 1 : ℕ) := by positivity
  nlinarith

/-- The polynomial truncations of a formal power series converge to it in `K⸨X⸩`. -/
private theorem tendsto_sum_C_mul_X_pow_coe (f : K⟦X⟧) :
    Tendsto (fun N : ℕ ↦
      ((∑ k ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k : K⟦X⟧) :
        K⸨X⸩)) atTop (𝓝 (f : K⸨X⸩)) := by
  rw [tendsto_laurentSeries_iff_orderTop_sub]
  intro k
  filter_upwards [eventually_ge_atTop k.toNat] with N hN
  have hdiff : (∑ i ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i) -
      f = -(PowerSeries.X ^ N * PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) f) := by
    have h := PowerSeries.eq_X_pow_mul_shift_add_trunc N f
    rw [← Polynomial.eval₂_C_X_eq_coe, PowerSeries.eval₂_trunc_eq_sum_range] at h
    linear_combination -h
  rw [← PowerSeries.coe_sub, hdiff, PowerSeries.coe_neg, orderTop_neg, PowerSeries.coe_mul,
    ofPowerSeries_X_pow]
  refine le_trans (WithTop.coe_le_coe.mpr (by omega : k ≤ (N : ℤ))) ?_
  refine le_trans (b := (HahnSeries.single (N : ℤ) (1 : K)).orderTop +
      ((PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) f : K⟦X⟧) : K⸨X⸩).orderTop) ?_
    orderTop_add_le_mul
  rw [orderTop_single one_ne_zero, PowerSeries.orderTop_coe]
  cases (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + N) f).order with
  | top => simp
  | coe m =>
    rw [ENat.map_natCast, ← WithTop.coe_add, WithTop.coe_le_coe]
    omega

/-- **Characterization of continuous `K`-algebra endomorphisms of the Puiseux field.** A
`K`-algebra endomorphism `ρ` of `puiseuxField K` is continuous if and only if it maps every formal
power series `f ∈ K⟦X⟧` into the valuation ring `0 ≤ ord (ρ f)`. -/
theorem continuous_algHom_iff {ρ : puiseuxField K →ₐ[K] puiseuxField K} :
    Continuous ρ ↔ ∀ f : K⟦X⟧, 0 ≤ addVal K (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))) := by
  refine ⟨fun hρ f ↦ ?_, fun hρ ↦ continuous_of_order_ringHom_single_one_pos ρ.toRingHom hρ
    (order_algHom_single_one_pos_of_addVal_coe_nonneg hρ)⟩
  have hs_nonneg := addVal_algHom_single_one_nonneg_of_continuous hρ
  have hpow (m : ℕ) : 0 ≤ addVal K (ρ (single K 1 1) ^ m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, (addVal K).map_mul]
      exact add_nonneg ih hs_nonneg
  let truncPow (N : ℕ) : K⟦X⟧ :=
    ∑ k ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k
  have hρ_tendsto : Tendsto (fun N : ℕ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) (truncPow N : K⸨X⸩)))
      atTop (𝓝 (ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩)))) :=
    ((hρ.comp (continuous_levelEmbedding 1)).tendsto _).comp (tendsto_sum_C_mul_X_pow_coe f)
  obtain ⟨N, hN⟩ := (((tendsto_iff_addVal_sub _ _).mp hρ_tendsto 0)).exists
  have htrunc_nonneg : 0 ≤ addVal K (ρ (algebraMap K⸨X⸩ (puiseuxField K) (truncPow N : K⸨X⸩))) := by
    simp only [truncPow, map_sum]
    refine AddValuation.map_le_sum (addVal K) fun k _ ↦ ?_
    have hterm : ρ (algebraMap K⸨X⸩ (puiseuxField K)
        ((PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k : K⟦X⟧) : K⸨X⸩)) =
        algebraMap K (puiseuxField K) (PowerSeries.coeff k f) * ρ (single K 1 1) ^ k := by
      rw [PowerSeries.coe_mul, ofPowerSeries_C, ofPowerSeries_X_pow,
        ← _root_.LaurentSeries.algebraMap_apply, map_mul, ← IsScalarTower.algebraMap_apply,
        map_mul, AlgHom.commutes]
      congr 1
      have hXk : (HahnSeries.single (k : ℤ) (1 : K) : K⸨X⸩) = HahnSeries.single 1 1 ^ k := by
        rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
      rw [hXk, map_pow, map_pow]
      exact congrArg (· ^ k) (congrArg ρ (levelEmbedding_single_self 1))
    rw [hterm, (addVal K).map_mul]
    exact add_nonneg (addVal_algebraMap_nonneg _) (hpow k)
  have hsub : ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩)) =
      ρ (algebraMap K⸨X⸩ (puiseuxField K) (truncPow N : K⸨X⸩)) -
        (ρ (algebraMap K⸨X⸩ (puiseuxField K) (truncPow N : K⸨X⸩)) -
          ρ (algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩))) := by ring
  rw [hsub]
  exact (le_min htrunc_nonneg hN).trans (AddValuation.map_sub _ _ _)

/-- A `K`-algebra endomorphism of `puiseuxField K` is continuous if and only if it preserves
nonnegative orders. -/
theorem continuous_algHom_iff_addVal_nonneg {ρ : puiseuxField K →ₐ[K] puiseuxField K} :
    Continuous ρ ↔ ∀ x : puiseuxField K, 0 ≤ addVal K x → 0 ≤ addVal K (ρ x) := by
  rw [continuous_algHom_iff]
  refine ⟨fun hρ x hx ↦ addVal_ringHom_nonneg ρ.toRingHom hρ hx, fun h f ↦ h _ ?_⟩
  rw [algebraMap_laurentSeries_apply]
  simpa using (div_le_addVal_levelEmbedding_iff 1 (f : K⸨X⸩) 0).mpr
    (by simp [PowerSeries.orderTop_coe])

/-- A `K`-algebra endomorphism of `puiseuxField K` is continuous if and only if it maps the
valuation ring `v x ≤ 1` into itself. -/
theorem continuous_algHom_iff_valuation_le_one {ρ : puiseuxField K →ₐ[K] puiseuxField K} :
    Continuous ρ ↔ ∀ x : puiseuxField K, valuation K x ≤ 1 → valuation K (ρ x) ≤ 1 := by
  simp_rw [continuous_algHom_iff_addVal_nonneg, valuation_le_one_iff]

/-- A continuous `K`-algebra endomorphism of `puiseuxField K` sends `t` to a series of strictly
positive rational order. -/
theorem order_algHom_single_one_pos {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : Continuous ρ) :
    0 < (ρ (single K 1 1) : HahnSeries ℚ K).order :=
  order_algHom_single_one_pos_of_addVal_coe_nonneg (continuous_algHom_iff.mp hρ)

/-- A continuous `K`-algebra endomorphism of `puiseuxField K` sends `t` to a series of strictly
positive `WithTop ℚ`-valued order. -/
theorem addVal_algHom_single_one_pos {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : Continuous ρ) :
    0 < addVal K (ρ (single K 1 1)) := by
  have hs0 : (ρ (single K 1 1) : HahnSeries ℚ K) ≠ 0 := by
    exact_mod_cast (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  rw [addVal_apply, ← order_eq_orderTop_of_ne_zero hs0, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact order_algHom_single_one_pos hρ

/-- A continuous `K`-algebra endomorphism `ρ` of `puiseuxField K` multiplies every order by
`ord (ρ t)`. -/
theorem addVal_algHom_apply {ρ : puiseuxField K →ₐ[K] puiseuxField K} (hρ : Continuous ρ)
    (x : puiseuxField K) :
    addVal K (ρ x) = (addVal K x).map ((ρ (single K 1 1) : HahnSeries ℚ K).order * ·) :=
  addVal_ringHom_apply ρ.toRingHom (continuous_algHom_iff.mp hρ) x

/-- A continuous `K`-algebra endomorphism `ρ` of `puiseuxField K` multiplies every rational order
by `ord (ρ t)`. -/
theorem order_algHom_apply {ρ : puiseuxField K →ₐ[K] puiseuxField K} (hρ : Continuous ρ)
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order =
      (ρ (single K 1 1) : HahnSeries ℚ K).order * (x : HahnSeries ℚ K).order :=
  order_ringHom_apply ρ.toRingHom (continuous_algHom_iff.mp hρ) x

/-- Every continuous `K`-algebra endomorphism of `puiseuxField K` is a topological embedding. -/
theorem isEmbedding_of_continuous_algHom {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : Continuous ρ) :
    IsEmbedding ρ :=
  isEmbedding_of_order_ringHom_single_one_pos ρ.toRingHom (continuous_algHom_iff.mp hρ)
    (order_algHom_single_one_pos hρ)

/-- A continuous `K`-algebra endomorphism of `puiseuxField K` sending `t` to a series of order one
preserves orders. -/
theorem addVal_algHom_eq_of_order_eq_one {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : Continuous ρ) (h : (ρ (single K 1 1) : HahnSeries ℚ K).order = 1)
    (x : puiseuxField K) :
    addVal K (ρ x) = addVal K x := by
  rw [addVal_algHom_apply hρ, h]
  cases addVal K x <;> simp

/-- A continuous `K`-algebra endomorphism of `puiseuxField K` sending `t` to a series of order one
is an isometry for the multiplicative valuation. -/
theorem valuation_algHom_eq_of_order_eq_one {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : Continuous ρ) (h : (ρ (single K 1 1) : HahnSeries ℚ K).order = 1)
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x := by
  have hord := addVal_algHom_eq_of_order_eq_one hρ h x
  rw [addVal_apply, addVal_apply] at hord
  rw [valuation_apply, valuation_apply]
  exact le_antisymm (HahnSeries.valuation_le_valuation_iff.mpr hord.ge)
    (HahnSeries.valuation_le_valuation_iff.mpr hord.le)

end AlgHom

end puiseuxField

end TauCeti
