/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation

import TauCeti.RingTheory.HahnSeries.Inverse
import TauCeti.RingTheory.Valuation.Integral.Basic

/-!
# Valuation scaling and continuity of homomorphisms between Puiseux fields

Let `K` and `L` be fields and `ρ : puiseuxField K →+* puiseuxField L` a ring homomorphism between
Puiseux fields. Since the valuation ring `{x | valuation K x ≤ 1}` is the integral closure of
`K⟦X⟧` in `puiseuxField K` (`isIntegral_powerSeries_iff`), whenever `ρ` maps `K⟦X⟧` into the
valuation ring of `puiseuxField L`, it maps the entire valuation ring of `puiseuxField K` into that
of `puiseuxField L` (`valuation_map_le_one_of_le_one_of_forall_valuation_le_one`) and scales every
rational order by the rational order of `ρ (single K 1 1)`
(`order_map_eq_mul_of_forall_addVal_nonneg`).

Consequently, the following are equivalent for any ring homomorphism
`ρ : puiseuxField K →+* puiseuxField L`:

* `ρ` is a topological embedding (`isEmbedding_ringHom_iff_continuous`);
* `ρ` is continuous (`continuous_ringHom_iff`);
* the restriction of `ρ` to `K⸨X⸩` is continuous
  (`continuous_ringHom_iff_continuous_comp_algebraMap`);
* `ρ` sends `K⟦X⟧` into the valuation ring of `puiseuxField L` and sends `t = single K 1 1` to a
  series of strictly positive rational order.

In particular, every continuous ring isomorphism between Puiseux fields is a homeomorphism
(`isHomeomorph_ringEquiv_iff`, `continuous_symm_of_continuous_ringEquiv`), and for a `K`-algebra
endomorphism of `puiseuxField K`, strict positivity of the order of `ρ t` follows automatically
from sending `K⟦X⟧` into the valuation ring (`continuous_algHom_iff`).

## Main results

* `TauCeti.puiseuxField.valuation_map_le_one_of_le_one_of_forall_valuation_le_one`,
  `TauCeti.puiseuxField.addVal_map_nonneg_of_nonneg_of_forall_addVal_nonneg`: preserving the
  valuation ring on `K⟦X⟧` extends to the whole valuation ring of `puiseuxField K`.
* `TauCeti.puiseuxField.order_map_eq_mul_of_forall_addVal_nonneg`: valuation scaling on rational
  orders.
* `TauCeti.puiseuxField.mul_le_addVal_map_iff_of_forall_addVal_nonneg_of_order_pos`: order-ball
  comparison when `0 < (ρ t).order`.
* `TauCeti.puiseuxField.isEmbedding_of_forall_addVal_nonneg_of_order_pos`,
  `TauCeti.puiseuxField.isEmbedding_ringHom_iff_continuous`,
  `TauCeti.puiseuxField.continuous_ringHom_iff_continuous_comp_algebraMap`,
  `TauCeti.puiseuxField.continuous_ringHom_iff`,
  `TauCeti.puiseuxField.isHomeomorph_ringEquiv_iff`,
  `TauCeti.puiseuxField.continuous_symm_of_continuous_ringEquiv`: characterizations of continuity,
  topological embeddings, and homeomorphisms between Puiseux fields.
* `TauCeti.puiseuxField.order_map_single_one_pos_of_forall_addVal_nonneg`,
  `TauCeti.puiseuxField.continuous_algHom_iff`: continuity of a `K`-algebra endomorphism of
  `puiseuxField K` is equivalent to sending `K⟦X⟧` into the valuation ring.
-/

public section

open Filter HahnSeries LaurentSeries Polynomial Topology WithZero
open scoped LaurentSeries Polynomial PowerSeries

namespace TauCeti.puiseuxField

variable {K L : Type*} [Field K] [Field L]

private theorem coe_ne_zero {x : puiseuxField K} (hx : x ≠ 0) :
    (x : HahnSeries ℚ K) ≠ 0 :=
  ZeroMemClass.coe_eq_zero.not.mpr hx

/-- A ring homomorphism between Puiseux fields that maps `K⟦X⟧` into the valuation ring of
`puiseuxField L` maps the entire valuation ring of `puiseuxField K` into that of
`puiseuxField L`. -/
theorem valuation_map_le_one_of_le_one_of_forall_valuation_le_one
    (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1)
    {x : puiseuxField K} (hx : valuation K x ≤ 1) :
    valuation L (ρ x) ≤ 1 :=
  (Subring.integralClosure_le_iff (T := ((valuation L).comap ρ).integer)).mpr hρ
    (isIntegral_powerSeries_iff.mpr hx)

/-- Additive-valuation form of `valuation_map_le_one_of_le_one_of_forall_valuation_le_one`:
nonnegativity of rational orders on `K⟦X⟧` propagates to all series of nonnegative order in
`puiseuxField K`. -/
theorem addVal_map_nonneg_of_nonneg_of_forall_addVal_nonneg
    (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    {x : puiseuxField K} (hx : 0 ≤ addVal K x) :
    0 ≤ addVal L (ρ x) :=
  valuation_le_one_iff.mp <|
    valuation_map_le_one_of_le_one_of_forall_valuation_le_one ρ
      (fun f ↦ valuation_le_one_iff.mpr (hρ f)) (valuation_le_one_iff.mpr hx)

/-- Under a ring homomorphism sending `K⟦X⟧` into the valuation ring, any valuation unit `u` maps
to a series of rational order `0`. -/
private theorem order_map_eq_zero_of_valuation_eq_one (ρ : puiseuxField K →+* puiseuxField L)
    (hv : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1)
    {u : puiseuxField K} (hu_val : valuation K u = 1) :
    (ρ u : HahnSeries ℚ L).order = 0 := by
  have hu_ne : u ≠ 0 := fun h0 ↦ by simp [h0] at hu_val
  have hρu_ne : ρ u ≠ 0 := (map_ne_zero_iff ρ ρ.injective).mpr hu_ne
  have hρu_val : valuation L (ρ u) = 1 := by
    apply le_antisymm (valuation_map_le_one_of_le_one_of_forall_valuation_le_one ρ hv hu_val.le)
    have hinv : valuation L (ρ u⁻¹) ≤ 1 :=
      valuation_map_le_one_of_le_one_of_forall_valuation_le_one ρ hv
        (by rw [map_inv₀, hu_val, inv_one])
    rw [map_inv₀, map_inv₀] at hinv
    have hne : valuation L (ρ u) ≠ 0 := (Valuation.ne_zero_iff _).mpr hρu_ne
    exact (inv_le_one₀ (lt_of_le_of_ne' zero_le hne)).mp hinv
  have hexp := valuation_eq_exp_neg_order (coe_ne_zero hρu_ne)
  rw [← valuation_apply, hρu_val, ← exp_zero, eq_comm, exp_inj, neg_eq_zero] at hexp
  exact hexp

/-- **Valuation scaling**: any ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` that sends
`K⟦X⟧` into the valuation ring multiplies the rational order of every Puiseux series by the
rational order of `ρ (single K 1 1)`. -/
theorem order_map_eq_mul_of_forall_addVal_nonneg (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ L).order =
      (x : HahnSeries ℚ K).order * (ρ (single K 1 1) : HahnSeries ℚ L).order := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hv : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1 := fun f ↦
    valuation_le_one_iff.mpr (hρ f)
  set q : ℚ := (x : HahnSeries ℚ K).order
  set u : puiseuxField K := x * single K (-q) 1
  have hu_ne : u ≠ 0 := mul_ne_zero hx0 (by simp)
  have hu_val : valuation K u = 1 := by
    rw [map_mul, valuation_apply x, valuation_eq_exp_neg_order (coe_ne_zero hx0),
      valuation_single (-q) one_ne_zero, neg_neg, ← exp_add, neg_add_cancel, exp_zero]
  have hρu_ord := order_map_eq_zero_of_valuation_eq_one ρ hv hu_val
  let n : ℕ+ := ⟨q.den, q.den_pos⟩
  have hn_coe : (n : ℕ) = q.den := rfl
  set s : puiseuxField K := single K (1 / (n : ℚ)) 1
  have hn_ord : (ρ (single K 1 1) : HahnSeries ℚ L).order =
      (n : ℚ) * (ρ s : HahnSeries ℚ L).order := by
    have hs_pow : s ^ (n : ℕ) = single K 1 1 := by
      rw [single_pow, one_pow, mul_one_div, div_self (by exact_mod_cast n.ne_zero)]
    rw [← hs_pow, map_pow, IntermediateField.coe_pow, HahnSeries.order_pow, nsmul_eq_mul]
  have hq_ord : (ρ (single K q 1) : HahnSeries ℚ L).order =
      q * (ρ (single K 1 1) : HahnSeries ℚ L).order := by
    have hs_zpow : s ^ q.num = single K q 1 := by
      rw [single_zpow, one_zpow, mul_one_div, hn_coe, Rat.num_div_den]
    have hqn : (q.num : ℚ) = q * (n : ℚ) := by
      rw [hn_coe]
      exact (div_eq_iff (by exact_mod_cast q.den_nz)).mp q.num_div_den
    rw [← hs_zpow, map_zpow₀, ← IntermediateField.coe_val, map_zpow₀, IntermediateField.coe_val,
      HahnSeries.order_zpow, zsmul_eq_mul, hqn, mul_assoc, ← hn_ord]
  have hx_eq : x = u * single K q 1 := by
    apply Subtype.ext
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, coe_single, coe_single,
      mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
      ← HahnSeries.C_apply, map_one, mul_one]
  have hρu_ne : ρ u ≠ 0 := (map_ne_zero_iff ρ ρ.injective).mpr hu_ne
  have hρq_ne : ρ (single K q 1) ≠ 0 :=
    (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  rw [hx_eq, map_mul, IntermediateField.coe_mul,
    order_mul (coe_ne_zero hρu_ne) (coe_ne_zero hρq_ne), hρu_ord, zero_add, hq_ord]

/-- Order-ball comparison under a ring homomorphism mapping `K⟦X⟧` into the valuation ring and
sending `t` to an element of strictly positive order. -/
theorem mul_le_addVal_map_iff_of_forall_addVal_nonneg_of_order_pos
    (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    (he : 0 < (ρ (single K 1 1) : HahnSeries ℚ L).order) (q : ℚ) (x : puiseuxField K) :
    (((q * (ρ (single K 1 1) : HahnSeries ℚ L).order : ℚ) : WithTop ℚ) ≤ addVal L (ρ x)) ↔
      (q : WithTop ℚ) ≤ addVal K x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hρx := coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr hx0)
  rw [addVal_apply, addVal_apply, ← order_eq_orderTop_of_ne_zero hρx,
    ← order_eq_orderTop_of_ne_zero (coe_ne_zero hx0), WithTop.coe_le_coe, WithTop.coe_le_coe,
    order_map_eq_mul_of_forall_addVal_nonneg ρ hρ x, mul_le_mul_iff_of_pos_right he]

/-- If `ρ` is continuous on `K⸨X⸩`, then `ρ (single K 1 1)` has strictly positive rational order. -/
private theorem order_map_single_one_pos_of_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L)
    (hcont : Continuous fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    0 < (ρ (single K 1 1) : HahnSeries ℚ L).order := by
  let φ : K⸨X⸩ →+* puiseuxField L := ρ.comp (algebraMap K⸨X⸩ (puiseuxField K))
  have hφ_cont : Continuous φ := hcont
  have hφ_single_one : φ (HahnSeries.single 1 1) = ρ (single K 1 1) := by
    rw [RingHom.comp_apply, algebraMap_laurentSeries_single_one]
  have hρt_ne : ρ (single K 1 1) ≠ 0 :=
    (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  have hu : Tendsto (fun k : ℕ ↦ (HahnSeries.single (k : ℤ) (1 : K) : K⸨X⸩)) atTop (𝓝 0) := by
    rw [tendsto_laurentSeries_iff_orderTop_sub]
    intro m
    filter_upwards [eventually_ge_atTop m.toNat] with k hk
    rw [sub_zero, orderTop_single one_ne_zero, WithTop.coe_le_coe]
    omega
  obtain ⟨k, hk1, hk_pos⟩ := (((tendsto_iff_addVal_sub _ 0).mp
    ((hφ_cont.tendsto' 0 0 (map_zero φ)).comp hu) 1).and (eventually_ge_atTop 1)).exists
  rw [Function.comp_apply, sub_zero, RatFunc.single_zpow, zpow_natCast, map_pow, hφ_single_one,
    addVal_apply, ← order_eq_orderTop_of_ne_zero (coe_ne_zero (pow_ne_zero k hρt_ne)),
    IntermediateField.coe_pow, HahnSeries.order_pow, nsmul_eq_mul, WithTop.coe_le_coe] at hk1
  have : (0 : ℚ) < k := by exact_mod_cast hk_pos
  nlinarith

/-- If `ρ` is continuous on `K⸨X⸩`, then every constant `c : K` has nonnegative order under `ρ`. -/
private theorem addVal_map_algebraMap_nonneg_of_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L)
    (hcont : Continuous fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f)) (c : K) :
    0 ≤ addVal L (ρ (algebraMap K (puiseuxField K) c)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_contra hlt
  let φ : K⸨X⸩ →+* puiseuxField L := ρ.comp (algebraMap K⸨X⸩ (puiseuxField K))
  have hφ_cont : Continuous φ := hcont
  have hφ_single_one : φ (HahnSeries.single 1 1) = ρ (single K 1 1) := by
    rw [RingHom.comp_apply, algebraMap_laurentSeries_single_one]
  have hc_ne : ρ (algebraMap K (puiseuxField K) c) ≠ 0 :=
    (map_ne_zero_iff ρ ρ.injective).mpr ((map_ne_zero_iff _ (algebraMap K _).injective).mpr hc)
  have hρt_ne : ρ (single K 1 1) ≠ 0 :=
    (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero)
  rw [addVal_apply, ← order_eq_orderTop_of_ne_zero (coe_ne_zero hc_ne), WithTop.coe_nonneg,
    not_le] at hlt
  set q : ℚ := (ρ (algebraMap K (puiseuxField K) c) : HahnSeries ℚ L).order
  set e : ℚ := (ρ (single K 1 1) : HahnSeries ℚ L).order
  obtain ⟨M, hM⟩ := exists_nat_ge (e / (-q))
  have hMq : (M : ℚ) * q + e ≤ 0 := by
    have := (div_le_iff₀ (neg_pos.mpr hlt)).mp hM; linarith
  have hv : Tendsto (fun k : ℕ ↦ (HahnSeries.single (k : ℤ) (c ^ (k * M)) : K⸨X⸩))
      atTop (𝓝 0) := by
    rw [tendsto_laurentSeries_iff_orderTop_sub]
    intro m
    filter_upwards [eventually_ge_atTop m.toNat] with k hk
    rw [sub_zero, orderTop_single (pow_ne_zero _ hc), WithTop.coe_le_coe]; omega
  obtain ⟨k, hk1, _⟩ := (((tendsto_iff_addVal_sub _ 0).mp
    ((hφ_cont.tendsto' 0 0 (map_zero φ)).comp hv) 1).and (eventually_ge_atTop 1)).exists
  have hφvk : φ (HahnSeries.single (k : ℤ) (c ^ (k * M))) =
      ρ (algebraMap K (puiseuxField K) c) ^ (k * M) * ρ (single K 1 1) ^ k := by
    have hvk : (HahnSeries.single (k : ℤ) (c ^ (k * M)) : K⸨X⸩) =
        algebraMap K K⸨X⸩ c ^ (k * M) * HahnSeries.single 1 1 ^ k := by
      rw [← map_pow, _root_.LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
        HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one, HahnSeries.single_mul_single,
        zero_add, mul_one]
    rw [hvk, map_mul, map_pow, map_pow, hφ_single_one]
    exact congrArg (· ^ (k * M) * _)
      (congrArg ρ (IsScalarTower.algebraMap_apply K K⸨X⸩ (puiseuxField K) c).symm)
  have h1_ne := coe_ne_zero (pow_ne_zero (k * M) hc_ne)
  have h2_ne := coe_ne_zero (pow_ne_zero k hρt_ne)
  rw [Function.comp_apply, sub_zero, hφvk, addVal_apply, IntermediateField.coe_mul,
    ← order_eq_orderTop_of_ne_zero (mul_ne_zero h1_ne h2_ne), order_mul h1_ne h2_ne,
    IntermediateField.coe_pow, IntermediateField.coe_pow, HahnSeries.order_pow,
    HahnSeries.order_pow, nsmul_eq_mul, nsmul_eq_mul, WithTop.coe_le_coe] at hk1
  push_cast at hk1
  linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hMq]

/-- Polynomial case of `forall_addVal_nonneg_and_order_pos_of_continuous_comp_algebraMap`. -/
private theorem addVal_map_polynomial_nonneg_of_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L)
    (he : 0 ≤ (ρ (single K 1 1) : HahnSeries ℚ L).order)
    (hconst : ∀ c : K, 0 ≤ addVal L (ρ (algebraMap K (puiseuxField K) c))) (P : K[X]) :
    0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) ((P : K⟦X⟧) : K⸨X⸩))) := by
  let φ : K⸨X⸩ →+* puiseuxField L := ρ.comp (algebraMap K⸨X⸩ (puiseuxField K))
  have hφ_apply (g : K⸨X⸩) : φ g = ρ (algebraMap K⸨X⸩ (puiseuxField K) g) := rfl
  rw [← hφ_apply]
  have hφ_single_one : φ (HahnSeries.single 1 1) = ρ (single K 1 1) := by
    rw [hφ_apply, algebraMap_laurentSeries_single_one]
  have hρt_pos : (0 : WithTop ℚ) ≤ addVal L (ρ (single K 1 1)) := by
    have hρt_ne : (ρ (single K 1 1) : HahnSeries ℚ L) ≠ 0 := coe_ne_zero
      ((map_ne_zero_iff ρ ρ.injective).mpr ((single_eq_zero_iff (q := 1)).not.mpr one_ne_zero))
    rw [addVal_apply, ← order_eq_orderTop_of_ne_zero hρt_ne, WithTop.coe_nonneg]
    exact he
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.coe_add, map_add, map_add]
    exact le_trans (le_min hP hQ) (AddValuation.map_add _ _ _)
  | monomial j c =>
    have hm : ((Polynomial.monomial j c : K[X]) : K⟦X⟧) = PowerSeries.C c * PowerSeries.X ^ j := by
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow]
    have hc' : φ ((PowerSeries.C c : K⟦X⟧) : K⸨X⸩) = ρ (algebraMap K (puiseuxField K) c) := by
      rw [hφ_apply, ← algebraMap_powerSeries_apply, ← PowerSeries.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K K⟦X⟧ (puiseuxField K)]
    rw [hm, map_mul, map_pow, PowerSeries.coe_X, map_mul, map_pow, hφ_single_one, hc']
    refine valuation_le_one_iff.mp ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right zero_le
      (pow_le_one' (valuation_le_one_iff.mpr hρt_pos) j)).trans
      (valuation_le_one_iff.mpr (hconst c))

/-- If `ρ : puiseuxField K →+* puiseuxField L` is continuous on `K⸨X⸩`, then `ρ` sends `K⟦X⟧` into
the valuation ring and sends `t` to a series of strictly positive order. -/
private theorem forall_addVal_nonneg_and_order_pos_of_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L)
    (hcont : Continuous fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    (∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f))) ∧
      0 < (ρ (single K 1 1) : HahnSeries ℚ L).order := by
  have he := order_map_single_one_pos_of_continuous_comp_algebraMap ρ hcont
  have hconst := addVal_map_algebraMap_nonneg_of_continuous_comp_algebraMap ρ hcont
  let φ : K⸨X⸩ →+* puiseuxField L := ρ.comp (algebraMap K⸨X⸩ (puiseuxField K))
  have hφ_apply (g : K⸨X⸩) : φ g = ρ (algebraMap K⸨X⸩ (puiseuxField K) g) := rfl
  have hφ_cont : Continuous φ := hcont
  refine ⟨fun f ↦ ?_, he⟩
  have htrunc : Tendsto (fun N : ℕ ↦ (((f.trunc N : K[X]) : K⟦X⟧) : K⸨X⸩))
      atTop (𝓝 (f : K⸨X⸩)) := by
    rw [tendsto_laurentSeries_iff_orderTop_sub]
    intro m
    filter_upwards [eventually_ge_atTop m.toNat] with N hN
    refine le_orderTop_iff_forall.mpr fun j hj ↦ ?_
    rw [HahnSeries.coeff_sub, sub_eq_zero]
    by_cases hj0 : j < 0
    · simp [PowerSeries.coeff_coe, hj0]
    · lift j to ℕ using not_lt.mp hj0
      have hjN : j < N := by
        have hjm : (j : ℤ) < m := WithTop.coe_lt_coe.mp hj
        omega
      simp [PowerSeries.coeff_coe, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hjN]
  obtain ⟨N, hN⟩ := ((tendsto_iff_addVal_sub _ (φ (f : K⸨X⸩))).mp
    ((hφ_cont.tendsto (f : K⸨X⸩)).comp htrunc) 0).exists
  rw [Function.comp_apply] at hN
  have hdecomp : φ (f : K⸨X⸩) = φ (((f.trunc N : K[X]) : K⟦X⟧) : K⸨X⸩) -
      (φ (((f.trunc N : K[X]) : K⟦X⟧) : K⸨X⸩) - φ (f : K⸨X⸩)) := by ring
  rw [algebraMap_powerSeries_apply, ← hφ_apply, hdecomp]
  exact le_trans
    (le_min
      (addVal_map_polynomial_nonneg_of_continuous_comp_algebraMap ρ he.le hconst (f.trunc N)) hN)
    (AddValuation.map_sub _ _ _)

/-- If `ρ : puiseuxField K →+* puiseuxField L` maps `K⟦X⟧` into the valuation ring and sends `t` to
an element of strictly positive order, then `ρ` is a topological embedding. -/
theorem isEmbedding_of_forall_addVal_nonneg_of_order_pos (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    (he : 0 < (ρ (single K 1 1) : HahnSeries ℚ L).order) :
    IsEmbedding ρ := by
  set e : ℚ := (ρ (single K 1 1) : HahnSeries ℚ L).order
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm ?_ ?_), ρ.injective⟩
  · rw [← map_le_iff_le_comap]
    refine (hasBasis_nhds_zero.map ρ).le_basis_iff hasBasis_nhds_zero |>.mpr fun r _ ↦ ?_
    refine ⟨r / e, trivial, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hre : r / e * e = r := div_mul_cancel₀ r he.ne'
    have hle :=
      (mul_le_addVal_map_iff_of_forall_addVal_nonneg_of_order_pos ρ hρ he (r / e) x).mpr hx
    rwa [Set.mem_ofPred_eq, ← hre]
  · refine hasBasis_nhds_zero.ge_iff.mpr fun q _ ↦ ?_
    refine eventually_comap.mpr (hasBasis_nhds_zero.eventually_iff.mpr ⟨q * e, trivial, ?_⟩)
    rintro _ hy x rfl
    exact (mul_le_addVal_map_iff_of_forall_addVal_nonneg_of_order_pos ρ hρ he q x).mp hy

/-- **Automatic topological embedding**: a ring homomorphism between Puiseux fields is a
topological embedding if and only if it is continuous. -/
theorem isEmbedding_ringHom_iff_continuous (ρ : puiseuxField K →+* puiseuxField L) :
    IsEmbedding ρ ↔ Continuous ρ := by
  refine ⟨IsEmbedding.continuous, fun hcont ↦ ?_⟩
  obtain ⟨hpow, he⟩ := forall_addVal_nonneg_and_order_pos_of_continuous_comp_algebraMap ρ
    (hcont.comp continuous_algebraMap_laurentSeries)
  exact isEmbedding_of_forall_addVal_nonneg_of_order_pos ρ hpow he

/-- Continuity of a ring homomorphism out of `puiseuxField K` into `puiseuxField L` is equivalent
to continuity of its restriction to `K⸨X⸩`. -/
theorem continuous_ringHom_iff_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L) :
    Continuous ρ ↔ Continuous fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f) := by
  refine ⟨fun h ↦ h.comp continuous_algebraMap_laurentSeries, fun h ↦ ?_⟩
  obtain ⟨hpow, he⟩ := forall_addVal_nonneg_and_order_pos_of_continuous_comp_algebraMap ρ h
  exact (isEmbedding_of_forall_addVal_nonneg_of_order_pos ρ hpow he).continuous

/-- **Continuity criterion for ring homomorphisms between Puiseux fields**: `ρ` is continuous if
and only if it sends `K⟦X⟧` into the valuation ring and sends `t` to a series of strictly positive
order. -/
theorem continuous_ringHom_iff (ρ : puiseuxField K →+* puiseuxField L) :
    Continuous ρ ↔
      (∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f))) ∧
        0 < (ρ (single K 1 1) : HahnSeries ℚ L).order :=
  ⟨fun h ↦ forall_addVal_nonneg_and_order_pos_of_continuous_comp_algebraMap ρ
    (h.comp continuous_algebraMap_laurentSeries),
    fun ⟨hpow, he⟩ ↦ (isEmbedding_of_forall_addVal_nonneg_of_order_pos ρ hpow he).continuous⟩

/-- **Automatic bicontinuity**: every continuous ring isomorphism between Puiseux fields is a
homeomorphism. -/
theorem isHomeomorph_ringEquiv_iff (e : puiseuxField K ≃+* puiseuxField L) :
    IsHomeomorph e ↔ Continuous e :=
  ⟨IsHomeomorph.continuous, fun h ↦
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨(isEmbedding_ringHom_iff_continuous e.toRingHom).mpr h, e.surjective⟩⟩

/-- Every continuous ring isomorphism between Puiseux fields has a continuous inverse. -/
theorem continuous_symm_of_continuous_ringEquiv {e : puiseuxField K ≃+* puiseuxField L}
    (he : Continuous e) : Continuous e.symm :=
  ((e.toEquiv.isHomeomorph_iff).mp ((isHomeomorph_ringEquiv_iff e).mpr he)).2

/-- For a `K`-algebra endomorphism `ρ` of `puiseuxField K` sending `K⟦X⟧` into the valuation ring,
the image of `t` automatically has strictly positive order. -/
theorem order_map_single_one_pos_of_forall_addVal_nonneg
    (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal K (ρ (algebraMap K⟦X⟧ (puiseuxField K) f))) :
    0 < (ρ (single K 1 1) : HahnSeries ℚ K).order := by
  have hρt_ne : (ρ (single K 1 1) : HahnSeries ℚ K) ≠ 0 :=
    coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr
      ((single_eq_zero_iff (q := 1)).not.mpr one_ne_zero))
  have hρt_nonneg : 0 ≤ addVal K (ρ (single K 1 1)) := by
    simpa [algebraMap_powerSeries_X] using hρ PowerSeries.X
  have hnonneg : 0 ≤ (ρ (single K 1 1) : HahnSeries ℚ K).order := by
    rwa [addVal_apply, ← order_eq_orderTop_of_ne_zero hρt_ne, WithTop.coe_nonneg] at hρt_nonneg
  refine lt_of_le_of_ne' hnonneg fun h0 ↦ ?_
  set c : K := (ρ (single K 1 1) : HahnSeries ℚ K).coeff 0 with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, ← h0, ← leadingCoeff_eq]
    exact leadingCoeff_ne_zero.mpr hρt_ne
  have hu : IsUnit (PowerSeries.X - PowerSeries.C c) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_X,
      PowerSeries.constantCoeff_C, zero_sub]
    exact hc0.isUnit.neg
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hmul : (ρ (single K 1 1) - algebraMap K (puiseuxField K) c) *
      ρ (algebraMap K⟦X⟧ (puiseuxField K) g) = 1 := by
    have hXc : ρ (algebraMap K⟦X⟧ (puiseuxField K) (PowerSeries.X - PowerSeries.C c)) =
        ρ (single K 1 1) - algebraMap K (puiseuxField K) c := by
      rw [map_sub, map_sub, algebraMap_powerSeries_X, ← PowerSeries.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K K⟦X⟧ (puiseuxField K), AlgHom.commutes]
    rw [← hXc, ← map_mul, ← map_mul, hg, map_one, map_one]
  have h1 : valuation K (ρ (single K 1 1) - algebraMap K (puiseuxField K) c) < 1 :=
    valuation_lt_one_iff.mpr (addVal_sub_algebraMap_coeff_zero_pos_of_addVal_nonneg hρt_nonneg)
  have h2 : valuation K (ρ (algebraMap K⟦X⟧ (puiseuxField K) g)) ≤ 1 :=
    valuation_le_one_iff.mpr (hρ g)
  have hval_lt : valuation K ((ρ (single K 1 1) - algebraMap K (puiseuxField K) c) *
      ρ (algebraMap K⟦X⟧ (puiseuxField K) g)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le h2) h1
  rw [hmul, map_one] at hval_lt
  exact lt_irrefl _ hval_lt

/-- **Continuity criterion for `K`-algebra endomorphisms of the Puiseux field**: a `K`-algebra
endomorphism is continuous if and only if it maps `K⟦X⟧` into the valuation ring. -/
theorem continuous_algHom_iff (ρ : puiseuxField K →ₐ[K] puiseuxField K) :
    Continuous ρ ↔ ∀ f : K⟦X⟧, 0 ≤ addVal K (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) :=
  ⟨fun h ↦ ((continuous_ringHom_iff ρ.toRingHom).mp h).1,
    fun h ↦ (continuous_ringHom_iff ρ.toRingHom).mpr
      ⟨h, order_map_single_one_pos_of_forall_addVal_nonneg ρ h⟩⟩

end TauCeti.puiseuxField
