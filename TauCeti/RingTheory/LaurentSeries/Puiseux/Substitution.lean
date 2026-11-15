/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.LaurentSeries.IntegrallyClosed
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.RingTheory.LaurentSeries.Cartier
import TauCeti.RingTheory.LaurentSeries.Colimit
import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial
import TauCeti.RingTheory.LaurentSeries.Root
import TauCeti.RingTheory.PowerSeries.Hensel

/-!
# Valuation scaling, continuity, and substitution lifts on the Puiseux field

Let `K` be a field and `puiseuxField K` the field of Puiseux series over `K`, endowed with its
additive valuation `addVal K` and valuation topology from `valuation K`. Through the level-one
embedding `K⟦X⟧ → K⸨X⸩ → puiseuxField K`, the Puiseux field is a `K⟦X⟧`-algebra.

The first part of this file identifies the integral closure of `K⟦X⟧` in `puiseuxField K` with the
valuation ring `{x | valuation K x ≤ 1}`, proves that `K` is integrally closed in
`puiseuxField K` (so all roots of unity of `puiseuxField K` lie in `K`), and shows that if
`y ^ d` lies in level `m`, then `y` lies in level `m * d`, in every characteristic and without
auxiliary assumptions on `K`.

The second part deduces rigidity of ring homomorphisms `ρ : puiseuxField K →+* puiseuxField L`
between Puiseux fields: whenever `ρ` sends `K⟦X⟧` into the valuation ring of `puiseuxField L`, it
scales rational orders everywhere by the rational order of `ρ t`. Consequently, `ρ` is a
topological embedding if and only if it is continuous, if and only if its restriction to `K⸨X⸩` is
continuous, if and only if it maps `K⟦X⟧` into the valuation ring and sends `t` to a series of
strictly positive order. In particular, every continuous ring isomorphism between Puiseux fields is
a homeomorphism, and for `K`-algebra endomorphisms of `puiseuxField K` positivity of the order of
`ρ t` follows automatically from preserving nonnegativity of orders on `K⟦X⟧`.

The third part applies this to algebraic lifts of Laurent-series substitutions
`LaurentSeries.substAlgHom` and formal-coordinate automorphisms `LaurentSeries.substAlgEquiv`:
every algebraic lift to `puiseuxField K` is automatically continuous (and bicontinuous in the
coordinate case) and restricts on every ramified level `n` to a Laurent substitution `ψ` satisfying
`ψ ^ n = φ.expand n`.

Finally, when the unit group `Kˣ` is `ℕ`-rootable (for instance when `K` is algebraically closed,
in any characteristic), `(puiseuxField K)ˣ` is `ℕ`-rootable as well; choosing a compatible family
of `n`-th roots of `φ` and descending along the colimit presentation `levelCoconeIsColimit`
constructs continuous `K`-algebra endomorphisms lifting arbitrary nonzero substitutions `X ↦ φ`
with `constantCoeff φ = 0`, and bicontinuous `K`-algebra automorphisms lifting arbitrary formal
coordinates `φ : FormalCoordinate K`.

## Main definitions

* `TauCeti.puiseuxField.algebraPowerSeries`: the `K⟦X⟧`-algebra structure on `puiseuxField K`.
* `TauCeti.puiseuxField.continuousAlgHomOfSubstAlgHom`: bundles any `K`-algebra lift of
  `LaurentSeries.substAlgHom` as a continuous `K`-algebra endomorphism of `puiseuxField K`.
* `TauCeti.puiseuxField.continuousAlgEquivOfSubstAlgEquiv`: bundles any `K`-algebra automorphism
  lifting `LaurentSeries.substAlgEquiv` as a bicontinuous `K`-algebra automorphism.
* `TauCeti.puiseuxField.instRootableByUnitsNat`: `(puiseuxField K)ˣ` is `ℕ`-rootable whenever
  `Kˣ` is `ℕ`-rootable.

## Main results

* `TauCeti.puiseuxField.isIntegral_powerSeries_iff`: `x : puiseuxField K` is integral over `K⟦X⟧`
  if and only if `valuation K x ≤ 1`.
* `TauCeti.puiseuxField.isIntegrallyClosedIn`: `K` is integrally closed in `puiseuxField K`.
* `TauCeti.puiseuxField.mem_range_levelEmbedding_of_pow_mem_range`: if `y ^ d` lies in level `m`,
  then `y` lies in level `m * d`.
* `TauCeti.puiseuxField.order_map_eq_mul_of_forall_powerSeries`: any ring homomorphism sending
  `K⟦X⟧` into the valuation ring multiplies rational orders by `(ρ t).order`.
* `TauCeti.puiseuxField.isEmbedding_ringHom_iff_continuous`,
  `TauCeti.puiseuxField.continuous_ringHom_iff`,
  `TauCeti.puiseuxField.isHomeomorph_ringEquiv_iff`: characterizations of continuity, topological
  embeddings, and homeomorphisms between Puiseux fields.
* `TauCeti.puiseuxField.continuous_algHom_iff`: a `K`-algebra endomorphism of `puiseuxField K` is
  continuous if and only if it maps `K⟦X⟧` into the valuation ring.
* `TauCeti.puiseuxField.exists_substAlgHom_apply_levelEmbedding`: every algebraic lift of
  `LaurentSeries.substAlgHom` preserves each ramified level via a Laurent substitution.
* `TauCeti.puiseuxField.nonempty_rootableBy_units_nat_iff`: `(puiseuxField K)ˣ` is `ℕ`-rootable if
  and only if `Kˣ` is `ℕ`-rootable.
* `TauCeti.puiseuxField.exists_continuousAlgHom_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv`: existence of
  continuous substitution endomorphisms and bicontinuous coordinate automorphisms when
  `[RootableBy Kˣ ℕ]`, in arbitrary characteristic.
-/

public section

open Filter HahnSeries LaurentSeries Polynomial Topology WithZero
open scoped LaurentSeries Polynomial PowerSeries

namespace TauCeti.puiseuxField

/-! ### Power-series algebra structure, integral closure, and level membership of roots -/

section IntegralAndRoots

variable {K : Type*} [Field K]

private theorem coe_ne_zero {x : puiseuxField K} (hx : x ≠ 0) :
    (x : HahnSeries ℚ K) ≠ 0 :=
  ZeroMemClass.coe_eq_zero.not.mpr hx

/-- Integer power of a Puiseux monomial `single K q a`. -/
@[simp]
theorem single_zpow (q : ℚ) (a : K) (k : ℤ) :
    single K q a ^ k = single K (k * q) (a ^ k) := by
  cases k with
  | ofNat m =>
    simp [Int.ofNat_eq_natCast, single_pow]
  | negSucc m =>
    rw [zpow_negSucc, zpow_negSucc, single_pow, inv_single, Int.cast_negSucc, neg_mul]

/-- Rational order of an `m`-th power of a Puiseux series. -/
theorem order_pow (x : puiseuxField K) (m : ℕ) :
    ((x ^ m : puiseuxField K) : HahnSeries ℚ K).order =
      (m : ℚ) * (x : HahnSeries ℚ K).order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne m 0 with rfl | hm
    · simp [HahnSeries.order_one]
    · simp [zero_pow hm]
  have hexp := valuation_eq_exp_neg_order (coe_ne_zero (pow_ne_zero m hx))
  rw [← valuation_apply, map_pow, valuation_apply, valuation_eq_exp_neg_order (coe_ne_zero hx),
    ← exp_nsmul, eq_comm, exp_inj, nsmul_eq_mul, mul_neg, neg_inj] at hexp
  exact hexp

/-- Rational order of a `k`-th integer power of a Puiseux series. -/
theorem order_zpow (x : puiseuxField K) (k : ℤ) :
    ((x ^ k : puiseuxField K) : HahnSeries ℚ K).order =
      (k : ℚ) * (x : HahnSeries ℚ K).order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne k 0 with rfl | hk
    · simp [HahnSeries.order_one]
    · simp [zero_zpow k hk]
  have hexp := valuation_eq_exp_neg_order (coe_ne_zero (zpow_ne_zero k hx))
  rw [← valuation_apply, map_zpow₀, valuation_apply, valuation_eq_exp_neg_order (coe_ne_zero hx),
    ← exp_zsmul, eq_comm, exp_inj, zsmul_eq_mul, mul_neg, neg_inj] at hexp
  exact hexp

variable (K) in
/-- The Puiseux field is a `K⟦X⟧`-algebra through `K⟦X⟧ → K⸨X⸩ → puiseuxField K`. -/
noncomputable instance algebraPowerSeries : Algebra K⟦X⟧ (puiseuxField K) :=
  ((algebraMap K⸨X⸩ (puiseuxField K)).comp (algebraMap K⟦X⟧ K⸨X⸩)).toAlgebra

/-- The `K⟦X⟧`-algebra map into the Puiseux field factors through coercion to `K⸨X⸩`. -/
theorem algebraMap_powerSeries_apply (f : K⟦X⟧) :
    algebraMap K⟦X⟧ (puiseuxField K) f = algebraMap K⸨X⸩ (puiseuxField K) (f : K⸨X⸩) :=
  (rfl)

/-- As a Hahn series, the image of `f : K⟦X⟧` in the Puiseux field is its level-one embedding. -/
@[simp]
theorem coe_algebraMap_powerSeries (f : K⟦X⟧) :
    (algebraMap K⟦X⟧ (puiseuxField K) f : HahnSeries ℚ K) = ramifiedEmbedding K 1 (f : K⸨X⸩) := by
  rw [algebraMap_powerSeries_apply, coe_algebraMap_laurentSeries]

/-- Scalar actions of `K⟦X⟧` and `K⸨X⸩` on `puiseuxField K` form a scalar tower. -/
instance isScalarTower_powerSeries_laurentSeries :
    IsScalarTower K⟦X⟧ K⸨X⸩ (puiseuxField K) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Scalar actions of `K` and `K⟦X⟧` on `puiseuxField K` form a scalar tower. -/
instance isScalarTower_powerSeries : IsScalarTower K K⟦X⟧ (puiseuxField K) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [algebraMap_powerSeries_apply, ← _root_.LaurentSeries.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩,
      ← IsScalarTower.algebraMap_apply K K⸨X⸩ (puiseuxField K)]

/-- The `K⟦X⟧`-algebra map sends `X` to the Puiseux parameter `t = single K 1 1`. -/
@[simp]
theorem algebraMap_powerSeries_X :
    algebraMap K⟦X⟧ (puiseuxField K) PowerSeries.X = single K 1 1 := by
  rw [algebraMap_powerSeries_apply, PowerSeries.coe_X, algebraMap_laurentSeries_apply]
  exact levelEmbedding_single_self 1

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
    valuation K (algebraMap K⟦X⟧ (puiseuxField K) f) ≤ 1 := by
  simpa using (valuation_le_exp_neg_iff (K := K) 0).mpr (addVal_algebraMap_powerSeries_nonneg f)

/-- **Integral closure of `K⟦X⟧` in the Puiseux field**: a Puiseux series is integral over `K⟦X⟧`
if and only if its multiplicative valuation is at most `1`. -/
theorem isIntegral_powerSeries_iff {x : puiseuxField K} :
    IsIntegral K⟦X⟧ x ↔ valuation K x ≤ 1 := by
  refine ⟨fun ⟨P, hPm, hP0⟩ ↦ ?_, fun hv ↦ ?_⟩
  · let ι : K⟦X⟧ →+* (valuation K).integer :=
      (algebraMap K⟦X⟧ (puiseuxField K)).codRestrict (valuation K).integer
        valuation_algebraMap_powerSeries_le_one
    have hsub : (algebraMap (valuation K).integer (puiseuxField K)).comp ι =
        algebraMap K⟦X⟧ (puiseuxField K) := rfl
    have hint : IsIntegral (valuation K).integer x :=
      ⟨P.map ι, hPm.map ι, by rw [eval₂_map, hsub, hP0]⟩
    exact (Valuation.integer.integers (valuation K)).isIntegral_iff_v_le_one.mp hint
  · obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
    obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
    have hord : (0 : WithTop ℤ) ≤ f.orderTop := by
      have h0 : 0 ≤ addVal K (levelEmbedding K n f) := by
        simpa using (valuation_le_exp_neg_iff (K := K) 0).mp hv
      exact (div_le_addVal_levelEmbedding_iff n f 0).mp (by simpa using h0)
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
  rw [isIntegral_powerSeries_iff]
  simpa using (valuation_le_exp_neg_iff (K := K) 0)

variable (K) in
/-- A field `K` is integrally closed in `puiseuxField K`: the Puiseux series algebraic over `K`
are the constants. -/
instance isIntegrallyClosedIn : IsIntegrallyClosedIn K (puiseuxField K) := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K (puiseuxField K)).injective, fun {x} hx ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    ((isIntegral_algHom_iff (levelEmbedding K n) (levelEmbedding K n).injective).mp hx)
  exact ⟨c, by rw [← AlgHom.commutes (levelEmbedding K n), hc]⟩

/-- Every `d`-th root of unity in `puiseuxField K` is the image of a `d`-th root of unity in `K`. -/
theorem exists_rootsOfUnity_algebraMap_eq {d : ℕ+} {w : puiseuxField K} (hw : w ^ (d : ℕ) = 1) :
    ∃ η : rootsOfUnity d K, algebraMap K (puiseuxField K) ((η : Kˣ) : K) = w := by
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    (IsIntegral.of_pow (R := K) d.pos (hw ▸ isIntegral_one))
  have hcd : c ^ (d : ℕ) = 1 :=
    (algebraMap K (puiseuxField K)).injective (by rw [map_pow, hc, hw, map_one])
  exact ⟨rootsOfUnity.mkOfPowEq c hcd, by rw [rootsOfUnity.coe_mkOfPowEq, hc]⟩

/-- In characteristic `p`, raising a Puiseux series `y` to the `p`-th power moves its `q`-th
coefficient (raised to the `p`-th power) to exponent `p * q`. -/
theorem coeff_pow_charP (p : ℕ) [CharP K p] (y : puiseuxField K) (q : ℚ) :
    ((y ^ p : puiseuxField K) : HahnSeries ℚ K).coeff ((p : ℚ) * q) =
      ((y : HahnSeries ℚ K).coeff q) ^ p := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  let d : ℕ+ := ⟨p, Nat.pos_of_ne_zero hp0⟩
  have hp_prime : Nat.Prime d := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  have hexp : ExpChar K d := .prime hp_prime
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding y
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hn
  have hd_eq : (d : ℕ) = p := rfl
  rw [← hd_eq, ← map_pow, ← mapRingHom_frobenius_expand d g, coe_levelEmbedding,
    coe_levelEmbedding]
  by_cases hq : q.den ∣ n
  · obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hq
    have hmul : (d : ℚ) * ((k : ℚ) / n) = (((d : ℤ) * k : ℤ) : ℚ) / n := by
      push_cast
      ring
    rw [hmul, coeff_ramifiedEmbedding_intCast_div, coeff_ramifiedEmbedding_intCast_div,
      coeff_mapRingHom, _root_.LaurentSeries.coeff_expand_mul, frobenius_def]
  · rw [coeff_ramifiedEmbedding_of_not_den_dvd n g hq, zero_pow d.ne_zero]
    by_cases hmq : ((d : ℚ) * q).den ∣ n
    · obtain ⟨m, hm⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hmq
      rw [hm, coeff_ramifiedEmbedding_intCast_div, coeff_mapRingHom]
      have hndvd : ¬ ((d : ℤ) ∣ m) := by
        rintro ⟨k, rfl⟩
        apply hq
        refine (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mpr ⟨k, ?_⟩
        have hd_ne : (d : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
        apply mul_left_cancel₀ hd_ne
        rw [hm]
        push_cast
        ring
      rw [_root_.LaurentSeries.coeff_expand_of_not_dvd d g hndvd, map_zero]
    · exact coeff_ramifiedEmbedding_of_not_den_dvd n _ hmq

/-- If `z ^ d` is the level-`m` embedding of a unit power series `u`, then `z` has order `0` and
the `d`-th power of its constant term is `constantCoeff u`. -/
private theorem coeff_zero_pow_eq_constantCoeff_of_pow_eq_levelEmbedding {m d : ℕ+}
    {z : puiseuxField K} {u : K⟦X⟧} (hu : IsUnit u)
    (hzd : z ^ (d : ℕ) = levelEmbedding K m (u : K⸨X⸩)) :
    (z : HahnSeries ℚ K).coeff 0 ≠ 0 ∧
      PowerSeries.constantCoeff u = ((z : HahnSeries ℚ K).coeff 0) ^ (d : ℕ) := by
  have hz0 : z ≠ 0 := fun h0 ↦
    hu.ne_zero (ofPowerSeries_injective ((levelEmbedding K m).toRingHom.injective
      (by simpa [h0, zero_pow d.ne_zero] using hzd.symm)))
  have hz_ord : (z : HahnSeries ℚ K).order = 0 := by
    have hzd_ord : ((z ^ (d : ℕ) : puiseuxField K) : HahnSeries ℚ K).order = 0 := by
      rw [hzd, coe_levelEmbedding, order_ramifiedEmbedding, PowerSeries.order_coe,
        PowerSeries.order_zero_of_isUnit hu, ENat.toNat_zero, Nat.cast_zero, Int.cast_zero,
        zero_div]
    rw [order_pow] at hzd_ord
    exact (mul_eq_zero.mp hzd_ord).resolve_left (by exact_mod_cast d.ne_zero)
  have hlead_pow : ∀ (x : HahnSeries ℚ K) (k : ℕ), (x ^ k).leadingCoeff = x.leadingCoeff ^ k := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]
  have hc0 : (z : HahnSeries ℚ K).coeff 0 ≠ 0 := by
    rw [← hz_ord, ← leadingCoeff_eq]
    exact leadingCoeff_ne_zero.mpr (coe_ne_zero hz0)
  refine ⟨hc0, ?_⟩
  have hlhs : ((z ^ (d : ℕ) : puiseuxField K) : HahnSeries ℚ K).leadingCoeff =
      PowerSeries.constantCoeff u := by
    rw [hzd, coe_levelEmbedding, leadingCoeff_eq, order_ramifiedEmbedding, PowerSeries.order_coe,
      PowerSeries.order_zero_of_isUnit hu, ENat.toNat_zero, Nat.cast_zero,
      coeff_ramifiedEmbedding_intCast_div]
    simp [PowerSeries.coeff_coe]
  rw [← hlhs, IntermediateField.coe_pow, hlead_pow, leadingCoeff_eq, hz_ord]

/-- When `(d : K) ≠ 0`, if `y ^ d = levelEmbedding K m f`, then rescaling `y` by
`levelEmbedding K (m * d) (single (-f.order) 1)` places it in the unramified level `m`. -/
theorem mul_mem_range_levelEmbedding_of_pow_eq {m d : ℕ+} (hd : ((d : ℕ) : K) ≠ 0)
    {y : puiseuxField K} {f : K⸨X⸩} (hf : y ^ (d : ℕ) = levelEmbedding K m f) :
    levelEmbedding K (m * d) (HahnSeries.single (-f.order) 1) * y ∈
      (levelEmbedding K m).range := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have hy0 : y = 0 := (pow_eq_zero_iff d.ne_zero).mp (by simpa using hf)
    simp [hy0]
  set s : puiseuxField K := levelEmbedding K (m * d) (HahnSeries.single (-f.order) 1)
  set z : puiseuxField K := s * y
  have hzd : z ^ (d : ℕ) = levelEmbedding K m (f.powerSeriesPart : K⸨X⸩) := by
    rw [mul_pow, ← map_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, hf]
    have hexp : levelEmbedding K (m * d) (HahnSeries.single ((d : ℤ) * -f.order) 1) =
        levelEmbedding K m (HahnSeries.single (-f.order) 1) := by
      rw [← levelEmbedding_expand m d, expand_single]
    rw [hexp, ← map_mul]
    congr 1
    nth_rw 2 [← single_order_mul_powerSeriesPart f]
    rw [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
      ← HahnSeries.C_apply, map_one, one_mul]
  obtain ⟨hc0, hc_pow⟩ := coeff_zero_pow_eq_constantCoeff_of_pow_eq_levelEmbedding
    (TauCeti.LaurentSeries.isUnit_powerSeriesPart hf0) hzd
  obtain ⟨v, hv, -⟩ := PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow hd hc0 hc_pow
  set z₀ : puiseuxField K := levelEmbedding K m (v : K⸨X⸩)
  have hz₀_pow : z₀ ^ (d : ℕ) = z ^ (d : ℕ) := by
    rw [hzd, ← map_pow, ← PowerSeries.coe_pow, hv]
  have hz0 : z ≠ 0 := fun h0 ↦ hc0 (by simp [h0])
  have hz₀_ne : z₀ ≠ 0 := fun h0 ↦
    pow_ne_zero (d : ℕ) hz0 (by rw [← hz₀_pow, h0, zero_pow d.ne_zero])
  obtain ⟨η, hη⟩ := exists_rootsOfUnity_algebraMap_eq (d := d) (w := z / z₀)
    (by rw [div_pow, hz₀_pow, div_self (pow_ne_zero (d : ℕ) hz0)])
  refine (AlgHom.mem_range _).mpr ⟨algebraMap K K⸨X⸩ ((η : Kˣ) : K) * (v : K⸨X⸩), ?_⟩
  rw [map_mul, AlgHom.commutes, hη, div_mul_cancel₀ _ hz₀_ne]

/-- In positive characteristic `p`, an exponent `p * q` lies in the support of `y ^ p` if and only
if `q` lies in the support of `y`. -/
theorem mul_mem_support_pow_charP_iff {p : ℕ} [CharP K p] (hp : p ≠ 0)
    (y : puiseuxField K) (q : ℚ) :
    (p : ℚ) * q ∈ ((y ^ p : puiseuxField K) : HahnSeries ℚ K).support ↔
      q ∈ (y : HahnSeries ℚ K).support := by
  rw [mem_support, mem_support, coeff_pow_charP p y q, pow_ne_zero_iff hp]

/-- **Level membership of roots**: over any field `K`, if `y ^ d` lies in the level-`m` subfield
of `puiseuxField K`, then `y` lies in the level-`(m * d)` subfield. -/
theorem mem_range_levelEmbedding_of_pow_mem_range {m d : ℕ+} {y : puiseuxField K}
    (hy : y ^ (d : ℕ) ∈ (levelEmbedding K m).range) :
    y ∈ (levelEmbedding K (m * d)).range := by
  induction hd : (d : ℕ) using Nat.strong_induction_on generalizing m d y with
  | ind n ih =>
    subst hd
    by_cases hd1 : d = 1
    · subst hd1
      simpa using hy
    · obtain ⟨p, hp, hpd⟩ := PNat.exists_prime_and_dvd hd1
      let k := d.divExact p
      have hdk : k * p = d := by rw [mul_comm, PNat.mul_div_exact hpd]
      have hk_lt : (k : ℕ) < d := by
        have hp1 : 1 < (p : ℕ) := hp.one_lt
        have hk0 : 0 < (k : ℕ) := k.pos
        have : (k : ℕ) * p = d := congrArg PNat.val hdk
        nlinarith
      have hyp : (y ^ (p : ℕ)) ^ (k : ℕ) ∈ (levelEmbedding K m).range := by
        rwa [← pow_mul, mul_comm (p : ℕ), ← PNat.mul_coe, hdk]
      have hyp_mem : y ^ (p : ℕ) ∈ (levelEmbedding K (m * k)).range :=
        ih k hk_lt hyp rfl
      have hy_mem : y ∈ (levelEmbedding K (m * k * p)).range := by
        by_cases hp0 : ((p : ℕ) : K) = 0
        · have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
          rw [mem_range_levelEmbedding_iff, mem_range_ramifiedEmbedding_iff] at hyp_mem ⊢
          intro q hq
          obtain ⟨j, hj⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div (m * k).ne_zero).mp
            (hyp_mem _ ((mul_mem_support_pow_charP_iff p.ne_zero y q).mpr hq))
          refine (Rat.den_dvd_iff_exists_eq_intCast_div (m * k * p).ne_zero).mpr ⟨j, ?_⟩
          have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast p.ne_zero
          apply mul_left_cancel₀ hp_ne
          rw [hj]; simp only [PNat.mul_coe, Nat.cast_mul]; field_simp
        · obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hyp_mem
          set s : puiseuxField K := levelEmbedding K (m * k * p) (HahnSeries.single (-f.order) 1)
          have hs0 : s ≠ 0 := by simp [s]
          have hy_eq : y = s⁻¹ * (s * y) := by rw [inv_mul_cancel_left₀ hs0]
          rw [hy_eq]
          refine Subalgebra.mul_mem _ ((AlgHom.mem_range _).mpr ⟨HahnSeries.single f.order 1, ?_⟩)
            (range_levelEmbedding_le_of_dvd (dvd_mul_right (m * k) p)
              (mul_mem_range_levelEmbedding_of_pow_eq hp0 hf.symm))
          rw [← map_inv₀ (levelEmbedding K (m * k * p)), HahnSeries.inv_single, inv_one, neg_neg]
      rwa [mul_assoc, hdk] at hy_mem

/-- If `y ^ d` lies in `K⸨X⸩` (level one), then `y` lies in level `d`. -/
theorem mem_range_levelEmbedding_of_pow_eq_algebraMap {d : ℕ+} {y : puiseuxField K} {f : K⸨X⸩}
    (hy : y ^ (d : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) f) :
    y ∈ (levelEmbedding K d).range := by
  have h1 : y ^ (d : ℕ) ∈ (levelEmbedding K 1).range :=
    (AlgHom.mem_range _).mpr ⟨f, (algebraMap_laurentSeries_apply f).symm.trans hy.symm⟩
  simpa using mem_range_levelEmbedding_of_pow_mem_range h1

end IntegralAndRoots

/-! ### Valuation scaling, automatic continuity, and automatic bicontinuity -/

section Continuity

variable {K L : Type*} [Field K] [Field L]

/-- A ring homomorphism between Puiseux fields that maps `K⟦X⟧` into the valuation ring of
`puiseuxField L` maps the entire valuation ring of `puiseuxField K` into that of
`puiseuxField L`. -/
theorem valuation_le_one_of_forall_powerSeries (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1)
    {x : puiseuxField K} (hx : valuation K x ≤ 1) :
    valuation L (ρ x) ≤ 1 := by
  obtain ⟨P, hPm, hP0⟩ := isIntegral_powerSeries_iff.mpr hx
  let ι : K⟦X⟧ →+* (valuation L).integer :=
    (ρ.comp (algebraMap K⟦X⟧ (puiseuxField K))).codRestrict (valuation L).integer hρ
  have hsub : (algebraMap (valuation L).integer (puiseuxField L)).comp ι =
      ρ.comp (algebraMap K⟦X⟧ (puiseuxField K)) := rfl
  have hint : IsIntegral (valuation L).integer (ρ x) := by
    refine ⟨P.map ι, hPm.map ι, ?_⟩
    rw [eval₂_map, hsub, ← hom_eval₂, hP0, map_zero]
  exact (Valuation.integer.integers (valuation L)).isIntegral_iff_v_le_one.mp hint

/-- Additive-valuation form of `valuation_le_one_of_forall_powerSeries`: nonnegativity of rational
orders on `K⟦X⟧` propagates to all series of nonnegative order in `puiseuxField K`. -/
theorem addVal_nonneg_of_forall_powerSeries (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    {x : puiseuxField K} (hx : 0 ≤ addVal K x) :
    0 ≤ addVal L (ρ x) := by
  have hv : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1 := fun f ↦ by
    simpa using (valuation_le_exp_neg_iff (K := L) 0).mpr (hρ f)
  have hx' : valuation K x ≤ 1 := by
    simpa using (valuation_le_exp_neg_iff (K := K) 0).mpr hx
  simpa using (valuation_le_exp_neg_iff (K := L) 0).mp
    (valuation_le_one_of_forall_powerSeries ρ hv hx')

/-- Under a ring homomorphism sending `K⟦X⟧` into the valuation ring, any valuation unit `u` maps
to a series of rational order `0`. -/
private theorem order_map_eq_zero_of_valuation_eq_one (ρ : puiseuxField K →+* puiseuxField L)
    (hv : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1)
    {u : puiseuxField K} (hu_val : valuation K u = 1) :
    (ρ u : HahnSeries ℚ L).order = 0 := by
  have hu_ne : u ≠ 0 := fun h0 ↦ by simp [h0] at hu_val
  have hρu_ne : ρ u ≠ 0 := (map_ne_zero_iff ρ ρ.injective).mpr hu_ne
  have hρu_val : valuation L (ρ u) = 1 := by
    apply le_antisymm (valuation_le_one_of_forall_powerSeries ρ hv hu_val.le)
    have hinv : valuation L (ρ u⁻¹) ≤ 1 :=
      valuation_le_one_of_forall_powerSeries ρ hv (by rw [map_inv₀, hu_val, inv_one])
    rw [map_inv₀, map_inv₀] at hinv
    have hne : valuation L (ρ u) ≠ 0 := (Valuation.ne_zero_iff _).mpr hρu_ne
    exact (inv_le_one₀ (lt_of_le_of_ne' zero_le hne)).mp hinv
  have hexp := valuation_eq_exp_neg_order (coe_ne_zero hρu_ne)
  rw [← valuation_apply, hρu_val, ← exp_zero, eq_comm, exp_inj, neg_eq_zero] at hexp
  exact hexp

/-- **Valuation scaling**: any ring homomorphism `ρ : puiseuxField K →+* puiseuxField L` that sends
`K⟦X⟧` into the valuation ring multiplies the rational order of every Puiseux series by the
rational order of `ρ (single K 1 1)`. -/
theorem order_map_eq_mul_of_forall_powerSeries (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ L).order =
      (x : HahnSeries ℚ K).order * (ρ (single K 1 1) : HahnSeries ℚ L).order := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hv : ∀ f : K⟦X⟧, valuation L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)) ≤ 1 := fun f ↦ by
    simpa using (valuation_le_exp_neg_iff (K := L) 0).mpr (hρ f)
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
    rw [← hs_pow, map_pow, order_pow]
  have hq_ord : (ρ (single K q 1) : HahnSeries ℚ L).order =
      q * (ρ (single K 1 1) : HahnSeries ℚ L).order := by
    have hs_zpow : s ^ q.num = single K q 1 := by
      rw [single_zpow, one_zpow, mul_one_div, hn_coe, Rat.num_div_den]
    have hqn : (q.num : ℚ) = q * (n : ℚ) := by
      rw [hn_coe]
      exact (div_eq_iff (by exact_mod_cast q.den_nz)).mp q.num_div_den
    rw [← hs_zpow, map_zpow₀, order_zpow, hqn, mul_assoc, ← hn_ord]
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
theorem le_addVal_map_iff_of_forall_powerSeries (ρ : puiseuxField K →+* puiseuxField L)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f)))
    (he : 0 < (ρ (single K 1 1) : HahnSeries ℚ L).order) (q : ℚ) (x : puiseuxField K) :
    (((q * (ρ (single K 1 1) : HahnSeries ℚ L).order : ℚ) : WithTop ℚ) ≤ addVal L (ρ x)) ↔
      (q : WithTop ℚ) ≤ addVal K x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hρx := coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr hx0)
  rw [addVal_apply, addVal_apply, ← order_eq_orderTop_of_ne_zero hρx,
    ← order_eq_orderTop_of_ne_zero (coe_ne_zero hx0), WithTop.coe_le_coe, WithTop.coe_le_coe,
    order_map_eq_mul_of_forall_powerSeries ρ hρ x, mul_le_mul_iff_of_pos_right he]

/-- If `ρ` is continuous on `K⸨X⸩`, then `ρ (single K 1 1)` has strictly positive rational order. -/
private theorem order_map_single_one_pos_of_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L)
    (hcont : Continuous fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    0 < (ρ (single K 1 1) : HahnSeries ℚ L).order := by
  let φ : K⸨X⸩ →+* puiseuxField L := ρ.comp (algebraMap K⸨X⸩ (puiseuxField K))
  have hφ_cont : Continuous φ := hcont
  have hφ_single_one : φ (HahnSeries.single 1 1) = ρ (single K 1 1) := by
    rw [RingHom.comp_apply, algebraMap_laurentSeries_apply]
    exact congrArg ρ (levelEmbedding_single_self 1)
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
    order_pow, WithTop.coe_le_coe] at hk1
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
  have hφ_single_one : φ (HahnSeries.single 1 1) = ρ (single K 1 1) :=
    congrArg ρ (levelEmbedding_single_self 1)
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
    order_pow, order_pow, WithTop.coe_le_coe] at hk1
  push_cast at hk1
  linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hMq]

/-- Polynomial case of `forall_powerSeries_and_order_pos_of_continuous_comp_algebraMap`. -/
private theorem addVal_map_polynomial_nonneg_of_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L)
    (he : 0 ≤ (ρ (single K 1 1) : HahnSeries ℚ L).order)
    (hconst : ∀ c : K, 0 ≤ addVal L (ρ (algebraMap K (puiseuxField K) c))) (P : K[X]) :
    0 ≤ addVal L (ρ (algebraMap K⸨X⸩ (puiseuxField K) ((P : K⟦X⟧) : K⸨X⸩))) := by
  let φ : K⸨X⸩ →+* puiseuxField L := ρ.comp (algebraMap K⸨X⸩ (puiseuxField K))
  have hφ_apply (g : K⸨X⸩) : φ g = ρ (algebraMap K⸨X⸩ (puiseuxField K) g) := rfl
  rw [← hφ_apply]
  have hφ_single_one : φ (HahnSeries.single 1 1) = ρ (single K 1 1) := by
    rw [hφ_apply, algebraMap_laurentSeries_apply]
    exact congrArg ρ (levelEmbedding_single_self 1)
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
    refine (valuation_le_exp_neg_iff (K := L) 0).mp ?_
    rw [neg_zero, exp_zero, map_mul, map_pow]
    have h1 : valuation L (ρ (algebraMap K (puiseuxField K) c)) ≤ 1 := by
      simpa using (valuation_le_exp_neg_iff (K := L) 0).mpr (hconst c)
    have h2 : valuation L (ρ (single K 1 1)) ≤ 1 := by
      simpa using (valuation_le_exp_neg_iff (K := L) 0).mpr hρt_pos
    exact (mul_le_of_le_one_right zero_le (pow_le_one' h2 j)).trans h1

/-- If `ρ : puiseuxField K →+* puiseuxField L` is continuous on `K⸨X⸩`, then `ρ` sends `K⟦X⟧` into
the valuation ring and sends `t` to a series of strictly positive order. -/
private theorem forall_powerSeries_and_order_pos_of_continuous_comp_algebraMap
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
theorem isEmbedding_of_forall_powerSeries (ρ : puiseuxField K →+* puiseuxField L)
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
    have hle := (le_addVal_map_iff_of_forall_powerSeries ρ hρ he (r / e) x).mpr hx
    rwa [Set.mem_ofPred_eq, ← hre]
  · refine hasBasis_nhds_zero.ge_iff.mpr fun q _ ↦ ?_
    refine eventually_comap.mpr (hasBasis_nhds_zero.eventually_iff.mpr ⟨q * e, trivial, ?_⟩)
    rintro _ hy x rfl
    exact (le_addVal_map_iff_of_forall_powerSeries ρ hρ he q x).mp hy

/-- **Automatic topological embedding**: a ring homomorphism between Puiseux fields is a
topological embedding if and only if it is continuous. -/
theorem isEmbedding_ringHom_iff_continuous (ρ : puiseuxField K →+* puiseuxField L) :
    IsEmbedding ρ ↔ Continuous ρ := by
  refine ⟨IsEmbedding.continuous, fun hcont ↦ ?_⟩
  obtain ⟨hpow, he⟩ := forall_powerSeries_and_order_pos_of_continuous_comp_algebraMap ρ
    (hcont.comp (continuous_levelEmbedding 1))
  exact isEmbedding_of_forall_powerSeries ρ hpow he

/-- Continuity of a ring homomorphism out of `puiseuxField K` into `puiseuxField L` is equivalent
to continuity of its restriction to `K⸨X⸩`. -/
theorem continuous_ringHom_iff_continuous_comp_algebraMap
    (ρ : puiseuxField K →+* puiseuxField L) :
    Continuous ρ ↔ Continuous fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f) := by
  refine ⟨fun h ↦ h.comp (continuous_levelEmbedding 1), fun h ↦ ?_⟩
  obtain ⟨hpow, he⟩ := forall_powerSeries_and_order_pos_of_continuous_comp_algebraMap ρ h
  exact (isEmbedding_of_forall_powerSeries ρ hpow he).continuous

/-- **Continuity criterion for ring homomorphisms between Puiseux fields**: `ρ` is continuous if
and only if it sends `K⟦X⟧` into the valuation ring and sends `t` to a series of strictly positive
order. -/
theorem continuous_ringHom_iff (ρ : puiseuxField K →+* puiseuxField L) :
    Continuous ρ ↔
      (∀ f : K⟦X⟧, 0 ≤ addVal L (ρ (algebraMap K⟦X⟧ (puiseuxField K) f))) ∧
        0 < (ρ (single K 1 1) : HahnSeries ℚ L).order :=
  ⟨fun h ↦ forall_powerSeries_and_order_pos_of_continuous_comp_algebraMap ρ
    (h.comp (continuous_levelEmbedding 1)),
    fun ⟨hpow, he⟩ ↦ (isEmbedding_of_forall_powerSeries ρ hpow he).continuous⟩

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

private theorem algebraMap_eq_single (c : K) :
    algebraMap K (puiseuxField K) c = single K 0 c := by
  have h1 : single K 0 (1 : K) = 1 :=
    Subtype.ext (by rw [coe_single, ← HahnSeries.C_apply, map_one, OneMemClass.coe_one])
  simpa [h1] using algebraMap_mul_single c 0 (1 : K)

/-- Subtracting the constant term from a Puiseux series of rational order `0` yields a series of
strictly positive additive valuation. -/
private theorem addVal_sub_algebraMap_coeff_zero_pos {x : puiseuxField K}
    (hx0 : (x : HahnSeries ℚ K).order = 0) :
    (0 : WithTop ℚ) <
      addVal K (x - algebraMap K (puiseuxField K) ((x : HahnSeries ℚ K).coeff 0)) := by
  set c : K := (x : HahnSeries ℚ K).coeff 0 with hc_def
  by_cases hsub : x - algebraMap K (puiseuxField K) c = 0
  · simp [hsub]
  have hsub' := coe_ne_zero hsub
  rw [addVal_apply, ← order_eq_orderTop_of_ne_zero hsub', WithTop.coe_pos]
  set q := ((x - algebraMap K (puiseuxField K) c : puiseuxField K) : HahnSeries ℚ K).order
  have hq_ne : ((x - algebraMap K (puiseuxField K) c : puiseuxField K) :
      HahnSeries ℚ K).coeff q ≠ 0 := by
    rw [← leadingCoeff_eq]
    exact leadingCoeff_ne_zero.mpr hsub'
  by_contra hle
  rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | hq0
  · have h1 : (x : HahnSeries ℚ K).coeff q = 0 := coeff_eq_zero_of_lt_order (hx0 ▸ hlt)
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

/-- For a `K`-algebra endomorphism `ρ` of `puiseuxField K` sending `K⟦X⟧` into the valuation ring,
the image of `t` automatically has strictly positive order. -/
theorem order_map_single_one_pos_of_forall_powerSeries
    (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (hρ : ∀ f : K⟦X⟧, 0 ≤ addVal K (ρ (algebraMap K⟦X⟧ (puiseuxField K) f))) :
    0 < (ρ (single K 1 1) : HahnSeries ℚ K).order := by
  have hρt_ne : (ρ (single K 1 1) : HahnSeries ℚ K) ≠ 0 :=
    coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr
      ((single_eq_zero_iff (q := 1)).not.mpr one_ne_zero))
  have hnonneg : 0 ≤ (ρ (single K 1 1) : HahnSeries ℚ K).order := by
    have := hρ PowerSeries.X
    rwa [algebraMap_powerSeries_X, addVal_apply, ← order_eq_orderTop_of_ne_zero hρt_ne,
      WithTop.coe_nonneg] at this
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
  have h1 : valuation K (ρ (single K 1 1) - algebraMap K (puiseuxField K) c) < 1 := by
    simpa using (valuation_lt_exp_neg_iff (K := K) 0).mpr
      (addVal_sub_algebraMap_coeff_zero_pos h0)
  have h2 : valuation K (ρ (algebraMap K⟦X⟧ (puiseuxField K) g)) ≤ 1 := by
    simpa using (valuation_le_exp_neg_iff (K := K) 0).mpr (hρ g)
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
      ⟨h, order_map_single_one_pos_of_forall_powerSeries ρ h⟩⟩

end Continuity

/-! ### Automatic continuity and level compatibility of substitution and coordinate lifts -/

section SubstLift

variable {K : Type*} [Field K]

/-- Two continuous `K`-algebra maps `K⸨X⸩ →ₐ[K] puiseuxField K` that agree on `X` are equal. -/
private theorem algHom_eq_of_continuous_of_single_one_eq
    {φ₁ φ₂ : K⸨X⸩ →ₐ[K] puiseuxField K} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hX : φ₁ (HahnSeries.single 1 1) = φ₂ (HahnSeries.single 1 1)) :
    φ₁ = φ₂ := by
  apply DFunLike.ext'
  refine LaurentPolynomial.denseRange_toLaurentSeries.equalizer h₁ h₂ (funext fun p ↦ ?_)
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [Function.comp_apply, map_add] at hp hq ⊢
    rw [hp, hq]
  | C_mul_T k c =>
    simp only [Function.comp_apply, map_mul, LaurentPolynomial.toLaurentSeries_C,
      LaurentPolynomial.toLaurentSeries_T, ← _root_.LaurentSeries.algebraMap_apply,
      AlgHom.commutes]
    rw [RatFunc.single_zpow, map_zpow₀, map_zpow₀, hX]

/-- If `y ^ n` is the level-one image of a nonzero power series `φ` with `constantCoeff φ = 0`,
then `y` is the level-`n` image of a nonzero power series `ψ` with `constantCoeff ψ = 0` and
`ψ ^ n = φ.expand n`. -/
private theorem exists_powerSeries_levelEmbedding_eq_of_pow_eq {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (n : ℕ+) {y : puiseuxField K}
    (hy : y ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩)) :
    ∃ (ψ : K⟦X⟧) (_ : PowerSeries.constantCoeff ψ = 0) (_ : ψ ≠ 0),
      ψ ^ (n : ℕ) = φ.expand n n.ne_zero ∧ levelEmbedding K n (ψ : K⸨X⸩) = y := by
  obtain ⟨g, hg⟩ := (AlgHom.mem_range _).mp (mem_range_levelEmbedding_of_pow_eq_algebraMap hy)
  have hinj : Function.Injective (levelEmbedding K n) := (levelEmbedding K n).toRingHom.injective
  have hg_pow : g ^ (n : ℕ) = ((φ.expand n n.ne_zero : K⟦X⟧) : K⸨X⸩) :=
    hinj (by rw [map_pow, hg, hy, ← levelEmbedding_expand_self n, expand_coe])
  have hexp₀ : φ.expand n n.ne_zero ≠ 0 := fun h ↦
    hφ₀ (PowerSeries.ext fun k ↦ by
      simpa [PowerSeries.coeff_expand_mul] using congrArg (PowerSeries.coeff (n * k)) h)
  have hg0 : g ≠ 0 := fun h ↦ hexp₀ (ofPowerSeries_injective (Γ := ℤ) (R := K) (by
    rw [← hg_pow, h, zero_pow n.ne_zero, map_zero]))
  have hg_ordTop : (1 : WithTop ℤ) ≤ g.orderTop := by
    have hmul_ord : (g ^ (n : ℕ)).order = (n : ℤ) * g.order := by
      have hexp := TauCeti.LaurentSeries.valuation_eq_exp_neg_order (pow_ne_zero (n : ℕ) hg0)
      rw [map_pow, TauCeti.LaurentSeries.valuation_eq_exp_neg_order hg0, ← exp_nsmul, eq_comm,
        exp_inj, nsmul_eq_mul, mul_neg, neg_inj] at hexp
      exact hexp
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (PowerSeries.order_eq_top.not.mpr hφ₀)
    have hm_pos : 1 ≤ m := by
      have hm_ne : m ≠ 0 := by
        have := PowerSeries.toNat_order_ne_zero hφ hφ₀
        rwa [← hm, ENat.toNat_natCast] at this
      omega
    have hexp_ord : (φ.expand n n.ne_zero).order.toNat = (n : ℕ) * m := by
      rw [PowerSeries.order_expand, ← hm, nsmul_eq_mul, ← Nat.cast_mul, ENat.toNat_natCast]
    have hgn : (n : ℤ) ≤ (g ^ (n : ℕ)).order := by
      rw [hg_pow, PowerSeries.order_coe, hexp_ord, Nat.cast_mul]
      have : 1 ≤ (m : ℤ) := by exact_mod_cast hm_pos
      nlinarith
    rw [← order_eq_orderTop_of_ne_zero hg0, ← WithTop.coe_one, WithTop.coe_le_coe]
    rw [hmul_ord] at hgn
    have : (0 : ℤ) < n := by exact_mod_cast n.pos
    nlinarith
  obtain ⟨ψ, rfl⟩ : g ∈ Set.range (ofPowerSeries ℤ K) :=
    TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff.mpr fun k hk ↦
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr (by omega)).trans_le hg_ordTop)
  have hψ_pow : ψ ^ (n : ℕ) = φ.expand n n.ne_zero :=
    ofPowerSeries_injective (by rwa [PowerSeries.coe_pow])
  have hψ₀ : ψ ≠ 0 := fun h ↦ hg0 (by simp [h])
  have hψ : PowerSeries.constantCoeff ψ = 0 := by
    have h0 : ((ψ : K⸨X⸩)).coeff 0 = 0 :=
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr zero_lt_one).trans_le hg_ordTop)
    simpa [PowerSeries.coeff_coe] using h0
  exact ⟨ψ, hψ, hψ₀, hψ_pow, hg⟩

/-- Any ring endomorphism of `puiseuxField K` that intertwines a ramified level `n` with a
Laurent-series substitution into level `m` is automatically continuous on the entire Puiseux
field. -/
theorem continuous_of_apply_levelEmbedding_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    (n m : ℕ+) {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (levelEmbedding K n f) =
      levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ := by
  rw [continuous_ringHom_iff_continuous_comp_algebraMap]
  have hcomp : (fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f)) =
      fun f ↦ levelEmbedding K m
        (LaurentSeries.substAlgHom hφ hφ₀ (_root_.LaurentSeries.expand K n f)) := by
    funext f
    rw [← levelEmbedding_expand_self n f, hρ]
  rw [hcomp]
  have hexp : Continuous (_root_.LaurentSeries.expand K n) := by
    rw [← LaurentSeries.substAlgHom_X_pow_eq_expand n]
    exact LaurentSeries.continuous_substAlgHom _ _
  exact (continuous_levelEmbedding m).comp
    ((LaurentSeries.continuous_substAlgHom hφ hφ₀).comp hexp)

/-- Any ring endomorphism of `puiseuxField K` extending `LaurentSeries.substAlgHom hφ hφ₀` on
`K⸨X⸩` is automatically continuous on `puiseuxField K`. -/
theorem continuous_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ :=
  continuous_of_apply_levelEmbedding_substAlgHom 1 1 hφ hφ₀ hρ

/-- Any ring automorphism of `puiseuxField K` extending `LaurentSeries.substAlgEquiv φ` on `K⸨X⸩`
is automatically a homeomorphism of `puiseuxField K`. -/
theorem isHomeomorph_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    IsHomeomorph ρ :=
  (isHomeomorph_ringEquiv_iff ρ).mpr
    (continuous_of_apply_algebraMap_substAlgHom (ρ := ρ.toRingHom)
      φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero fun f ↦ by
        rw [← LaurentSeries.coe_substAlgEquiv]
        exact hρ f)

/-- **Automatic level compatibility**: every `K`-algebra endomorphism `ρ` of `puiseuxField K`
extending `LaurentSeries.substAlgHom hφ hφ₀` preserves each ramified level `n` via a Laurent
substitution `ψ` satisfying `ψ ^ n = φ.expand n`. -/
theorem exists_substAlgHom_apply_levelEmbedding {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (n : ℕ+) :
    ∃ (ψ : K⟦X⟧) (hψ : PowerSeries.constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0),
      ψ ^ (n : ℕ) = φ.expand n n.ne_zero ∧
        ∀ f, ρ (levelEmbedding K n f) =
          levelEmbedding K n (LaurentSeries.substAlgHom hψ hψ₀ f) := by
  set y : puiseuxField K := ρ (levelEmbedding K n (HahnSeries.single 1 1))
  have hy_pow : y ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩) := by
    rw [← map_pow, ← map_pow (levelEmbedding K n), HahnSeries.single_pow, one_pow, nsmul_eq_mul,
      mul_one, levelEmbedding_single_self, ← algebraMap_powerSeries_X, algebraMap_powerSeries_apply,
      hρ, PowerSeries.coe_X, LaurentSeries.substAlgHom_single_one]
  obtain ⟨ψ, hψ, hψ₀, hψ_pow, hg⟩ :=
    exists_powerSeries_levelEmbedding_eq_of_pow_eq hφ hφ₀ n hy_pow
  refine ⟨ψ, hψ, hψ₀, hψ_pow, fun f ↦ ?_⟩
  have h_eq := algHom_eq_of_continuous_of_single_one_eq
    (φ₁ := ρ.comp (levelEmbedding K n))
    (φ₂ := (levelEmbedding K n).comp (LaurentSeries.substAlgHom hψ hψ₀))
    ((continuous_of_apply_algebraMap_substAlgHom (ρ := ρ.toRingHom) hφ hφ₀ hρ).comp
      (continuous_levelEmbedding n))
    ((continuous_levelEmbedding n).comp (LaurentSeries.continuous_substAlgHom hψ hψ₀))
    (by simp [y, hg])
  exact AlgHom.congr_fun h_eq f

/-- Bundles any `K`-algebra endomorphism `ρ` of `puiseuxField K` extending
`LaurentSeries.substAlgHom hφ hφ₀` as a continuous `K`-algebra endomorphism. -/
noncomputable def continuousAlgHomOfSubstAlgHom (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    puiseuxField K →A[K] puiseuxField K where
  toAlgHom := ρ
  cont := continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ

/-- Evaluation of `continuousAlgHomOfSubstAlgHom` is the underlying algebra endomorphism. -/
@[simp]
theorem continuousAlgHomOfSubstAlgHom_apply (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    continuousAlgHomOfSubstAlgHom ρ hφ hφ₀ hρ x = ρ x :=
  (rfl)

/-- Forgetting continuity of `continuousAlgHomOfSubstAlgHom` recovers `ρ`. -/
@[simp]
theorem toAlgHom_continuousAlgHomOfSubstAlgHom (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (continuousAlgHomOfSubstAlgHom ρ hφ hφ₀ hρ).toAlgHom = ρ :=
  (rfl)

/-- Under any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀`, the image of `t` has rational order
`φ.order.toNat`. -/
theorem order_single_one_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (ρ (single K 1 1) : HahnSeries ℚ K).order = φ.order.toNat := by
  rw [← algebraMap_powerSeries_X, algebraMap_powerSeries_apply, hρ, PowerSeries.coe_X,
    LaurentSeries.substAlgHom_single_one, coe_algebraMap_laurentSeries, order_ramifiedEmbedding,
    PowerSeries.order_coe, PNat.one_coe, Nat.cast_one, div_one, Int.cast_natCast]

/-- Any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀` multiplies the rational order of every
Puiseux series by `φ.order.toNat`. -/
theorem order_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = φ.order.toNat * (x : HahnSeries ℚ K).order := by
  have hpow := ((continuous_ringHom_iff ρ).mp
    (continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ)).1
  rw [order_map_eq_mul_of_forall_powerSeries ρ hpow x,
    order_single_one_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ, mul_comm]

/-- Any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀` raises the Puiseux valuation to the power
`φ.order.toNat`. -/
theorem valuation_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x ^ φ.order.toNat := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, map_zero, zero_pow (PowerSeries.toNat_order_ne_zero hφ hφ₀)]
  have hρx := coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr hx0)
  rw [valuation_apply, valuation_apply, valuation_eq_exp_neg_order hρx,
    valuation_eq_exp_neg_order (coe_ne_zero hx0), ← exp_nsmul,
    order_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x, nsmul_eq_mul, mul_neg]

/-- Bundles any `K`-algebra automorphism `ρ` of `puiseuxField K` extending
`LaurentSeries.substAlgEquiv φ` as a bicontinuous `K`-algebra automorphism. -/
noncomputable def continuousAlgEquivOfSubstAlgEquiv (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    puiseuxField K ≃A[K] puiseuxField K where
  toAlgEquiv := ρ
  continuous_toFun := continuous_of_apply_algebraMap_substAlgHom
    (ρ := ρ.toRingEquiv.toRingHom) φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero fun f ↦ by
      rw [← LaurentSeries.coe_substAlgEquiv]
      exact hρ f
  continuous_invFun := continuous_symm_of_continuous_ringEquiv (e := ρ.toRingEquiv)
    (continuous_of_apply_algebraMap_substAlgHom (ρ := ρ.toRingEquiv.toRingHom)
      φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero fun f ↦ by
        rw [← LaurentSeries.coe_substAlgEquiv]
        exact hρ f)

/-- Evaluation of `continuousAlgEquivOfSubstAlgEquiv` is the underlying algebra automorphism. -/
@[simp]
theorem continuousAlgEquivOfSubstAlgEquiv_apply (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    continuousAlgEquivOfSubstAlgEquiv ρ φ hρ x = ρ x :=
  (rfl)

/-- Inverse evaluation of `continuousAlgEquivOfSubstAlgEquiv` is `ρ.symm`. -/
@[simp]
theorem continuousAlgEquivOfSubstAlgEquiv_symm_apply (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    (continuousAlgEquivOfSubstAlgEquiv ρ φ hρ).symm x = ρ.symm x :=
  (rfl)

/-- Forgetting bicontinuity of `continuousAlgEquivOfSubstAlgEquiv` recovers `ρ`. -/
@[simp]
theorem toAlgEquiv_continuousAlgEquivOfSubstAlgEquiv (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (continuousAlgEquivOfSubstAlgEquiv ρ φ hρ).toAlgEquiv = ρ :=
  (rfl)

/-- Any lift of a formal-coordinate substitution preserves rational orders on `puiseuxField K`. -/
theorem order_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K →+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = (x : HahnSeries ℚ K).order := by
  have hρ' : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K)
        (LaurentSeries.substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero f) :=
    fun f ↦ by rw [← LaurentSeries.coe_substAlgEquiv]; exact hρ f
  simpa [φ.order_toPowerSeries] using
    order_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
      φ.toPowerSeries_ne_zero hρ' x

/-- Any lift of a formal-coordinate substitution preserves the valuation of `puiseuxField K`. -/
theorem valuation_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K →+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x := by
  have hρ' : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K)
        (LaurentSeries.substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero f) :=
    fun f ↦ by rw [← LaurentSeries.coe_substAlgEquiv]; exact hρ f
  simpa [φ.order_toPowerSeries] using
    valuation_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
      φ.toPowerSeries_ne_zero hρ' x

/-- Any lift of a formal-coordinate substitution preserves the `WithTop ℚ`-valued order
`addVal K`. -/
theorem addVal_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K →+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = addVal K x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hρx := coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr hx0)
  rw [addVal_apply, addVal_apply, ← order_eq_orderTop_of_ne_zero hρx,
    ← order_eq_orderTop_of_ne_zero (coe_ne_zero hx0),
    order_of_apply_algebraMap_substAlgEquiv φ hρ x]

end SubstLift

/-! ### Unit divisibility and existence of continuous substitution and coordinate lifts -/

section Existence

variable {K : Type*} [Field K]

/-- Over a field `K` with `ℕ`-rootable unit group, every Puiseux series has a `d`-th root in
`puiseuxField K`, in arbitrary characteristic. -/
theorem exists_pow_eq [RootableBy Kˣ ℕ] (d : ℕ+) (x : puiseuxField K) :
    ∃ y : puiseuxField K, y ^ (d : ℕ) = x := by
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨g, hg⟩ := exists_pow_eq_expand d f
  exact ⟨levelEmbedding K (n * d) g, by rw [← map_pow, hg, levelEmbedding_expand]⟩

/-- When `Kˣ` is `ℕ`-rootable, the unit group `(puiseuxField K)ˣ` is `ℕ`-rootable. -/
noncomputable instance instRootableByUnitsNat [RootableBy Kˣ ℕ] :
    RootableBy (puiseuxField K)ˣ ℕ :=
  rootableByOfPowLeftSurj _ _ fun {n} hn u ↦ by
    let d : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
    obtain ⟨y, hy⟩ := exists_pow_eq d u.val
    have hy' : y ^ n = u.val := hy
    have hy0 : y ≠ 0 := fun h0 ↦ u.ne_zero (by rw [← hy', h0, zero_pow hn])
    exact ⟨Units.mk0 y hy0, Units.ext hy'⟩

/-- The unit group `(puiseuxField K)ˣ` is `ℕ`-rootable if and only if `Kˣ` is `ℕ`-rootable. -/
theorem nonempty_rootableBy_units_nat_iff :
    Nonempty (RootableBy (puiseuxField K)ˣ ℕ) ↔ Nonempty (RootableBy Kˣ ℕ) := by
  refine ⟨fun ⟨_⟩ ↦ ⟨rootableByOfPowLeftSurj _ _ fun {n} hn u ↦ ?_⟩,
    fun ⟨_⟩ ↦ ⟨inferInstance⟩⟩
  let u' : (puiseuxField K)ˣ := Units.map (algebraMap K (puiseuxField K)).toMonoidHom u
  obtain ⟨y, hy⟩ := RootableBy.surjective_pow (puiseuxField K)ˣ ℕ hn u'
  have hy_val : (y : puiseuxField K) ^ n = algebraMap K (puiseuxField K) u := by
    simpa [u'] using congrArg Units.val hy
  have hy_int : IsIntegral K (y : puiseuxField K) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hy_val ▸ isIntegral_algebraMap)
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hy_int
  have hc0 : c ≠ 0 := fun h0 ↦ y.ne_zero (by rw [← hc, h0, map_zero])
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact (algebraMap K (puiseuxField K)).injective (by rw [map_pow, hc, hy_val])

/-- Every Puiseux series over a field `K` with `[RootableBy Kˣ ℕ]` admits a compatible family of
`n`-th roots indexed by `ℕ+`. -/
theorem exists_pow_compat [RootableBy Kˣ ℕ] (x : puiseuxField K) :
    ∃ y : ℕ+ → puiseuxField K, y 1 = x ∧ ∀ n d : ℕ+, y (n * d) ^ (d : ℕ) = y n := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, rfl, fun _ d ↦ zero_pow d.ne_zero⟩
  let : DivisibleBy (Additive (puiseuxField K)ˣ) ℕ :=
    divisibleByOfSMulRightSurj _ _ fun {n} hn a ↦ by
      obtain ⟨b, hb⟩ := RootableBy.surjective_pow (puiseuxField K)ˣ ℕ hn a.toMul
      exact ⟨Additive.ofMul b, by simpa using congrArg Additive.ofMul hb⟩
  let : DivisibleBy (Additive (puiseuxField K)ˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  let u : (puiseuxField K)ˣ := Units.mk0 x hx
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible (Additive (puiseuxField K)ˣ))
    |>.extension_property_addMonoidHom (Int.castAddHom ℚ) Int.cast_injective
      (zmultiplesHom (Additive (puiseuxField K)ˣ) (Additive.ofMul u))
  refine ⟨fun n ↦ ((Additive.toMul (χ (1 / (n : ℚ))) : (puiseuxField K)ˣ) : puiseuxField K),
    ?_, fun n d ↦ ?_⟩
  · have h1 := DFunLike.congr_fun hχ 1
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, Int.cast_one, zmultiplesHom_apply,
      one_smul] at h1
    simp only [PNat.one_coe, Nat.cast_one, div_one, h1, u]
    rfl
  · have hq : (d : ℕ) • (1 / ((n * d : ℕ+) : ℚ)) = 1 / (n : ℚ) := by
      rw [nsmul_eq_mul, PNat.mul_coe, Nat.cast_mul]
      have : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
      field_simp
    have hmul := congrArg
      (fun z : ℚ ↦ ((Additive.toMul (χ z) : (puiseuxField K)ˣ) : puiseuxField K)) hq
    rwa [map_nsmul, toMul_nsmul, Units.val_pow_eq_pow_val] at hmul

/-- Assembles a compatible family of level-`n` substitution maps into a cocone over
`levelDiagram K`. -/
private noncomputable def substCocone (leg : ℕ+ → (K⸨X⸩ →ₐ[K] puiseuxField K))
    (hleg_compat : ∀ {n m : ℕ+}, n ∣ m →
      (leg m).comp (_root_.LaurentSeries.expand K (m.divExact n)) = leg n) :
    CategoryTheory.Limits.Cocone (levelDiagram K) where
  pt := CommAlgCat.of K (puiseuxField K)
  ι :=
    { app := fun n ↦ CommAlgCat.ofHom (leg n.toPNat)
      naturality := fun {_ _} f ↦ by
        apply CommAlgCat.hom_ext
        dsimp only [levelDiagram, CategoryTheory.Functor.const_obj_obj]
        simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom,
          CategoryTheory.Functor.const_obj_map, CommAlgCat.hom_id, AlgHom.id_comp]
        rw [RamificationIndex.transitionDegree_def]
        exact hleg_compat f.le }

/-- **Existence of continuous substitution endomorphisms**: over a field `K` with
`[RootableBy Kˣ ℕ]` (in arbitrary characteristic), every nonzero power series `φ` with
`constantCoeff φ = 0` lifts to a continuous `K`-algebra endomorphism of `puiseuxField K` extending
`LaurentSeries.substAlgHom`. -/
theorem exists_continuousAlgHom_apply_algebraMap_substAlgHom [RootableBy Kˣ ℕ]
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) :
    ∃ ρ : puiseuxField K →A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
  obtain ⟨y, hy1, hy_pow⟩ := exists_pow_compat (algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩))
  have hy_self : ∀ n : ℕ+, y n ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩) := fun n ↦ by
    simpa [hy1] using hy_pow 1 n
  choose ψ hψ hψ₀ _ hψ_eq using fun n ↦
    exists_powerSeries_levelEmbedding_eq_of_pow_eq hφ hφ₀ n (hy_self n)
  let leg : ℕ+ → (K⸨X⸩ →ₐ[K] puiseuxField K) := fun n ↦
    (levelEmbedding K n).comp (LaurentSeries.substAlgHom (hψ n) (hψ₀ n))
  have hleg_compat : ∀ {n m : ℕ+}, n ∣ m →
      (leg m).comp (_root_.LaurentSeries.expand K (m.divExact n)) = leg n := by
    intro n m h
    have hexp_cont : Continuous (_root_.LaurentSeries.expand K (m.divExact n)) := by
      rw [← LaurentSeries.substAlgHom_X_pow_eq_expand (m.divExact n)]
      exact LaurentSeries.continuous_substAlgHom _ _
    refine algHom_eq_of_continuous_of_single_one_eq
      ((continuous_levelEmbedding m).comp
        ((LaurentSeries.continuous_substAlgHom (hψ m) (hψ₀ m)).comp hexp_cont))
      ((continuous_levelEmbedding n).comp (LaurentSeries.continuous_substAlgHom (hψ n) (hψ₀ n))) ?_
    simp only [leg, AlgHom.comp_apply, expand_single, mul_one,
      LaurentSeries.substAlgHom_single_one]
    rw [RatFunc.single_zpow, zpow_natCast, map_pow, map_pow,
      LaurentSeries.substAlgHom_single_one, hψ_eq m, hψ_eq n]
    have hpow := hy_pow n (m.divExact n)
    rwa [PNat.mul_div_exact h] at hpow
  let s := substCocone leg hleg_compat
  let ρ₀ : puiseuxField K →ₐ[K] puiseuxField K := (levelCoconeIsColimit.desc s).hom
  have hψ1 : ψ 1 = φ :=
    ofPowerSeries_injective ((levelEmbedding K 1).toRingHom.injective ((hψ_eq 1).trans hy1))
  have hρ₀ : ∀ f, ρ₀ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
    intro f
    have hfac : ρ₀ (levelEmbedding K 1 f) = leg 1 f :=
      CategoryTheory.ConcreteCategory.congr_hom (levelCoconeIsColimit.fac s ⟨1⟩) f
    rw [algebraMap_laurentSeries_apply, hfac]
    simp only [leg, AlgHom.comp_apply, algebraMap_laurentSeries_apply]
    have hsubst : LaurentSeries.substAlgHom (hψ 1) (hψ₀ 1) = LaurentSeries.substAlgHom hφ hφ₀ := by
      subst hψ1
      rfl
    rw [hsubst]
  exact ⟨continuousAlgHomOfSubstAlgHom ρ₀ hφ hφ₀ hρ₀, hρ₀⟩

/-- **Existence of bicontinuous coordinate automorphisms**: over a field `K` with
`[RootableBy Kˣ ℕ]` (in arbitrary characteristic), every formal coordinate `φ` lifts to a
bicontinuous `K`-algebra automorphism of `puiseuxField K` extending
`LaurentSeries.substAlgEquiv φ`. -/
theorem exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv [RootableBy Kˣ ℕ]
    (φ : FormalCoordinate K) :
    ∃ ρ : puiseuxField K ≃A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_continuousAlgHom_apply_algebraMap_substAlgHom
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
  have hsurj : Function.Surjective ρ₀ := by
    intro z
    obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding z
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).mp hn
    obtain ⟨ψ, hψ, hψ₀, hψ_pow, hψ_level⟩ := exists_substAlgHom_apply_levelEmbedding
      (ρ := ρ₀.toAlgHom) φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero hρ₀ n
    simp only [ContinuousAlgHom.coe_coe] at hψ_level
    have hψ_ord : ψ.order = 1 := by
      have hmul : (n : ℕ) • ψ.order = (n : ℕ) • (1 : ℕ∞) := by
        rw [← PowerSeries.order_pow, hψ_pow, PowerSeries.order_expand, φ.order_toPowerSeries]
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (PowerSeries.order_eq_top.not.mpr hψ₀)
      rw [← hk, nsmul_eq_mul, nsmul_eq_mul, mul_one, ← Nat.cast_mul, Nat.cast_inj] at hmul
      have hk1 : k = 1 := by
        have := n.pos
        nlinarith
      rw [← hk, hk1, Nat.cast_one]
    let ψc : FormalCoordinate K :=
      ⟨ψ, hψ, ((PowerSeries.order_eq_nat.mp hψ_ord).1).isUnit⟩
    refine ⟨levelEmbedding K n ((LaurentSeries.substAlgEquiv ψc).symm h), ?_⟩
    have hcoe : LaurentSeries.substAlgHom hψ hψ₀ ((LaurentSeries.substAlgEquiv ψc).symm h) =
        LaurentSeries.substAlgEquiv ψc ((LaurentSeries.substAlgEquiv ψc).symm h) :=
      (congrFun (LaurentSeries.coe_substAlgEquiv ψc) _).symm
    rw [hψ_level, hcoe, AlgEquiv.apply_symm_apply]
  let e : puiseuxField K ≃ₐ[K] puiseuxField K :=
    AlgEquiv.ofBijective ρ₀.toAlgHom ⟨ρ₀.toAlgHom.injective, hsurj⟩
  have he : ∀ f, e (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) := fun f ↦ by
    rw [LaurentSeries.coe_substAlgEquiv]
    exact hρ₀ f
  exact ⟨continuousAlgEquivOfSubstAlgEquiv e φ he, he⟩

end Existence

end TauCeti.puiseuxField
