/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Derivation
public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation

/-!
# The derivative of Puiseux series

Over a field `K` of characteristic zero, the derivative `d/dt` of rational-exponent Hahn series,
`d/dt (t ^ q) = q t ^ (q - 1)`, preserves the Puiseux field. This file restricts it to a
`K`-derivation `TauCeti.puiseuxField.derivation K` of `puiseuxField K`.

Differentiation does not change the denominators of exponents, so it preserves every ramified
level `K⸨t ^ (1 / n)⸩`. On that level, written in the variable `u = t ^ (1 / n)` with `t = u ^ n`,
it is the chain rule `d/dt = (1 / n) u ^ (1 - n) d/du`: for a Laurent series `f`,

`d/dt (f (t ^ (1 / n))) = ((1 / n) u ^ (1 - n) f'(u)) (u = t ^ (1 / n))`.

For `n = 1` this says that `d/dt` extends the derivative of `K⸨X⸩`. Since differentiation lowers
the order by at most one, it is continuous for the valuation topology, and in characteristic
zero its kernel consists of the constants.

## Main definitions

* `TauCeti.puiseuxField.derivation K`: the derivative `d/dt` of Puiseux series.

## Main results

* `LaurentSeries.ratHahnSeriesDerivation_ramifiedEmbedding`,
  `TauCeti.puiseuxField.derivation_levelEmbedding`: the chain rule on level `n`.
* `TauCeti.puiseuxField.derivation_algebraMap_laurentSeries`: `d/dt` extends the derivative of
  `K⸨X⸩`.
* `TauCeti.puiseuxField.derivation_mem_range_levelEmbedding`: `d/dt` preserves every level.
* `TauCeti.puiseuxField.continuous_derivation`: `d/dt` is continuous.
* `TauCeti.puiseuxField.derivation_eq_zero_iff`: the kernel of `d/dt` is `K`.
-/

public section

open Filter HahnSeries LaurentSeries Topology
open scoped LaurentSeries

namespace LaurentSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **Chain rule on ramified levels**: under the level-`n` embedding `u ↦ t ^ (1 / n)`, the
derivative `d/dt` of rational-exponent Hahn series is `(1 / n) u ^ (1 - n) d/du`. -/
theorem ratHahnSeriesDerivation_ramifiedEmbedding (n : ℕ+) (f : R⸨X⸩) :
    TauCeti.ratHahnSeriesDerivation R (ramifiedEmbedding R n f) =
      ramifiedEmbedding R n (single (1 - n : ℤ) (algebraMap ℚ R (n : ℚ)⁻¹) * derivative R f) := by
  ext q
  rw [TauCeti.coeff_ratHahnSeriesDerivation]
  by_cases hq : q.den ∣ n
  · obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hq
    have hn : (n : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hk : (k : ℚ) / n + 1 = ((k + n : ℤ) : ℚ) / n := by
      push_cast
      field_simp
    rw [hk, coeff_ramifiedEmbedding_intCast_div, coeff_ramifiedEmbedding_intCast_div,
      coeff_single_mul, coeff_derivative, show k - (1 - n) + 1 = k + n by ring, ← hk,
      Algebra.smul_def, zsmul_eq_mul, ← mul_assoc]
    congr 1
    rw [show (k : ℚ) / n + 1 = (n : ℚ)⁻¹ * ((k + n : ℤ) : ℚ) by field_simp; push_cast; ring,
      map_mul, map_intCast]
  · rw [coeff_ramifiedEmbedding_of_not_den_dvd n _ hq, coeff_ramifiedEmbedding_of_not_den_dvd n,
      smul_zero]
    rwa [← Int.cast_one, Rat.add_intCast_den]

end LaurentSeries

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K]

/-- The derivative of a Puiseux series is a Puiseux series. -/
theorem ratHahnSeriesDerivation_mem_puiseuxField {x : HahnSeries ℚ K} (hx : x ∈ puiseuxField K) :
    ratHahnSeriesDerivation K x ∈ puiseuxField K := by
  obtain ⟨n, hn⟩ := mem_puiseuxField_iff.mp hx
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  rw [ratHahnSeriesDerivation_ramifiedEmbedding]
  exact ramifiedEmbedding_mem_puiseuxField n _

namespace puiseuxField

variable (K) in
/-- The **derivative `d/dt` of Puiseux series**, `d/dt (t ^ q) = q t ^ (q - 1)`: the restriction of
the derivative of rational-exponent Hahn series to the Puiseux field. -/
noncomputable def derivation : Derivation K (puiseuxField K) (puiseuxField K) where
  toFun x := ⟨ratHahnSeriesDerivation K x, ratHahnSeriesDerivation_mem_puiseuxField x.2⟩
  map_add' x y := Subtype.ext ((ratHahnSeriesDerivation K).map_add x y)
  map_smul' r x := Subtype.ext <| by
    -- The scalar action of `K` on the Puiseux field is multiplication by the image of `K`.
    simp only [RingHom.id_apply, Algebra.smul_def, MulMemClass.coe_mul,
      IntermediateField.coe_algebraMap_apply, Derivation.leibniz, Derivation.map_algebraMap,
      Algebra.algebraMap_self, mul_zero, add_zero]
  map_one_eq_zero' := Subtype.ext (ratHahnSeriesDerivation K).map_one_eq_zero
  leibniz' x y := Subtype.ext ((ratHahnSeriesDerivation K).leibniz x y)

/-- As a Hahn series, the derivative of a Puiseux series is its derivative as a rational-exponent
Hahn series. -/
@[simp]
theorem coe_derivation (x : puiseuxField K) :
    (derivation K x : HahnSeries ℚ K) = ratHahnSeriesDerivation K x :=
  (rfl)

/-- **Power rule**: the derivative of `a t ^ q` is `q a t ^ (q - 1)`. -/
@[simp]
theorem derivation_single (q : ℚ) (a : K) :
    derivation K (single K q a) = single K (q - 1) (q • a) :=
  Subtype.ext <| by rw [coe_derivation, coe_single, coe_single, ratHahnSeriesDerivation_single]

/-- **Chain rule on ramified levels**: on level `n`, with `u = t ^ (1 / n)`, the derivative `d/dt`
is `(1 / n) u ^ (1 - n) d/du`. -/
theorem derivation_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    derivation K (levelEmbedding K n f) =
      levelEmbedding K n (HahnSeries.single (1 - n : ℤ) (n : K)⁻¹ * derivative K f) := by
  refine Subtype.ext ?_
  rw [coe_derivation, coe_levelEmbedding, coe_levelEmbedding,
    ratHahnSeriesDerivation_ramifiedEmbedding, eq_ratCast, Rat.cast_inv, Rat.cast_natCast]

/-- The derivative `d/dt` of Puiseux series extends the derivative of `K⸨X⸩`. -/
@[simp]
theorem derivation_algebraMap_laurentSeries (f : K⸨X⸩) :
    derivation K (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (derivative K f) := by
  rw [algebraMap_laurentSeries_apply, algebraMap_laurentSeries_apply, derivation_levelEmbedding]
  simp

/-- The derivative preserves every level `K⸨t ^ (1 / n)⸩`. -/
theorem derivation_mem_range_levelEmbedding {n : ℕ+} {x : puiseuxField K}
    (hx : x ∈ (levelEmbedding K n).range) : derivation K x ∈ (levelEmbedding K n).range := by
  obtain ⟨f, rfl⟩ := hx
  exact ⟨_, (derivation_levelEmbedding n f).symm⟩

/-- **Differentiation lowers the order by at most one**: `ord x ≤ ord (dx/dt) + 1`. -/
theorem addVal_le_addVal_derivation_add_one (x : puiseuxField K) :
    addVal K x ≤ addVal K (derivation K x) + 1 := by
  rw [addVal_apply, addVal_apply, coe_derivation]
  exact orderTop_le_orderTop_ratHahnSeriesDerivation_add_one _

/-- The derivative of Puiseux series is continuous for the valuation topology. -/
theorem continuous_derivation : Continuous (derivation K) := by
  refine continuous_of_continuousAt_zero (derivation K) ?_
  rw [ContinuousAt, map_zero, hasBasis_nhds_zero.tendsto_right_iff]
  intro q _
  filter_upwards [hasBasis_nhds_zero.mem_of_mem (i := q + 1) trivial] with x hx
  have h := hx.trans (addVal_le_addVal_derivation_add_one x)
  rwa [WithTop.coe_add, WithTop.coe_one, WithTop.add_le_add_iff_right WithTop.one_ne_top] at h

/-- **The kernel of `d/dt`**: in characteristic zero, the Puiseux series with derivative zero are
the constants. -/
theorem derivation_eq_zero_iff {x : puiseuxField K} :
    derivation K x = 0 ↔ ∃ a : K, algebraMap K (puiseuxField K) a = x := by
  rw [← Subtype.coe_inj, coe_derivation, ZeroMemClass.coe_zero,
    ratHahnSeriesDerivation_eq_zero_iff]
  simp only [← Subtype.coe_inj, IntermediateField.coe_algebraMap_apply]

end puiseuxField

end TauCeti
