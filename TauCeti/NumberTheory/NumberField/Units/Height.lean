/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.NumberTheory.Height.FiniteOrder

import TauCeti.NumberTheory.Height.House

/-!
# Height zero and torsion units

A unit of a number field has multiplicative height one, equivalently logarithmic height zero,
exactly when it belongs to the torsion subgroup. Both relative and absolute heights detect
this subgroup, which is also the kernel of the logarithmic embedding. Consequently every
unit in a fundamental system has strictly positive logarithmic height. Conversely, the height of
a unit `ζ ∏ j, u j ^ e j` with `ζ` torsion is bounded by its exponents `e j` and the houses of the
`u j`.

For a nonzero algebraic integer, height one likewise characterizes finite multiplicative
order and implies that the integer is a unit.
-/

public section

open Height NumberField
open scoped NumberField

namespace NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- A unit has relative multiplicative height one exactly when it is torsion. -/
@[simp]
theorem mulHeight₁_eq_one_iff (u : (𝓞 K)ˣ) :
    mulHeight₁ (u : K) = 1 ↔ u ∈ torsion K := by
  rw [Height.mulHeight₁_eq_one_iff, or_iff_right (coe_ne_zero u), torsion,
    CommGroup.mem_torsion]
  exact (coe_injective K).isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (_root_.Units.coeHom (𝓞 K)))

/-- A unit has relative logarithmic height zero exactly when it is torsion. -/
@[simp]
theorem logHeight₁_eq_zero_iff (u : (𝓞 K)ˣ) :
    logHeight₁ (u : K) = 0 ↔ u ∈ torsion K := by
  rw [Height.logHeight₁_eq_zero_iff, or_iff_right (coe_ne_zero u), torsion,
    CommGroup.mem_torsion]
  exact (coe_injective K).isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (_root_.Units.coeHom (𝓞 K)))

/-- A unit has absolute multiplicative height one exactly when it is torsion. -/
@[simp]
theorem absMulHeight₁_eq_one_iff (u : (𝓞 K)ˣ) :
    absMulHeight₁ (u : K) = 1 ↔ u ∈ torsion K := by
  rw [NumberField.absMulHeight₁_eq_one_iff (Algebra.IsIntegral.isIntegral (u : K)),
    or_iff_right (coe_ne_zero u), torsion, CommGroup.mem_torsion]
  exact (coe_injective K).isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (_root_.Units.coeHom (𝓞 K)))

/-- A unit has absolute logarithmic height zero exactly when it is torsion. -/
@[simp]
theorem absLogHeight₁_eq_zero_iff (u : (𝓞 K)ˣ) :
    absLogHeight₁ (u : K) = 0 ↔ u ∈ torsion K := by
  rw [NumberField.absLogHeight₁_eq_zero_iff (Algebra.IsIntegral.isIntegral (u : K)),
    or_iff_right (coe_ne_zero u), torsion, CommGroup.mem_torsion]
  exact (coe_injective K).isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (_root_.Units.coeHom (𝓞 K)))

open dirichletUnitTheorem in
/-- The relative logarithmic height vanishes exactly on the kernel of the logarithmic
embedding. -/
theorem logHeight₁_eq_zero_iff_logEmbedding_eq_zero (u : (𝓞 K)ˣ) :
    logHeight₁ (u : K) = 0 ↔ logEmbedding K (Additive.ofMul u) = 0 := by
  rw [logHeight₁_eq_zero_iff, logEmbedding_eq_zero_iff]

/-- A nontorsion unit has relative multiplicative height strictly greater than one. -/
theorem one_lt_mulHeight₁ {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    1 < mulHeight₁ (u : K) := by
  exact lt_of_le_of_ne (Height.one_le_mulHeight₁ _) fun h ↦
    hu ((mulHeight₁_eq_one_iff u).mp h.symm)

/-- A nontorsion unit has strictly positive relative logarithmic height. -/
theorem logHeight₁_pos {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    0 < logHeight₁ (u : K) :=
  Real.log_pos (one_lt_mulHeight₁ hu)

/-- A nontorsion unit has absolute multiplicative height strictly greater than one. -/
theorem one_lt_absMulHeight₁ {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    1 < absMulHeight₁ (u : K) :=
  lt_of_le_of_ne (NumberField.one_le_absMulHeight₁ _) fun h ↦
    hu ((absMulHeight₁_eq_one_iff u).mp h.symm)

/-- A nontorsion unit has strictly positive absolute logarithmic height. -/
theorem absLogHeight₁_pos {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    0 < absLogHeight₁ (u : K) :=
  Real.log_pos (one_lt_absMulHeight₁ hu)

/-- A unit `ζ ∏ j, u j ^ e j` with `ζ` a root of unity and every `|e j| ≤ B` has relative height
at most `[K : ℚ] * B * ∑ j, log (house (u j))`. -/
theorem logHeight₁_mul_prod_zpow_le {ι : Type*} [Fintype ι] {u : ι → (𝓞 K)ˣ} {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ torsion K) {e : ι → ℤ} {B : ℝ} (he : ∀ j, |(e j : ℝ)| ≤ B) :
    logHeight₁ ((ζ * ∏ j, u j ^ e j : (𝓞 K)ˣ) : K) ≤
      Module.finrank ℚ K * (B * ∑ j, Real.log (house (u j : K))) := by
  have hcoe : ((ζ * ∏ j, u j ^ e j : (𝓞 K)ˣ) : K) = (ζ : K) * ∏ j, (u j : K) ^ e j := by
    rw [coe_mul]
    congr 1
    simp only [← coe_zpow]
    exact map_prod ((_root_.Units.coeHom K).comp (_root_.Units.map
      (algebraMap (𝓞 K) K).toMonoidHom)) _ _
  -- Each `u j` is an algebraic integer of house at least `1`.
  have hu (j : ι) :
      logHeight₁ (u j : K) ≤ Module.finrank ℚ K * Real.log (house (u j : K)) := by
    have h := logHeight₁_le_finrank_mul_posLog_house (u j : 𝓞 K).isIntegral_coe
    rwa [Real.posLog_eq_log (by
      rw [abs_of_nonneg (house_nonneg _)]
      exact one_le_house_of_isIntegral (RingOfIntegers.isIntegral_coe _) (coe_ne_zero (u j)))] at h
  calc logHeight₁ ((ζ * ∏ j, u j ^ e j : (𝓞 K)ˣ) : K)
      ≤ logHeight₁ (ζ : K) + ∑ j, logHeight₁ ((u j : K) ^ e j) := by
        rw [hcoe]
        exact (logHeight₁_mul_le _ _).trans (add_le_add le_rfl (logHeight₁_prod_le _ _))
    _ = ∑ j, |(e j : ℝ)| * logHeight₁ (u j : K) := by
        rw [(logHeight₁_eq_zero_iff ζ).mpr hζ, zero_add]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [logHeight₁_zpow, Nat.cast_natAbs, Int.cast_abs]
    _ ≤ ∑ j, B * (Module.finrank ℚ K * Real.log (house (u j : K))) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul (he j) (hu j) (zero_le_logHeight₁ _)
          ((abs_nonneg _).trans (he j))
    _ = Module.finrank ℚ K * (B * ∑ j, Real.log (house (u j : K))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

end NumberField.Units

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero algebraic integer has relative multiplicative height one exactly when it has
finite multiplicative order. -/
theorem mulHeight₁_eq_one_iff {x : 𝓞 K} (hx : x ≠ 0) :
    mulHeight₁ (x : K) = 1 ↔ IsOfFinOrder x := by
  rw [Height.mulHeight₁_eq_one_iff,
    or_iff_right (by exact_mod_cast hx : (x : K) ≠ 0)]
  exact RingOfIntegers.coe_injective.isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom)

/-- A nonzero algebraic integer has absolute multiplicative height one exactly when it has
finite multiplicative order. -/
theorem absMulHeight₁_eq_one_iff {x : 𝓞 K} (hx : x ≠ 0) :
    absMulHeight₁ (x : K) = 1 ↔ IsOfFinOrder x := by
  rw [NumberField.absMulHeight₁_eq_one_iff (Algebra.IsIntegral.isIntegral (x : K)),
    or_iff_right (by exact_mod_cast hx : (x : K) ≠ 0)]
  exact RingOfIntegers.coe_injective.isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom)

/-- A nonzero algebraic integer of absolute multiplicative height one is a unit. -/
theorem isUnit_of_absMulHeight₁_eq_one {x : 𝓞 K} (hx : x ≠ 0)
    (hheight : absMulHeight₁ (x : K) = 1) : IsUnit x :=
  ((absMulHeight₁_eq_one_iff hx).mp hheight).isUnit

end NumberField.RingOfIntegers
