/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Counting
public import TauCeti.NumberTheory.NumberField.Units.Log.Embedding

/-!
# An explicit height gap for nontorsion units

There are at most `unitPowerCountBound d` algebraic integers of degree at most `d` whose
conjugates have modulus at most two. If a unit has relative logarithmic height less than
`log 2 / (unitPowerCountBound d + 1)`, its first `unitPowerCountBound d + 1` powers all
belong to this set. Two powers coincide, so the unit is torsion.

This gives a deliberately coarse, explicit degree-only lower bound for the height of every
nontorsion unit. Unlike a minimum obtained from qualitative Northcott finiteness, the bound
is a finite sum of natural-number expressions and `log 2`. The same gap holds for every
nonzero algebraic integer of infinite multiplicative order.

The counting input is `TauCeti.finite_setOf_isIntegral_house_le`; the proof does not require
a lower bound for Mahler measure such as Dobrowolski's theorem.
-/

public section

open Height NumberField NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

/-- An explicit upper bound on the number of algebraic integers of degree at most `d` with
house at most two. -/
def unitPowerCountBound (d : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d + 1), k * (2 * 4 ^ k + 1) ^ k

/-- The finite-sum formula for the bounded-power count. -/
theorem unitPowerCountBound_def (d : ℕ) :
    unitPowerCountBound d = ∑ k ∈ Finset.range (d + 1), k * (2 * 4 ^ k + 1) ^ k := by rfl

/-- The explicit relative logarithmic height gap obtained by counting bounded powers. -/
noncomputable def unitHeightLowerBound (d : ℕ) : ℝ :=
  Real.log 2 / (unitPowerCountBound d + 1 : ℝ)

/-- The formula for the relative logarithmic unit-height gap. -/
theorem unitHeightLowerBound_def (d : ℕ) :
    unitHeightLowerBound d = Real.log 2 / (unitPowerCountBound d + 1 : ℝ) := by rfl

/-- The explicit unit height bound is strictly positive in every degree. -/
theorem unitHeightLowerBound_pos (d : ℕ) : 0 < unitHeightLowerBound d := by
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

variable {K : Type*} [Field K] [NumberField K]

/-- **Explicit height gap for algebraic integers.** A nonzero algebraic integer of
infinite multiplicative order has relative logarithmic height at least the explicit
bounded-power constant. The nonzero hypothesis is necessary because zero has height zero. -/
theorem unitHeightLowerBound_le_logHeight₁_of_isIntegral {x : K}
    (hx : IsIntegral ℤ x) (hx0 : x ≠ 0) (hxord : ¬IsOfFinOrder x) :
    unitHeightLowerBound (Module.finrank ℚ K) ≤ logHeight₁ x := by
  classical
  set d := Module.finrank ℚ K
  set N := unitPowerCountBound d
  set S := {z : K | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ TauCeti.house z ≤ 2}
  have hcount := TauCeti.finite_setOf_isIntegral_house_le (F := K) d 2
  have hS : S.Finite := hcount.1
  have hcard : S.ncard ≤ N := by
    -- At house bound two the coefficient bound is the natural number four to the k.
    have hfloor (k : ℕ) : ⌊((2 : ℝ) * max 2 1) ^ k⌋₊ = 4 ^ k := by
      have hbase : (2 : ℝ) * max 2 1 = 4 := by norm_num
      have hcast : (4 : ℝ) ^ k = ((4 ^ k : ℕ) : ℝ) := by simp
      rw [hbase, hcast, Nat.floor_natCast]
    simpa only [N, unitPowerCountBound_def, S, hfloor] using hcount.2
  rw [unitHeightLowerBound_def]
  -- The local abbreviations record the degree and its explicit bounded-power count.
  change Real.log 2 / (N + 1 : ℝ) ≤ logHeight₁ x
  by_contra! hsmall
  have hmul : (N + 1 : ℝ) * logHeight₁ x < Real.log 2 :=
    (lt_div_iff₀' (by positivity : (0 : ℝ) < N + 1)).mp hsmall
  have hpowers (i : ℕ) (hi : i < N + 1) : x ^ i ∈ S := by
    refine ⟨hx.pow i, minpoly.natDegree_le _, ?_⟩
    have hheight : logHeight₁ (x ^ i) < Real.log 2 := by
      rw [logHeight₁_pow]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le)
        (zero_le_logHeight₁ _)).trans_lt hmul
    calc TauCeti.house (x ^ i) = NumberField.house (x ^ i) :=
          TauCeti.house_eq_numberField_house _
      _ ≤ Real.exp (logHeight₁ (x ^ i)) := NumberField.house_le_exp_logHeight₁ _
      _ ≤ 2 := by
        simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
          (Real.exp_lt_exp.mpr hheight).le
  have hinj : Function.Injective fun i : ℕ ↦ x ^ i := by
    have hxord' : ¬IsOfFinOrder (Units.mk0 x hx0) := by
      simpa only [← Units.isOfFinOrder_val, Units.val_mk0] using hxord
    intro i j h
    apply (injective_pow_iff_not_isOfFinOrder.mpr hxord')
    apply Units.val_injective
    simpa using h
  have := Set.le_ncard_of_inj_on_range (fun i ↦ x ^ i) hpowers
    (fun _ _ _ _ h ↦ hinj h) hS
  omega

/-- **Explicit unit height gap.** Every nontorsion unit of a degree-`d` number field has
relative logarithmic height at least `log 2 / (unitPowerCountBound d + 1)`. -/
theorem unitHeightLowerBound_le_logHeight₁ {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    unitHeightLowerBound (Module.finrank ℚ K) ≤ logHeight₁ (u : K) := by
  apply unitHeightLowerBound_le_logHeight₁_of_isIntegral
    (RingOfIntegers.isIntegral_coe (u : 𝓞 K)) (NumberField.Units.coe_ne_zero u)
  have hu' : ¬IsOfFinOrder u := by
    simpa only [NumberField.Units.torsion, CommGroup.mem_torsion] using hu
  exact fun h ↦ hu' (((NumberField.Units.coe_injective K).isOfFinOrder_iff
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K)))).mp h)

end TauCeti.NumberField.Units
