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
is a finite sum of natural-number expressions and `log 2`.

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

/-- The explicit relative logarithmic height gap obtained by counting bounded powers. -/
noncomputable def unitHeightLowerBound (d : ℕ) : ℝ :=
  Real.log 2 / (unitPowerCountBound d + 1 : ℝ)

/-- The explicit unit height bound is strictly positive in every degree. -/
theorem unitHeightLowerBound_pos (d : ℕ) : 0 < unitHeightLowerBound d := by
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

variable {K : Type*} [Field K] [NumberField K]

/-- Every conjugate of a unit has modulus at most the exponential of its relative
logarithmic height. -/
theorem house_le_exp_logHeight₁ (u : (𝓞 K)ˣ) :
    TauCeti.house (u : K) ≤ Real.exp (logHeight₁ (u : K)) := by
  rw [TauCeti.house_eq_numberField_house, NumberField.house, canonicalEmbedding]
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun φ ↦ ?_
  let w : InfinitePlace K := InfinitePlace.mk φ
  have h := TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁
    (Sum.inr w) (u : K)
  simp only [TauCeti.GlobalNumberFields.normalizedAbsValue_inr, Real.log_pow, abs_mul,
    Nat.abs_cast] at h
  have hm : (1 : ℝ) ≤ w.mult := by exact_mod_cast InfinitePlace.mult_pos (w := w)
  have hw : Real.log (w u) ≤ logHeight₁ (u : K) :=
    (le_abs_self _).trans ((le_mul_of_one_le_left (abs_nonneg _) hm).trans h)
  change w u ≤ Real.exp (logHeight₁ (u : K))
  rw [← Real.exp_log (NumberField.Units.pos_at_place u w)]
  exact Real.exp_le_exp.mpr hw

/-- **Explicit unit height gap.** Every nontorsion unit of a degree-`d` number field has
relative logarithmic height at least `log 2 / (unitPowerCountBound d + 1)`. -/
theorem unitHeightLowerBound_le_logHeight₁ {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) :
    unitHeightLowerBound (Module.finrank ℚ K) ≤
      logHeight₁ (u : K) := by
  classical
  set d := Module.finrank ℚ K
  set N := unitPowerCountBound d
  set S := {z : K | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ TauCeti.house z ≤ 2}
  have hcount := TauCeti.finite_setOf_isIntegral_house_le (F := K) d 2
  have hS : S.Finite := hcount.1
  have hcard : S.ncard ≤ N := by
    have hfloor (k : ℕ) : ⌊((2 : ℝ) * max 2 1) ^ k⌋₊ = 4 ^ k := by
      norm_num only [show (2 : ℝ) * max 2 1 = 4 by norm_num]
      rw [show (4 : ℝ) ^ k = ((4 ^ k : ℕ) : ℝ) by simp, Nat.floor_natCast]
    simpa only [hfloor, unitPowerCountBound, N, S] using hcount.2
  change Real.log 2 / (N + 1 : ℝ) ≤ logHeight₁ (u : K)
  by_contra! hsmall
  have hmul : (N + 1 : ℝ) * logHeight₁ (u : K) < Real.log 2 :=
    (lt_div_iff₀' (by positivity : (0 : ℝ) < N + 1)).mp hsmall
  have hpowers (i : ℕ) (hi : i < N + 1) : (u : K) ^ i ∈ S := by
    refine ⟨(RingOfIntegers.isIntegral_coe (u : 𝓞 K)).pow i, minpoly.natDegree_le _, ?_⟩
    have hheight : logHeight₁ ((u : K) ^ i) < Real.log 2 := by
      rw [logHeight₁_pow]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le)
        (zero_le_logHeight₁ _)).trans_lt hmul
    calc TauCeti.house ((u : K) ^ i) = TauCeti.house ((u ^ i : (𝓞 K)ˣ) : K) := by simp
      _ ≤ Real.exp (logHeight₁ ((u ^ i : (𝓞 K)ˣ) : K)) := house_le_exp_logHeight₁ _
      _ ≤ 2 := by
        simpa only [Units.val_pow_eq_pow_val, map_pow,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
          (Real.exp_lt_exp.mpr hheight).le
  have hinj : Function.Injective fun i : ℕ ↦ (u : K) ^ i := by
    have hu' : ¬IsOfFinOrder u := by
      simpa only [NumberField.Units.torsion, CommGroup.mem_torsion] using hu
    intro i j h
    apply (injective_pow_iff_not_isOfFinOrder.mpr hu')
    exact NumberField.Units.coe_injective K (by simpa using h)
  have := Set.le_ncard_of_inj_on_range (fun i ↦ (u : K) ^ i) hpowers
    (fun _ _ _ _ h ↦ hinj h) hS
  omega

end TauCeti.NumberField.Units
