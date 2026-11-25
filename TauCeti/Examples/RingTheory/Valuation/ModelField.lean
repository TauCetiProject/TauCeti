/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import Mathlib.RingTheory.Valuation.ValuativeRel.Trivial
public import TauCeti.NumberTheory.LocalField.ModelField
public import TauCeti.NumberTheory.LocalField.Unramified.ModelField

/-!
# Tests for model fields

* `ℚ_[p]` is a model field, through the instance for nonarchimedean local fields, so its
  valuation ring `𝒪[ℚ_[p]]` is a discrete valuation ring.
* A field whose valuative relation is the trivial one (compatible with the trivial valuation `1`)
  is not a model field.
* The completion `Breve ℚ_[p]` of the maximal unramified extension of `ℚ_[p]` is a model field.
* A valuation whose value group is `ℤ × ℤ`, ordered lexicographically, is discrete (`(0, -1)` is
  the largest value below one) but does not have rank at most one (every power of `(0, 1)` lies
  below `(1, 0)`), so it is not a model field.
-/

public section

open ValuativeRel

namespace TauCeti.Examples.ModelField

/-- `ℚ_[p]` is a model field. -/
example (p : ℕ) [Fact p.Prime] : ModelField ℚ_[p] := inferInstance

/-- The valuation ring of `ℚ_[p]` is a discrete valuation ring, through `ModelField`. -/
example (p : ℕ) [Fact p.Prime] : IsDiscreteValuationRing 𝒪[ℚ_[p]] :=
  ModelField.isDiscreteValuationRing ℚ_[p]

/-- A trivially valued field is not a model field. -/
example (K Γ : Type*) [Field K] [DecidableEq K] [ValuativeRel K] [LinearOrderedCommGroupWithZero Γ]
    [Valuation.Compatible (1 : Valuation K Γ)] : ¬ ModelField K :=
  ModelField.not_of_not_isNontrivial K (not_isNontrivial_of_trivialRel (R := K) (Γ := Γ))

/-- The completion of the maximal unramified extension of `ℚ_[p]` is a model field. -/
example (p : ℕ) [Fact p.Prime] : ModelField (MaxUnramifiedCompletion.Breve ℚ_[p]) := inferInstance

/-- A valuation with value group `ℤ × ℤ`, ordered lexicographically, is discrete but does not have
rank at most one. -/
example (K : Type*) [Field K] [ValuativeRel K]
    (e : ValueGroupWithZero K ≃*o WithZero (Multiplicative (ℤ ×ₗ ℤ))) :
    IsDiscrete K ∧ ¬ IsRankLeOne K := by
  let v : ℤ → ℤ → ValueGroupWithZero K := fun a b ↦
    e.symm ((Multiplicative.ofAdd (toLex (a, b)) : Multiplicative (ℤ ×ₗ ℤ)) : WithZero _)
  have hv_lt (a b c d : ℤ) : v a b < v c d ↔ a < c ∨ a = c ∧ b < d := by
    simp only [v]
    rw [map_lt_map_iff, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt, Prod.Lex.toLex_lt_toLex]
  have hv_one : (1 : ValueGroupWithZero K) = v 0 0 := by
    simp only [v]
    rw [← map_one e.symm]
    rfl
  have hv_pow (b : ℤ) (n : ℕ) : v 0 b ^ n = v 0 (n * b) := by
    simp only [v]
    rw [← map_pow, ← WithZero.coe_pow, ← ofAdd_nsmul]
    congr
  refine ⟨⟨⟨v 0 (-1), by rw [hv_one, hv_lt]; omega, fun δ hδ ↦ ?_⟩⟩, ?_⟩
  · rcases eq_or_ne δ 0 with rfl | hδ0
    · exact zero_le
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp ((map_ne_zero e).mpr hδ0)
    have hδm : δ = v (ofLex m.toAdd).1 (ofLex m.toAdd).2 := by
      simp only [v, toLex_ofLex, Prod.mk.eta, ofAdd_toAdd, hm]
      exact (e.symm_apply_apply δ).symm
    rw [hδm, hv_one, hv_lt] at hδ
    rw [hδm]
    refine le_of_not_gt fun h ↦ ?_
    rw [hv_lt] at h
    omega
  · rintro ⟨⟨f, hf⟩⟩
    have h1 : 1 < f (v 0 1) := by
      rw [← map_one f, hv_one]
      exact hf ((hv_lt _ _ _ _).mpr (Or.inr ⟨rfl, one_pos⟩))
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (f (v 1 0)) h1
    rw [← map_pow, hv_pow] at hn
    exact (hf ((hv_lt _ _ _ _).mpr (Or.inl one_pos))).not_gt hn

end TauCeti.Examples.ModelField
