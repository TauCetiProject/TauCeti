/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.UnitInterval

/-!
# The unit interval wound once around the additive circle

For a real period `p`, the continuous map `AddCircle.ofUnitInterval p : C(I, AddCircle p)` sends
`t` to the class of `t * p`. For `0 < p` it winds the unit interval once around the circle: it is
surjective, and it identifies exactly the two endpoints `0` and `1`, both of which go to `0`. It
is therefore the quotient map through which loops on the unit interval are read as maps out of
the circle, and maps out of the circle as loops.

## Main definitions

* `AddCircle.ofUnitInterval p`: the map `t ↦ t * p` from the unit interval to `AddCircle p`.

## Main results

* `AddCircle.ofUnitInterval_zero`, `AddCircle.ofUnitInterval_one`: both endpoints go to `0`.
* `AddCircle.surjective_ofUnitInterval`: for `0 < p` the map is surjective.
* `AddCircle.ofUnitInterval_eq_ofUnitInterval_iff`: for `0 < p` two points have the same image
  exactly when they are equal or are the two endpoints.
-/

public section

noncomputable section

open Set
open scoped unitInterval

namespace AddCircle

variable {p : ℝ}

/-- The map `t ↦ t * p` from the unit interval to `AddCircle p`. For `0 < p` it is onto and
winds once around the circle. -/
def ofUnitInterval (p : ℝ) : C(I, AddCircle p) :=
  ⟨fun t => ((t * p : ℝ) : AddCircle p), by fun_prop⟩

@[simp]
theorem ofUnitInterval_apply (t : I) : ofUnitInterval p t = ((t * p : ℝ) : AddCircle p) :=
  (rfl)

theorem ofUnitInterval_zero : ofUnitInterval p 0 = 0 := by
  simp [ofUnitInterval_apply]

theorem ofUnitInterval_one : ofUnitInterval p 1 = 0 := by
  simp [ofUnitInterval_apply]

/-- For a positive period, every point of the circle is the image of a point of the unit
interval. -/
theorem surjective_ofUnitInterval [hp : Fact (0 < p)] :
    Function.Surjective (ofUnitInterval p) := by
  intro θ
  obtain ⟨⟨x, hx₀, hx₁⟩, hx⟩ : ∃ x : Ico (0 : ℝ) (0 + p), (x : AddCircle p) = θ :=
    ⟨equivIco p 0 θ, coe_equivIco⟩
  rw [zero_add] at hx₁
  refine ⟨⟨x / p, div_nonneg hx₀ hp.out.le, (div_le_one hp.out).2 hx₁.le⟩, ?_⟩
  rw [ofUnitInterval_apply, ← hx, div_mul_cancel₀ x hp.out.ne']

/-- For a positive period, two points of the unit interval have the same image in the circle
exactly when they are equal or are the two endpoints. -/
theorem ofUnitInterval_eq_ofUnitInterval_iff [hp : Fact (0 < p)] {s t : I} :
    ofUnitInterval p s = ofUnitInterval p t ↔ s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [ofUnitInterval_apply, ofUnitInterval_apply] at h
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h)
    rw [zsmul_eq_mul, ← sub_eq_neg_add, ← sub_mul] at hk
    have hk' : (k : ℝ) = t - s := mul_right_cancel₀ hp.out.ne' hk
    obtain ⟨hs₀, hs₁⟩ := s.2
    obtain ⟨ht₀, ht₁⟩ := t.2
    -- `k = t - s` lies in `[-1, 1]`, so it is one of `-1`, `0`, `1`
    have hk_lo : (-1 : ℝ) ≤ k := by linarith
    have hk_hi : (k : ℝ) ≤ 1 := by linarith
    obtain rfl | rfl | rfl : k = -1 ∨ k = 0 ∨ k = 1 := by
      have : -1 ≤ k := by exact_mod_cast hk_lo
      have : k ≤ 1 := by exact_mod_cast hk_hi
      omega
    · refine Or.inr (Or.inr ⟨Subtype.ext ?_, Subtype.ext ?_⟩) <;>
        · push_cast at hk'
          simp only [Icc.coe_one, Icc.coe_zero]
          linarith
    · exact Or.inl (Subtype.ext (by push_cast at hk'; linarith))
    · refine Or.inr (Or.inl ⟨Subtype.ext ?_, Subtype.ext ?_⟩) <;>
        · push_cast at hk'
          simp only [Icc.coe_one, Icc.coe_zero]
          linarith
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp only [ofUnitInterval_zero, ofUnitInterval_one]

end AddCircle
