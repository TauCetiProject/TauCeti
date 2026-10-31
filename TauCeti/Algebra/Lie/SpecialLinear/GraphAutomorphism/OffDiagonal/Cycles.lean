/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.OffDiagonal.Basic

/-!
# Explicit off-diagonal cycles of the type-A graph automorphism

An off-diagonal position is a cycle representative when its index sum is at most
the rank. Equality gives a singleton; strict inequality gives a two-element cycle.
This supplies the concrete finite family needed for signed fixed-module coordinates.
-/

public section

namespace TauCeti

variable (r : ℕ)

/-- Representatives of reverse-transpose orbits whose index sum is at most the rank. -/
abbrev TypeAOffDiagonalCycle :=
  {p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} //
    p.val.1.val + p.val.2.val ≤ r}

/-- One less than the cycle length, as required by the signed-cycle family API. -/
def typeAOffDiagonalCyclePredLength (c : TypeAOffDiagonalCycle r) : ℕ :=
  if c.val.val.1.val + c.val.val.2.val < r then 1 else 0

/-- The predecessor length distinguishes strict representatives from antidiagonal singletons. -/
theorem typeAOffDiagonalCyclePredLength_eq (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCyclePredLength r c =
      if c.val.val.1.val + c.val.val.2.val < r then 1 else 0 :=
  (rfl)

/-- A representative with index sum strictly less than the rank has a two-element cycle. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_of_lt (c : TypeAOffDiagonalCycle r)
    (h : c.val.val.1.val + c.val.val.2.val < r) :
    typeAOffDiagonalCyclePredLength r c = 1 := by
  rw [typeAOffDiagonalCyclePredLength_eq, ite_eq_left h]

/-- An antidiagonal representative has a singleton cycle. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_of_eq (c : TypeAOffDiagonalCycle r)
    (h : c.val.val.1.val + c.val.val.2.val = r) :
    typeAOffDiagonalCyclePredLength r c = 0 := by
  rw [typeAOffDiagonalCyclePredLength_eq, h, ite_eq_right (lt_irrefl r)]

/-- Predecessor length one characterizes representatives with index sum below the rank. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_eq_one_iff (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCyclePredLength r c = 1 ↔ c.val.val.1.val + c.val.val.2.val < r := by
  by_cases h : c.val.val.1.val + c.val.val.2.val < r <;>
    simp [typeAOffDiagonalCyclePredLength_eq, h]

/-- Predecessor length zero characterizes antidiagonal representatives. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_eq_zero_iff (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCyclePredLength r c = 0 ↔ c.val.val.1.val + c.val.val.2.val = r := by
  by_cases h : c.val.val.1.val + c.val.val.2.val < r
  · simp [typeAOffDiagonalCyclePredLength_of_lt r c h, ne_of_lt h]
  · have he : c.val.val.1.val + c.val.val.2.val = r :=
      le_antisymm c.property (Nat.le_of_not_gt h)
    simp [he]

private theorem offDiagonalPerm_sum
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    (typeAOffDiagonalPerm r p).val.1.val + (typeAOffDiagonalPerm r p).val.2.val +
      (p.val.1.val + p.val.2.val) = 2 * r := by
  simp only [typeAOffDiagonalPerm_apply_val, Fin.val_rev]
  have hi := p.val.1.isLt
  have hj := p.val.2.isLt
  omega

private theorem cycle_lt_of_ne_zero (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) (hi : i ≠ 0) :
    c.val.val.1.val + c.val.val.2.val < r := by
  by_contra h
  have hn := (typeAOffDiagonalCyclePredLength_eq_zero_iff r c).mpr
    (le_antisymm c.property (Nat.le_of_not_gt h))
  have hil := i.isLt
  exact hi (Fin.ext (by omega))

private theorem cycle_index_lt_two (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) : i.val < 2 := by
  have hi := i.isLt
  have hn := typeAOffDiagonalCyclePredLength_eq r c
  split_ifs at hn <;> omega

private def offDiagonalCyclePoint (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} :=
  if i = 0 then c.val else typeAOffDiagonalPerm r c.val

private theorem offDiagonalCyclePoint_injective :
    Function.Injective (fun x : Σ c, Fin (typeAOffDiagonalCyclePredLength r c + 1) ↦
      offDiagonalCyclePoint r x.1 x.2) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  have hi := cycle_index_lt_two r c i
  have hj := cycle_index_lt_two r d j
  by_cases hi0 : i = 0
  · by_cases hj0 : j = 0
    · have hcd : c = d := Subtype.ext (by
        simpa only [offDiagonalCyclePoint, hi0, hj0, ite_true] using h)
      subst d
      simp only [hi0, hj0]
    · have hd := cycle_lt_of_ne_zero r d j hj0
      have hs := offDiagonalPerm_sum r d.val
      have he : c.val = typeAOffDiagonalPerm r d.val := by
        simpa only [offDiagonalCyclePoint, hi0, ite_true, ite_eq_right hj0] using h
      rw [← he] at hs
      have hc := c.property
      omega
  · by_cases hj0 : j = 0
    · have hc := cycle_lt_of_ne_zero r c i hi0
      have hs := offDiagonalPerm_sum r c.val
      have he : typeAOffDiagonalPerm r c.val = d.val := by
        simpa only [offDiagonalCyclePoint, hj0, ite_true, ite_eq_right hi0] using h
      rw [he] at hs
      have hd := d.property
      omega
    · have hcd : c = d := Subtype.ext ((typeAOffDiagonalPerm r).injective (by
        simpa only [offDiagonalCyclePoint, ite_eq_right hi0, ite_eq_right hj0] using h))
      subst d
      have hij : i = j := Fin.ext (by
        have hi' : i.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hi0
        have hj' : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj0
        omega)
      subst j
      rfl

private theorem offDiagonalCyclePoint_surjective :
    Function.Surjective (fun x : Σ c, Fin (typeAOffDiagonalCyclePredLength r c + 1) ↦
      offDiagonalCyclePoint r x.1 x.2) := by
  intro p
  by_cases hp : p.val.1.val + p.val.2.val ≤ r
  · exact ⟨⟨⟨p, hp⟩, 0⟩, by simp [offDiagonalCyclePoint]⟩
  · have hs := offDiagonalPerm_sum r p
    have hlt : (typeAOffDiagonalPerm r p).val.1.val +
        (typeAOffDiagonalPerm r p).val.2.val < r := by omega
    let c : TypeAOffDiagonalCycle r := ⟨typeAOffDiagonalPerm r p, hlt.le⟩
    have hc : typeAOffDiagonalCyclePredLength r c = 1 :=
      (typeAOffDiagonalCyclePredLength_eq_one_iff r c).mpr hlt
    refine ⟨⟨c, ⟨1, by omega⟩⟩, ?_⟩
    simp [offDiagonalCyclePoint, c]

/-- A concrete enumeration of all off-diagonal positions by their one- or two-cycles. -/
noncomputable def typeAOffDiagonalCycleEquiv :
    (Σ c, Fin (typeAOffDiagonalCyclePredLength r c + 1)) ≃
      {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} :=
  Equiv.ofBijective (fun x ↦ offDiagonalCyclePoint r x.1 x.2)
    ⟨offDiagonalCyclePoint_injective r, offDiagonalCyclePoint_surjective r⟩

/-- Position zero is the chosen representative and position one is its reflected transpose. -/
theorem typeAOffDiagonalCycleEquiv_apply (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleEquiv r ⟨c, i⟩ =
      if i = 0 then c.val else typeAOffDiagonalPerm r c.val :=
  (rfl)

/-- Cyclic successor in the explicit family is the native reverse-transpose permutation. -/
theorem typeAOffDiagonalCycleEquiv_rotate (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleEquiv r ⟨c, finRotate _ i⟩ =
      typeAOffDiagonalPerm r (typeAOffDiagonalCycleEquiv r ⟨c, i⟩) := by
  by_cases hc : c.val.val.1.val + c.val.val.2.val < r
  · have hn := (typeAOffDiagonalCyclePredLength_eq_one_iff r c).mpr hc
    by_cases hi : i = 0
    · have hrot : finRotate (typeAOffDiagonalCyclePredLength r c + 1) i ≠ 0 := by
        rw [hi, finRotate_apply_zero]
        simp [Fin.ext_iff, hn]
      rw [typeAOffDiagonalCycleEquiv_apply, typeAOffDiagonalCycleEquiv_apply,
        ite_eq_right hrot, ite_eq_left hi]
    · have hilast : i = Fin.last (typeAOffDiagonalCyclePredLength r c) := by
        apply Fin.ext
        have hil := cycle_index_lt_two r c i
        have hi0 : i.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hi
        simp only [Fin.val_last]
        omega
      have hrot : finRotate (typeAOffDiagonalCyclePredLength r c + 1) i = 0 := by
        rw [hilast, finRotate_last]
      rw [typeAOffDiagonalCycleEquiv_apply, typeAOffDiagonalCycleEquiv_apply,
        ite_eq_left hrot, ite_eq_right hi, typeAOffDiagonalPerm_apply_apply]
  · have hn := (typeAOffDiagonalCyclePredLength_eq_zero_iff r c).mpr
      (le_antisymm c.property (Nat.le_of_not_gt hc))
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    have hrot : finRotate (typeAOffDiagonalCyclePredLength r c + 1) i = 0 :=
      Fin.ext (by have := (finRotate _ i).isLt; omega)
    have hfix : typeAOffDiagonalPerm r c.val = c.val :=
      (typeAOffDiagonalPerm_eq_self_iff r c.val).mpr (by have := c.property; omega)
    rw [typeAOffDiagonalCycleEquiv_apply, typeAOffDiagonalCycleEquiv_apply,
      ite_eq_left hrot, ite_eq_left hi, hfix]

/-- Integral arrow signs on the explicitly enumerated off-diagonal cycles. -/
noncomputable def typeAOffDiagonalCycleSign (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) : ℤ :=
  typeAOffDiagonalSign r (typeAOffDiagonalCycleEquiv r ⟨c, i⟩)

/-- The two arrows in a nontrivial cycle have the same integral sign. -/
theorem typeAOffDiagonalCycleSign_eq (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleSign r c i = typeAOffDiagonalSign r c.val := by
  rw [typeAOffDiagonalCycleSign, typeAOffDiagonalCycleEquiv_apply]
  split_ifs
  · rfl
  · exact typeAOffDiagonalSign_perm r c.val

/-- Every arrow weight is an integral sign before any scalar extension. -/
theorem typeAOffDiagonalCycleSign_eq_one_or_neg_one (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleSign r c i = 1 ∨ typeAOffDiagonalCycleSign r c i = -1 := by
  rw [typeAOffDiagonalCycleSign_eq]
  exact mul_self_eq_one_iff.mp (typeAOffDiagonalSign_mul_self r c.val)

/-- Two-cycles have positive monodromy; singletons have the rank-dependent sign. -/
theorem prod_typeAOffDiagonalCycleSign (c : TypeAOffDiagonalCycle r) :
    (∏ i, typeAOffDiagonalCycleSign r c i) =
      if c.val.val.1.val + c.val.val.2.val < r then 1 else (-1 : ℤ) ^ (r + 1) := by
  simp only [typeAOffDiagonalCycleSign_eq, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  by_cases hc : c.val.val.1.val + c.val.val.2.val < r
  · simp [hc, pow_two]
  · have hs : c.val.val.1.val + c.val.val.2.val = r := by
      have := c.property
      omega
    simp only [typeAOffDiagonalCyclePredLength_of_eq r c hs, ite_eq_right hc, zero_add,
      pow_one]
    exact typeAOffDiagonalSign_of_fixed r c.val
      ((typeAOffDiagonalPerm_eq_self_iff r c.val).mpr hs)

end TauCeti
