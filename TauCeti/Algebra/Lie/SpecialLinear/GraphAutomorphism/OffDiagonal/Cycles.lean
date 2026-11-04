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

## Main definitions

* `TauCeti.TypeAOffDiagonalCycle`: the representatives, the positions with index sum at most the
  rank, with `TauCeti.typeAOffDiagonalCyclePredLength` one less than the cycle length.
* `TauCeti.typeAOffDiagonalCycleEquiv`: the enumeration of all off-diagonal positions by cycle
  and position in the cycle. Its inverse is computed by
  `TauCeti.typeAOffDiagonalCycleEquiv_symm_apply_of_le` and
  `TauCeti.typeAOffDiagonalCycleEquiv_symm_apply_of_gt`.
* `TauCeti.typeAOffDiagonalCycleSign`: the integral arrow signs along a cycle.

## Main results

* `TauCeti.typeAOffDiagonalCycleEquiv_finRotate`: the cyclic successor in a cycle is the reversed
  exchange `TauCeti.finDistinctPairsRevSwap`.
* `TauCeti.prod_typeAOffDiagonalCycleSign`, `TauCeti.prod_typeAOffDiagonalCycleSign_eq_one_iff`
  and `TauCeti.prod_typeAOffDiagonalCycleSign_eq_neg_one_iff`: the sign product of a cycle is `1`
  on two-element cycles and `(-1) ^ (r + 1)` on singletons, so it is `-1` exactly on antidiagonal
  singletons in even rank.
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
theorem typeAOffDiagonalCyclePredLength_def (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCyclePredLength r c =
      if c.val.val.1.val + c.val.val.2.val < r then 1 else 0 :=
  (rfl)

/-- A representative with index sum strictly less than the rank has a two-element cycle. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_of_lt (c : TypeAOffDiagonalCycle r)
    (h : c.val.val.1.val + c.val.val.2.val < r) :
    typeAOffDiagonalCyclePredLength r c = 1 := by
  rw [typeAOffDiagonalCyclePredLength_def, ite_eq_left h]

/-- An antidiagonal representative has a singleton cycle. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_of_eq (c : TypeAOffDiagonalCycle r)
    (h : c.val.val.1.val + c.val.val.2.val = r) :
    typeAOffDiagonalCyclePredLength r c = 0 := by
  rw [typeAOffDiagonalCyclePredLength_def, h, ite_eq_right (lt_irrefl r)]

/-- Predecessor length one characterizes representatives with index sum below the rank. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_eq_one_iff (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCyclePredLength r c = 1 ↔ c.val.val.1.val + c.val.val.2.val < r := by
  by_cases h : c.val.val.1.val + c.val.val.2.val < r <;>
    simp [typeAOffDiagonalCyclePredLength_def, h]

/-- Predecessor length zero characterizes antidiagonal representatives. -/
@[simp]
theorem typeAOffDiagonalCyclePredLength_eq_zero_iff (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCyclePredLength r c = 0 ↔ c.val.val.1.val + c.val.val.2.val = r := by
  by_cases h : c.val.val.1.val + c.val.val.2.val < r
  · simp [typeAOffDiagonalCyclePredLength_of_lt r c h, ne_of_lt h]
  · have he : c.val.val.1.val + c.val.val.2.val = r :=
      le_antisymm c.property (Nat.le_of_not_gt h)
    simp [he]

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
  have hn := typeAOffDiagonalCyclePredLength_def r c
  split_ifs at hn <;> omega

private def offDiagonalCyclePoint (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} :=
  if i = 0 then c.val else finDistinctPairsRevSwap (r + 1) c.val

private theorem offDiagonalCyclePoint_zero (c : TypeAOffDiagonalCycle r) :
    offDiagonalCyclePoint r c 0 = c.val := by
  rw [offDiagonalCyclePoint, ite_eq_left rfl]

private theorem last_ne_zero_of_lt (c : TypeAOffDiagonalCycle r)
    (h : c.val.val.1.val + c.val.val.2.val < r) :
    Fin.last (typeAOffDiagonalCyclePredLength r c) ≠ 0 :=
  mt Fin.last_eq_zero_iff.1
    (by rw [typeAOffDiagonalCyclePredLength_of_lt r c h]; exact one_ne_zero)

private theorem offDiagonalCyclePoint_last (c : TypeAOffDiagonalCycle r)
    (h : c.val.val.1.val + c.val.val.2.val < r) :
    offDiagonalCyclePoint r c (Fin.last _) = finDistinctPairsRevSwap (r + 1) c.val := by
  rw [offDiagonalCyclePoint, ite_eq_right (last_ne_zero_of_lt r c h)]

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
      have hs := finDistinctPairsRevSwap_val_fst_add_val_snd d.val
      have he : c.val = finDistinctPairsRevSwap (r + 1) d.val := by
        simpa only [offDiagonalCyclePoint, hi0, ite_true, ite_eq_right hj0] using h
      rw [← he] at hs
      have hc := c.property
      omega
  · by_cases hj0 : j = 0
    · have hc := cycle_lt_of_ne_zero r c i hi0
      have hs := finDistinctPairsRevSwap_val_fst_add_val_snd c.val
      have he : finDistinctPairsRevSwap (r + 1) c.val = d.val := by
        simpa only [offDiagonalCyclePoint, hj0, ite_true, ite_eq_right hi0] using h
      rw [he] at hs
      have hd := d.property
      omega
    · have hcd : c = d := Subtype.ext ((finDistinctPairsRevSwap (r + 1)).injective (by
        simpa only [offDiagonalCyclePoint, ite_eq_right hi0, ite_eq_right hj0] using h))
      subst d
      have hij : i = j := Fin.ext (by
        have hi' : i.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hi0
        have hj' : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj0
        omega)
      subst j
      rfl

private def offDiagonalCycleIndex (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    Σ c, Fin (typeAOffDiagonalCyclePredLength r c + 1) :=
  if h : p.val.1.val + p.val.2.val ≤ r then ⟨⟨p, h⟩, 0⟩
  else
    ⟨⟨finDistinctPairsRevSwap (r + 1) p,
      (finDistinctPairsRevSwap_val_fst_add_val_snd_lt p (not_le.mp h)).le⟩, Fin.last _⟩

private theorem offDiagonalCyclePoint_offDiagonalCycleIndex :
    Function.LeftInverse (fun x : Σ c, Fin (typeAOffDiagonalCyclePredLength r c + 1) ↦
      offDiagonalCyclePoint r x.1 x.2) (offDiagonalCycleIndex r) := by
  intro p
  by_cases hp : p.val.1.val + p.val.2.val ≤ r
  · rw [offDiagonalCycleIndex, dite_eq_left hp]
    exact offDiagonalCyclePoint_zero r ⟨p, hp⟩
  · have hlt : (finDistinctPairsRevSwap (r + 1) p).val.1.val +
        (finDistinctPairsRevSwap (r + 1) p).val.2.val < r :=
      finDistinctPairsRevSwap_val_fst_add_val_snd_lt p (not_le.mp hp)
    rw [offDiagonalCycleIndex, dite_eq_right hp]
    exact (offDiagonalCyclePoint_last r ⟨finDistinctPairsRevSwap (r + 1) p, hlt.le⟩ hlt).trans
      (finDistinctPairsRevSwap_finDistinctPairsRevSwap p)

/-- A concrete enumeration of all off-diagonal positions by their one- or two-cycles. A position
with index sum at most the rank is the representative of its own cycle, at position zero;
otherwise it is the reflected transpose of its representative, at the last position. -/
def typeAOffDiagonalCycleEquiv :
    (Σ c, Fin (typeAOffDiagonalCyclePredLength r c + 1)) ≃
      {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} where
  toFun x := offDiagonalCyclePoint r x.1 x.2
  invFun := offDiagonalCycleIndex r
  left_inv := (offDiagonalCyclePoint_offDiagonalCycleIndex r).rightInverse_of_injective
    (offDiagonalCyclePoint_injective r)
  right_inv := offDiagonalCyclePoint_offDiagonalCycleIndex r

/-- Position zero is the chosen representative and position one is its reflected transpose. -/
theorem typeAOffDiagonalCycleEquiv_apply (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleEquiv r ⟨c, i⟩ =
      if i = 0 then c.val else finDistinctPairsRevSwap (r + 1) c.val :=
  (rfl)

/-- Position zero of every cycle is its chosen representative. -/
@[simp]
theorem typeAOffDiagonalCycleEquiv_zero (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCycleEquiv r ⟨c, 0⟩ = c.val := by
  rw [typeAOffDiagonalCycleEquiv_apply, ite_eq_left rfl]

/-- The last position of every cycle is the reflected transpose of its representative. -/
@[simp]
theorem typeAOffDiagonalCycleEquiv_last (c : TypeAOffDiagonalCycle r) :
    typeAOffDiagonalCycleEquiv r ⟨c, Fin.last _⟩ = finDistinctPairsRevSwap (r + 1) c.val := by
  by_cases h : c.val.val.1.val + c.val.val.2.val < r
  · rw [typeAOffDiagonalCycleEquiv_apply, ite_eq_right (last_ne_zero_of_lt r c h)]
  · have hs : c.val.val.1.val + c.val.val.2.val = r :=
      le_antisymm c.property (not_lt.mp h)
    have hlast : (Fin.last (typeAOffDiagonalCyclePredLength r c) :
        Fin (typeAOffDiagonalCyclePredLength r c + 1)) = 0 := by
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_zero, typeAOffDiagonalCyclePredLength_of_eq r c hs]
    rw [hlast, typeAOffDiagonalCycleEquiv_zero]
    exact ((finDistinctPairsRevSwap_eq_self_iff c.val).mpr (by rw [hs])).symm

/-- A position with index sum at most the rank is the representative of its own cycle, at
position zero. -/
theorem typeAOffDiagonalCycleEquiv_symm_apply_of_le
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) (h : p.val.1.val + p.val.2.val ≤ r) :
    (typeAOffDiagonalCycleEquiv r).symm p = ⟨⟨p, h⟩, 0⟩ :=
  (Equiv.symm_apply_eq _).mpr (typeAOffDiagonalCycleEquiv_zero r ⟨p, h⟩).symm

/-- A position with index sum beyond the rank is the reflected transpose of its cycle
representative, at the last position of a two-element cycle. -/
theorem typeAOffDiagonalCycleEquiv_symm_apply_of_gt
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) (h : r < p.val.1.val + p.val.2.val) :
    (typeAOffDiagonalCycleEquiv r).symm p =
      ⟨⟨finDistinctPairsRevSwap (r + 1) p,
        (finDistinctPairsRevSwap_val_fst_add_val_snd_lt p h).le⟩, Fin.last _⟩ := by
  have hlt : (finDistinctPairsRevSwap (r + 1) p).val.1.val +
      (finDistinctPairsRevSwap (r + 1) p).val.2.val < r :=
    finDistinctPairsRevSwap_val_fst_add_val_snd_lt p h
  exact (Equiv.symm_apply_eq _).mpr
    ((typeAOffDiagonalCycleEquiv_last r ⟨finDistinctPairsRevSwap (r + 1) p, hlt.le⟩).trans
      (finDistinctPairsRevSwap_finDistinctPairsRevSwap p)).symm

/-- Cyclic successor in the explicit family is the native reverse-transpose permutation. -/
theorem typeAOffDiagonalCycleEquiv_finRotate (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleEquiv r ⟨c, finRotate _ i⟩ =
      finDistinctPairsRevSwap (r + 1) (typeAOffDiagonalCycleEquiv r ⟨c, i⟩) := by
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
        ite_eq_left hrot, ite_eq_right hi, finDistinctPairsRevSwap_finDistinctPairsRevSwap]
  · have hn := (typeAOffDiagonalCyclePredLength_eq_zero_iff r c).mpr
      (le_antisymm c.property (Nat.le_of_not_gt hc))
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    have hrot : finRotate (typeAOffDiagonalCyclePredLength r c + 1) i = 0 :=
      Fin.ext (by have := (finRotate _ i).isLt; omega)
    have hfix : finDistinctPairsRevSwap (r + 1) c.val = c.val :=
      (finDistinctPairsRevSwap_eq_self_iff c.val).mpr (by have := c.property; omega)
    rw [typeAOffDiagonalCycleEquiv_apply, typeAOffDiagonalCycleEquiv_apply,
      ite_eq_left hrot, ite_eq_left hi, hfix]

/-- Integral arrow signs on the explicitly enumerated off-diagonal cycles. -/
def typeAOffDiagonalCycleSign (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) : ℤ :=
  typeAOffDiagonalSign r (typeAOffDiagonalCycleEquiv r ⟨c, i⟩)

/-- The arrow sign of a cycle position is the sign of the corresponding off-diagonal position. -/
theorem typeAOffDiagonalCycleSign_def (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleSign r c i =
      typeAOffDiagonalSign r (typeAOffDiagonalCycleEquiv r ⟨c, i⟩) :=
  (rfl)

/-- The two arrows in a nontrivial cycle have the same integral sign. -/
theorem typeAOffDiagonalCycleSign_eq (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleSign r c i = typeAOffDiagonalSign r c.val := by
  rw [typeAOffDiagonalCycleSign, typeAOffDiagonalCycleEquiv_apply]
  split_ifs
  · rfl
  · exact typeAOffDiagonalSign_finDistinctPairsRevSwap r c.val

/-- Every arrow weight is an integral sign before any scalar extension. -/
theorem typeAOffDiagonalCycleSign_eq_one_or_neg_one (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    typeAOffDiagonalCycleSign r c i = 1 ∨ typeAOffDiagonalCycleSign r c i = -1 := by
  rw [typeAOffDiagonalCycleSign_eq, typeAOffDiagonalSign_def]
  exact neg_one_pow_eq_or ℤ _

/-- Two-cycles have positive monodromy; singletons have the rank-dependent sign. -/
theorem prod_typeAOffDiagonalCycleSign (c : TypeAOffDiagonalCycle r) :
    (∏ i, typeAOffDiagonalCycleSign r c i) =
      if c.val.val.1.val + c.val.val.2.val < r then 1 else (-1 : ℤ) ^ (r + 1) := by
  simp only [typeAOffDiagonalCycleSign_eq, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  by_cases hc : c.val.val.1.val + c.val.val.2.val < r
  · simp [hc, pow_two, typeAOffDiagonalSign_def, ← mul_pow]
  · have hs : c.val.val.1.val + c.val.val.2.val = r := by
      have := c.property
      omega
    simp only [typeAOffDiagonalCyclePredLength_of_eq r c hs, ite_eq_right hc, zero_add,
      pow_one]
    exact typeAOffDiagonalSign_of_fixed r c.val
      ((finDistinctPairsRevSwap_eq_self_iff c.val).mpr (by rw [hs]))

/-- The sign product is positive exactly on two-element cycles and, in odd rank, on every
cycle. -/
theorem prod_typeAOffDiagonalCycleSign_eq_one_iff (c : TypeAOffDiagonalCycle r) :
    (∏ i, typeAOffDiagonalCycleSign r c i) = 1 ↔
      c.val.val.1.val + c.val.val.2.val < r ∨ Odd r := by
  rw [prod_typeAOffDiagonalCycleSign]
  by_cases hc : c.val.val.1.val + c.val.val.2.val < r
  · rw [ite_eq_left hc]
    exact iff_of_true rfl (Or.inl hc)
  · rw [ite_eq_right hc, or_iff_right hc]
    rw [neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1),
      Nat.even_add_one, Nat.not_even_iff_odd]

/-- The sign product is negative exactly on antidiagonal singletons in even rank. -/
theorem prod_typeAOffDiagonalCycleSign_eq_neg_one_iff (c : TypeAOffDiagonalCycle r) :
    (∏ i, typeAOffDiagonalCycleSign r c i) = -1 ↔
      c.val.val.1.val + c.val.val.2.val = r ∧ Even r := by
  rw [prod_typeAOffDiagonalCycleSign]
  by_cases hc : c.val.val.1.val + c.val.val.2.val < r
  · rw [ite_eq_left hc]
    exact iff_of_false (by decide) fun h ↦ hc.ne h.1
  · have hs : c.val.val.1.val + c.val.val.2.val = r := le_antisymm c.property (not_lt.mp hc)
    rw [ite_eq_right hc, hs, and_iff_right rfl]
    rw [neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤ) ≠ 1),
      Nat.odd_add_one, Nat.not_odd_iff_even]

end TauCeti
