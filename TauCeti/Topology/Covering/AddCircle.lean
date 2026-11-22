/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import TauCeti.Algebra.AddCircle

/-!
# The double cover of the circle

The doubling map `x ↦ 2 • x` of the circle `ℝ ⧸ ℤ` (`TauCeti.addCircleDoubleCover`) is a covering
map (`TauCeti.isCoveringMap_addCircleDoubleCover`). Its fibre over `0` has the two points `0` and
`1 / 2` (`TauCeti.addCircleDoubleCover_eq_zero_iff`, `TauCeti.natCard_fiber_addCircleDoubleCover`),
and the generator `t ↦ t` of the fundamental group of the circle exchanges them under monodromy
(`TauCeti.coe_monodromyPerm_addCircleDoubleCover_zero`,
`TauCeti.coe_monodromyPerm_addCircleDoubleCover_half`): its lifts from `0` and from `1 / 2` are the
paths `t ↦ t / 2` and `t ↦ (1 + t) / 2`.

## Main definitions

* `TauCeti.addCircleDoubleCover`: the double cover of the circle.

## Main results

* `TauCeti.isCoveringMap_addCircleDoubleCover`: the doubling map is a covering map.
* `TauCeti.natCard_fiber_addCircleDoubleCover`: its fibre over `0` has two points.
* `TauCeti.coe_monodromyPerm_addCircleDoubleCover_zero`,
  `TauCeti.coe_monodromyPerm_addCircleDoubleCover_half`: the generator of the fundamental group
  exchanges the two points of the fibre.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the monodromy action
  on the fibre of a covering).
-/

public section

noncomputable section

namespace TauCeti

/-- The **double cover of the circle** `x ↦ 2 • x` of `ℝ ⧸ ℤ`. -/
def addCircleDoubleCover : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)) :=
  ⟨fun x ↦ 2 • x, continuous_id.nsmul 2⟩

@[simp]
theorem addCircleDoubleCover_apply (x : AddCircle (1 : ℝ)) : addCircleDoubleCover x = 2 • x :=
  (rfl)

/-- The doubling map of the circle is a covering map. -/
theorem isCoveringMap_addCircleDoubleCover : IsCoveringMap addCircleDoubleCover :=
  (AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 2).isCoveringMap

/-- **The fibre of the double cover over `0` has the two points `0` and `1 / 2`.** -/
theorem addCircleDoubleCover_eq_zero_iff (x : AddCircle (1 : ℝ)) :
    addCircleDoubleCover x = ((0 : ℝ) : AddCircle (1 : ℝ)) ↔
      x = ((0 : ℝ) : AddCircle (1 : ℝ)) ∨ x = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [addCircleDoubleCover_apply, AddCircle.coe_zero]
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa using AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℝ) two_ne_zero
      (by rwa [ofNat_zsmul])
  · rintro (rfl | rfl)
    · simp
    · rw [← AddCircle.coe_nsmul]
      norm_num [AddCircle.coe_period]

/-- **The fibre of the double cover over `0` has two points**: it is the `2`-torsion of the
circle (`AddCircle.natCard_torsionBy`). -/
theorem natCard_fiber_addCircleDoubleCover :
    Nat.card {x // addCircleDoubleCover x = ((0 : ℝ) : AddCircle (1 : ℝ))} = 2 := by
  rw [← AddCircle.natCard_torsionBy (1 : ℝ) (n := 2)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
  rw [addCircleDoubleCover_apply, AddCircle.coe_zero, AddSubgroup.torsionBy.nsmul_iff]

/-- `0` lies in the fibre of the double cover over `0`. -/
theorem addCircleDoubleCover_zero :
    addCircleDoubleCover ((0 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  (addCircleDoubleCover_eq_zero_iff _).2 (Or.inl rfl)

/-- `1 / 2` lies in the fibre of the double cover over `0`. -/
theorem addCircleDoubleCover_half :
    addCircleDoubleCover ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  (addCircleDoubleCover_eq_zero_iff _).2 (Or.inr rfl)

/-- **The generator of the fundamental group moves `0` to `1 / 2`**: the loop `t ↦ t` of the circle
lifts along the double cover from `0` to the path `t ↦ t / 2`. -/
theorem coe_monodromyPerm_addCircleDoubleCover_zero :
    (isCoveringMap_addCircleDoubleCover.monodromyPerm _
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1)))
        ⟨_, addCircleDoubleCover_zero⟩ : AddCircle (1 : ℝ)) =
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [IsCoveringMap.coe_monodromyPerm]
  refine isCoveringMap_addCircleDoubleCover.monodromy_eq_apply_one
    (Γ := ⟨fun t ↦ ((t / 2 : ℝ) : AddCircle (1 : ℝ)), by fun_prop⟩) ?_ ?_
  · funext t
    have h : (2 • ((t : ℝ) / 2) : ℝ) = t := by rw [nsmul_eq_mul]; push_cast; ring
    rw [Function.comp_apply, addCircleDoubleCover_apply, ContinuousMap.coe_mk,
      ← AddCircle.coe_nsmul, h, AddCircle.zsmulLoop_apply]
    simp
  · simp

/-- **The generator of the fundamental group moves `1 / 2` back to `0`**: the loop `t ↦ t` of the
circle lifts along the double cover from `1 / 2` to the path `t ↦ (1 + t) / 2`. -/
theorem coe_monodromyPerm_addCircleDoubleCover_half :
    (isCoveringMap_addCircleDoubleCover.monodromyPerm _
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1)))
        ⟨_, addCircleDoubleCover_half⟩ : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [IsCoveringMap.coe_monodromyPerm]
  refine (isCoveringMap_addCircleDoubleCover.monodromy_eq_apply_one
    (Γ := ⟨fun t ↦ (((1 + t) / 2 : ℝ) : AddCircle (1 : ℝ)), by fun_prop⟩) ?_ ?_).trans ?_
  · funext t
    have h : (2 • ((1 + (t : ℝ)) / 2) : ℝ) = t + 1 := by rw [nsmul_eq_mul]; push_cast; ring
    rw [Function.comp_apply, addCircleDoubleCover_apply, ContinuousMap.coe_mk,
      ← AddCircle.coe_nsmul, h, AddCircle.coe_add_period, AddCircle.zsmulLoop_apply]
    simp
  · simp
  · norm_num [AddCircle.coe_period]

end TauCeti
