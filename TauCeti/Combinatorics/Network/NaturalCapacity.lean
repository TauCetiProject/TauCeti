/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Cast
public import TauCeti.Combinatorics.Network.Coefficients
public import TauCeti.Combinatorics.Network.Nonnegative

/-!
# Natural-capacity flows over ordered rings

Natural capacities can be regarded as integer, rational, or real capacities. This file connects
these views at the level of maximum flows. An integer `NatFlow` maps to any linearly ordered
additive commutative group with one in which the integer cast is faithful,
preserving every arrow value and the flow value under the integer cast. The mapped flow is maximum
exactly when the integer flow is maximum.

Consequently, natural capacities cast into the rationals or the reals admit a maximum flow whose
arrow values are natural numbers. More precisely, that flow is the coefficientwise cast of a
maximum integer `NatFlow`.

## Main results

* `TauCeti.NatFlow.cast`: cast an integer `NatFlow` to an ordered coefficient group.
* `TauCeti.NatFlow.isMaximum_cast_iff`: casting preserves and reflects maximality.
* `TauCeti.NatFlow.exists_isMaximum_cast`: a maximum flow for cast natural capacities comes from
  a maximum integer `NatFlow`.
* `TauCeti.NatFlow.exists_isMaximum_rat` and `TauCeti.NatFlow.exists_isMaximum_real`: the rational
  and real specializations.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {R : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)]

namespace NatFlow

section Cast

variable [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
variable {cap : Assignment Q ℕ} {s t : V}

/-- The canonical order-preserving additive map from the integers to the coefficient group. -/
private def intCastOrderAddMonoidHom : ℤ →+o R :=
  OrderAddMonoidHom.mk (Int.castAddHom R) Int.cast_mono

/-- Evaluation of the order-preserving additive integer cast. -/
@[simp]
private theorem intCastOrderAddMonoidHom_apply (z : ℤ) :
    intCastOrderAddMonoidHom (R := R) z = (z : R) :=
  rfl

omit [Fintype V] [∀ x y, Fintype (Q x y)] in
private theorem map_natCast_intCast :
    (cap.map (Nat.cast : ℕ → ℤ)).map (intCastOrderAddMonoidHom (R := R)) =
      cap.map (Nat.cast : ℕ → R) := by
  funext x y e
  simp

/-- Cast an integer flow with natural capacities to the coefficient group. The capacities are the
direct natural-number casts, rather than a nested natural-to-integer-to-group expression. -/
def cast (f : NatFlow cap s t) : Flow (cap.map (Nat.cast : ℕ → R)) s t :=
  Flow.congr (map_natCast_intCast (R := R)) rfl rfl
    (f.map (intCastOrderAddMonoidHom (R := R)))

/-- Casting a natural-capacity flow casts its integer assignment coefficientwise. -/
@[simp]
theorem cast_toFun (f : NatFlow cap s t) :
    (f.cast (R := R)).toFun = f.toFun.map (Int.cast : ℤ → R) := by
  funext x y e
  rw [cast, Flow.toBoundedFlow_congr, BoundedFlow.congr_apply_toFun, Flow.map_toFun]
  simp

/-- Casting a natural-capacity flow casts each integer arrow value. -/
@[simp]
theorem cast_apply (f : NatFlow cap s t) {x y : V} (e : Q x y) :
    (f.cast (R := R)).toFun e = (f.toFun e : R) := by
  rw [cast_toFun]
  rfl

/-- The cast flow has the natural arrow values recovered from the integer flow. -/
theorem cast_toFun_eq_natAssignment (f : NatFlow cap s t) :
    (f.cast (R := R)).toFun = f.natAssignment.map (Nat.cast : ℕ → R) := by
  funext x y e
  rw [cast_apply, Assignment.map_apply, ← f.coe_natAssignment e]
  exact Int.cast_natCast (f.natAssignment e)

/-- Casting a natural-capacity flow casts its value. -/
@[simp]
theorem val_cast (f : NatFlow cap s t) : (f.cast (R := R)).val = (f.val : R) := by
  rw [cast, Flow.toBoundedFlow_congr, BoundedFlow.val_congr]
  simpa only [intCastOrderAddMonoidHom_apply] using
    Flow.val_map (intCastOrderAddMonoidHom (R := R)) f

end Cast

section Maximum

variable [AddCommGroupWithOne R] [LinearOrder R] [IsOrderedAddMonoid R]
  [ZeroLEOneClass R] [NeZero (1 : R)]
variable {cap : Assignment Q ℕ} {s t : V}

/-- A natural-capacity flow is maximum exactly when its coefficient cast is maximum. -/
theorem isMaximum_cast_iff (f : NatFlow cap s t) :
    (f.cast (R := R)).IsMaximum ↔ f.IsMaximum := by
  rcases eq_or_ne s t with rfl | hst
  · constructor <;> intro _ <;> rw [Flow.isMaximum_iff] <;> intro g
    · rw [g.val_eq_zero_of_eq rfl, f.val_eq_zero_of_eq rfl]
    · rw [g.val_eq_zero_of_eq rfl, (f.cast (R := R)).val_eq_zero_of_eq rfl]
  · rw [cast, Flow.isMaximum_congr_iff,
      Flow.isMaximum_map_iff hst (by
        intro a b hab
        simpa only [intCastOrderAddMonoidHom_apply] using
          Int.cast_strictMono (R := R) hab)]

/-- Natural capacities cast to the coefficient group admit a maximum flow obtained by casting a
maximum integer `NatFlow`. Its arrow values are therefore natural numbers. -/
theorem exists_isMaximum_cast (cap : Assignment Q ℕ) (s t : V) :
    ∃ f : NatFlow cap s t, f.IsMaximum ∧ (f.cast (R := R)).IsMaximum := by
  obtain ⟨f, hf⟩ := Flow.exists_isMaximum (cap := cap.map (Nat.cast : ℕ → ℤ))
    (fun _ _ e ↦ Int.natCast_nonneg (cap e))
  exact ⟨f, hf, (isMaximum_cast_iff (R := R) f).2 hf⟩

end Maximum

/-- Natural capacities cast into the rationals admit a maximum flow that is the cast of a maximum
integer `NatFlow`. -/
theorem exists_isMaximum_rat (cap : Assignment Q ℕ) (s t : V) :
    ∃ f : NatFlow cap s t, f.IsMaximum ∧ (f.cast (R := ℚ)).IsMaximum :=
  exists_isMaximum_cast (R := ℚ) cap s t

/-- Natural capacities cast into the reals admit a maximum flow that is the cast of a maximum
integer `NatFlow`. -/
theorem exists_isMaximum_real (cap : Assignment Q ℕ) (s t : V) :
    ∃ f : NatFlow cap s t, f.IsMaximum ∧ (f.cast (R := ℝ)).IsMaximum :=
  exists_isMaximum_cast (R := ℝ) cap s t

end NatFlow

end TauCeti
