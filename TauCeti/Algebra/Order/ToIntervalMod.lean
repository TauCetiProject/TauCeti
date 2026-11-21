/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.GroupTheory.QuotientGroup.ModEq

/-!
# Periodic functions on fundamental intervals

Two `c`-periodic functions on an Archimedean linearly ordered additive group that agree on one
interval `[a, a + c)` are equal (`Function.Periodic.eq_of_eqOn_Ico`): every point reduces modulo
`c` to a point of `[a, a + c)`, where both functions take the value they take at the point.

A `c`-periodic function on an Archimedean linearly ordered additive group that is injective on
`[0, c)` is injective on every half-open interval `[s, s + c)` of length `c`
(`Function.Periodic.injOn_Ico`): two points of `[s, s + c)` with the same value reduce modulo `c`
to the same point of `[0, c)`, hence to the same point of `[s, s + c)`. Such a function descends to
an injective function on the quotient `α ⧸ zmultiples c` (`Function.Periodic.lift_injective`).
-/

public section

namespace Function

variable {α β : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Archimedean α]
  {f : α → β} {c : α}

/-- A `c`-periodic function that is injective on `[0, c)` is injective on every interval
`[s, s + c)`. -/
theorem Periodic.injOn_Ico (hf : Periodic f c) (hc : 0 < c) (h : Set.InjOn f (Set.Ico 0 c))
    (s : α) : Set.InjOn f (Set.Ico s (s + c)) := by
  have hred : ∀ t, f (toIcoMod hc 0 t) = f t := fun t ↦ by
    rw [toIcoMod, hf.sub_zsmul_eq]
  intro t₁ ht₁ t₂ ht₂ heq
  have h₀ : toIcoMod hc 0 t₁ = toIcoMod hc 0 t₂ :=
    h (toIcoMod_mem_Ico' hc t₁) (toIcoMod_mem_Ico' hc t₂) (by rw [hred, hred, heq])
  have hs : toIcoMod hc s t₁ = toIcoMod hc s t₂ :=
    (toIcoMod_eq_toIcoMod hc).2 ((toIcoMod_eq_toIcoMod hc).1 h₀)
  rwa [(toIcoMod_eq_self hc).2 ht₁, (toIcoMod_eq_self hc).2 ht₂] at hs

/-- Two `c`-periodic functions that agree on an interval `[a, a + c)` are equal. -/
theorem Periodic.eq_of_eqOn_Ico {g : α → β} (hf : Periodic f c) (hg : Periodic g c) (hc : 0 < c)
    (a : α) (h : Set.EqOn f g (Set.Ico a (a + c))) : f = g :=
  funext fun t ↦ calc
    f t = f (toIcoMod hc a t) := by rw [toIcoMod, hf.sub_zsmul_eq]
    _ = g (toIcoMod hc a t) := h (toIcoMod_mem_Ico hc a t)
    _ = g t := by rw [toIcoMod, hg.sub_zsmul_eq]

/-- A `c`-periodic function that is injective on `[0, c)` descends to an injective function on
`α ⧸ zmultiples c`: it takes equal values exactly at points that agree modulo `c`. -/
theorem Periodic.lift_injective (hf : Periodic f c) (hc : 0 < c) (h : Set.InjOn f (Set.Ico 0 c)) :
    Injective hf.lift := by
  intro x y hxy
  induction x using QuotientAddGroup.induction_on with | H s => ?_
  induction y using QuotientAddGroup.induction_on with | H t => ?_
  have hs : s ∈ Set.Ico s (s + c) := Set.left_mem_Ico.2 (lt_add_of_pos_right s hc)
  have hst : toIcoMod hc s t = toIcoMod hc s s := by
    rw [(toIcoMod_eq_self hc).2 hs]
    exact hf.injOn_Ico hc h s (toIcoMod_mem_Ico hc s t) hs
      (by rw [toIcoMod, hf.sub_zsmul_eq]; exact hxy.symm)
  exact (AddCommGroup.modEq_iff_eq_mod_zmultiples.1 ((toIcoMod_inj hc).1 hst)).symm

end Function
