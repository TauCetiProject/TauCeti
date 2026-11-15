/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Injectivity of periodic functions on fundamental intervals

A `c`-periodic function on an Archimedean linearly ordered additive group that is injective on
`[0, c)` is injective on every half-open interval `[s, s + c)` of length `c`
(`Function.Periodic.injOn_Ico`): two points of `[s, s + c)` with the same value reduce modulo `c`
to the same point of `[0, c)`, hence to the same point of `[s, s + c)`.
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

end Function
