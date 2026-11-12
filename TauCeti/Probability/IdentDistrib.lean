/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib

/-!
# Identical distributions of natural-valued differences

Equal laws of natural-valued differences transfer to integer-valued differences under
almost-sure order bounds. This allows increment laws of nondecreasing count processes
to be compared after casting to the integers.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

/-- Equal laws of differences of natural-valued random variables remain equal after casting
to the integers, provided the subtrahends are a.e. at most the minuends.
The sample spaces may differ. -/
theorem IdentDistrib.natCast_sub_of_le {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {a b : Ω → ℕ} {a' b' : Ω' → ℕ}
    (h : IdentDistrib (fun ω ↦ b ω - a ω) (fun ω ↦ b' ω - a' ω) P Q)
    (hab : ∀ᵐ ω ∂P, a ω ≤ b ω) (hab' : ∀ᵐ ω ∂Q, a' ω ≤ b' ω) :
    IdentDistrib (fun ω ↦ (b ω : ℤ) - a ω)
      (fun ω ↦ (b' ω : ℤ) - a' ω) P Q := by
  have hcast := h.comp (measurable_of_countable (fun n : ℕ ↦ (n : ℤ)))
  have hx : (fun ω ↦ ((b ω - a ω : ℕ) : ℤ)) =ᵐ[P]
      (fun ω ↦ (b ω : ℤ) - a ω) := by
    filter_upwards [hab] with ω hω using Int.ofNat_sub hω
  have hy : (fun ω ↦ ((b' ω - a' ω : ℕ) : ℤ)) =ᵐ[Q]
      (fun ω ↦ (b' ω : ℤ) - a' ω) := by
    filter_upwards [hab'] with ω hω using Int.ofNat_sub hω
  exact (IdentDistrib.of_ae_eq hcast.aemeasurable_fst hx).symm.trans
    (hcast.trans (IdentDistrib.of_ae_eq hcast.aemeasurable_snd hy))

end ProbabilityTheory
