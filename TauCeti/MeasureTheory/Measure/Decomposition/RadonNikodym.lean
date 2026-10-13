/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The Radon–Nikodym derivative off a set carrying the measure

If `μ` is concentrated on a set `s`, that is `x ∈ s` for `μ`-almost every `x`, then the
Radon–Nikodym derivative `μ.rnDeriv ν` vanishes `ν`-almost everywhere off `s`. This is the
contrapositive form of `Mathlib`'s `MeasureTheory.Measure.ae_rnDeriv_ne_zero_imp_of_ae`, stated
for membership in a set.
-/

public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- If `μ` is concentrated on `s`, then its density with respect to `ν` vanishes `ν`-almost
everywhere off `s`. -/
theorem ae_notMem_imp_rnDeriv_eq_zero [SigmaFinite μ] [SigmaFinite ν] {s : Set α}
    (hs : ∀ᵐ x ∂μ, x ∈ s) : ∀ᵐ x ∂ν, x ∉ s → μ.rnDeriv ν x = 0 :=
  (ae_rnDeriv_ne_zero_imp_of_ae ν hs).mono fun _ hx hxs ↦ by
    by_contra h
    exact hxs (hx h)

end MeasureTheory.Measure
