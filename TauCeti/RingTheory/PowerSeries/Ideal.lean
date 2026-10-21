/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The kernel of the coefficientwise map of power series

For a ring homomorphism `f : R →+* S` with finitely generated kernel, the kernel of the induced
map `R⟦X⟧ →+* S⟦X⟧` is the extension of `ker f` along the constant embedding `C`. This is the
one-variable form of `MvPowerSeries.ker_map_of_fg`.

## Main results

* `PowerSeries.ker_map_of_fg`: `ker (map f) = (ker f).map C` when `ker f` is finitely generated.
-/

public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- If `f : R →+* S` has finitely generated kernel, the kernel of the coefficientwise map
`R⟦X⟧ →+* S⟦X⟧` is the extension of `ker f` along the constant embedding. -/
theorem ker_map_of_fg (f : R →+* S) (hf : (RingHom.ker f).FG) :
    RingHom.ker (map f) = (RingHom.ker f).map C := by
  -- `PowerSeries.map` is `MvPowerSeries.map` over `Unit`, and `C` is `MvPowerSeries.C`.
  rw [map, MvPowerSeries.ker_map_of_fg _ hf]
  rfl

end PowerSeries
