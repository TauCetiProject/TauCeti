/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.Basic
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# The p-adic integers as a complete adic ring

The ring `ℤ_[p]` of `p`-adic integers with its norm topology is a complete separated adic ring of
finite ideal type (`TauCeti.IsAdicRing`), with the maximal ideal `(p)` as ideal of definition.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.1.4.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6.
-/

public section

namespace TauCeti.IsAdicRing

/-- The `p`-adic integers `ℤ_[p]` with their norm topology form a complete separated adic ring of
finite ideal type, with ideal of definition `(p)`. -/
instance padicInt {p : ℕ} [Fact p.Prime] : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

end TauCeti.IsAdicRing
