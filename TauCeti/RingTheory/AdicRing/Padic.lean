/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.Basic
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# The `p`-adic integers as a complete adic ring

This module supplies the complete separated adic-ring structure (`TauCeti.IsAdicRing`) on
`ℤ_[p]`, with ideal of definition `(p)`, from `PadicInt.isAdic_maximalIdeal`.

## Main instances

* `TauCeti.IsAdicRing.padicInt`: `ℤ_[p]` is a complete separated adic ring of finite ideal type,
  with ideal of definition `(p)`.
-/

public section

namespace TauCeti.IsAdicRing

/-- **`ℤ_[p]` is a complete separated adic ring of finite ideal type**, with ideal of definition
`(p)`. -/
instance padicInt (p : ℕ) [Fact p.Prime] : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    PadicInt.maximalIdeal_eq_span_p (p := p) ▸ Submodule.fg_span_singleton _,
    _root_.PadicInt.isAdic_maximalIdeal, inferInstance⟩

end TauCeti.IsAdicRing
