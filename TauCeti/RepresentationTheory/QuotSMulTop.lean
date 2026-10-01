/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Reducing a representation modulo a scalar

For a representation `ρ` of a monoid `G` on a module `V` over a commutative ring `k` and an
element `r : k`, every operator `ρ g` is `k`-linear and so preserves `r • V`. The representation
therefore descends to the quotient `QuotSMulTop r V = V ⧸ r • V`; this is
`Representation.quotSMulTop`, whose operators are Mathlib's `QuotSMulTop.map r` applied to those
of `ρ`.

Reducing the regular representation `k[G]` modulo `r` gives, up to isomorphism, the regular
representation of `G` over `k ⧸ (r)`. Such reductions are the graded pieces of filtrations
`V ⊇ r • V ⊇ r ^ 2 • V ⊇ ⋯` of a representation, and of the multiplicative filtrations of unit
groups modelled on them.

## Main definitions

* `Representation.quotSMulTop`: the representation induced by `ρ` on `V ⧸ r • V`.
-/

public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The representation induced by `ρ` on the reduction `V ⧸ r • V` of `V` modulo `r`. Its value on
the class of `x` is computed by `Representation.quotSMulTop_apply_mk`. -/
noncomputable def quotSMulTop (ρ : Representation k G V) (r : k) :
    Representation k G (QuotSMulTop r V) where
  toFun g := QuotSMulTop.map r (ρ g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp]

/-- `ρ.quotSMulTop r g` sends the class of `x` to the class of `ρ g x`. -/
@[simp]
theorem quotSMulTop_apply_mk (ρ : Representation k G V) (r : k) (g : G) (x : V) :
    ρ.quotSMulTop r g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
  (rfl)

end Representation
