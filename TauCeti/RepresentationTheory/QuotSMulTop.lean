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
of `ρ`. It is Mathlib's `Representation.quotient` by the `G`-stable submodule `r • ⊤`.

Reducing the regular representation `k[G]` modulo `r` gives, up to isomorphism, the regular
representation of `G` over `k ⧸ (r)`. Such reductions are the graded pieces of filtrations
`V ⊇ r • V ⊇ r ^ 2 • V ⊇ ⋯` of a representation, and of the multiplicative filtrations of unit
groups modelled on them.

## Main definitions

* `Representation.quotSMulTop`: the representation induced by `ρ` on `V ⧸ r • V`.

## Main statements

* `Representation.quotSMulTop_forall_eq_sum`: if the identity of `ρ` is a norm
  `x ↦ ∑ g, ρ g (φ (ρ g⁻¹ x))`, then so is the identity of `ρ.quotSMulTop r`.
-/

public section

open scoped Pointwise

namespace Representation

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The representation induced by `ρ` on the reduction `V ⧸ r • V` of `V` modulo `r`: Mathlib's
quotient representation `Representation.quotient` by the `G`-stable submodule `r • ⊤`. Its
operators are `QuotSMulTop.map r (ρ g)` (`Representation.quotSMulTop_apply`). -/
noncomputable def quotSMulTop (ρ : Representation k G V) (r : k) :
    Representation k G (QuotSMulTop r V) :=
  ρ.quotient (r • ⊤) fun g ↦ by
    simpa only [Submodule.ideal_span_singleton_smul] using
      Submodule.smul_top_le_comap_smul_top (Ideal.span {r}) (ρ g)

/-- The operators of `ρ.quotSMulTop r` are the reductions `QuotSMulTop.map r (ρ g)`. -/
@[simp]
theorem quotSMulTop_apply (ρ : Representation k G V) (r : k) (g : G) :
    ρ.quotSMulTop r g = QuotSMulTop.map r (ρ g) :=
  (rfl)

/-- `ρ.quotSMulTop r g` sends the class of `x` to the class of `ρ g x`. -/
theorem quotSMulTop_apply_mk (ρ : Representation k G V) (r : k) (g : G) (x : V) :
    ρ.quotSMulTop r g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
  (rfl)

section Group

variable {G : Type*} [Group G] [Fintype G] {ρ : Representation k G V}

/-- If the identity of `ρ` is the norm `x ↦ ∑ g, ρ g (φ (ρ g⁻¹ x))` of a `k`-linear map `φ`, then
the identity of `ρ.quotSMulTop r` is the norm of the reduction `QuotSMulTop.map r φ`. -/
theorem quotSMulTop_forall_eq_sum (φ : V →ₗ[k] V) (hφ : ∀ x, x = ∑ g : G, ρ g (φ (ρ g⁻¹ x)))
    (r : k) (x : QuotSMulTop r V) :
    x = ∑ g : G, ρ.quotSMulTop r g (QuotSMulTop.map r φ (ρ.quotSMulTop r g⁻¹ x)) := by
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  conv_lhs => rw [hφ x, ← Submodule.mkQ_apply, map_sum]
  simp

end Group

end Representation
