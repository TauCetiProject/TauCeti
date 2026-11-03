/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Flat
public import TauCeti.RingTheory.Smooth.Regular

/-!
# Smooth algebras over Cohen–Macaulay rings

A smooth algebra `S` over a Cohen–Macaulay ring `R` is Cohen–Macaulay. The algebra is flat and
Noetherian, and its fibres `κ(p) ⊗[R] S` are smooth over fields, hence regular and in particular
Cohen–Macaulay, so `TauCeti.Ring.IsCohenMacaulay.of_flat` applies.

## Main results

* `TauCeti.Ring.IsCohenMacaulay.of_smooth`: a smooth algebra over a Cohen–Macaulay ring is a
  Cohen–Macaulay ring.

## References

* H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.3.
-/

public section

universe u

namespace TauCeti.Ring

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A smooth algebra over a Cohen–Macaulay ring is Cohen–Macaulay. -/
theorem IsCohenMacaulay.of_smooth [IsCohenMacaulay R] [_root_.Algebra.Smooth R S] :
    IsCohenMacaulay S :=
  have := _root_.Algebra.FiniteType.isNoetherianRing R S
  .of_flat (R := R) fun p _ ↦
    have : IsRegularRing (p.Fiber S) := IsRegularRing.of_smooth (R := p.ResidueField)
    inferInstance

end TauCeti.Ring
