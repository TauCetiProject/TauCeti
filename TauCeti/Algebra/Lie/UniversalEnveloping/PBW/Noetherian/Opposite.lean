/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Noetherian.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode

/-!
# Right Noetherian universal enveloping algebras

The antipode identifies a universal enveloping algebra with its opposite algebra, so
left Noetherianity implies right Noetherianity. Mathlib expresses the latter as
`IsNoetherianRing (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ`.

In particular, the enveloping algebra of a Lie algebra finite as a module over a
commutative Noetherian ring is Noetherian on both sides. The left Noetherian result in
`TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Noetherian.Basic` uses the surjection from the
symmetric algebra to the PBW associated graded and the filtered-to-graded transfer.
The instance here obtains its right counterpart through the existing
`TauCeti.UniversalEnvelopingAlgebra.antipodeEquiv`, without freeness, characteristic,
or algebraic-closure assumptions. This supplies the ascending chain condition on right
ideals used in the structure theory of enveloping algebras.

## References

* J. Dixmier, *Enveloping Algebras*, AMS GSM 11 (1996), §2.3.
* J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, Wiley (1987), §1.6.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A left Noetherian universal enveloping algebra is also right Noetherian. In particular,
this applies to every module-finite Lie algebra over a commutative Noetherian ring. -/
instance instIsNoetherianRingMulOpposite
    [IsNoetherianRing (_root_.UniversalEnvelopingAlgebra R L)] :
    IsNoetherianRing (_root_.UniversalEnvelopingAlgebra R L)ᵐᵒᵖ :=
  isNoetherianRing_of_ringEquiv _ (antipodeEquiv (L := L) R).toRingEquiv

end TauCeti.UniversalEnvelopingAlgebra
