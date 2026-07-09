/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Additional API for monoid-algebra bialgebra maps

This file records small convenience lemmas for Mathlib's bialgebra maps between monoid algebras.

## Main declarations

* `TauCeti.MonoidAlgebra.mapDomainBialgHom_single`: the bialgebra map induced by a monoid
  homomorphism sends `single g r` to `single (φ g) r`.

## References

The bialgebra map `MonoidAlgebra.mapDomainBialgHom` is Mathlib's
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`.
-/

public section

namespace TauCeti

universe u v w

namespace MonoidAlgebra

variable {R : Type u} {G : Type v} {G' : Type w}
variable [CommSemiring R] [Monoid G] [Monoid G']

/-- The bialgebra map induced by a monoid homomorphism sends a monoid-algebra generator to the
corresponding generator. -/
@[simp]
theorem mapDomainBialgHom_single (φ : G →* G') (g : G) (r : R) :
    _root_.MonoidAlgebra.mapDomainBialgHom R φ (_root_.MonoidAlgebra.single g r) =
      _root_.MonoidAlgebra.single (φ g) r := by
  rw [_root_.MonoidAlgebra.mapDomainBialgHom, _root_.BialgHom.ofAlgHom_apply,
    _root_.MonoidAlgebra.mapDomainAlgHom_apply, _root_.MonoidAlgebra.mapDomain_single]

end MonoidAlgebra

end TauCeti
