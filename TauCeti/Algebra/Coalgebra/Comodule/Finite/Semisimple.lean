/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# Semisimple endomorphisms of bundled finite comodules

Over a commutative ring, the bundled finitely generated comodule `FGComoduleCat.of N`
reconstructs its additive group from its module structure. So semisimplicity of an endomorphism
on the bundled object and on the unbundled comodule `N` use different additive-group instances.
This file records that the two statements agree, so callers need not rebuild the
`@`-explicit transport.

## Main declarations

* `TauCeti.isSemisimple_fgComoduleCatOf_iff`: semisimplicity of an endomorphism on
  `FGComoduleCat.of N` agrees with semisimplicity on `N`.
-/

public section

namespace TauCeti

universe u v w

/-- Semisimplicity of an endomorphism of a bundled finitely generated comodule agrees with
semisimplicity on the underlying unbundled comodule. The bundled object reconstructs its additive
group from its module structure, so the two statements use different additive group instances. -/
theorem isSemisimple_fgComoduleCatOf_iff {R : Type u} {C : Type v} {N : Type w} [CommRing R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommGroup N] [Module R N]
    [Comodule R C N] [Module.Finite R N] (f : Module.End R N) :
    @Module.End.IsSemisimple R (FGComoduleCat.of (R := R) (C := C) N) _
        (FGComoduleCat.instAddCommGroupCarrier _) _ f ↔ f.IsSemisimple :=
  @LinearEquiv.isSemisimple_iff R (FGComoduleCat.of (R := R) (C := C) N) _
    (FGComoduleCat.instAddCommGroupCarrier _) _ f N _ _ f (LinearEquiv.refl R N) rfl

end TauCeti
