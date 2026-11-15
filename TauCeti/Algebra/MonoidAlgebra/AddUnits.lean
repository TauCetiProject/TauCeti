/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import TauCeti.Data.Finsupp.AddUnits

/-!
# Zero-sum-free monoid and polynomial semirings

If a semiring `R` has trivial additive units (`Subsingleton (AddUnits R)`), then so do
`MonoidAlgebra R G` and `AddMonoidAlgebra R M`. Since `Polynomial R`, `MvPolynomial σ R`, and
Laurent polynomial semirings are abbreviations for `AddMonoidAlgebra`, they inherit this instance
automatically.
-/

public section

namespace TauCeti

instance instSubsingletonAddUnitsMonoidAlgebra {R G : Type*} [Semiring R]
    [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (MonoidAlgebra R G)) :=
  (AddUnits.map_injective (f := MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
    MonoidAlgebra.coeff_injective).subsingleton

instance instSubsingletonAddUnitsAddMonoidAlgebra {R M : Type*} [Semiring R]
    [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (AddMonoidAlgebra R M)) :=
  (AddUnits.map_injective (f := AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
    AddMonoidAlgebra.coeff_injective).subsingleton

end TauCeti
