/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Finitely generated trivial comodules

This file packages the trivial right comodule examples as finitely generated bundled
comodules. These are finite-category examples, so they live next to `FGComoduleCat` rather
than in the unbundled trivial-comodule API.

## Main definitions

* `TauCeti.FGComoduleCat.trivial`: the finitely generated bundled trivial comodule on `R`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v

namespace FGComoduleCat

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The finitely generated bundled trivial right comodule over a bialgebra.

Its underlying module is the rank-one module `R`, with coaction `r ↦ r ⊗ 1`. -/
abbrev trivial : FGComoduleCat.{u, v, u} R C :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  of (R := R) (C := C) R

/-- The ambient bundled comodule underlying `FGComoduleCat.trivial`. -/
@[simp]
theorem trivial_obj : (trivial R C).obj = ComoduleCat.trivial R C :=
  rfl

/-- The coaction on `FGComoduleCat.trivial` sends `r` to `r ⊗ 1`. -/
@[simp]
theorem trivial_coact :
    letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
    Comodule.coact (R := R) (C := C) (M := (trivial R C).obj) =
      (TensorProduct.mk R R C).flip (1 : C) :=
  rfl

end FGComoduleCat

end TauCeti
