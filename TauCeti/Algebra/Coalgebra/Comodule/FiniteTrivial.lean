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
* `TauCeti.FGComoduleCat.trivialTensor`: the finitely generated bundled tensor product of
  two trivial comodules, implemented as the existing trivial comodule on `M ⊗[R] N`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace FGComoduleCat

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The finitely generated bundled trivial right comodule over a bialgebra.

Its underlying module is the rank-one module `R`, with coaction `r ↦ r ⊗ 1`. -/
abbrev trivial : FGComoduleCat.{u, v, u} R C :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  of (R := R) (C := C) R

variable {R C}
variable {M : Type w} {N : Type x}
variable [AddCommMonoid M] [Module R M] [Module.Finite R M]
variable [AddCommMonoid N] [Module R N] [Module.Finite R N]

/-- The finitely generated bundled tensor product of two trivial comodules. -/
abbrev trivialTensor : FGComoduleCat.{u, v, max w x} R C :=
  letI : Comodule R C (M ⊗[R] N) := Comodule.trivial (R := R) (C := C) (M := M ⊗[R] N)
  of (R := R) (C := C) (M ⊗[R] N)

end FGComoduleCat

end TauCeti
