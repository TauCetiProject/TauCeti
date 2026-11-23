/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension conditions as `Fact` instances

Constructions whose dimension hypothesis `Module.finrank R M = Module.finrank R N` is supplied as
an instance `Fact (Module.finrank R M = Module.finrank R N)` (such as the orthonormal frame bundle
`TauCeti.OrthonormalFrameBundle.Fiber`) apply without further work when `M = N`, by the instance
`TauCeti.instFactFinrankEqSelf`.

The dimension of a product of free finite modules of dimensions `2 n` and `2 m` is `2 (n + m)`, as
an instance of `Fact` (`TauCeti.fact_finrank_prod_eq_two_mul_add`). This is the even-dimensional
form taken by the dimension hypothesis of the volume form of a two-form, such as the product of
two symplectic forms.
-/

public section

namespace TauCeti

/-- A module has its own dimension, as an instance of `Fact`. -/
instance instFactFinrankEqSelf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Fact (Module.finrank R M = Module.finrank R M) :=
  ⟨rfl⟩

/-- The product of free finite modules of dimensions `2 n` and `2 m` has dimension `2 (n + m)`, as
an instance of `Fact`. -/
instance fact_finrank_prod_eq_two_mul_add {R M N : Type*} [Semiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] [AddCommMonoid N]
    [Module R N] [Module.Free R N] [Module.Finite R N] {n m : ℕ}
    [hn : Fact (Module.finrank R M = 2 * n)] [hm : Fact (Module.finrank R N = 2 * m)] :
    Fact (Module.finrank R (M × N) = 2 * (n + m)) :=
  ⟨by rw [Module.finrank_prod, hn.out, hm.out, Nat.mul_add]⟩

end TauCeti
