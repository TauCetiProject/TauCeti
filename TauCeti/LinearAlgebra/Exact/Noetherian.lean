/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.LinearAlgebra.Exact

/-!
# Finite generation in exact sequences over Noetherian modules

If `M --f--> N --g--> P` is exact at `N`, `M` is finitely generated, and `P` is Noetherian, then
`N` is finitely generated (`TauCeti.finite_of_exact`). In particular, over a Noetherian ring `R`,
`N` is finitely generated whenever `M` and `P` are.
-/

public section

namespace TauCeti

/-- If `M --f--> N --g--> P` is exact at `N`, `M` is finitely generated, and `P` is Noetherian,
then `N` is finitely generated.

In particular, over a Noetherian ring `R`, `N` is finitely generated whenever `M` and `P` are.
This is deduced from `Module.Finite.of_exact`, which asks the second map to be surjective, by
corestricting `g` to its range (a submodule of the Noetherian module `P`, hence finitely
generated). -/
theorem finite_of_exact {R M N P : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] {f : M →ₗ[R] N}
    {g : N →ₗ[R] P} (h : Function.Exact f g) [Module.Finite R M] [IsNoetherian R P] :
    Module.Finite R N :=
  Module.Finite.of_exact h.rangeRestrict g.surjective_rangeRestrict

end TauCeti
