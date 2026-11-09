/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple

/-!
# Transporting semisimplicity of an endomorphism along an injection

`LinearEquiv.isSemisimple_iff` transports semisimplicity between two endomorphisms intertwined by
a linear equivalence. For one of the two directions an injection is enough: an endomorphism that
embeds equivariantly into a semisimple one is semisimple, just as a submodule of a semisimple
module is semisimple.

## Main results

* `Module.End.IsSemisimple.of_injective`: semisimplicity passes to an endomorphism that
  admits an injective intertwiner into a semisimple one.
-/

public section

open Polynomial

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Semisimplicity descends along an injective intertwiner.** If `i` is injective and carries
`f` to `g`, and `g` is semisimple, then so is `f`. -/
theorem IsSemisimple.of_injective {f : End R M} {g : End R N} (hg : g.IsSemisimple)
    (i : M →ₗ[R] N) (hi : Function.Injective i) (hcomm : i ∘ₗ f = g ∘ₗ i) :
    f.IsSemisimple :=
  have : IsSemisimpleModule R[X] (AEval' g) := hg
  -- `i` is `R[X]`-linear for the two `AEval'` structures precisely because it intertwines the
  -- endomorphisms, so it embeds `AEval' f` into the semisimple module `AEval' g`.
  IsSemisimpleModule.of_injective
    (LinearMap.ofAEval _ ((AEval'.of g).toLinearMap ∘ₗ i) fun x ↦ by
      simpa [AEval'.X_smul_of] using congr(AEval'.of g ($hcomm x)))
    -- By definition of `LinearMap.ofAEval`, this embedding is `i` conjugated by `AEval'.of`.
    ((AEval'.of g).injective.comp hi |>.comp (AEval'.of f).symm.injective)

end Module.End
