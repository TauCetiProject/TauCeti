/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Components of the Galois group as a limit of finite Galois groups

Mathlib identifies the Galois group of a Galois extension `K/k`, with its Krull topology, with the
limit `lim_L Gal(L/k)` of the finite Galois groups over the finite Galois intermediate fields `L`
(`InfiniteGalois.continuousMulEquivToLimit`). This file records that the component at `L` of the
image of `σ` is the restriction of `σ` to `L`, so that components can be computed by rewriting.

## Main results

* `InfiniteGalois.proj_algEquivToLimit`: the component at `L` of `algEquivToLimit k K σ` is the
  restriction of `σ` to `L`.
* `InfiniteGalois.continuousMulEquivToLimit_apply`: `continuousMulEquivToLimit` is
  `algEquivToLimit` as a function.
-/

public section

namespace InfiniteGalois

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The component at `L` of the point of `lim_L Gal(L/k)` attached to `σ` is the restriction of `σ`
to `L`. -/
theorem proj_algEquivToLimit (σ : Gal(K/k)) (L : FiniteGaloisIntermediateField k K) :
    proj L (algEquivToLimit k K σ) = AlgEquiv.restrictNormalHom L σ :=
  (rfl)

/-- The isomorphism `continuousMulEquivToLimit k K` is `algEquivToLimit k K` as a function. -/
theorem continuousMulEquivToLimit_apply [IsGalois k K] (σ : Gal(K/k)) :
    continuousMulEquivToLimit k K σ = algEquivToLimit k K σ :=
  (rfl)

end InfiniteGalois
