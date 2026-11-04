/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# The `ℤ`-linear equivalence with the integer lattice in the mixed space

For a number field `K`, `mixedEmbedding K` embeds `𝓞 K` injectively onto
`NumberField.mixedEmbedding.integerLattice K ⊆ mixedSpace K`. This file packages that bijection as a
`ℤ`-linear equivalence `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K`.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K`: the `ℤ`-linear equivalence
  `𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K` induced by `mixedEmbedding K`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.coe_integerLatticeEquiv`: coercing
  `integerLatticeEquiv K x` to `mixedSpace K` gives `mixedEmbedding K (x : K)`.
-/

public section

noncomputable section

open NumberField NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

/-- The `ℤ`-linear equivalence `𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K` induced by
`mixedEmbedding K`. -/
def integerLatticeEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K :=
  LinearEquiv.ofInjective
    ((mixedEmbedding K).toIntAlgHom.toLinearMap.comp
      ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ))
    (fun _ _ hxy ↦ RingOfIntegers.ext <| mixedEmbedding_injective K (by simpa using hxy))

/-- Coercing `integerLatticeEquiv K x` to `mixedSpace K` evaluates `mixedEmbedding K` at `x`. -/
@[simp]
theorem coe_integerLatticeEquiv {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    (integerLatticeEquiv K x : mixedSpace K) = mixedEmbedding K (x : K) :=
  (rfl)

end TauCeti.NumberField.mixedEmbedding
end
