/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.Depth.TrivSqZeroExt

/-!
# Trivial square-zero extensions which are not Cohen–Macaulay

Let `R` be a local ring and `M` an `R`-module of depth zero. Then the trivial square-zero
extension `S = TrivSqZeroExt R M` has depth zero over itself (`TrivSqZeroExt.depth_eq_zero`). As
`S` has the Krull dimension of `R`, it is not Cohen–Macaulay unless `R` has dimension zero.

The main example is `M = R ⧸ 𝔪`, where `S ≅ R[z] ⧸ (z², 𝔪z)` with `z = (0, 1)`. For a regular
local ring `R` of positive dimension, `R → S` is a finite local homomorphism of Noetherian local
rings satisfying the dimension formula `dim S = dim R + dim S ⧸ 𝔪S`, since the closed fibre
`S ⧸ 𝔪S = κ[z] ⧸ (z²)` has dimension zero
(`TauCeti.ringKrullDim_quotient_map_maximalIdeal_eq_zero`). Yet `S` is not flat over `R`
(`TrivSqZeroExt.not_flat`). So the Cohen–Macaulay hypothesis of miracle flatness
(Stacks, Lemma 10.128.1 (00R4)) cannot be dropped.

## Main results

* `TrivSqZeroExt.not_isCohenMacaulay`: the trivial square-zero extension of a local ring of
  positive dimension by a module of depth zero is not Cohen–Macaulay.

## References

* [Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), miracle flatness,
  whose Cohen–Macaulay hypothesis this example shows to be necessary.
-/

public section

open IsLocalRing

universe u v

namespace TrivSqZeroExt

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [Small.{v} R]

/-- The trivial square-zero extension of a local ring of positive dimension by a module of depth
zero is not Cohen–Macaulay. -/
theorem not_isCohenMacaulay (hM : depth (ModuleCat.of R M) = 0) (hR : ringKrullDim R ≠ 0) :
    ¬ Module.IsCohenMacaulay (TrivSqZeroExt R M) (TrivSqZeroExt R M) := fun h ↦ by
  have := h.depth_eq
  rw [depth_eq_zero hM, Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq] at this
  exact hR (by exact_mod_cast this.symm)

end TrivSqZeroExt
