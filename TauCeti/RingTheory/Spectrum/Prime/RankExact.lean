/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Basic
import TauCeti.LinearAlgebra.Exact

/-!
# Rank at stalks along short exact sequences

A short exact sequence `0 → K → X → Y → 0` with `Y` projective splits
(`Function.Exact.exists_linearEquiv_prod_of_projective`), so when `X` is finite flat, `K` is a
finite flat direct summand of `X` and the rank at every prime is additive along the sequence.

## Main results

* `Function.Exact.rankAtStalk_eq_add`: rank is additive on a short exact sequence of a finite flat
  module onto a projective one.
-/

public section

namespace Function.Exact

/-- **Rank is additive on short exact sequences.** If `0 → K → X → Y → 0` is exact, `X` is finite
flat and `Y` is projective (hence finite, as a quotient of `X`), then the rank of `X` at every
prime is the sum of the ranks of `K` and `Y`. -/
theorem rankAtStalk_eq_add {R K X Y : Type*} [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module.Finite R X]
    [Module.Flat R X] [Module.Projective R Y] {f : K →ₗ[R] X}
    {g : X →ₗ[R] Y} (hfg : Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.rankAtStalk (R := R) X = Module.rankAtStalk K + Module.rankAtStalk Y := by
  have : Module.Finite R Y := .of_surjective g hg
  -- The sequence splits, so `K` is a direct summand of `X`, with retraction `π`.
  obtain ⟨e, -, -⟩ := hfg.exists_linearEquiv_prod_of_projective hf hg
  let π : X →ₗ[R] K := LinearMap.fst R K Y ∘ₗ e.toLinearMap
  have : Module.Finite R K := .of_surjective π (Prod.fst_surjective.comp e.surjective)
  have : Module.Flat R K := .of_retract (e.symm.toLinearMap ∘ₗ LinearMap.inl R K Y) π
    (by ext x; simp [π])
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]

end Function.Exact
