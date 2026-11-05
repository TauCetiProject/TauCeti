/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis

/-!
# Dual bases for the Killing form

For a Lie algebra with nondegenerate Killing form, every basis has a Killing-dual basis. The
coordinate identities and the basis-independent contraction of a bilinear map against a basis and
its dual hold for every nondegenerate bilinear form; they live in
`TauCeti.LinearAlgebra.BilinearForm.Dual.Basis` and apply to the Killing-dual basis directly. This
file adds the fact that uses the Lie structure: the canonical contraction is invariant under the
adjoint action, because the Killing form is.

## Main definitions

* `TauCeti.killingDualBasis`: the basis dual to a given one under the Killing form.

## Main results

* `TauCeti.sum_apply_lie_killingDualBasis_add_eq_zero`: the canonical contraction is invariant under
  the adjoint action.
-/

public section

open LieAlgebra

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L]

/-- The basis of `L` **dual to `b` under the Killing form**: `κ (killingDualBasis b i) (b j)` is
`1` when `i = j` and `0` otherwise. It abbreviates `(killingForm K L).dualBasis` with the
nondegeneracy supplied by `LieAlgebra.IsKilling`, so Mathlib's `LinearMap.BilinForm.dualBasis` API
and the expansions in `TauCeti.LinearAlgebra.BilinearForm.Dual.Basis` apply to it unchanged. -/
noncomputable abbrev killingDualBasis {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι K L) : Module.Basis ι K L :=
  (killingForm K L).dualBasis (IsKilling.killingForm_nondegenerate K L) b

/-- **The element `∑ᵢ xᵢ ⊗ yᵢ` is invariant under the adjoint action.**  Read through a bilinear
map `f`, the Leibniz expansion of the adjoint action of `z` vanishes: `ad z` and `-ad z` are an
adjoint pair for the Killing form by its invariance, so the two sums are negatives of each other. -/
theorem sum_apply_lie_killingDualBasis_add_eq_zero {W : Type w} [AddCommGroup W] [Module K W]
    (f : L →ₗ[K] L →ₗ[K] W) {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L)
    (z : L) :
    ∑ i, f ⁅z, b i⁆ (killingDualBasis b i) + ∑ i, f (b i) ⁅z, killingDualBasis b i⁆ = 0 := by
  have hpq : LinearMap.IsAdjointPair (killingForm K L) (killingForm K L) (ad K L z) ⇑(-ad K L z) :=
    fun x y ↦ by
      rw [LinearMap.neg_apply, ad_apply, ad_apply, map_neg]
      exact LieModule.traceForm_apply_lie_apply' K L L z x y
  have h := f.sum_apply_dualBasis_of_isAdjointPair (IsKilling.killingForm_nondegenerate K L) b hpq
  simp only [LinearMap.neg_apply, ad_apply, map_neg, Finset.sum_neg_distrib] at h
  rw [← h, add_neg_cancel]

end TauCeti
