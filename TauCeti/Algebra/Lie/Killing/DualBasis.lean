/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis

import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# Dual bases for the Killing form

For a Lie algebra with nondegenerate Killing form, every basis has a Killing-dual basis. The
coordinate identities and the basis-independent contraction of a bilinear map against a basis and
its dual hold for every nondegenerate bilinear form; they live in
`TauCeti.LinearAlgebra.BilinearForm.Dual.Basis` and apply to the Killing-dual basis directly. This
file adds the facts that use the Lie structure: the trace of `ad x` vanishes along a basis and its
Killing dual, and the canonical contraction is invariant under the adjoint action, because the
Killing form is. Consequently the bracket of `∑ᵢ xᵢ ⊗ yᵢ` vanishes, and the Casimir operator
`z ↦ ∑ᵢ ⁅⁅z, xᵢ⁆, yᵢ⁆` of the adjoint representation is the identity.

## Main definitions

* `TauCeti.killingDualBasis`: the basis dual to a given one under the Killing form.

## Main results

* `TauCeti.sum_killingForm_lie_killingDualBasis_eq_zero`: the trace of `ad x`, written along a basis
  and its Killing dual, vanishes.
* `TauCeti.sum_apply_lie_killingDualBasis_add_eq_zero`: the canonical contraction is invariant under
  the adjoint action.
* `TauCeti.sum_lie_killingDualBasis_eq_zero`: `∑ᵢ ⁅xᵢ, yᵢ⁆ = 0`.
* `TauCeti.sum_lie_lie_killingDualBasis`: the adjoint Casimir operator is the identity.
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

/-- **The trace of `ad x`, written along a basis and its Killing dual, vanishes**, because a Lie
algebra with nondegenerate Killing form is perfect. -/
theorem sum_killingForm_lie_killingDualBasis_eq_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) (x : L) :
    ∑ i, killingForm K L ⁅x, b i⁆ (killingDualBasis b i) = 0 := by
  have := b.finiteDimensional_of_finite
  have htrace := LinearMap.BilinForm.sum_apply_dualBasis_eq_trace
    (IsKilling.killingForm_nondegenerate K L) b (ad K L x)
  simp only [ad_apply] at htrace
  rw [Finset.sum_congr rfl fun i _ ↦ LieModule.traceForm_comm K L L ⁅x, b i⁆ _, htrace]
  refine LieModule.trace_toEnd_eq_zero_of_mem_lcs K L L le_rfl
    (LieModule.derivedSeries_le_lowerCentralSeries K L 1 ?_)
  rw [derivedSeries_one_eq_top_of_isKilling]
  exact LieSubmodule.mem_top x

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

/-- **The bracket of `∑ᵢ xᵢ ⊗ yᵢ` vanishes**: `∑ᵢ ⁅xᵢ, yᵢ⁆ = 0` for a basis `x` and its Killing
dual `y`. -/
theorem sum_lie_killingDualBasis_eq_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) :
    ∑ i, ⁅b i, killingDualBasis b i⁆ = 0 := by
  -- Paired with any `w`, the sum is the trace of `ad w`, which vanishes.
  refine (IsKilling.killingForm_nondegenerate K L).2 _ fun w ↦ ?_
  simp only [map_sum, ← LieModule.traceForm_apply_lie_apply]
  exact sum_killingForm_lie_killingDualBasis_eq_zero b w

/-- **The Casimir operator of the adjoint representation is the identity**:
`∑ᵢ ⁅⁅z, xᵢ⁆, yᵢ⁆ = z` for a basis `x` and its Killing dual `y`. -/
theorem sum_lie_lie_killingDualBasis {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) (z : L) :
    ∑ i, ⁅⁅z, b i⁆, killingDualBasis b i⁆ = z := by
  have := b.finiteDimensional_of_finite
  rw [← sub_eq_zero]
  -- Paired with any `w`, the left side is the trace of `ad w ∘ ad z`, that is `κ(w, z)`.
  refine (IsKilling.killingForm_nondegenerate K L).2 _ fun w ↦ ?_
  have htrace := LinearMap.BilinForm.sum_apply_dualBasis_eq_trace
    (IsKilling.killingForm_nondegenerate K L) b (ad K L w ∘ₗ ad K L z)
  simp only [LinearMap.comp_apply, ad_apply, ← killingForm_apply_apply] at htrace
  rw [map_sub, map_sum, ← htrace, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← LieModule.traceForm_apply_lie_apply, LieModule.traceForm_comm]

end TauCeti
