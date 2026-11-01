/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Basis
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.DirectSum
import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Weight vectors under morphisms of Lie modules and in direct sums

Let `h : κ → L` be a family of designated Cartan vectors of a rational Lie algebra `L`. A morphism
of Lie modules intertwines the enveloping-algebra actions, so it carries a joint eigenvector of the
operators `h j` to a joint eigenvector of the same integral weight. For a family `P i` of Lie
modules, the inclusion `DirectSum.lof` of a summand into `⨁ i, P i` is such a morphism, so it
carries weight vectors to weight vectors and the span of the integral joint weight spaces of a
summand into that of the direct sum.

These are the facts that move the weight data of the summands of a direct sum, for instance of
admissible lattices of the summands, to the direct sum itself, where
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` consumes it.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.map`: a morphism of Lie modules
  preserves weight vectors and their weights.
* `TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_lof`: the inclusion of a summand
  preserves weight vectors and their weights.
* `TauCeti.UniversalEnvelopingAlgebra.lof_mem_iSup_jointWeightSpace`: it maps the span of the
  integral joint weight spaces of a summand into that of the direct sum.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {κ : Type*} {h : κ → L}

/-- **A morphism of Lie modules preserves weight vectors**: it carries a joint eigenvector of the
designated Cartan vectors to one of the same integral weight. -/
theorem IsCartanWeightVector.map {M N : Type*} [AddCommGroup M] [Module ℚ M] [LieRingModule L M]
    [LieModule ℚ L M] [AddCommGroup N] [Module ℚ N] [LieRingModule L N] [LieModule ℚ L N]
    {μ : κ → ℤ} {m : M} (hm : IsCartanWeightVector h (representation ℚ L M) μ m)
    (f : M →ₗ⁅ℚ,L⁆ N) : IsCartanWeightVector h (representation ℚ L N) μ (f m) :=
  (isCartanWeightVector_iff _ _).2 fun j => by
    rw [← map_representation, (isCartanWeightVector_iff _ _).1 hm j, map_smul]

variable {ι : Type*} [DecidableEq ι] {P : ι → Type*} [∀ i, AddCommGroup (P i)]
  [∀ i, Module ℚ (P i)] [∀ i, LieRingModule L (P i)] [∀ i, LieModule ℚ L (P i)]

/-- **The inclusion of a summand preserves weight vectors**: a joint eigenvector of the designated
Cartan vectors in `P i` remains one, of the same integral weight, in `⨁ i, P i`. -/
theorem isCartanWeightVector_lof {i : ι} {μ : κ → ℤ} {m : P i}
    (hm : IsCartanWeightVector h (representation ℚ L (P i)) μ m) :
    IsCartanWeightVector h (representation ℚ L (⨁ i, P i)) μ (lof ℚ ι P i m) := by
  have hc := hm.map (lieModuleOf ℚ ι L P i)
  rwa [lieModuleOf_apply, ← lof_eq_of ℚ] at hc

variable (h) in
/-- **The inclusion of a summand respects the integral weight spaces**: it maps a vector in the span
of the integral joint weight spaces of `P i` into the span of those of `⨁ i, P i`. -/
theorem lof_mem_iSup_jointWeightSpace {i : ι} {m : P i}
    (hm : m ∈ ⨆ μ : κ → ℤ, jointWeightSpace h (representation ℚ L (P i)) μ) :
    lof ℚ ι P i m ∈ ⨆ μ : κ → ℤ, jointWeightSpace h (representation ℚ L (⨁ i, P i)) μ := by
  have hle : (⨆ μ : κ → ℤ, jointWeightSpace h (representation ℚ L (P i)) μ).map (lof ℚ ι P i) ≤
      ⨆ μ : κ → ℤ, jointWeightSpace h (representation ℚ L (⨁ i, P i)) μ := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun μ => Submodule.map_le_iff_le_comap.mpr fun v hv => ?_
    rw [Submodule.mem_comap, mem_jointWeightSpace_iff]
    exact isCartanWeightVector_lof ((mem_jointWeightSpace_iff h _).1 hv)
  exact hle (Submodule.mem_map_of_mem hm)

end TauCeti.UniversalEnvelopingAlgebra
