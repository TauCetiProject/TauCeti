/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Basis
-- Non-public: this supplies the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.DirectSum

/-!
# Weight vectors in direct sums

Let `h : κ → L` be a family of designated Cartan vectors of a rational Lie algebra `L`. A morphism
of Lie modules carries a joint eigenvector of the operators `h j` to a joint eigenvector of the same
integral weight (`TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector.map`), and the span of
the integral joint weight spaces into that of its target
(`TauCeti.UniversalEnvelopingAlgebra.map_mem_iSup_jointWeightSpace`). For a family `P i` of Lie
modules, the inclusion `DirectSum.lof` of a summand into `⨁ i, P i` is such a morphism, so it
carries weight vectors to weight vectors and the span of the integral joint weight spaces of a
summand into that of the direct sum.

These are the facts that move the weight data of the summands of a direct sum, for instance of
admissible lattices of the summands, to the direct sum itself, where
`TauCeti.UniversalEnvelopingAlgebra.kostantWeightBasis` consumes it.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_lof`: the inclusion of a summand
  preserves weight vectors and their weights.
* `TauCeti.UniversalEnvelopingAlgebra.lof_mem_iSup_jointWeightSpace`: it maps the span of the
  integral joint weight spaces of a summand into that of the direct sum.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {κ : Type*} {h : κ → L}

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
  have hc := map_mem_iSup_jointWeightSpace h hm (lieModuleOf ℚ ι L P i)
  rwa [lieModuleOf_apply, ← lof_eq_of ℚ] at hc

end TauCeti.UniversalEnvelopingAlgebra
