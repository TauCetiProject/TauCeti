/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# Subspaces of linear maps stable under composition

A subspace of `Hom(V, W)` stable under composition with every endomorphism of the source and
of the target is either zero or the whole space, when `V` is finite-dimensional. This is the
linear-algebra input to irreducibility of two-sided Hom representations.
-/

public section

open scoped TensorProduct

namespace Submodule

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k V]

/-- A subspace of linear maps closed under arbitrary precomposition and postcomposition is
either zero or the whole space. Only the source needs to be finite-dimensional. -/
theorem eq_bot_or_eq_top_of_comp_mem (N : Submodule k (V →ₗ[k] W))
    (hleft : ∀ (a : Module.End k W) ⦃f⦄, f ∈ N → a.comp f ∈ N)
    (hright : ∀ (a : Module.End k V) ⦃f⦄, f ∈ N → f.comp a ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  refine or_iff_not_imp_left.mpr fun hN ↦ ?_
  obtain ⟨f, hf, hne⟩ := N.ne_bot_iff.mp hN
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := DFunLike.ne_iff.mp hne
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv
  have hrank (φ : Module.Dual k V) (w : W) : φ.smulRight w ∈ N := by
    convert hleft (l.smulRight w) (hright (φ.smulRight v) hf) using 1
    ext
    simp [hl]
  refine N.eq_top_iff'.mpr fun F ↦ ?_
  obtain ⟨z, rfl⟩ := (dualTensorHomEquiv k V W).surjective F
  induction z using TensorProduct.inductionOn with
  | tmul φ w => exact hrank φ w
  | add a b ha hb => simpa using N.add_mem ha hb

end Submodule
