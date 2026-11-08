/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite fields of definition for tensors

A finite collection of vectors after an algebraic extension of scalars is already defined over
one finite intermediate field. No finite-dimensionality assumption on the vector space is needed.
-/

public section

open scoped TensorProduct

namespace Set

/-- Finitely many tensors over an algebraic extension have a common finite field of definition. -/
theorem exists_finiteDimensional_intermediateField_subset_range_rTensor
    {k K V : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [AddCommMonoid V] [Module k V] (s : Set (K ⊗[k] V)) (hs : s.Finite) :
    ∃ L : IntermediateField k K, FiniteDimensional k L ∧
      s ⊆ LinearMap.range (LinearMap.rTensor V L.val.toLinearMap) := by
  obtain ⟨J, ⟨t, rfl⟩, hJ⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype s hs
  let L := IntermediateField.adjoin k (t : Set K)
  have hJL : Submodule.span k t ≤ L.toSubalgebra.toSubmodule :=
    Submodule.span_le.mpr (IntermediateField.subset_adjoin k _)
  refine ⟨L, IntermediateField.finiteDimensional_adjoin
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), hJ.trans ?_⟩
  rw [← Submodule.subtype_comp_inclusion _ _ hJL, Subalgebra.toSubmodule_subtype,
    LinearMap.rTensor_comp]
  -- `IntermediateField.val` is defined as `L.toSubalgebra.val`.
  exact LinearMap.range_comp_le_range _ _

end Set
