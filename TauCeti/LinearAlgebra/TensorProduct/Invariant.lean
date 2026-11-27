/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Invariant kernels under scalar extension

Scalar extension of a quotient map preserves invariance of its kernel, without a flatness
assumption on the coefficient algebra.
-/

public section

/-- Scalar extension preserves invariance of the kernel of a quotient map. -/
theorem Submodule.invtSubmodule_ker_baseChange {A B P : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup P] [Module A P] (N : Submodule A P)
    {s : Module.End A P} (hN : N ∈ Module.End.invtSubmodule s) :
    (N.mkQ.baseChange B).ker ∈ Module.End.invtSubmodule (s.baseChange B) := by
  have hker : (N.mkQ.baseChange B).ker = N.baseChange B := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_lTensor, ← LinearMap.mem_ker,
      _root_.lTensor_mkQ, Submodule.baseChange, LinearMap.mem_range, LinearMap.mem_range]
    simp only [LinearMap.baseChange_eq_lTensor]
  rw [hker, Submodule.baseChange_eq_span, Module.End.mem_invtSubmodule, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul]
  exact Submodule.subset_span ⟨s x, hN hx, rfl⟩
