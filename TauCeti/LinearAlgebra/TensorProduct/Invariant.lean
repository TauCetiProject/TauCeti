/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import TauCeti.LinearAlgebra.TensorProduct.Kernel
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Invariant submodules under scalar extension

Scalar extension preserves invariant submodules over semirings. Over rings this also identifies
invariant kernels of scalar-extended quotient maps, without a flatness assumption on the
coefficient algebra.
-/

public section

/-- Scalar extension preserves invariant submodules over semirings. -/
theorem Submodule.invtSubmodule_baseChange {A B P : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [AddCommMonoid P] [Module A P] (N : Submodule A P)
    {s : Module.End A P} (hN : N ∈ Module.End.invtSubmodule s) :
    N.baseChange B ∈ Module.End.invtSubmodule (s.baseChange B) := by
  rw [Submodule.baseChange_eq_span, Module.End.mem_invtSubmodule, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul]
  exact Submodule.subset_span ⟨s x, hN hx, rfl⟩

/-- Scalar extension preserves invariance of the kernel of a quotient map. -/
theorem Submodule.invtSubmodule_ker_baseChange {A B P : Type*} [CommRing A] [Ring B]
    [Algebra A B] [AddCommGroup P] [Module A P] (N : Submodule A P)
    {s : Module.End A P} (hN : N ∈ Module.End.invtSubmodule s) :
    (N.mkQ.baseChange B).ker ∈ Module.End.invtSubmodule (s.baseChange B) := by
  rw [LinearMap.ker_baseChange_of_surjective B _ N.mkQ_surjective, Submodule.ker_mkQ]
  exact N.invtSubmodule_baseChange hN
