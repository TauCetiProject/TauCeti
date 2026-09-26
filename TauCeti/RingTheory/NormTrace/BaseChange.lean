/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Norm and trace under scalar extension

This file records the compatibility of algebra norms and traces with scalar extension on pure
tensors.
-/

public section

namespace TauCeti

universe u

variable {K : Type u} [CommRing K]
variable {A B : Type*} [CommRing A] [Algebra K A]

section Norm

variable [Ring B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Norm commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.norm_baseChange_tmul (x : B) :
    Algebra.norm A ((1 : A) ⊗ₜ[K] x) = algebraMap K A (Algebra.norm K x) := by
  rw [Algebra.norm_apply]
  calc
    LinearMap.det (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.det ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.det (Algebra.lmul K B x)) :=
      LinearMap.det_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)
    _ = algebraMap K A (Algebra.norm K x) := by
      rw [Algebra.norm_apply]

end Norm

section Trace

variable [CommRing B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Trace commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.trace_baseChange_tmul (x : B) :
    Algebra.trace A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K B x) := by
  rw [Algebra.trace_apply]
  calc
    LinearMap.trace A (TensorProduct K A B)
        (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.trace A (TensorProduct K A B) ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.trace K B (Algebra.lmul K B x)) :=
      LinearMap.trace_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)
    _ = algebraMap K A (Algebra.trace K B x) := by
      rw [Algebra.trace_apply]

end Trace

end TauCeti
