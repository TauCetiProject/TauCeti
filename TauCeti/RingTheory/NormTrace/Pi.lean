/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.Trace.Pi

/-!
# Norms and traces of finite products

This file records the determinant, norm, and trace calculations for finite dependent products.
The scalar-extension identities used by the number-field local-global development live in
`TauCeti.RingTheory.NormTrace.BaseChange`.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u v

variable {K : Type u} [CommRing K]

variable {ι : Type v} [Fintype ι]
variable {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

open Module

/-- The norm of an element of a finite dependent product is the product of its component norms. -/
@[simp]
theorem Algebra.norm_pi (x : ∀ i, L i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  rw [Algebra.norm_apply]
  have h : Algebra.lmul K (∀ i, L i) x =
      LinearMap.pi (fun i ↦ (Algebra.lmul K (L i) (x i)).comp (LinearMap.proj i)) := by
    ext y i
    simp [Algebra.lmul]
  rw [h]
  rw [LinearMap.det_pi_of_apply_eq_dependent
    (f := fun i ↦ Algebra.lmul K (L i) (x i)) (hT := by
    intro y i
    simp [Algebra.lmul])]
  simp_rw [Algebra.norm_apply]

/-- The trace of an element of a finite dependent product is the sum of its component traces. -/
@[simp]
theorem Algebra.trace_pi (x : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) x = ∑ i, Algebra.trace K (L i) (x i) := by
  rw [Algebra.trace_apply]
  calc
    LinearMap.trace K (∀ i, L i) (Algebra.lmul K (∀ i, L i) x) =
        ∑ i, LinearMap.trace K (L i) (Algebra.lmul K (L i) (x i)) := by
      apply LinearMap.trace_pi_of_apply_eq_dependent
        (f := fun i ↦ Algebra.lmul K (L i) (x i))
      intro y i
      simp [Algebra.lmul]
    _ = ∑ i, Algebra.trace K (L i) (x i) := by
      simp_rw [Algebra.trace_apply]

end TauCeti
