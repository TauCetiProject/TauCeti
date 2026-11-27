/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Trace.Defs

/-!
# The trace on the ideal of an idempotent

For an idempotent `c` of a finite-dimensional commutative algebra `A` over a field `K`, the ideal
`c A` is a representation of `A` over `K`, and the trace of `x` on it is `Tr_{A/K} (c x)`
(`IsIdempotentElem.trace_lsmul_span_singleton`). Multiplication by `c x` maps `A` onto `c A`, and
`c` acts as the identity on `c A`, so this is the cyclicity of the trace.
-/

public section

/-- **The trace on the ideal of an idempotent.** For an idempotent `c` of a finite-dimensional
commutative algebra `A` over a field `K`, the trace of multiplication by `x` on the ideal `c A` is
`Tr_{A/K} (c x)`. -/
theorem IsIdempotentElem.trace_lsmul_span_singleton {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [FiniteDimensional K A] {c : A} (hc : IsIdempotentElem c) (x : A) :
    LinearMap.trace K (Ideal.span {c}) (Algebra.lsmul K K (Ideal.span {c}) x) =
      Algebra.trace K A (c * x) := by
  set V := Ideal.span {c}
  -- Multiplication by `c x` maps `A` onto `V`, and `c` acts as the identity on `V`.
  let g : A →ₗ[K] V := (LinearMap.toSpanSingleton A V
    ⟨c * x, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)⟩).restrictScalars K
  have hcV (v : V) : c * (v : A) = v := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp v.prop
    rw [← ha, mul_left_comm, hc.eq]
  have h : Algebra.lsmul K K V x = g ∘ₗ V.subtype.restrictScalars K := by
    refine LinearMap.ext fun v ↦ Subtype.ext ?_
    simp [g, ← mul_assoc, mul_comm _ c, hcV, mul_comm x]
  rw [h, LinearMap.trace_comp_comm', Algebra.trace_apply]
  congr 1
  ext y
  simp [g, mul_comm y]
