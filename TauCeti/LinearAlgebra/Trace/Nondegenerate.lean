/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Nondegeneracy of the trace pairing

This file records that the trace pairing `(f, g) ↦ trace (f * g)` on the endomorphisms of a
finite free module over a commutative semiring is nondegenerate. This is the endomorphism
counterpart of `Matrix.ext_iff_trace_mul_right`.

## Main results

* `LinearMap.ext_iff_trace_mul_right`: two endomorphisms are equal exactly when their
  products with every endomorphism have equal trace.
* `LinearMap.forall_trace_mul_eq_zero_iff`: an endomorphism is zero exactly when its products
  with every endomorphism have zero trace.
* `LinearMap.eq_zero_of_forall_trace_mul_eq_zero`: it suffices to test against a spanning family.
* `LinearMap.det_trace_mul_ne_zero`: over an integral domain, the Gram matrix of the trace pairing
  on a basis of the endomorphisms is invertible.
-/

public section

namespace LinearMap

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- The trace pairing on the endomorphisms of a finite free module over a commutative semiring is
nondegenerate: two endomorphisms are equal exactly when their products with every endomorphism
have equal trace. -/
theorem ext_iff_trace_mul_right {f g : Module.End K V} :
    f = g ↔ ∀ h : Module.End K V, trace K V (f * h) = trace K V (g * h) := by
  refine ⟨fun hfg _ ↦ hfg ▸ rfl, fun hfg ↦ ?_⟩
  let b := Module.Free.chooseBasis K V
  refine (toMatrix b b).injective <| Matrix.ext_iff_trace_mul_right.mpr fun Y ↦ ?_
  simpa [trace_eq_matrix_trace K b, toMatrix_mul] using hfg (Matrix.toLin b b Y)

/-- An endomorphism of a finite free module is zero exactly when its products with every
endomorphism have zero trace. -/
@[simp]
theorem forall_trace_mul_eq_zero_iff {f : Module.End K V} :
    (∀ g : Module.End K V, trace K V (f * g) = 0) ↔ f = 0 := by
  simp [ext_iff_trace_mul_right (g := 0)]

/-- The trace pairing against a spanning family is injective: if `trace (bᵢ * f) = 0` for every
member `bᵢ` of a family spanning the endomorphisms, then `f = 0`. -/
theorem eq_zero_of_forall_trace_mul_eq_zero {ι : Type*} {b : ι → Module.End K V}
    (hb : Submodule.span K (Set.range b) = ⊤) {f : Module.End K V}
    (hf : ∀ i, trace K V (b i * f) = 0) : f = 0 := by
  refine forall_trace_mul_eq_zero_iff.mp fun g => ?_
  have hg : g ∈ Submodule.span K (Set.range b) := hb ▸ Submodule.mem_top
  rw [trace_mul_comm]
  induction hg using Submodule.span_induction with
  | mem h hh => obtain ⟨i, rfl⟩ := hh; exact hf i
  | zero => simp
  | add h h' _ _ hh hh' => simp [add_mul, hh, hh']
  | smul a h _ hh => simp [hh]

/-- Over an integral domain, the Gram matrix `(trace (bᵢ * bⱼ))` of the trace pairing on a basis
`b` of the endomorphisms is invertible. -/
theorem det_trace_mul_ne_zero {K V : Type*} [CommRing K] [IsDomain K] [AddCommGroup V]
    [Module K V] [Module.Free K V] [Module.Finite K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K (Module.End K V)) :
    (Matrix.of fun i j => trace K V (b i * b j)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hx : ∑ j, v j • b j = 0 := by
    refine eq_zero_of_forall_trace_mul_eq_zero b.span_eq fun i => ?_
    have := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  exact hv (funext fun j => Fintype.linearIndependent_iff.mp b.linearIndependent v hx j)

end LinearMap
