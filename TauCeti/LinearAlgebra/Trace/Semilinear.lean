/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Traces under semilinear equivalences

A linear equivalence preserves traces (`LinearMap.trace_conj'`). A semilinear equivalence
`j : M ≃ₛₗ[σ] M'` twists them by `σ`: if endomorphisms `T` of `M` and `T'` of `M'` are related by
`T' j = j T`, then `tr T' = σ (tr T)`. For a conjugate-linear equivalence of complex vector
spaces, such as charge conjugation of spinors, the traces are complex conjugate.

## Main results

* `LinearEquiv.trace_eq_map_trace`: `tr T' = σ (tr T)` when `T' j = j T`.
-/

public section

namespace LinearEquiv

open Module

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Module.Free R M] [Module.Finite R M] {σ σ' : R →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/-- Endomorphisms related by a semilinear equivalence `j`, `T' (j x) = j (T x)`, have traces
related by its twist: `tr T' = σ (tr T)`. -/
theorem trace_eq_map_trace (j : M ≃ₛₗ[σ] M') {T : M →ₗ[R] M} {T' : M' →ₗ[R] M'}
    (h : ∀ x, T' (j x) = j (T x)) :
    LinearMap.trace R M' T' = σ (LinearMap.trace R M T) := by
  classical
  let b := Module.Free.chooseBasis R M
  -- `j` carries the basis `b` of `M` to a basis of `M'`.
  have hli : LinearIndependent R fun i ↦ j (b i) :=
    b.linearIndependent.map_of_injective_injectiveₛ σ' j.toAddEquiv.toAddMonoidHom
      (fun _ _ hab ↦ by simpa using congrArg σ hab) j.injective fun r x ↦ by simp [map_smulₛₗ]
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun i ↦ j (b i)) := by
    intro y _
    rw [← j.apply_symm_apply y, ← b.sum_repr (j.symm y), map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Basis.mk hli hsp
  rw [LinearMap.trace_eq_matrix_trace R b' T', LinearMap.trace_eq_matrix_trace R b T,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hT : T' (b' i) = ∑ k, σ (b.repr (T (b i)) k) • b' k := by
    rw [Basis.mk_apply, h, ← b.sum_repr (T (b i)), map_sum]
    simp [b', map_smulₛₗ]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hT, b'.repr_sum_self]

end LinearEquiv
