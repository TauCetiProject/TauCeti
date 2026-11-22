/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Traces under semilinear equivalences

A linear equivalence preserves traces (`LinearMap.trace_conj'`). A semilinear equivalence
`j : M ≃ₛₗ[σ] M'` twists them by `σ`: if endomorphisms `T` of `M` and `T'` of `M'` are related by
`T' j = j T`, then `tr T' = σ (tr T)`. For a conjugate-linear equivalence of complex vector
spaces, such as charge conjugation of spinors, the traces are complex conjugate.

## Main results

* `LinearEquiv.trace_eq_map_trace`: `tr T' = σ (tr T)` when `T' j = j T`.
* `LinearMap.trace_comp_comp_of_involutive`: `tr (K ∘ f ∘ K) = σ (tr f)` for a `σ`-semilinear
  involution `K`.
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

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {σ : R →+* R}
  [RingHomInvPair σ σ] [RingHomCompTriple σ σ (RingHom.id R)]

/-- Conjugating an endomorphism by a `σ`-semilinear involution `K` twists its trace by `σ`:
`tr (K ∘ f ∘ K) = σ (tr f)`. For a conjugate-linear involution of a complex vector space the
traces are complex conjugate. Without a finite basis both traces vanish. -/
theorem trace_comp_comp_of_involutive {K : M →ₛₗ[σ] M} (hK : Function.Involutive K)
    (f : M →ₗ[R] M) : trace R M ((K.comp f).comp K) = σ (trace R M f) := by
  by_cases hb : ∃ s : Finset M, Nonempty (Module.Basis s R M)
  · obtain ⟨s, ⟨b⟩⟩ := hb
    have : Module.Free R M := .of_basis b
    have : Module.Finite R M := .of_basis b
    exact (LinearEquiv.ofInvolutive K hK).trace_eq_map_trace fun x ↦ by
      simp [LinearEquiv.coe_ofInvolutive, hK x]
  · simp [TauCeti.LinearMap.trace_eq_zero_of_not_exists_basis hb]

end LinearMap

