/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace of an endomorphism of a tensor square

A tensor square carries a basis indexed by *pairs* of indices of a basis of the underlying module,
and the two tensor squares in the library — the binary `M ⊗[R] M` and the `Fin 2`-indexed
`⨂[R]^2 M` — differ only in how that pair index is spelled. This file isolates the computation
they share: an endomorphism of the square whose diagonal entry at the pair `(i, j)` is `aᵢⱼ aⱼᵢ`,
where `a` is the matrix of an endomorphism `f` of the module, has trace `tr (f ∘ f)`, because
summing `aᵢⱼ aⱼᵢ` over all pairs is the trace of `a * a`.

The endomorphism the two callers feed in is `f ⊗ f` composed with the flip of the two factors, but
nothing here knows that: the input is the diagonal of the matrix, so the statement is about an
arbitrary finite basis whose index type is equivalent to a pair type, and the two callers supply
their own basis and their own diagonal computation.

## Main results

* `Module.Basis.trace_eq_trace_comp_self_of_toMatrix_diag`: an endomorphism with diagonal entries
  `aᵢⱼ aⱼᵢ` in a pair-indexed basis has trace `tr (f ∘ f)`.
-/

public section

namespace Module.Basis

variable {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [Finite ι]

/-- **An endomorphism whose diagonal entries are `aᵢⱼ aⱼᵢ` has trace `tr (f ∘ f)`.** Here `a` is
the matrix of `f` in the basis `b`, and the diagonal is read in a basis `B` whose index type is
equivalent, through `e`, to pairs of indices of `b`; summing `aᵢⱼ aⱼᵢ` over all pairs is the trace
of `a * a`, which is the trace of `f ∘ f`. Only the index type of `b` is assumed finite; the
equivalence `e` ensures that the index type of `B` is finite too. -/
theorem trace_eq_trace_comp_self_of_toMatrix_diag (b : Module.Basis ι R M)
    (B : Module.Basis κ R N) (e : κ ≃ ι × ι) (f : M →ₗ[R] M) (T : N →ₗ[R] N)
    (hdiag : ∀ p : κ, B.toMatrix (T ∘ B) p p
      = b.toMatrix (f ∘ b) (e p).1 (e p).2 * b.toMatrix (f ∘ b) (e p).2 (e p).1) :
    LinearMap.trace R N T = LinearMap.trace R M (f ∘ₗ f) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofEquiv (ι × ι) e.symm
  rw [LinearMap.trace_eq_matrix_trace R B, LinearMap.trace_eq_matrix_trace R b,
    LinearMap.toMatrix_comp b b b f f, Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_eq_basisToMatrix, hdiag, Matrix.mul_apply]
  refine Eq.trans (Fintype.sum_equiv e _
    (fun q ↦ b.toMatrix (f ∘ b) q.1 q.2 * b.toMatrix (f ∘ b) q.2 q.1)
    fun _ ↦ rfl) ?_
  exact Fintype.sum_prod_type _

end Module.Basis
