/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.Bialgebra.Module.TensorProduct

/-!
# Twisted traces on tensor products of bialgebra modules

Let `a` be an element of a bialgebra `H` whose coproduct is `Δ a = a ⊗ a`, for example a
group-like element. On the tensor product `M ⊗ N` of two `H`-modules, with `H` acting through its
coproduct (`BialgebraModule.Tensor`), the element `a` acts as `a ⊗ a`. Consequently the twisted
trace `φ ↦ tr(a ∘ φ)` is multiplicative on tensor products of `H`-linear endomorphisms:

`tr_(M ⊗ N)(a ∘ (f ⊗ g)) = tr_M(a ∘ f) · tr_N(a ∘ g)`.

When `a` is a group-like element implementing the square of the antipode by conjugation, these
twisted traces are the traces of the pivotal structure `v ↦ (φ ↦ φ(a v))` on finite-dimensional
modules, and the formula above is their multiplicativity.

## Main results

* `TauCeti.BialgebraModule.trace_lsmul_comp_tensorMap`: the twisted trace of a tensor product of
  intertwiners is the product of the twisted traces.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XIV, for twisted
  (quantum) traces of modules over Hopf algebras.
-/

public section

open Module

namespace TauCeti.BialgebraModule

variable {R H M N : Type*} [CommRing R] [Semiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Module H M] [IsScalarTower R H M]
  [AddCommGroup N] [Module R N] [Module H N] [IsScalarTower R H N]

/-- **Twisted traces are multiplicative.** For an element `a` with coproduct `a ⊗ a`, the trace of
`a ∘ (f ⊗ g)` on the coproduct tensor product of two finite free modules is the product of the
traces of `a ∘ f` and of `a ∘ g`. -/
theorem trace_lsmul_comp_tensorMap [Module.Free R M] [Module.Finite R M] [Module.Free R N]
    [Module.Finite R N] {a : H} (ha : Coalgebra.comul (R := R) a = a ⊗ₜ[R] a)
    (f : M →ₗ[H] M) (g : N →ₗ[H] N) :
    LinearMap.trace R (Tensor R H M N)
        (Algebra.lsmul R R (Tensor R H M N) a ∘ₗ (tensorMap R H f g).restrictScalars R) =
      LinearMap.trace R M (Algebra.lsmul R R M a ∘ₗ f.restrictScalars R) *
        LinearMap.trace R N (Algebra.lsmul R R N a ∘ₗ g.restrictScalars R) := by
  -- Through `tensorEquiv`, the twisted endomorphism is the native tensor product of maps.
  have h : (tensorEquiv R H M N).symm.conj
      (TensorProduct.map (Algebra.lsmul R R M a ∘ₗ f.restrictScalars R)
        (Algebra.lsmul R R N a ∘ₗ g.restrictScalars R)) =
      Algebra.lsmul R R (Tensor R H M N) a ∘ₗ (tensorMap R H f g).restrictScalars R := by
    refine LinearMap.ext fun x => (tensorEquiv R H M N).injective ?_
    simp [-tensorEquiv_smul, LinearEquiv.conj_apply_apply, tensorEquiv_smul_of_comul_eq_tmul ha,
      TensorProduct.map_comp]
  rw [← h, LinearMap.trace_conj', LinearMap.trace_tensorProduct']

end TauCeti.BialgebraModule
