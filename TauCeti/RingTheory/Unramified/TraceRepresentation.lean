/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Unramified.Basic
import TauCeti.RingTheory.Semisimple.Trace.Basic
import TauCeti.RingTheory.Unramified.Field

/-!
# Representations of an unramified algebra are determined by their traces

Let `E` be a finite-dimensional formally unramified algebra over a field `K`, for instance a finite
product of number fields over `ℚ`, and let `k` be a field of characteristic zero containing `K`. A
representation of `E` on a finite-dimensional `k`-vector space `V` is a `K`-algebra homomorphism
`ρ : E → End_k V`. This file proves that two such representations with the same trace,
`tr_k (ρ a) = tr_k (ρ' a)` for every `a ∈ E`, are isomorphic
(`TauCeti.exists_linearEquiv_of_trace_eq`).

A representation of `E` over `k` is a module over `k ⊗[K] E`. That algebra is finite-dimensional
over `k` and formally unramified, hence reduced, hence semisimple; so every such module is
semisimple, and finite-dimensional semisimple modules in characteristic zero are determined by
their traces (`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`). The trace of `c ⊗ a` is
`c · tr_k (ρ a)`, so the traces of `ρ` determine those of the whole `k ⊗[K] E`-module.

## Main results

* `TauCeti.exists_linearEquiv_of_trace_eq`: representations of a finite-dimensional formally
  unramified `K`-algebra over a field of characteristic zero with the same traces are isomorphic.

## References

* J. S. Milne, *Complex Multiplication*, §1, proof of Proposition 1.21, p.15.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {K E k V W : Type*} [Field K] [CommRing E] [Algebra K E] [Field k]
  [Algebra K k] [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower K k V]
  [AddCommGroup W] [Module k W] [Module K W] [IsScalarTower K k W]

/-- The algebra map `k ⊗[K] E → End_k V` of a representation `ρ` of `E`, sending `c ⊗ a` to
`c • ρ a`. -/
private noncomputable def tensorLift (ρ : E →ₐ[K] Module.End k V) :
    k ⊗[K] E →ₐ[k] Module.End k V :=
  AlgHom.liftEquiv K k E _ ρ

private theorem tensorLift_tmul (ρ : E →ₐ[K] Module.End k V) (c : k) (a : E) :
    tensorLift ρ (c ⊗ₜ a) = c • ρ a :=
  AlgHom.liftEquiv_tmul ..

/-- **Representations of an unramified algebra are determined by their traces.** Let `E` be a
finite-dimensional formally unramified algebra over a field `K`, such as a finite product of
number fields over `ℚ`, and `k` a field of characteristic zero containing `K`. Two
representations `ρ`, `ρ'` of `E` on finite-dimensional `k`-vector spaces with
`tr_k (ρ a) = tr_k (ρ' a)` for every `a` are isomorphic: some `k`-linear equivalence intertwines
them. -/
theorem exists_linearEquiv_of_trace_eq [CharZero k] [Module.Finite K E]
    [Algebra.FormallyUnramified K E] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : E →ₐ[K] Module.End k V) (ρ' : E →ₐ[K] Module.End k W)
    (h : ∀ a, LinearMap.trace k V (ρ a) = LinearMap.trace k W (ρ' a)) :
    ∃ e : V ≃ₗ[k] W, ∀ a v, e (ρ a v) = ρ' a (e v) := by
  let : Module (k ⊗[K] E) V := Module.compHom V (tensorLift ρ : k ⊗[K] E →+* Module.End k V)
  let : Module (k ⊗[K] E) W := Module.compHom W (tensorLift ρ' : k ⊗[K] E →+* Module.End k W)
  have hV (x : k ⊗[K] E) (v : V) : x • v = tensorLift ρ x v := rfl
  have hW (x : k ⊗[K] E) (w : W) : x • w = tensorLift ρ' x w := rfl
  have : IsScalarTower k (k ⊗[K] E) V := ⟨fun c x v ↦ by simp [hV]⟩
  have : IsScalarTower k (k ⊗[K] E) W := ⟨fun c x w ↦ by simp [hW]⟩
  have hlV (x : k ⊗[K] E) : Algebra.lsmul k k V x = tensorLift ρ x := LinearMap.ext (hV x)
  have hlW (x : k ⊗[K] E) : Algebra.lsmul k k W x = tensorLift ρ' x := LinearMap.ext (hW x)
  -- the traces of `ρ` determine those of the whole `k ⊗[K] E`-module
  have htr (x : k ⊗[K] E) :
      LinearMap.trace k V (tensorLift ρ x) = LinearMap.trace k W (tensorLift ρ' x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c a => simp [tensorLift_tmul, h]
    | add x y hx hy => simp [hx, hy]
  obtain ⟨e⟩ := IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq (k := k) (A := k ⊗[K] E) V W
    fun x ↦ by rw [hlV, hlW]; exact htr x
  refine ⟨e.restrictScalars k, fun a v ↦ ?_⟩
  have h1 : ρ a v = (1 ⊗ₜ a : k ⊗[K] E) • v := by simp [hV, tensorLift_tmul]
  have h2 : ρ' a (e v) = (1 ⊗ₜ a : k ⊗[K] E) • e v := by simp [hW, tensorLift_tmul]
  simp only [LinearEquiv.restrictScalars_apply]
  rw [h1, h2, map_smul]

end TauCeti
