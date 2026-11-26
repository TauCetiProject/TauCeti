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

Let `E` be a formally unramified algebra of essentially finite type over a commutative ring
`R`, for instance a finite product of number fields over `ℚ`, and let `k` be a field of
characteristic zero that is an `R`-algebra. A representation of `E` on a finite-dimensional
`k`-vector space `V` is an `R`-algebra homomorphism `ρ : E → End_k V`. This file proves that
two such representations with the same trace, `tr_k (ρ a) = tr_k (ρ' a)` for every `a ∈ E`, are
isomorphic (`TauCeti.exists_linearEquiv_of_trace_eq`).

A representation of `E` over `k` is a module over `k ⊗[R] E`. That algebra is finite-dimensional
over `k` and formally unramified, hence reduced, hence semisimple; so every such module is
semisimple, and finite-dimensional semisimple modules in characteristic zero are determined by
their traces (`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`). The trace of `c ⊗ a` is
`c · tr_k (ρ a)`, so the traces of `ρ` determine those of the whole `k ⊗[R] E`-module.

## Main results

* `TauCeti.exists_linearEquiv_of_trace_eq`: representations of a formally unramified
  `R`-algebra of essentially finite type over a field of characteristic zero with the same traces
  are isomorphic.

## References

* J. S. Milne, *Complex Multiplication*, §1, proof of Proposition 1.21, p.15.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R E k V W : Type*} [CommRing R] [CommRing E] [Algebra R E] [Field k]
  [Algebra R k] [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]
  [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower R k W]

/-- **Representations of an unramified algebra are determined by their traces.** Let `E` be a
formally unramified algebra of essentially finite type over a commutative ring `R`, such as a
finite product of number fields over `ℚ`, and `k` a field of characteristic zero that is an
`R`-algebra. Two
representations `ρ`, `ρ'` of `E` on finite-dimensional `k`-vector spaces with
`tr_k (ρ a) = tr_k (ρ' a)` for every `a` are isomorphic: some `k`-linear equivalence intertwines
them. -/
theorem exists_linearEquiv_of_trace_eq [CharZero k] [Algebra.EssFiniteType R E]
    [Algebra.FormallyUnramified R E] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : E →ₐ[R] Module.End k V) (ρ' : E →ₐ[R] Module.End k W)
    (h : ∀ a, LinearMap.trace k V (ρ a) = LinearMap.trace k W (ρ' a)) :
    ∃ e : V ≃ₗ[k] W, ∀ a v, e (ρ a v) = ρ' a (e v) := by
  let : Module (k ⊗[R] E) V := Module.compHom V (AlgHom.liftEquiv R k E _ ρ).toRingHom
  let : Module (k ⊗[R] E) W := Module.compHom W (AlgHom.liftEquiv R k E _ ρ').toRingHom
  have hV (x : k ⊗[R] E) (v : V) : x • v = AlgHom.liftEquiv R k E _ ρ x v := rfl
  have hW (x : k ⊗[R] E) (w : W) : x • w = AlgHom.liftEquiv R k E _ ρ' x w := rfl
  have : IsScalarTower k (k ⊗[R] E) V := ⟨fun c x v ↦ by simp [hV]⟩
  have : IsScalarTower k (k ⊗[R] E) W := ⟨fun c x w ↦ by simp [hW]⟩
  have hlV (x : k ⊗[R] E) : Algebra.lsmul k k V x = AlgHom.liftEquiv R k E _ ρ x :=
    LinearMap.ext (hV x)
  have hlW (x : k ⊗[R] E) : Algebra.lsmul k k W x = AlgHom.liftEquiv R k E _ ρ' x :=
    LinearMap.ext (hW x)
  -- the traces of `ρ` determine those of the whole `k ⊗[R] E`-module
  have htr (x : k ⊗[R] E) :
      LinearMap.trace k V (AlgHom.liftEquiv R k E _ ρ x) =
        LinearMap.trace k W (AlgHom.liftEquiv R k E _ ρ' x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c a => simp [h]
    | add x y hx hy => simp [hx, hy]
  obtain ⟨e⟩ := IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq (k := k) (A := k ⊗[R] E) V W
    fun x ↦ by rw [hlV, hlW]; exact htr x
  refine ⟨e.restrictScalars k, fun a v ↦ ?_⟩
  have h1 : ρ a v = (1 ⊗ₜ a : k ⊗[R] E) • v := by simp [hV]
  have h2 : ρ' a (e v) = (1 ⊗ₜ a : k ⊗[R] E) • e v := by simp [hW]
  simp only [LinearEquiv.restrictScalars_apply]
  rw [h1, h2, map_smul]

end TauCeti
