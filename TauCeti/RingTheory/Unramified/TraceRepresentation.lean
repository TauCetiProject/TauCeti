/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import TauCeti.RingTheory.Semisimple.Trace.Basic

/-!
# Representations of an unramified algebra are determined by their traces

Let `E` be a finite-dimensional formally unramified `ℚ`-algebra, for instance a finite product of
number fields, and let `k` be a field of characteristic zero. A representation of `E` on a
finite-dimensional `k`-vector space `V` is a ring homomorphism `ρ : E → End_k V`. This file proves
that two such representations with the same trace, `tr_k (ρ a) = tr_k (ρ' a)` for every `a ∈ E`,
are isomorphic (`TauCeti.exists_linearEquiv_of_trace_eq`).

A representation of `E` over `k` is a module over `k ⊗[ℚ] E`. That algebra is finite-dimensional
over `k` and formally unramified, hence reduced, hence semisimple; so every such module is
semisimple, and finite-dimensional semisimple modules in characteristic zero are determined by
their traces (`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`). The trace of `c ⊗ a` is
`c · tr_k (ρ a)`, so the traces of `ρ` determine those of the whole `k ⊗[ℚ] E`-module.

## Main results

* `TauCeti.exists_linearEquiv_of_trace_eq`: representations of a finite-dimensional formally
  unramified `ℚ`-algebra over a field of characteristic zero with the same traces are isomorphic.

## References

* J. S. Milne, *Complex Multiplication*, §1, proof of Proposition 1.21, p.15.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {E k V W : Type*} [CommRing E] [Algebra ℚ E] [Field k] [CharZero k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The algebra map `k ⊗[ℚ] E → End_k V` of a representation `ρ` of `E`, sending `c ⊗ a` to
`c • ρ a`. -/
private noncomputable def tensorLift (ρ : E →+* Module.End k V) :
    k ⊗[ℚ] E →ₐ[k] Module.End k V :=
  letI : Algebra ℚ (Module.End k V) := Algebra.compHom _ (algebraMap ℚ k)
  haveI : IsScalarTower ℚ k (Module.End k V) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  AlgHom.liftEquiv ℚ k E _ ρ.toRatAlgHom

private theorem tensorLift_tmul (ρ : E →+* Module.End k V) (c : k) (a : E) :
    tensorLift ρ (c ⊗ₜ a) = c • ρ a := by
  simp [tensorLift, Algebra.smul_def]

/-- **Representations of an unramified algebra are determined by their traces.** Let `E` be a
finite-dimensional formally unramified `ℚ`-algebra, such as a finite product of number fields,
and `k` a field of characteristic zero. Two representations `ρ`, `ρ'` of `E` on
finite-dimensional `k`-vector spaces with `tr_k (ρ a) = tr_k (ρ' a)` for every `a` are
isomorphic: some `k`-linear equivalence intertwines them. -/
theorem exists_linearEquiv_of_trace_eq [Module.Finite ℚ E] [Algebra.FormallyUnramified ℚ E]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : E →+* Module.End k V) (ρ' : E →+* Module.End k W)
    (h : ∀ a, LinearMap.trace k V (ρ a) = LinearMap.trace k W (ρ' a)) :
    ∃ e : V ≃ₗ[k] W, ∀ a v, e (ρ a v) = ρ' a (e v) := by
  have : IsReduced (k ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field k _
  have : IsArtinianRing (k ⊗[ℚ] E) := IsArtinianRing.of_finite k _
  have : IsSemisimpleRing (k ⊗[ℚ] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let : Module (k ⊗[ℚ] E) V := Module.compHom V (tensorLift ρ : k ⊗[ℚ] E →+* Module.End k V)
  let : Module (k ⊗[ℚ] E) W := Module.compHom W (tensorLift ρ' : k ⊗[ℚ] E →+* Module.End k W)
  have hV (x : k ⊗[ℚ] E) (v : V) : x • v = tensorLift ρ x v := rfl
  have hW (x : k ⊗[ℚ] E) (w : W) : x • w = tensorLift ρ' x w := rfl
  have : IsScalarTower k (k ⊗[ℚ] E) V := ⟨fun c x v ↦ by simp [hV]⟩
  have : IsScalarTower k (k ⊗[ℚ] E) W := ⟨fun c x w ↦ by simp [hW]⟩
  -- the traces of `ρ` determine those of the whole `k ⊗[ℚ] E`-module
  have htr (x : k ⊗[ℚ] E) :
      LinearMap.trace k V (tensorLift ρ x) = LinearMap.trace k W (tensorLift ρ' x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c a => simp [tensorLift_tmul, h]
    | add x y hx hy => simp [hx, hy]
  obtain ⟨e⟩ := IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq (k := k) (A := k ⊗[ℚ] E) V W
    fun x ↦ htr x
  refine ⟨e.restrictScalars k, fun a v ↦ ?_⟩
  have h1 : ρ a v = (1 ⊗ₜ a : k ⊗[ℚ] E) • v := by simp [hV, tensorLift_tmul]
  have h2 : ρ' a (e v) = (1 ⊗ₜ a : k ⊗[ℚ] E) • e v := by simp [hW, tensorLift_tmul]
  simp only [LinearEquiv.restrictScalars_apply]
  rw [h1, h2, map_smul]

end TauCeti
