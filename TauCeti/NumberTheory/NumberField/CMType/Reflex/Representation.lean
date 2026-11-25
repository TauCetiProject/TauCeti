/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import TauCeti.RingTheory.Unramified.TraceRepresentation

/-!
# Representations with the type trace

Let `Φ` be a CM type on a commutative ring `E` with finitely many complex embeddings, with type
trace `typeTrace_Φ(a) = ∑_{φ ∈ Φ} φ(a)`. The reflex norm of `Φ` with values in a subfield
`k ⊆ ℂ` is built from a finite-dimensional representation `V` of `E` over `k` whose trace is the
type trace, `Tr_k(a | V) = typeTrace_Φ(a)`. Such a representation exists exactly when `k`
contains the reflex field `E*`, and it is then unique up to isomorphism (Milne, *Complex
Multiplication*, Proposition 1.21, p.15).

This file proves three parts of that statement.

* **Necessity.** If such a representation exists over `k`, then every type trace lies in `k`, so
  `E* ⊆ k` (`TauCeti.CMType.reflexField_le_of_trace_eq`).
* **Uniqueness.** When `E` is a finite-dimensional formally unramified `ℚ`-algebra, such as a
  finite product of CM fields, two representations with the type trace are isomorphic
  (`TauCeti.CMType.exists_linearEquiv_of_trace_eq_typeTrace`).
* **Existence over `ℂ`.** `E` acts on `ℂ^Φ` through the embeddings in `Φ`, with trace the type
  trace (`TauCeti.CMType.typeRepresentation`, `TauCeti.CMType.trace_typeRepresentation`).

Existence over a subfield `k` with `E* ⊆ k ⊊ ℂ`, the descent of `ℂ^Φ` to `k`, is not done here.

## Main definitions

* `TauCeti.CMType.typeRepresentation Φ`: the representation of `E` on `ℂ^Φ`,
  `a ↦ diag (φ a)_{φ ∈ Φ}`.

## Main results

* `TauCeti.CMType.reflexField_le_of_trace_eq`: a representation over `k` with the type trace
  forces `E* ⊆ k`.
* `TauCeti.CMType.exists_linearEquiv_of_trace_eq_typeTrace`: representations with the type trace
  are unique up to isomorphism; `TauCeti.CMType.exists_linearEquiv_of_trace_eq_typeTrace_pi`
  states it for a finite product of number fields.
* `TauCeti.CMType.trace_typeRepresentation`: `ℂ^Φ` has the type trace.

## References

* J. S. Milne, *Complex Multiplication*, §1, Proposition 1.21, p.15.
-/

public section

namespace TauCeti.CMType

variable {E : Type*} [CommRing E]

section Finite

variable [Finite (E →+* ℂ)]

/-- **Necessity of `E* ⊆ k`.** If `E` has a representation on a `k`-vector space whose trace is
the type trace of `Φ`, then the reflex field of `Φ` lies in `k`. -/
theorem reflexField_le_of_trace_eq (Φ : CMType E) (k : IntermediateField ℚ ℂ)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : E →+* Module.End k V)
    (h : ∀ a, (LinearMap.trace k V (ρ a) : ℂ) = Φ.typeTrace a) : Φ.reflexField ≤ k :=
  reflexField_le_iff.mpr fun a ↦ h a ▸ (LinearMap.trace k V (ρ a)).prop

/-- **Uniqueness of the representation with the type trace.** Let `E` be a finite-dimensional
formally unramified `ℚ`-algebra, such as a finite product of CM fields. Two representations of
`E` on finite-dimensional vector spaces over a subfield `k ⊆ ℂ`, both with trace the type trace of
`Φ`, are isomorphic. -/
theorem exists_linearEquiv_of_trace_eq_typeTrace [Algebra ℚ E] [Module.Finite ℚ E]
    [Algebra.FormallyUnramified ℚ E] (Φ : CMType E) (k : IntermediateField ℚ ℂ)
    {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : E →+* Module.End k V) (ρ' : E →+* Module.End k W)
    (h : ∀ a, (LinearMap.trace k V (ρ a) : ℂ) = Φ.typeTrace a)
    (h' : ∀ a, (LinearMap.trace k W (ρ' a) : ℂ) = Φ.typeTrace a) :
    ∃ e : V ≃ₗ[k] W, ∀ a v, e (ρ a v) = ρ' a (e v) :=
  exists_linearEquiv_of_trace_eq ρ ρ' fun a ↦ Subtype.ext ((h a).trans (h' a).symm)

/-- **Uniqueness of the representation with the type trace, for a product of number fields**,
such as a CM algebra `E = ∏ Fᵢ`: two representations of `E` over a subfield `k ⊆ ℂ`, both with
trace the type trace of `Φ`, are isomorphic. -/
theorem exists_linearEquiv_of_trace_eq_typeTrace_pi {ι : Type*} [Finite ι] (F : ι → Type*)
    [∀ i, Field (F i)] [∀ i, NumberField (F i)] (Φ : CMType (∀ i, F i))
    (k : IntermediateField ℚ ℂ) {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : (∀ i, F i) →+* Module.End k V) (ρ' : (∀ i, F i) →+* Module.End k W)
    (h : ∀ a, (LinearMap.trace k V (ρ a) : ℂ) = Φ.typeTrace a)
    (h' : ∀ a, (LinearMap.trace k W (ρ' a) : ℂ) = Φ.typeTrace a) :
    ∃ e : V ≃ₗ[k] W, ∀ a v, e (ρ a v) = ρ' a (e v) := by
  have := Fintype.ofFinite ι
  have (i : ι) := Algebra.FormallyUnramified.of_isSeparable ℚ (F i)
  exact exists_linearEquiv_of_trace_eq_typeTrace Φ k ρ ρ' h h'

end Finite

/-- **The representation of `E` on `ℂ^Φ`**: `a` acts by the diagonal matrix
`diag (φ a)_{φ ∈ Φ}`. Its trace is the type trace (`TauCeti.CMType.trace_typeRepresentation`). -/
noncomputable def typeRepresentation (Φ : CMType E) : E →+* Module.End ℂ (Φ → ℂ) :=
  (Algebra.lmul ℂ (Φ → ℂ)).toRingHom.comp (RingHom.pi fun φ : Φ ↦ (φ : E →+* ℂ))

@[simp]
theorem typeRepresentation_apply (Φ : CMType E) (a : E) (v : Φ → ℂ) (φ : Φ) :
    Φ.typeRepresentation a v φ = (φ : E →+* ℂ) a * v φ :=
  (rfl)

/-- **`ℂ^Φ` has the type trace**: the trace of `a` on `ℂ^Φ` is `∑_{φ ∈ Φ} φ a`. -/
@[simp]
theorem trace_typeRepresentation [Finite (E →+* ℂ)] (Φ : CMType E) (a : E) :
    LinearMap.trace ℂ (Φ → ℂ) (Φ.typeRepresentation a) = Φ.typeTrace a := by
  classical
  have := Fintype.ofFinite (E →+* ℂ)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ Φ), typeTrace_eq_sum,
    ← Finset.sum_subtype_eq_sum_filter]
  simp [Matrix.trace]

end TauCeti.CMType
