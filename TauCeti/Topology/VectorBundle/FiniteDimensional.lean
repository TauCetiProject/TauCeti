/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Finite-rank vector bundles: products of fibres and maps between fibres

For a vector bundle `E` with finite-dimensional model fibre `F` and finitely many base points
`x : ι → B`, the product `Π i, E (x i)` of the fibres is finite-dimensional
(`VectorBundle.finiteDimensional_pi`), of dimension `Nat.card ι * finrank R F`
(`VectorBundle.finrank_pi`).

A bijective linear map between the fibres `E x → E' x` of two vector bundles forces their model
fibres to have the same rank (`TauCeti.finrank_eq_of_bijective_fiber`), and if the zero map
`E x → E' x` is bijective, both model fibres are zero
(`TauCeti.subsingleton_of_bijective_zero_fiber`).
-/

public section

namespace VectorBundle

open Bundle Module

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]
  [FiniteDimensional R F]

include F

/-- The product of the fibres of a finite-rank vector bundle at finitely many points is
finite-dimensional. -/
protected theorem finiteDimensional_pi {ι : Type*} [Finite ι] (x : ι → B) :
    FiniteDimensional R (Π i, E (x i)) :=
  have (i : ι) : FiniteDimensional R (E (x i)) := VectorBundle.finiteDimensional R F E (x i)
  inferInstance

/-- The product of the fibres of a finite-rank vector bundle at finitely many points has dimension
the number of points times the rank. -/
protected theorem finrank_pi {ι : Type*} [Finite ι] (x : ι → B) :
    finrank R (Π i, E (x i)) = Nat.card ι * finrank R F := by
  have := Fintype.ofFinite ι
  have (i : ι) : FiniteDimensional R (E (x i)) := VectorBundle.finiteDimensional R F E (x i)
  simp [Module.finrank_pi_fintype, VectorBundle.finrank_eq R F E, Nat.card_eq_fintype_card]

end VectorBundle

namespace TauCeti

open Bundle Module

variable {R B F F' : Type*} {E E' : B → Type*} [NontriviallyNormedField R] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace (TotalSpace F E)]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]
  [NormedAddCommGroup F'] [NormedSpace R F'] [TopologicalSpace (TotalSpace F' E')]
  [(x : B) → TopologicalSpace (E' x)] [FiberBundle F' E']
  [(x : B) → AddCommGroup (E' x)] [(x : B) → Module R (E' x)] [VectorBundle R F' E']

include F F'

/-- A bijective linear map between the fibres `E x → E' x` of two vector bundles forces the model
fibres to have the same rank. -/
theorem finrank_eq_of_bijective_fiber {x : B} {f : E x →ₗ[R] E' x} (hf : Function.Bijective f) :
    finrank R F = finrank R F' := by
  rw [← VectorBundle.finrank_eq R F E x, ← VectorBundle.finrank_eq R F' E' x]
  exact (LinearEquiv.ofBijective f hf).finrank_eq

/-- If the zero map between the fibres `E x → E' x` of two vector bundles is bijective, both
fibres are zero, and so are the model fibres. -/
theorem subsingleton_of_bijective_zero_fiber (x : B)
    (h : Function.Bijective (0 : E x →ₗ[R] E' x)) : Subsingleton F ∧ Subsingleton F' := by
  have hE : Subsingleton (E x) := ⟨fun u v ↦ h.1 (by simp)⟩
  have hE' : Subsingleton (E' x) := ⟨fun u v ↦ by
    obtain ⟨u', rfl⟩ := h.2 u
    obtain ⟨v', rfl⟩ := h.2 v
    simp⟩
  exact ⟨(VectorBundle.continuousLinearEquivAt R F E x).symm.toEquiv.subsingleton,
    (VectorBundle.continuousLinearEquivAt R F' E' x).symm.toEquiv.subsingleton⟩

end TauCeti
