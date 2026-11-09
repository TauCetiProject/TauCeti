/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.FiniteAlgebra
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Checks for completed finite base change

The unit and split computations fix the scalar map and the order of the two sheets.
The plus-ring check excludes a coefficient outside the chosen plus ring, even if it
is power-bounded. A final check applies the finite projective comparison to finite
étale algebras without assuming projectivity separately.
-/

public section

open TensorProduct Algebra.TensorProduct TauCeti.Huber

namespace TauCeti.Examples.FiniteAlgebraBaseChange

section Unit

variable (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsHuberRing A] [CompleteSpace A] [T2Space A]

/-- The natural topology on the unit tensor used in the plus-ring check. -/
noncomputable local instance unitTensorTopology : TopologicalSpace (A ⊗[A] A) :=
  moduleTopology A (A ⊗[A] A)
local instance : IsTopologicalRing (A ⊗[A] A) := IsModuleTopology.isTopologicalRing A _
local instance : IsHuberRing (A ⊗[A] A) := IsHuberRing.of_isModuleTopology (A := A)

local instance : IsAdicHom (algebraMap A A) := by
  simpa using (IsAdicHom.id (A := A))

/-- *baseChangeIso_identity*: the inverse comparison followed by the unit map
multiplies the specified coefficients. -/
example (c a : A) :
    Algebra.TensorProduct.rid A A A
      ((Pair.finiteAlgebra.baseChangeEquiv A A A).symm
        (CompletedTensor.toCompletion A A A (c ⊗ₜ[A] a))) = a * c := by
  simp

/-- *baseChangeIso_proper_plus*: the comparison cannot turn a coefficient outside
the chosen plus ring into an integral element. -/
example (S : Pair A) {a : A} (ha : a ∉ S.plus) :
    Pair.finiteAlgebra.baseChangeEquiv A A A (a ⊗ₜ[A] 1) ∉
      (S.completedTensor A (S.finiteAlgebra A)).plus := by
  intro h
  rw [← Pair.finiteAlgebra.map_plus_baseChangeEquiv S S (Pair.Hom.id S) (by simp)] at h
  obtain ⟨x, hx, he⟩ := h
  have he' : x = a ⊗ₜ[A] 1 := (Pair.finiteAlgebra.baseChangeEquiv A A A).injective he
  subst x
  let f := Pair.finiteAlgebra.lift (Pair.Hom.id S) (by simp)
    (Algebra.TensorProduct.lid A A).toAlgHom
  have hm := f.map_mem_plus (a ⊗ₜ[A] 1) hx
  apply ha
  simpa [f, Algebra.smul_def] using hm

end Unit

section Split

local instance : IsAdicHom (algebraMap ℤ ℤ) := by
  simpa using (IsAdicHom.id (A := ℤ))

local instance : IsAdicHom (algebraMap ℤ (ℤ × ℤ)) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

/-- *baseChangeIso_split*: the two ordered idempotents give the two ordered sheets. -/
example (c₁ c₂ : ℤ) :
    (Algebra.TensorProduct.prodRight ℤ ℤ ℤ ℤ ℤ
      ((Pair.finiteAlgebra.baseChangeEquiv ℤ ℤ (ℤ × ℤ)).symm
        (CompletedTensor.toCompletion ℤ ℤ (ℤ × ℤ)
          (c₁ ⊗ₜ[ℤ] (1, 0) + c₂ ⊗ₜ[ℤ] (0, 1))))).map
        (Algebra.TensorProduct.rid ℤ ℤ ℤ) (Algebra.TensorProduct.rid ℤ ℤ ℤ) = (c₁, c₂) := by
  rw [Pair.finiteAlgebra.baseChangeEquiv_symm_toCompletion]
  simp only [map_add, Algebra.TensorProduct.prodRight_tmul]
  simp

end Split

section Etale

variable (A C B : Type*) [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T2Space C]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]
  [Module.Finite A B] [Algebra.Etale A B]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)]

-- Finite étaleness supplies all the algebraic hypotheses of the comparison.
example : Nonempty (C ⊗[A] B ≃+* CompletedTensor A C B) := by
  have : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  exact ⟨Pair.finiteAlgebra.baseChangeEquiv A C B⟩

end Etale

end TauCeti.Examples.FiniteAlgebraBaseChange
