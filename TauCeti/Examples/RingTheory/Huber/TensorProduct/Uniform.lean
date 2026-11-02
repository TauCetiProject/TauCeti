/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Uniform

/-!
# Checks for the uniform completed tensor product

Over a Tate base the uniform completed tensor ring is a complete Hausdorff uniform Tate ring.
Being reduced, it kills the image of every nilpotent of either factor, which the ordinary
completed tensor product need not do. The universal map evaluates products of the two
coprojections factorwise, and a zero factor makes the whole uniform completed tensor ring zero.
-/

public section

open TauCeti.Huber TauCeti.Huber.Pair

variable (A : Type*) {B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [IsTateRing A]
  (S : Pair B) (T : Pair C)

example : IsTateRing (Uniformization (CompletedTensor A B C)) := inferInstance
example : IsUniform (Uniformization (CompletedTensor A B C)) := inferInstance
example : CompleteSpace (Uniformization (CompletedTensor A B C)) := inferInstance
example : T2Space (Uniformization (CompletedTensor A B C)) := inferInstance

-- Nilpotents of either factor die in the uniform completed tensor product.
example {b : B} (hb : IsNilpotent b) : (uniformCompletedTensor.inl A S T).toRingHom b = 0 := by
  have := IsUniform.isReduced (A := Uniformization (CompletedTensor A B C))
  exact (hb.map _).eq_zero

example {c : C} (hc : IsNilpotent c) : (uniformCompletedTensor.inr A S T).toRingHom c = 0 := by
  have := IsUniform.isReduced (A := Uniformization (CompletedTensor A B C))
  exact (hc.map _).eq_zero

-- A zero factor gives the zero pair.
example [Subsingleton B] : Subsingleton (Uniformization (CompletedTensor A B C)) :=
  (uniformCompletedTensor.inl A S T).toRingHom.codomain_trivial

section Lift

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [CompleteSpace R] [T0Space R] [IsHuberRing R] [IsUniform R] {U : Pair R}
  {S T} (φ : Hom S U) (ψ : Hom T U)
  (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C))

-- The universal map evaluates a difference of products of coprojections factorwise.
example (b₁ b₂ : B) (c₁ c₂ : C) :
    (uniformCompletedTensor.lift A φ ψ h).toRingHom
        ((uniformCompletedTensor.inl A S T).toRingHom b₁ *
            (uniformCompletedTensor.inr A S T).toRingHom c₁ -
          (uniformCompletedTensor.inl A S T).toRingHom b₂ *
            (uniformCompletedTensor.inr A S T).toRingHom c₂) =
      φ.toRingHom b₁ * ψ.toRingHom c₁ - φ.toRingHom b₂ * ψ.toRingHom c₂ := by
  simp only [map_sub, map_mul, ← RingHom.comp_apply, ← Hom.toRingHom_comp,
    uniformCompletedTensor.lift_comp_inl, uniformCompletedTensor.lift_comp_inr]

-- The universal map is unique.
example (χ : Hom (S.uniformCompletedTensor A T) U)
    (hχB : χ.comp (uniformCompletedTensor.inl A S T) = φ)
    (hχC : χ.comp (uniformCompletedTensor.inr A S T) = ψ) :
    χ = uniformCompletedTensor.lift A φ ψ h :=
  uniformCompletedTensor.hom_ext A (by simp [hχB]) (by simp [hχC])

end Lift

-- Exchanging the factors twice is the identity.
example : (uniformCompletedTensor.comm A T S).comp (uniformCompletedTensor.comm A S T) =
    Hom.id _ :=
  uniformCompletedTensor.comm_comp_comm A S T
