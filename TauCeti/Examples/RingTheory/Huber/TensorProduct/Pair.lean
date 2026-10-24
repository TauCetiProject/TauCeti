/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Checks for the completed tensor product of Huber pairs

These checks use only the public interface. The plus ring of `B ⊗̂_A C` contains the images of
`b ⊗ c` for `b ∈ B⁺` and `c ∈ C⁺`, every nilpotent and every idempotent element, and is the
whole ring when one factor is zero. The pair-level extension restricts to the prescribed maps.
-/

public section

open TensorProduct TauCeti.Huber

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  (T : Pair B) (U : Pair C)

-- The image of `b ⊗ c` lies in the plus ring when `b ∈ B⁺` and `c ∈ C⁺`.
example {b : B} {c : C} (hb : b ∈ T.plus) (hc : c ∈ U.plus) :
    CompletedTensor.toCompletion A B C (b ⊗ₜ[A] c) ∈ (Pair.completedTensor A T U).plus :=
  Pair.toCompletion_mem_completedTensor_plus (Pair.tmul_mem_tensorPlus hb hc)

-- Every nilpotent element of the completed tensor ring lies in its plus ring.
example {x : CompletedTensor A B C} (hx : IsNilpotent x) :
    x ∈ (Pair.completedTensor A T U).plus := by
  obtain ⟨n, hn⟩ := hx
  have hint := (Pair.completedTensor A T U).isRingOfIntegralElements.isIntegrallyClosedIn
  refine Subring.isIntegrallyClosedIn_iff.mp hint ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [pow_zero] at hn
    exact (subsingleton_of_zero_eq_one hn.symm).elim x 0 ▸ isIntegral_zero
  · exact IsIntegral.of_pow hpos (hn ▸ isIntegral_zero)

-- Every idempotent element of the completed tensor ring lies in its plus ring.
example {e : CompletedTensor A B C} (he : IsIdempotentElem e) :
    e ∈ (Pair.completedTensor A T U).plus := by
  have hint := (Pair.completedTensor A T U).isRingOfIntegralElements.isIntegrallyClosedIn
  refine Subring.isIntegrallyClosedIn_iff.mp hint
    ⟨Polynomial.X ^ 2 - Polynomial.X,
      Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [Polynomial.eval₂_sub, sq, he.eq]

-- With a zero right factor the plus ring is the whole completed tensor ring.
example [Subsingleton C] : (Pair.completedTensor A T U).plus = ⊤ := by
  have := (CompletedTensor.inr A B C).codomain_trivial
  exact eq_top_iff.mpr fun x _ ↦ Subsingleton.elim 1 x ▸ one_mem _

section Lift

variable {A B C T U} {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsHuberRing R] [CompleteSpace R] [T0Space R] {V : Pair R}

-- The pair-level extension computes on pure tensors.
example (φ : Pair.Hom T V) (ψ : Pair.Hom U V)
    (h : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C)) (b : B) (c : C) :
    (Pair.completedTensor.lift φ ψ h).toRingHom (CompletedTensor.toCompletion A B C (b ⊗ₜ c)) =
      φ.toRingHom b * ψ.toRingHom c := by
  simp

end Lift
