/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra

/-!
# Transport of A-infinity algebras along linear equivalences

An `A∞` structure on a graded module `A` transports along any linear equivalence `e : A ≃ B`:
the target is graded by the images of the pieces of `A`, as in `TauCeti.InternalGrading.map`, and
its operations are `mₙ(b₁, …, bₙ) = e (mₙ(e⁻¹ b₁, …, e⁻¹ bₙ))`.  The Stasheff identities
transport because they are natural in linear maps intertwining the operations,
`TauCeti.AInfinity.map_stasheffSum`.

This is how an `A∞` structure given on one model of a graded module is moved to another, for
instance from an algebra `A` to the total module of morphisms of the one-object graded linear
quiver with endomorphisms `A`.

## Main definitions

* `TauCeti.AInfinityAlgebra.map`: the transport of an `A∞` algebra along a linear equivalence.

## Main results

* `TauCeti.AInfinityAlgebra.map_grading` and `TauCeti.AInfinityAlgebra.map_m_apply`: the grading
  and the operations of the transported algebra.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

universe uR uA uB

namespace TauCeti

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]

namespace AInfinityAlgebra

variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The **transport** of an `A∞` algebra along a linear equivalence `e : A ≃ B`.  The degree-`p`
piece of `B` is the image of the degree-`p` piece of `A`, and the operations are
`mₙ(b₁, …, bₙ) = e (mₙ(e⁻¹ b₁, …, e⁻¹ bₙ))`. -/
noncomputable def map (𝒜 : AInfinityAlgebra R A) (e : A ≃ₗ[R] B) : AInfinityAlgebra R B :=
  ofStasheff (𝒜.grading.map e)
    (fun n ↦ e.toLinearMap.compMultilinearMap ((𝒜.m n).compLinearMap fun _ ↦ e.symm.toLinearMap))
    (by simp)
    (fun n hn ↦ MultilinearMap.isHomogeneous_def.2 fun d x hx ↦ by
      simpa using (𝒜.m_degree n hn).map_mem d (fun i ↦ e.symm (x i))
        fun i ↦ (InternalGrading.mem_map_piece_iff _ _ _ _).1 (hx i))
    _ (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun n hn d x hx ↦ e.symm.injective <| by
      rw [← LinearEquiv.coe_coe, AInfinity.map_stasheffSum _ d x e.symm.toLinearMap 𝒜.m
        (fun k y ↦ by simp), map_zero]
      exact 𝒜.stasheff n hn d _ fun i hi ↦ (InternalGrading.mem_map_piece_iff _ _ _ _).1 (hx i hi))

variable (𝒜 : AInfinityAlgebra R A) (e : A ≃ₗ[R] B)

/-- The grading of a transported `A∞` algebra is the transported grading. -/
@[simp]
theorem map_grading : (𝒜.map e).grading = 𝒜.grading.map e := by
  rw [map, ofStasheff_grading]

/-- The operations of a transported `A∞` algebra are conjugated by the linear equivalence. -/
@[simp]
theorem map_m_apply (n : ℕ) (x : Fin n → B) :
    (𝒜.map e).m n x = e (𝒜.m n fun i ↦ e.symm (x i)) := by
  simp [map, ofStasheff_m]

end AInfinityAlgebra

end TauCeti
