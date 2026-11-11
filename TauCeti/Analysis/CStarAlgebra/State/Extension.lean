/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Extension of states

Every state of a unital C⋆-subalgebra extends to a state of the ambient C⋆-algebra.

* `TauCeti.surjOn_pullbackFunctional_stateSpace`: along an injective unital star homomorphism
  `f : A → B`, restriction of states `pullbackFunctional A f` maps the state space of `B` onto the
  state space of `A`.
* `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`: every state of a closed star
  subalgebra `S` of `A` (containing the unit of `A`) is the restriction of a state of `A`.

The proof takes a norm-preserving Hahn–Banach extension of the state, transported to the range of
`f`, and reads off that it is a state from its value `1` at the unit, by
`TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The range carries the norm of `A` because
an injective star homomorphism of C⋆-algebras is isometric. An extension of a state need not be
pure, multiplicative or unique.

## References

* B. Blackadar, *Operator Algebras*, II.6.3.1.
-/

public section

open Set WeakDual

namespace TauCeti

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Extension of states.** Along an injective unital star homomorphism `f : A → B` of C⋆-algebras,
every state of `A` is the restriction `φ ∘ f` of a state `φ` of `B`. -/
theorem surjOn_pullbackFunctional_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
  intro φ hφ
  let fₗ : A →ₗ[ℂ] B := f
  let e : A ≃ₗ[ℂ] LinearMap.range fₗ := LinearEquiv.ofInjective fₗ hf
  have hfe (x : LinearMap.range fₗ) : f (e.symm x) = x :=
    congrArg Subtype.val (e.apply_symm_apply x)
  -- the state `φ`, read on the range of `f`, which carries the norm of `B`
  let g : StrongDual ℂ (LinearMap.range fₗ) :=
    ((toStrongDual φ : A →ₗ[ℂ] ℂ) ∘ₗ e.symm.toLinearMap).mkContinuous 1 fun x => by
      simpa [← hfe x, NonUnitalStarAlgHom.norm_map f hf] using
        norm_apply_le_of_mem_stateSpace hφ (e.symm x)
  obtain ⟨ψ, hψ, hnorm⟩ := exists_extension_norm_eq (LinearMap.range fₗ) g
  have hrestrict (a : A) : ψ (f a) = φ a := by
    have he : e.symm ⟨f a, a, rfl⟩ = a := e.symm_apply_eq.2 rfl
    simpa [g, he] using hψ ⟨f a, a, rfl⟩
  have h1 : ψ 1 = 1 := by
    simpa [map_one f] using (hrestrict 1).trans (map_one_of_mem_stateSpace hφ)
  have : Nontrivial B := ⟨⟨1, 0, fun h => by simp [h] at h1⟩⟩
  refine ⟨StrongDual.toWeakDual ψ, mem_stateSpace_iff_norm_eq_one_and_map_one.2 ⟨?_, by simpa⟩,
    DFunLike.ext _ _ fun a => by simpa using hrestrict a⟩
  refine le_antisymm ?_ ?_
  · simpa [hnorm] using LinearMap.mkContinuous_norm_le _ zero_le_one _
  · simpa [h1] using ψ.le_opNorm 1

end TauCeti

namespace StarSubalgebra

open TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Extension of states from a C⋆-subalgebra.** Every state of a closed star subalgebra `S` of a
unital C⋆-algebra `A`, containing the unit of `A`, is the restriction of a state of `A`. -/
theorem exists_mem_stateSpace_forall_apply_coe_eq (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ stateSpace S) :
    ∃ ψ ∈ stateSpace A, ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ := surjOn_pullbackFunctional_stateSpace S.subtype Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => (pullbackFunctional_apply S.subtype ψ s).symm⟩

end StarSubalgebra
