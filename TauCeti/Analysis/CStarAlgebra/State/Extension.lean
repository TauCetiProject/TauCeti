/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Extension of states and state characterizations of spectrum, order and norm

Every state of a unital C⋆-subalgebra extends to a state of the ambient C⋆-algebra, so Gelfand
characters on commutative C⋆-subalgebras `StarAlgebra.elemental ℂ a` extend to states on `A`.

* `TauCeti.surjOn_pullbackFunctional_stateSpace`: along an injective unital star homomorphism
  `f : A → B`, restriction of states `pullbackFunctional A f` maps the state space of `B` onto the
  state space of `A`.
* `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`: every state of a closed star
  subalgebra `S` of `A` (containing the unit of `A`) is the restriction of a state of `A`.
* `TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum`: for any normal element `x` and
  `z ∈ spectrum ℂ x`, some state `φ ∈ stateSpace A` satisfies `φ x = z`.
* `TauCeti.exists_mem_stateSpace_apply_eq_norm` and `TauCeti.norm_le_of_forall_mem_stateSpace`:
  every nonnegative element of a nontrivial unital C⋆-algebra attains its norm at a state, so its
  norm is bounded by any nonnegative bound holding across `stateSpace A`.
* `TauCeti.nonneg_iff_forall_mem_stateSpace`: an element `a` of a unital C⋆-algebra is nonnegative
  if and only if `0 ≤ φ a` for every state `φ ∈ stateSpace A`.

The proof takes a norm-preserving Hahn–Banach extension of the state along `f`, by
`LinearIsometry.exists_extension_norm_eq`, and reads off that it is a state from its value `1` at
the unit, by `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The extension applies because
an injective star homomorphism of C⋆-algebras is isometric. An extension of a state need not be
pure, multiplicative or unique.

## References

* B. Blackadar, *Operator Algebras*, II.6.3.1 and II.6.3.3.
-/

public section

open Set WeakDual
open scoped ComplexOrder ComplexStarModule CStarAlgebra

namespace TauCeti

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Extension of states.** Along an injective unital star homomorphism `f : A → B` of C⋆-algebras,
every state of `A` is the restriction `φ ∘ f` of a state `φ` of `B`. -/
theorem surjOn_pullbackFunctional_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
  intro φ hφ
  let i : A →ₗᵢ[ℂ] B := ⟨(f : A →ₗ[ℂ] B), NonUnitalStarAlgHom.norm_map f hf⟩
  obtain ⟨ψ, hψ, hnorm⟩ := i.exists_extension_norm_eq (toStrongDual φ)
  have hrestrict (a : A) : ψ (f a) = φ a := DFunLike.congr_fun hψ a
  have h1 : ψ 1 = 1 := by
    simpa [map_one f] using (hrestrict 1).trans (map_one_of_mem_stateSpace hφ)
  refine ⟨StrongDual.toWeakDual ψ, mem_stateSpace_iff_norm_eq_one_and_map_one.2
    ⟨hnorm.trans (norm_toStrongDual_of_mem_stateSpace hφ), by simpa⟩,
    DFunLike.ext _ _ fun a => by simpa using hrestrict a⟩

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

namespace TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For every normal element `x` of a unital C⋆-algebra and every `z ∈ spectrum ℂ x`, there is a
state `φ ∈ stateSpace A` with `φ x = z`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum {x : A} [IsStarNormal x] {z : ℂ}
    (hz : z ∈ spectrum ℂ x) :
    ∃ φ ∈ stateSpace A, φ x = z := by
  let S := StarAlgebra.elemental ℂ x
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ x
  obtain ⟨p, hp⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum x).2 ⟨z, hz⟩
  have hp_state : (p : WeakDual ℂ S) ∈ stateSpace S :=
    mem_stateSpace_iff_map_one.2 ⟨fun _ hy => map_nonneg p hy, map_one p⟩
  obtain ⟨φ, hφ, hφ_eq⟩ := S.exists_mem_stateSpace_forall_apply_coe_eq hp_state
  refine ⟨φ, hφ, (hφ_eq ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩).trans ?_⟩
  exact congrArg Subtype.val hp

/-- For every nonnegative element `a` of a nontrivial unital C⋆-algebra, there is a state `φ`
attaining its norm: `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  have : IsStarNormal a := ha.isSelfAdjoint.isStarNormal
  obtain ⟨z, hz, hrad⟩ := spectrum.exists_nnNorm_eq_spectralRadius a
  have hnorm : ‖z‖ = ‖a‖ := by
    simpa [ha.isSelfAdjoint.spectralRadius_eq_nnNorm] using congrArg ENNReal.toReal hrad
  obtain ⟨hz_re, hz_im⟩ := Complex.nonneg_iff.mp (spectrum_nonneg_of_nonneg ha hz)
  have hzeq : z = (‖a‖ : ℂ) := by
    have hz_real : z = (z.re : ℂ) := Complex.ext rfl hz_im.symm
    rw [← hnorm, hz_real, Complex.norm_real, Real.norm_of_nonneg hz_re]
  exact exists_mem_stateSpace_apply_eq_of_mem_spectrum (hzeq ▸ hz)

/-- A nonnegative element `a` of a unital C⋆-algebra (including the zero algebra) has norm at most
`c ≥ 0` whenever `‖φ a‖ ≤ c` for every state `φ`. -/
theorem norm_le_of_forall_mem_stateSpace {a : A} (ha : 0 ≤ a) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ φ ∈ stateSpace A, ‖φ a‖ ≤ c) : ‖a‖ ≤ c := by
  rcases subsingleton_or_nontrivial A with hsub | _
  · simpa [Subsingleton.elim a 0] using hc
  · obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_eq_norm ha
    have hle := h φ hφ
    rwa [hφa, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a)] at hle

/-- A self-adjoint element that is nonnegative under every state is nonnegative. -/
private theorem nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace {s : A} (hs : IsSelfAdjoint s)
    (h : ∀ φ ∈ stateSpace A, 0 ≤ φ s) : 0 ≤ s := by
  have : IsStarNormal s := hs.isStarNormal
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) s hs]
  intro r hr
  have hrc : (r : ℂ) ∈ spectrum ℂ s := (spectrum.algebraMap_mem_iff ℂ).mpr hr
  obtain ⟨φ, hφ, hφs⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum hrc
  exact RCLike.ofReal_nonneg.mp (hφs ▸ h φ hφ)

/-- An element `a` of a unital C⋆-algebra is nonnegative if and only if `0 ≤ φ a` for every state
`φ ∈ stateSpace A`. -/
theorem nonneg_iff_forall_mem_stateSpace {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  have hstar (φ : WeakDual ℂ A) (hφ : φ ∈ stateSpace A) : φ (star a) = φ a := by
    let ω : A →ₚ[ℂ] ℂ := .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) fun _ => map_nonneg_of_mem_stateSpace hφ
    have hω : ω (star a) = star (ω a) := map_star ω a
    exact hω.trans (h φ hφ).isSelfAdjoint.star_eq
  have him_zero (φ : WeakDual ℂ A) (hφ : φ ∈ stateSpace A) : φ (ℑ a : A) = 0 := by
    rw [← toStrongDual_apply, imaginaryPart_apply_coe, map_smul,
      (toStrongDual φ).map_smul_of_tower, map_sub]
    simp [hstar φ hφ]
  have him_nonneg : 0 ≤ (ℑ a : A) :=
    nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace (ℑ a).2 fun φ hφ => by simp [him_zero φ hφ]
  have him_nonpos : 0 ≤ -(ℑ a : A) :=
    nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace (ℑ a).2.neg fun φ hφ => by
      rw [← toStrongDual_apply, map_neg, toStrongDual_apply, him_zero φ hφ, neg_zero]
  have him_eq : ℑ a = 0 := Subtype.ext <| le_antisymm (neg_nonneg.mp him_nonpos) him_nonneg
  have hre_nonneg : 0 ≤ (ℜ a : A) :=
    nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace (ℜ a).2 fun φ hφ => by
      have ha_eq : (ℜ a : A) = a := by simpa [him_eq] using realPart_add_I_smul_imaginaryPart a
      rw [ha_eq]
      exact h φ hφ
  exact nonneg_iff_realPart_imaginaryPart.mpr ⟨hre_nonneg, him_eq⟩

end TauCeti
