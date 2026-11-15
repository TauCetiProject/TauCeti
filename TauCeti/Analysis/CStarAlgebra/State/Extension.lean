/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
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
* `TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum`: for any element `x` of a unital
  C⋆-algebra and `z ∈ spectrum ℂ x`, some state `φ ∈ stateSpace A` satisfies `φ x = z`.
* `TauCeti.exists_mem_stateSpace_apply_eq_norm` and `TauCeti.norm_le_of_forall_mem_stateSpace`:
  every nonnegative element of a nontrivial (possibly nonunital) C⋆-algebra attains its norm at a
  state, and every normal element has norm bounded by any nonnegative bound holding across
  `stateSpace A`.
* `TauCeti.nonneg_iff_forall_mem_stateSpace`: an element `a` of a (possibly nonunital) C⋆-algebra
  is nonnegative if and only if `0 ≤ φ a` for every state `φ ∈ stateSpace A`.

The proof takes a norm-preserving Hahn–Banach extension of the state along `f`, by
`LinearIsometry.exists_extension_norm_eq`, and reads off that it is a state from its value `1` at
the unit, by `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The extension applies because
an injective star homomorphism of C⋆-algebras is isometric. An extension of a state need not be
pure, multiplicative or unique.

## References

* B. Blackadar, *Operator Algebras*, II.6.3.1 and II.6.3.3.
-/

public section

open Set Unitization WeakDual
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

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum_normal {x : A} [IsStarNormal x]
    {z : ℂ} (hz : z ∈ spectrum ℂ x) :
    ∃ φ ∈ stateSpace A, φ x = z := by
  let S := StarAlgebra.elemental ℂ x
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ x
  obtain ⟨p, hp⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum x).2 ⟨z, hz⟩
  have hp_state : (p : WeakDual ℂ S) ∈ stateSpace S :=
    mem_stateSpace_iff_map_one.2 ⟨fun _ hy => map_nonneg p hy, map_one p⟩
  obtain ⟨φ, hφ, hφ_eq⟩ := S.exists_mem_stateSpace_forall_apply_coe_eq hp_state
  refine ⟨φ, hφ, (hφ_eq ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩).trans ?_⟩
  exact congrArg Subtype.val hp

/-- For every element `x` of a unital C⋆-algebra and every `z ∈ spectrum ℂ x`, there is a state
`φ ∈ stateSpace A` with `φ x = z`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum {x : A} {z : ℂ}
    (hz : z ∈ spectrum ℂ x) :
    ∃ φ ∈ stateSpace A, φ x = z := by
  let y : A := algebraMap ℂ A z - x
  have hy : ¬ IsUnit y := spectrum.mem_iff.mp hz
  have hnot : ¬ IsUnit (star y * y) ∨ ¬ IsUnit (y * star y) := by
    rw [← not_and_or]
    rintro ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩
    refine hy (isUnit_iff_exists_and_exists.mpr ⟨⟨star y * ↑u₂⁻¹, ?_⟩, ⟨↑u₁⁻¹ * star y, ?_⟩⟩)
    · rw [← mul_assoc, ← hu₂, Units.mul_inv]
    · rw [mul_assoc, ← hu₁, Units.inv_mul]
  suffices ∃ φ ∈ stateSpace A, φ y = 0 by
    obtain ⟨φ, hφ, hφy⟩ := this
    refine ⟨φ, hφ, ?_⟩
    have hsub : z - φ x = 0 := by
      simpa [y, Algebra.algebraMap_eq_smul_one, map_one_of_mem_stateSpace hφ] using
        (toStrongDual_apply φ y).symm.trans hφy
    exact (sub_eq_zero.mp hsub).symm
  rcases hnot with h₁ | h₂
  · have : IsStarNormal (star y * y) := (IsSelfAdjoint.star_mul_self y).isStarNormal
    have hmem : (0 : ℂ) ∈ spectrum ℂ (star y * y) := by simpa [spectrum.mem_iff] using h₁
    obtain ⟨φ, hφ, hφ0⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum_normal hmem
    let ω : A →ₚ[ℂ] ℂ := .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) fun _ => map_nonneg_of_mem_stateSpace hφ
    have h0 : ω (star y * y) = 0 := hφ0
    have hωy : ω y = 0 := by simpa [h0] using PositiveLinearMap.norm_map_star_mul_le ω 1 y
    exact ⟨φ, hφ, hωy⟩
  · have : IsStarNormal (y * star y) := (IsSelfAdjoint.mul_star_self y).isStarNormal
    have hmem : (0 : ℂ) ∈ spectrum ℂ (y * star y) := by simpa [spectrum.mem_iff] using h₂
    obtain ⟨φ, hφ, hφ0⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum_normal hmem
    let ω : A →ₚ[ℂ] ℂ := .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) fun _ => map_nonneg_of_mem_stateSpace hφ
    have h0 : ω (y * star y) = 0 := hφ0
    have hωy : ω y = 0 := by simpa [h0] using PositiveLinearMap.norm_map_mul_star_le ω y 1
    exact ⟨φ, hφ, hωy⟩

private theorem nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace {s : A} (hs : IsSelfAdjoint s)
    (h : ∀ φ ∈ stateSpace A, 0 ≤ φ s) : 0 ≤ s := by
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) s hs]
  intro r hr
  have hrc : (r : ℂ) ∈ spectrum ℂ s := (spectrum.algebraMap_mem_iff ℂ).mpr hr
  obtain ⟨φ, hφ, hφs⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum hrc
  exact RCLike.ofReal_nonneg.mp (hφs ▸ h φ hφ)

private theorem nonneg_iff_forall_mem_stateSpace_unital {a : A} :
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

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Pulling back a state of `A⁺¹` that attains the norm at a nonzero element `a : A` yields a
state of `A`. -/
private theorem pullback_inr_mem_stateSpace_of_norm_eq {a : A} (ha : a ≠ 0) {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) (hnorm : ‖ψ (a : A⁺¹)‖ = ‖a‖) :
    pullbackFunctional A (inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A := by
  let φ := pullbackFunctional A (inrNonUnitalStarAlgHom ℂ A) ψ
  refine mem_stateSpace_iff.mpr
    ⟨fun x hx => by simpa [φ] using map_nonneg_of_mem_stateSpace hψ hx.inr, le_antisymm ?_ ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa [φ, Unitization.norm_inr] using norm_apply_le_of_mem_stateSpace hψ (x : A⁺¹)
  · have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hle : ‖a‖ ≤ ‖toStrongDual φ‖ * ‖a‖ := by
      simpa [φ, hnorm] using (toStrongDual φ).le_opNorm a
    exact (le_mul_iff_one_le_left ha_pos).mp hle

private theorem exists_mem_stateSpace_apply_eq_norm_of_ne_zero {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  have hmem : (‖(a : A⁺¹)‖ : ℂ) ∈ spectrum ℂ (a : A⁺¹) :=
    (spectrum.algebraMap_mem_iff ℂ).mpr
      (_root_.CStarAlgebra.norm_mem_spectrum_of_nonneg (a : A⁺¹) ha.inr)
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum hmem
  rw [Unitization.norm_inr] at hψa
  have hnorm : ‖ψ (a : A⁺¹)‖ = ‖a‖ := by
    rw [hψa, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a)]
  exact ⟨pullbackFunctional A (inrNonUnitalStarAlgHom ℂ A) ψ,
    pullback_inr_mem_stateSpace_of_norm_eq ha0 hψ hnorm, by simpa using hψa⟩

/-- For every nonnegative element `a` of a nontrivial C⋆-algebra, there is a state `φ` attaining
its norm: `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨b, hb⟩ := exists_ne (0 : A)
    obtain ⟨φ, hφ, _⟩ := exists_mem_stateSpace_apply_eq_norm_of_ne_zero (star_mul_self_nonneg b)
      (star_mul_self_eq_zero.not.mpr hb)
    exact ⟨φ, hφ, by simp [← toStrongDual_apply]⟩
  · exact exists_mem_stateSpace_apply_eq_norm_of_ne_zero ha ha0

/-- A normal element `a` of a C⋆-algebra has norm at most `c ≥ 0` whenever `‖φ a‖ ≤ c` for every
state `φ`. -/
theorem norm_le_of_forall_mem_stateSpace {a : A} [IsStarNormal a] {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ φ ∈ stateSpace A, ‖φ a‖ ≤ c) : ‖a‖ ≤ c := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simpa using hc
  · obtain ⟨z, hz, hrad⟩ := spectrum.exists_nnNorm_eq_spectralRadius (a : A⁺¹)
    rw [IsStarNormal.spectralRadius_eq_nnNorm (a : A⁺¹)] at hrad
    have hnorm : ‖z‖ = ‖a‖ := by
      simpa [Unitization.norm_inr] using congrArg ENNReal.toReal hrad
    obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum hz
    have hφ : pullbackFunctional A (inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A :=
      pullback_inr_mem_stateSpace_of_norm_eq ha0 hψ (hψa.symm ▸ hnorm)
    simpa [hψa, hnorm] using h _ hφ

/-- An element `a` of a C⋆-algebra is nonnegative if and only if `0 ≤ φ a` for every state
`φ ∈ stateSpace A`. -/
theorem nonneg_iff_forall_mem_stateSpace {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  rw [← Unitization.inr_nonneg_iff, nonneg_iff_forall_mem_stateSpace_unital]
  intro ψ hψ
  let φ := pullbackFunctional A (inrNonUnitalStarAlgHom ℂ A) ψ
  rcases eq_or_ne (toStrongDual φ) 0 with h0 | hne
  · have hφa : φ a = 0 := by rw [← toStrongDual_apply, h0, zero_apply]
    have hψa : ψ (a : A⁺¹) = 0 := by simpa [φ] using hφa
    exact le_of_eq hψa.symm
  · set r := ‖toStrongDual φ‖
    have hr : 0 < r := norm_pos_iff.mpr hne
    let c : ℂ := (r⁻¹ : ℝ)
    have hc : 0 ≤ c := RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hr.le)
    have hrc : (r : ℂ) * c = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one]
    have hstate : c • φ ∈ stateSpace A := by
      refine mem_stateSpace_iff.mpr ⟨fun x hx => ?_, ?_⟩
      · rw [← toStrongDual_apply, map_smul, smul_apply, smul_eq_mul, toStrongDual_apply]
        have hx0 : 0 ≤ φ x := by simpa [φ] using map_nonneg_of_mem_stateSpace hψ hx.inr
        exact mul_nonneg hc hx0
      · rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
          inv_mul_cancel₀ hr.ne']
    have hle : 0 ≤ (c • φ) a := h _ hstate
    rw [← toStrongDual_apply, map_smul, smul_apply, smul_eq_mul, toStrongDual_apply] at hle
    have hmul := mul_nonneg (RCLike.ofReal_nonneg.mpr hr.le) hle
    simpa [φ, ← mul_assoc, hrc] using hmul

end NonUnital

end TauCeti

