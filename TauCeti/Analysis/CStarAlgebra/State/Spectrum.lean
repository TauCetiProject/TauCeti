/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
import TauCeti.Analysis.CStarAlgebra.State.Extension

/-!
# Spectral and norm-attaining states, and state characterizations of order and norm

On a unital C⋆-algebra, every Gelfand character on `StarAlgebra.elemental ℂ a` is a state, and
extending it via `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq` gives for every
spectral value `z ∈ spectrum ℂ a` of a normal `a` a state sending `star a ^ m * a ^ n` to
`star z ^ m * z ^ n`
(`exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum`), hence a state on
any `0 ≤ a` attaining `‖a‖ ^ n` (`exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow`,
`exists_positiveContinuousLinearMap_apply_eq_norm`). Pulling back along `A → 𝓜(ℂ, A)` yields a
norm-one positive functional on any nontrivial C⋆-algebra `A` with `ω a = ‖a‖` and
`ω (a * a) = ‖a‖ ^ 2` (`exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq`).

On `TauCeti.stateSpace`, Cauchy–Schwarz extends spectral attainment to arbitrary (not necessarily
normal) elements of unital C⋆-algebras (`TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum`),
and passing through the unitization `A⁺¹` gives state characterizations of norm and order on
possibly nonunital C⋆-algebras (`TauCeti.exists_mem_stateSpace_apply_eq_norm`,
`TauCeti.norm_le_of_forall_mem_stateSpace`, `TauCeti.nonneg_iff_forall_mem_stateSpace`).

## References

* B. Blackadar, *Operator Algebras*, II.6.3.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.4.
-/

public section

open scoped CStarAlgebra ComplexOrder MultiplierAlgebra

namespace TauCeti.CStarAlgebra

section Unital

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- On a unital C⋆-algebra, every spectral value `z ∈ spectrum ℂ a` of a normal element `a` admits
a state `ω` satisfying `ω (star a ^ m * a ^ n) = star z ^ m * z ^ n` for all `m n : ℕ`. -/
theorem exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum {a : M}
    [IsStarNormal a] {z : ℂ} (hz : z ∈ spectrum ℂ a) :
    ∃ ω : M →P[ℂ] ℂ, ω 1 = 1 ∧ ‖(ω : M →L[ℂ] ℂ)‖ = 1 ∧
      ∀ m n : ℕ, ω (star a ^ m * a ^ n) = star z ^ m * z ^ n := by
  have : Nontrivial M :=
    nontrivial_of_ne (1 : M) 0 fun h10 => hz ⟨⟨_, 0, by simp [h10], by simp [h10]⟩, rfl⟩
  set S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set M) := StarAlgebra.elemental.isClosed ℂ a
  let x : S := ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  obtain ⟨χ, hχa⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.1
    (StarSubalgebra.spectrum_eq (S := S) (a := x) ▸ spectrum.algebraMap_mem ℂ hz)
  have hχ_strong : WeakDual.toStrongDual (χ : WeakDual ℂ S) =
      (WeakDual.CharacterSpace.toAlgHom χ : S →ₙₐ[ℂ] ℂ).toStrongDual :=
    DFunLike.ext _ _ fun _ => by simp
  have hχ_state : (χ : WeakDual ℂ S) ∈ stateSpace S :=
    mem_stateSpace_iff_norm_eq_one_and_map_one.2
      ⟨hχ_strong ▸ AlgHom.norm_toStrongDual_toNonUnitalAlgHom _, by simp⟩
  obtain ⟨ψ, hψ, hψ_ext⟩ := S.exists_mem_stateSpace_forall_apply_coe_eq hχ_state
  refine ⟨.mk₀ (WeakDual.toStrongDual ψ) fun _ => map_nonneg_of_mem_stateSpace hψ,
    (PositiveContinuousLinearMap.mk₀_apply _ _ 1).trans <|
      (WeakDual.toStrongDual_apply ψ 1).trans (map_one_of_mem_stateSpace hψ),
    (congrArg norm (PositiveContinuousLinearMap.toContinuousLinearMap_mk₀ _ _)).trans
      (norm_toStrongDual_of_mem_stateSpace hψ), fun m n => ?_⟩
  have hx : (⟨star a ^ m * a ^ n, (star x ^ m * x ^ n).prop⟩ : S) = star x ^ m * x ^ n :=
    Subtype.ext (by simp [x])
  exact (PositiveContinuousLinearMap.mk₀_apply _ _ _).trans <|
    (WeakDual.toStrongDual_apply ψ _).trans <|
      (hψ_ext ⟨star a ^ m * a ^ n, (star x ^ m * x ^ n).prop⟩).trans <|
        (congrArg χ hx).trans (by simp [map_star, hχa])

variable [Nontrivial M]

/-- On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `ω` satisfying
`ω (a ^ n) = ‖a‖ ^ n` for every `n : ℕ`. -/
theorem exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow {a : M} (ha : 0 ≤ a) :
    ∃ ω : M →P[ℂ] ℂ, ω 1 = 1 ∧ ‖(ω : M →L[ℂ] ℂ)‖ = 1 ∧
      ∀ n : ℕ, ω (a ^ n) = (‖a‖ : ℂ) ^ n := by
  have := ha.isSelfAdjoint.isStarNormal
  obtain ⟨ω, h1, hn, hp⟩ :=
    exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum
      (_root_.CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)
  exact ⟨ω, h1, hn, fun n => by simpa using hp 0 n⟩

/-- On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `ω` with
`ω a = ‖a‖`. -/
theorem exists_positiveContinuousLinearMap_apply_eq_norm {a : M} (ha : 0 ≤ a) :
    ∃ ω : M →P[ℂ] ℂ, ω 1 = 1 ∧ ‖(ω : M →L[ℂ] ℂ)‖ = 1 ∧ ω a = ‖a‖ :=
  let ⟨ω, h1, hn, hp⟩ := exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow ha
  ⟨ω, h1, hn, by simpa using hp 1⟩

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem exists_positiveContinuousLinearMap_of_ne_zero {x : A} (hx : 0 ≤ x) (hx0 : x ≠ 0) :
    ∃ ω : A →P[ℂ] ℂ, ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ω x = ‖x‖ ∧ ω (x * x) = (‖x‖ : ℂ) ^ 2 := by
  let := _root_.CStarAlgebra.spectralOrder 𝓜(ℂ, A)
  have := _root_.CStarAlgebra.spectralOrderedRing 𝓜(ℂ, A)
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have : Nontrivial 𝓜(ℂ, A) := ⟨(x : 𝓜(ℂ, A)), 0, fun h0 => hx_pos.ne' <| by
    rw [← DoubleCentralizer.norm_coe (𝕜 := ℂ), h0, norm_zero]⟩
  obtain ⟨ω₀, -, hω₀_norm, hω₀⟩ := exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow
    (map_nonneg (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)) hx)
  let ω : A →P[ℂ] ℂ :=
    ω₀.comp (.ofClass (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)))
  have h1 : ω x = ‖x‖ := by simpa [ω, DoubleCentralizer.norm_coe] using hω₀ 1
  have h2 : ω (x * x) = (‖x‖ : ℂ) ^ 2 := by
    simpa [ω, sq, ← DoubleCentralizer.coe_mul, DoubleCentralizer.norm_coe] using hω₀ 2
  refine ⟨ω, le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => ?_) ?_, h1, h2⟩
  · simpa [ω, hω₀_norm, DoubleCentralizer.norm_coe] using
      (ω₀ : 𝓜(ℂ, A) →L[ℂ] ℂ).le_opNorm (b : 𝓜(ℂ, A))
  · have hle := (ω : A →L[ℂ] ℂ).le_opNorm x
    rw [PositiveContinuousLinearMap.coe_toContinuousLinearMap, h1, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg x)] at hle
    exact le_of_mul_le_mul_right (by simpa only [one_mul] using hle) hx_pos

/-- On a nontrivial C⋆-algebra, every nonnegative element `a` admits a positive continuous linear
functional `ω` of norm `1` satisfying `ω a = ‖a‖` and `ω (a * a) = ‖a‖ ^ 2`. -/
theorem exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq [Nontrivial A]
    {a : A} (ha : 0 ≤ a) :
    ∃ ω : A →P[ℂ] ℂ, ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ω a = ‖a‖ ∧ ω (a * a) = (‖a‖ : ℂ) ^ 2 := by
  rcases ne_or_eq a 0 with ha0 | rfl
  · exact exists_positiveContinuousLinearMap_of_ne_zero ha ha0
  · obtain ⟨b, hb⟩ := exists_ne (0 : A)
    obtain ⟨ω, hnorm, -, -⟩ := exists_positiveContinuousLinearMap_of_ne_zero
      (star_mul_self_nonneg b) (star_mul_self_eq_zero.not.2 hb)
    exact ⟨ω, hnorm, by simp, by simp⟩

end NonUnital

end TauCeti.CStarAlgebra

namespace TauCeti

open Unitization WeakDual
open scoped ComplexStarModule

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum_normal {x : A} [IsStarNormal x]
    {z : ℂ} (hz : z ∈ spectrum ℂ x) :
    ∃ φ ∈ stateSpace A, φ x = z := by
  obtain ⟨ω, -, hnorm, hp⟩ :=
    CStarAlgebra.exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum hz
  exact ⟨StrongDual.toWeakDual (ω : A →L[ℂ] ℂ), ω.toWeakDual_mem_stateSpace_iff.2 hnorm,
    by simpa using hp 0 1⟩

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
    nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace (ℑ a).property fun φ hφ => by
      simp [him_zero φ hφ]
  have him_nonpos : 0 ≤ -(ℑ a : A) :=
    nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace (ℑ a).property.neg fun φ hφ => by
      rw [← toStrongDual_apply, map_neg, toStrongDual_apply, him_zero φ hφ, neg_zero]
  have him_eq : ℑ a = 0 := Subtype.ext <| le_antisymm (neg_nonneg.mp him_nonpos) him_nonneg
  have hre_nonneg : 0 ≤ (ℜ a : A) :=
    nonneg_of_isSelfAdjoint_of_forall_mem_stateSpace (ℜ a).property fun φ hφ => by
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
    ⟨fun x hx => by simpa [φ] using map_nonneg_of_mem_stateSpace hψ (hx.inr ℂ), le_antisymm ?_ ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa [φ, Unitization.norm_inr] using norm_apply_le_of_mem_stateSpace hψ (x : A⁺¹)
  · have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hle : ‖a‖ ≤ ‖toStrongDual φ‖ * ‖a‖ := by
      simpa [φ, hnorm] using (toStrongDual φ).le_opNorm a
    exact (le_mul_iff_one_le_left ha_pos).mp hle

/-- For every nonnegative element `a` of a nontrivial C⋆-algebra, there is a state `φ` attaining
its norm: `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  obtain ⟨ω, hnorm, ha_eq, -⟩ :=
    CStarAlgebra.exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq ha
  exact ⟨StrongDual.toWeakDual (ω : A →L[ℂ] ℂ), ω.toWeakDual_mem_stateSpace_iff.2 hnorm,
    by simpa using ha_eq⟩

/-- A normal element `a` of a C⋆-algebra has norm at most `c ≥ 0` whenever `‖φ a‖ ≤ c` for every
state `φ`. -/
theorem norm_le_of_forall_mem_stateSpace {a : A} [IsStarNormal a] {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ φ ∈ stateSpace A, ‖φ a‖ ≤ c) : ‖a‖ ≤ c := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simpa using hc
  · obtain ⟨z, hz, hrad⟩ := spectrum.exists_eNorm_eq_spectralRadius (a : A⁺¹)
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
  rw [← Unitization.inr_nonneg_iff ℂ, nonneg_iff_forall_mem_stateSpace_unital]
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
        have hx0 : 0 ≤ φ x := by simpa [φ] using map_nonneg_of_mem_stateSpace hψ (hx.inr ℂ)
        exact mul_nonneg hc hx0
      · rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
          inv_mul_cancel₀ hr.ne']
    have hle : 0 ≤ (c • φ) a := h _ hstate
    rw [← toStrongDual_apply, map_smul, smul_apply, smul_eq_mul, toStrongDual_apply] at hle
    have hmul := mul_nonneg (RCLike.ofReal_nonneg.mpr hr.le) hle
    simpa [φ, ← mul_assoc, hrc] using hmul

end NonUnital

end TauCeti
