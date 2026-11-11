/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality

import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Algebra.Algebra.Spectrum

/-!
# Pullback of characters

An algebra homomorphism pulls scalar characters back continuously for the weak-star topologies,
even when the homomorphism itself is not assumed continuous. This construction extends
Mathlib's `WeakDual.CharacterSpace.compContinuousMap` from star algebra homomorphisms to
algebra homomorphisms, using the same scalar automatic-continuity argument.

For a homomorphism with dense range whose image units lift to units, pullback identifies the
target character space with the hull of its kernel. A character killing that kernel is bounded
in the image norm by the spectral bound and therefore extends to the target algebra.

## References

* G. K. Pedersen, *Analysis Now*, §4.2, Exercises 11–12.
* The pullback construction adapts Mathlib's
  `WeakDual.CharacterSpace.compContinuousMap` in `Mathlib.Analysis.CStarAlgebra.GelfandDuality`.
-/

public section

open WeakDual

namespace AlgHom

variable {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra 𝕜 B]

/-- Pullback of scalar characters along an algebra homomorphism. Continuity of the
homomorphism is unnecessary: scalar characters on the source Banach algebra are automatically
continuous. -/
noncomputable def characterPullback (Φ : A →ₐ[𝕜] B) :
    C(characterSpace 𝕜 B, characterSpace 𝕜 A) where
  toFun χ := CharacterSpace.equivAlgHom.symm ((CharacterSpace.toAlgHom χ).comp Φ)
  continuous_toFun := Continuous.subtype_mk
    (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (Φ a)) _

@[simp]
theorem characterPullback_apply (Φ : A →ₐ[𝕜] B) (χ : characterSpace 𝕜 B) (a : A) :
    Φ.characterPullback χ a = χ (Φ a) := (rfl)

@[simp]
theorem characterPullback_id :
    (AlgHom.id 𝕜 A).characterPullback = ContinuousMap.id (characterSpace 𝕜 A) := by
  ext χ a
  rfl

variable [NormedRing C] [NormedAlgebra 𝕜 C]

@[simp]
theorem characterPullback_comp [CompleteSpace B] (Ψ : B →ₐ[𝕜] C) (Φ : A →ₐ[𝕜] B) :
    (Ψ.comp Φ).characterPullback = Φ.characterPullback.comp Ψ.characterPullback := by
  ext χ a
  rfl

/-- Naturality of the Gelfand transform with respect to algebra homomorphisms. -/
theorem gelfandTransform_comp_characterPullback (Φ : A →ₐ[𝕜] B) (a : A) :
    (gelfandTransform 𝕜 A a).comp Φ.characterPullback = gelfandTransform 𝕜 B (Φ a) := by
  ext χ
  rfl

/-- Dense range makes character pullback injective. -/
theorem characterPullback_injective (Φ : A →ₐ[𝕜] B) (hΦ : DenseRange Φ) :
    Function.Injective Φ.characterPullback := by
  intro χ ψ h
  apply CharacterSpace.ext
  exact congrFun (hΦ.equalizer (map_continuous χ) (map_continuous ψ)
    (funext fun a => congrArg (fun ξ : characterSpace 𝕜 A => ξ a) h))

section CompleteField

variable [CompleteSpace 𝕜] [CompleteSpace B]

/-- Every character killing the kernel extends across a dense homomorphism whose image
units lift to units. No continuity assumption on the homomorphism is needed. -/
theorem exists_characterPullback_eq_of_ker_le (Φ : A →ₐ[𝕜] B) (hΦ : DenseRange Φ)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a)
    (χ : characterSpace 𝕜 A) (hχ : RingHom.ker Φ ≤ RingHom.ker χ) :
    ∃ ψ : characterSpace 𝕜 B, Φ.characterPullback ψ = χ := by
  have hbound (a : A) : ‖χ a‖ ≤ ‖Φ a‖ :=
    quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum 𝕜 (Φ a)
      (Φ.apply_mem_spectrum_of_ker_le hUnits (CharacterSpace.toAlgHom χ) hχ a))
  let e : B →L[𝕜] 𝕜 := (CharacterSpace.toAlgHom χ).toLinearMap.extendOfNorm Φ.toLinearMap
  have he (a : A) : e (Φ a) = χ a :=
    LinearMap.extendOfNorm_eq hΦ ⟨1, fun a => by simpa using hbound a⟩ a
  have he_mul (b c : B) : e (b * c) = e b * e c := by
    refine hΦ.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ b c
    intro a a'
    rw [← map_mul, he, he, he, map_mul]
  let ψ : B →ₐ[𝕜] 𝕜 :=
    { e.toLinearMap with
      map_one' := by simpa using he 1
      map_zero' := e.map_zero
      map_mul' := he_mul
      commutes' := fun r => by simpa [AlgHomClass.commutes] using he (algebraMap 𝕜 A r) }
  refine ⟨CharacterSpace.equivAlgHom.symm ψ, ?_⟩
  ext a
  exact he a

/-- The image of character pullback is the hull of the kernel when the homomorphism has
dense range and units in its image lift to units. -/
theorem range_characterPullback (Φ : A →ₐ[𝕜] B) (hΦ : DenseRange Φ)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a) :
    Set.range Φ.characterPullback = {χ : characterSpace 𝕜 A |
      RingHom.ker Φ ≤ RingHom.ker χ} := by
  ext χ
  constructor
  · rintro ⟨ψ, rfl⟩ a ha
    simp only [RingHom.mem_ker, characterPullback_apply, RingHom.mem_ker.mp ha,
      map_zero]
  · exact Φ.exists_characterPullback_eq_of_ker_le hΦ hUnits χ

end CompleteField

variable [ProperSpace 𝕜] [CompleteSpace B]

/-- Pullback is a homeomorphism onto the hull of the kernel for a dense homomorphism
whose image units lift to units. The lifting condition says exactly that the units of the
target lying in the image are images of source units. -/
noncomputable def characterPullbackHomeomorph (Φ : A →ₐ[𝕜] B) (hΦ : DenseRange Φ)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a) :
    characterSpace 𝕜 B ≃ₜ {χ : characterSpace 𝕜 A // RingHom.ker Φ ≤ RingHom.ker χ} := by
  let f : characterSpace 𝕜 B → {χ : characterSpace 𝕜 A //
      RingHom.ker Φ ≤ RingHom.ker χ} := fun ψ => ⟨Φ.characterPullback ψ,
        (Φ.range_characterPullback hΦ hUnits).subset (Set.mem_range_self ψ)⟩
  have hf : Function.Bijective f :=
    ⟨fun χ ψ h => Φ.characterPullback_injective hΦ (congrArg Subtype.val h),
      fun χ => by
        obtain ⟨ψ, hψ⟩ := Φ.exists_characterPullback_eq_of_ker_le hΦ hUnits χ.val χ.property
        exact ⟨ψ, Subtype.ext hψ⟩⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    (Φ.characterPullback.continuous.subtype_mk _)

@[simp]
theorem characterPullbackHomeomorph_apply (Φ : A →ₐ[𝕜] B) (hΦ : DenseRange Φ)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a)
    (ψ : characterSpace 𝕜 B) :
    (Φ.characterPullbackHomeomorph hΦ hUnits ψ).val = Φ.characterPullback ψ := (rfl)

@[simp]
theorem characterPullbackHomeomorph_symm_apply (Φ : A →ₐ[𝕜] B) (hΦ : DenseRange Φ)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a)
    (χ : {χ : characterSpace 𝕜 A // RingHom.ker Φ ≤ RingHom.ker χ}) (a : A) :
    (Φ.characterPullbackHomeomorph hΦ hUnits).symm χ (Φ a) = χ.val a := by
  have h := congrArg (fun ξ => ξ.val a)
    ((Φ.characterPullbackHomeomorph hΦ hUnits).apply_symm_apply χ)
  simpa only [characterPullbackHomeomorph_apply, characterPullback_apply] using h

end AlgHom

namespace StarAlgHom

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [StarRing A]
  [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarRing B]

/-- Algebra-homomorphism pullback agrees with Mathlib's star-homomorphism pullback. -/
theorem characterPullback_eq_compContinuousMap (Φ : A →⋆ₐ[𝕜] B) :
    Φ.toAlgHom.characterPullback = CharacterSpace.compContinuousMap Φ := by
  ext χ a
  rfl

end StarAlgHom
