/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
import TauCeti.Analysis.CStarAlgebra.State.Extension

/-!
# Spectral and norm-attaining states and positive functionals

On a unital C⋆-algebra, every Gelfand character on `StarAlgebra.elemental ℂ a` is a state, and
extending it via `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq` gives for every
spectral value `z ∈ spectrum ℂ a` of a normal `a` a state sending `star a ^ m * a ^ n` to
`star z ^ m * z ^ n`
(`exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum`), hence a state on
any `0 ≤ a` attaining `‖a‖ ^ n` (`exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow`,
`exists_positiveContinuousLinearMap_apply_eq_norm`). Pulling back along `A → 𝓜(ℂ, A)` yields a
norm-one positive functional on any nontrivial C⋆-algebra `A` with `ω a = ‖a‖` and
`ω (a * a) = ‖a‖ ^ 2` (`exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq`).

## References

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
      (WeakDual.CharacterSpace.toAlgHom χ).toContinuousLinearMap :=
    DFunLike.ext _ _ fun _ => by simp
  have hχ_state : (χ : WeakDual ℂ S) ∈ stateSpace S :=
    mem_stateSpace_iff_norm_eq_one_and_map_one.2
      ⟨hχ_strong ▸ AlgHom.toContinuousLinearMap_norm _, by simp⟩
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
