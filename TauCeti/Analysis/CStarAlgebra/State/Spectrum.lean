/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
import TauCeti.Analysis.CStarAlgebra.State.Extension
import TauCeti.Analysis.CStarAlgebra.State.Unitization

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

Applying spectral attainment on normal elements to `star x * x` or `x * star x` for
`x = algebraMap ℂ B z - b` together with Cauchy–Schwarz removes the normality hypothesis on a
unital C⋆-algebra `B`: every spectral value `z ∈ spectrum ℂ b` of any `b : B` is attained by a
state in `stateSpace B` (`TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum`).

Passing to the minimal unitization `A⁺¹` and restricting norm-attaining states back to `A` via
`TauCeti.pullbackFunctional_inr_mem_stateSpace_of_mem_stateSpace_of_norm_apply_eq_norm_of_ne_zero`
yields the `stateSpace A` norm-attainment and state-existence theorems for possibly nonunital
C⋆-algebras:

* `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal`: for normal `a` (assuming
  `a ≠ 0`, or `[Nontrivial A]`), a state attains `‖a‖` in modulus.
* `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg`: for `0 ≤ a` (assuming `a ≠ 0`, or
  `[Nontrivial A]`), a state takes the value `‖a‖` at `a`.
* `TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq`: assuming `a ≠ 0` (or
  `[Nontrivial A]`), a state takes the value `‖a‖ ^ 2` at `star a * a`.
* `TauCeti.stateSpace_nonempty_iff` and `TauCeti.stateSpace_nonempty`: `A` admits a state if and
  only if `A` is nontrivial.
* `TauCeti.norm_eq_iSup_norm_apply_stateSpace_of_isStarNormal`: for normal `a` (without
  `[Nontrivial A]`), `‖a‖ = ⨆ φ : stateSpace A, ‖φ.1 a‖`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.3.6 and
  Section 3.4.
* J. Peterson, *Notes on von Neumann algebras* (2013), Proposition 4.1.4, p. 56.
-/

public section

open Set WeakDual
open scoped CStarAlgebra ComplexOrder MultiplierAlgebra NNReal ENNReal

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

section UnitalStateSpace

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

private theorem exists_mem_stateSpace_apply_eq_of_isStarNormal_of_mem_spectrum (b : B)
    [IsStarNormal b] {z : ℂ} (hz : z ∈ spectrum ℂ b) : ∃ φ ∈ stateSpace B, φ b = z := by
  obtain ⟨ω, -, hnorm, hp⟩ :=
    CStarAlgebra.exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum hz
  exact ⟨StrongDual.toWeakDual (ω : B →L[ℂ] ℂ), ω.toWeakDual_mem_stateSpace_iff.2 hnorm,
    by simpa using hp 0 1⟩

private theorem isUnit_of_isUnit_mul_of_isUnit_mul {M : Type*} [Monoid M] {x y : M}
    (h₁ : IsUnit (y * x)) (h₂ : IsUnit (x * y)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  exact isUnit_iff_exists_and_exists.2
    ⟨⟨y * ↑v⁻¹, by rw [← mul_assoc, ← hv, v.mul_inv]⟩,
     ⟨↑u⁻¹ * y, by rw [mul_assoc, ← hu, u.inv_mul]⟩⟩

private theorem exists_mem_stateSpace_apply_eq_zero_of_not_isUnit_star_mul_self {y : B}
    (hy : ¬ IsUnit (star y * y)) : ∃ φ ∈ stateSpace B, φ y = 0 := by
  have : IsStarNormal (star y * y) := (star_mul_self_nonneg y).isSelfAdjoint.isStarNormal
  have h0 : (0 : ℂ) ∈ spectrum ℂ (star y * y) := by rw [spectrum.mem_iff]; simpa using hy
  obtain ⟨φ, hφ, hφ0⟩ :=
    exists_mem_stateSpace_apply_eq_of_isStarNormal_of_mem_spectrum (star y * y) h0
  have hle : ‖φ y‖ ^ 2 ≤ 0 := by simpa [hφ0] using norm_apply_sq_le_of_mem_stateSpace hφ y
  exact ⟨φ, hφ, norm_eq_zero.1 (sq_eq_zero_iff.1 (le_antisymm hle (sq_nonneg _)))⟩

/-- **Spectral attainment by states.** For every element `b` of a unital C⋆-algebra `B`, every
spectral value `z ∈ spectrum ℂ b` is attained by some state `φ ∈ stateSpace B`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum (b : B) {z : ℂ}
    (hz : z ∈ spectrum ℂ b) : ∃ φ ∈ stateSpace B, φ b = z := by
  rw [spectrum.mem_iff] at hz
  set x : B := algebraMap ℂ B z - b
  obtain ⟨φ, hφ, hφx⟩ : ∃ φ ∈ stateSpace B, φ x = 0 := by
    by_cases h₁ : IsUnit (star x * x)
    · by_cases h₂ : IsUnit (x * star x)
      · exact absurd (isUnit_of_isUnit_mul_of_isUnit_mul h₁ h₂) hz
      · obtain ⟨φ, hφ, hφsx⟩ := exists_mem_stateSpace_apply_eq_zero_of_not_isUnit_star_mul_self
          (y := star x) (by simpa [star_star] using h₂)
        exact ⟨φ, hφ, star_eq_zero.1 ((map_star_of_mem_stateSpace hφ x).symm.trans hφsx)⟩
    · exact exists_mem_stateSpace_apply_eq_zero_of_not_isUnit_star_mul_self h₁
  refine ⟨φ, hφ, ?_⟩
  have hsub : z - φ b = 0 := by
    simpa [x, map_sub, Algebra.algebraMap_eq_smul_one, map_smul, map_one_of_mem_stateSpace hφ]
      using hφx
  exact (sub_eq_zero.1 hsub).symm

end UnitalStateSpace

section NonUnitalStateSpace

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Norm attainment on normal elements.** For any nonzero normal element `a` of a possibly
nonunital C⋆-algebra `A`, there is a state `φ ∈ stateSpace A` with `‖φ a‖ = ‖a‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal_of_ne_zero {a : A}
    [IsStarNormal a] (ha : a ≠ 0) : ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  obtain ⟨z, hz, hz_norm⟩ :=
    exists_eNorm_spectrum_eq_spectralRadius_of_nonempty (spectrum.nonempty (a : A⁺¹))
  have hz_eq : ‖z‖ = ‖a‖ := by
    have hspec : (‖z‖₊ : ℝ≥0∞) = ‖(a : A⁺¹)‖₊ :=
      hz_norm.trans (IsStarNormal.spectralRadius_eq_nnNorm (a : A⁺¹))
    exact (congr_arg NNReal.toReal (ENNReal.coe_inj.1 hspec)).trans (Unitization.norm_inr a)
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : A⁺¹) hz
  have hψ_norm : ‖ψ (a : A⁺¹)‖ = ‖a‖ := by rw [hψa, hz_eq]
  exact ⟨pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ,
    pullbackFunctional_inr_mem_stateSpace_of_mem_stateSpace_of_norm_apply_eq_norm_of_ne_zero
      hψ ha hψ_norm,
    by simpa using hψ_norm⟩

/-- **Norm attainment on nonnegative elements.** For any nonzero nonnegative element `a` of a
possibly nonunital C⋆-algebra `A`, there is a state `φ ∈ stateSpace A` with `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero {a : A} (ha : 0 ≤ a)
    (ha0 : a ≠ 0) : ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  have := ha.isSelfAdjoint.isStarNormal
  obtain ⟨φ, hφ, hφa⟩ :=
    exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal_of_ne_zero ha0
  exact ⟨φ, hφ, (Complex.norm_of_nonneg' (map_nonneg_of_mem_stateSpace hφ ha)).symm.trans
    (congr_arg Complex.ofReal hφa)⟩

/-- For any nonzero element `a` of a possibly nonunital C⋆-algebra `A`, there is a state
`φ ∈ stateSpace A` with `φ (star a * a) = ‖a‖ ^ 2`. -/
theorem exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero {a : A} (ha : a ≠ 0) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = ‖a‖ ^ 2 := by
  have hne : star a * a ≠ 0 := star_mul_self_eq_zero.not.2 ha
  obtain ⟨φ, hφ, hφa⟩ :=
    exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero (star_mul_self_nonneg a) hne
  exact ⟨φ, hφ, by simpa [CStarRing.norm_star_mul_self, sq] using hφa⟩

/-- **Existence of states on possibly nonunital C⋆-algebras.** A C⋆-algebra has a state if and only
if it is nontrivial. -/
theorem stateSpace_nonempty_iff : (stateSpace A).Nonempty ↔ Nontrivial A := by
  refine ⟨fun ⟨φ, hφ⟩ => ?_, fun h => ?_⟩
  · by_contra htriv
    rw [not_nontrivial_iff_subsingleton] at htriv
    simp [stateSpace_eq_empty] at hφ
  · obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨φ, hφ, -⟩ := exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero ha
    exact ⟨φ, hφ⟩

/-- **Existence of states.** Every nontrivial C⋆-algebra (possibly nonunital) admits a state. -/
theorem stateSpace_nonempty [Nontrivial A] : (stateSpace A).Nonempty :=
  stateSpace_nonempty_iff.2 ‹Nontrivial A›

/-- Every nontrivial C⋆-algebra has a nonempty state space. -/
instance [Nontrivial A] : Nonempty (stateSpace A) :=
  stateSpace_nonempty.to_subtype

/-- On a nontrivial C⋆-algebra, every normal element `a` (including `0`) has a state attaining
`‖a‖` in modulus. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal [Nontrivial A] (a : A)
    [IsStarNormal a] : ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty (A := A)
    exact ⟨φ, hφ, by simp⟩
  · exact exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal_of_ne_zero ha

/-- On a nontrivial C⋆-algebra, every nonnegative element `a` (including `0`) has a state taking
the value `‖a‖` at `a`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  have := ha.isSelfAdjoint.isStarNormal
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal a
  exact ⟨φ, hφ, (Complex.norm_of_nonneg' (map_nonneg_of_mem_stateSpace hφ ha)).symm.trans
    (congr_arg Complex.ofReal hφa)⟩

/-- On a nontrivial C⋆-algebra, every element `a` has a state taking the value `‖a‖ ^ 2` at
`star a * a`. -/
theorem exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq [Nontrivial A] (a : A) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = ‖a‖ ^ 2 := by
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_eq_norm_of_nonneg (star_mul_self_nonneg a)
  exact ⟨φ, hφ, by simpa [CStarRing.norm_star_mul_self, sq] using hφa⟩

/-- **Norm recovery from states.** For every normal element `a` of a C⋆-algebra `A` (possibly
nonunital or trivial), `‖a‖` is the supremum of `‖φ a‖` over all states `φ ∈ stateSpace A`. -/
theorem norm_eq_iSup_norm_apply_stateSpace_of_isStarNormal (a : A) [IsStarNormal a] :
    ‖a‖ = ⨆ φ : stateSpace A, ‖φ.val a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [Real.iSup_const_zero]
  · have hbdd : BddAbove (range fun φ : stateSpace A => ‖φ.val a‖) :=
      ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact norm_apply_le_of_mem_stateSpace φ.property a⟩
    obtain ⟨φ, hφ, hφa⟩ :=
      exists_mem_stateSpace_norm_apply_eq_norm_of_isStarNormal_of_ne_zero ha
    refine le_antisymm ?_ (Real.iSup_le (fun ψ => norm_apply_le_of_mem_stateSpace ψ.property a)
      (norm_nonneg a))
    exact hφa ▸ le_ciSup hbdd ⟨φ, hφ⟩

end NonUnitalStateSpace

end TauCeti
