/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic

/-!
# Norms and norm attainment of positive functionals on C⋆-algebras

## Pullback along surjective homomorphisms

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. A
surjective star-algebra homomorphism carries increasing approximate units to increasing
approximate units, so pulling a positive functional back along it does not change the norm,
`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`. In particular states pull back
to states along quotient maps; without surjectivity the norm can drop, for instance to `0`.

## Positive functionals in the weak-* dual

For a functional `φ : WeakDual ℂ A` on a C⋆-algebra that is nonnegative on nonnegative elements,
this file records the norm facts about positive functionals in the form used on the weak-* dual.

* `WeakDual.monotone_toStrongDual_of_map_nonneg`: `φ` is monotone.
* `WeakDual.tendsto_approximateUnit_norm_of_map_nonneg`: along the approximate unit, `φ` tends
  to its norm.
* `WeakDual.norm_toStrongDual_eq_map_one_of_map_nonneg`: if `A` is unital, the norm of `φ` is
  `φ 1`.

These are Mathlib's `ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm` and
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`, restated for `WeakDual ℂ A`.

`WeakDual.ext_nonneg` shows that a functional on a C⋆-algebra is determined by its values on
nonnegative elements, since these span the algebra.

## Spectral and norm-attaining states and positive functionals

On a unital C⋆-algebra, every spectral value `z ∈ spectrum ℂ a` of a normal element `a` admits a
state evaluating `star a ^ m * a ^ n` to `star z ^ m * z ^ n`; see
`TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum`.
This is constructed by extending a character on the generated commutative C⋆-subalgebra via
Hahn–Banach.
Specializing to `0 ≤ a` on a nontrivial unital C⋆-algebra gives a state taking `‖a‖ ^ n` on each
`a ^ n` (`TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow`,
`TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_eq_norm`). Pulling back along the
isometric inclusion into `𝓜(ℂ, A)` yields a norm-one positive continuous linear functional on any
nontrivial (possibly nonunital) C⋆-algebra `A` satisfying `ω a = ‖a‖` and `ω (a * a) = ‖a‖ ^ 2`
(`TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq`).

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.4 (states attaining the norm and the
  Gelfand–Naimark theorem).
-/

public section

open Filter
open scoped ComplexOrder Topology

namespace PositiveContinuousLinearMap

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Pulling a positive functional back along a surjective star-algebra homomorphism of
C⋆-algebras preserves its norm. -/
theorem opNorm_comp_ofClass_of_surjective (ω : B →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f) :
    ‖((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(ω : B →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  exact Complex.ofReal_injective <| tendsto_nhds_unique
    ((ω.comp (.ofClass f)).tendsto_nhds_opNorm hl)
    (Filter.tendsto_map'_iff.mp (ω.tendsto_nhds_opNorm (hl.map f hf)))

end PositiveContinuousLinearMap

namespace WeakDual

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

/-- A functional on a C⋆-algebra is determined by its values on nonnegative elements, since
these span the algebra. In particular two states that agree on nonnegative elements are equal. -/
theorem ext_nonneg {φ ψ : WeakDual ℂ A} (h : ∀ a, 0 ≤ a → φ a = ψ a) : φ = ψ := by
  have := LinearMap.ext_on (CStarAlgebra.span_nonneg (A := A))
    (f := (toStrongDual φ : A →ₗ[ℂ] ℂ)) (g := toStrongDual ψ) fun a ha => h a ha
  exact DFunLike.ext _ _ fun a => by simpa using LinearMap.congr_fun this a

/-- A functional that is nonnegative on nonnegative elements is monotone. -/
theorem monotone_toStrongDual_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Monotone (toStrongDual φ) :=
  (monotone_iff_map_nonneg _).mpr fun a ha => (hφ a ha).trans_eq (toStrongDual_apply φ a).symm

/-- Along the approximate unit, a functional that is nonnegative on nonnegative elements tends
to its norm. -/
theorem tendsto_approximateUnit_norm_of_map_nonneg (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    Tendsto (fun e => φ e) (CStarAlgebra.approximateUnit A) (𝓝 (‖toStrongDual φ‖ : ℂ)) := by
  simpa using (ContinuousLinearMap.monotone_iff_tendsto_nhds_opNorm
    (CStarAlgebra.increasingApproximateUnit A)).mp (monotone_toStrongDual_of_map_nonneg hφ)

end NonUnital

/-- On a unital C⋆-algebra, the norm of a functional that is nonnegative on nonnegative elements
is its value at `1`. -/
theorem norm_toStrongDual_eq_map_one_of_map_nonneg {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {φ : WeakDual ℂ A} (hφ : ∀ a, 0 ≤ a → 0 ≤ φ a) :
    (‖toStrongDual φ‖ : ℂ) = φ 1 := by
  simpa using ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mp
    (monotone_toStrongDual_of_map_nonneg hφ)

end WeakDual

open scoped CStarAlgebra MultiplierAlgebra

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
  have haS : a ∈ S := StarAlgebra.elemental.self_mem ℂ a
  let x : S := ⟨a, haS⟩
  have hzS : z ∈ spectrum ℂ x := by
    rw [StarSubalgebra.spectrum_eq]
    exact spectrum.algebraMap_mem ℂ hz
  obtain ⟨χ, hχa⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.1 hzS
  obtain ⟨g, hg_ext, hg_norm⟩ := exists_extension_norm_eq S.toSubmodule
    ((WeakDual.CharacterSpace.toAlgHom χ).toContinuousLinearMap : StrongDual ℂ S.toSubmodule)
  replace hg_norm : ‖g‖ = 1 := hg_norm.trans (AlgHom.toContinuousLinearMap_norm _)
  have hg_one : g 1 = 1 := (hg_ext ⟨1, S.one_mem⟩).trans (map_one χ)
  refine ⟨{ __ := g
            monotone' := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.2
              (by simp [hg_norm, hg_one]) }, hg_one, hg_norm, fun m n => ?_⟩
  have hx : (⟨star a ^ m * a ^ n, (star x ^ m * x ^ n).prop⟩ : S) = star x ^ m * x ^ n := by
    ext; simp [x]
  exact (hg_ext ⟨star a ^ m * a ^ n, (star x ^ m * x ^ n).prop⟩).trans <|
    (congrArg χ hx).trans (by simp [map_star, hχa])

variable [Nontrivial M]

/-- On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `ω` satisfying
`ω (a ^ n) = ‖a‖ ^ n` for every `n : ℕ`. -/
theorem exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow {a : M} (ha : 0 ≤ a) :
    ∃ ω : M →P[ℂ] ℂ, ω 1 = 1 ∧ ‖(ω : M →L[ℂ] ℂ)‖ = 1 ∧
      ∀ n : ℕ, ω (a ^ n) = (‖a‖ : ℂ) ^ n := by
  have : IsStarNormal a := ha.isSelfAdjoint.isStarNormal
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

private theorem exists_positiveContinuousLinearMap_of_ne_zero
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {x : A} (hx : 0 ≤ x) (hx0 : x ≠ 0) :
    ∃ ω : A →P[ℂ] ℂ, ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ω x = ‖x‖ ∧ ω (x * x) = (‖x‖ : ℂ) ^ 2 := by
  let := _root_.CStarAlgebra.spectralOrder 𝓜(ℂ, A)
  have := _root_.CStarAlgebra.spectralOrderedRing 𝓜(ℂ, A)
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have : Nontrivial 𝓜(ℂ, A) := ⟨(x : 𝓜(ℂ, A)), 0, fun h0 => hx_pos.ne' <| by
    rw [← DoubleCentralizer.norm_coe (𝕜 := ℂ), h0, norm_zero]⟩
  have hxM : 0 ≤ (x : 𝓜(ℂ, A)) := by
    simpa using map_nonneg (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)) hx
  obtain ⟨ω₀, -, hω₀_norm, hω₀⟩ := exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow hxM
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
theorem exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
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
