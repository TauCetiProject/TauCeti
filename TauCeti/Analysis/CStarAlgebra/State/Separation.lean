/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Analysis.CStarAlgebra.State.Extension

/-!
# Separation of elements by states and faithful states on separable C⋆-algebras

For a possibly nonunital C⋆-algebra `A` equipped with its C⋆-order (`[PartialOrder A]`
`[StarOrderedRing A]`), states separate elements, detect self-adjointness and the order, and attain
the norm of every nonzero normal element (and of every normal or nonnegative element when `A` is
nontrivial; for `A = 0` the state space is empty). When `A` is separable and nontrivial, a
countable convex combination of states produces a single faithful state. Together, state separation
and faithful separable states supply faithfulness of the universal and separable GNS
representations in the Gelfand–Naimark construction
(`TauCeti.Analysis.CStarAlgebra.GelfandNaimark`).

## Main results

* `TauCeti.characterSpace_subset_stateSpace`: every character of a possibly nonunital C⋆-algebra is
  a state.
* `TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum` and
  `TauCeti.exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq`: on a unital C⋆-algebra, every
  spectral value of any element is attained by a state; when `A` is nontrivial and `x` is normal,
  some state attains a spectral value of maximum modulus `‖x‖`.
* `TauCeti.exists_mem_stateSpace_norm_apply_eq_of_ne_zero`,
  `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero`,
  `TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq`, and
  `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg`: for possibly nonunital `A`, states
  attain `‖x‖` on nonzero normal elements, `‖a‖` on nonzero nonnegative elements (and on all
  nonnegative elements when `A` is nontrivial), and `‖a‖ ^ 2` on `star a * a` for every nonzero
  `a : A`. In particular, `TauCeti.stateSpace_nonempty` gives existence of states for every
  nontrivial C⋆-algebra without assuming a unit.
* `TauCeti.eq_zero_iff_forall_mem_stateSpace`, `TauCeti.eq_iff_forall_mem_stateSpace`,
  `TauCeti.isSelfAdjoint_iff_forall_mem_stateSpace`, `TauCeti.nonneg_iff_forall_mem_stateSpace`, and
  `TauCeti.le_iff_forall_mem_stateSpace`: states separate points and detect self-adjointness and the
  C⋆-order.
* `TauCeti.exists_mem_stateSpace_faithful`: every nontrivial separable C⋆-algebra admits a faithful
  state.

## References

* Jesse Peterson, *Notes on operator algebras*, Propositions 4.1.2, 4.1.4, and 4.1.5.
* Gerard J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open Filter Set WeakDual
open scoped ComplexOrder ComplexStarModule Topology

namespace TauCeti

section CharacterSpace

private theorem unital_characterSpace_subset_stateSpace {B : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :
    (WeakDual.characterSpace ℂ B : Set (WeakDual ℂ B)) ⊆ stateSpace B := by
  intro φ hφ
  let χ : WeakDual.characterSpace ℂ B := ⟨φ, hφ⟩
  have hχ : ⇑φ = ⇑χ := WeakDual.CharacterSpace.coe_coe χ
  exact mem_stateSpace_iff_map_one.2 ⟨fun a ha ↦ hχ ▸ map_nonneg χ ha, hχ ▸ map_one χ⟩

/-- Every character of a possibly nonunital C⋆-algebra is a state. -/
theorem characterSpace_subset_stateSpace {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] :
    (WeakDual.characterSpace ℂ B : Set (WeakDual ℂ B)) ⊆ stateSpace B := by
  intro φ hφ
  have hunit : unitizeFunctional φ ∈ WeakDual.characterSpace ℂ (Unitization ℂ B) := by
    refine ⟨fun h0 ↦ ?_, fun x y ↦ ?_⟩
    · have h1 := DFunLike.congr_fun h0 1
      rw [← toStrongDual_apply 0] at h1
      simp at h1
    · simp only [unitizeFunctional_apply, Unitization.fst_mul, Unitization.snd_mul, map_add,
        map_smul, smul_eq_mul, hφ.2]
      ring
  have hpos : ∀ b, 0 ≤ b → 0 ≤ φ b :=
    (unitizeFunctional_mem_stateSpace_iff.1 (unital_characterSpace_subset_stateSpace hunit)).1
  obtain ⟨b, hb⟩ : ∃ b, φ b ≠ 0 := by
    contrapose! hφ
    exact fun h ↦ h.1 (DFunLike.ext _ _ fun b ↦ by simp [hφ b, ← toStrongDual_apply])
  have hl := CStarAlgebra.increasingApproximateUnit B
  have := hl.neBot
  have h1 : Tendsto (fun e : B ↦ φ (e * b)) (CStarAlgebra.approximateUnit B) (𝓝 (φ b)) := by
    simpa [Function.comp_def] using
      ((toStrongDual φ).continuous.tendsto b).comp (hl.tendsto_mul_right b)
  have h2 : Tendsto (fun e : B ↦ φ (e * b)) (CStarAlgebra.approximateUnit B)
      (𝓝 ((‖toStrongDual φ‖ : ℂ) * φ b)) := by
    simpa only [hφ.2] using (tendsto_approximateUnit_norm_of_map_nonneg hpos).mul_const (φ b)
  have hmul : (‖toStrongDual φ‖ : ℂ) * φ b = 1 * φ b := by
    simpa using tendsto_nhds_unique h2 h1
  exact mem_stateSpace_iff.2
    ⟨hpos, Complex.ofReal_injective (by simpa using mul_right_cancel₀ hb hmul)⟩

end CharacterSpace

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum_of_isStarNormal (x : A)
    [IsStarNormal x] {z : ℂ} (hz : z ∈ spectrum ℂ x) : ∃ φ ∈ stateSpace A, φ x = z := by
  let S : StarSubalgebra ℂ A := StarAlgebra.elemental ℂ x
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ x
  let χ : WeakDual.characterSpace ℂ S :=
    (StarAlgebra.elemental.characterSpaceHomeo x).symm ⟨z, hz⟩
  have hχx : χ ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩ = z :=
    congrArg Subtype.val ((StarAlgebra.elemental.characterSpaceHomeo x).apply_symm_apply ⟨z, hz⟩)
  obtain ⟨φ, hφ, hφ_ext⟩ := StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq S
    (characterSpace_subset_stateSpace χ.prop)
  exact ⟨φ, hφ, (hφ_ext ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩).trans hχx⟩

private theorem exists_mem_stateSpace_apply_eq_zero_of_not_exists_left_inv {y : A}
    (hy : ¬ ∃ b, b * y = 1) : ∃ φ ∈ stateSpace A, φ y = 0 := by
  have h0_spec : (0 : ℂ) ∈ spectrum ℂ (star y * y) := by
    rw [spectrum.mem_iff, map_zero, zero_sub]
    intro hu
    obtain ⟨d, hd⟩ := hu.exists_left_inv
    exact hy ⟨-d * star y, by simpa [mul_assoc] using hd⟩
  have := (star_mul_self_nonneg y).isSelfAdjoint.isStarNormal
  obtain ⟨φ, hφ, hφ0⟩ :=
    exists_mem_stateSpace_apply_eq_of_mem_spectrum_of_isStarNormal (star y * y) h0_spec
  let ω : A →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass (statePositiveLinearMap ⟨φ, hφ⟩)
  have hcs : ‖φ y‖ ^ 2 ≤ 0 := by
    simpa [ω, hφ0] using ω.norm_map_sq_le_opNorm_mul y
  have hnorm0 : ‖φ y‖ = 0 := by nlinarith [sq_nonneg ‖φ y‖, norm_nonneg (φ y)]
  exact ⟨φ, hφ, norm_eq_zero.1 hnorm0⟩

/-- **Spectral values are attained by states.** For any element `x` of a unital C⋆-algebra `A` and
`z ∈ spectrum ℂ x`, some state `φ` of `A` satisfies `φ x = z`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum (x : A) {z : ℂ}
    (hz : z ∈ spectrum ℂ x) : ∃ φ ∈ stateSpace A, φ x = z := by
  set y : A := algebraMap ℂ A z - x
  have hy_not_unit : ¬ IsUnit y := spectrum.mem_iff.1 hz
  have ⟨φ, hφ, hφy⟩ : ∃ φ ∈ stateSpace A, φ y = 0 := by
    rw [isUnit_iff_exists_and_exists, not_and_or] at hy_not_unit
    rcases hy_not_unit with hright | hleft
    · have hleft_star : ¬ ∃ b, b * star y = 1 := by
        rintro ⟨b, hb⟩
        exact hright ⟨star b, by simpa using congrArg star hb⟩
      obtain ⟨φ, hφ, hφ_star⟩ := exists_mem_stateSpace_apply_eq_zero_of_not_exists_left_inv
        hleft_star
      rw [map_star_of_mem_stateSpace hφ, star_eq_zero] at hφ_star
      exact ⟨φ, hφ, hφ_star⟩
    · exact exists_mem_stateSpace_apply_eq_zero_of_not_exists_left_inv hleft
  refine ⟨φ, hφ, ?_⟩
  have hsub : z - φ x = 0 := by
    simpa [y, Algebra.algebraMap_eq_smul_one, map_one_of_mem_stateSpace hφ] using hφy
  exact (sub_eq_zero.1 hsub).symm

/-- On a nontrivial unital C⋆-algebra, every normal element `x` admits a state `φ` such that
`φ x ∈ spectrum ℂ x` and `‖φ x‖ = ‖x‖`. -/
theorem exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq [Nontrivial A] (x : A)
    [IsStarNormal x] : ∃ φ ∈ stateSpace A, φ x ∈ spectrum ℂ x ∧ ‖φ x‖ = ‖x‖ := by
  obtain ⟨z, hz, hnorm⟩ := spectrum.exists_nnNorm_eq_spectralRadius x
  rw [IsStarNormal.spectralRadius_eq_nnNorm, ENNReal.coe_inj] at hnorm
  obtain ⟨φ, hφ, hφx⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum x hz
  exact ⟨φ, hφ, hφx ▸ hz, by simpa [hφx] using congrArg NNReal.toReal hnorm⟩

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For a nonzero normal element `x` of a possibly nonunital C⋆-algebra `A`, some state `φ` of `A`
satisfies `‖φ x‖ = ‖x‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_of_ne_zero {x : A} [IsStarNormal x] (hx : x ≠ 0) :
    ∃ φ ∈ stateSpace A, ‖φ x‖ = ‖x‖ := by
  obtain ⟨ψ, hψ, -, hψx⟩ :=
    exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq (x : Unitization ℂ A)
  rw [Unitization.norm_inr] at hψx
  let φ : WeakDual ℂ A := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  have hge : 1 ≤ ‖toStrongDual φ‖ := by
    have hbound : ‖x‖ ≤ ‖toStrongDual φ‖ * ‖x‖ := by
      simpa [φ, hψx] using (toStrongDual φ).le_opNorm x
    exact (le_mul_iff_one_le_left (norm_pos_iff.2 hx)).1 hbound
  exact ⟨φ, mem_stateSpace_iff.2
    ⟨fun _ ↦ map_nonneg_pullbackFunctional_inr_of_mem_stateSpace hψ,
      le_antisymm (norm_toStrongDual_pullbackFunctional_inr_le_one_of_mem_stateSpace hψ) hge⟩,
    by simpa [φ] using hψx⟩

/-- For a nonzero nonnegative element `a` of a possibly nonunital C⋆-algebra `A`, some state `φ` of
`A` satisfies `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero {a : A} (ha : 0 ≤ a)
    (ha0 : a ≠ 0) : ∃ φ ∈ stateSpace A, φ a = (‖a‖ : ℂ) := by
  have := ha.isSelfAdjoint.isStarNormal
  obtain ⟨φ, hφ, hnorm⟩ := exists_mem_stateSpace_norm_apply_eq_of_ne_zero ha0
  have hpos := map_nonneg_of_mem_stateSpace hφ ha
  exact ⟨φ, hφ, (Complex.eq_coe_norm_of_nonneg hpos).trans (by rw [hnorm])⟩

/-- For every nonzero element `a` of a possibly nonunital C⋆-algebra `A`, some state `φ` of `A`
satisfies `φ (star a * a) = ‖a‖ ^ 2`. -/
theorem exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq {a : A} (ha : a ≠ 0) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = (‖a‖ ^ 2 : ℂ) := by
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero
    (star_mul_self_nonneg a) (star_mul_self_eq_zero.not.2 ha)
  exact ⟨φ, hφ, by simpa [CStarRing.norm_star_mul_self, sq] using hφa⟩

/-- **Existence of states.** Every nontrivial C⋆-algebra, possibly nonunital, has a state. -/
theorem stateSpace_nonempty [Nontrivial A] : (stateSpace A).Nonempty := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨φ, hφ, -⟩ := exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq ha
  exact ⟨φ, hφ⟩

/-- On a nontrivial C⋆-algebra, possibly nonunital, every nonnegative element `a` admits a state
`φ` with `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = (‖a‖ : ℂ) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty (A := A)
    exact ⟨φ, hφ, by simp⟩
  · exact exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero ha ha0

/-- An element of a C⋆-algebra is zero if and only if `φ (star a * a) = 0` for every state `φ`. -/
theorem eq_zero_iff_forall_mem_stateSpace_star_mul_self {a : A} :
    a = 0 ↔ ∀ φ ∈ stateSpace A, φ (star a * a) = 0 := by
  refine ⟨fun ha φ _ ↦ by simp [ha], fun h ↦ ?_⟩
  by_contra ha
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq ha
  have hzero : (‖a‖ ^ 2 : ℂ) = 0 := hφa.symm.trans (h φ hφ)
  exact ha (norm_eq_zero.1 (sq_eq_zero_iff.1 (by exact_mod_cast hzero)))

private theorem eq_zero_of_isSelfAdjoint_of_forall_mem_stateSpace {b : A} (hb : IsSelfAdjoint b)
    (h : ∀ φ ∈ stateSpace A, φ b = 0) : b = 0 := by
  by_contra hne
  have := hb.isStarNormal
  obtain ⟨φ, hφ, hnorm⟩ := exists_mem_stateSpace_norm_apply_eq_of_ne_zero hne
  exact hne (norm_eq_zero.1 (by simpa [h φ hφ] using hnorm.symm))

/-- An element of a C⋆-algebra is zero if and only if every state vanishes on it. -/
theorem eq_zero_iff_forall_mem_stateSpace {a : A} :
    a = 0 ↔ ∀ φ ∈ stateSpace A, φ a = 0 := by
  refine ⟨fun ha φ _ ↦ by simp [ha], fun h ↦ ?_⟩
  have hre : (ℜ a : A) = 0 :=
    eq_zero_of_isSelfAdjoint_of_forall_mem_stateSpace (ℜ a).2 fun φ hφ ↦ by
      rw [realPart_apply_coe, ← algebraMap_smul ℂ]
      simp [map_star_of_mem_stateSpace hφ, h φ hφ]
  have him : (ℑ a : A) = 0 :=
    eq_zero_of_isSelfAdjoint_of_forall_mem_stateSpace (ℑ a).2 fun φ hφ ↦ by
      rw [imaginaryPart_apply_coe, ← algebraMap_smul ℂ (2 : ℝ)⁻¹]
      simp [map_star_of_mem_stateSpace hφ, h φ hφ]
  rw [← realPart_add_I_smul_imaginaryPart a, hre, him, smul_zero, add_zero]

/-- **States separate points.** Two elements of a C⋆-algebra are equal if and only if every state
takes the same value on them. -/
theorem eq_iff_forall_mem_stateSpace {a b : A} :
    a = b ↔ ∀ φ ∈ stateSpace A, φ a = φ b := by
  rw [← sub_eq_zero, eq_zero_iff_forall_mem_stateSpace]
  simp [sub_eq_zero]

/-- An element of a C⋆-algebra is self-adjoint if and only if every state takes a real value on
it. -/
theorem isSelfAdjoint_iff_forall_mem_stateSpace {a : A} :
    IsSelfAdjoint a ↔ ∀ φ ∈ stateSpace A, (φ a).im = 0 := by
  refine ⟨fun ha φ hφ ↦ ?_, fun h ↦ ?_⟩
  · have hstar := map_star_of_mem_stateSpace hφ a
    rw [ha.star_eq] at hstar
    exact Complex.conj_eq_iff_im.1 hstar.symm
  · rw [isSelfAdjoint_iff, eq_iff_forall_mem_stateSpace]
    exact fun φ hφ ↦ (map_star_of_mem_stateSpace hφ a).trans (Complex.conj_eq_iff_im.2 (h φ hφ))

/-- **States detect positivity.** An element of a C⋆-algebra is nonnegative if and only if every
state is nonnegative on it. -/
theorem nonneg_iff_forall_mem_stateSpace {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ ↦ map_nonneg_of_mem_stateSpace hφ ha, fun h ↦ ?_⟩
  have hsa : IsSelfAdjoint a := isSelfAdjoint_iff_forall_mem_stateSpace.2 fun φ hφ ↦
    (Complex.nonneg_iff.1 (h φ hφ)).2.symm
  have hsa_inr : IsSelfAdjoint (a : Unitization ℂ A) := hsa.inr ℂ
  rw [← Unitization.inr_nonneg_iff,
    StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : Unitization ℂ A) hsa_inr]
  intro r hr
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : Unitization ℂ A)
    (spectrum.algebraMap_mem ℂ hr)
  let ψ₀ : WeakDual ℂ A := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  by_cases h0 : toStrongDual ψ₀ = 0
  · have h0a : (toStrongDual ψ₀) a = 0 := by simp [h0]
    have hr0 : r = 0 := by simpa [ψ₀, hψa] using h0a
    exact hr0.ge
  · set c : ℝ := ‖toStrongDual ψ₀‖
    have hc : 0 < c := norm_pos_iff.2 h0
    let φ : WeakDual ℂ A := StrongDual.toWeakDual (((c⁻¹ : ℝ) : ℂ) • toStrongDual ψ₀)
    have hφ_eval (b : A) : φ b = ((c⁻¹ : ℝ) : ℂ) * ψ₀ b := by
      rw [← toStrongDual_apply φ]
      simp [φ]
    have hstate : φ ∈ stateSpace A := by
      refine mem_stateSpace_iff.2 ⟨fun b hb ↦ ?_, ?_⟩
      · rw [hφ_eval]
        exact mul_nonneg (Complex.zero_le_real.2 (inv_nonneg.2 hc.le))
          (map_nonneg_pullbackFunctional_inr_of_mem_stateSpace hψ hb)
      · simp only [φ, StrongDual.toStrongDual_toWeakDual, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
        exact inv_mul_cancel₀ hc.ne'
    have hpos : 0 ≤ φ a := h _ hstate
    have hval : φ a = ((c⁻¹ * r : ℝ) : ℂ) := by simp [hφ_eval, ψ₀, hψa]
    rw [hval, Complex.zero_le_real] at hpos
    exact (mul_nonneg_iff_of_pos_left (inv_pos.2 hc)).1 hpos

/-- **States detect the C⋆-order.** In a C⋆-algebra, `a ≤ b` if and only if `φ a ≤ φ b` for every
state `φ`. -/
theorem le_iff_forall_mem_stateSpace {a b : A} :
    a ≤ b ↔ ∀ φ ∈ stateSpace A, φ a ≤ φ b := by
  rw [← sub_nonneg, nonneg_iff_forall_mem_stateSpace]
  simp [sub_nonneg]

end NonUnital

section Separable

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
private theorem eq_zero_of_denseRange {x : ℕ → A} (hx : DenseRange x) {ψ : ℕ → WeakDual ℂ A}
    (hψ : ∀ n, ψ n ∈ stateSpace A) (hψ_norm : ∀ n, ψ n (star (x n) * x n) = (‖x n‖ ^ 2 : ℂ))
    {a : A} (hall_zero : ∀ n, ψ n (star a * a) = 0) : a = 0 := by
  by_contra ha
  have hpos_a : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hx a (‖a‖ / 4) (by positivity)
  rw [dist_comm, dist_eq_norm] at hn
  have hdiff : star (x n) * x n - star a * a =
      star (x n - a) * x n + star a * (x n - a) := by
    simp only [star_sub, sub_mul, mul_sub]
    abel
  have hsq_le : ‖x n‖ ^ 2 ≤ ‖x n - a‖ * (‖x n‖ + ‖a‖) := by
    have hval : ψ n (star (x n) * x n - star a * a) = (‖x n‖ ^ 2 : ℂ) := by
      rw [map_sub, hψ_norm n, hall_zero n, sub_zero]
    calc ‖x n‖ ^ 2 = ‖(‖x n‖ ^ 2 : ℂ)‖ := by simp
      _ = ‖ψ n (star (x n) * x n - star a * a)‖ := by rw [hval]
      _ ≤ ‖star (x n) * x n - star a * a‖ := norm_apply_le_of_mem_stateSpace (hψ n) _
      _ = ‖star (x n - a) * x n + star a * (x n - a)‖ := by rw [hdiff]
      _ ≤ ‖star (x n - a) * x n‖ + ‖star a * (x n - a)‖ := norm_add_le _ _
      _ ≤ ‖star (x n - a)‖ * ‖x n‖ + ‖star a‖ * ‖x n - a‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖x n - a‖ * (‖x n‖ + ‖a‖) := by rw [norm_star, norm_star]; ring
  have hxn_lower : 3 * ‖a‖ / 4 < ‖x n‖ := by
    have htri : ‖a‖ ≤ ‖x n‖ + ‖x n - a‖ := by simpa using norm_sub_le (x n) (x n - a)
    linarith
  have hxn_upper : ‖x n‖ < 5 * ‖a‖ / 4 := by
    have htri : ‖x n‖ ≤ ‖a‖ + ‖x n - a‖ := by simpa using norm_add_le a (x n - a)
    linarith
  nlinarith [norm_nonneg (x n - a), hxn_lower, hxn_upper]

/-- **Existence of a faithful state on a separable C⋆-algebra.** Every nontrivial separable
C⋆-algebra, possibly nonunital, admits a state `φ` such that `φ (star a * a) = 0 ↔ a = 0` for all
`a`. -/
theorem exists_mem_stateSpace_faithful [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ φ ∈ stateSpace A, ∀ a, φ (star a * a) = 0 ↔ a = 0 := by
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq A
  have hex (n : ℕ) : ∃ ψ ∈ stateSpace A, ψ (star (x n) * x n) = (‖x n‖ ^ 2 : ℂ) := by
    obtain ⟨ψ, hψ, hψ_eq⟩ :=
      exists_mem_stateSpace_apply_eq_norm_of_nonneg (star_mul_self_nonneg (x n))
    exact ⟨ψ, hψ, by simpa [CStarRing.norm_star_mul_self, sq] using hψ_eq⟩
  choose ψ hψ hψ_norm using hex
  set w : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 1)
  have hw0 (n : ℕ) : 0 ≤ w n := by positivity
  have hw_pos (n : ℕ) : 0 < w n := by positivity
  have hw1 : HasSum w 1 := by
    simpa [w, pow_succ, mul_comm, div_eq_mul_inv] using hasSum_geometric_two' (1 : ℝ)
  set φ : WeakDual ℂ A := StrongDual.toWeakDual (∑' n, w n • toStrongDual (ψ n))
  refine ⟨φ, toWeakDual_tsum_mem_stateSpace hψ hw0 hw1,
    fun a ↦ ⟨fun ha0 ↦ eq_zero_of_denseRange hx hψ hψ_norm fun n ↦ ?_, fun ha ↦ by simp [ha]⟩⟩
  have heval : HasSum (fun k ↦ w k * (ψ k (star a * a)).re) (φ (star a * a)).re := by
    simpa [φ] using Complex.reCLM.hasSum
      (hasSum_toWeakDual_tsum_apply_of_mem_stateSpace hψ hw0 hw1.summable (star a * a))
  have hre0 : (φ (star a * a)).re = 0 := by simp [ha0]
  have hnonneg (k : ℕ) : 0 ≤ w k * (ψ k (star a * a)).re :=
    mul_nonneg (hw0 k) (Complex.nonneg_iff.1
      (map_nonneg_of_mem_stateSpace (hψ k) (star_mul_self_nonneg a))).1
  have hterm0 : w n * (ψ n (star a * a)).re = 0 :=
    le_antisymm ((heval.summable.le_tsum n fun k _ ↦ hnonneg k).trans_eq
      (heval.tsum_eq.trans hre0)) (hnonneg n)
  exact Complex.ext ((mul_eq_zero.1 hterm0).resolve_left (hw_pos n).ne')
    (Complex.nonneg_iff.1 (map_nonneg_of_mem_stateSpace (hψ n) (star_mul_self_nonneg a))).2.symm

end Separable

end TauCeti
