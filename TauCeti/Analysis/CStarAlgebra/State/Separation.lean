/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Spectrum
import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic
import TauCeti.Analysis.CStarAlgebra.State.Spectrum

/-!
# Norm recovery, order detection, and point separation by states

States of a possibly nonunital C⋆-algebra `A` recover norms of normal elements, detect the
self-adjoint subspace and the positive cone, and separate points.

* `TauCeti.CStarAlgebra.stateSpace_nonempty`, `TauCeti.stateSpace_nonempty_iff`: a C⋆-algebra has a
  state if and only if it is nontrivial.
* `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm`,
  `TauCeti.norm_le_iff_forall_mem_stateSpace`: on a nontrivial C⋆-algebra, every normal element `a`
  admits a state `φ` with `‖φ a‖ = ‖a‖`, obtained by pulling a spectral state of `𝓜(ℂ, A)` back
  along `A → 𝓜(ℂ, A)`.
* `TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_posPart_eq_zero`: if `a` is
  self-adjoint with `a⁻ ≠ 0`, a state of `𝓜(ℂ, A)` attaining `1` on `u = ‖a⁻‖⁻¹ • a⁻` vanishes on
  `1 - u` by Cauchy–Schwarz, hence vanishes on `a⁺ = a⁺ (1 - u)` while sending `a⁻` to `‖a⁻‖`.
* `TauCeti.nonneg_iff_forall_mem_stateSpace`, `TauCeti.le_iff_forall_mem_stateSpace`: an element `a`
  satisfies `0 ≤ a` if and only if `0 ≤ φ a` for every state `φ`, with neither a unit nor a prior
  self-adjointness hypothesis on `a`.
* `TauCeti.isSelfAdjoint_iff_forall_mem_stateSpace`, `TauCeti.eq_iff_forall_mem_stateSpace`: states
  detect self-adjointness and separate points of `A`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.4.
* B. Blackadar, *Operator Algebras*, II.6.3.
-/

public section

open Set WeakDual
open scoped CStarAlgebra ComplexOrder MultiplierAlgebra ENNReal NNReal

namespace TauCeti

namespace CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem norm_comp_coeHom_eq_one {M : Type*} [CStarAlgebra M] [PartialOrder M]
    [StarOrderedRing M] (ι : A →⋆ₙₐ[ℂ] M) (hι : ∀ b, ‖ι b‖ = ‖b‖) (ω₀ : M →P[ℂ] ℂ)
    (hω₀ : ‖(ω₀ : M →L[ℂ] ℂ)‖ = 1) {x : A} (hx0 : x ≠ 0) (hx : ‖ω₀ (ι x)‖ = ‖x‖) :
    ‖((ω₀.comp (.ofClass ι) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = 1 := by
  let ω : A →P[ℂ] ℂ := ω₀.comp (.ofClass ι)
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => ?_) ?_
  · simpa [ω, hω₀, hι b] using (ω₀ : M →L[ℂ] ℂ).le_opNorm (ι b)
  · have hle := (ω : A →L[ℂ] ℂ).le_opNorm x
    rw [PositiveContinuousLinearMap.coe_toContinuousLinearMap] at hle
    exact le_of_mul_le_mul_right (by simpa [ω, hx] using hle) (norm_pos_iff.2 hx0)

/-- On a nontrivial C⋆-algebra, every normal element `a` admits a norm-one positive continuous
linear functional `ω` satisfying `‖ω a‖ = ‖a‖`. -/
theorem exists_positiveContinuousLinearMap_norm_apply_eq_norm [Nontrivial A] (a : A)
    [IsStarNormal a] :
    ∃ ω : A →P[ℂ] ℂ, ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ‖ω a‖ = ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨ω, hnorm, -, -⟩ :=
      exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq (le_rfl : (0 : A) ≤ 0)
    exact ⟨ω, hnorm, by simp⟩
  let := _root_.CStarAlgebra.spectralOrder 𝓜(ℂ, A)
  have := _root_.CStarAlgebra.spectralOrderedRing 𝓜(ℂ, A)
  let ι : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A) := DoubleCentralizer.coeHom (𝕜 := ℂ)
  have hι (b : A) : ‖ι b‖ = ‖b‖ := DoubleCentralizer.norm_coe b
  have : Nontrivial 𝓜(ℂ, A) := ⟨ι a, 0, fun h0 => ha0 <| norm_eq_zero.1 <| by
    simpa [hι] using congrArg norm h0⟩
  obtain ⟨z, hz, hznorm⟩ := spectrum.exists_nnNorm_eq_spectralRadius (ι a)
  rw [IsStarNormal.spectralRadius_eq_nnNorm, ENNReal.coe_inj] at hznorm
  have hz_eq : ‖z‖ = ‖a‖ := (congrArg NNReal.toReal hznorm).trans (hι a)
  obtain ⟨ω₀, -, hω₀_norm, hω₀⟩ :=
    exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum hz
  have hωa : ω₀ (ι a) = z := by simpa using hω₀ 0 1
  exact ⟨ω₀.comp (.ofClass ι),
    norm_comp_coeHom_eq_one ι hι ω₀ hω₀_norm ha0 (by simp [hωa, hz_eq]),
    by simp [hωa, hz_eq]⟩

/-- For an element `a` of a C⋆-algebra with `a⁻ ≠ 0`, there is a norm-one positive continuous
linear functional vanishing on `a⁺` and sending `a⁻` to `‖a⁻‖`. -/
theorem exists_positiveContinuousLinearMap_apply_posPart_eq_zero {a : A} (ha_neg : a⁻ ≠ 0) :
    ∃ ω : A →P[ℂ] ℂ, ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ω a⁺ = 0 ∧ ω a⁻ = ‖a⁻‖ := by
  let := _root_.CStarAlgebra.spectralOrder 𝓜(ℂ, A)
  have := _root_.CStarAlgebra.spectralOrderedRing 𝓜(ℂ, A)
  let ι : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A) := DoubleCentralizer.coeHom (𝕜 := ℂ)
  have hι (b : A) : ‖ι b‖ = ‖b‖ := DoubleCentralizer.norm_coe b
  let u : A := ‖a⁻‖⁻¹ • a⁻
  have hu_nonneg : 0 ≤ u := smul_nonneg (inv_nonneg.2 (norm_nonneg _)) (CFC.negPart_nonneg a)
  have hu_norm : ‖u‖ = 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 ha_neg)]
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (hu_norm.symm ▸ one_ne_zero)
  have : Nontrivial 𝓜(ℂ, A) := ⟨ι u, 0, fun h0 => hu0 <| norm_eq_zero.1 <| by
    simpa [hι] using congrArg norm h0⟩
  obtain ⟨ω₀, hω₀1, hω₀_norm, hω₀⟩ :=
    exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow (map_nonneg ι hu_nonneg)
  have hω₀u : ω₀ (ι u) = 1 := by simpa [hι, hu_norm] using hω₀ 1
  have hω₀u2 : ω₀ (ι u * ι u) = 1 := by simpa [sq, hι, hu_norm] using hω₀ 2
  have h1u : ω₀ (star (1 - ι u) * (1 - ι u)) = 0 := by
    have hsu : star (ι u) = ι u := (map_nonneg ι hu_nonneg).isSelfAdjoint.star_eq
    have hexp : star (1 - ι u) * (1 - ι u) = 1 - ι u - (ι u - ι u * ι u) := by
      rw [star_sub, star_one, hsu, mul_sub, mul_one, sub_mul, one_mul]
    rw [hexp, map_sub, map_sub, map_sub, hω₀1, hω₀u, hω₀u2]
    ring
  have hcs := PositiveLinearMap.norm_map_star_mul_le ω₀ (star (ι a⁺)) (1 - ι u)
  rw [star_star, h1u, norm_zero, Real.sqrt_zero, mul_zero, norm_le_zero_iff] at hcs
  have hmul : ι a⁺ * ι u = 0 := by
    rw [← map_mul]; simp [u, mul_smul_comm, CFC.posPart_mul_negPart]
  have hpos_zero : ω₀ (ι a⁺) = 0 := by simpa [mul_sub, mul_one, hmul] using hcs
  have hneg_eq : (ω₀.comp (.ofClass ι)) a⁻ = ‖a⁻‖ := by
    have hu_inv : a⁻ = ‖a⁻‖ • u := by
      simp [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 ha_neg)]
    conv_lhs => rw [hu_inv]
    simp [PositiveContinuousLinearMap.comp_apply, Complex.real_smul, hω₀u]
  exact ⟨ω₀.comp (.ofClass ι), norm_comp_coeHom_eq_one ι hι ω₀ hω₀_norm hu0
    (by simp [hω₀u, hu_norm]), hpos_zero, hneg_eq⟩

/-- **Existence of states.** Every nontrivial (possibly nonunital) C⋆-algebra has a state. -/
theorem stateSpace_nonempty [Nontrivial A] : (stateSpace A).Nonempty := by
  obtain ⟨ω, hnorm, -, -⟩ :=
    exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq (le_rfl : (0 : A) ≤ 0)
  exact ⟨StrongDual.toWeakDual (ω : A →L[ℂ] ℂ), ω.toWeakDual_mem_stateSpace_iff.2 hnorm⟩

end CStarAlgebra

section StateSpace

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] {φ : WeakDual ℂ A}

/-- The state space of a subsingleton C⋆-algebra is empty. -/
theorem stateSpace_eq_empty [Subsingleton A] : stateSpace A = ∅ := by
  ext ψ
  simp only [mem_stateSpace_iff, mem_empty_iff_false, iff_false, not_and]
  intro _
  rw [Subsingleton.elim (toStrongDual ψ) 0, norm_zero]
  exact zero_ne_one

variable [StarOrderedRing A]

/-- The state space of a C⋆-algebra is nonempty if and only if the algebra is nontrivial. -/
theorem stateSpace_nonempty_iff : (stateSpace A).Nonempty ↔ Nontrivial A := by
  refine ⟨fun ⟨ψ, hψ⟩ => ?_, fun _ => CStarAlgebra.stateSpace_nonempty⟩
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  simp [stateSpace_eq_empty] at hψ

/-- Every state of a C⋆-algebra preserves the involution: `φ (star a) = star (φ a)`. -/
theorem map_star_of_mem_stateSpace (hφ : φ ∈ stateSpace A) (a : A) :
    φ (star a) = star (φ a) := by
  obtain ⟨ω, -, rfl⟩ := mem_stateSpace_iff_exists_positiveLinearMap.1 hφ
  exact map_star ω a

/-- Every state sends self-adjoint elements to real (self-adjoint) scalars. -/
theorem isSelfAdjoint_map_of_mem_stateSpace (hφ : φ ∈ stateSpace A) {a : A}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (φ a) := by
  rw [IsSelfAdjoint, ← map_star_of_mem_stateSpace hφ, ha.star_eq]

/-- On a nontrivial C⋆-algebra, every nonnegative element `a` admits a state `φ` satisfying
`φ a = ‖a‖` and `φ (a * a) = ‖a‖ ^ 2`. -/
theorem exists_mem_stateSpace_apply_mul_self_eq_norm_sq [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ ∧ φ (a * a) = (‖a‖ : ℂ) ^ 2 := by
  obtain ⟨ω, hnorm, ha1, ha2⟩ :=
    CStarAlgebra.exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq ha
  exact ⟨StrongDual.toWeakDual (ω : A →L[ℂ] ℂ), ω.toWeakDual_mem_stateSpace_iff.2 hnorm, ha1, ha2⟩

/-- On a nontrivial C⋆-algebra, every nonnegative element `a` admits a state `φ` with
`φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ :=
  let ⟨φ, hφ, ha1, _⟩ := exists_mem_stateSpace_apply_mul_self_eq_norm_sq ha
  ⟨φ, hφ, ha1⟩

/-- **Norm attainment for normal elements.** On a nontrivial C⋆-algebra, every normal element `a`
admits a state `φ` satisfying `‖φ a‖ = ‖a‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  obtain ⟨ω, hnorm, ha⟩ := CStarAlgebra.exists_positiveContinuousLinearMap_norm_apply_eq_norm a
  exact ⟨StrongDual.toWeakDual (ω : A →L[ℂ] ℂ), ω.toWeakDual_mem_stateSpace_iff.2 hnorm, ha⟩

/-- For a normal element `a` and `0 ≤ c`, `‖a‖ ≤ c` if and only if `‖φ a‖ ≤ c` for all states `φ`.
-/
theorem norm_le_iff_forall_mem_stateSpace (a : A) [IsStarNormal a] {c : ℝ} (hc : 0 ≤ c) :
    ‖a‖ ≤ c ↔ ∀ φ ∈ stateSpace A, ‖φ a‖ ≤ c := by
  refine ⟨fun h φ hφ => (norm_apply_le_of_mem_stateSpace hφ a).trans h, fun h => ?_⟩
  rcases subsingleton_or_nontrivial A with _ | _
  · rwa [Subsingleton.elim a 0, norm_zero]
  · obtain ⟨φ, hφ, hnorm⟩ := exists_mem_stateSpace_norm_apply_eq_norm a
    exact hnorm ▸ h φ hφ

/-- **Self-adjointness detection by states.** An element `a : A` is self-adjoint if and only if
`φ a` is self-adjoint (i.e., real) for every state `φ` of `A`. -/
theorem isSelfAdjoint_iff_forall_mem_stateSpace {a : A} :
    IsSelfAdjoint a ↔ ∀ φ ∈ stateSpace A, IsSelfAdjoint (φ a) := by
  refine ⟨fun ha φ hφ => isSelfAdjoint_map_of_mem_stateSpace hφ ha, fun h => ?_⟩
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim a 0]
    exact IsSelfAdjoint.zero A
  let y : A := Complex.I • (a - star a)
  have hy_sa : IsSelfAdjoint y := by
    rw [IsSelfAdjoint]
    simp [y, star_smul, smul_sub, sub_eq_add_neg, add_comm]
  have : IsStarNormal y := hy_sa.isStarNormal
  have hy0 : ‖y‖ ≤ 0 := (norm_le_iff_forall_mem_stateSpace y le_rfl).2 fun φ hφ => by
    have hφa : star (φ a) = φ a := (h φ hφ).star_eq
    simp [y, map_sub, map_smul, map_star_of_mem_stateSpace hφ, hφa]
  have hsub : a - star a = 0 :=
    (smul_eq_zero.1 (norm_le_zero_iff.1 hy0)).resolve_left Complex.I_ne_zero
  exact (sub_eq_zero.1 hsub).symm

/-- **Positivity detection by states.** An element `a : A` satisfies `0 ≤ a` if and only if
`0 ≤ φ a` for every state `φ` of `A`. Neither a unit in `A` nor prior self-adjointness of `a` is
required. -/
theorem nonneg_iff_forall_mem_stateSpace {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  have ha_sa : IsSelfAdjoint a :=
    isSelfAdjoint_iff_forall_mem_stateSpace.2 fun φ hφ => (h φ hφ).isSelfAdjoint
  by_contra ha_not
  have ha_neg : a⁻ ≠ 0 := fun h0 => ha_not <| by
    rw [← CFC.posPart_sub_negPart a ha_sa, h0, sub_zero]
    exact CFC.posPart_nonneg a
  obtain ⟨ω, hnorm, hpos, hneg⟩ :=
    CStarAlgebra.exists_positiveContinuousLinearMap_apply_posPart_eq_zero ha_neg
  let φ : WeakDual ℂ A := StrongDual.toWeakDual (ω : A →L[ℂ] ℂ)
  have hφ : φ ∈ stateSpace A := ω.toWeakDual_mem_stateSpace_iff.2 hnorm
  have hφa : φ a = -(‖a⁻‖ : ℂ) := by
    change ω a = -(‖a⁻‖ : ℂ)
    conv_lhs => rw [← CFC.posPart_sub_negPart a ha_sa]
    rw [map_sub, hpos, hneg, zero_sub]
  have hre : 0 ≤ (φ a).re := (Complex.le_def.1 (h φ hφ)).1
  rw [hφa, Complex.neg_re, Complex.ofReal_re, Left.nonneg_neg_iff] at hre
  exact (norm_pos_iff.2 ha_neg).not_ge hre

/-- **Order detection by states.** In a C⋆-algebra `A`, `a ≤ b` if and only if `φ a ≤ φ b` for
every state `φ` of `A`. -/
theorem le_iff_forall_mem_stateSpace {a b : A} :
    a ≤ b ↔ ∀ φ ∈ stateSpace A, φ a ≤ φ b := by
  rw [← sub_nonneg, nonneg_iff_forall_mem_stateSpace]
  exact forall₂_congr fun φ _ => by rw [map_sub, sub_nonneg]

/-- **Point separation by states.** Two elements of a C⋆-algebra `A` are equal if and only if every
state of `A` takes the same value on them. -/
theorem eq_iff_forall_mem_stateSpace {a b : A} :
    a = b ↔ ∀ φ ∈ stateSpace A, φ a = φ b := by
  refine ⟨fun h _ _ => h ▸ rfl, fun h => le_antisymm ?_ ?_⟩
  · exact le_iff_forall_mem_stateSpace.2 fun φ hφ => (h φ hφ).le
  · exact le_iff_forall_mem_stateSpace.2 fun φ hφ => (h φ hφ).symm.le

end StateSpace

end TauCeti
