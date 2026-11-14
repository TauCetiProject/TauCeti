/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Extension
import TauCeti.Analysis.CStarAlgebra.State.Unitization
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Separation of points, norms, and positivity by states

States of a possibly nonunital C⋆-algebra `A` recover its norm on normal elements, detect
self-adjointness and positivity, and separate points.

For a unital C⋆-algebra `B` and a normal element `b : B`, every point `z ∈ spectrum ℂ b` is
attained by a state of `B` (`TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum`), combining
Gelfand duality (`WeakDual.CharacterSpace.mem_spectrum_iff_exists`) on the elemental subalgebra
with Hahn–Banach state extension (`StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`).
Passing to the minimal unitization `A⁺¹` and restricting norm-attaining states back to `A` via
`TauCeti.pullbackFunctional_inr_mem_stateSpace_of_norm_apply_eq_norm` extends norm attainment and
separation to every C⋆-algebra `A`, without assuming a unit or nontriviality:

* `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm`: for normal `a`, a state attains `‖a‖` in
  modulus.
* `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg`: for `0 ≤ a`, a state takes the value
  `‖a‖` at `a`.
* `TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq`: a state takes the value
  `‖a‖ ^ 2` at `star a * a`.
* `TauCeti.stateSpace_nonempty_iff`: `A` admits a state if and only if `A` is nontrivial.
* `TauCeti.norm_eq_iSup_norm_apply_stateSpace`: for normal `a`, `‖a‖ = ⨆ φ : stateSpace A, ‖φ a‖`.
* `TauCeti.eq_zero_of_forall_mem_stateSpace_apply_eq_zero`,
  `TauCeti.eq_of_forall_mem_stateSpace_apply_eq`, and `TauCeti.forall_mem_stateSpace_apply_eq_iff`:
  states separate all elements of `A`.
* `TauCeti.isSelfAdjoint_iff_forall_mem_stateSpace` and
  `TauCeti.nonneg_iff_forall_mem_stateSpace`: an element `a : A` is self-adjoint (respectively
  nonnegative) if and only if `φ a` is self-adjoint (respectively nonnegative) for every state `φ`.

## References

* J. Peterson, *Notes on Operator Algebras*, Propositions 4.1.4 and 4.1.5, p. 56.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.3.6.
-/

public section

open Set WeakDual
open scoped CStarAlgebra ComplexOrder NNReal ENNReal

namespace TauCeti

section Unital

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Spectral attainment by states.** For a normal element `b` of a unital C⋆-algebra `B`, every
spectral value `z ∈ spectrum ℂ b` is attained by some state `φ ∈ stateSpace B`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum (b : B) [IsStarNormal b] {z : ℂ}
    (hz : z ∈ spectrum ℂ b) : ∃ φ ∈ stateSpace B, φ b = z := by
  let S := StarAlgebra.elemental ℂ b
  have : IsClosed (S : Set B) := StarAlgebra.elemental.isClosed ℂ b
  let bS : S := ⟨b, StarAlgebra.elemental.self_mem ℂ b⟩
  -- View `z` in the spectrum of `b` inside the commutative C⋆-subalgebra `S`, get a character
  -- attaining `z` by Gelfand duality, and extend that character state to `B`.
  have hzS : z ∈ spectrum ℂ bS := by rwa [StarSubalgebra.mem_spectrum_iff]
  obtain ⟨χ, hχ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.1 hzS
  have hid : StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ) ∈ stateSpace ℂ := by
    simp [stateSpace_complex]
  have hχ_state : pullbackFunctional S χ (StrongDual.toWeakDual (.id ℂ ℂ)) ∈ stateSpace S :=
    mapsTo_pullbackFunctional_stateSpace χ hid
  obtain ⟨φ, hφ, hφS⟩ := StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq S hχ_state
  exact ⟨φ, hφ, (hφS bS).trans (by simpa using hχ)⟩

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Norm attainment on normal elements.** For any nonzero normal element `a` of a possibly
nonunital C⋆-algebra `A`, there is a state `φ ∈ stateSpace A` with `‖φ a‖ = ‖a‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero {a : A} [IsStarNormal a]
    (ha : a ≠ 0) : ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  obtain ⟨z, hz, hz_norm⟩ :=
    spectrum.exists_nnNorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (a : A⁺¹))
  have hz_eq : ‖z‖ = ‖a‖ := by
    have hspec : (‖z‖₊ : ℝ≥0∞) = ‖(a : A⁺¹)‖₊ :=
      hz_norm.trans (IsStarNormal.spectralRadius_eq_nnNorm (a : A⁺¹))
    exact (congr_arg NNReal.toReal (ENNReal.coe_inj.1 hspec)).trans (Unitization.norm_inr a)
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : A⁺¹) hz
  have hψ_norm : ‖ψ (a : A⁺¹)‖ = ‖a‖ := by rw [hψa, hz_eq]
  exact ⟨pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ,
    pullbackFunctional_inr_mem_stateSpace_of_norm_apply_eq_norm hψ ha hψ_norm,
    by simpa using hψ_norm⟩

/-- **Norm attainment on nonnegative elements.** For any nonzero nonnegative element `a` of a
possibly nonunital C⋆-algebra `A`, there is a state `φ ∈ stateSpace A` with `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero {a : A} (ha : 0 ≤ a)
    (ha0 : a ≠ 0) : ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  have ha_inr : 0 ≤ (a : A⁺¹) := Unitization.inr_nonneg_iff.2 ha
  have : IsStarNormal (a : A⁺¹) := ha_inr.isSelfAdjoint.isStarNormal
  have hmem : (‖a‖ : ℂ) ∈ spectrum ℂ (a : A⁺¹) := by
    simpa [Unitization.norm_inr] using
      spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg (a : A⁺¹) ha_inr)
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : A⁺¹) hmem
  have hψ_norm : ‖ψ (a : A⁺¹)‖ = ‖a‖ := by
    rw [hψa, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a)]
  exact ⟨pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ,
    pullbackFunctional_inr_mem_stateSpace_of_norm_apply_eq_norm hψ ha0 hψ_norm,
    by simpa using hψa⟩

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

/-- On a nontrivial C⋆-algebra, every normal element `a` (including `0`) has a state attaining
`‖a‖` in modulus. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty_iff.2 ‹Nontrivial A›
    exact ⟨φ, hφ, by simp⟩
  · exact exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero ha

/-- On a nontrivial C⋆-algebra, every nonnegative element `a` (including `0`) has a state taking
the value `‖a‖` at `a`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty_iff.2 ‹Nontrivial A›
    exact ⟨φ, hφ, by simp⟩
  · exact exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero ha ha0

/-- On a nontrivial C⋆-algebra, every element `a` has a state taking the value `‖a‖ ^ 2` at
`star a * a`. -/
theorem exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq [Nontrivial A] (a : A) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = ‖a‖ ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty_iff.2 ‹Nontrivial A›
    exact ⟨φ, hφ, by simp⟩
  · exact exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero ha

/-- **Norm recovery from states.** For every normal element `a` of a C⋆-algebra `A` (possibly
nonunital or trivial), `‖a‖` is the supremum of `‖φ a‖` over all states `φ ∈ stateSpace A`. -/
theorem norm_eq_iSup_norm_apply_stateSpace (a : A) [IsStarNormal a] :
    ‖a‖ = ⨆ φ : stateSpace A, ‖φ.1 a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [Real.iSup_const_zero]
  · have hbdd : BddAbove (range fun φ : stateSpace A => ‖φ.1 a‖) :=
      ⟨‖a‖, by rintro _ ⟨φ, rfl⟩; exact norm_apply_le_of_mem_stateSpace φ.2 a⟩
    obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero ha
    refine le_antisymm ?_ (Real.iSup_le (fun ψ => norm_apply_le_of_mem_stateSpace ψ.2 a)
      (norm_nonneg a))
    exact hφa ▸ le_ciSup hbdd ⟨φ, hφ⟩

/-- If `φ (star a * a) = 0` for every state `φ` of `A`, then `a = 0`. -/
theorem eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero {a : A}
    (h : ∀ φ ∈ stateSpace A, φ (star a * a) = 0) : a = 0 := by
  by_contra ha
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero ha
  have hzero : (‖a‖ ^ 2 : ℂ) = 0 := hφa.symm.trans (h φ hφ)
  exact ha (norm_eq_zero.1 (Complex.ofReal_eq_zero.1 (sq_eq_zero_iff.1 hzero)))

/-- **State separation of zero.** If `φ a = 0` for every state `φ` of `A`, then `a = 0`. -/
theorem eq_zero_of_forall_mem_stateSpace_apply_eq_zero {a : A}
    (h : ∀ φ ∈ stateSpace A, φ a = 0) : a = 0 := by
  have hsa (x : selfAdjoint A) (hx : ∀ φ : stateSpace A, φ.1 x = 0) : (x : A) = 0 := by
    have : IsStarNormal (x : A) := x.2.isStarNormal
    exact norm_eq_zero.1 <| by simp [norm_eq_iSup_norm_apply_stateSpace (x : A), hx,
      Real.iSup_const_zero]
  rw [← realPart_add_I_smul_imaginaryPart a,
    hsa (realPart a) fun φ => by
      simpa [h φ.1 φ.2] using map_realPart (StateSpace.toPositiveLinearMap φ) a,
    hsa (imaginaryPart a) fun φ => by
      simpa [h φ.1 φ.2] using map_imaginaryPart (StateSpace.toPositiveLinearMap φ) a,
    smul_zero, add_zero]

/-- An element `a` of a C⋆-algebra is zero if and only if every state vanishes on `a`. -/
@[simp]
theorem forall_mem_stateSpace_apply_eq_zero_iff {a : A} :
    (∀ φ ∈ stateSpace A, φ a = 0) ↔ a = 0 :=
  ⟨eq_zero_of_forall_mem_stateSpace_apply_eq_zero, by rintro rfl φ _; simp⟩

/-- **States separate points.** Two elements of a C⋆-algebra are equal if every state takes the
same value on them. -/
theorem eq_of_forall_mem_stateSpace_apply_eq {a b : A}
    (h : ∀ φ ∈ stateSpace A, φ a = φ b) : a = b :=
  sub_eq_zero.1 <| eq_zero_of_forall_mem_stateSpace_apply_eq_zero fun φ hφ => by
    rw [map_sub, h φ hφ, sub_self]

/-- Two elements of a C⋆-algebra are equal if and only if every state takes the same value on
them. -/
@[simp]
theorem forall_mem_stateSpace_apply_eq_iff {a b : A} :
    (∀ φ ∈ stateSpace A, φ a = φ b) ↔ a = b :=
  ⟨eq_of_forall_mem_stateSpace_apply_eq, fun h _ _ => h ▸ rfl⟩

/-- **Detection of self-adjointness by states.** An element `a` of a C⋆-algebra is self-adjoint if
and only if `φ a` is self-adjoint (real) for every state `φ`. -/
theorem isSelfAdjoint_iff_forall_mem_stateSpace {a : A} :
    IsSelfAdjoint a ↔ ∀ φ ∈ stateSpace A, IsSelfAdjoint (φ a) := by
  refine ⟨fun ha φ hφ => isSelfAdjoint_apply_of_mem_stateSpace hφ ha, fun h => ?_⟩
  rw [isSelfAdjoint_iff]
  refine eq_of_forall_mem_stateSpace_apply_eq fun φ hφ => ?_
  rw [map_star_of_mem_stateSpace hφ, (h φ hφ).star_eq]

/-- **Detection of positivity by states.** An element `a` of a C⋆-algebra is nonnegative (`0 ≤ a`)
if and only if `0 ≤ φ a` for every state `φ`. No self-adjointness hypothesis on `a` is needed. -/
theorem nonneg_iff_forall_mem_stateSpace {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ => map_nonneg_of_mem_stateSpace hφ ha, fun h => ?_⟩
  have ha_sa : IsSelfAdjoint a :=
    isSelfAdjoint_iff_forall_mem_stateSpace.2 fun φ hφ => (h φ hφ).isSelfAdjoint
  -- Pass to `A⁺¹`: any state `ψ` of `A⁺¹` restricts to a multiple of a state of `A` (or to `0`),
  -- so `0 ≤ ψ a` holds on all of `stateSpace A⁺¹`, making the real spectrum of `(a : A⁺¹)`
  -- nonnegative.
  have hunit (ψ : WeakDual ℂ A⁺¹) (hψ : ψ ∈ stateSpace A⁺¹) : 0 ≤ ψ (a : A⁺¹) := by
    set φ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
    by_cases hφ0 : φ = 0
    · simpa [φ] using (DFunLike.congr_fun (congr_arg toStrongDual hφ0) a).ge
    · have hpos : 0 < ‖toStrongDual φ‖ := by simp [hφ0]
      have hcφ := h _ (inv_norm_toStrongDual_smul_mem_stateSpace
        (fun _ => map_nonneg_pullbackFunctional_inr_of_mem_stateSpace hψ) hφ0)
      simpa [-Complex.real_smul, φ, smul_smul, mul_inv_cancel₀ hpos.ne'] using
        smul_nonneg hpos.le hcφ
  rw [← Unitization.inr_nonneg_iff]
  have ha_inr_sa : IsSelfAdjoint (a : A⁺¹) := ha_sa.inr ℂ
  have : IsStarNormal (a : A⁺¹) := ha_inr_sa.isStarNormal
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : A⁺¹) ha_inr_sa]
  intro r hr
  have hrc : (r : ℂ) ∈ spectrum ℂ (a : A⁺¹) := by simpa using spectrum.algebraMap_mem ℂ hr
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : A⁺¹) hrc
  exact Complex.zero_le_real.1 (hψa ▸ hunit ψ hψ)

end NonUnital

end TauCeti
