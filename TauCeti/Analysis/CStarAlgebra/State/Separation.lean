/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Extension
public import TauCeti.Analysis.CStarAlgebra.State.Unitization
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Separation of points and order by states, and faithful states

States of a possibly nonunital C⋆-algebra `A` separate points, detect self-adjointness and
positivity, attain the norm on normal elements, and admit norm-convergent countable convex
combinations.

## Main results

For unital `A`:

* `TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum`: for a normal element `a : A` and any
  spectral value `z ∈ spectrum ℂ a`, some state `φ ∈ stateSpace A` satisfies `φ a = z`.

For possibly nonunital `A` (via unitization and restriction from `Unitization ℂ A`):

* `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero` and
  `TauCeti.exists_mem_stateSpace_norm_apply_eq_norm`: for a normal element `a : A`, some state
  attains `‖φ a‖ = ‖a‖`; for `0 ≤ a`, `φ a = ‖a‖`
  (`TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg`); and for arbitrary `a : A`, some state
  satisfies `φ (star a * a) = ‖a‖ ^ 2`
  (`TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq`).
* `TauCeti.stateSpace_nonempty_iff` and `TauCeti.stateSpace_eq_empty_iff`: `stateSpace A` is
  nonempty if and only if `A` is nontrivial.
* `TauCeti.forall_mem_stateSpace_apply_eq_zero_iff`, `TauCeti.forall_mem_stateSpace_apply_eq_iff`,
  `TauCeti.isSelfAdjoint_iff_forall_mem_stateSpace`,
  `TauCeti.nonneg_iff_forall_mem_stateSpace_nonneg`, and `TauCeti.le_iff_forall_mem_stateSpace_le`:
  states separate elements and determine both self-adjointness and the C⋆-algebra order (with no
  nontriviality assumption).
* `TauCeti.toWeakDual_tsum_smul_mem_stateSpace`: any countable or arbitrary `HasSum`-weighted convex
  combination of states in the strong dual defines a state.
* `TauCeti.exists_faithful_mem_stateSpace`: every nonzero separable C⋆-algebra admits a faithful
  state `φ ∈ stateSpace A`, meaning `0 < φ (star a * a)` for all `a ≠ 0`.

## References

* Jesse Peterson, *Notes on operator algebras*, Section 4.1 (Proposition 4.1.6).
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), Theorems 3.3.6–3.3.9.
-/

public section

noncomputable section

open Filter Set WeakDual
open scoped ComplexOrder CStarAlgebra NNReal ENNReal Topology

namespace TauCeti

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Spectral values are attained by states.** For a normal element `a` of a unital C⋆-algebra `A`
and any `z ∈ spectrum ℂ a`, there exists a state `φ ∈ stateSpace A` with `φ a = z`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum {a : A}
    (ha : IsStarNormal a := by cfc_tac) {z : ℂ} (hz : z ∈ spectrum ℂ a) :
    ∃ φ ∈ stateSpace A, φ a = z := by
  let := CStarAlgebra.spectralOrder C(spectrum ℂ a, ℂ)
  have := CStarAlgebra.spectralOrderedRing C(spectrum ℂ a, ℂ)
  let ev := ContinuousMap.evalStarAlgHom ℂ ℂ (⟨z, hz⟩ : spectrum ℂ a)
  let idℂ := StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)
  have hidℂ : idℂ ∈ stateSpace ℂ := by simp [idℂ, stateSpace_complex]
  have hev : pullbackFunctional C(spectrum ℂ a, ℂ) ev idℂ ∈ stateSpace C(spectrum ℂ a, ℂ) :=
    mapsTo_pullbackFunctional_stateSpace ev hidℂ
  obtain ⟨φ, hφ, hres⟩ := surjOn_pullbackFunctional_stateSpace (cfcHom ha) (cfcHom_injective ha) hev
  refine ⟨φ, hφ, ?_⟩
  simpa [ev, idℂ] using congr($hres ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)))

/-- Real spectral values of a self-adjoint element in a unital C⋆-algebra are attained by states. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum_real {a : A}
    (ha : IsSelfAdjoint a := by cfc_tac) {r : ℝ} (hr : r ∈ spectrum ℝ a) :
    ∃ φ ∈ stateSpace A, φ a = r :=
  have := ha.isStarNormal
  exists_mem_stateSpace_apply_eq_of_mem_spectrum ha.isStarNormal (spectrum.algebraMap_mem _ hr)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Norm attainment on nonzero normal elements.** For any nonzero normal element `a` of a
possibly nonunital C⋆-algebra `A`, some state `φ ∈ stateSpace A` satisfies `‖φ a‖ = ‖a‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero {a : A}
    (ha : IsStarNormal a := by cfc_tac) (ha0 : a ≠ 0) :
    ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  have hainr : IsStarNormal (a : Unitization ℂ A) :=
    ⟨by simp [Commute, SemiconjBy, ← Unitization.inr_star, ← Unitization.inr_mul,
      ha.star_comm_self.eq]⟩
  obtain ⟨z, hz, hznorm⟩ :=
    spectrum.exists_nnNorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (a : Unitization ℂ A))
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum hainr hz
  have hza : ‖z‖ = ‖a‖ := by
    have hspec : (‖z‖₊ : ℝ≥0∞) = ‖(a : Unitization ℂ A)‖₊ :=
      hznorm.trans (IsStarNormal.spectralRadius_eq_nnNorm (a : Unitization ℂ A))
    exact (congrArg NNReal.toReal (ENNReal.coe_inj.mp hspec)).trans (Unitization.norm_inr a)
  let φ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  have hφa : ‖φ a‖ = ‖a‖ := by
    simpa [φ, hψa] using hza
  have hanorm : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hle1 : ‖toStrongDual φ‖ ≤ 1 :=
    norm_toStrongDual_pullbackFunctional_inrNonUnitalStarAlgHom_le hψ
  have hge1 : 1 ≤ ‖toStrongDual φ‖ := by
    have hbound : ‖a‖ ≤ ‖toStrongDual φ‖ * ‖a‖ := by
      simpa [hφa] using (toStrongDual φ).le_opNorm a
    exact (le_mul_iff_one_le_left hanorm).1 hbound
  refine ⟨φ, (pullbackFunctional_inrNonUnitalStarAlgHom_mem_stateSpace_iff hψ).2
    (le_antisymm hle1 hge1), hφa⟩

/-- The state space of a possibly nonunital C⋆-algebra `A` is nonempty if and only if `A` is
nontrivial. -/
theorem stateSpace_nonempty_iff : (stateSpace A).Nonempty ↔ Nontrivial A := by
  refine ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun h ↦ ?_⟩
  · contrapose! hφ with hsub
    have hzero : toStrongDual φ = 0 := Subsingleton.elim _ _
    simp [mem_stateSpace_iff, hzero]
  · obtain ⟨x, hx⟩ := exists_ne (0 : A)
    have hx2 : star x * x ≠ 0 := by simpa using hx
    obtain ⟨φ, hφ, -⟩ := exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero
      (IsSelfAdjoint.star_mul_self x).isStarNormal hx2
    exact ⟨φ, hφ⟩

/-- The state space of `A` is empty if and only if `A` is a subsingleton (`A = 0`). -/
theorem stateSpace_eq_empty_iff : stateSpace A = ∅ ↔ Subsingleton A := by
  rw [← not_nonempty_iff_eq_empty, stateSpace_nonempty_iff, not_nontrivial_iff_subsingleton]

/-- **Norm attainment on normal elements.** On a nontrivial C⋆-algebra `A`, every normal element
`a : A` admits a state `φ ∈ stateSpace A` with `‖φ a‖ = ‖a‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_norm [Nontrivial A] (a : A)
    (ha : IsStarNormal a := by cfc_tac) :
    ∃ φ ∈ stateSpace A, ‖φ a‖ = ‖a‖ := by
  by_cases ha0 : a = 0
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty_iff.2 ‹_›
    exact ⟨φ, hφ, by simp [ha0]⟩
  · exact exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero ha ha0

/-- For any nonzero nonnegative element `0 ≤ a`, some state `φ ∈ stateSpace A` satisfies
`φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero {a : A} (ha : 0 ≤ a)
    (ha0 : a ≠ 0) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  obtain ⟨φ, hφ, hnorm⟩ :=
    exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero
      (IsSelfAdjoint.of_nonneg ha).isStarNormal ha0
  refine ⟨φ, hφ, ?_⟩
  rw [Complex.eq_coe_norm_of_nonneg (map_nonneg_of_mem_stateSpace hφ ha), hnorm]

/-- On a nontrivial C⋆-algebra `A`, every nonnegative element `0 ≤ a` admits a state
`φ ∈ stateSpace A` with `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = ‖a‖ := by
  by_cases ha0 : a = 0
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty_iff.2 ‹_›
    exact ⟨φ, hφ, by simp [ha0]⟩
  · exact exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero ha ha0

/-- For any nonzero element `a : A`, some state `φ ∈ stateSpace A` satisfies
`φ (star a * a) = ‖a‖ ^ 2`. -/
theorem exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero {a : A} (ha0 : a ≠ 0) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = (‖a‖ : ℂ) ^ 2 := by
  have hstar0 : star a * a ≠ 0 := by simpa using ha0
  obtain ⟨φ, hφ, hφa⟩ :=
    exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero (star_mul_self_nonneg a) hstar0
  refine ⟨φ, hφ, ?_⟩
  rw [hφa, CStarRing.norm_star_mul_self, ← sq]
  norm_cast

/-- On a nontrivial C⋆-algebra `A`, every element `a : A` admits a state `φ ∈ stateSpace A` with
`φ (star a * a) = ‖a‖ ^ 2`. -/
theorem exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq [Nontrivial A] (a : A) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = (‖a‖ : ℂ) ^ 2 := by
  by_cases ha0 : a = 0
  · obtain ⟨φ, hφ⟩ := stateSpace_nonempty_iff.2 ‹_›
    exact ⟨φ, hφ, by simp [ha0]⟩
  · exact exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero ha0

/-- An element `a : A` satisfies `φ (star a * a) = 0` for all states `φ` if and only if `a = 0`. -/
theorem forall_mem_stateSpace_star_mul_self_eq_zero_iff {a : A} :
    (∀ φ ∈ stateSpace A, φ (star a * a) = 0) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra ha0
    obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero ha0
    have h0 : (‖a‖ : ℂ) ^ 2 = 0 := hφa.symm.trans (h φ hφ)
    exact ha0 (norm_eq_zero.1 (sq_eq_zero_iff.1 (by exact_mod_cast h0)))
  · rintro rfl
    simp

/-- **Separation of points by states.** An element `a : A` vanishes under every state if and only if
`a = 0`. -/
theorem forall_mem_stateSpace_apply_eq_zero_iff {a : A} :
    (∀ φ ∈ stateSpace A, φ a = 0) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hnorm_zero : ∀ {x : A}, IsSelfAdjoint x → (∀ φ ∈ stateSpace A, φ x = 0) → x = 0 := by
      intro x hx hx0
      by_contra hxne
      obtain ⟨φ, hφ, hφx⟩ :=
        exists_mem_stateSpace_norm_apply_eq_norm_of_ne_zero hx.isStarNormal hxne
      exact hxne (norm_eq_zero.1 (by simpa [hx0 φ hφ] using hφx.symm))
    have hre : a + star a = 0 := by
      refine hnorm_zero ?_ fun φ hφ ↦ ?_
      · simp [IsSelfAdjoint, add_comm]
      · simp [map_add, map_star_of_mem_stateSpace hφ, h φ hφ]
    have him : Complex.I • (star a - a) = 0 := by
      refine hnorm_zero ?_ fun φ hφ ↦ ?_
      · rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
          neg_smul, ← smul_neg, neg_sub]
      · simp [map_sub, map_star_of_mem_stateSpace hφ, h φ hφ]
    have hsub : star a - a = 0 := (smul_eq_zero.1 him).resolve_left Complex.I_ne_zero
    have hstar : star a = a := sub_eq_zero.1 hsub
    have h2 : (2 : ℂ) • a = 0 := by
      rw [two_smul]
      simpa [hstar] using hre
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  · rintro rfl
    simp

/-- Two elements of a C⋆-algebra are equal if and only if every state assigns them the same
value. -/
theorem forall_mem_stateSpace_apply_eq_iff {a b : A} :
    (∀ φ ∈ stateSpace A, φ a = φ b) ↔ a = b := by
  rw [← sub_eq_zero, ← forall_mem_stateSpace_apply_eq_zero_iff]
  simp [sub_eq_zero]

/-- **Detection of self-adjointness by states.** An element `a : A` is self-adjoint if and only if
`φ a` is self-adjoint (equivalently real) for every state `φ ∈ stateSpace A`. -/
theorem isSelfAdjoint_iff_forall_mem_stateSpace {a : A} :
    IsSelfAdjoint a ↔ ∀ φ ∈ stateSpace A, IsSelfAdjoint (φ a) := by
  simp only [IsSelfAdjoint]
  rw [← forall_mem_stateSpace_apply_eq_iff]
  exact forall₂_congr fun φ hφ ↦ by rw [map_star_of_mem_stateSpace hφ]

/-- **Detection of positivity by states.** An element `a : A` is nonnegative in the C⋆-algebra order
if and only if `0 ≤ φ a` for every state `φ ∈ stateSpace A`. -/
theorem nonneg_iff_forall_mem_stateSpace_nonneg {a : A} :
    0 ≤ a ↔ ∀ φ ∈ stateSpace A, 0 ≤ φ a := by
  refine ⟨fun ha φ hφ ↦ map_nonneg_of_mem_stateSpace hφ ha, fun h ↦ ?_⟩
  have hsa : IsSelfAdjoint a :=
    isSelfAdjoint_iff_forall_mem_stateSpace.2 fun φ hφ ↦ .of_nonneg (h φ hφ)
  have hsainr : IsSelfAdjoint (a : Unitization ℂ A) := by
    rw [IsSelfAdjoint, ← Unitization.inr_star, hsa.star_eq]
  refine Unitization.inr_nonneg_iff.1
    ((StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℂ) (a : Unitization ℂ A)
      hsainr.isStarNormal).2 fun z hz ↦ ?_)
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum hsainr.isStarNormal hz
  let φ₀ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  by_cases hφ₀ : φ₀ = 0
  · have hz0 : z = 0 := by simpa [φ₀, hψa] using congr(toStrongDual $hφ₀ a)
    simp [hz0]
  · have hmem := inv_norm_smul_pullbackFunctional_inrNonUnitalStarAlgHom_mem_stateSpace hψ hφ₀
    have hpos : 0 < ‖toStrongDual φ₀‖ :=
      norm_pos_iff.2 fun h0 ↦ hφ₀ (toStrongDual.injective (by simpa using h0))
    have hval : 0 ≤ (‖toStrongDual φ₀‖⁻¹ : ℝ) • z := by
      simpa [φ₀, hψa] using h _ hmem
    have hcancel := smul_nonneg hpos.le hval
    rwa [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at hcancel

/-- States determine the partial order on a C⋆-algebra: `a ≤ b` if and only if `φ a ≤ φ b` for
every state `φ ∈ stateSpace A`. -/
theorem le_iff_forall_mem_stateSpace_le {a b : A} :
    a ≤ b ↔ ∀ φ ∈ stateSpace A, φ a ≤ φ b := by
  rw [← sub_nonneg, nonneg_iff_forall_mem_stateSpace_nonneg]
  simp [sub_nonneg]

section ConvexSeries

omit [StarOrderedRing A] in
/-- A family of states weighted by nonnegative scalars of sum `1` is summable in the strong dual. -/
theorem summable_smul_toStrongDual_of_mem_stateSpace {ι : Type*} {φ : ι → WeakDual ℂ A}
    (hφ : ∀ i, φ i ∈ stateSpace A) {w : ι → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : HasSum w 1) :
    Summable fun i ↦ w i • toStrongDual (φ i) := by
  refine .of_norm_bounded hw_sum.summable fun i ↦ ?_
  rw [norm_smul, Real.norm_of_nonneg (hw_nonneg i), norm_toStrongDual_of_mem_stateSpace (hφ i),
    mul_one]

omit [StarOrderedRing A] in
/-- On a nonnegative element `a`, a weighted sum of states evaluates to the real series
`∑' i, w i * ‖φ i a‖`. -/
private theorem tsum_smul_toStrongDual_apply_of_nonneg {ι : Type*} {φ : ι → WeakDual ℂ A}
    (hφ : ∀ i, φ i ∈ stateSpace A) {w : ι → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : HasSum w 1) {a : A} (ha : 0 ≤ a) :
    (∑' i, w i • toStrongDual (φ i)) a = ((∑' i, w i * ‖φ i a‖ : ℝ) : ℂ) := by
  have hsum := summable_smul_toStrongDual_of_mem_stateSpace hφ hw_nonneg hw_sum
  have hterm (i : ι) : (w i • toStrongDual (φ i)) a = ((w i * ‖φ i a‖ : ℝ) : ℂ) := by
    simp only [smul_apply, toStrongDual_apply, Complex.real_smul, Complex.ofReal_mul]
    rw [← Complex.eq_coe_norm_of_nonneg (map_nonneg_of_mem_stateSpace (hφ i) ha)]
  have hsum_real : Summable fun i ↦ w i * ‖φ i a‖ :=
    .of_nonneg_of_le (fun i ↦ mul_nonneg (hw_nonneg i) (norm_nonneg _))
      (fun i ↦ mul_le_mul_of_nonneg_left (norm_apply_le_of_mem_stateSpace (hφ i) a) (hw_nonneg i))
      (hw_sum.summable.mul_right ‖a‖)
  calc
    (∑' i, w i • toStrongDual (φ i)) a
        = ∑' i, (w i • toStrongDual (φ i)) a := (ContinuousLinearMap.apply ℂ ℂ a).map_tsum hsum
    _ = ∑' i, ((w i * ‖φ i a‖ : ℝ) : ℂ) := tsum_congr hterm
    _ = ((∑' i, w i * ‖φ i a‖ : ℝ) : ℂ) := (Complex.ofRealCLM.map_tsum hsum_real).symm

/-- **Countable / infinite convex combinations of states.** If `φ : ι → WeakDual ℂ A` is a family
of states and `w : ι → ℝ` is a nonnegative weight family with `HasSum w 1`, then the norm-convergent
series `∑' i, w i • toStrongDual (φ i)` defines a state of `A`. -/
theorem toWeakDual_tsum_smul_mem_stateSpace {ι : Type*} {φ : ι → WeakDual ℂ A}
    (hφ : ∀ i, φ i ∈ stateSpace A) {w : ι → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : HasSum w 1) :
    StrongDual.toWeakDual (∑' i, w i • toStrongDual (φ i)) ∈ stateSpace A := by
  set Φ : A →L[ℂ] ℂ := ∑' i, w i • toStrongDual (φ i)
  refine mem_stateSpace_iff.2 ⟨fun a ha ↦ ?_, ?_⟩
  · simp only [StrongDual.toWeakDual_apply, Φ,
      tsum_smul_toStrongDual_apply_of_nonneg hφ hw_nonneg hw_sum ha, Complex.zero_le_real]
    exact tsum_nonneg fun i ↦ mul_nonneg (hw_nonneg i) (norm_nonneg _)
  · simp only [StrongDual.toStrongDual_toWeakDual]
    refine le_antisymm ?_ (le_of_tendsto' hw_sum fun s ↦ ?_)
    · have hnorm (i : ι) : ‖w i • toStrongDual (φ i)‖ = w i := by
        rw [norm_smul, Real.norm_of_nonneg (hw_nonneg i),
          norm_toStrongDual_of_mem_stateSpace (hφ i), mul_one]
      exact (norm_tsum_le_tsum_norm (hw_sum.summable.congr fun i ↦ (hnorm i).symm)).trans_eq
        ((tsum_congr hnorm).trans hw_sum.tsum_eq)
    · have hl := CStarAlgebra.increasingApproximateUnit A
      have := hl.neBot
      have hlim : Tendsto (fun e : A ↦ ∑ i ∈ s, w i * ‖φ i e‖)
          (CStarAlgebra.approximateUnit A) (𝓝 (∑ i ∈ s, w i)) := by
        refine tendsto_finsetSum s fun i _ ↦ ?_
        have h1 : Tendsto (fun e : A ↦ φ i e) (CStarAlgebra.approximateUnit A) (𝓝 (1 : ℂ)) := by
          simpa [norm_toStrongDual_of_mem_stateSpace (hφ i)] using
            tendsto_approximateUnit_norm_of_map_nonneg
              (fun a ha ↦ map_nonneg_of_mem_stateSpace (hφ i) ha)
        simpa using h1.norm.const_mul (w i)
      refine le_of_tendsto hlim ?_
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he_nonneg he_norm
      have hsum_e : Summable fun i ↦ w i * ‖φ i e‖ :=
        .of_nonneg_of_le (fun i ↦ mul_nonneg (hw_nonneg i) (norm_nonneg _))
          (fun i ↦ mul_le_mul_of_nonneg_left (norm_apply_le_of_mem_stateSpace (hφ i) e)
            (hw_nonneg i))
          (hw_sum.summable.mul_right ‖e‖)
      calc
        ∑ i ∈ s, w i * ‖φ i e‖
            ≤ ∑' i, w i * ‖φ i e‖ :=
              hsum_e.sum_le_tsum s fun i _ ↦ mul_nonneg (hw_nonneg i) (norm_nonneg _)
        _ ≤ ‖((∑' i, w i * ‖φ i e‖ : ℝ) : ℂ)‖ := by
              rw [Complex.norm_real]
              exact le_abs_self _
        _ = ‖Φ e‖ := by
              rw [← tsum_smul_toStrongDual_apply_of_nonneg hφ hw_nonneg hw_sum he_nonneg]
        _ ≤ ‖Φ‖ * ‖e‖ := Φ.le_opNorm e
        _ ≤ ‖Φ‖ := mul_le_of_le_one_right (norm_nonneg Φ) he_norm

/-- **Existence of a faithful state on a separable C⋆-algebra.** Every nonzero separable C⋆-algebra
`A` (possibly nonunital) admits a state `φ ∈ stateSpace A` that is faithful in the sense that
`0 < φ (star a * a)` for every nonzero `a : A`. -/
theorem exists_faithful_mem_stateSpace [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ φ ∈ stateSpace A, ∀ a ≠ 0, 0 < φ (star a * a) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  choose φ hφ hφd using fun n ↦ exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq (d n)
  let w : ℕ → ℝ := fun n ↦ 1 / 2 / 2 ^ n
  have hw_pos (n : ℕ) : 0 < w n := by positivity
  have hw_nonneg (n : ℕ) : 0 ≤ w n := (hw_pos n).le
  have hw_sum : HasSum w 1 := hasSum_geometric_two' 1
  refine ⟨StrongDual.toWeakDual (∑' n, w n • toStrongDual (φ n)),
    toWeakDual_tsum_smul_mem_stateSpace hφ hw_nonneg hw_sum, fun a ha ↦ ?_⟩
  have hopen : IsOpen {x : A | ‖star x * x - star a * a‖ < ‖x‖ ^ 2} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  obtain ⟨n, hn⟩ := hd.exists_mem_open hopen ⟨a, by simpa using sq_pos_of_pos (norm_pos_iff.2 ha)⟩
  have hφn_ne : φ n (star a * a) ≠ 0 := by
    intro h0
    have h1 : ‖φ n (star (d n) * d n)‖ = ‖d n‖ ^ 2 := by
      rw [hφd n]
      norm_cast
      exact abs_of_nonneg (sq_nonneg _)
    have h2 : ‖φ n (star (d n) * d n)‖ ≤ ‖star (d n) * d n - star a * a‖ := by
      simpa [h0, map_sub] using
        norm_apply_le_of_mem_stateSpace (hφ n) (star (d n) * d n - star a * a)
    exact (not_le_of_gt hn) (h1 ▸ h2)
  have hsum_real : Summable fun k ↦ w k * ‖φ k (star a * a)‖ :=
    .of_nonneg_of_le (fun k ↦ mul_nonneg (hw_nonneg k) (norm_nonneg _))
      (fun k ↦ mul_le_mul_of_nonneg_left
        (norm_apply_le_of_mem_stateSpace (hφ k) (star a * a)) (hw_nonneg k))
      (hw_sum.summable.mul_right ‖star a * a‖)
  rw [StrongDual.toWeakDual_apply,
    tsum_smul_toStrongDual_apply_of_nonneg hφ hw_nonneg hw_sum (star_mul_self_nonneg a),
    Complex.zero_lt_real]
  exact hsum_real.tsum_pos (fun k ↦ mul_nonneg (hw_nonneg k) (norm_nonneg _)) n
    (mul_pos (hw_pos n) (norm_pos_iff.2 hφn_ne))

end ConvexSeries

end NonUnital

end TauCeti
