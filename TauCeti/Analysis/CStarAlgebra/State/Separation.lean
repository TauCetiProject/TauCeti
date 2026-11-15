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

States on a possibly nonunital C⋆-algebra `A` separate elements, detect self-adjointness and the
order, and attain the norm of every normal element. When `A` is separable and nonzero, a countable
convex combination of states produces a single faithful state.

## Main results

* `TauCeti.unitizeFunctional`, `TauCeti.unitizeFunctional_mem_stateSpace_iff`: extending a
  functional `φ : WeakDual ℂ A` to `Unitization ℂ A` by `x ↦ x.fst + φ x.snd` yields a state of the
  unitization if and only if `φ` is positive and contractive.
* `TauCeti.characterSpace_subset_stateSpace`: characters of a commutative unital C⋆-algebra are
  states.
* `TauCeti.exists_mem_stateSpace_apply_eq_of_mem_spectrum` and
  `TauCeti.exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq`: on a unital C⋆-algebra, every
  spectral value of a normal element is attained by a state; when `A` is nontrivial, some state
  attains a spectral value of maximum modulus `‖x‖`.
* `TauCeti.exists_mem_stateSpace_norm_apply_eq_of_ne_zero`,
  `TauCeti.exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero`, and
  `TauCeti.exists_mem_stateSpace_star_mul_self_eq_norm_sq`: for possibly nonunital `A`, states
  attain `‖x‖` on nonzero normal elements, `‖a‖` on nonzero positive elements, and `‖a‖ ^ 2` on
  `star a * a` for every nonzero `a : A`. In particular, `TauCeti.stateSpace_nonempty_of_nontrivial`
  gives existence of states without assuming a unit.
* `TauCeti.eq_zero_iff_forall_mem_stateSpace`, `TauCeti.eq_iff_forall_mem_stateSpace`,
  `TauCeti.isSelfAdjoint_iff_forall_mem_stateSpace`, `TauCeti.nonneg_iff_forall_mem_stateSpace`, and
  `TauCeti.le_iff_forall_mem_stateSpace`: states separate points and detect self-adjointness and the
  C⋆-order.
* `TauCeti.toWeakDual_tsum_mem_stateSpace`, `TauCeti.exists_mem_stateSpace_faithful`,
  `TauCeti.exists_positiveLinearMap_norm_eq_one_faithful`: countable convex combinations of states
  are states, and every nonzero separable C⋆-algebra admits a faithful state.

## References

* Jesse Peterson, *Notes on operator algebras*, Propositions 4.1.2, 4.1.4, and 4.1.5.
* Gerard J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open Filter Set WeakDual
open scoped ComplexOrder ComplexStarModule Topology

namespace TauCeti

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Extend a continuous linear functional `φ : WeakDual ℂ A` to the minimal unitization
`Unitization ℂ A` by sending `(w, a)` to `w + φ a`. -/
noncomputable def unitizeFunctional (φ : WeakDual ℂ A) : WeakDual ℂ (Unitization ℂ A) :=
  StrongDual.toWeakDual
    { toFun x := x.fst + φ x.snd
      map_add' x y := by
        simp only [Unitization.fst_add, Unitization.snd_add, map_add]
        ring
      map_smul' c x := by
        simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul, smul_eq_mul,
          RingHom.id_apply]
        ring
      cont := by fun_prop }

@[simp]
theorem unitizeFunctional_apply (φ : WeakDual ℂ A) (x : Unitization ℂ A) :
    unitizeFunctional φ x = x.fst + φ x.snd :=
  (rfl)

theorem unitizeFunctional_inr (φ : WeakDual ℂ A) (a : A) :
    unitizeFunctional φ (a : Unitization ℂ A) = φ a := by
  simp

theorem unitizeFunctional_one (φ : WeakDual ℂ A) :
    unitizeFunctional φ 1 = 1 := by
  simp

variable [PartialOrder A] [StarOrderedRing A]

@[simp]
theorem pullbackFunctional_inr_unitizeFunctional (φ : WeakDual ℂ A) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) (unitizeFunctional φ) = φ :=
  DFunLike.ext _ _ fun a ↦ by simp

private theorem unitizeFunctional_star_mul_self_nonneg {φ : WeakDual ℂ A}
    (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) (hnorm : ‖toStrongDual φ‖ ≤ 1) (y : Unitization ℂ A) :
    0 ≤ unitizeFunctional φ (star y * y) := by
  set w : ℂ := y.fst
  set b : A := y.snd
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h1 : Tendsto (fun e : A ↦ φ (e * b)) (CStarAlgebra.approximateUnit A) (𝓝 (φ b)) := by
    simpa [Function.comp_def] using
      ((toStrongDual φ).continuous.tendsto b).comp (hl.tendsto_mul_right b)
  have h2 : Tendsto (fun e : A ↦ φ (star b * e)) (CStarAlgebra.approximateUnit A)
      (𝓝 (φ (star b))) := by
    simpa [Function.comp_def] using
      ((toStrongDual φ).continuous.tendsto (star b)).comp (hl.tendsto_mul_left (star b))
  have hlim : Tendsto
      (fun e : A ↦ star w * w + star w * φ (e * b) + w * φ (star b * e) + φ (star b * b))
      (CStarAlgebra.approximateUnit A) (𝓝 (unitizeFunctional φ (star y * y))) := by
    have htarget : star w * w + star w * φ b + w * φ (star b) + φ (star b * b) =
        unitizeFunctional φ (star y * y) := by
      simp only [unitizeFunctional_apply, Unitization.fst_mul, Unitization.fst_star,
        Unitization.snd_mul, Unitization.snd_star, map_add, map_smul, smul_eq_mul, w, b]
      ring
    exact htarget ▸
      (((tendsto_const_nhds.add (h1.const_mul _)).add (h2.const_mul _)).add tendsto_const_nhds)
  refine ge_of_tendsto hlim ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he0 he1
  have he_sa : star e = e := he0.isSelfAdjoint.star_eq
  have he2_pos : 0 ≤ φ (e * e) := hpos (e * e) (by nth_rw 1 [← he_sa]; exact star_mul_self_nonneg e)
  have he2_le_one : φ (e * e) ≤ 1 := by
    have hle : ‖φ (e * e)‖ ≤ 1 :=
      ((toStrongDual φ).le_opNorm _).trans <|
        (mul_le_mul hnorm (norm_mul_le e e) (norm_nonneg _) zero_le_one).trans
          (by nlinarith [norm_nonneg e])
    exact Complex.le_def.2 ⟨(Complex.re_le_norm _).trans (by simpa using hle),
      by simpa using (Complex.nonneg_iff.1 he2_pos).2.symm⟩
  have hze : 0 ≤ φ (star (w • e + b) * (w • e + b)) := hpos _ (star_mul_self_nonneg _)
  have hmul : star (w • e + b) * (w • e + b) =
      (star w * w) • (e * e) + star w • (e * b) + w • (star b * e) + star b * b := by
    simp only [star_add, star_smul, he_sa, add_mul, mul_add, smul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm w (star w)]
    abel
  rw [hmul, map_add, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at hze
  exact hze.trans (add_le_add (add_le_add (add_le_add
    (mul_le_of_le_one_right (star_mul_self_nonneg w) he2_le_one) le_rfl) le_rfl) le_rfl)

/-- The unitization extension `unitizeFunctional φ` is a state of `Unitization ℂ A` if and only if
`φ` is nonnegative on nonnegative elements and has norm at most one. -/
theorem unitizeFunctional_mem_stateSpace_iff {φ : WeakDual ℂ A} :
    unitizeFunctional φ ∈ stateSpace (Unitization ℂ A) ↔
      (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1 := by
  rw [mem_stateSpace_iff_map_one]
  refine ⟨fun ⟨hpos, _⟩ ↦ ⟨fun a ha ↦ ?_, ?_⟩, fun ⟨hpos, hnorm⟩ ↦ ⟨fun x hx ↦ ?_, by simp⟩⟩
  · simpa using hpos (a : Unitization ℂ A) (Unitization.inr_nonneg_iff.2 ha)
  · refine (toStrongDual φ).opNorm_le_bound zero_le_one fun a ↦ ?_
    have hstate : unitizeFunctional φ ∈ stateSpace (Unitization ℂ A) :=
      mem_stateSpace_iff_map_one.2 ⟨hpos, by simp⟩
    simpa [Unitization.norm_inr] using
      norm_apply_le_of_mem_stateSpace hstate (a : Unitization ℂ A)
  · rw [StarOrderedRing.nonneg_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact unitizeFunctional_star_mul_self_nonneg hpos hnorm y
    | zero => simp
    | add _ _ _ _ hu hv => simpa only [map_add] using add_nonneg hu hv

/-- Every state of `A` extends via `unitizeFunctional` to a state of `Unitization ℂ A`. -/
theorem unitizeFunctional_mem_stateSpace {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) :
    unitizeFunctional φ ∈ stateSpace (Unitization ℂ A) :=
  unitizeFunctional_mem_stateSpace_iff.2
    ⟨fun _ ↦ map_nonneg_of_mem_stateSpace hφ, (norm_toStrongDual_of_mem_stateSpace hφ).le⟩

end Unitization

section Unital

/-- Every character of a commutative unital C⋆-algebra is a state. -/
theorem characterSpace_subset_stateSpace {B : Type*} [CommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] :
    (WeakDual.characterSpace ℂ B : Set (WeakDual ℂ B)) ⊆ stateSpace B := by
  intro φ hφ
  let χ : WeakDual.characterSpace ℂ B := ⟨φ, hφ⟩
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha ↦ ?_, map_one χ⟩
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    change 0 ≤ χ (star y * y)
    rw [map_mul, map_star]
    exact star_mul_self_nonneg (χ y)
  | zero => simp
  | add _ _ _ _ hx hy => simpa only [map_add] using add_nonneg hx hy

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Spectral values of normal elements are attained by states.** For a normal element `x` of a
unital C⋆-algebra `A` and `z ∈ spectrum ℂ x`, some state `φ` of `A` satisfies `φ x = z`. -/
theorem exists_mem_stateSpace_apply_eq_of_mem_spectrum (x : A) [IsStarNormal x] {z : ℂ}
    (hz : z ∈ spectrum ℂ x) : ∃ φ ∈ stateSpace A, φ x = z := by
  let S : StarSubalgebra ℂ A := StarAlgebra.elemental ℂ x
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ x
  let χ : WeakDual.characterSpace ℂ S :=
    (StarAlgebra.elemental.characterSpaceHomeo x).symm ⟨z, hz⟩
  have hχx : χ ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩ = z :=
    congrArg Subtype.val ((StarAlgebra.elemental.characterSpaceHomeo x).apply_symm_apply ⟨z, hz⟩)
  obtain ⟨φ, hφ, hφ_ext⟩ := StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq S
    (characterSpace_subset_stateSpace χ.prop)
  exact ⟨φ, hφ, (hφ_ext ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩).trans hχx⟩

/-- On a nontrivial unital C⋆-algebra, every normal element `x` admits a state `φ` such that
`φ x ∈ spectrum ℂ x` and `‖φ x‖ = ‖x‖`. -/
theorem exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq [Nontrivial A] (x : A)
    [IsStarNormal x] : ∃ φ ∈ stateSpace A, φ x ∈ spectrum ℂ x ∧ ‖φ x‖ = ‖x‖ := by
  obtain ⟨z, hz, hnorm⟩ := spectrum.exists_nnNorm_eq_spectralRadius x
  rw [IsStarNormal.spectralRadius_eq_nnNorm, ENNReal.coe_inj] at hnorm
  obtain ⟨φ, hφ, hφx⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum x hz
  exact ⟨φ, hφ, hφx ▸ hz, by simpa [hφx] using congrArg NNReal.toReal hnorm⟩

/-- On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `φ` with
`φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a) :
    ∃ φ ∈ stateSpace A, φ a = (‖a‖ : ℂ) := by
  have := ha.isSelfAdjoint.isStarNormal
  obtain ⟨φ, hφ, -, hnorm⟩ := exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq a
  have hpos := map_nonneg_of_mem_stateSpace hφ ha
  refine ⟨φ, hφ, ?_⟩
  rw [← hnorm, ← Complex.re_eq_norm.2 hpos]
  exact Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hpos)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every state preserves the involution: `φ (star a) = star (φ a)`. -/
theorem map_star_of_mem_stateSpace {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) (a : A) :
    φ (star a) = star (φ a) := by
  obtain ⟨ω, -, rfl⟩ := mem_stateSpace_iff_exists_positiveLinearMap.1 hφ
  exact map_star ω a

/-- For a nonzero normal element `x` of a possibly nonunital C⋆-algebra `A`, some state `φ` of `A`
satisfies `‖φ x‖ = ‖x‖`. -/
theorem exists_mem_stateSpace_norm_apply_eq_of_ne_zero {x : A} [IsStarNormal x] (hx : x ≠ 0) :
    ∃ φ ∈ stateSpace A, ‖φ x‖ = ‖x‖ := by
  have : IsStarNormal (x : Unitization ℂ A) :=
    ⟨by rw [Commute, SemiconjBy, ← Unitization.inr_star, ← Unitization.inr_mul,
      ← Unitization.inr_mul, star_comm_self]⟩
  obtain ⟨ψ, hψ, -, hψx⟩ :=
    exists_mem_stateSpace_apply_mem_spectrum_and_norm_eq (x : Unitization ℂ A)
  rw [Unitization.norm_inr] at hψx
  let φ : WeakDual ℂ A := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  have hpos : ∀ b, 0 ≤ b → 0 ≤ φ b := fun b hb ↦ by
    simpa [φ] using map_nonneg_of_mem_stateSpace hψ (Unitization.inr_nonneg_iff.2 hb)
  have hle : ‖toStrongDual φ‖ ≤ 1 :=
    (toStrongDual φ).opNorm_le_bound zero_le_one fun b ↦ by
      simpa [φ, Unitization.norm_inr] using
        norm_apply_le_of_mem_stateSpace hψ (b : Unitization ℂ A)
  have hge : 1 ≤ ‖toStrongDual φ‖ := by
    have hbound : ‖x‖ ≤ ‖toStrongDual φ‖ * ‖x‖ := by
      simpa [φ, hψx] using (toStrongDual φ).le_opNorm x
    exact (le_mul_iff_one_le_left (norm_pos_iff.2 hx)).1 hbound
  exact ⟨φ, mem_stateSpace_iff.2 ⟨hpos, le_antisymm hle hge⟩, by simpa [φ] using hψx⟩

/-- For a nonzero nonnegative element `a` of a possibly nonunital C⋆-algebra `A`, some state `φ` of
`A` satisfies `φ a = ‖a‖`. -/
theorem exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero {a : A} (ha : 0 ≤ a)
    (ha0 : a ≠ 0) : ∃ φ ∈ stateSpace A, φ a = (‖a‖ : ℂ) := by
  have := ha.isSelfAdjoint.isStarNormal
  obtain ⟨φ, hφ, hnorm⟩ := exists_mem_stateSpace_norm_apply_eq_of_ne_zero ha0
  have hpos := map_nonneg_of_mem_stateSpace hφ ha
  refine ⟨φ, hφ, ?_⟩
  rw [← hnorm, ← Complex.re_eq_norm.2 hpos]
  exact Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hpos)

/-- For every nonzero element `a` of a possibly nonunital C⋆-algebra `A`, some state `φ` of `A`
satisfies `φ (star a * a) = ‖a‖ ^ 2`. -/
theorem exists_mem_stateSpace_star_mul_self_eq_norm_sq {a : A} (ha : a ≠ 0) :
    ∃ φ ∈ stateSpace A, φ (star a * a) = (‖a‖ ^ 2 : ℂ) := by
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_apply_eq_norm_of_nonneg_of_ne_zero
    (star_mul_self_nonneg a) (star_mul_self_eq_zero.not.2 ha)
  exact ⟨φ, hφ, by simpa [CStarRing.norm_star_mul_self, sq] using hφa⟩

/-- **Existence of states.** Every nonzero C⋆-algebra, possibly nonunital, has a state. -/
theorem stateSpace_nonempty_of_nontrivial [Nontrivial A] : (stateSpace A).Nonempty := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨φ, hφ, -⟩ := exists_mem_stateSpace_star_mul_self_eq_norm_sq ha
  exact ⟨φ, hφ⟩

/-- An element of a C⋆-algebra is zero if and only if `φ (star a * a) = 0` for every state `φ`. -/
theorem eq_zero_iff_forall_mem_stateSpace_star_mul_self {a : A} :
    a = 0 ↔ ∀ φ ∈ stateSpace A, φ (star a * a) = 0 := by
  refine ⟨fun ha φ _ ↦ by simp [ha], fun h ↦ ?_⟩
  by_contra ha
  obtain ⟨φ, hφ, hφa⟩ := exists_mem_stateSpace_star_mul_self_eq_norm_sq ha
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
  have := hsa_inr.isStarNormal
  rw [← Unitization.inr_nonneg_iff,
    StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : Unitization ℂ A) hsa_inr]
  intro r hr
  obtain ⟨ψ, hψ, hψa⟩ := exists_mem_stateSpace_apply_eq_of_mem_spectrum (a : Unitization ℂ A)
    (spectrum.algebraMap_mem ℂ hr)
  let ψ₀ : WeakDual ℂ A := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  have hψ₀_pos : ∀ b, 0 ≤ b → 0 ≤ ψ₀ b := fun b hb ↦ by
    simpa [ψ₀] using map_nonneg_of_mem_stateSpace hψ (Unitization.inr_nonneg_iff.2 hb)
  by_cases h0 : toStrongDual ψ₀ = 0
  · have h0a : (toStrongDual ψ₀) a = 0 := by simp [h0]
    exact (show r = 0 by simpa [ψ₀, hψa] using h0a).ge
  · set c : ℝ := ‖toStrongDual ψ₀‖
    have hc : 0 < c := norm_pos_iff.2 h0
    let φ : WeakDual ℂ A := StrongDual.toWeakDual (((c⁻¹ : ℝ) : ℂ) • toStrongDual ψ₀)
    have hφ_eval (b : A) : φ b = ((c⁻¹ : ℝ) : ℂ) * ψ₀ b := by
      rw [← toStrongDual_apply φ]
      simp [φ]
    have hstate : φ ∈ stateSpace A := by
      refine mem_stateSpace_iff.2 ⟨fun b hb ↦ ?_, ?_⟩
      · rw [hφ_eval]
        exact mul_nonneg (Complex.zero_le_real.2 (inv_nonneg.2 hc.le)) (hψ₀_pos b hb)
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

/-- **Countable convex combinations of states are states.** If `φ n` are states of `A` and `w n ≥ 0`
satisfy `∑' n, w n = 1`, then the norm-convergent series `∑' n, w n • toStrongDual (φ n)` defines a
state of `A`. -/
theorem toWeakDual_tsum_mem_stateSpace {φ : ℕ → WeakDual ℂ A} (hφ : ∀ n, φ n ∈ stateSpace A)
    {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : HasSum w 1) :
    StrongDual.toWeakDual (∑' n, w n • toStrongDual (φ n)) ∈ stateSpace A := by
  have hbound (n : ℕ) : ‖w n • toStrongDual (φ n)‖ ≤ w n := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 n), norm_toStrongDual_of_mem_stateSpace (hφ n), mul_one]
  have hsum : Summable fun n ↦ w n • toStrongDual (φ n) :=
    Summable.of_norm_bounded hw1.summable hbound
  set g : StrongDual ℂ A := ∑' n, w n • toStrongDual (φ n)
  have hpos (a : A) (ha : 0 ≤ a) : 0 ≤ g a := by
    have heval : HasSum (fun n ↦ (w n : ℂ) * φ n a) (g a) := by
      simpa [g, Complex.real_smul] using (ContinuousLinearMap.apply ℂ ℂ a).hasSum hsum.hasSum
    refine ge_of_tendsto heval.tendsto_sum_nat <| .of_forall fun s ↦ Finset.sum_nonneg fun n _ ↦ ?_
    exact mul_nonneg (Complex.zero_le_real.2 (hw0 n)) (map_nonneg_of_mem_stateSpace (hφ n) ha)
  refine mem_stateSpace_iff.2 ⟨fun a ha ↦ by simpa using hpos a ha, le_antisymm ?_ ?_⟩
  · simpa using tsum_of_norm_bounded hw1 hbound
  · have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hg_lim : Tendsto (fun e ↦ g e) (CStarAlgebra.approximateUnit A) (𝓝 (‖g‖ : ℂ)) := by
      simpa using tendsto_approximateUnit_norm_of_map_nonneg (φ := StrongDual.toWeakDual g)
        fun a ha ↦ by simpa using hpos a ha
    refine le_of_tendsto hw1 <| .of_forall fun s ↦ ?_
    have hterm_lim (n : ℕ) : Tendsto (fun e : A ↦ w n * (φ n e).re)
        (CStarAlgebra.approximateUnit A) (𝓝 (w n)) := by
      have hφn : Tendsto (fun e : A ↦ φ n e) (CStarAlgebra.approximateUnit A) (𝓝 (1 : ℂ)) := by
        simpa [norm_toStrongDual_of_mem_stateSpace (hφ n)] using
          tendsto_approximateUnit_norm_of_map_nonneg
            (fun a ha ↦ map_nonneg_of_mem_stateSpace (hφ n) ha)
      have hre : Tendsto (fun e : A ↦ (φ n e).re) (CStarAlgebra.approximateUnit A) (𝓝 1) :=
        ((Complex.continuous_re.tendsto (1 : ℂ)).comp hφn).congr fun _ ↦ rfl
      simpa only [mul_one] using tendsto_const_nhds.mul hre
    have hg_re : Tendsto (fun e : A ↦ (g e).re) (CStarAlgebra.approximateUnit A) (𝓝 ‖g‖) :=
      ((Complex.continuous_re.tendsto (‖g‖ : ℂ)).comp hg_lim).congr fun _ ↦ rfl
    refine le_of_tendsto_of_tendsto (tendsto_finsetSum s fun n _ ↦ hterm_lim n) hg_re ?_
    filter_upwards [hl.eventually_nonneg] with e he
    have he_re : HasSum (fun n ↦ w n * (φ n e).re) (g e).re := by
      have hc : HasSum (fun n ↦ (w n : ℂ) * φ n e) (g e) := by
        simpa [g, Complex.real_smul] using (ContinuousLinearMap.apply ℂ ℂ e).hasSum hsum.hasSum
      simpa using Complex.reCLM.hasSum hc
    exact he_re.summable.sum_le_tsum s (fun k _ ↦ mul_nonneg (hw0 k)
      (Complex.nonneg_iff.1 (map_nonneg_of_mem_stateSpace (hφ k) he)).1) |>.trans_eq he_re.tsum_eq

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

/-- **Existence of a faithful state on a separable C⋆-algebra.** Every nonzero separable C⋆-algebra,
possibly nonunital, admits a state `φ` such that `φ (star a * a) = 0 ↔ a = 0` for all `a`. -/
theorem exists_mem_stateSpace_faithful [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ φ ∈ stateSpace A, ∀ a, φ (star a * a) = 0 ↔ a = 0 := by
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨φ₀, hφ₀⟩ := stateSpace_nonempty_of_nontrivial (A := A)
  have hex (n : ℕ) : ∃ ψ ∈ stateSpace A, ψ (star (x n) * x n) = (‖x n‖ ^ 2 : ℂ) := by
    rcases eq_or_ne (x n) 0 with h0 | hne
    · exact ⟨φ₀, hφ₀, by simp [h0]⟩
    · exact exists_mem_stateSpace_star_mul_self_eq_norm_sq hne
  choose ψ hψ hψ_norm using hex
  set w : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 1)
  have hw0 (n : ℕ) : 0 ≤ w n := by positivity
  have hw_pos (n : ℕ) : 0 < w n := by positivity
  have hw1 : HasSum w 1 := by
    simpa [w, pow_succ, mul_comm, div_eq_mul_inv] using hasSum_geometric_two' (1 : ℝ)
  have hsum : Summable fun n ↦ w n • toStrongDual (ψ n) := by
    refine Summable.of_norm_bounded hw1.summable fun n ↦ ?_
    rw [norm_smul, Real.norm_of_nonneg (hw0 n), norm_toStrongDual_of_mem_stateSpace (hψ n), mul_one]
  let g : StrongDual ℂ A := ∑' n, w n • toStrongDual (ψ n)
  refine ⟨StrongDual.toWeakDual g, toWeakDual_tsum_mem_stateSpace hψ hw0 hw1,
    fun a ↦ ⟨fun ha0 ↦ eq_zero_of_denseRange hx hψ hψ_norm fun n ↦ ?_, fun ha ↦ by simp [ha]⟩⟩
  have heval : HasSum (fun k ↦ w k * (ψ k (star a * a)).re) (g (star a * a)).re := by
    have hc : HasSum (fun k ↦ (w k : ℂ) * ψ k (star a * a)) (g (star a * a)) := by
      simpa [Complex.real_smul, g] using
        (ContinuousLinearMap.apply ℂ ℂ (star a * a)).hasSum hsum.hasSum
    simpa using Complex.reCLM.hasSum hc
  have hre0 : (g (star a * a)).re = 0 := by simp [show g (star a * a) = 0 from ha0]
  have hnonneg (k : ℕ) : 0 ≤ w k * (ψ k (star a * a)).re :=
    mul_nonneg (hw0 k) (Complex.nonneg_iff.1
      (map_nonneg_of_mem_stateSpace (hψ k) (star_mul_self_nonneg a))).1
  have hterm0 : w n * (ψ n (star a * a)).re = 0 :=
    le_antisymm ((heval.summable.le_tsum n fun k _ ↦ hnonneg k).trans_eq
      (heval.tsum_eq.trans hre0)) (hnonneg n)
  exact Complex.ext ((mul_eq_zero.1 hterm0).resolve_left (hw_pos n).ne')
    (Complex.nonneg_iff.1 (map_nonneg_of_mem_stateSpace (hψ n) (star_mul_self_nonneg a))).2.symm

/-- Bundled `PositiveLinearMap` form of `TauCeti.exists_mem_stateSpace_faithful`: every nonzero
separable C⋆-algebra admits a norm-one positive linear functional `ω : A →ₚ[ℂ] ℂ` with
`ω (star a * a) = 0 ↔ a = 0`. -/
theorem exists_positiveLinearMap_norm_eq_one_faithful [TopologicalSpace.SeparableSpace A]
    [Nontrivial A] :
    ∃ ω : A →ₚ[ℂ] ℂ,
      ‖(PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ)‖ = 1 ∧
        ∀ a, ω (star a * a) = 0 ↔ a = 0 := by
  obtain ⟨φ, hφ, hfaith⟩ := exists_mem_stateSpace_faithful (A := A)
  obtain ⟨ω, hnorm, rfl⟩ := mem_stateSpace_iff_exists_positiveLinearMap.1 hφ
  exact ⟨ω, hnorm, hfaith⟩

end Separable

end TauCeti
