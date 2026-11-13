/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic

/-!
# Unitization and restriction of states on C⋆-algebras

For a possibly nonunital C⋆-algebra `A`, every functional `φ : WeakDual ℂ A` extends to the
minimal unitization `A⁺¹ = Unitization ℂ A` by sending `c + a` to `c + φ a`
(`TauCeti.unitizationFunctional`). Conversely, restricting along the canonical embedding
`Unitization.inrNonUnitalStarAlgHom ℂ A : A →⋆ₙₐ[ℂ] A⁺¹` via `TauCeti.pullbackFunctional`
recovers `φ`.

These two maps match `TauCeti.stateSpace A⁺¹` bijectively with the positive contractive functionals
(quasistates) `{φ : WeakDual ℂ A | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1}` of `A`. In
particular, every state of `A` extends uniquely to a state of `A⁺¹`, and the restriction of a
state of `A⁺¹` to `A` is a state of `A` whenever its restriction has norm one — for instance
whenever it attains the norm of some nonzero element of `A`. This reduction transfers unital
state-separation and extension results from `A⁺¹` to arbitrary nonunital C⋆-algebras.

## Main declarations

* `TauCeti.unitizationFunctional`: the weak-* continuous affine extension `WeakDual ℂ A →
  WeakDual ℂ A⁺¹` sending `x` to `x.fst + φ x.snd`.
* `TauCeti.unitizationFunctional_mem_stateSpace_iff`: `unitizationFunctional φ` is a state of
  `A⁺¹` if and only if `φ` is nonnegative on nonnegative elements and has norm at most one.
* `TauCeti.bijOn_unitizationFunctional`: `unitizationFunctional` maps the positive contractive
  functionals of `A` bijectively onto `stateSpace A⁺¹`, with inverse given by restriction along
  `Unitization.inrNonUnitalStarAlgHom ℂ A` (`TauCeti.unitizationFunctional_pullbackFunctional_inr`).
* `TauCeti.existsUnique_mem_stateSpace_unitization`: every state of `A` extends uniquely to a
  state of `A⁺¹`.
* `TauCeti.pullbackFunctional_inr_mem_stateSpace_of_norm_apply_eq_norm`: restricting a state of
  `A⁺¹` that attains `‖a‖` on a nonzero `a : A` gives a state of `A`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.3.9.
* B. Blackadar, *Operator Algebras*, Springer, 2006, II.6.2.5.
* J. Peterson, *Notes on Operator Algebras*, Section 4.1.
-/

public section

open Set WeakDual
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

section Basic

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Extend a functional `φ` in the weak-* dual of `A` to the minimal unitization `A⁺¹` by sending
`x` to `x.fst + φ x.snd`. -/
noncomputable def unitizationFunctional (φ : WeakDual ℂ A) : WeakDual ℂ A⁺¹ :=
  StrongDual.toWeakDual
    { toLinearMap := (Unitization.fstHom ℂ A).toLinearMap +
        (toStrongDual φ : A →ₗ[ℂ] ℂ).comp (Unitization.sndHom ℂ ℂ A)
      cont := Unitization.continuous_fst.add
        ((toStrongDual φ).continuous.comp Unitization.continuous_snd) }

/-- `unitizationFunctional φ` evaluates at `x : A⁺¹` as `x.fst + φ x.snd`. -/
@[simp]
theorem unitizationFunctional_apply (φ : WeakDual ℂ A) (x : A⁺¹) :
    unitizationFunctional φ x = x.fst + φ x.snd :=
  (rfl)

/-- `unitizationFunctional φ` takes the value `1` at the unit of `A⁺¹`. -/
theorem unitizationFunctional_one (φ : WeakDual ℂ A) : unitizationFunctional φ 1 = 1 := by
  simp

/-- `unitizationFunctional φ` restricts to `φ` on `A ↪ A⁺¹`. -/
theorem unitizationFunctional_inr (φ : WeakDual ℂ A) (a : A) :
    unitizationFunctional φ (a : A⁺¹) = φ a := by
  simp

/-- `unitizationFunctional φ` acts as the identity on scalars `Unitization.inl c`. -/
theorem unitizationFunctional_inl (φ : WeakDual ℂ A) (c : ℂ) :
    unitizationFunctional φ (Unitization.inl c) = c := by
  simp

/-- `unitizationFunctional` is weak-* continuous. -/
@[fun_prop]
theorem continuous_unitizationFunctional :
    Continuous (unitizationFunctional : WeakDual ℂ A → WeakDual ℂ A⁺¹) :=
  continuous_of_continuous_eval fun x => continuous_const.add (eval_continuous x.snd)

/-- `unitizationFunctional` preserves affine combinations. -/
theorem unitizationFunctional_combo (φ ψ : WeakDual ℂ A) {s t : ℝ} (hst : s + t = 1) :
    unitizationFunctional (s • φ + t • ψ) =
      s • unitizationFunctional φ + t • unitizationFunctional ψ :=
  DFunLike.ext _ _ fun x => by
    simp only [unitizationFunctional_apply, add_apply, WeakDual.real_smul_apply]
    have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
    linear_combination -x.fst * hst'

/-- `unitizationFunctional` is injective. -/
theorem unitizationFunctional_injective :
    Function.Injective (unitizationFunctional : WeakDual ℂ A → WeakDual ℂ A⁺¹) := fun φ ψ h =>
  DFunLike.ext _ _ fun a => by simpa using congr($h (a : A⁺¹))

end Basic

section Order

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

/-- Restricting `unitizationFunctional φ` along `inr` recovers `φ`. -/
@[simp]
theorem pullbackFunctional_inr_unitizationFunctional (φ : WeakDual ℂ A) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) (unitizationFunctional φ) = φ :=
  DFunLike.ext _ _ fun a => by simp

/-- Any functional `ψ` on `A⁺¹` normalized by `ψ 1 = 1` is the unitization extension of its
restriction to `A`. -/
theorem unitizationFunctional_pullbackFunctional_inr {ψ : WeakDual ℂ A⁺¹} (hψ : ψ 1 = 1) :
    unitizationFunctional (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ) = ψ :=
  DFunLike.ext _ _ fun x => by
    conv_rhs => rw [← Unitization.inl_fst_add_inr_snd_eq x, ← Unitization.algebraMap_eq_inl,
      Algebra.algebraMap_eq_smul_one]
    simp [map_add, map_smul, hψ]

/-- Key square-positivity step: for a positive contractive functional `φ` on `A`, its unitization
extension is nonnegative on every element of the form `star s * s` in `A⁺¹`. -/
private theorem unitizationFunctional_star_mul_self_nonneg
    (hpos : ∀ a, 0 ≤ a → 0 ≤ φ a) (hnorm : ‖toStrongDual φ‖ ≤ 1) (s : A⁺¹) :
    0 ≤ unitizationFunctional φ (star s * s) := by
  set c : ℂ := s.fst
  set a : A := s.snd
  set r : ℝ := ‖φ (star a * a)‖
  have hw_eq : φ (star a * a) = (r : ℂ) :=
    (Complex.norm_of_nonneg' (hpos _ (star_mul_self_nonneg a))).symm
  have hcs : ‖φ a‖ ^ 2 ≤ r :=
    (WeakDual.norm_apply_sq_le_mul_of_map_nonneg hpos a).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hstar : φ (star a) = star (φ a) := WeakDual.map_star_of_map_nonneg hpos a
  -- Complete the square:
  -- `‖c‖² + star c * φ a + c * star (φ a) + φ (a⋆ * a) = ‖c + φ a‖² + (φ (a⋆ * a) - ‖φ a‖²)`.
  have hid : unitizationFunctional φ (star s * s) =
      ((‖c + φ a‖ ^ 2 + (r - ‖φ a‖ ^ 2) : ℝ) : ℂ) := by
    simp only [unitizationFunctional_apply, Unitization.fst_mul, Unitization.fst_star,
      Unitization.snd_mul, Unitization.snd_star, map_add, map_smul, smul_eq_mul]
    rw [hstar, hw_eq]
    have hnorm_sq (z : ℂ) : (‖z‖ : ℂ) ^ 2 = star z * z := (Complex.conj_mul' z).symm
    push_cast
    rw [hnorm_sq (c + φ a), hnorm_sq (φ a)]
    simp only [star_add]
    ring
  rw [hid]
  exact Complex.zero_le_real.2 (by linarith [sq_nonneg ‖c + φ a‖])

/-- **Characterization of unitized states.** The unitization extension `unitizationFunctional φ`
is a state of `A⁺¹` if and only if `φ` is nonnegative on nonnegative elements of `A` and has
operator norm at most `1`. -/
theorem unitizationFunctional_mem_stateSpace_iff :
    unitizationFunctional φ ∈ stateSpace A⁺¹ ↔
      (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1 := by
  rw [mem_stateSpace_iff_map_one]
  refine ⟨fun ⟨hpos, _⟩ => ⟨fun a ha => ?_, ?_⟩, fun ⟨hpos, hnorm⟩ => ⟨fun x hx => ?_, by simp⟩⟩
  · simpa using hpos (a : A⁺¹) (Unitization.inr_nonneg_iff.2 ha)
  · refine (toStrongDual φ).opNorm_le_bound zero_le_one fun a => ?_
    have hψ : unitizationFunctional φ ∈ stateSpace A⁺¹ :=
      mem_stateSpace_iff_map_one.2 ⟨hpos, by simp⟩
    simpa [Unitization.norm_inr] using norm_apply_le_of_mem_stateSpace hψ (a : A⁺¹)
  · rw [StarOrderedRing.nonneg_iff] at hx
    refine AddSubmonoid.closure_induction ?_ (by simp)
      (fun u v _ _ hu hv => by simpa [map_add] using add_nonneg hu hv) hx
    rintro _ ⟨s, rfl⟩
    exact unitizationFunctional_star_mul_self_nonneg hpos hnorm s

/-- Every state of `A` extends via `unitizationFunctional` to a state of `A⁺¹`. -/
theorem unitizationFunctional_mem_stateSpace (hφ : φ ∈ stateSpace A) :
    unitizationFunctional φ ∈ stateSpace A⁺¹ :=
  unitizationFunctional_mem_stateSpace_iff.2
    ⟨fun _ => map_nonneg_of_mem_stateSpace hφ, (norm_toStrongDual_of_mem_stateSpace hφ).le⟩

/-- The zero functional on `A` extends via `unitizationFunctional` to the character `x ↦ x.fst`,
which is a state of `A⁺¹`. -/
theorem unitizationFunctional_zero_mem_stateSpace :
    unitizationFunctional (0 : WeakDual ℂ A) ∈ stateSpace A⁺¹ :=
  unitizationFunctional_mem_stateSpace_iff.2
    ⟨fun a _ => by rw [← toStrongDual_apply]; simp, by simp⟩

/-- `unitizationFunctional` maps the positive contractive functionals of `A` bijectively onto the
state space of `A⁺¹`. -/
theorem bijOn_unitizationFunctional :
    BijOn (unitizationFunctional (A := A))
      {φ : WeakDual ℂ A | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ ≤ 1}
      (stateSpace A⁺¹) := by
  refine ⟨fun φ hφ => unitizationFunctional_mem_stateSpace_iff.2 hφ,
    unitizationFunctional_injective.injOn, fun ψ hψ => ?_⟩
  refine ⟨pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ, ?_,
    unitizationFunctional_pullbackFunctional_inr (map_one_of_mem_stateSpace hψ)⟩
  exact unitizationFunctional_mem_stateSpace_iff.1 <|
    (unitizationFunctional_pullbackFunctional_inr (map_one_of_mem_stateSpace hψ)).symm ▸ hψ

/-- States of `A⁺¹` are determined by their restrictions to `A`. -/
theorem injOn_pullbackFunctional_inr_stateSpace :
    InjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A)) (stateSpace A⁺¹) := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ h
  rw [← unitizationFunctional_pullbackFunctional_inr (map_one_of_mem_stateSpace hψ₁),
    ← unitizationFunctional_pullbackFunctional_inr (map_one_of_mem_stateSpace hψ₂), h]

/-- **Unique extension of states to the unitization.** Every state of `A` extends to a unique state
of `A⁺¹`. -/
theorem existsUnique_mem_stateSpace_unitization (hφ : φ ∈ stateSpace A) :
    ∃! ψ : WeakDual ℂ A⁺¹, ψ ∈ stateSpace A⁺¹ ∧ ∀ a : A, ψ a = φ a := by
  refine ⟨unitizationFunctional φ, ⟨unitizationFunctional_mem_stateSpace hφ, fun a => by simp⟩, ?_⟩
  rintro ψ ⟨hψ, hψφ⟩
  rw [← unitizationFunctional_pullbackFunctional_inr (map_one_of_mem_stateSpace hψ)]
  congr 1
  exact DFunLike.ext _ _ fun a => by simpa using hψφ a

/-- Restricting a state of `A⁺¹` along `inr` produces a functional that is nonnegative on
nonnegative elements of `A`. -/
theorem map_nonneg_pullbackFunctional_inr_of_mem_stateSpace {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) {a : A} (ha : 0 ≤ a) :
    0 ≤ pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ a := by
  simpa using map_nonneg_of_mem_stateSpace hψ (Unitization.inr_nonneg_iff.2 ha)

/-- Restricting a state of `A⁺¹` along `inr` produces a contractive functional on `A`. -/
theorem norm_toStrongDual_pullbackFunctional_inr_le_one {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) :
    ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ ≤ 1 :=
  (unitizationFunctional_mem_stateSpace_iff.1 <|
    (unitizationFunctional_pullbackFunctional_inr (map_one_of_mem_stateSpace hψ)).symm ▸ hψ).2

/-- The restriction of a state of `A⁺¹` to `A` is a state of `A` if and only if its norm on `A` is
one. -/
theorem pullbackFunctional_inr_mem_stateSpace_iff {ψ : WeakDual ℂ A⁺¹} (hψ : ψ ∈ stateSpace A⁺¹) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A ↔
      ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ = 1 :=
  ⟨norm_toStrongDual_of_mem_stateSpace, fun hnorm =>
    mem_stateSpace_iff.2 ⟨fun _ => map_nonneg_pullbackFunctional_inr_of_mem_stateSpace hψ, hnorm⟩⟩

/-- **Restriction of norm-attaining unitized states.** If a state `ψ` of `A⁺¹` attains the norm of
some nonzero element `a : A` (`‖ψ a‖ = ‖a‖`), then its restriction to `A` is a state of `A`. -/
theorem pullbackFunctional_inr_mem_stateSpace_of_norm_apply_eq_norm {ψ : WeakDual ℂ A⁺¹}
    (hψ : ψ ∈ stateSpace A⁺¹) {a : A} (ha : a ≠ 0) (hnorm : ‖ψ (a : A⁺¹)‖ = ‖a‖) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A := by
  rw [pullbackFunctional_inr_mem_stateSpace_iff hψ]
  set φ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  refine le_antisymm (norm_toStrongDual_pullbackFunctional_inr_le_one hψ) ?_
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hle : ‖a‖ ≤ ‖toStrongDual φ‖ * ‖a‖ := by
    simpa [φ, hnorm] using (toStrongDual φ).le_opNorm a
  exact (le_mul_iff_one_le_left ha_pos).1 hle

end Order

end TauCeti
