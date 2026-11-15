/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Unitization and restriction of positive functionals and states

Every positive continuous linear functional `ω : A →P[ℂ] ℂ` on a possibly nonunital C⋆-algebra `A`
extends canonically and norm-preservingly to `Unitization ℂ A` by setting the value at `1` equal to
`‖ω‖`:

`ω.unitization x = x.fst * ‖ω‖ + ω x.snd`.

Conversely, restricting a state `ψ ∈ stateSpace (Unitization ℂ A)` along the canonical embedding
`Unitization.inrNonUnitalStarAlgHom ℂ A` produces a positive contraction on `A`. Unlike pullback
along surjective or unital star homomorphisms, this restriction need not be a state (the scalar
augmentation restricts to `0`), so it lies in `stateSpace A` precisely when its norm is `1`, and
normalizing any nonzero restriction gives a state of `A`.

Together these operations reduce spectral and order separation properties of states on arbitrary
nonunital C⋆-algebras to the unital case on `Unitization ℂ A`.

## Main declarations

* `PositiveContinuousLinearMap.unitization`: the canonical norm-preserving positive extension of
  `ω : A →P[ℂ] ℂ` to `Unitization ℂ A`, with `opNorm_unitization` and uniqueness
  `eq_unitization_of_opNorm_le`.
* `TauCeti.injOn_pullbackFunctional_inrNonUnitalStarAlgHom_stateSpace` and
  `TauCeti.surjOn_pullbackFunctional_inrNonUnitalStarAlgHom_stateSpace`: restriction from
  `stateSpace (Unitization ℂ A)` is injective and covers `stateSpace A`.
* `TauCeti.existsUnique_mem_stateSpace_unitization`: every state of `A` extends uniquely to a
  state of `Unitization ℂ A`.
* `TauCeti.inv_norm_smul_pullbackFunctional_inrNonUnitalStarAlgHom_mem_stateSpace`: normalizing any
  nonzero restriction of a state of `Unitization ℂ A` yields a state of `A`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), Theorem 3.3.9.
* Jesse Peterson, *Notes on operator algebras*, Section 4.1.
-/

public section

noncomputable section

open Filter Set WeakDual
open scoped ComplexOrder CStarAlgebra Topology

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Along an increasing approximate unit, `ω (x.fst • e + x.snd * e)` converges to
`x.fst * ‖ω‖ + ω x.snd`, giving the sharp norm bound for the unitized functional. -/
private theorem norm_fst_mul_opNorm_add_apply_snd_le (ω : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    ‖x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd‖ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hlim : Tendsto (fun e : A ↦ ω (x.fst • e + x.snd * e))
      (CStarAlgebra.approximateUnit A) (𝓝 (x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd)) := by
    have heq : (fun e : A ↦ ω (x.fst • e + x.snd * e)) =
        fun e : A ↦ x.fst * ω e + ω (x.snd * e) := by
      ext e
      simp
    rw [heq]
    exact ((ω.tendsto_nhds_opNorm hl).const_mul x.fst).add
      ((ω.continuous.tendsto x.snd).comp (hl.tendsto_mul_left x.snd))
  refine le_of_tendsto hlim.norm ?_
  filter_upwards [hl.eventually_norm] with e he
  have hinr : ((x.fst • e + x.snd * e : A) : Unitization ℂ A) = x * (e : Unitization ℂ A) :=
    Unitization.ext (by simp) (by simp)
  calc
    ‖ω (x.fst • e + x.snd * e)‖
        ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x.fst • e + x.snd * e‖ := (ω : A →L[ℂ] ℂ).le_opNorm _
    _ = ‖(ω : A →L[ℂ] ℂ)‖ * ‖x * (e : Unitization ℂ A)‖ := by
          rw [← Unitization.norm_inr (𝕜 := ℂ), hinr]
    _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * (‖x‖ * ‖(e : Unitization ℂ A)‖) := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x‖ := by
          rw [Unitization.norm_inr]
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg x) he)
            (norm_nonneg _)

/-- The underlying continuous linear map of `PositiveContinuousLinearMap.unitization`. -/
private def unitizationCLM (ω : A →P[ℂ] ℂ) : Unitization ℂ A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun x := x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd
      map_add' x y := by
        simp only [Unitization.fst_add, Unitization.snd_add, add_mul, map_add]
        ring
      map_smul' c x := by
        simp only [Unitization.fst_smul, Unitization.snd_smul, smul_eq_mul, map_smul,
          RingHom.id_apply]
        ring }
    ‖(ω : A →L[ℂ] ℂ)‖ (norm_fst_mul_opNorm_add_apply_snd_le ω)

private theorem opNorm_unitizationCLM (ω : A →P[ℂ] ℂ) :
    ‖unitizationCLM ω‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) ?_
  refine (ω : A →L[ℂ] ℂ).opNorm_le_bound (norm_nonneg _) fun a ↦ ?_
  simpa [unitizationCLM, Unitization.norm_inr] using
    (unitizationCLM ω).le_opNorm (a : Unitization ℂ A)

/-- The canonical norm-preserving positive extension of `ω : A →P[ℂ] ℂ` to `Unitization ℂ A`,
mapping `x` to `x.fst * ‖ω‖ + ω x.snd`. -/
def unitization (ω : A →P[ℂ] ℂ) : Unitization ℂ A →P[ℂ] ℂ where
  toContinuousLinearMap := unitizationCLM ω
  monotone' := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.2 <| by
    rw [opNorm_unitizationCLM]
    simp [unitizationCLM]

/-- Explicit coordinate formula for `ω.unitization`. -/
theorem unitization_apply (ω : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    ω.unitization x = x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd :=
  (rfl)

/-- `ω.unitization` extends `ω` along the canonical inclusion `A → Unitization ℂ A`. -/
@[simp]
theorem unitization_inr (ω : A →P[ℂ] ℂ) (a : A) :
    ω.unitization (a : Unitization ℂ A) = ω a := by
  simp [unitization_apply]

/-- `ω.unitization` evaluates to `‖ω‖` at the adjoined unit `1`. -/
@[simp]
theorem unitization_one (ω : A →P[ℂ] ℂ) :
    ω.unitization 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
  simp [unitization_apply]

/-- `ω.unitization` scales the scalar summand by `‖ω‖`. -/
@[simp]
theorem unitization_inl (ω : A →P[ℂ] ℂ) (z : ℂ) :
    ω.unitization (Unitization.inl z) = z * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
  simp [unitization_apply]

/-- Restricting `ω.unitization` back to `A` recovers `ω`. -/
@[simp]
theorem comp_inrNonUnitalStarAlgHom_unitization (ω : A →P[ℂ] ℂ) :
    ω.unitization.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)) = ω := by
  ext a
  simp

/-- Passing from `ω` to `ω.unitization` preserves the operator norm. -/
@[simp]
theorem opNorm_unitization (ω : A →P[ℂ] ℂ) :
    ‖(ω.unitization : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ :=
  opNorm_unitizationCLM ω

/-- `ω.unitization` is the unique positive extension of `ω` to `Unitization ℂ A` of norm at most
`‖ω‖`. -/
theorem eq_unitization_of_opNorm_le {ω : A →P[ℂ] ℂ} {ψ : Unitization ℂ A →P[ℂ] ℂ}
    (h_ext : ∀ a : A, ψ a = ω a)
    (h_norm : ‖(ψ : Unitization ℂ A →L[ℂ] ℂ)‖ ≤ ‖(ω : A →L[ℂ] ℂ)‖) :
    ψ = ω.unitization := by
  have h_eq_norm : ‖(ψ : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
    refine le_antisymm h_norm <| (ω : A →L[ℂ] ℂ).opNorm_le_bound (norm_nonneg _) fun a ↦ ?_
    simpa [h_ext a, Unitization.norm_inr] using
      (ψ : Unitization ℂ A →L[ℂ] ℂ).le_opNorm (a : Unitization ℂ A)
  have h1 : ψ 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
    rw [← h_eq_norm, ψ.ofReal_opNorm_eq_map_one]
  ext x
  induction x with
  | inl_add_inr r a =>
    have hr : Unitization.inl (A := A) r = r • (1 : Unitization ℂ A) := by
      rw [← Unitization.algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one]
    simp [map_add, hr, h1, h_ext a]

end PositiveContinuousLinearMap

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restricting a state of `Unitization ℂ A` to `A` yields a functional nonnegative on nonnegative
elements. -/
theorem map_nonneg_pullbackFunctional_inrNonUnitalStarAlgHom
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A))
    {a : A} (ha : 0 ≤ a) :
    0 ≤ pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ a := by
  rw [pullbackFunctional_apply]
  exact map_nonneg_of_mem_stateSpace hψ (Unitization.inr_nonneg_iff.2 ha)

/-- Restricting a state of `Unitization ℂ A` to `A` is contractive in operator norm. -/
theorem norm_toStrongDual_pullbackFunctional_inrNonUnitalStarAlgHom_le
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A)) :
    ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a ↦ ?_
  simpa [Unitization.norm_inr] using norm_apply_le_of_mem_stateSpace hψ (a : Unitization ℂ A)

/-- The restriction of a state of `Unitization ℂ A` to `A` is a state of `A` if and only if its
norm is `1`. -/
theorem pullbackFunctional_inrNonUnitalStarAlgHom_mem_stateSpace_iff
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A)) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A ↔
      ‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖ = 1 := by
  rw [mem_stateSpace_iff, and_iff_right_iff_imp]
  exact fun _ _ ha ↦ map_nonneg_pullbackFunctional_inrNonUnitalStarAlgHom hψ ha

/-- Normalizing any nonzero restriction of a state of `Unitization ℂ A` produces a state of `A`. -/
theorem inv_norm_smul_pullbackFunctional_inrNonUnitalStarAlgHom_mem_stateSpace
    {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A))
    (hne : pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ≠ 0) :
    (‖toStrongDual (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ)‖⁻¹ : ℝ) •
        pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A := by
  set φ := pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ
  have hφ0 : toStrongDual φ ≠ 0 := fun h ↦ hne (toStrongDual.injective (by simpa using h))
  have hpos : 0 < ‖toStrongDual φ‖ := norm_pos_iff.2 hφ0
  refine mem_stateSpace_iff.2 ⟨fun a ha ↦ ?_, ?_⟩
  · rw [smul_apply]
    exact smul_nonneg (inv_nonneg.2 hpos.le)
      (map_nonneg_pullbackFunctional_inrNonUnitalStarAlgHom hψ ha)
  · rw [LinearMapClass.map_smul_of_tower toStrongDual, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']

/-- Restriction along the canonical inclusion `A → Unitization ℂ A` is injective on
`stateSpace (Unitization ℂ A)`. -/
theorem injOn_pullbackFunctional_inrNonUnitalStarAlgHom_stateSpace :
    InjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A))
      (stateSpace (Unitization ℂ A)) := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ h
  refine DFunLike.ext _ _ fun x ↦ ?_
  induction x with
  | inl_add_inr r a =>
    have hr : Unitization.inl (A := A) r = r • (1 : Unitization ℂ A) := by
      rw [← Unitization.algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one]
    have ha : ψ₁ a = ψ₂ a := by
      simpa using congr($h a)
    simp [map_add, hr, map_one_of_mem_stateSpace hψ₁, map_one_of_mem_stateSpace hψ₂, ha]

/-- Every state of `A` is the restriction of a state of `Unitization ℂ A`. -/
theorem surjOn_pullbackFunctional_inrNonUnitalStarAlgHom_stateSpace :
    SurjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A))
      (stateSpace (Unitization ℂ A)) (stateSpace A) := by
  intro φ hφ
  let ω : A →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ ha ↦ map_nonneg_of_mem_stateSpace hφ ha
  have hω : ‖(ω : A →L[ℂ] ℂ)‖ = 1 := norm_toStrongDual_of_mem_stateSpace hφ
  refine ⟨StrongDual.toWeakDual (ω.unitization : Unitization ℂ A →L[ℂ] ℂ), ?_, ?_⟩
  · rw [PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff, ω.opNorm_unitization]
    exact hω
  · refine DFunLike.ext _ _ fun a ↦ ?_
    simp [ω]
    -- `PositiveContinuousLinearMap.mk₀` has no simp evaluation lemma; it evaluates as `φ a`
    rfl

/-- **Unique unitization of states.** Every state `φ` of a possibly nonunital C⋆-algebra `A`
extends uniquely to a state of `Unitization ℂ A`. -/
theorem existsUnique_mem_stateSpace_unitization {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) :
    ∃! ψ, ψ ∈ stateSpace (Unitization ℂ A) ∧ ∀ a : A, ψ a = φ a := by
  obtain ⟨ψ, hψ, hres⟩ := surjOn_pullbackFunctional_inrNonUnitalStarAlgHom_stateSpace hφ
  refine ⟨ψ, ⟨hψ, fun a ↦ ?_⟩, fun ψ' ⟨hψ', hψ'a⟩ ↦ ?_⟩
  · simpa using congr($hres a)
  · refine injOn_pullbackFunctional_inrNonUnitalStarAlgHom_stateSpace hψ' hψ ?_
    refine DFunLike.ext _ _ fun a ↦ ?_
    simpa [hψ'a a] using congr($hres a).symm

end TauCeti
