/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Prod
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
import TauCeti.Analysis.CStarAlgebra.State.Space

/-!
# Positive tracial functionals and tracial states

A **positive tracial functional** on a C⋆-algebra `A` is a positive linear functional
`τ : A → ℂ` with `τ (a * b) = τ (b * a)`. Like every positive functional on a C⋆-algebra it is
bounded, but it need not have norm one. These are the functionals that pair with `K₀(A)` through
the unnormalized matrix trace `τ_m(p) = ∑ i, τ (p i i)`.

Tracial states are the norm-one case. This file does not define its own tracial-state predicate:
a tracial state is a `0`-KMS state of the trivial real dynamics,
`(CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0 ω`, which
`CStarAction.isKMSState_zero_iff` identifies with a positive functional of norm one satisfying
`ω (a * b) = ω (b * a)`. The statements below about tracial states are phrased with that
predicate applied to `τ.toPositiveContinuousLinearMap`.

Positive tracial functionals pull back along star homomorphisms: for `φ : A →⋆ₙₐ[ℂ] B` and a
positive tracial functional `τ` of `B`, the composite `τ ∘ φ` is a positive tracial functional of
`A`. The composite of a tracial state with a star homomorphism need not be a state, for instance
`(λ ↦ (λ, 0))` followed by `(a, b) ↦ b`, which is zero; it is one when `A` and `B` are unital and
`φ` is unital.

## Main declarations

* `TauCeti.PositiveTracialFunctional`: positive tracial functionals, with their `FunLike`,
  `LinearMapClass` and `OrderHomClass` instances, and `PositiveTracialFunctional.map_mul_comm`.
* `TauCeti.PositiveTracialFunctional.toPositiveContinuousLinearMap`: the functional is bounded,
  with `PositiveTracialFunctional.norm_apply_le`.
* `TauCeti.PositiveTracialFunctional.comp`: pullback along a star homomorphism, with
  `comp_id` and `comp_comp`.
* `TauCeti.PositiveTracialFunctional.isKMSState_trivial_zero_iff_opNorm_eq_one`: a positive
  tracial functional is a tracial state exactly when it has norm one, and for unital `A`
  exactly when it takes the value `1` at `1`, `isKMSState_trivial_zero_iff_map_one`. Tracial
  states pull back to tracial states along unital star homomorphisms,
  `isKMSState_trivial_zero_comp`, and are bounded by `1`, `norm_apply_le_of_isKMSState`.
* `TauCeti.PositiveTracialFunctional.ofIsKMSState`: a tracial state as a positive tracial
  functional.
* `TauCeti.not_isKMSState_sndTracialFunctional_comp_inl`: the pullback of the tracial state
  `(a, b) ↦ b` of `ℂ × ℂ` along `λ ↦ (λ, 0)` is zero, a positive tracial functional that is not
  a state.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §6.9.
* B. Blackadar, *Operator Algebras*, II.6.8.
-/

public section

open scoped ComplexOrder

namespace TauCeti

variable {A B C : Type*}

section NonUnital

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A **positive tracial functional** on a C⋆-algebra `A`: a positive linear functional
`τ : A → ℂ` with `τ (a * b) = τ (b * a)`. No normalization is imposed. -/
structure PositiveTracialFunctional (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] extends A →ₚ[ℂ] ℂ where
  /-- The functional is tracial. -/
  map_mul_comm' (a b : A) : toPositiveLinearMap (a * b) = toPositiveLinearMap (b * a)

namespace PositiveTracialFunctional

instance instFunLike : FunLike (PositiveTracialFunctional A) A ℂ where
  coe τ := τ.toPositiveLinearMap
  coe_injective τ σ h := by
    cases τ
    cases σ
    congr
    exact DFunLike.coe_injective h

instance instLinearMapClass : LinearMapClass (PositiveTracialFunctional A) ℂ A ℂ where
  map_add τ := map_add τ.toPositiveLinearMap
  map_smulₛₗ τ := map_smulₛₗ τ.toPositiveLinearMap

instance instOrderHomClass : OrderHomClass (PositiveTracialFunctional A) A ℂ where
  map_rel τ := fun {_ _} h => τ.toPositiveLinearMap.monotone h

/-- Positive tracial functionals are determined by their values. -/
@[ext]
theorem ext {τ σ : PositiveTracialFunctional A} (h : ∀ a, τ a = σ a) : τ = σ :=
  DFunLike.ext τ σ h

@[simp]
theorem coe_mk (f : A →ₚ[ℂ] ℂ) (h : ∀ a b, f (a * b) = f (b * a)) :
    ⇑(⟨f, h⟩ : PositiveTracialFunctional A) = f :=
  (rfl)

@[simp]
theorem toPositiveLinearMap_apply (τ : PositiveTracialFunctional A) (a : A) :
    τ.toPositiveLinearMap a = τ a :=
  rfl

/-- A positive tracial functional is tracial. -/
theorem map_mul_comm (τ : PositiveTracialFunctional A) (a b : A) : τ (a * b) = τ (b * a) :=
  τ.map_mul_comm' a b

/-- A positive tracial functional is bounded, as every positive functional on a C⋆-algebra is. -/
noncomputable def toPositiveContinuousLinearMap (τ : PositiveTracialFunctional A) :
    A →P[ℂ] ℂ :=
  .ofClass τ

@[simp]
theorem toPositiveContinuousLinearMap_apply (τ : PositiveTracialFunctional A) (a : A) :
    τ.toPositiveContinuousLinearMap a = τ a :=
  (rfl)

/-- A positive tracial functional is bounded by the operator norm of its bounded functional. -/
theorem norm_apply_le (τ : PositiveTracialFunctional A) (a : A) :
    ‖τ a‖ ≤ ‖(τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ)‖ * ‖a‖ :=
  (τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ).le_opNorm a

/-- **Naturality.** The pullback `τ ∘ φ` of a positive tracial functional along a star
homomorphism. -/
noncomputable def comp (τ : PositiveTracialFunctional B) (φ : A →⋆ₙₐ[ℂ] B) :
    PositiveTracialFunctional A where
  toPositiveLinearMap := τ.toPositiveLinearMap.comp (.ofClass φ)
  map_mul_comm' a b := by
    -- The composite evaluates as `τ ∘ φ` by definition; `comp_apply` is stated after this
    -- structure, so the field is proved by unfolding the composite here.
    change τ (φ (a * b)) = τ (φ (b * a))
    rw [map_mul φ, map_mul φ]
    exact τ.map_mul_comm (φ a) (φ b)

@[simp]
theorem comp_apply (τ : PositiveTracialFunctional B) (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    τ.comp φ a = τ (φ a) :=
  (rfl)

@[simp]
theorem comp_id (τ : PositiveTracialFunctional A) : τ.comp (NonUnitalStarAlgHom.id ℂ A) = τ := by
  ext a
  simp

theorem comp_comp (τ : PositiveTracialFunctional C) (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    (τ.comp ψ).comp φ = τ.comp (ψ.comp φ) := by
  ext a
  simp

/-- A positive tracial functional is a tracial state, a `0`-KMS state of the trivial dynamics,
exactly when it has norm one. -/
theorem isKMSState_trivial_zero_iff_opNorm_eq_one (τ : PositiveTracialFunctional A) :
    (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0
        τ.toPositiveContinuousLinearMap ↔
      ‖(τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ)‖ = 1 := by
  rw [CStarAction.isKMSState_zero_iff]
  exact and_iff_left fun a b => τ.map_mul_comm a b

/-- A tracial state, a `0`-KMS state of the trivial dynamics, is bounded by `1`. -/
theorem norm_apply_le_of_isKMSState {τ : PositiveTracialFunctional A}
    (hτ : (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0
      τ.toPositiveContinuousLinearMap) (a : A) : ‖τ a‖ ≤ ‖a‖ := by
  simpa [hτ.norm_eq_one] using τ.norm_apply_le a

/-- A tracial state, a `0`-KMS state `ω` of the trivial dynamics, as a positive tracial
functional. -/
def ofIsKMSState (ω : A →P[ℂ] ℂ)
    (hω : (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0 ω) :
    PositiveTracialFunctional A where
  toPositiveLinearMap := ω.toPositiveLinearMap
  map_mul_comm' := (CStarAction.isKMSState_zero_iff.mp hω).2

@[simp]
theorem ofIsKMSState_apply (ω : A →P[ℂ] ℂ)
    (hω : (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0 ω) (a : A) :
    ofIsKMSState ω hω a = ω a :=
  (rfl)

@[simp]
theorem toPositiveContinuousLinearMap_ofIsKMSState (ω : A →P[ℂ] ℂ)
    (hω : (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0 ω) :
    (ofIsKMSState ω hω).toPositiveContinuousLinearMap = ω := by
  ext a
  simp

end PositiveTracialFunctional

end NonUnital

section Unital

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PositiveTracialFunctional

/-- On a unital C⋆-algebra a positive tracial functional is a tracial state, a `0`-KMS state of
the trivial dynamics, exactly when `τ 1 = 1`. -/
theorem isKMSState_trivial_zero_iff_map_one (τ : PositiveTracialFunctional A) :
    (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0
        τ.toPositiveContinuousLinearMap ↔ τ 1 = 1 := by
  rw [isKMSState_trivial_zero_iff_opNorm_eq_one,
    ← PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff, mem_stateSpace_iff_map_one]
  refine ⟨fun h => ?_, fun h => ⟨fun a ha => ?_, ?_⟩⟩
  · simpa using h.2
  · simpa using map_nonneg τ ha
  · simpa using h

/-- Tracial states pull back to tracial states along unital star homomorphisms. -/
theorem isKMSState_trivial_zero_comp {τ : PositiveTracialFunctional B}
    (hτ : (CStarAction.trivial : CStarAction (Multiplicative ℝ) B).IsKMSState 0
      τ.toPositiveContinuousLinearMap) (φ : A →⋆ₐ[ℂ] B) :
    (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).IsKMSState 0
      (τ.comp φ.toNonUnitalStarAlgHom).toPositiveContinuousLinearMap := by
  rw [isKMSState_trivial_zero_iff_map_one] at hτ ⊢
  simpa using hτ

end PositiveTracialFunctional

end Unital

section Example

open PositiveTracialFunctional

/-- The second-coordinate functional `(a, b) ↦ b` on `ℂ × ℂ`, a tracial state. -/
noncomputable def sndTracialFunctional : PositiveTracialFunctional (ℂ × ℂ) where
  toPositiveLinearMap := .mk₀ (LinearMap.snd ℂ ℂ ℂ) fun _ hx => hx.2
  map_mul_comm' a b := by simp [mul_comm]

/-- The second-coordinate functional evaluates as `(a, b) ↦ b`. -/
@[simp]
theorem sndTracialFunctional_apply (x : ℂ × ℂ) : sndTracialFunctional x = x.2 :=
  (rfl)

/-- The second-coordinate functional on `ℂ × ℂ` is a tracial state. -/
theorem isKMSState_sndTracialFunctional :
    (CStarAction.trivial : CStarAction (Multiplicative ℝ) (ℂ × ℂ)).IsKMSState 0
      sndTracialFunctional.toPositiveContinuousLinearMap := by
  simp [isKMSState_trivial_zero_iff_map_one]

/-- The pullback of `(a, b) ↦ b` along `λ ↦ (λ, 0)` is zero. -/
theorem sndTracialFunctional_comp_inl_apply (z : ℂ) :
    sndTracialFunctional.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) z = 0 := by
  simp

/-- A pullback of a tracial state along a nonunital star homomorphism need not be a state: the
pullback of `(a, b) ↦ b` along `λ ↦ (λ, 0)` is the zero functional. So the natural pairing with
`K₀` uses positive tracial functionals rather than tracial states. -/
theorem not_isKMSState_sndTracialFunctional_comp_inl :
    ¬ (CStarAction.trivial : CStarAction (Multiplicative ℝ) ℂ).IsKMSState 0
      (sndTracialFunctional.comp
        (NonUnitalStarAlgHom.inl ℂ ℂ ℂ)).toPositiveContinuousLinearMap := by
  rw [isKMSState_trivial_zero_iff_map_one, sndTracialFunctional_comp_inl_apply]
  exact zero_ne_one

end Example

end TauCeti
