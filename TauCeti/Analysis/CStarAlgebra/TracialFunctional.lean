/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Prod

/-!
# Positive tracial functionals and tracial states

A **positive tracial functional** on a C⋆-algebra `A` is a positive linear functional
`τ : A → ℂ` with `τ (a * b) = τ (b * a)`. Like every positive functional on a C⋆-algebra it is
bounded, but it need not have norm one; a **tracial state** is a positive tracial functional of
norm one. These are the functionals that pair with `K₀(A)` through the unnormalized matrix trace
`τ_m(p) = ∑ i, τ (p i i)`.

Positive tracial functionals pull back along star homomorphisms: for `φ : A →⋆ₙₐ[ℂ] B` and a
positive tracial functional `τ` of `B`, the composite `τ ∘ φ` is a positive tracial functional of
`A`. The composite of a tracial state with a star homomorphism need not be a state, for instance
`(λ ↦ (λ, 0))` followed by `(a, b) ↦ b`, which is zero; it is one when `A` and `B` are unital and
`φ` is unital.

## Main declarations

* `TauCeti.PositiveTracialFunctional`: positive tracial functionals, with their `FunLike`,
  `LinearMapClass` and `OrderHomClass` instances, and `PositiveTracialFunctional.map_mul_comm`.
* `TauCeti.PositiveTracialFunctional.toPositiveContinuousLinearMap`: the functional is bounded.
* `TauCeti.PositiveTracialFunctional.comp`: pullback along a star homomorphism, with
  `comp_id` and `comp_comp`.
* `TauCeti.PositiveTracialFunctional.IsTracialState`: norm one, and for unital `A`,
  `isTracialState_iff_map_one`: this means `τ 1 = 1`. Tracial states pull back to tracial states
  along unital star homomorphisms, `IsTracialState.comp`.
* `TauCeti.not_isTracialState_sndTracialFunctional_comp_inl`: the pullback of the tracial state
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

instance : FunLike (PositiveTracialFunctional A) A ℂ where
  coe τ := τ.toPositiveLinearMap
  coe_injective τ σ h := by
    cases τ
    cases σ
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (PositiveTracialFunctional A) ℂ A ℂ where
  map_add τ := map_add τ.toPositiveLinearMap
  map_smulₛₗ τ := map_smulₛₗ τ.toPositiveLinearMap

instance : OrderHomClass (PositiveTracialFunctional A) A ℂ where
  map_rel τ := fun {_ _} h => τ.toPositiveLinearMap.monotone h

/-- Positive tracial functionals are determined by their values. -/
@[ext]
theorem ext {τ σ : PositiveTracialFunctional A} (h : ∀ a, τ a = σ a) : τ = σ :=
  DFunLike.ext τ σ h

@[simp]
theorem toPositiveLinearMap_apply (τ : PositiveTracialFunctional A) (a : A) :
    τ.toPositiveLinearMap a = τ a :=
  rfl

/-- A positive tracial functional is tracial. -/
theorem map_mul_comm (τ : PositiveTracialFunctional A) (a b : A) : τ (a * b) = τ (b * a) :=
  τ.map_mul_comm' a b

/-- A positive tracial functional is bounded, as every positive functional on a C⋆-algebra is. -/
@[expose] noncomputable def toPositiveContinuousLinearMap (τ : PositiveTracialFunctional A) :
    A →P[ℂ] ℂ :=
  .ofClass τ

@[simp]
theorem toPositiveContinuousLinearMap_apply (τ : PositiveTracialFunctional A) (a : A) :
    τ.toPositiveContinuousLinearMap a = τ a :=
  rfl

/-- The bound `‖τ a‖ ≤ ‖τ‖ ‖a‖`, with `‖τ‖` the operator norm of the bounded functional. -/
theorem norm_apply_le (τ : PositiveTracialFunctional A) (a : A) :
    ‖τ a‖ ≤ ‖(τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ)‖ * ‖a‖ :=
  (τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ).le_opNorm a

/-- **Naturality.** The pullback `τ ∘ φ` of a positive tracial functional along a star
homomorphism. -/
@[expose] noncomputable def comp (τ : PositiveTracialFunctional B) (φ : A →⋆ₙₐ[ℂ] B) :
    PositiveTracialFunctional A where
  toPositiveLinearMap := τ.toPositiveLinearMap.comp (.ofClass φ)
  map_mul_comm' a b := by
    change τ (φ (a * b)) = τ (φ (b * a))
    rw [map_mul φ, map_mul φ]
    exact τ.map_mul_comm (φ a) (φ b)

@[simp]
theorem comp_apply (τ : PositiveTracialFunctional B) (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    τ.comp φ a = τ (φ a) :=
  rfl

@[simp]
theorem comp_id (τ : PositiveTracialFunctional A) : τ.comp (NonUnitalStarAlgHom.id ℂ A) = τ :=
  rfl

theorem comp_comp (τ : PositiveTracialFunctional C) (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    (τ.comp ψ).comp φ = τ.comp (ψ.comp φ) :=
  rfl

/-- A **tracial state**: a positive tracial functional of norm one. -/
def IsTracialState (τ : PositiveTracialFunctional A) : Prop :=
  ‖(τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ)‖ = 1

end PositiveTracialFunctional

end NonUnital

section Unital

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PositiveTracialFunctional

/-- On a unital C⋆-algebra the norm of a positive tracial functional is its value at `1`. -/
theorem ofReal_norm_eq_map_one (τ : PositiveTracialFunctional A) :
    (‖(τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ)‖ : ℂ) = τ 1 :=
  τ.toPositiveContinuousLinearMap.ofReal_opNorm_eq_map_one

/-- On a unital C⋆-algebra a positive tracial functional is a tracial state exactly when
`τ 1 = 1`. -/
theorem isTracialState_iff_map_one (τ : PositiveTracialFunctional A) :
    τ.IsTracialState ↔ τ 1 = 1 := by
  rw [IsTracialState, ← ofReal_norm_eq_map_one, Complex.ofReal_eq_one]

/-- Tracial states pull back to tracial states along unital star homomorphisms. -/
theorem IsTracialState.comp {τ : PositiveTracialFunctional B} (hτ : τ.IsTracialState)
    (φ : A →⋆ₐ[ℂ] B) : (τ.comp φ.toNonUnitalStarAlgHom).IsTracialState := by
  rw [isTracialState_iff_map_one] at hτ ⊢
  simpa using hτ

end PositiveTracialFunctional

end Unital

section Example

open PositiveTracialFunctional

/-- The second-coordinate functional `(a, b) ↦ b` on `ℂ × ℂ`, a tracial state. -/
@[expose] noncomputable def sndTracialFunctional : PositiveTracialFunctional (ℂ × ℂ) where
  toPositiveLinearMap := .mk₀ (LinearMap.snd ℂ ℂ ℂ) fun _ hx => hx.2
  map_mul_comm' a b := by simp [mul_comm]

theorem sndTracialFunctional_isTracialState : sndTracialFunctional.IsTracialState := by
  rw [isTracialState_iff_map_one]
  rfl

/-- A pullback of a tracial state along a nonunital star homomorphism need not be a state: the
pullback of `(a, b) ↦ b` along `λ ↦ (λ, 0)` is the zero functional. This is why the pairing with
`K₀` is set up for positive tracial functionals rather than tracial states. -/
theorem sndTracialFunctional_comp_inl_apply (z : ℂ) :
    sndTracialFunctional.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) z = 0 :=
  rfl

theorem not_isTracialState_sndTracialFunctional_comp_inl :
    ¬ (sndTracialFunctional.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ)).IsTracialState := by
  rw [isTracialState_iff_map_one, sndTracialFunctional_comp_inl_apply]
  exact zero_ne_one

end Example

end TauCeti
