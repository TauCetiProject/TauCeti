/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Intertwiners of joint representations

Two commuting unital star representations `π` and `σ` on a Hilbert space determine
`Algebra.TensorProduct.starLift π σ`, the joint representation of their algebraic tensor
product. A bounded linear map intertwines two joint representations exactly when it
intertwines both constituent representations.

For an M–N Hilbert bimodule, take the second algebra to be `Nᵐᵒᵖ`. The tensor `x ⊗ yᵒᵖ`
then acts by `ξ ↦ xξy`; the theorem below identifies bimodule intertwiners with joint
representation intertwiners, without any normality assumptions on the actions.
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct

namespace ContinuousLinearMap

variable {𝕜 A B H K : Type*} [RCLike 𝕜]
  [Semiring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A]
  [Semiring B] [StarRing B] [Algebra 𝕜 B] [StarModule 𝕜 B]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- A bounded operator intertwines joint representations if and only if it intertwines
both commuting constituent representations. -/
theorem comp_starLift_iff (T : H →L[𝕜] K)
    (π : A →⋆ₐ[𝕜] H →L[𝕜] H) (σ : B →⋆ₐ[𝕜] H →L[𝕜] H)
    (π' : A →⋆ₐ[𝕜] K →L[𝕜] K) (σ' : B →⋆ₐ[𝕜] K →L[𝕜] K)
    (h : ∀ a b, Commute (π a) (σ b)) (h' : ∀ a b, Commute (π' a) (σ' b)) :
    (∀ z, T.comp (starLift π σ h z) = (starLift π' σ' h' z).comp T) ↔
      (∀ a, T.comp (π a) = (π' a).comp T) ∧
      (∀ b, T.comp (σ b) = (σ' b).comp T) := by
  constructor
  · intro hz
    constructor
    · intro a
      simpa using hz (a ⊗ₜ[𝕜] (1 : B))
    · intro b
      simpa using hz ((1 : A) ⊗ₜ[𝕜] b)
  · rintro ⟨hπ, hσ⟩ z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      ext ξ
      have hπξ (η : H) := congrArg (fun S : H →L[𝕜] K => S η) (hπ a)
      have hσξ := congrArg (fun S : H →L[𝕜] K => S ξ) (hσ b)
      simpa only [starLift_tmul, comp_apply, mul_apply_eq_comp] using
        (hπξ (σ b ξ)).trans (congrArg (π' a) hσξ)
    | add z w hz hw => simp only [map_add, comp_add, add_comp, hz, hw]

end ContinuousLinearMap
