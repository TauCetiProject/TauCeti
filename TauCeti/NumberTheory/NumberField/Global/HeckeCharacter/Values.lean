/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.InfinityType.Basic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.PrincipalPower
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Powers of algebraic Hecke character values

A character on the finite ideles with open kernel and algebraic infinity type takes
algebraic values. In fact one exponent works for every idele: a power of the idele has
a principal representative modulo integral units in the kernel, so its character value
is given by the infinity type evaluated on that same representative.

This is the power formula for characters of Weil type `A₀` (A. Weil, *Basic Number Theory*,
Chapter VII, §3), in the form of `New.AlgHeckeChar.exists_pow_eq_prod` in lsernau/grh-lean,
`grh/src/Lib/ClassField/HeckeCharacter/AlgebraicValues.lean`, revision `72fead1`.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
open TauCeti.GlobalNumberFields
open scoped NumberField

namespace MonoidHom

/-- For a finite idele character with open kernel and infinity type `n`, one positive power
of each idele has the valuations of a global element `γ` and character value given by the
embedding monomial of exponent `-n` at that same `γ`. -/
theorem exists_pow_eq_prod_of_isOpen_ker {K : Type*} [Field K] [NumberField K]
    (θ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ) (n : AlgebraicInfinityType K)
    (hθ : IsOpen (θ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ))
    (hprincipal : θ.comp (unitEmbedding (𝓞 K) K) = (-n).embeddingCharacter) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : (FiniteAdeleRing (𝓞 K) K)ˣ,
      ∃ γ : Kˣ, y ^ N / unitEmbedding (𝓞 K) K γ ∈ integralUnits (𝓞 K) K ∧
        (θ y : ℂ) ^ N = ∏ τ : K →+* ℂ, τ (γ : K) ^ (-n τ) := by
  obtain ⟨N, hN, h⟩ := θ.exists_pow_eq_apply_unitEmbedding_of_isOpen_ker hθ
  refine ⟨N, hN, fun y ↦ ?_⟩
  obtain ⟨γ, hval, he⟩ := h y
  refine ⟨γ, hval, ?_⟩
  have hp := DFunLike.congr_fun hprincipal γ
  rw [MonoidHom.comp_apply] at hp
  simpa only [Units.val_pow_eq_pow_val, AlgebraicInfinityType.coe_embeddingCharacter_apply,
    Pi.neg_apply] using congrArg Units.val (he.trans hp)

/-- A finite idele character with open kernel takes algebraic values if it does so on
principal ideles. No choice of infinity type is required for this implication. -/
theorem isAlgebraic_apply_of_isOpen_ker {K : Type*} [Field K] [NumberField K]
    (θ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ))
    (hprincipal : ∀ γ : Kˣ, IsAlgebraic ℚ (θ (unitEmbedding (𝓞 K) K γ) : ℂ))
    (y : (FiniteAdeleRing (𝓞 K) K)ˣ) : IsAlgebraic ℚ (θ y : ℂ) := by
  obtain ⟨N, hN, h⟩ := θ.exists_pow_eq_apply_unitEmbedding_of_isOpen_ker hθ
  obtain ⟨γ, _, hγ⟩ := h y
  have he : (θ y : ℂ) ^ N = (θ (unitEmbedding (𝓞 K) K γ) : ℂ) := by
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hγ
  exact IsAlgebraic.of_pow hN (he ▸ hprincipal γ)

/-- A finite idele character with open kernel and principal values given by an algebraic
infinity type takes algebraic values on all finite ideles. -/
theorem isAlgebraic_apply_of_embeddingCharacter {K : Type*} [Field K] [NumberField K]
    (θ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ) (n : AlgebraicInfinityType K)
    (hθ : IsOpen (θ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ))
    (hprincipal : θ.comp (unitEmbedding (𝓞 K) K) = (-n).embeddingCharacter)
    (y : (FiniteAdeleRing (𝓞 K) K)ˣ) : IsAlgebraic ℚ (θ y : ℂ) := by
  apply θ.isAlgebraic_apply_of_isOpen_ker hθ _ y
  intro γ
  have he := congrArg Units.val (DFunLike.congr_fun hprincipal γ)
  rw [MonoidHom.comp_apply, AlgebraicInfinityType.coe_embeddingCharacter_apply] at he
  rw [he]
  refine (IsIntegral.prod _ fun τ _ ↦ ?_).isAlgebraic
  exact ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ : K)).algHom
    τ.toRatAlgHom).isIntegral.zpow _

end MonoidHom
