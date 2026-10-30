/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.TrivSqZeroExt
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Pure

/-!
# Trivial square-zero extensions of depth zero

Let `R` be a local ring and `M` an `R`-module of depth zero, that is, with a nonzero element
killed by the maximal ideal `𝔪` of `R`. Then the trivial square-zero extension
`S = TrivSqZeroExt R M` has depth zero over itself, since that element of `M ⊆ S` is killed by
the maximal ideal `𝔪 ⊕ M` of `S`. As `S` has the Krull dimension of `R`, it is not
Cohen–Macaulay unless `R` has dimension zero.

The main example is `M = R ⧸ 𝔪`, where `S ≅ R[z] ⧸ (z², 𝔪z)` with `z = (0, 1)`. For a regular
local ring `R` of positive dimension, `R → S` is a finite local homomorphism of Noetherian local
rings satisfying the dimension formula `dim S = dim R + dim S ⧸ 𝔪S`, since the closed fibre
`S ⧸ 𝔪S = κ[z] ⧸ (z²)` has dimension zero
(`TauCeti.ringKrullDim_quotient_map_maximalIdeal_eq_zero`). Yet `S` is not flat over `R`. So the
Cohen–Macaulay hypothesis of miracle flatness (Stacks, Lemma 10.128.1 (00R4)) cannot be dropped.

## Main results

* `TrivSqZeroExt.depth_eq_zero`: the trivial square-zero extension by a module of depth zero has
  depth zero.
* `TrivSqZeroExt.not_isCohenMacaulay`: if moreover `R` has positive dimension, it is not
  Cohen–Macaulay.
* `TrivSqZeroExt.not_flat`: over a Noetherian local ring that is not a field,
  `TrivSqZeroExt R (R ⧸ 𝔪)` is not flat.

## References

* [Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), miracle flatness,
  whose Cohen–Macaulay hypothesis this example shows to be necessary.
-/

public section

open IsLocalRing

universe u v

namespace TrivSqZeroExt

variable {R : Type u} [CommRing R] [IsLocalRing R]

section DepthZero

variable {M : Type v} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [Small.{v} R]

/-- The trivial square-zero extension of a local ring by a module of depth zero has depth zero
over itself. -/
theorem depth_eq_zero (hM : depth (ModuleCat.of R M) = 0) :
    depth (ModuleCat.of (TrivSqZeroExt R M) (TrivSqZeroExt R M)) = 0 := by
  rw [depth_eq_zero_iff_nontrivial_linearMap] at hM ⊢
  obtain ⟨f, hf⟩ := exists_ne (0 : R ⧸ maximalIdeal R →ₗ[R] M)
  -- `m` is the image of `1`; it is nonzero, and killed by the maximal ideal of `R`.
  set m := f (Submodule.mkQ _ 1)
  have hm : m ≠ 0 := fun h ↦ hf <| Submodule.linearMap_qext _ <| LinearMap.ext_ring (by simpa)
  have hker : maximalIdeal (TrivSqZeroExt R M) ≤
      LinearMap.ker (LinearMap.toSpanSingleton _ _ (inr m : TrivSqZeroExt R M)) := fun x hx ↦ by
    have h0 : Submodule.mkQ (maximalIdeal R) x.fst = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (mem_maximalIdeal_iff.1 hx)
    have : x.fst • m = 0 := by rw [← map_smul, ← map_smul, smul_eq_mul, mul_one, h0, map_zero]
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
    ext <;> simp [this]
  -- So `s ↦ s • m` descends to a nonzero map from the residue field of `TrivSqZeroExt R M`.
  refine ⟨⟨(maximalIdeal (TrivSqZeroExt R M)).liftQ _ hker, 0,
    fun h ↦ hm (inr_injective (R := R) ?_)⟩⟩
  have h1 := LinearMap.congr_fun h (Submodule.mkQ _ 1)
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul,
    LinearMap.zero_apply] at h1
  rw [h1, inr_zero]

/-- The trivial square-zero extension of a local ring of positive dimension by a module of depth
zero is not Cohen–Macaulay. -/
theorem not_isCohenMacaulay (hM : depth (ModuleCat.of R M) = 0) (hR : ringKrullDim R ≠ 0) :
    ¬ Module.IsCohenMacaulay (TrivSqZeroExt R M) (TrivSqZeroExt R M) := fun h ↦ by
  have := h.depth_eq
  rw [depth_eq_zero hM, Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq] at this
  exact hR (by exact_mod_cast this.symm)

end DepthZero

/-- Over a Noetherian local ring which is not a field, `TrivSqZeroExt R (R ⧸ 𝔪)` is not flat. -/
theorem not_flat [IsNoetherianRing R] (h : ¬ IsField R) :
    ¬ Module.Flat R (TrivSqZeroExt R (R ⧸ maximalIdeal R)) := fun _ ↦ by
  -- The direct summand `R ⧸ 𝔪` would be flat, making `𝔪` idempotent and hence zero.
  have : (maximalIdeal R).Pure := .of_retract (inrHom R _) (sndHom R _) (by ext; simp)
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing _).1
    (maximalIdeal R).isIdempotentElem_of_pure with h' | h'
  · exact h (isField_iff_maximalIdeal_eq.2 h')
  · exact (maximalIdeal.isMaximal R).ne_top h'

end TrivSqZeroExt
