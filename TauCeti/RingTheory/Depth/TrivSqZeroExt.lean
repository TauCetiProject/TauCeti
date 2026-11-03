/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Basic
public import TauCeti.RingTheory.TrivSqZeroExt

/-!
# Trivial square-zero extensions of depth zero

Let `R` be a local ring and `M` an `R`-module of depth zero, that is, with a nonzero element
killed by the maximal ideal `𝔪` of `R`. Then the trivial square-zero extension
`S = TrivSqZeroExt R M` has depth zero over itself, since that element of `M ⊆ S` is killed by
the maximal ideal `𝔪 ⊕ M` of `S`.

## Main results

* `TrivSqZeroExt.depth_eq_zero`: the trivial square-zero extension by a module of depth zero has
  depth zero.
-/

public section

open IsLocalRing

universe u v

namespace TrivSqZeroExt

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
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

end TrivSqZeroExt
