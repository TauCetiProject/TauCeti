/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Ring-theoretic properties of trivial square-zero extensions

For a commutative ring `R` and an `R`-module `M`, the trivial square-zero extension
`TrivSqZeroExt R M` is the ring `R ⊕ M` in which `M` is an ideal of square zero. As an `R`-module
it is `R × M`.

This file records the standard finiteness and dimension invariants: over a local ring `R` the
extension is local and the inclusion of `R` is a local homomorphism; it is finite, respectively
Noetherian, when `M` is finite (and `R` is Noetherian); and, being integral over `R`, it has the
Krull dimension of `R`. Over a free module of finite rank `n` it is free of rank `n + 1`.

Taking for `M` the residue field of a local ring `A` gives `A[z] ⧸ (z², 𝔪z)`, a finite local
`A`-algebra with the dimension of `A` and of depth zero, which is not flat over `A` unless `A` is
a field (`TrivSqZeroExt.depth_eq_zero`, `TrivSqZeroExt.not_flat`).

## Main results

* `TrivSqZeroExt.isLocalRing`: the trivial square-zero extension of a local ring is local.
* `TrivSqZeroExt.mem_maximalIdeal_iff`: its maximal ideal consists of the elements whose first
  component lies in the maximal ideal of `R`; in particular, for `M = R ⧸ 𝔪` every element of the
  maximal ideal annihilates `inr (R ⧸ 𝔪)` (`TrivSqZeroExt.mul_inr_eq_zero_of_mem_maximalIdeal`).
* `TrivSqZeroExt.ringKrullDim_eq`: `TrivSqZeroExt R M` has the Krull dimension of `R`.
* `TrivSqZeroExt.finrank_eq_finrank_add_one`: `TrivSqZeroExt R M` has rank `finrank R M + 1`.
-/
public section

open IsLocalRing

namespace TrivSqZeroExt

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

section LocalRing

variable [IsLocalRing R]

/-- The trivial square-zero extension of a local ring is local. -/
instance isLocalRing : IsLocalRing (TrivSqZeroExt R M) :=
  .of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    simpa [isUnit_iff_isUnit_fst] using isUnit_or_isUnit_one_sub_self x.fst

/-- An element of the trivial square-zero extension of a local ring lies in the maximal ideal if
and only if its first component does. -/
theorem mem_maximalIdeal_iff {x : TrivSqZeroExt R M} :
    x ∈ maximalIdeal (TrivSqZeroExt R M) ↔ x.fst ∈ maximalIdeal R := by
  simp [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_isUnit_fst]

/-- In the trivial square-zero extension of a local ring `(R, 𝔪)` by its residue field `R ⧸ 𝔪`,
every element of the maximal ideal annihilates `inr (R ⧸ 𝔪)`. -/
theorem mul_inr_eq_zero_of_mem_maximalIdeal {x : TrivSqZeroExt R (R ⧸ maximalIdeal R)}
    (hx : x ∈ maximalIdeal (TrivSqZeroExt R (R ⧸ maximalIdeal R)))
    (b : R ⧸ maximalIdeal R) : x * inr b = 0 := by
  rw [mem_maximalIdeal_iff] at hx
  induction b using Submodule.Quotient.induction_on with | H a =>
    ext
    · simp
    · simpa [Algebra.smul_def] using Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right a _ hx)

/-- The inclusion of a local ring into its trivial square-zero extension is a local
homomorphism. -/
instance isLocalHom_algebraMap : IsLocalHom (algebraMap R (TrivSqZeroExt R M)) :=
  ⟨fun r h ↦ by rwa [algebraMap_eq_inl, isUnit_inl_iff] at h⟩

end LocalRing

/-- The trivial square-zero extension by a finite module is a finite algebra. -/
instance [Module.Finite R M] : Module.Finite R (TrivSqZeroExt R M) :=
  inferInstanceAs (Module.Finite R (R × M))

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
/-- The trivial square-zero extension by a free module is a free module. -/
instance [Module.Free R M] : Module.Free R (TrivSqZeroExt R M) :=
  inferInstanceAs (Module.Free R (R × M))

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
/-- The trivial square-zero extension by a free module of finite rank `n` has rank `n + 1`. -/
theorem finrank_eq_finrank_add_one [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (TrivSqZeroExt R M) = Module.finrank R M + 1 := by
  -- As a module, `TrivSqZeroExt R M` is the product `R × M`.
  rw [show Module.finrank R (TrivSqZeroExt R M) = Module.finrank R (R × M) from rfl,
    Module.finrank_prod, Module.finrank_self, add_comm]

/-- The trivial square-zero extension of a Noetherian ring by a finite module is Noetherian. -/
instance [IsNoetherianRing R] [Module.Finite R M] : IsNoetherianRing (TrivSqZeroExt R M) :=
  .of_finite R _

/-- Every element of the trivial square-zero extension is integral over `R`: it is the sum of an
element of `R` and an element of `M`, whose square is zero. -/
instance : Algebra.IsIntegral R (TrivSqZeroExt R M) where
  isIntegral x := by
    rw [← inl_fst_add_inr_snd_eq x, ← algebraMap_eq_inl]
    refine isIntegral_algebraMap.add (IsIntegral.of_pow two_pos ?_)
    rw [sq, inr_mul_inr]
    exact isIntegral_zero

/-- The inclusion of `R` into its trivial square-zero extension is injective. -/
instance : FaithfulSMul R (TrivSqZeroExt R M) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 inl_injective

/-- The trivial square-zero extension has the Krull dimension of the base ring. -/
theorem ringKrullDim_eq : ringKrullDim (TrivSqZeroExt R M) = ringKrullDim R :=
  TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul

end TrivSqZeroExt
