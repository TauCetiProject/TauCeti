/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Ring-theoretic properties of trivial square-zero extensions

For a commutative ring `R` and an `R`-module `M`, the trivial square-zero extension
`TrivSqZeroExt R M` is the ring `R ⊕ M` in which `M` is an ideal of square zero. As an `R`-module
it is `R × M` (`TrivSqZeroExt.linearEquivProd`).

This file records the standard finiteness and dimension invariants: over a local ring `R` the
extension is local and the inclusion of `R` is a local homomorphism; it is finite, free,
respectively Noetherian, when `M` is finite, free (and `R` is Noetherian); its `finrank` is the
sum of those of `R` and `M`; and, being integral over `R`, it has the Krull dimension of `R`.

Taking for `M` the residue field of a local ring `A` gives `A[z] ⧸ (z², 𝔪z)`, a finite local
`A`-algebra with the dimension of `A` and of depth zero, which is not flat over `A` unless `A` is
a field (`TrivSqZeroExt.depth_eq_zero`, `TrivSqZeroExt.not_flat`).

## Main results

* `TrivSqZeroExt.linearEquivProd`: as an `S`-module, `TrivSqZeroExt R M ≃ₗ[S] R × M`.
* `TrivSqZeroExt.finrank_eq`: `finrank S (TrivSqZeroExt R M) = finrank S R + finrank S M`.
* `TrivSqZeroExt.isLocalRing`: the trivial square-zero extension of a local ring is local.
* `TrivSqZeroExt.mem_maximalIdeal_iff`: its maximal ideal consists of the elements whose first
  component lies in the maximal ideal of `R`.
* `TrivSqZeroExt.ringKrullDim_eq`: `TrivSqZeroExt R M` has the Krull dimension of `R`.
-/
public section

open IsLocalRing

namespace TrivSqZeroExt

section Module

/-- As an `S`-module, the trivial square-zero extension `TrivSqZeroExt R M` is `R × M`. -/
def linearEquivProd (S R M : Type*) [Semiring S] [AddCommMonoid R] [AddCommMonoid M]
    [Module S R] [Module S M] : TrivSqZeroExt R M ≃ₗ[S] R × M where
  toFun x := (x.fst, x.snd)
  invFun p := inl p.1 + inr p.2
  left_inv := inl_fst_add_inr_snd_eq
  right_inv p := by ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem linearEquivProd_apply {S R M : Type*} [Semiring S] [AddCommMonoid R] [AddCommMonoid M]
    [Module S R] [Module S M] (x : TrivSqZeroExt R M) :
    linearEquivProd S R M x = (x.fst, x.snd) := by rfl

@[simp]
theorem linearEquivProd_symm_apply {S R M : Type*} [Semiring S] [AddCommMonoid R]
    [AddCommMonoid M] [Module S R] [Module S M] (p : R × M) :
    (linearEquivProd S R M).symm p = inl p.1 + inr p.2 := by rfl

/-- The trivial square-zero extension of two free `S`-modules is free. -/
instance moduleFree {S R M : Type*} [Semiring S] [AddCommMonoid R] [AddCommMonoid M]
    [Module S R] [Module S M] [Module.Free S R] [Module.Free S M] :
    Module.Free S (TrivSqZeroExt R M) :=
  Module.Free.of_equiv (linearEquivProd S R M).symm

/-- The `finrank` of a trivial square-zero extension is the sum of the `finrank`s of its base
and infinitesimal parts. -/
theorem finrank_eq {S R M : Type*} [Ring S] [StrongRankCondition S] [AddCommGroup R]
    [AddCommGroup M] [Module S R] [Module S M] [Module.Free S R] [Module.Finite S R]
    [Module.Free S M] [Module.Finite S M] :
    Module.finrank S (TrivSqZeroExt R M) = Module.finrank S R + Module.finrank S M :=
  (linearEquivProd S R M).finrank_eq.trans Module.finrank_prod

end Module

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

/-- The inclusion of a local ring into its trivial square-zero extension is a local
homomorphism. -/
instance isLocalHom_algebraMap : IsLocalHom (algebraMap R (TrivSqZeroExt R M)) :=
  ⟨fun r h ↦ by rwa [algebraMap_eq_inl, isUnit_inl_iff] at h⟩

end LocalRing

/-- The trivial square-zero extension by a finite module is a finite algebra. -/
instance [Module.Finite R M] : Module.Finite R (TrivSqZeroExt R M) :=
  inferInstanceAs (Module.Finite R (R × M))

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
