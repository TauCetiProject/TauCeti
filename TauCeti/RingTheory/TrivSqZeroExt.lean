/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
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
extension is local and the inclusion of `R` is a local homomorphism; the square-zero ideal
`TrivSqZeroExt.kerIdeal R M` is `R`-linearly equivalent to `M` and is finitely generated whenever
`M` is finite; `TrivSqZeroExt R M` is finite, respectively Noetherian, when `M` is finite (and `R`
is Noetherian); and, being integral over `R`, it has the Krull dimension of `R`. Over a free
module of finite rank `n` it is free of rank `n + 1`.

Taking for `M` the residue field of a local ring `A` gives `A[z] ⧸ (z², 𝔪z)`, a finite local
`A`-algebra with the dimension of `A` and of depth zero, which is not flat over `A` unless `A` is
a field (`TrivSqZeroExt.depth_eq_zero`, `TrivSqZeroExt.not_flat`).

## Main results

* `TrivSqZeroExt.kerIdealLinearEquiv`: `M ≃ₗ[R] TrivSqZeroExt.kerIdeal R M`.
* `TrivSqZeroExt.fg_kerIdeal`: `TrivSqZeroExt.kerIdeal R M` is finitely generated when `M` is
  finite.
* `TrivSqZeroExt.isLocalRing`: the trivial square-zero extension of a local ring is local.
* `TrivSqZeroExt.mem_maximalIdeal_iff`: its maximal ideal consists of the elements whose first
  component lies in the maximal ideal of `R`.
* `TrivSqZeroExt.ringKrullDim_eq`: `TrivSqZeroExt R M` has the Krull dimension of `R`.
* `TrivSqZeroExt.finrank_eq_finrank_add_one`: `TrivSqZeroExt R M` has rank `finrank R M + 1`.
-/
public section

open IsLocalRing

namespace TrivSqZeroExt

section KerIdeal

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

/-- The square-zero ideal `TrivSqZeroExt.kerIdeal R M` is `R`-linearly equivalent to `M`. -/
def kerIdealLinearEquiv : M ≃ₗ[R] kerIdeal R M where
  toFun m := ⟨inr m, (mem_kerIdeal_iff_inr R M _).mpr rfl⟩
  invFun z := z.val.snd
  map_add' _ _ := Subtype.ext (inr_add R _ _)
  map_smul' r m := Subtype.ext (by simp [Algebra.smul_def, algebraMap_eq_inl])
  left_inv _ := by simp
  right_inv z := Subtype.ext ((mem_kerIdeal_iff_inr R M z.val).mp z.property).symm

variable {R M}

/-- `kerIdealLinearEquiv` sends `m` to `inr m`. -/
@[simp]
theorem coe_kerIdealLinearEquiv (m : M) :
    (kerIdealLinearEquiv R M m : TrivSqZeroExt R M) = inr m :=
  (rfl)

/-- The inverse of `kerIdealLinearEquiv` extracts the second component `snd`. -/
@[simp]
theorem kerIdealLinearEquiv_symm_apply (z : kerIdeal R M) :
    (kerIdealLinearEquiv R M).symm z = z.val.snd :=
  (rfl)

/-- When `M` is a finite `R`-module, the square-zero ideal `TrivSqZeroExt.kerIdeal R M` is finitely
generated. -/
theorem fg_kerIdeal [Module.Finite R M] : (kerIdeal R M).FG :=
  (Module.Finite.iff_fg.mp (Module.Finite.equiv (kerIdealLinearEquiv R M))).of_restrictScalars R

end KerIdeal

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
