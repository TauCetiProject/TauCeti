/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# Restriction of scalars for root pairings

Given a balanced root pairing `P` over a field `L` whose pairings take values in a subfield `K`
(`P.IsValuedIn K`), Mathlib's `RootPairing.restrictScalars' K` restricts `P` to a *root system* over
`K` on the `K`-spans `span K (range P.root)` and `span K (range P.coroot)`. Two specializations are
central in applications:

* `K = L` (available for any balanced root pairing over `L`, and in particular for any finite root
  pairing over a field of characteristic zero by `RootPairing.instIsBalancedOfCharZero`), which cuts
  an ambient root pairing with central directions down to the spanning root system on its root and
  coroot spans over the *same* field `L`;
* `K = ℚ` (or `ℝ` inside `ℂ`) for crystallographic pairings (`RootPairing.restrictScalars`), which
  simultaneously passes to the root span and descends the scalar field.

This file develops the elementary scalar-restriction API—reflections, functionals, Coxeter weights,
`IsValuedIn`, and `IsReduced`—for `P.restrictScalars' K`.

## Main results

* `RootPairing.isValuedIn_restrictScalars'` and `RootPairing.isReduced_restrictScalars'`:
  `P.restrictScalars' K` inherits `IsValuedIn T` (in particular `IsCrystallographic`) and
  `IsReduced` from `P`.
* `RootPairing.coe_restrictScalars'_reflection_apply` and
  `RootPairing.coe_restrictScalars'_coreflection_apply`: reflections and coreflections of `P`
  restrict to those of `P.restrictScalars' K`.
* `RootPairing.algebraMap_coroot'_restrictScalars'` and `RootPairing.coroot'_restrictScalars'_self`:
  the coroot functionals of `P.restrictScalars' K` are those of `P`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

open Function Set Submodule

namespace RootPairing

section Basic

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- `RootPairing.restrictScalars'` preserves the reflection permutations on root indices. -/
@[simp]
theorem restrictScalars'_reflectionPerm :
    (P.restrictScalars' K).reflectionPerm = P.reflectionPerm :=
  (rfl)

/-- Under `algebraMap K L`, the Coxeter weights of `P.restrictScalars' K` agree with those of
`P`. -/
@[simp]
theorem algebraMap_restrictScalars'_coxeterWeight (i j : ι) :
    algebraMap K L ((P.restrictScalars' K).coxeterWeight i j) = P.coxeterWeight i j := by
  simp [coxeterWeight]

/-- Each root reflection of `P.restrictScalars' K` is the restriction of the corresponding
reflection of `P`. -/
@[simp]
theorem coe_restrictScalars'_reflection_apply (i : ι) (x : span K (range P.root)) :
    ((P.restrictScalars' K).reflection i x : M) = P.reflection i x := by
  rw [reflection_apply, Submodule.coe_sub, SetLike.val_smul, restrictScalars_coe_root,
    algebra_compatible_smul L, reflection_apply]
  dsimp only [coroot', LinearMap.flip_apply]
  rw [← restrictScalars_coe_coroot (P := P) (K := K), restrictScalars_toLinearMap_apply_apply,
    restrictScalars_coe_coroot]

/-- Each coreflection of `P.restrictScalars' K` is the restriction of the corresponding
coreflection of `P`. -/
@[simp]
theorem coe_restrictScalars'_coreflection_apply (i : ι) (y : span K (range P.coroot)) :
    ((P.restrictScalars' K).coreflection i y : N) = P.coreflection i y := by
  rw [coreflection_apply, Submodule.coe_sub, SetLike.val_smul, restrictScalars_coe_coroot,
    algebra_compatible_smul L, coreflection_apply]
  dsimp only [root']
  rw [← restrictScalars_coe_root (P := P) (K := K), restrictScalars_toLinearMap_apply_apply,
    restrictScalars_coe_root]

/-- The coroot functionals of `P.restrictScalars' K` are those of `P`, read on the `K`-span of the
roots. -/
theorem algebraMap_coroot'_restrictScalars' (i : ι) (x : span K (range P.root)) :
    algebraMap K L ((P.restrictScalars' K).coroot' i x) = P.coroot' i x := by
  simp [coroot', restrictScalars_toLinearMap_apply_apply]

section IsValuedIn

variable (T : Type*) [CommRing T] [Algebra T K] [Algebra T L] [IsScalarTower T K L]

/-- If `P` takes pairing values in `T`, then so does `P.restrictScalars' K`; for `T = ℤ` this makes
`P.restrictScalars' K` crystallographic whenever `P` is. -/
instance isValuedIn_restrictScalars' [P.IsValuedIn T] :
    (P.restrictScalars' K).IsValuedIn T where
  exists_value i j := by
    obtain ⟨t, ht⟩ := P.exists_value (S := T) i j
    refine ⟨t, FaithfulSMul.algebraMap_injective K L ?_⟩
    rw [← IsScalarTower.algebraMap_apply T K L, ht, restrictScalars_pairing]

/-- Restriction of scalars preserves `T`-valued root-coroot pairings. -/
@[simp]
theorem restrictScalars'_pairingIn [P.IsValuedIn T] (i j : ι) :
    (P.restrictScalars' K).pairingIn T i j = P.pairingIn T i j := by
  simp only [pairingIn]
  congr! 1
  ext t
  rw [← (FaithfulSMul.algebraMap_injective K L).eq_iff, ← IsScalarTower.algebraMap_apply T K L,
    restrictScalars_pairing]

end IsValuedIn

/-- Restriction of scalars preserves reducedness of a balanced root pairing. -/
instance isReduced_restrictScalars' [P.IsReduced] : (P.restrictScalars' K).IsReduced where
  eq_or_eq_neg i j hij := by
    have hL : ¬ LinearIndependent L ![P.root i, P.root j] := fun h ↦ hij <| by
      refine LinearIndependent.of_comp (span K (range P.root)).subtype ?_
      convert h.restrict_scalars' K using 1
      ext k
      fin_cases k <;> simp [restrictScalars_coe_root]
    exact (IsReduced.eq_or_eq_neg (P := P) i j hL).imp Subtype.ext Subtype.ext

end Basic

section Self

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} [P.IsBalanced]

/-- On the span of the roots, the coroot functionals of `P.restrictScalars' L` are those of `P`. -/
theorem coroot'_restrictScalars'_self (i : ι) (x : span L (range P.root)) :
    (P.restrictScalars' L).coroot' i x = P.coroot' i x := by
  simpa using P.algebraMap_coroot'_restrictScalars' L i x

end Self

end RootPairing
