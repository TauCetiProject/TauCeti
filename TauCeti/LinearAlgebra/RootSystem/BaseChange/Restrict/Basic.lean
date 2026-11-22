/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Restriction of scalars for root pairings and morphisms

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
`IsValuedIn`, and `IsReduced`—together with functorial restriction of morphisms, equivalences, and
automorphisms of balanced root pairings to `P.restrictScalars' K`.

## Main definitions

* `RootPairing.Hom.restrictScalars'` and `RootPairing.Equiv.restrictScalars'`: functorial
  restriction of morphisms and equivalences of balanced root pairings to `restrictScalars' K`.
* `RootPairing.Equiv.restrictScalars'Hom` (and `RootPairing.Equiv.restrictScalarsHom`): the group
  homomorphism `P.Aut →* (P.restrictScalars' K).Aut` restricting automorphisms to the `K`-spans.

## Main results

* `RootPairing.isValuedIn_restrictScalars'` and `RootPairing.isReduced_restrictScalars'`:
  `P.restrictScalars' K` inherits `IsValuedIn T` (in particular `IsCrystallographic`) and
  `IsReduced` from `P`.
* `RootPairing.coe_restrictScalars'_reflection_apply` and
  `RootPairing.Equiv.reflection_restrictScalars'`: reflections of `P` restrict to those of
  `P.restrictScalars' K`.

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

-- Not `@[simp]`: `coroot'` is an `abbrev` for `toLinearMap.flip ∘ coroot`, which `simp` unfolds to
-- `restrictScalars_toLinearMap_apply_apply` (`simpNF`).
/-- Under `algebraMap K L`, each coroot functional of `P.restrictScalars' K` agrees with that of
`P`. -/
theorem algebraMap_restrictScalars'_coroot'_apply (i : ι) (x : span K (range P.root)) :
    algebraMap K L ((P.restrictScalars' K).coroot' i x) = P.coroot' i x := by
  simp

/-- Under `algebraMap K L`, each root functional of `P.restrictScalars' K` agrees with that of
`P`. -/
theorem algebraMap_restrictScalars'_root'_apply (i : ι) (y : span K (range P.coroot)) :
    algebraMap K L ((P.restrictScalars' K).root' i y) = P.root' i y := by
  simp [root']

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
    algebra_compatible_smul L, algebraMap_restrictScalars'_coroot'_apply, reflection_apply]

/-- Each coreflection of `P.restrictScalars' K` is the restriction of the corresponding
coreflection of `P`. -/
@[simp]
theorem coe_restrictScalars'_coreflection_apply (i : ι) (y : span K (range P.coroot)) :
    ((P.restrictScalars' K).coreflection i y : N) = P.coreflection i y := by
  rw [coreflection_apply, Submodule.coe_sub, SetLike.val_smul, restrictScalars_coe_coroot,
    algebra_compatible_smul L, algebraMap_restrictScalars'_root'_apply, coreflection_apply]

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
      fin_cases k <;> rfl
    exact (IsReduced.eq_or_eq_neg (P := P) i j hL).imp Subtype.ext Subtype.ext

end Basic

section HomEquiv

variable {ι ι₂ L M N M₂ N₂ : Type*} [Field L]
  [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  [AddCommGroup M₂] [AddCommGroup N₂] [Module L M₂] [Module L N₂]
  {P : RootPairing ι L M N} {Q : RootPairing ι₂ L M₂ N₂}
  (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [Module K M₂] [Module K N₂] [IsScalarTower K L M₂] [IsScalarTower K L N₂]
  [P.IsBalanced] [Q.IsBalanced] [P.IsValuedIn K] [Q.IsValuedIn K]

/-- Restriction of a morphism of balanced root pairings to `restrictScalars' K`. -/
noncomputable def Hom.restrictScalars' (f : P.Hom Q) :
    (P.restrictScalars' K).Hom (Q.restrictScalars' K) where
  weightMap := (f.weightMap.restrictScalars K).restrict fun _ hx ↦ by
    simpa only [LinearMap.restrictScalars_apply, rootSpan] using f.weightMap_mem_rootSpan hx
  coweightMap := (f.coweightMap.restrictScalars K).restrict fun _ hy ↦ by
    simpa only [LinearMap.restrictScalars_apply, corootSpan] using f.coweightMap_mem_corootSpan hy
  indexEquiv := f.indexEquiv
  weight_coweight_transpose := by
    ext y x
    apply FaithfulSMul.algebraMap_injective K L
    simp only [flip_toLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      LinearMap.toLinearMap_toPerfPair, LinearMap.dualMap_apply, LinearMap.flip_apply,
      restrictScalars_toLinearMap_apply_apply, LinearMap.coe_restrict_apply,
      LinearMap.restrictScalars_apply]
    simpa only [flip_toLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      LinearMap.toLinearMap_toPerfPair, LinearMap.dualMap_apply, LinearMap.flip_apply] using
      congr($f.weight_coweight_transpose (y : N₂) (x : M))
  root_weightMap := by
    ext i
    exact f.root_weightMap_apply P Q i
  coroot_coweightMap := by
    ext j
    exact f.coroot_coweightMap_apply P Q j

/-- The weight map of `f.restrictScalars' K` is the restriction of `f.weightMap`. -/
@[simp]
theorem Hom.coe_weightMap_restrictScalars' (f : P.Hom Q) (x : span K (range P.root)) :
    ((f.restrictScalars' K).weightMap x : M₂) = f.weightMap x :=
  (rfl)

/-- The coweight map of `f.restrictScalars' K` is the restriction of `f.coweightMap`. -/
@[simp]
theorem Hom.coe_coweightMap_restrictScalars' (f : P.Hom Q) (y : span K (range Q.coroot)) :
    ((f.restrictScalars' K).coweightMap y : N) = f.coweightMap y :=
  (rfl)

/-- `Hom.restrictScalars'` preserves the root-index equivalence. -/
@[simp]
theorem Hom.indexEquiv_restrictScalars' (f : P.Hom Q) :
    (f.restrictScalars' K).indexEquiv = f.indexEquiv :=
  (rfl)

/-- `Hom.restrictScalars'` sends the identity morphism to the identity morphism. -/
@[simp]
theorem Hom.id_restrictScalars' :
    (Hom.id P).restrictScalars' K = Hom.id (P.restrictScalars' K) := by
  ext <;> rfl

/-- `Hom.restrictScalars'` commutes with composition of morphisms. -/
@[simp]
theorem Hom.comp_restrictScalars' {ι₃ M₃ N₃ : Type*} [AddCommGroup M₃] [AddCommGroup N₃]
    [Module L M₃] [Module L N₃] {S : RootPairing ι₃ L M₃ N₃} [Module K M₃] [Module K N₃]
    [IsScalarTower K L M₃] [IsScalarTower K L N₃] [S.IsBalanced] [S.IsValuedIn K]
    (g : Q.Hom S) (f : P.Hom Q) :
    (Hom.comp g f).restrictScalars' K =
      Hom.comp (g.restrictScalars' K) (f.restrictScalars' K) := by
  ext <;> rfl

/-- Restriction of an equivalence of balanced root pairings to `restrictScalars' K`. -/
noncomputable def Equiv.restrictScalars' (e : P.Equiv Q) :
    (P.restrictScalars' K).Equiv (Q.restrictScalars' K) :=
  { e.toHom.restrictScalars' K with
    bijective_weightMap :=
      ⟨fun x y h ↦ Subtype.ext (e.bijective_weightMap.1 (by
        simpa only [Hom.coe_weightMap_restrictScalars'] using congrArg Subtype.val h)),
       fun y ↦ ⟨((Equiv.symm P Q e).toHom.restrictScalars' K).weightMap y, Subtype.ext (by
        rw [Hom.coe_weightMap_restrictScalars', Hom.coe_weightMap_restrictScalars',
          Equiv.inv_weightMap]
        exact e.weightMap_weightEquiv_symm y)⟩⟩
    bijective_coweightMap :=
      ⟨fun x y h ↦ Subtype.ext (e.bijective_coweightMap.1 (by
        simpa only [Hom.coe_coweightMap_restrictScalars'] using congrArg Subtype.val h)),
       fun y ↦ ⟨((Equiv.symm P Q e).toHom.restrictScalars' K).coweightMap y, Subtype.ext (by
        rw [Hom.coe_coweightMap_restrictScalars', Hom.coe_coweightMap_restrictScalars',
          Equiv.inv_coweightMap]
        exact e.coweightMap_coweightEquiv_symm y)⟩⟩ }

/-- The underlying morphism of `e.restrictScalars' K` is `e.toHom.restrictScalars' K`. -/
@[simp]
theorem Equiv.toHom_restrictScalars' (e : P.Equiv Q) :
    (e.restrictScalars' K).toHom = e.toHom.restrictScalars' K :=
  (rfl)

/-- The weight equivalence of `e.restrictScalars' K` is the restriction of `e.weightEquiv`. -/
theorem Equiv.coe_weightEquiv_restrictScalars' (e : P.Equiv Q) (x : span K (range P.root)) :
    ((e.restrictScalars' K).weightEquiv x : M₂) = e.weightEquiv x :=
  (rfl)

/-- The coweight equivalence of `e.restrictScalars' K` is the restriction of `e.coweightEquiv`. -/
theorem Equiv.coe_coweightEquiv_restrictScalars' (e : P.Equiv Q) (y : span K (range Q.coroot)) :
    ((e.restrictScalars' K).coweightEquiv y : N) = e.coweightEquiv y :=
  (rfl)

/-- `Equiv.restrictScalars'` preserves the root-index equivalence. -/
theorem Equiv.indexEquiv_restrictScalars' (e : P.Equiv Q) :
    (e.restrictScalars' K).indexEquiv = e.indexEquiv :=
  (rfl)

/-- `Equiv.restrictScalars'` sends the identity equivalence to the identity equivalence. -/
@[simp]
theorem Equiv.id_restrictScalars' :
    (Equiv.id P).restrictScalars' K = Equiv.id (P.restrictScalars' K) := by
  ext <;> rfl

/-- `Equiv.restrictScalars'` commutes with composition of equivalences. -/
@[simp]
theorem Equiv.comp_restrictScalars' {ι₃ M₃ N₃ : Type*} [AddCommGroup M₃] [AddCommGroup N₃]
    [Module L M₃] [Module L N₃] {S : RootPairing ι₃ L M₃ N₃} [Module K M₃] [Module K N₃]
    [IsScalarTower K L M₃] [IsScalarTower K L N₃] [S.IsBalanced] [S.IsValuedIn K]
    (g : Q.Equiv S) (f : P.Equiv Q) :
    (Equiv.comp g f).restrictScalars' K =
      Equiv.comp (g.restrictScalars' K) (f.restrictScalars' K) := by
  ext <;> rfl

/-- `Equiv.restrictScalars'` commutes with inversion of equivalences. -/
@[simp]
theorem Equiv.symm_restrictScalars' (e : P.Equiv Q) :
    (Equiv.symm P Q e).restrictScalars' K =
      Equiv.symm (P.restrictScalars' K) (Q.restrictScalars' K) (e.restrictScalars' K) := by
  refine Equiv.ext (LinearMap.ext fun x ↦ ?_) (LinearMap.ext fun x ↦ ?_) rfl
  · refine Subtype.ext (e.bijective_weightMap.1 ?_)
    rw [Equiv.toHom_restrictScalars', Hom.coe_weightMap_restrictScalars', Equiv.inv_weightMap,
      LinearEquiv.coe_coe, e.weightMap_weightEquiv_symm, ← Hom.coe_weightMap_restrictScalars',
      ← Equiv.toHom_restrictScalars', Equiv.inv_weightMap, LinearEquiv.coe_coe,
      (e.restrictScalars' K).weightMap_weightEquiv_symm]
  · refine Subtype.ext (e.bijective_coweightMap.1 ?_)
    rw [Equiv.toHom_restrictScalars', Hom.coe_coweightMap_restrictScalars', Equiv.inv_coweightMap,
      LinearEquiv.coe_coe, e.coweightMap_coweightEquiv_symm, ← Hom.coe_coweightMap_restrictScalars',
      ← Equiv.toHom_restrictScalars', Equiv.inv_coweightMap, LinearEquiv.coe_coe,
      (e.restrictScalars' K).coweightMap_coweightEquiv_symm]

end HomEquiv

section Aut

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section Valued

variable [P.IsValuedIn K]

/-- The group homomorphism restricting automorphisms of `P` to automorphisms of
`P.restrictScalars' K`. -/
noncomputable def Equiv.restrictScalars'Hom : P.Aut →* (P.restrictScalars' K).Aut where
  toFun g := g.restrictScalars' K
  map_one' := Equiv.id_restrictScalars' K
  map_mul' g h := Equiv.comp_restrictScalars' K g h

/-- `Equiv.restrictScalars'Hom` evaluates to `Equiv.restrictScalars'`. -/
@[simp]
theorem Equiv.restrictScalars'Hom_apply (g : P.Aut) :
    Equiv.restrictScalars'Hom P K g = g.restrictScalars' K :=
  (rfl)

/-- The action of `g.restrictScalars' K` on `span K (range P.root)` is the restriction of the
action of `g` on `M`. -/
@[simp]
theorem coe_restrictScalars'_smul (g : P.Aut) (x : span K (range P.root)) :
    ((g.restrictScalars' K • x : span K (range P.root)) : M) = g • (x : M) :=
  (rfl)

/-- `Equiv.restrictScalars'` sends each reflection automorphism of `P` to the corresponding
reflection automorphism of `P.restrictScalars' K`. -/
@[simp]
theorem Equiv.reflection_restrictScalars' (i : ι) :
    (Equiv.reflection P i).restrictScalars' K =
      Equiv.reflection (P.restrictScalars' K) i := by
  refine Equiv.ext (LinearMap.ext fun x ↦ Subtype.ext ?_) (LinearMap.ext fun y ↦ Subtype.ext ?_) rfl
  · simp [← Equiv.weightEquiv_apply]
  · simp [← Equiv.coweightEquiv_apply]

end Valued

/-- Restriction of automorphisms for a crystallographic balanced root pairing. -/
noncomputable abbrev Equiv.restrictScalarsHom [P.IsCrystallographic] :
    P.Aut →* (P.restrictScalars K).Aut :=
  have := IsValuedIn.trans P K ℤ
  Equiv.restrictScalars'Hom P K

end Aut

end RootPairing
