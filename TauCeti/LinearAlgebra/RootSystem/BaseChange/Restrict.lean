/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm

/-!
# Restriction of scalars and the root-span root system

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

This file transports the structural, combinatorial, and geometric invariants of `P` to
`P.restrictScalars' K`, and connects `P.restrictScalars' L` back to the ambient weight space via the
root-span projection `P.rootSpanProj` from `TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced`.

## Main definitions

* `RootPairing.Hom.restrictScalars'` and `RootPairing.Equiv.restrictScalars'`: functorial
  restriction of morphisms and equivalences of balanced root pairings to `restrictScalars' K`.
* `RootPairing.Equiv.restrictScalars'Hom` (and `RootPairing.Equiv.restrictScalarsHom`): the group
  homomorphism `P.Aut →* (P.restrictScalars' K).Aut` restricting automorphisms to the `K`-spans.
* `RootPairing.weylGroupRestrictScalars'Equiv`: the canonical group isomorphism
  `P.weylGroup ≃* (P.restrictScalars' K).weylGroup`.
* `RootPairing.Base.restrictScalars'` (and `RootPairing.Base.restrictScalars`): a base `b` of `P`
  restricted to a base of `P.restrictScalars' K` with the same support, with support equivalence
  `RootPairing.Base.supportRestrictScalars'Equiv`.

## Main results

* `RootPairing.isValuedIn_restrictScalars'` and `RootPairing.isReduced_restrictScalars'`:
  `P.restrictScalars' K` inherits `IsValuedIn T` (in particular `IsCrystallographic`) and
  `IsReduced` from `P`.
* `RootPairing.Base.cartanMatrixIn_restrictScalars'_apply`,
  `RootPairing.Base.height_restrictScalars'`, `RootPairing.Base.isPos_restrictScalars'_iff`, and
  `RootPairing.posRoots_restrictScalars'`: the Cartan matrix, root heights, and positive roots of
  `b.restrictScalars' K` agree with those of `b`.
* `RootPairing.Base.mem_basedAut_restrictScalars'_iff`: an automorphism of `P` is based for `b` if
  and only if its restriction to `P.restrictScalars' K` is based for `b.restrictScalars' K`.
* `RootPairing.mem_posRootCone_restrictScalars'_iff` and `RootPairing.rootLE_restrictScalars'_iff`:
  the positive root cone and integral root dominance in `P.restrictScalars' K` are the restrictions
  of those of `P`.
* `RootPairing.isRegularWeight_restrictScalars'_iff`,
  `RootPairing.mem_dominantChamber_restrictScalars'_iff_of_nonneg_iff`, and
  `RootPairing.mem_openDominantChamber_restrictScalars'_iff_of_pos_iff`: regularity and chamber
  membership on `span K (range P.root)` agree with those in `P`.
* `RootPairing.orbitIndices_restrictScalars'` and `RootPairing.coe_orbitSum_restrictScalars'`:
  root orbits and root-orbit sums under a restricted automorphism agree with those in `P`.
* `RootPairing.restrictScalars'_self_smul_rootSpanProj`,
  `RootPairing.rootLE_restrictScalars'_self_rootSpanProj_of_rootLE`, and
  `RootPairing.rootLE_restrictScalars'_self_rootSpanProj_iff_of_sub_mem`: compatibility of
  `P.restrictScalars' L` with the ambient projection `P.rootSpanProj`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

open Function Set Submodule TauCeti

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

section Self

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [P.IsBalanced]

/-- The bilinear pairing of `P.restrictScalars' L` is the restriction of `P.toLinearMap`. -/
@[simp]
theorem restrictScalars'_self_toLinearMap_apply_apply
    (x : span L (range P.root)) (y : span L (range P.coroot)) :
    (P.restrictScalars' L).toLinearMap x y = P.toLinearMap x y :=
  P.restrictScalars_toLinearMap_apply_apply L x y

/-- `P.restrictScalars' L` has the same root-coroot pairings as `P`. -/
@[simp]
theorem restrictScalars'_self_pairing (i j : ι) :
    (P.restrictScalars' L).pairing i j = P.pairing i j :=
  P.restrictScalars_pairing L i j

-- Not `@[simp]`: `coroot'` unfolds to `toLinearMap.flip ∘ coroot` (`simpNF`).
/-- Each coroot functional of `P.restrictScalars' L` is the restriction of `P.coroot' i`. -/
theorem restrictScalars'_self_coroot'_apply (i : ι) (x : span L (range P.root)) :
    (P.restrictScalars' L).coroot' i x = P.coroot' i x :=
  P.algebraMap_restrictScalars'_coroot'_apply L i x

/-- Each root functional of `P.restrictScalars' L` is the restriction of `P.root' i`. -/
theorem restrictScalars'_self_root'_apply (i : ι) (y : span L (range P.coroot)) :
    (P.restrictScalars' L).root' i y = P.root' i y :=
  P.algebraMap_restrictScalars'_root'_apply L i y

/-- `P.restrictScalars' L` has the same Coxeter weights as `P`. -/
@[simp]
theorem restrictScalars'_self_coxeterWeight (i j : ι) :
    (P.restrictScalars' L).coxeterWeight i j = P.coxeterWeight i j :=
  P.algebraMap_restrictScalars'_coxeterWeight L i j

/-- Projecting onto the root span intertwines each ambient reflection with the corresponding
reflection of `P.restrictScalars' L`. -/
@[simp]
theorem rootSpanProj_reflection (i : ι) (x : M) :
    P.rootSpanProj (P.reflection i x) = (P.restrictScalars' L).reflection i (P.rootSpanProj x) := by
  ext
  rw [coe_rootSpanProj_reflection, coe_restrictScalars'_reflection_apply]

end Self

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

/-- Restriction of automorphisms maps `P.weylGroup` onto `(P.restrictScalars' K).weylGroup`. -/
@[simp]
theorem map_weylGroup_restrictScalars'Hom :
    P.weylGroup.map (Equiv.restrictScalars'Hom P K) = (P.restrictScalars' K).weylGroup := by
  have h : (Equiv.restrictScalars'Hom P K ∘ Equiv.reflection P) =
      Equiv.reflection (P.restrictScalars' K) :=
    funext fun i ↦ Equiv.reflection_restrictScalars' P K i
  rw [weylGroup, MonoidHom.map_closure, ← range_comp, h, weylGroup]

/-- **The Weyl group of `P` is canonically isomorphic to that of `P.restrictScalars' K`.** -/
noncomputable def weylGroupRestrictScalars'Equiv :
    P.weylGroup ≃* (P.restrictScalars' K).weylGroup :=
  P.weylGroupEquivOfReflectionPermEq (P.restrictScalars' K) rfl
    P.weylGroupToPerm_injective_of_isBalanced (weylGroupToPerm_injective (P.restrictScalars' K))

/-- `RootPairing.weylGroupRestrictScalars'Equiv` commutes with the root-index permutation
representations. -/
theorem weylGroupToPerm_weylGroupRestrictScalars'Equiv (w : P.weylGroup) :
    (P.restrictScalars' K).weylGroupToPerm (P.weylGroupRestrictScalars'Equiv K w) =
      P.weylGroupToPerm w :=
  weylGroupToPerm_weylGroupEquivOfReflectionPermEq _ _ _ _ _ w

/-- `RootPairing.weylGroupRestrictScalars'Equiv` sends each indexed reflection to the reflection
with the same root index. -/
@[simp]
theorem weylGroupRestrictScalars'Equiv_ofIdx (i : ι) :
    P.weylGroupRestrictScalars'Equiv K (weylGroup.ofIdx P i) =
      weylGroup.ofIdx (P.restrictScalars' K) i :=
  weylGroupEquivOfReflectionPermEq_ofIdx _ _ _ _ _ i

/-- Coercing `RootPairing.weylGroupRestrictScalars'Equiv` to `(P.restrictScalars' K).Aut` agrees
with `RootPairing.Equiv.restrictScalars'Hom`. -/
@[simp]
theorem coe_weylGroupRestrictScalars'Equiv (w : P.weylGroup) :
    (P.weylGroupRestrictScalars'Equiv K w : (P.restrictScalars' K).Aut) =
      Equiv.restrictScalars'Hom P K w := by
  apply Equiv.indexHom_injective (P.restrictScalars' K)
  rw [← MonoidHom.domRestrict_apply (Equiv.indexHom (P.restrictScalars' K)),
    weylGroupToPerm_weylGroupRestrictScalars'Equiv, MonoidHom.domRestrict_apply,
    Equiv.indexHom_apply, Equiv.indexHom_apply, Equiv.restrictScalars'Hom_apply,
    Equiv.indexEquiv_restrictScalars']

end Valued

/-- Restriction of automorphisms for a crystallographic balanced root pairing. -/
noncomputable abbrev Equiv.restrictScalarsHom [P.IsCrystallographic] :
    P.Aut →* (P.restrictScalars K).Aut :=
  have := IsValuedIn.trans P K ℤ
  Equiv.restrictScalars'Hom P K

/-- Projecting onto the `L`-span of the roots intertwines the action of `P.Aut` on `M` with the
action of `(P.restrictScalars' L).Aut` on `P.rootSpan L`. -/
@[simp]
theorem restrictScalars'_self_smul_rootSpanProj (g : P.Aut) (x : M) :
    g.restrictScalars' L • P.rootSpanProj x = P.rootSpanProj (g • x) := by
  ext
  rw [coe_restrictScalars'_smul, coe_rootSpanProj_smul]

end Aut

section Base

private lemma Base.restrictScalars'_root_mem_or_neg_mem {ι L M N : Type*} [Field L]
    (K : Type*) [Field K] [Algebra K L] [AddCommGroup M] [AddCommGroup N]
    [Module L M] [Module L N] {Q : RootPairing ι L M N} [Module K M] [Module K N]
    [IsScalarTower K L M] [IsScalarTower K L N] [Q.IsBalanced] [Q.IsValuedIn K]
    (b' : Q.Base) (i : ι) :
    (Q.restrictScalars' K).root i ∈
        AddSubmonoid.closure ((Q.restrictScalars' K).root '' b'.support) ∨
      -(Q.restrictScalars' K).root i ∈
        AddSubmonoid.closure ((Q.restrictScalars' K).root '' b'.support) := by
  obtain ⟨f, -, h | h⟩ := b'.exists_root_eq_sum_nat_or_neg i
  · refine Or.inl ?_
    have hi : (Q.restrictScalars' K).root i =
        ∑ j ∈ b'.support, f j • (Q.restrictScalars' K).root j := by
      ext; simpa using h
    rw [hi]
    exact sum_mem fun j hj ↦
      nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ hj)) (f j)
  · refine Or.inr ?_
    have hi : -(Q.restrictScalars' K).root i =
        ∑ j ∈ b'.support, f j • (Q.restrictScalars' K).root j := by
      ext; simpa [neg_eq_iff_eq_neg] using h
    rw [hi]
    exact sum_mem fun j hj ↦
      nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ hj)) (f j)

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section Valued

variable [P.IsValuedIn K] (b : P.Base)

/-- A base `b` of `P` restricts to a base of `P.restrictScalars' K` with the same support. -/
noncomputable def Base.restrictScalars' : (P.restrictScalars' K).Base where
  support := b.support
  linearIndepOn_root :=
    LinearIndependent.of_comp (span K (range P.root)).subtype
      (b.linearIndepOn_root.restrict_scalars' K)
  linearIndepOn_coroot :=
    LinearIndependent.of_comp (span K (range P.coroot)).subtype
      (b.linearIndepOn_coroot.restrict_scalars' K)
  root_mem_or_neg_mem := Base.restrictScalars'_root_mem_or_neg_mem K b
  coroot_mem_or_neg_mem := Base.restrictScalars'_root_mem_or_neg_mem K b.flip

/-- `Base.restrictScalars'` preserves the simple-root support. -/
@[simp]
theorem Base.support_restrictScalars' : (b.restrictScalars' K).support = b.support :=
  (rfl)

/-- `Base.restrictScalars'` commutes with `Base.flip`. -/
@[simp]
theorem Base.flip_restrictScalars' :
    (b.restrictScalars' K).flip = b.flip.restrictScalars' K :=
  Base.ext rfl

/-- `Base.restrictScalars'` commutes with transporting a base along an equivalence. -/
@[simp]
theorem Base.map_restrictScalars' {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [AddCommGroup N₂]
    [Module L M₂] [Module L N₂] {Q : RootPairing ι₂ L M₂ N₂} [Module K M₂] [Module K N₂]
    [IsScalarTower K L M₂] [IsScalarTower K L N₂] [Q.IsBalanced] [Q.IsValuedIn K]
    (e : P.Equiv Q) :
    (b.map e).restrictScalars' K = (b.restrictScalars' K).map (e.restrictScalars' K) := by
  classical
  apply Base.ext
  rw [support_restrictScalars', support_map_eq, support_map_eq, support_restrictScalars',
    Equiv.indexEquiv_restrictScalars']

/-- The canonical identification between the support subtype of `b.restrictScalars' K` and that of
`b` (`Base.support_restrictScalars'`). -/
def Base.supportRestrictScalars'Equiv :
    (b.restrictScalars' K).support ≃ b.support :=
  _root_.Equiv.subtypeEquivRight fun _ ↦ by rw [Base.support_restrictScalars']

/-- `Base.supportRestrictScalars'Equiv` preserves the underlying root index. -/
@[simp]
theorem Base.coe_supportRestrictScalars'Equiv (i : (b.restrictScalars' K).support) :
    (b.supportRestrictScalars'Equiv K i : ι) = i :=
  (rfl)

/-- `(Base.supportRestrictScalars'Equiv).symm` preserves the underlying root index. -/
@[simp]
theorem Base.coe_supportRestrictScalars'Equiv_symm (i : b.support) :
    ((b.supportRestrictScalars'Equiv K).symm i : ι) = i :=
  (rfl)

/-- The `T`-valued Cartan matrix of `b.restrictScalars' K` agrees with that of `b` along
`Base.supportRestrictScalars'Equiv`. -/
@[simp]
theorem Base.cartanMatrixIn_restrictScalars'_apply (T : Type*) [CommRing T] [Algebra T K]
    [Algebra T L] [IsScalarTower T K L] [P.IsValuedIn T]
    (i j : (b.restrictScalars' K).support) :
    (b.restrictScalars' K).cartanMatrixIn T i j =
      b.cartanMatrixIn T (b.supportRestrictScalars'Equiv K i)
        (b.supportRestrictScalars'Equiv K j) :=
  P.restrictScalars'_pairingIn K T i j

-- Not `@[simp]`: `cartanMatrix` is an `abbrev` for `cartanMatrixIn ℤ`, which
-- `Base.cartanMatrixIn_restrictScalars'_apply` already simplifies (`simpNF`).
/-- The Cartan matrix of `b.restrictScalars' K` agrees with that of `b` along
`Base.supportRestrictScalars'Equiv`. -/
theorem Base.cartanMatrix_restrictScalars'_apply [P.IsCrystallographic]
    (i j : (b.restrictScalars' K).support) :
    (b.restrictScalars' K).cartanMatrix i j =
      b.cartanMatrix (b.supportRestrictScalars'Equiv K i)
        (b.supportRestrictScalars'Equiv K j) :=
  b.cartanMatrixIn_restrictScalars'_apply K ℤ i j

/-- Root heights with respect to `b.restrictScalars' K` agree with those with respect to `b`. -/
@[simp]
theorem Base.height_restrictScalars' [CharZero K] [CharZero L] (i : ι) :
    (b.restrictScalars' K).height i = b.height i := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  have hfK : (P.restrictScalars' K).root i =
      ∑ j ∈ (b.restrictScalars' K).support, f j • (P.restrictScalars' K).root j := by
    ext; simpa using hf
  rw [(b.restrictScalars' K).height_eq_sum hfK, b.height_eq_sum hf, support_restrictScalars']

/-- Positivity of a root index with respect to `b.restrictScalars' K` agrees with positivity with
respect to `b`. -/
@[simp]
theorem Base.isPos_restrictScalars'_iff [CharZero K] [CharZero L] (i : ι) :
    (b.restrictScalars' K).IsPos i ↔ b.IsPos i := by
  simp only [Base.isPos_iff, Base.height_restrictScalars']

/-- The set of positive roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem posRoots_restrictScalars' [CharZero K] [CharZero L] :
    posRoots (P.restrictScalars' K) (b.restrictScalars' K) = posRoots P b := by
  ext i
  simp only [mem_posRoots, Base.isPos_restrictScalars'_iff]

/-- The set of negative roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem negRoots_restrictScalars' [CharZero K] [CharZero L] :
    negRoots (P.restrictScalars' K) (b.restrictScalars' K) = negRoots P b := by
  ext i
  simp only [mem_negRoots, Base.isPos_restrictScalars'_iff]

/-- The finset of positive roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem posRootsFinset_restrictScalars' [Finite ι] [CharZero K] [CharZero L] :
    posRootsFinset (P.restrictScalars' K) (b.restrictScalars' K) = posRootsFinset P b := by
  ext i
  simp only [mem_posRootsFinset, posRoots_restrictScalars']

/-- The finset of negative roots of `b.restrictScalars' K` equals that of `b`. -/
@[simp]
theorem negRootsFinset_restrictScalars' [Finite ι] [CharZero K] [CharZero L] :
    negRootsFinset (P.restrictScalars' K) (b.restrictScalars' K) = negRootsFinset P b := by
  ext i
  simp only [mem_negRootsFinset, negRoots_restrictScalars']

/-- An automorphism of `P` is based for `b` if and only if its restriction to
`P.restrictScalars' K` is based for `b.restrictScalars' K`. -/
theorem Base.mem_basedAut_restrictScalars'_iff {g : P.Aut} :
    Equiv.restrictScalars'Hom P K g ∈ (b.restrictScalars' K).basedAut ↔ g ∈ b.basedAut := by
  simp only [Base.mem_basedAut_iff, Base.support_restrictScalars',
    Equiv.restrictScalars'Hom_apply, Equiv.indexEquiv_restrictScalars']

end Valued

/-- Restriction of a base for a crystallographic balanced root pairing. -/
noncomputable abbrev Base.restrictScalars [P.IsCrystallographic] (b : P.Base) :
    (P.restrictScalars K).Base :=
  have := IsValuedIn.trans P K ℤ
  b.restrictScalars' K

end Base

section ConeAndChamber

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- Membership in the positive root cone of `P.restrictScalars' K` agrees with membership in that
of `P`. -/
@[simp]
theorem mem_posRootCone_restrictScalars'_iff (b : P.Base) (x : span K (range P.root)) :
    x ∈ posRootCone (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ posRootCone P b := by
  simp only [mem_posRootCone, Base.support_restrictScalars', Subtype.ext_iff,
    Submodule.coe_sum, AddSubmonoidClass.coe_nsmul, restrictScalars_coe_root]

/-- Integral root dominance in `P.restrictScalars' K` agrees with integral root dominance in `P`. -/
@[simp]
theorem rootLE_restrictScalars'_iff (b : P.Base) (x y : span K (range P.root)) :
    (P.restrictScalars' K).rootLE (b.restrictScalars' K) x y ↔
      P.rootLE b (x : M) (y : M) := by
  rw [rootLE_iff_sub_mem_posRootCone, rootLE_iff_sub_mem_posRootCone,
    mem_posRootCone_restrictScalars'_iff, Submodule.coe_sub]

/-- Weight regularity in `P.restrictScalars' K` agrees with weight regularity in `P`. -/
@[simp]
theorem isRegularWeight_restrictScalars'_iff (x : span K (range P.root)) :
    (P.restrictScalars' K).IsRegularWeight x ↔ P.IsRegularWeight (x : M) := by
  simp only [isRegularWeight_iff, ← P.algebraMap_restrictScalars'_coroot'_apply K, ne_eq,
    FaithfulSMul.algebraMap_eq_zero_iff]

/-- When `algebraMap K L` preserves and reflects nonnegativity (for example when `K` and `L` are
linearly ordered fields and `algebraMap K L` is order-preserving, or when `K = L`), membership in
the closed dominant chamber of `P.restrictScalars' K` agrees with that in `P`. -/
theorem mem_dominantChamber_restrictScalars'_iff_of_nonneg_iff [Preorder K] [Preorder L]
    (h : ∀ a : K, 0 ≤ algebraMap K L a ↔ 0 ≤ a) (b : P.Base) (x : span K (range P.root)) :
    x ∈ dominantChamber (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ dominantChamber P b := by
  simp only [mem_dominantChamber, Base.support_restrictScalars',
    ← P.algebraMap_restrictScalars'_coroot'_apply K, h]

/-- When `algebraMap K L` preserves and reflects strict positivity, membership in the open dominant
chamber of `P.restrictScalars' K` agrees with that in `P`. -/
theorem mem_openDominantChamber_restrictScalars'_iff_of_pos_iff [Preorder K] [Preorder L]
    (h : ∀ a : K, 0 < algebraMap K L a ↔ 0 < a) (b : P.Base) (x : span K (range P.root)) :
    x ∈ openDominantChamber (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ openDominantChamber P b := by
  simp only [mem_openDominantChamber, Base.support_restrictScalars',
    ← P.algebraMap_restrictScalars'_coroot'_apply K, h]

end ConeAndChamber

section SelfChamber

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [P.IsBalanced] (b : P.Base)

/-- Membership in the closed dominant chamber of `P.restrictScalars' L` agrees with that in `P`. -/
theorem mem_dominantChamber_restrictScalars'_self_iff [Preorder L] (x : span L (range P.root)) :
    x ∈ dominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      (x : M) ∈ dominantChamber P b :=
  P.mem_dominantChamber_restrictScalars'_iff_of_nonneg_iff L (fun _ ↦ Iff.rfl) b x

/-- Membership in the open dominant chamber of `P.restrictScalars' L` agrees with that in `P`. -/
theorem mem_openDominantChamber_restrictScalars'_self_iff [Preorder L]
    (x : span L (range P.root)) :
    x ∈ openDominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      (x : M) ∈ openDominantChamber P b :=
  P.mem_openDominantChamber_restrictScalars'_iff_of_pos_iff L (fun _ ↦ Iff.rfl) b x

/-- Integral root dominance in `P` implies integral root dominance of the root-span projections in
`P.restrictScalars' L`. -/
theorem rootLE_restrictScalars'_self_rootSpanProj_of_rootLE {x y : M} (h : P.rootLE b x y) :
    (P.restrictScalars' L).rootLE (b.restrictScalars' L) (P.rootSpanProj x) (P.rootSpanProj y) :=
  (P.rootLE_restrictScalars'_iff L b _ _).mpr (P.rootLE_coe_rootSpanProj_of_rootLE b h)

/-- For weights with the same central component (`y - x ∈ P.rootSpan L`), integral root dominance
of their projections in `P.restrictScalars' L` is equivalent to integral root dominance in `P`. -/
theorem rootLE_restrictScalars'_self_rootSpanProj_iff_of_sub_mem {x y : M}
    (h : y - x ∈ P.rootSpan L) :
    (P.restrictScalars' L).rootLE (b.restrictScalars' L) (P.rootSpanProj x) (P.rootSpanProj y) ↔
      P.rootLE b x y :=
  (P.rootLE_restrictScalars'_iff L b _ _).trans (P.rootLE_coe_rootSpanProj_iff_of_sub_mem b h)

end SelfChamber

section OrbitSum

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [Finite ι] (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K] (σ : P.Aut)

/-- Root orbits under a restricted automorphism in `P.restrictScalars' K` coincide with those in
`P`. -/
@[simp]
theorem orbitIndices_restrictScalars' (i : ι) :
    (P.restrictScalars' K).orbitIndices (σ.restrictScalars' K) i =
      P.orbitIndices σ i := by
  ext j
  rw [mem_orbitIndices, mem_orbitIndices]
  rfl

/-- Each root-orbit sum in `P.restrictScalars' K` coerces to the corresponding root-orbit sum in
`P`. -/
@[simp]
theorem coe_orbitSum_restrictScalars' (i : ι) :
    ((P.restrictScalars' K).orbitSum (σ.restrictScalars' K) i : M) =
      P.orbitSum σ i := by
  simp only [orbitSum_def, orbitIndices_restrictScalars', Submodule.coe_sum,
    restrictScalars_coe_root]

/-- The set of folded root-orbit sums in `P.restrictScalars' K` maps under coercion onto
`P.foldedIndices σ`. -/
@[simp]
theorem image_subtype_foldedIndices_restrictScalars' :
    Subtype.val '' (P.restrictScalars' K).foldedIndices (σ.restrictScalars' K) =
      P.foldedIndices σ := by
  ext x
  simp only [mem_image, mem_foldedIndices]
  refine ⟨?_, fun ⟨i, hi⟩ ↦ ⟨_, ⟨i, rfl⟩, (P.coe_orbitSum_restrictScalars' K σ i).trans hi⟩⟩
  rintro ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, (P.coe_orbitSum_restrictScalars' K σ i).symm⟩

end OrbitSum

end RootPairing
