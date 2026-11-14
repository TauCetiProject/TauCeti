/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Morita.Matrix
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ExtendScalars
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.RingEquiv
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Algebra.Ring.Opposite

import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.Algebra.Group.Prod
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RingTheory.LocalRing.Module

/-!
# Algebraic `K₀` of a ring, functoriality, Morita invariance, and basic computations

For a possibly noncommutative ring `R`, this file develops the categorical and group-level API of
projective `K₀`, both in the left-module convention
`SplitK0 (finiteProjectiveModules R).FullSubcategory` used by the Cartan-map development and in the
right-module convention

```text
AlgebraicK0 R := SplitK0 (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory
```

matching `TauCeti.AlgebraicK1` (where invertible matrices act on finite free right `R`-modules) and
Weibel, *The K-book*, Definition II.2.1.

## Main definitions

* `TauCeti.FiniteProjectiveModules.freeObj`, `TauCeti.FiniteProjectiveModules.finFreeObj`, and
  `TauCeti.FiniteProjectiveModules.selfObj`: the finite free `R`-modules `ι → R` and `Fin n → R`
  and the regular module `R` as objects of `(finiteProjectiveModules R).FullSubcategory`.
* `TauCeti.finiteProjectiveModulesSplitK0Equiv`: the canonical comparison isomorphism
  between `SplitK0 (finiteProjectiveModules R).FullSubcategory` and
  `ExactK0 (finiteProjectiveModulesExactStructure R)`.
* `CategoryTheory.Equivalence.finiteProjectiveModulesSplitK0Equiv` and
  `RingEquiv.finiteProjectiveModulesSplitK0Equiv`: invariance of `SplitK0` of finitely generated
  projective modules under equivalences of module categories and ring isomorphisms.
* `TauCeti.finiteProjectiveModulesProdSplitK0Equiv`: the product decomposition
  `K₀(proj (R × S)) ≃+ K₀(proj R) × K₀(proj S)`.
* `TauCeti.finiteProjectiveModulesToMatrixFunctor`,
  `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv`, and
  `TauCeti.finiteProjectiveModulesMatrixFinSplitK0Equiv`: the canonical matrix Morita isomorphisms
  `K₀(proj R) ≃+ K₀(proj M_ι(R))` and `K₀(proj R) ≃+ K₀(proj M_n(R))`, independent of any choice of
  index.
* `TauCeti.finiteProjectiveModulesFinrankSplitK0EquivOfFree` and its specializations to division
  rings, principal left-ideal domains, and local rings: the rank isomorphism `K₀(proj R) ≃+ ℤ`.
* `TauCeti.AlgebraicK0`, `TauCeti.AlgebraicK0.one`, `TauCeti.AlgebraicK0.map`,
  `RingEquiv.algebraicK0Equiv`, `TauCeti.AlgebraicK0.prodEquiv`,
  `TauCeti.AlgebraicK0.matrixEquiv`, `TauCeti.AlgebraicK0.matrixFinEquiv`,
  `TauCeti.AlgebraicK0.finrankEquivDivisionRing`, `TauCeti.AlgebraicK0.finrankEquivPID`,
  `TauCeti.AlgebraicK0.finrankEquivInt`, and `TauCeti.AlgebraicK0.finrankEquivLocalRing`: algebraic
  `K₀` of a ring in the right-module convention, its covariant functoriality, product and matrix
  decompositions, and rank computations normalized so that `[R] ↦ 1`.

## Main results

* `TauCeti.FiniteProjectiveModules.exists_biprod_iso_fin`: every object `P` of
  `(finiteProjectiveModules R).FullSubcategory` admits a complement `Q` and `n : ℕ` with
  `P ⊞ Q ≅ Rⁿ`.
* `TauCeti.SplitK0.exists_eq_of_sub_nsmul_selfObj`: every class in `K₀(proj R)` has the form
  `[P] - n • [R]`.
* `RingEquiv.map_finiteProjectiveModulesExtendScalars_eq`: along a ring isomorphism `e : R ≃+* S`,
  extension of scalars along `e` and restriction of scalars along `e.symm` induce the same
  isomorphism on `K₀`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Definition 2.1, Lemma 2.1, Examples 2.1.1–2.1.2, Proposition 2.4 (Morita invariance),
  and §2.8 (functoriality and products).
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

universe u u'

namespace TauCeti

/-! ### Free complements and standard generators in `(finiteProjectiveModules R).FullSubcategory` -/

namespace FiniteProjectiveModules

/-- The finite free module `ι → R` as an object of `(finiteProjectiveModules R).FullSubcategory`. -/
def freeObj (R : Type u) [Ring R] (ι : Type u) [_root_.Finite ι] :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (ι → R), finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp]
theorem freeObj_obj (R : Type u) [Ring R] (ι : Type u) [_root_.Finite ι] :
    (freeObj R ι).obj = ModuleCat.of R (ι → R) :=
  (rfl)

/-- The finite free module `Fin n → R` as an object of
`(finiteProjectiveModules R).FullSubcategory`. -/
def finFreeObj (R : Type u) [Ring R] (n : ℕ) : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp]
theorem finFreeObj_obj (R : Type u) [Ring R] (n : ℕ) :
    (finFreeObj R n).obj = ModuleCat.of R (Fin n → R) :=
  (rfl)

/-- The regular left `R`-module `R` as an object of
`(finiteProjectiveModules R).FullSubcategory`. -/
def selfObj (R : Type u) [Ring R] : (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R R, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp]
theorem selfObj_obj (R : Type u) [Ring R] : (selfObj R).obj = ModuleCat.of R R :=
  (rfl)

/-- **Categorical free-complement theorem.** Every object `P` of
`(finiteProjectiveModules R).FullSubcategory` admits a complement `Q` in the same subcategory and a
natural number `n` with `P ⊞ Q ≅ Rⁿ`. -/
theorem exists_biprod_iso_fin {R : Type u} [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ∃ (Q : (finiteProjectiveModules R).FullSubcategory) (n : ℕ),
      Nonempty (P ⊞ Q ≅ finFreeObj R n) := by
  obtain ⟨N, _, _, hfin, hproj, n, ⟨e⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin R P.obj
  let Q : (finiteProjectiveModules R).FullSubcategory :=
    ⟨ModuleCat.of R N, finiteProjectiveModules_iff.mpr ⟨hfin, hproj⟩⟩
  exact ⟨Q, n, ⟨(finiteProjectiveModules R).fullyFaithfulι.preimageIso
    ((biprodLinearEquiv P Q).trans e).toModuleIso⟩⟩

end FiniteProjectiveModules

namespace SplitK0

/-- The class of the finite free module `Fin n → R` in `SplitK0` is `n` times `[R]`. -/
@[simp]
theorem of_finFreeObj {R : Type u} [Ring R] (n : ℕ) :
    SplitK0.of.{u} (FiniteProjectiveModules.finFreeObj R n) =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  of_eq_nsmul_of_linearEquiv_fin (X := FiniteProjectiveModules.finFreeObj R n)
    (R' := FiniteProjectiveModules.selfObj R) (.refl R (Fin n → R)) (.refl R R)

/-- The class of the finite free module `ι → R` in `SplitK0` is `Fintype.card ι` times `[R]`. -/
@[simp]
theorem of_freeObj {R : Type u} [Ring R] (ι : Type u) [Fintype ι] :
    SplitK0.of.{u} (FiniteProjectiveModules.freeObj R ι) =
      Fintype.card ι • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  of_eq_nsmul_of_linearEquiv_fin (X := FiniteProjectiveModules.freeObj R ι)
    (R' := FiniteProjectiveModules.selfObj R)
    (LinearEquiv.funCongrLeft R R (Fintype.equivFin ι).symm) (.refl R R)

/-- Every element of `SplitK0 (finiteProjectiveModules R).FullSubcategory` has the form
`[P] - n • [R]` for some finitely generated projective `R`-module `P` and `n : ℕ`
(Weibel, *The K-book*, Lemma II.2.1). -/
theorem exists_eq_of_sub_nsmul_selfObj {R : Type u} [Ring R]
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    ∃ (P : (finiteProjectiveModules R).FullSubcategory) (n : ℕ),
      x = SplitK0.of.{u} P - n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := by
  obtain ⟨P₁, P₂, rfl⟩ := SplitK0.exists_eq_sub.{u} x
  obtain ⟨Q, n, ⟨e⟩⟩ := FiniteProjectiveModules.exists_biprod_iso_fin P₂
  refine ⟨P₁ ⊞ Q, n, ?_⟩
  have hQ : SplitK0.of.{u} P₂ + SplitK0.of.{u} Q =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := by
    rw [← SplitK0.of_biprod.{u}, SplitK0.of_congr.{u} e, of_finFreeObj]
  rw [SplitK0.of_biprod.{u}, ← hQ]
  abel

/-- Extension of scalars along `f : R →+* S` sends the class of the regular module `R` to the class
of the regular module `S`. -/
@[simp]
theorem of_finiteProjectiveModulesExtendScalars_selfObj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj
        (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj S) :=
  (SplitK0.map_of.{u, u} f.finiteProjectiveModulesExtendScalars
    (FiniteProjectiveModules.selfObj R)).symm.trans <|
    map_finiteProjectiveModulesExtendScalars_of_linearEquiv_pi (f := f)
      (FiniteProjectiveModules.selfObj R) (FiniteProjectiveModules.selfObj S)
      (LinearEquiv.funUnique Unit R R).symm (LinearEquiv.funUnique Unit S S).symm

/-- Extension of scalars along `f : R →+* S` sends `[R]` to `[S]`. -/
theorem map_finiteProjectiveModulesExtendScalars_selfObj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars
        (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj S) := by
  simp

end SplitK0

/-! ### Comparison between `SplitK0` and `ExactK0` of finitely generated projective modules -/

private theorem split_conflation_finiteProjectiveModules (R : Type u) [Ring R]
    {S : ShortComplex (finiteProjectiveModules R).FullSubcategory}
    (hS : (finiteProjectiveModulesExactStructure R).Conflation S) :
    Nonempty S.Splitting := by
  rw [finiteProjectiveModulesExactStructure_eq_split] at hS
  exact (ExactStructure.split_conflation S).mp hS

/-- **Comparison between split and exact `K₀` of finitely generated projective modules.** Every
short exact sequence of finitely generated projective `R`-modules splits
(`TauCeti.finiteProjectiveModulesExactStructure_eq_split`), so the canonical comparison
`TauCeti.ExactK0.fromSplit` is an isomorphism. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv (R : Type u) [Ring R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  ExactK0.fromSplitEquiv.{u} (split_conflation_finiteProjectiveModules R)

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_of (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesSplitK0Equiv R (SplitK0.of.{u} P) = ExactK0.of.{u} P :=
  (ExactK0.fromSplitEquiv_apply.{u} (split_conflation_finiteProjectiveModules R)
    (SplitK0.of.{u} P)).trans (ExactK0.fromSplit_of.{u} P)

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_symm_of (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModulesSplitK0Equiv R).symm (ExactK0.of.{u} P) = SplitK0.of.{u} P :=
  ExactK0.fromSplitEquiv_symm_of.{u} (split_conflation_finiteProjectiveModules R) P

/-- `TauCeti.finiteProjectiveModulesSplitK0Equiv` intertwines extension of scalars on `SplitK0` and
on `ExactK0`. -/
theorem finiteProjectiveModulesSplitK0Equiv_comp_map_extendScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    (finiteProjectiveModulesSplitK0Equiv S).toAddMonoidHom.comp
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars) =
      f.finiteProjectiveModulesK0Extend.comp
        (finiteProjectiveModulesSplitK0Equiv R).toAddMonoidHom :=
  SplitK0.hom_ext fun P ↦ by simp

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_map_extendScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesSplitK0Equiv S
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      f.finiteProjectiveModulesK0Extend (finiteProjectiveModulesSplitK0Equiv R x) :=
  DFunLike.congr_fun (finiteProjectiveModulesSplitK0Equiv_comp_map_extendScalars f) x

end TauCeti

/-! ### Morita invariance and ring-isomorphism invariance on `SplitK0` -/

namespace CategoryTheory.Equivalence

open TauCeti

/-- **Morita invariance of `SplitK0` of finitely generated projective modules.** An equivalence
`e : ModuleCat A ≌ ModuleCat B` induces an additive equivalence between the split Grothendieck
groups of finitely generated projective modules over `A` and `B`. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv {A : Type u} [Ring A] {B : Type u'} [Ring B]
    (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+
      SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory :=
  SplitK0.mapEquiv.{u, u'} e.finiteProjectiveModulesEquivalence

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_of {A : Type u} [Ring A] {B : Type u'} [Ring B]
    (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) (P : (finiteProjectiveModules A).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv (SplitK0.of.{u} P) =
      SplitK0.of.{u'} (e.finiteProjectiveModulesEquivalence.functor.obj P) :=
  SplitK0.mapEquiv_of.{u, u'} _ P

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_symm_of {A : Type u} [Ring A] {B : Type u'} [Ring B]
    (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) (Q : (finiteProjectiveModules B).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv.symm (SplitK0.of.{u'} Q) =
      SplitK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj Q) :=
  SplitK0.mapEquiv_symm_of.{u, u'} _ Q

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom {A : Type u} [Ring A] {B : Type u'}
    [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B) :
    (e.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules A).FullSubcategory →+
          SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory) =
      SplitK0.map.{u, u'} e.finiteProjectiveModulesEquivalence.functor :=
  SplitK0.mapEquiv_toAddMonoidHom.{u, u'} _

/-- `TauCeti.finiteProjectiveModulesSplitK0Equiv` intertwines Morita equivalences on `SplitK0` and
on `ExactK0`. -/
@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_apply_splitK0Equiv {A : Type u} [Ring A] {B : Type u'}
    [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    TauCeti.finiteProjectiveModulesSplitK0Equiv B (e.finiteProjectiveModulesSplitK0Equiv x) =
      e.finiteProjectiveModulesK0Equiv (TauCeti.finiteProjectiveModulesSplitK0Equiv A x) := by
  refine DFunLike.congr_fun (SplitK0.hom_ext
    (f := (TauCeti.finiteProjectiveModulesSplitK0Equiv B).toAddMonoidHom.comp
      e.finiteProjectiveModulesSplitK0Equiv.toAddMonoidHom)
    (g := e.finiteProjectiveModulesK0Equiv.toAddMonoidHom.comp
      (TauCeti.finiteProjectiveModulesSplitK0Equiv A).toAddMonoidHom) fun P ↦ ?_) x
  simp

end CategoryTheory.Equivalence

namespace RingEquiv

open TauCeti

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism on `SplitK0` of finitely generated
projective modules by extension of scalars along `e` and `e.symm`. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddMonoidHom.toAddEquiv
    (SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} e.symm.toRingHom.finiteProjectiveModulesExtendScalars)
    (AddMonoidHom.ext fun x ↦ by simp)
    (AddMonoidHom.ext fun x ↦ by simp)

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_apply {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv x =
      SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars x :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_symm {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    e.finiteProjectiveModulesSplitK0Equiv.symm = e.symm.finiteProjectiveModulesSplitK0Equiv :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesSplitK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).finiteProjectiveModulesSplitK0Equiv = AddEquiv.refl _ := by
  ext x
  simp

theorem finiteProjectiveModulesSplitK0Equiv_trans {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').finiteProjectiveModulesSplitK0Equiv =
      e.finiteProjectiveModulesSplitK0Equiv.trans e'.finiteProjectiveModulesSplitK0Equiv := by
  ext x
  simp [RingEquiv.toRingHom_trans]

/-- **Extension and restriction of scalars agree along a ring isomorphism.** For `e : R ≃+* S`,
extension of scalars along `e.toRingHom` induces the same map on `SplitK0` as restriction of scalars
along `e.symm` (`(ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm`). -/
theorem map_finiteProjectiveModulesExtendScalars_eq {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars =
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          e).symm.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) := by
  refine SplitK0.hom_ext fun P ↦ ?_
  rw [SplitK0.map_of, Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom,
    SplitK0.map_of]
  refine SplitK0.of_congr (ObjectProperty.isoMk _ ?_)
  exact eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
    (BalancedExtension.functorRingEquivIso.{u, u, u} e).app P.obj ≪≫
    eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      e).symm.finiteProjectiveModulesEquivalence_functor_obj_obj P).symm

theorem finiteProjectiveModulesSplitK0Equiv_eq_restrictScalars {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    e.finiteProjectiveModulesSplitK0Equiv =
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        e).symm.finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective (map_finiteProjectiveModulesExtendScalars_eq e)

end RingEquiv

namespace TauCeti

/-! ### Zero ring, binary product rings, matrix rings, and rank isomorphisms on `SplitK0` -/

/-- Over a subsingleton (zero) ring, every module is a zero object, so `SplitK0` of finitely
generated projective modules is trivial. -/
instance {R : Type u} [Ring R] [Subsingleton R] :
    Subsingleton (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) := by
  have hzero : ∀ x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory, x = 0 := by
    refine DFunLike.congr_fun (SplitK0.hom_ext (f := AddMonoidHom.id _) (g := 0) fun P ↦ ?_)
    have : Subsingleton P.obj :=
      ⟨fun x y ↦ by
        rw [← one_smul R x, Subsingleton.elim (1 : R) 0, zero_smul,
          ← one_smul R y, Subsingleton.elim (1 : R) 0, zero_smul]⟩
    exact SplitK0.of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules R).ι P (ModuleCat.isZero_of_subsingleton P.obj))
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

section ProdRing

private theorem fst_restrictScalars_finiteProjective (R S : Type u) [Ring R] [Ring S] :
    finiteProjectiveModules R ≤
      (finiteProjectiveModules (R × S)).inverseImage
        (ModuleCat.restrictScalars (RingHom.fst R S)) := by
  rw [RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff]
  let : Module (R × S) R := (RingHom.fst R S).toModule
  let i : R →ₗ[R × S] R × S :=
    { toFun r := (r, 0)
      map_add' _ _ := by ext <;> simp
      map_smul' x r := Prod.ext rfl (mul_zero x.2).symm }
  let p : R × S →ₗ[R × S] R :=
    { toFun x := x.1
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hpi : p ∘ₗ i = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  exact ⟨Module.Finite.of_surjective p fun r ↦ ⟨(r, 0), rfl⟩,
    Module.Projective.of_split i p hpi⟩

private theorem snd_restrictScalars_finiteProjective (R S : Type u) [Ring R] [Ring S] :
    finiteProjectiveModules S ≤
      (finiteProjectiveModules (R × S)).inverseImage
        (ModuleCat.restrictScalars (RingHom.snd R S)) := by
  rw [RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff]
  let : Module (R × S) S := (RingHom.snd R S).toModule
  let i : S →ₗ[R × S] R × S :=
    { toFun s := (0, s)
      map_add' _ _ := by ext <;> simp
      map_smul' x s := Prod.ext (mul_zero x.1).symm rfl }
  let p : R × S →ₗ[R × S] S :=
    { toFun x := x.2
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hpi : p ∘ₗ i = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  exact ⟨Module.Finite.of_surjective p fun s ↦ ⟨(0, s), rfl⟩,
    Module.Projective.of_split i p hpi⟩

private noncomputable def prodInlFunctor (R S : Type u) [Ring R] [Ring S] :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (R × S)).FullSubcategory :=
  (finiteProjectiveModules (R × S)).lift
    ((finiteProjectiveModules R).ι ⋙ ModuleCat.restrictScalars.{u} (RingHom.fst R S))
    fun P ↦ fst_restrictScalars_finiteProjective R S P.obj P.property

private instance (R S : Type u) [Ring R] [Ring S] : (prodInlFunctor R S).Additive := by
  have : (prodInlFunctor R S ⋙ (finiteProjectiveModules (R × S)).ι).Additive :=
    inferInstanceAs
      ((finiteProjectiveModules R).ι ⋙ ModuleCat.restrictScalars.{u} (RingHom.fst R S)).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules (R × S)).ι

private noncomputable def prodInrFunctor (R S : Type u) [Ring R] [Ring S] :
    (finiteProjectiveModules S).FullSubcategory ⥤
      (finiteProjectiveModules (R × S)).FullSubcategory :=
  (finiteProjectiveModules (R × S)).lift
    ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars.{u} (RingHom.snd R S))
    fun Q ↦ snd_restrictScalars_finiteProjective R S Q.obj Q.property

private instance (R S : Type u) [Ring R] [Ring S] : (prodInrFunctor R S).Additive := by
  have : (prodInrFunctor R S ⋙ (finiteProjectiveModules (R × S)).ι).Additive :=
    inferInstanceAs
      ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars.{u} (RingHom.snd R S)).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules (R × S)).ι

-- `ModuleCat.restrictScalars` keeps the underlying carrier of `M`; wrapping the carrier cast in
-- typed helpers avoids semireducible `show` terms inside tactic states at `implicit` transparency.
private def ofRestrictScalars {A B : Type u} [Ring A] [Ring B] (f : A →+* B) (M : ModuleCat.{u} B)
    (m : (ModuleCat.restrictScalars.{u} f).obj M) : M :=
  m

private def toRestrictScalars {A B : Type u} [Ring A] [Ring B] (f : A →+* B) (M : ModuleCat.{u} B)
    (m : M) : (ModuleCat.restrictScalars.{u} f).obj M :=
  m

private theorem ofRestrictScalars_injective {A B : Type u} [Ring A] [Ring B] (f : A →+* B)
    (M : ModuleCat.{u} B) {x y : (ModuleCat.restrictScalars.{u} f).obj M}
    (h : ofRestrictScalars f M x = ofRestrictScalars f M y) : x = y :=
  h

private noncomputable def balancedExtensionFstRestrictFstEquiv (R S : Type u) [Ring R] [Ring S]
    (M : ModuleCat.{u} R) :
    BalancedExtension (RingHom.fst R S)
        ((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).obj M) ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (BalancedExtension.lift ((RingHom.fst R S).restrictScalarsSemilinearMap M))
    { toFun m :=
        BalancedExtension.tmul (RingHom.fst R S) 1 (toRestrictScalars (RingHom.fst R S) M m)
      map_add' m₁ m₂ := BalancedExtension.tmul_add 1 _ _
      map_smul' r m := by
        have hsmul : toRestrictScalars (RingHom.fst R S) M (r • m) =
            ((r, (0 : S)) : R × S) • toRestrictScalars (RingHom.fst R S) M m :=
          (ModuleCat.restrictScalars.smul_def (RingHom.fst R S) (r, (0 : S))
            (toRestrictScalars (RingHom.fst R S) M m)).symm
        rw [hsmul, BalancedExtension.tmul_smul]
        simp [BalancedExtension.smul_tmul] }
    (LinearMap.ext fun m ↦
      (BalancedExtension.lift_tmul _ 1 (toRestrictScalars (RingHom.fst R S) M m)).trans
        ((congrArg ((1 : R) • ·) ((RingHom.fst R S).restrictScalarsSemilinearMap_apply M
          (toRestrictScalars (RingHom.fst R S) M m))).trans (one_smul R m)))
    (BalancedExtension.hom_ext fun m ↦ by
      simp only [LinearMap.comp_apply, BalancedExtension.lift_tmul,
        RingHom.restrictScalarsSemilinearMap_apply, LinearMap.coe_mk, LinearMap.id_apply]
      exact congrArg
        (fun y : M ↦ BalancedExtension.tmul (RingHom.fst R S) 1
          (toRestrictScalars (RingHom.fst R S) M y))
        (one_smul R (ofRestrictScalars (RingHom.fst R S) M m)))

private noncomputable def balancedExtensionSndRestrictSndEquiv (R S : Type u) [Ring R] [Ring S]
    (N : ModuleCat.{u} S) :
    BalancedExtension (RingHom.snd R S)
        ((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).obj N) ≃ₗ[S] N :=
  LinearEquiv.ofLinearMap
    (BalancedExtension.lift ((RingHom.snd R S).restrictScalarsSemilinearMap N))
    { toFun n :=
        BalancedExtension.tmul (RingHom.snd R S) 1 (toRestrictScalars (RingHom.snd R S) N n)
      map_add' n₁ n₂ := BalancedExtension.tmul_add 1 _ _
      map_smul' s n := by
        have hsmul : toRestrictScalars (RingHom.snd R S) N (s • n) =
            (((0 : R), s) : R × S) • toRestrictScalars (RingHom.snd R S) N n :=
          (ModuleCat.restrictScalars.smul_def (RingHom.snd R S) ((0 : R), s)
            (toRestrictScalars (RingHom.snd R S) N n)).symm
        rw [hsmul, BalancedExtension.tmul_smul]
        simp [BalancedExtension.smul_tmul] }
    (LinearMap.ext fun n ↦
      (BalancedExtension.lift_tmul _ 1 (toRestrictScalars (RingHom.snd R S) N n)).trans
        ((congrArg ((1 : S) • ·) ((RingHom.snd R S).restrictScalarsSemilinearMap_apply N
          (toRestrictScalars (RingHom.snd R S) N n))).trans (one_smul S n)))
    (BalancedExtension.hom_ext fun n ↦ by
      simp only [LinearMap.comp_apply, BalancedExtension.lift_tmul,
        RingHom.restrictScalarsSemilinearMap_apply, LinearMap.coe_mk, LinearMap.id_apply]
      exact congrArg
        (fun y : N ↦ BalancedExtension.tmul (RingHom.snd R S) 1
          (toRestrictScalars (RingHom.snd R S) N y))
        (one_smul S (ofRestrictScalars (RingHom.snd R S) N n)))

private theorem subsingleton_balancedExtension_fst_restrict_snd (R S : Type u) [Ring R] [Ring S]
    (N : ModuleCat.{u} S) :
    Subsingleton (BalancedExtension (RingHom.fst R S)
      ((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).obj N)) := by
  let Y := (ModuleCat.restrictScalars.{u} (RingHom.snd R S)).obj N
  have hzero : ∀ z : BalancedExtension (RingHom.fst R S) Y, z = 0 := fun z ↦ by
    induction z using BalancedExtension.induction_on with
    | tmul r n =>
      have h := BalancedExtension.tmul_smul (f := RingHom.fst R S) (P := Y) r (1, (0 : S)) n
      have hsmul : ((1, (0 : S)) : R × S) • n = 0 := by
        rw [ModuleCat.restrictScalars.smul_def]
        exact zero_smul S (ofRestrictScalars (RingHom.snd R S) N n)
      rw [hsmul, BalancedExtension.tmul_zero] at h
      simpa using h.symm
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

private theorem subsingleton_balancedExtension_snd_restrict_fst (R S : Type u) [Ring R] [Ring S]
    (M : ModuleCat.{u} R) :
    Subsingleton (BalancedExtension (RingHom.snd R S)
      ((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).obj M)) := by
  let X := (ModuleCat.restrictScalars.{u} (RingHom.fst R S)).obj M
  have hzero : ∀ z : BalancedExtension (RingHom.snd R S) X, z = 0 := fun z ↦ by
    induction z using BalancedExtension.induction_on with
    | tmul s m =>
      have h := BalancedExtension.tmul_smul (f := RingHom.snd R S) (P := X) s ((0 : R), 1) m
      have hsmul : (((0 : R), 1) : R × S) • m = 0 := by
        rw [ModuleCat.restrictScalars.smul_def]
        exact zero_smul R (ofRestrictScalars (RingHom.fst R S) M m)
      rw [hsmul, BalancedExtension.tmul_zero] at h
      simpa using h.symm
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

private def prodFstLift (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] : BalancedExtension (RingHom.fst R S) P →+ P :=
  (BalancedTensorProduct.lift
    (LinearMap.mk₂ ℤ
      (fun r p ↦ (((BalancedExtension.Scalars.of (RingHom.fst R S)).symm r, (0 : S)) : R × S) • p)
      (fun r₁ r₂ p ↦ by
        have h : (((BalancedExtension.Scalars.of (RingHom.fst R S)).symm (r₁ + r₂),
            (0 : S)) : R × S) =
            ((BalancedExtension.Scalars.of (RingHom.fst R S)).symm r₁, 0) +
              ((BalancedExtension.Scalars.of (RingHom.fst R S)).symm r₂, 0) :=
          Prod.ext (map_add _ r₁ r₂) (add_zero 0).symm
        rw [h, add_smul])
      (fun z r p ↦ by
        have h : (((BalancedExtension.Scalars.of (RingHom.fst R S)).symm (z • r),
            (0 : S)) : R × S) =
            z • (((BalancedExtension.Scalars.of (RingHom.fst R S)).symm r, (0 : S)) : R × S) :=
          Prod.ext (map_zsmul _ z r) (zsmul_zero z).symm
        rw [h, smul_assoc])
      (fun _ _ _ ↦ smul_add _ _ _)
      (fun _ _ _ ↦ smul_comm _ _ _))
    fun x r p ↦ by
      obtain ⟨r, rfl⟩ := (BalancedExtension.Scalars.of (RingHom.fst R S)).surjective r
      simp only [LinearMap.mk₂_apply, BalancedExtension.Scalars.op_smul_of,
        AddEquiv.symm_apply_apply, ← mul_smul]
      exact congrArg (· • p) (Prod.ext rfl (zero_mul x.2).symm)).toAddMonoidHom

@[simp]
private theorem prodFstLift_tmul (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] (r : R) (p : P) :
    prodFstLift R S P (BalancedExtension.tmul (RingHom.fst R S) r p) =
      ((r, (0 : S)) : R × S) • p := by
  rw [prodFstLift, BalancedExtension.tmul_def, LinearMap.toAddMonoidHom_coe,
    BalancedTensorProduct.lift_tmul]
  simp

private def prodSndLift (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] : BalancedExtension (RingHom.snd R S) P →+ P :=
  (BalancedTensorProduct.lift
    (LinearMap.mk₂ ℤ
      (fun s p ↦ (((0 : R), (BalancedExtension.Scalars.of (RingHom.snd R S)).symm s) : R × S) • p)
      (fun s₁ s₂ p ↦ by
        have h : (((0 : R),
            (BalancedExtension.Scalars.of (RingHom.snd R S)).symm (s₁ + s₂)) : R × S) =
            (0, (BalancedExtension.Scalars.of (RingHom.snd R S)).symm s₁) +
              (0, (BalancedExtension.Scalars.of (RingHom.snd R S)).symm s₂) :=
          Prod.ext (add_zero 0).symm (map_add _ s₁ s₂)
        rw [h, add_smul])
      (fun z s p ↦ by
        have h : (((0 : R),
            (BalancedExtension.Scalars.of (RingHom.snd R S)).symm (z • s)) : R × S) =
            z • (((0 : R), (BalancedExtension.Scalars.of (RingHom.snd R S)).symm s) : R × S) :=
          Prod.ext (zsmul_zero z).symm (map_zsmul _ z s)
        rw [h, smul_assoc])
      (fun _ _ _ ↦ smul_add _ _ _)
      (fun _ _ _ ↦ smul_comm _ _ _))
    fun x s p ↦ by
      obtain ⟨s, rfl⟩ := (BalancedExtension.Scalars.of (RingHom.snd R S)).surjective s
      simp only [LinearMap.mk₂_apply, BalancedExtension.Scalars.op_smul_of,
        AddEquiv.symm_apply_apply, ← mul_smul]
      exact congrArg (· • p) (Prod.ext (zero_mul x.1).symm rfl)).toAddMonoidHom

@[simp]
private theorem prodSndLift_tmul (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] (s : S) (p : P) :
    prodSndLift R S P (BalancedExtension.tmul (RingHom.snd R S) s p) =
      (((0 : R), s) : R × S) • p := by
  rw [prodSndLift, BalancedExtension.tmul_def, LinearMap.toAddMonoidHom_coe,
    BalancedTensorProduct.lift_tmul]
  simp

private theorem tmul_fst_prodFstLift (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] (q : BalancedExtension (RingHom.fst R S) P) :
    BalancedExtension.tmul (RingHom.fst R S) 1 (prodFstLift R S P q) = q := by
  induction q using BalancedExtension.induction_on with
  | tmul r p => simp [BalancedExtension.tmul_smul]
  | add x y hx hy => rw [map_add, BalancedExtension.tmul_add, hx, hy]

private theorem tmul_fst_prodSndLift (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] (q : BalancedExtension (RingHom.snd R S) P) :
    BalancedExtension.tmul (RingHom.fst R S) 1 (prodSndLift R S P q) = 0 := by
  induction q using BalancedExtension.induction_on with
  | tmul s p => simp [BalancedExtension.tmul_smul]
  | add x y hx hy => rw [map_add, BalancedExtension.tmul_add, hx, hy, add_zero]

private theorem tmul_snd_prodFstLift (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] (q : BalancedExtension (RingHom.fst R S) P) :
    BalancedExtension.tmul (RingHom.snd R S) 1 (prodFstLift R S P q) = 0 := by
  induction q using BalancedExtension.induction_on with
  | tmul r p => simp [BalancedExtension.tmul_smul]
  | add x y hx hy => rw [map_add, BalancedExtension.tmul_add, hx, hy, add_zero]

private theorem tmul_snd_prodSndLift (R S : Type u) [Ring R] [Ring S] (P : Type u) [AddCommGroup P]
    [Module (R × S) P] (q : BalancedExtension (RingHom.snd R S) P) :
    BalancedExtension.tmul (RingHom.snd R S) 1 (prodSndLift R S P q) = q := by
  induction q using BalancedExtension.induction_on with
  | tmul s p => simp [BalancedExtension.tmul_smul]
  | add x y hx hy => rw [map_add, BalancedExtension.tmul_add, hx, hy]

private theorem ofRestrictScalars_semilinearMap_includeRight {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (P : ModuleCat.{u} R) (p : P) :
    ofRestrictScalars f (ModuleCat.of S (BalancedExtension f P))
      ((ModuleCat.semilinearMapAddEquiv f P (ModuleCat.of S (BalancedExtension f P))
        (BalancedExtension.includeRight f P)).hom p) =
      BalancedExtension.tmul f 1 p :=
  BalancedExtension.includeRight_apply p

private noncomputable def prodModuleDecompLinearEquiv (R S : Type u) [Ring R] [Ring S]
    (P : ModuleCat.{u} (R × S)) :
    P ≃ₗ[R × S]
      ((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).obj
        (ModuleCat.of R (BalancedExtension (RingHom.fst R S) P))) ×
      ((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).obj
        (ModuleCat.of S (BalancedExtension (RingHom.snd R S) P))) :=
  let M₁ := ModuleCat.of R (BalancedExtension (RingHom.fst R S) P)
  let M₂ := ModuleCat.of S (BalancedExtension (RingHom.snd R S) P)
  let u₁ := (ModuleCat.semilinearMapAddEquiv (RingHom.fst R S) P M₁
    (BalancedExtension.includeRight (RingHom.fst R S) P)).hom
  let u₂ := (ModuleCat.semilinearMapAddEquiv (RingHom.snd R S) P M₂
    (BalancedExtension.includeRight (RingHom.snd R S) P)).hom
  let φ := LinearMap.prod u₁ u₂
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := φ.map_smul
    invFun q :=
      prodFstLift R S P (ofRestrictScalars (RingHom.fst R S) M₁ q.1) +
        prodSndLift R S P (ofRestrictScalars (RingHom.snd R S) M₂ q.2)
    left_inv p := by
      have hsum : ((1, (0 : S)) : R × S) + (0, 1) = 1 := Prod.ext (add_zero 1) (zero_add 1)
      change prodFstLift R S P (ofRestrictScalars (RingHom.fst R S) M₁ (u₁ p)) +
          prodSndLift R S P (ofRestrictScalars (RingHom.snd R S) M₂ (u₂ p)) = p
      rw [ofRestrictScalars_semilinearMap_includeRight,
        ofRestrictScalars_semilinearMap_includeRight,
        prodFstLift_tmul, prodSndLift_tmul, ← add_smul, hsum, one_smul]
    right_inv := fun ⟨q₁, q₂⟩ ↦ by
      let q₁' : BalancedExtension (RingHom.fst R S) P := ofRestrictScalars (RingHom.fst R S) M₁ q₁
      let q₂' : BalancedExtension (RingHom.snd R S) P := ofRestrictScalars (RingHom.snd R S) M₂ q₂
      refine Prod.ext (ofRestrictScalars_injective (RingHom.fst R S) M₁ ?_)
        (ofRestrictScalars_injective (RingHom.snd R S) M₂ ?_)
      · exact (ofRestrictScalars_semilinearMap_includeRight (RingHom.fst R S) P _).trans
          ((BalancedExtension.tmul_add 1 _ _).trans
            ((congrArg₂ (· + ·) (tmul_fst_prodFstLift R S P q₁')
              (tmul_fst_prodSndLift R S P q₂')).trans (add_zero q₁')))
      · exact (ofRestrictScalars_semilinearMap_includeRight (RingHom.snd R S) P _).trans
          ((BalancedExtension.tmul_add 1 _ _).trans
            ((congrArg₂ (· + ·) (tmul_snd_prodFstLift R S P q₁')
              (tmul_snd_prodSndLift R S P q₂')).trans (zero_add q₂'))) }

/-- **`SplitK0` of finitely generated projective modules commutes with binary products of rings.**
The forward map applies extension of scalars along `RingHom.fst R S` and `RingHom.snd R S`, and the
inverse adds restriction of scalars along the two projections. -/
noncomputable def finiteProjectiveModulesProdSplitK0Equiv (R S : Type u) [Ring R] [Ring S] :
    SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ×
        SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddEquiv.ofProdCoprod
    (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (prodInlFunctor R S))
    (SplitK0.map.{u, u} (prodInrFunctor R S))
    (SplitK0.hom_ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        SplitK0.map_of, AddMonoidHom.id_apply]
      let e₁ := ((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).mapIso
        (eqToIso ((RingHom.fst R S).finiteProjectiveModulesExtendScalars_obj_obj
          P).symm)).toLinearEquiv
      let e₂ := ((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).mapIso
        (eqToIso ((RingHom.snd R S).finiteProjectiveModulesExtendScalars_obj_obj
          P).symm)).toLinearEquiv
      exact (SplitK0.of_eq_add_of_linearEquiv_prod
        ((prodModuleDecompLinearEquiv R S P.obj).trans (e₁.prodCongr e₂))).symm)
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj (balancedExtensionFstRestrictFstEquiv R S M.obj))
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      let Z : ModuleCat.{u} R := ModuleCat.of R (BalancedExtension (RingHom.fst R S)
        ((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).obj N.obj))
      have : Subsingleton Z := subsingleton_balancedExtension_fst_restrict_snd R S N.obj
      have hzero : IsZero (((RingHom.fst R S).finiteProjectiveModulesExtendScalars.obj
          ((prodInrFunctor R S).obj N)).obj) :=
        (ModuleCat.isZero_of_subsingleton Z).of_iso
          (eqToIso ((RingHom.fst R S).finiteProjectiveModulesExtendScalars_obj_obj _))
      exact SplitK0.of_eq_zero_of_isZero
        (IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules R).ι _ hzero))
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      let Z : ModuleCat.{u} S := ModuleCat.of S (BalancedExtension (RingHom.snd R S)
        ((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).obj M.obj))
      have : Subsingleton Z := subsingleton_balancedExtension_snd_restrict_fst R S M.obj
      have hzero : IsZero (((RingHom.snd R S).finiteProjectiveModulesExtendScalars.obj
          ((prodInlFunctor R S).obj M)).obj) :=
        (ModuleCat.isZero_of_subsingleton Z).of_iso
          (eqToIso ((RingHom.snd R S).finiteProjectiveModulesExtendScalars_obj_obj _))
      exact SplitK0.of_eq_zero_of_isZero
        (IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules S).ι _ hzero))
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj (balancedExtensionSndRestrictSndEquiv R S N.obj))

@[simp]
theorem finiteProjectiveModulesProdSplitK0Equiv_apply (R S : Type u) [Ring R] [Ring S]
    (x : SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory) :
    finiteProjectiveModulesProdSplitK0Equiv R S x =
      (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars x,
        SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars x) :=
  AddEquiv.ofProdCoprod_apply _ _ _ _ _ _ _ _ _ x

theorem finiteProjectiveModulesProdSplitK0Equiv_selfObj (R S : Type u) [Ring R] [Ring S] :
    finiteProjectiveModulesProdSplitK0Equiv R S
        (SplitK0.of.{u} (FiniteProjectiveModules.selfObj (R × S))) =
      (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R),
        SplitK0.of.{u} (FiniteProjectiveModules.selfObj S)) := by
  simp

end ProdRing

section MatrixMorita

/-- The canonical functor sending a finitely generated projective `R`-module `P` to the finitely
generated projective `Matrix ι ι R`-module `ι → P`, manifestly independent of any choice of index
in `ι`. -/
noncomputable def finiteProjectiveModulesToMatrixFunctor (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  (finiteProjectiveModules (Matrix ι ι R)).lift
    ((finiteProjectiveModules R).ι ⋙ ModuleCat.toMatrixModCat R ι)
    fun P ↦ by
      obtain ⟨i⟩ := ‹Nonempty ι›
      have h := congrFun
        (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModules_inverseImage P.obj
      exact (ObjectProperty.prop_inverseImage_iff _ _ P.obj).mp (h.symm ▸ P.property)

instance (R : Type u) [Ring R] (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (finiteProjectiveModulesToMatrixFunctor R ι).Additive := by
  have : (ModuleCat.toMatrixModCat R ι).Additive :=
    { map_add := fun {_ _ _ _} ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦
        funext fun _ ↦ rfl }
  have : (finiteProjectiveModulesToMatrixFunctor R ι ⋙
      (finiteProjectiveModules (Matrix ι ι R)).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules R).ι ⋙ ModuleCat.toMatrixModCat R ι).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules (Matrix ι ι R)).ι

@[simp]
theorem finiteProjectiveModulesToMatrixFunctor_obj_obj (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesToMatrixFunctor R ι).obj P).obj =
      (ModuleCat.toMatrixModCat R ι).obj P.obj :=
  (rfl)

/-- For any index `i : ι`, `TauCeti.finiteProjectiveModulesToMatrixFunctor` induces the same map on
`SplitK0` as `ModuleCat.matrixEquivalence R i`. -/
theorem map_finiteProjectiveModulesToMatrixFunctor_eq (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] (i : ι) :
    SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι) =
      ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory) := by
  rw [Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom]
  exact SplitK0.map_congr.{u, u} fun P ↦ ⟨ObjectProperty.isoMk _ (eqToIso
    ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesEquivalence_functor_obj_obj
      P).symm)⟩

/-- **Matrix Morita invariance of `SplitK0`.** Sending `P` to the column module `ι → P` induces an
isomorphism `SplitK0 (finiteProjectiveModules R).FullSubcategory ≃+
SplitK0 (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory` whose underlying map is
independent of any choice of index in `ι`. -/
noncomputable def finiteProjectiveModulesMatrixSplitK0Equiv (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  AddEquiv.ofBijective (SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι)) <| by
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [map_finiteProjectiveModulesToMatrixFunctor_eq R ι i]
    exact (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv.bijective

@[simp]
theorem finiteProjectiveModulesMatrixSplitK0Equiv_of (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι (SplitK0.of.{u} P) =
      SplitK0.of.{u} ((finiteProjectiveModulesToMatrixFunctor R ι).obj P) :=
  SplitK0.map_of.{u, u} _ P

/-- For every `i : ι`, `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv` agrees with the
Morita equivalence induced by `ModuleCat.matrixEquivalence R i`. -/
theorem finiteProjectiveModulesMatrixSplitK0Equiv_eq (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] (i : ι) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι =
      (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective (map_finiteProjectiveModulesToMatrixFunctor_eq R ι i)

private def matrixOfColumnModuleLinearEquiv (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ((ModuleCat.toMatrixModCat R ι).obj (ModuleCat.of R (ι → R))) ≃ₗ[Matrix ι ι R]
      Matrix ι ι R where
  toFun := Matrix.of
  invFun M := M
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' A v := by
    ext i k
    -- On `toMatrixModCat`, `Matrix ι ι R` acts by `(A • v) i = ∑ j, A i j • v j`.
    change (∑ j : ι, A i j • v j) k = (A * Matrix.of v) i k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply]
    rfl

/-- Under `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv`, `|ι|` copies of `[R]` map to the
class of the regular module `[Matrix ι ι R]`. -/
@[simp]
theorem finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι
        (Fintype.card ι • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj (Matrix ι ι R)) := by
  rw [← SplitK0.of_freeObj (R := R) ι, finiteProjectiveModulesMatrixSplitK0Equiv_of]
  exact SplitK0.of_congr (ObjectProperty.isoMk _
    (matrixOfColumnModuleLinearEquiv R ι).toModuleIso)

/-- **Matrix Morita invariance of `SplitK0` for `n × n` matrices (`n ≠ 0`)** over an arbitrary
universe-polymorphic ring `R : Type u`. -/
noncomputable def finiteProjectiveModulesMatrixFinSplitK0Equiv (R : Type u) [Ring R]
    (n : ℕ) [NeZero n] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules (Matrix (Fin n) (Fin n) R)).FullSubcategory :=
  have : Nonempty (ULift.{u} (Fin n)) := ⟨⟨0⟩⟩
  (finiteProjectiveModulesMatrixSplitK0Equiv R (ULift.{u} (Fin n))).trans
    (Matrix.reindexRingEquiv R Equiv.ulift).finiteProjectiveModulesSplitK0Equiv

@[simp]
theorem finiteProjectiveModulesMatrixFinSplitK0Equiv_nsmul_selfObj (R : Type u) [Ring R]
    (n : ℕ) [NeZero n] :
    finiteProjectiveModulesMatrixFinSplitK0Equiv R n
        (n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj (Matrix (Fin n) (Fin n) R)) := by
  have : Nonempty (ULift.{u} (Fin n)) := ⟨⟨0⟩⟩
  have h := finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj R (ULift.{u} (Fin n))
  simp only [Fintype.card_ulift, Fintype.card_fin] at h
  rw [finiteProjectiveModulesMatrixFinSplitK0Equiv, AddEquiv.trans_apply, h,
    RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply,
    SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj]

end MatrixMorita

section Finrank

@[simp]
theorem FiniteProjectiveModules.finrank_selfObj (R : Type u) [Ring R] [StrongRankCondition R] :
    Module.finrank R (FiniteProjectiveModules.selfObj R).obj = 1 :=
  ModuleCat.finrank_of_self R

private noncomputable def finrankSplitK0Invariant (R : Type u) [Ring R] [StrongRankCondition R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    SplitK0.AdditiveInvariant (finiteProjectiveModules R).FullSubcategory ℤ where
  obj P := (Module.finrank R P.obj : ℤ)
  map_iso P Q e :=
    congrArg Nat.cast (((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv.finrank_eq)
  map_biprod P Q := by
    have := hfree P
    have := hfree Q
    exact_mod_cast (FiniteProjectiveModules.biprodLinearEquiv P Q).finrank_eq.trans
      Module.finrank_prod

/-- **Rank isomorphism `K₀(proj R) ≃+ ℤ` when finitely generated projective modules are free.**
Over a ring `R` satisfying `StrongRankCondition R` in which every finitely generated projective
left `R`-module is free, `Module.finrank` descends to an isomorphism sending `[P]` to `finrank R P`
and `[R]` to `1`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivOfFree (R : Type u) [Ring R]
    [StrongRankCondition R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  AddMonoidHom.toAddEquiv
    (SplitK0.lift.{u} (finrankSplitK0Invariant R hfree))
    (zmultiplesHom (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory)
      (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)))
    (SplitK0.hom_ext fun P ↦ by
      have := hfree P
      simp only [AddMonoidHom.comp_apply, SplitK0.lift_of, finrankSplitK0Invariant,
        zmultiplesHom_apply, natCast_zsmul, AddMonoidHom.id_apply]
      exact (SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := P)
        (R' := FiniteProjectiveModules.selfObj R)
        (Module.finBasis R P.obj).equivFun (.refl R R)).symm)
    (AddMonoidHom.ext_int <| by
      simp [finrankSplitK0Invariant])

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_of (R : Type u) [Ring R]
    [StrongRankCondition R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  SplitK0.lift_of.{u} _ P

theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_selfObj (R : Type u) [Ring R]
    [StrongRankCondition R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) :
    finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree
        (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) = 1 := by
  simp

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_symm_apply (R : Type u) [Ring R]
    [StrongRankCondition R]
    (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj) (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  (rfl)

/-- Over a division ring `D`, `Module.finrank` induces `K₀(proj D) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivDivisionRing (D : Type u)
    [DivisionRing D] :
    SplitK0.{u} (finiteProjectiveModules D).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree D fun _ ↦ inferInstance

/-- Over a nontrivial principal left-ideal ring without zero divisors, `Module.finrank` induces
`K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivPID (R : Type u) [Ring R]
    [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun P ↦
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (LinearMap.id : P.obj →ₗ[R] P.obj) Function.injective_id

/-- Over a commutative local ring `R`, `Module.finrank` induces `K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun _ ↦
    Module.free_of_projective_of_isLocalRing

end Finrank

/-! ### Algebraic `K₀` of a ring (right-module convention) -/

/-- **Algebraic `K₀` of a ring `R`**: the split Grothendieck group of finitely generated projective
right `R`-modules (encoded as left `Rᵐᵒᵖ`-modules). This matches the right-module convention of
`TauCeti.AlgebraicK1`, where `GL_n(R)` acts on finite free right `R`-modules. -/
abbrev AlgebraicK0 (R : Type u) [Ring R] : Type u :=
  SplitK0.{u} (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory

namespace AlgebraicK0

/-- The regular right `R`-module `R` (viewed as a left `Rᵐᵒᵖ`-module) in
`(finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory`. -/
def freeRankOne (R : Type u) [Ring R] : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  FiniteProjectiveModules.selfObj Rᵐᵒᵖ

/-- The canonical class `[R]` of the free right `R`-module of rank one in `AlgebraicK0 R`. -/
noncomputable def one (R : Type u) [Ring R] : AlgebraicK0 R :=
  SplitK0.of.{u} (freeRankOne R)

theorem one_def (R : Type u) [Ring R] : one R = SplitK0.of.{u} (freeRankOne R) :=
  (rfl)

/-- Every class in `AlgebraicK0 R` has the form `[P] - n • [R]` for some finitely generated
projective right `R`-module `P` and `n : ℕ`. -/
theorem exists_eq_of_sub_nsmul_one {R : Type u} [Ring R] (x : AlgebraicK0 R) :
    ∃ (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) (n : ℕ),
      x = SplitK0.of.{u} P - n • one R :=
  SplitK0.exists_eq_of_sub_nsmul_selfObj x

/-- **Covariant functoriality of algebraic `K₀`.** A ring homomorphism `f : R →+* S` induces
`AlgebraicK0 R →+ AlgebraicK0 S` by balanced extension of scalars `P ↦ P ⊗_R S` on right modules
(encoded via `RingHom.op f : Rᵐᵒᵖ →+* Sᵐᵒᵖ`). -/
noncomputable def map {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    AlgebraicK0 R →+ AlgebraicK0 S :=
  SplitK0.map.{u, u} (RingHom.op f).finiteProjectiveModulesExtendScalars

@[simp]
theorem map_of {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (P : (finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory) :
    map f (SplitK0.of.{u} P) =
      SplitK0.of.{u} ((RingHom.op f).finiteProjectiveModulesExtendScalars.obj P) :=
  SplitK0.map_of.{u, u} _ P

@[simp]
theorem map_id (R : Type u) [Ring R] :
    map (RingHom.id R) = AddMonoidHom.id (AlgebraicK0 R) :=
  (SplitK0.map_finiteProjectiveModulesExtendScalars_congr (RingHom.op_id R)).trans
    SplitK0.map_finiteProjectiveModulesExtendScalars_id

theorem map_comp {R S T : Type u} [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) :=
  (SplitK0.map_finiteProjectiveModulesExtendScalars_congr (RingHom.op_comp f g)).trans
    (SplitK0.map_finiteProjectiveModulesExtendScalars_comp (RingHom.op g))

@[simp]
theorem map_map {R S T : Type u} [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)
    (x : AlgebraicK0 R) :
    map g (map f x) = map (g.comp f) x :=
  (DFunLike.congr_fun (map_comp f g) x).symm

@[simp]
theorem map_one {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    map f (one R) = one S :=
  SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj (RingHom.op f)

end AlgebraicK0

end TauCeti

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism `AlgebraicK0 R ≃+ AlgebraicK0 S`. -/
noncomputable def RingEquiv.algebraicK0Equiv {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    TauCeti.AlgebraicK0 R ≃+ TauCeti.AlgebraicK0 S :=
  (RingEquiv.op e).finiteProjectiveModulesSplitK0Equiv

namespace RingEquiv

open TauCeti

@[simp]
theorem algebraicK0Equiv_apply {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    (x : AlgebraicK0 R) :
    e.algebraicK0Equiv x = AlgebraicK0.map e.toRingHom x :=
  (rfl)

@[simp]
theorem algebraicK0Equiv_symm {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    e.algebraicK0Equiv.symm = e.symm.algebraicK0Equiv :=
  (rfl)

@[simp]
theorem algebraicK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).algebraicK0Equiv = AddEquiv.refl (AlgebraicK0 R) := by
  ext x
  simp

theorem algebraicK0Equiv_trans {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').algebraicK0Equiv = e.algebraicK0Equiv.trans e'.algebraicK0Equiv := by
  ext x
  simp [RingEquiv.toRingHom_trans]

theorem algebraicK0Equiv_one {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    e.algebraicK0Equiv (AlgebraicK0.one R) = AlgebraicK0.one S := by
  simp

end RingEquiv

namespace TauCeti.AlgebraicK0

/-- For a commutative ring `R`, `RingEquiv.toOpposite R : R ≃+* Rᵐᵒᵖ` identifies `AlgebraicK0 R`
with the left-module `SplitK0` of `R` (and with `ExactK0 (finiteProjectiveModulesExactStructure R)`
after composing with `TauCeti.finiteProjectiveModulesSplitK0Equiv`). -/
noncomputable def commRingLeftSplitK0Equiv (R : Type u) [CommRing R] :
    AlgebraicK0 R ≃+ SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  (RingEquiv.toOpposite R).symm.finiteProjectiveModulesSplitK0Equiv

@[simp]
theorem commRingLeftSplitK0Equiv_one (R : Type u) [CommRing R] :
    commRingLeftSplitK0Equiv R (one R) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj (RingEquiv.toOpposite R).symm.toRingHom

/-- Over a subsingleton (zero) ring, `AlgebraicK0 R` is trivial. -/
theorem subsingleton (R : Type u) [Ring R] [Subsingleton R] : Subsingleton (AlgebraicK0 R) :=
  inferInstance

/-- **Product decomposition of algebraic `K₀`.** For rings `R` and `S`,
`AlgebraicK0 (R × S) ≃+ AlgebraicK0 R × AlgebraicK0 S`, acting by `AlgebraicK0.map` along the two
projections. -/
noncomputable def prodEquiv (R S : Type u) [Ring R] [Ring S] :
    AlgebraicK0 (R × S) ≃+ AlgebraicK0 R × AlgebraicK0 S :=
  (RingEquiv.prodMulOpposite R S).finiteProjectiveModulesSplitK0Equiv.trans
    (finiteProjectiveModulesProdSplitK0Equiv Rᵐᵒᵖ Sᵐᵒᵖ)

@[simp]
theorem prodEquiv_apply (R S : Type u) [Ring R] [Ring S] (x : AlgebraicK0 (R × S)) :
    prodEquiv R S x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) := by
  simp only [prodEquiv, AddEquiv.trans_apply, RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply,
    finiteProjectiveModulesProdSplitK0Equiv_apply,
    SplitK0.map_finiteProjectiveModulesExtendScalars_apply_map, map]
  exact Prod.ext
    (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
      (RingEquiv.fst_comp_prodMulOpposite R S)) x)
    (DFunLike.congr_fun (SplitK0.map_finiteProjectiveModulesExtendScalars_congr
      (RingEquiv.snd_comp_prodMulOpposite R S)) x)

theorem prodEquiv_one (R S : Type u) [Ring R] [Ring S] :
    prodEquiv R S (one (R × S)) = (one R, one S) := by
  simp

/-- **Matrix Morita invariance of algebraic `K₀`.** For a nonempty finite index type `ι`,
`AlgebraicK0 R ≃+ AlgebraicK0 (Matrix ι ι R)` canonically (with no dependence on a chosen index in
`ι`), sending `|ι| • [R]` to `[Matrix ι ι R]`. -/
noncomputable def matrixEquiv (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    AlgebraicK0 R ≃+ AlgebraicK0 (Matrix ι ι R) :=
  (finiteProjectiveModulesMatrixSplitK0Equiv Rᵐᵒᵖ ι).trans
    (RingEquiv.mopMatrix (m := ι) (α := R)).finiteProjectiveModulesSplitK0Equiv

@[simp]
theorem matrixEquiv_card_nsmul_one (R : Type u) [Ring R]
    (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    matrixEquiv R ι (Fintype.card ι • one R) = one (Matrix ι ι R) := by
  simp only [matrixEquiv, one, freeRankOne, AddEquiv.trans_apply,
    finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj,
    RingEquiv.finiteProjectiveModulesSplitK0Equiv_apply]
  exact SplitK0.map_finiteProjectiveModulesExtendScalars_selfObj _

/-- **Matrix Morita invariance of algebraic `K₀` for `n × n` matrices (`n ≠ 0`)**, sending
`n • [R]` to `[Matrix (Fin n) (Fin n) R]`. -/
noncomputable def matrixFinEquiv (R : Type u) [Ring R] (n : ℕ) [NeZero n] :
    AlgebraicK0 R ≃+ AlgebraicK0 (Matrix (Fin n) (Fin n) R) :=
  have : Nonempty (ULift.{u} (Fin n)) := ⟨⟨0⟩⟩
  (matrixEquiv R (ULift.{u} (Fin n))).trans
    (RingEquiv.algebraicK0Equiv (Matrix.reindexRingEquiv R Equiv.ulift))

@[simp]
theorem matrixFinEquiv_nsmul_one (R : Type u) [Ring R] (n : ℕ) [NeZero n] :
    matrixFinEquiv R n (n • one R) = one (Matrix (Fin n) (Fin n) R) := by
  have : Nonempty (ULift.{u} (Fin n)) := ⟨⟨0⟩⟩
  have h := matrixEquiv_card_nsmul_one R (ULift.{u} (Fin n))
  simp only [Fintype.card_ulift, Fintype.card_fin] at h
  rw [matrixFinEquiv, AddEquiv.trans_apply, h, RingEquiv.algebraicK0Equiv_one]

/-- **Rank isomorphism `AlgebraicK0 D ≃+ ℤ` over a division ring `D`**, normalized so that
`[D] ↦ 1`. -/
noncomputable def finrankEquivDivisionRing (D : Type u) [DivisionRing D] :
    AlgebraicK0 D ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivDivisionRing Dᵐᵒᵖ

@[simp]
theorem finrankEquivDivisionRing_of (D : Type u) [DivisionRing D]
    (P : (finiteProjectiveModules Dᵐᵒᵖ).FullSubcategory) :
    finrankEquivDivisionRing D (SplitK0.of.{u} P) = (Module.finrank Dᵐᵒᵖ P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of Dᵐᵒᵖ _ P

@[simp]
theorem finrankEquivDivisionRing_one (D : Type u) [DivisionRing D] :
    finrankEquivDivisionRing D (one D) = 1 :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_selfObj Dᵐᵒᵖ _

@[simp]
theorem finrankEquivDivisionRing_symm_apply (D : Type u) [DivisionRing D] (n : ℤ) :
    (finrankEquivDivisionRing D).symm n = n • one D :=
  (rfl)

/-- **Rank isomorphism `AlgebraicK0 R ≃+ ℤ` over a principal ideal domain `R`**, normalized so that
`[R] ↦ 1`. -/
noncomputable def finrankEquivPID (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] :
    AlgebraicK0 R ≃+ ℤ :=
  (commRingLeftSplitK0Equiv R).trans (finiteProjectiveModulesFinrankSplitK0EquivPID R)

@[simp]
theorem finrankEquivPID_one (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    finrankEquivPID R (one R) = 1 := by
  simp [finrankEquivPID, finiteProjectiveModulesFinrankSplitK0EquivPID]

@[simp]
theorem finrankEquivPID_symm_apply (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (n : ℤ) :
    (finrankEquivPID R).symm n = n • one R := by
  apply (finrankEquivPID R).injective
  simp

/-- **Rank isomorphism `AlgebraicK0 ℤ ≃+ ℤ`**, sending `[ℤ]` to `1`. -/
noncomputable def finrankEquivInt : AlgebraicK0 ℤ ≃+ ℤ :=
  finrankEquivPID ℤ

@[simp]
theorem finrankEquivInt_one : finrankEquivInt (one ℤ) = 1 :=
  finrankEquivPID_one ℤ

@[simp]
theorem finrankEquivInt_symm_apply (n : ℤ) : finrankEquivInt.symm n = n • one ℤ :=
  finrankEquivPID_symm_apply ℤ n

/-- **Rank isomorphism `AlgebraicK0 R ≃+ ℤ` over a commutative local ring `R`**, normalized so that
`[R] ↦ 1`. -/
noncomputable def finrankEquivLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    AlgebraicK0 R ≃+ ℤ :=
  (commRingLeftSplitK0Equiv R).trans (finiteProjectiveModulesFinrankSplitK0EquivLocalRing R)

@[simp]
theorem finrankEquivLocalRing_one (R : Type u) [CommRing R] [IsLocalRing R] :
    finrankEquivLocalRing R (one R) = 1 := by
  simp [finrankEquivLocalRing, finiteProjectiveModulesFinrankSplitK0EquivLocalRing]

@[simp]
theorem finrankEquivLocalRing_symm_apply (R : Type u) [CommRing R] [IsLocalRing R] (n : ℤ) :
    (finrankEquivLocalRing R).symm n = n • one R := by
  apply (finrankEquivLocalRing R).injective
  simp

end TauCeti.AlgebraicK0
