/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Morita.Matrix
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ExtendScalars
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.RingEquiv
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Category.ModuleCat.Finrank

import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.Algebra.Group.Prod
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RingTheory.LocalRing.Module

/-!
# Split `K₀` of finitely generated projective modules: Morita invariance, products, and rank

For a possibly noncommutative ring `R`, this file develops the categorical and group-level API of
the left-module projective Grothendieck group
`SplitK0 (finiteProjectiveModules R).FullSubcategory`. The right-module specialization
`TauCeti.AlgebraicK0` matching `TauCeti.AlgebraicK1` builds on this file in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.AlgebraicK0`.

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

open CategoryTheory CategoryTheory.Limits

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
      e.finiteProjectiveModulesK0Equiv (TauCeti.finiteProjectiveModulesSplitK0Equiv A x) :=
  DFunLike.congr_fun (SplitK0.hom_ext
    (f := (TauCeti.finiteProjectiveModulesSplitK0Equiv B).toAddMonoidHom.comp
      e.finiteProjectiveModulesSplitK0Equiv.toAddMonoidHom)
    (g := e.finiteProjectiveModulesK0Equiv.toAddMonoidHom.comp
      (TauCeti.finiteProjectiveModulesSplitK0Equiv A).toAddMonoidHom) fun _ ↦ by simp) x

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
  ext x; simp

theorem finiteProjectiveModulesSplitK0Equiv_trans {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').finiteProjectiveModulesSplitK0Equiv =
      e.finiteProjectiveModulesSplitK0Equiv.trans e'.finiteProjectiveModulesSplitK0Equiv := by
  ext x; simp [RingEquiv.toRingHom_trans]

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
  exact SplitK0.of_congr <| ObjectProperty.isoMk _ <|
    eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
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

private theorem split_restrictScalars_finiteProjective {E A : Type u} [Ring E] [Ring A]
    (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a)
    (hmul_left : ∀ e a, e * j a = j (p e * a)) :
    finiteProjectiveModules A ≤
      (finiteProjectiveModules E).inverseImage (ModuleCat.restrictScalars p) := by
  rw [RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff]
  let : Module E A := p.toModule
  let i : A →ₗ[E] E := { toAddHom := j.toAddHom, map_smul' e a := (hmul_left e a).symm }
  let q : E →ₗ[E] A := { toAddHom := p.toAddMonoidHom.toAddHom, map_smul' := p.map_mul }
  exact ⟨Module.Finite.of_surjective q fun a ↦ ⟨j a, hpj a⟩,
    Module.Projective.of_split i q (LinearMap.ext hpj)⟩

private noncomputable def splitRestrictFunctor {E A : Type u} [Ring E] [Ring A]
    (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a)
    (hmul_left : ∀ e a, e * j a = j (p e * a)) :
    (finiteProjectiveModules A).FullSubcategory ⥤
      (finiteProjectiveModules E).FullSubcategory :=
  (finiteProjectiveModules E).lift ((finiteProjectiveModules A).ι ⋙ ModuleCat.restrictScalars.{u} p)
    fun M ↦ split_restrictScalars_finiteProjective p j hpj hmul_left M.obj M.property

private theorem additive_splitRestrictFunctor {E A : Type u} [Ring E] [Ring A]
    (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a)
    (hmul_left : ∀ e a, e * j a = j (p e * a)) :
    (splitRestrictFunctor p j hpj hmul_left).Additive := by
  have : (splitRestrictFunctor p j hpj hmul_left ⋙ (finiteProjectiveModules E).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules A).ι ⋙ ModuleCat.restrictScalars.{u} p).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules E).ι

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

private noncomputable def balancedExtensionRestrictSelfEquiv {E A : Type u} [Ring E] [Ring A]
    (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a) (M : ModuleCat.{u} A) :
    BalancedExtension p ((ModuleCat.restrictScalars.{u} p).obj M) ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap (BalancedExtension.lift (p.restrictScalarsSemilinearMap M))
    { toFun m := BalancedExtension.tmul p 1 (toRestrictScalars p M m)
      map_add' _ _ := BalancedExtension.tmul_add 1 _ _
      map_smul' a m := by
        have hsmul : toRestrictScalars p M (a • m) = j a • toRestrictScalars p M m :=
          ofRestrictScalars_injective p M <| (congrArg (fun b : A ↦ b • m) (hpj a).symm).trans
            (ModuleCat.restrictScalars.smul_def p (j a) (toRestrictScalars p M m)).symm
        rw [hsmul, BalancedExtension.tmul_smul, one_mul, hpj]
        simp [BalancedExtension.smul_tmul] }
    (LinearMap.ext fun m ↦ (BalancedExtension.lift_tmul _ 1 (toRestrictScalars p M m)).trans
      ((congrArg ((1 : A) • ·) (p.restrictScalarsSemilinearMap_apply M
        (toRestrictScalars p M m))).trans (one_smul A m)))
    (BalancedExtension.hom_ext fun m ↦ by
      simp only [LinearMap.comp_apply, BalancedExtension.lift_tmul,
        RingHom.restrictScalarsSemilinearMap_apply, LinearMap.coe_mk, LinearMap.id_apply]
      exact congrArg (fun y : M ↦ BalancedExtension.tmul p 1 (toRestrictScalars p M y))
        (one_smul A (ofRestrictScalars p M m)))

private theorem subsingleton_balancedExtension_restrict_of_orth {E A B : Type u}
    [Ring E] [Ring A] [Ring B] (p : E →+* A) (p' : E →+* B) (e : E)
    (hp : p e = 1) (hp' : p' e = 0) (N : ModuleCat.{u} B) :
    Subsingleton (BalancedExtension p ((ModuleCat.restrictScalars.{u} p').obj N)) := by
  let Y := (ModuleCat.restrictScalars.{u} p').obj N
  have hzero : ∀ z : BalancedExtension p Y, z = 0 := fun z ↦ by
    induction z using BalancedExtension.induction_on with
    | tmul a n =>
      have h := BalancedExtension.tmul_smul (f := p) (P := Y) a e n
      have hsmul : e • n = 0 := ofRestrictScalars_injective p' N <|
        (ModuleCat.restrictScalars.smul_def p' e n).trans
          ((congrArg (· • ofRestrictScalars p' N n) hp').trans (zero_smul B _))
      rw [hp, mul_one, hsmul, BalancedExtension.tmul_zero] at h
      exact h.symm
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

private def splitBalancedLift {E A : Type u} [Ring E] [Ring A] (p : E →+* A) (j : A →+ E)
    (hmul_right : ∀ a e, j a * e = j (a * p e)) (P : Type u) [AddCommGroup P] [Module E P] :
    BalancedExtension p P →+ P :=
  (BalancedTensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a x ↦ j ((BalancedExtension.Scalars.of p).symm a) • x)
      (fun a₁ a₂ x ↦ by rw [map_add, map_add, add_smul])
      (fun z a x ↦ by rw [map_zsmul, map_zsmul, smul_assoc])
      (fun _ _ _ ↦ smul_add _ _ _)
      (fun _ _ _ ↦ smul_comm _ _ _))
    fun e a x ↦ by
      obtain ⟨a, rfl⟩ := (BalancedExtension.Scalars.of p).surjective a
      simp only [LinearMap.mk₂_apply, BalancedExtension.Scalars.op_smul_of,
        AddEquiv.symm_apply_apply, ← mul_smul, hmul_right]).toAddMonoidHom

@[simp]
private theorem splitBalancedLift_tmul {E A : Type u} [Ring E] [Ring A] (p : E →+* A)
    (j : A →+ E) (hmul_right : ∀ a e, j a * e = j (a * p e)) (P : Type u) [AddCommGroup P]
    [Module E P] (a : A) (x : P) :
    splitBalancedLift p j hmul_right P (BalancedExtension.tmul p a x) = j a • x := by
  rw [splitBalancedLift, BalancedExtension.tmul_def, LinearMap.toAddMonoidHom_coe,
    BalancedTensorProduct.lift_tmul]
  simp

private theorem tmul_splitBalancedLift_self {E A : Type u} [Ring E] [Ring A] (p : E →+* A)
    (j : A →+ E) (hpj : ∀ a, p (j a) = a) (hmul_right : ∀ a e, j a * e = j (a * p e))
    (P : Type u) [AddCommGroup P] [Module E P] (q : BalancedExtension p P) :
    BalancedExtension.tmul p 1 (splitBalancedLift p j hmul_right P q) = q := by
  induction q using BalancedExtension.induction_on with
  | tmul a x => rw [splitBalancedLift_tmul, BalancedExtension.tmul_smul, one_mul, hpj]
  | add x y hx hy => rw [map_add, BalancedExtension.tmul_add, hx, hy]

private theorem tmul_splitBalancedLift_orth {E A B : Type u} [Ring E] [Ring A] [Ring B]
    (p : E →+* A) (p' : E →+* B) (j : A →+ E) (horth : ∀ a, p' (j a) = 0)
    (hmul_right : ∀ a e, j a * e = j (a * p e))
    (P : Type u) [AddCommGroup P] [Module E P] (q : BalancedExtension p P) :
    BalancedExtension.tmul p' 1 (splitBalancedLift p j hmul_right P q) = 0 := by
  induction q using BalancedExtension.induction_on with
  | tmul a x =>
    rw [splitBalancedLift_tmul, BalancedExtension.tmul_smul, one_mul, horth,
      BalancedExtension.zero_tmul]
  | add x y hx hy => rw [map_add, BalancedExtension.tmul_add, hx, hy, add_zero]

private theorem ofRestrictScalars_semilinearMap_includeRight {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (P : ModuleCat.{u} R) (p : P) :
    ofRestrictScalars f (ModuleCat.of S (BalancedExtension f P))
      ((ModuleCat.semilinearMapAddEquiv f P (ModuleCat.of S (BalancedExtension f P))
        (BalancedExtension.includeRight f P)).hom p) =
      BalancedExtension.tmul f 1 p :=
  BalancedExtension.includeRight_apply p

private theorem mul_inl_prod (R S : Type u) [Ring R] [Ring S] (x : R × S) (r : R) :
    x * AddMonoidHom.inl R S r = AddMonoidHom.inl R S (RingHom.fst R S x * r) :=
  Prod.ext rfl (mul_zero x.2)

private theorem inl_mul_prod (R S : Type u) [Ring R] [Ring S] (r : R) (x : R × S) :
    AddMonoidHom.inl R S r * x = AddMonoidHom.inl R S (r * RingHom.fst R S x) :=
  Prod.ext rfl (zero_mul x.2)

private theorem mul_inr_prod (R S : Type u) [Ring R] [Ring S] (x : R × S) (s : S) :
    x * AddMonoidHom.inr R S s = AddMonoidHom.inr R S (RingHom.snd R S x * s) :=
  Prod.ext (mul_zero x.1) rfl

private theorem inr_mul_prod (R S : Type u) [Ring R] [Ring S] (s : S) (x : R × S) :
    AddMonoidHom.inr R S s * x = AddMonoidHom.inr R S (s * RingHom.snd R S x) :=
  Prod.ext (zero_mul x.1) rfl

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
  let l₁ := splitBalancedLift (RingHom.fst R S) (AddMonoidHom.inl R S) (inl_mul_prod R S) P
  let l₂ := splitBalancedLift (RingHom.snd R S) (AddMonoidHom.inr R S) (inr_mul_prod R S) P
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := φ.map_smul
    invFun q := l₁ (ofRestrictScalars (RingHom.fst R S) M₁ q.1) +
      l₂ (ofRestrictScalars (RingHom.snd R S) M₂ q.2)
    left_inv p := by
      have hsum : ((1, (0 : S)) : R × S) + (0, 1) = 1 := Prod.ext (add_zero 1) (zero_add 1)
      change l₁ (ofRestrictScalars (RingHom.fst R S) M₁ (u₁ p)) +
          l₂ (ofRestrictScalars (RingHom.snd R S) M₂ (u₂ p)) = p
      rw [ofRestrictScalars_semilinearMap_includeRight,
        ofRestrictScalars_semilinearMap_includeRight,
        splitBalancedLift_tmul, splitBalancedLift_tmul]
      exact (add_smul ((1, (0 : S)) : R × S) (0, 1) p).symm.trans
        ((congrArg (· • p) hsum).trans (one_smul (R × S) p))
    right_inv := fun ⟨q₁, q₂⟩ ↦ by
      let q₁' : BalancedExtension (RingHom.fst R S) P := ofRestrictScalars (RingHom.fst R S) M₁ q₁
      let q₂' : BalancedExtension (RingHom.snd R S) P := ofRestrictScalars (RingHom.snd R S) M₂ q₂
      refine Prod.ext (ofRestrictScalars_injective (RingHom.fst R S) M₁ ?_)
        (ofRestrictScalars_injective (RingHom.snd R S) M₂ ?_)
      · exact (ofRestrictScalars_semilinearMap_includeRight (RingHom.fst R S) P _).trans
          ((BalancedExtension.tmul_add 1 _ _).trans
            ((congrArg₂ (· + ·)
              (tmul_splitBalancedLift_self _ _ (fun _ ↦ rfl) _ P q₁')
              (tmul_splitBalancedLift_orth _ _ _ (fun _ ↦ rfl) _ P q₂')).trans (add_zero q₁')))
      · exact (ofRestrictScalars_semilinearMap_includeRight (RingHom.snd R S) P _).trans
          ((BalancedExtension.tmul_add 1 _ _).trans
            ((congrArg₂ (· + ·)
              (tmul_splitBalancedLift_orth _ _ _ (fun _ ↦ rfl) _ P q₁')
              (tmul_splitBalancedLift_self _ _ (fun _ ↦ rfl) _ P q₂')).trans (zero_add q₂'))) }

private theorem of_extendScalars_splitRestrict_orth_eq_zero {E A B : Type u}
    [Ring E] [Ring A] [Ring B] (p : E →+* A) (p' : E →+* B) (j : B →+ E)
    (hp'j : ∀ b, p' (j b) = b) (hmul_left : ∀ x b, x * j b = j (p' x * b))
    (e : E) (hp : p e = 1) (hp' : p' e = 0)
    (N : (finiteProjectiveModules B).FullSubcategory) :
    SplitK0.of.{u}
        (p.finiteProjectiveModulesExtendScalars.obj
          ((splitRestrictFunctor p' j hp'j hmul_left).obj N)) = 0 := by
  let Z : ModuleCat.{u} A :=
    ModuleCat.of A (BalancedExtension p ((ModuleCat.restrictScalars.{u} p').obj N.obj))
  have : Subsingleton Z :=
    subsingleton_balancedExtension_restrict_of_orth p p' e hp hp' N.obj
  exact SplitK0.of_eq_zero_of_isZero <| IsZero.of_full_of_faithful_of_isZero
    (finiteProjectiveModules A).ι _ <| (ModuleCat.isZero_of_subsingleton Z).of_iso
      (eqToIso (p.finiteProjectiveModulesExtendScalars_obj_obj _))

private noncomputable def prodInlFunctor (R S : Type u) [Ring R] [Ring S] :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (R × S)).FullSubcategory :=
  splitRestrictFunctor (RingHom.fst R S) (AddMonoidHom.inl R S) (fun _ ↦ rfl) (mul_inl_prod R S)

private instance (R S : Type u) [Ring R] [Ring S] : (prodInlFunctor R S).Additive :=
  additive_splitRestrictFunctor _ _ _ _

private noncomputable def prodInrFunctor (R S : Type u) [Ring R] [Ring S] :
    (finiteProjectiveModules S).FullSubcategory ⥤
      (finiteProjectiveModules (R × S)).FullSubcategory :=
  splitRestrictFunctor (RingHom.snd R S) (AddMonoidHom.inr R S) (fun _ ↦ rfl) (mul_inr_prod R S)

private instance (R S : Type u) [Ring R] [Ring S] : (prodInrFunctor R S).Additive :=
  additive_splitRestrictFunctor _ _ _ _

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
      exact SplitK0.of_extendScalars_obj
        (balancedExtensionRestrictSelfEquiv (RingHom.fst R S) (AddMonoidHom.inl R S)
          (fun _ ↦ rfl) M.obj))
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      exact of_extendScalars_splitRestrict_orth_eq_zero (RingHom.fst R S) (RingHom.snd R S)
        (AddMonoidHom.inr R S) (fun _ ↦ rfl) (mul_inr_prod R S) (1, 0) rfl rfl N)
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      exact of_extendScalars_splitRestrict_orth_eq_zero (RingHom.snd R S) (RingHom.fst R S)
        (AddMonoidHom.inl R S) (fun _ ↦ rfl) (mul_inl_prod R S) (0, 1) rfl rfl M)
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj
        (balancedExtensionRestrictSelfEquiv (RingHom.snd R S) (AddMonoidHom.inr R S)
          (fun _ ↦ rfl) N.obj))

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
    have := hfree P; have := hfree Q
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
    (AddMonoidHom.ext_int <| by simp [finrankSplitK0Invariant])

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

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of (D : Type u) [DivisionRing D]
    (P : (finiteProjectiveModules D).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D (SplitK0.of.{u} P) =
      (Module.finrank D P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of D _ P

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_symm_apply (D : Type u)
    [DivisionRing D] (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj D) :=
  (rfl)

/-- Over a nontrivial principal left-ideal ring without zero divisors, `Module.finrank` induces
`K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivPID (R : Type u) [Ring R]
    [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun P ↦
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (LinearMap.id : P.obj →ₗ[R] P.obj) Function.injective_id

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivPID_of (R : Type u) [Ring R]
    [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivPID R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of R _ P

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivPID_symm_apply (R : Type u) [Ring R]
    [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R] (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivPID R).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  (rfl)

/-- Over a commutative local ring `R`, `Module.finrank` induces `K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun _ ↦
    Module.free_of_projective_of_isLocalRing

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of (R : Type u) [CommRing R]
    [IsLocalRing R] (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivLocalRing R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of R _ P

@[simp]
theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_symm_apply (R : Type u) [CommRing R]
    [IsLocalRing R] (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivLocalRing R).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) :=
  (rfl)

end Finrank

end TauCeti
