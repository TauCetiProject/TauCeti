/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Computing Ext from injective resolutions

Mathlib's `CategoryTheory.InjectiveResolution.extMk` sends a cocycle `f : X ⟶ Iⁿ` of an injective
resolution `I` of `Y` to its class in `Extⁿ(X, Y)`, and
`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff` says that this class vanishes exactly when
`f` is a coboundary, in every positive degree `n = p + 1`. In degree zero there are no
coboundaries, so the class of a degree-zero cocycle vanishes only when the cocycle itself does
(`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff_eq_zero`). Together the two statements
identify `Extⁿ(X, Y)` with the cohomology of the complex `Hom(X, I)` in every degree.

`homologyLinearCoyonedaEquiv` packages this identification as a linear equivalence on
native homology. It sends the homology class of a cocycle to Mathlib's `extMk` class.
The equivalence commutes with morphisms of resolutions and with precomposition in the
first argument. It gives `CategoryTheory.rightDerivedLinearCoyonedaIsoExt`, the
identification of derived covariant Hom with derived-category Ext, natural in both arguments.
-/

public section

universe w v u

open CategoryTheory Limits CochainComplex HomComplex Abelian

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y)

/-- The class of a degree-zero cocycle `f : X ⟶ I⁰` of an injective resolution in `Ext⁰` vanishes
only if `f` is zero. This is the degree-zero counterpart of
`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff`. -/
lemma extMk_eq_zero_iff_eq_zero (f : X ⟶ R.cocomplex.X 0) (m : ℕ) (hm : 0 + 1 = m)
    (hf : f ≫ R.cocomplex.d 0 m = 0) :
    R.extMk f m hm hf = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; simp⟩
  rw [← R.extEquivCohomologyClass.apply_eq_iff_eq, extEquivCohomologyClass_extMk,
    extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff,
    Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by lia)] at h
  obtain ⟨g, hg⟩ := h
  -- the resolution has no term in degree `-1`
  obtain rfl : g = 0 := (R.cochainComplex.isZero_of_isStrictlyGE 0 (-1)).eq_of_tgt _ _
  rw [zero_comp] at hg
  exact (cancel_mono (R.cochainComplexXIso 0 0 rfl).inv).1 (hg.symm.trans zero_comp.symm)

/-- The complex obtained by applying the linear covariant Hom functor to an injective
resolution. -/
abbrev linearCoyonedaComplex (k : Type*) [Ring k] [Linear k C] (X : C) :=
  (((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex _).obj R.cocomplex

variable {k : Type*} [Ring k] [Linear k C]

/-- The Ext class of a cocycle in the covariant Hom complex of an injective resolution. -/
private noncomputable def linearCoyonedaCycleExt (n : ℕ) :
    LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom →ₗ[k] Ext.{w} X Y n where
  toFun z := R.extMk z.val (n + 1) rfl z.property
  map_add' z z' := (R.add_extMk z.val z'.val (n + 1) rfl z.property z'.property).symm
  map_smul' c z := (R.smul_extMk c z.val (n + 1) rfl z.property).symm

private lemma linearCoyonedaCycleExt_apply (n : ℕ)
    (z : LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom) :
    R.linearCoyonedaCycleExt n z = R.extMk z.val (n + 1) rfl z.property :=
  (rfl)

/-- Every Ext class is represented by a cocycle of the linear covariant Hom complex. -/
private lemma linearCoyonedaCycleExt_surjective (n : ℕ) :
    Function.Surjective (R.linearCoyonedaCycleExt (k := k) (X := X) n) := by
  intro α
  obtain ⟨f, hf, hα⟩ := R.extMk_surjective α (n + 1) rfl
  exact ⟨⟨f, hf⟩, hα⟩

/-- The Ext class and the native homology class of a Hom cocycle vanish together. -/
private lemma linearCoyonedaCycleExt_eq_zero_iff (n : ℕ)
    (z : LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom) :
    R.linearCoyonedaCycleExt n z = 0 ↔
      (R.linearCoyonedaComplex k X).moduleCatKerHomologyClass
        (n := n) (m := n + 1) (by simp) z = 0 := by
  rw [HomologicalComplex.moduleCatKerHomologyClass_eq_moduleCatHomologyClass,
    linearCoyonedaCycleExt_apply,
    (R.linearCoyonedaComplex k X).moduleCatHomologyClass_eq_zero_iff
      (by simp) (Submodule.subtype _) (fun z ↦ z.property) rfl z]
  cases n with
  | zero =>
    have h := R.extMk_eq_zero_iff_eq_zero z.val 1 rfl z.property
    rw [CochainComplex.prev_nat_zero]
    rw [(R.linearCoyonedaComplex k X).shape 0 0 (by simp)]
    refine h.trans ?_
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, Submodule.subtype_apply]
    exact eq_comm
  | succ n =>
    rw [CochainComplex.prev_nat_succ]
    exact R.extMk_eq_zero_iff z.val (n + 1 + 1) rfl z.property n rfl

/-- The cohomology of `Hom(X, I)` for an injective resolution `I` of `Y` is `Extⁿ(X,Y)`,
linearly over any ring making the category linear. -/
noncomputable def homologyLinearCoyonedaEquiv (n : ℕ) :
    (R.linearCoyonedaComplex k X).homology n ≃ₗ[k] Ext.{w} X Y n :=
  LinearMap.equivOfSurjectiveOfKerEq
    ((R.linearCoyonedaComplex k X).moduleCatKerHomologyClass (n := n) (m := n + 1) (by simp))
    (R.linearCoyonedaCycleExt (k := k) (X := X) n)
    (by
      rw [HomologicalComplex.moduleCatKerHomologyClass_eq_moduleCatHomologyClass]
      exact (R.linearCoyonedaComplex k X).moduleCatHomologyClass_surjective
        (by simp) (Submodule.subtype _) (fun z ↦ z.property) (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩))
    (R.linearCoyonedaCycleExt_surjective n)
    (by
      ext z
      exact (R.linearCoyonedaCycleExt_eq_zero_iff n z).symm)

/-- The equivalence is characterized by sending a cocycle's homology class to `extMk`. -/
-- Rewrite before mapping a complex simplifies the type of the cocycle.
@[simp↓]
lemma homologyLinearCoyonedaEquiv_moduleCatKerHomologyClass (n : ℕ)
    (z : LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom) :
    R.homologyLinearCoyonedaEquiv n
        ((R.linearCoyonedaComplex k X).moduleCatKerHomologyClass
          (n := n) (m := n + 1) (by simp) z) =
      R.extMk z.val (n + 1) rfl z.property :=
  (LinearMap.equivOfSurjectiveOfKerEq_apply _ _ _ _ _ z).trans
    (linearCoyonedaCycleExt_apply R n z)

/-- Computing Ext by injective resolutions commutes with a morphism of resolutions. -/
lemma homologyLinearCoyonedaEquiv_naturality {Y' : C} (R' : InjectiveResolution Y')
    {g : Y ⟶ Y'} (φ : Hom R R' g) (n : ℕ)
    (x : (R.linearCoyonedaComplex k X).homology n) :
    R'.homologyLinearCoyonedaEquiv n
        (HomologicalComplex.homologyMap
          ((((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex _).map φ.hom) n x) =
      (R.homologyLinearCoyonedaEquiv n x).comp (Ext.mk₀ g) (add_zero n) := by
  obtain ⟨y, rfl⟩ := (R.linearCoyonedaComplex k X).moduleCat_homologyπ_surjective n x
  rw [← (R.linearCoyonedaComplex k X).moduleCatKerHomologyClass_moduleCatCyclesToKer
    (m := n + 1) (by simp) y]
  let z := (R.linearCoyonedaComplex k X).moduleCatCyclesToKer n (n + 1) y
  rw [HomologicalComplex.homologyMap_moduleCatKerHomologyClass,
    homologyLinearCoyonedaEquiv_moduleCatKerHomologyClass,
    homologyLinearCoyonedaEquiv_moduleCatKerHomologyClass]
  exact (R.extMk_comp_mk₀ z.val (n + 1) rfl z.property φ).symm

/-- Computing Ext by an injective resolution commutes with precomposition in its first
argument. -/
lemma homologyLinearCoyonedaEquiv_naturality_left {X' : C} (g : X' ⟶ X) (n : ℕ)
    (x : (R.linearCoyonedaComplex k X).homology n) :
    R.homologyLinearCoyonedaEquiv n
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((linearCoyoneda k C).map g.op) _).app
            R.cocomplex) n x) =
      (Ext.mk₀ g).comp (R.homologyLinearCoyonedaEquiv n x) (zero_add n) := by
  obtain ⟨y, rfl⟩ := (R.linearCoyonedaComplex k X).moduleCat_homologyπ_surjective n x
  rw [← (R.linearCoyonedaComplex k X).moduleCatKerHomologyClass_moduleCatCyclesToKer
    (m := n + 1) (by simp) y]
  let z := (R.linearCoyonedaComplex k X).moduleCatCyclesToKer n (n + 1) y
  rw [HomologicalComplex.homologyMap_moduleCatKerHomologyClass,
    homologyLinearCoyonedaEquiv_moduleCatKerHomologyClass,
    homologyLinearCoyonedaEquiv_moduleCatKerHomologyClass]
  exact (R.mk₀_comp_extMk z.val (n + 1) rfl z.property g).symm

/-- In degree zero, the augmentation morphism `Y ⟶ I⁰` of an injective resolution represents
the identity class `Ext.mk₀ (𝟙 Y)` in `Ext⁰(Y, Y)`. -/
lemma extMk_ι_f_zero :
    R.extMk (R.ι.f 0) 1 rfl (by simp) = Ext.mk₀ (𝟙 Y) := by
  have := HasDerivedCategory.standard C
  have hc : Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk (R.ι.f 0 ≫ (R.cochainComplexXIso (0 : ℕ) 0 rfl).inv)
        (zero_add ((0 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) (by lia)
        (by simp [R.cochainComplex_d 0 1 0 1 rfl rfl])) =
      ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp) R.ι' := by
    refine Cocycle.equivHomShift.injective ?_
    rw [AddEquiv.apply_symm_apply]
    refine Cocycle.ext (Cochain.ext _ _ fun p q hpq ↦ ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 0 := by simpa using hpq.symm
      simp [Cocycle.equivHomShift_apply, ShiftedHom.mk₀, shiftFunctorZero',
        Cochain.rightUnshift_v _ 0 _ _ _ _ _ rfl, InjectiveResolution.ι'_f_zero,
        CochainComplex.shiftFunctorZero_inv_app_f]
    · rw [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v_eq_zero _ _ _ _ _ hp]
      exact ((HomologicalComplex.isZero_single_obj_X _ 0 Y p hp).eq_of_src _ _).symm
  ext
  rw [R.extMk_hom, hc, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀,
    IsIso.hom_inv_id_assoc, ShiftedHom.mk₀_comp_mk₀]
  erw [Iso.hom_inv_id_app]
  simp [Ext.mk₀_hom]

/-- In degree zero, the cocycle `f ≫ I.ι.f 0` of an injective resolution represents `Ext.mk₀ f`. -/
lemma extMk_comp_ι_f_zero (f : X ⟶ Y) :
    R.extMk (f ≫ R.ι.f 0) 1 rfl (by simp) = Ext.mk₀ f := by
  rw [← R.mk₀_comp_extMk _ 1 rfl (by simp) f, R.extMk_ι_f_zero, Ext.mk₀_comp_mk₀,
    Category.comp_id]

end CategoryTheory.InjectiveResolution

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  [EnoughInjectives C] (k : Type*) [CommRing k] [Linear k C] (X : C)

/-- Right deriving the linear covariant Hom functor computes the derived-category Ext
functor, naturally in the second argument. -/
noncomputable def rightDerivedLinearCoyonedaIsoExt (n : ℕ) :
    ((linearCoyoneda k C).obj (Opposite.op X)).rightDerived n ≅
      (linearExtFunctor k C n).obj (Opposite.op X) :=
  NatIso.ofComponents (fun Y ↦
    (injectiveResolution Y).isoRightDerivedObj _ n ≪≫
      ((injectiveResolution Y).homologyLinearCoyonedaEquiv (k := k) (X := X) n).toModuleIso)
    fun {Y Y'} g ↦ by
      let φ := InjectiveResolution.desc g (injectiveResolution Y') (injectiveResolution Y)
      -- Rebundle the linear equivalences as module morphisms: rewriting the composite
      -- isomorphisms directly fails because their intermediate homology objects are
      -- presented as both native objects and ModuleCat.of of their underlying modules.
      change (((linearCoyoneda k C).obj (Opposite.op X)).rightDerived n).map g ≫
          ((injectiveResolution Y').isoRightDerivedObj _ n).hom ≫
          ModuleCat.ofHom ((injectiveResolution Y').homologyLinearCoyonedaEquiv
            (k := k) (X := X) n).toLinearMap =
        ((injectiveResolution Y).isoRightDerivedObj _ n).hom ≫
          ModuleCat.ofHom ((injectiveResolution Y).homologyLinearCoyonedaEquiv
            (k := k) (X := X) n).toLinearMap ≫
          ((linearExtFunctor k C n).obj (Opposite.op X)).map g
      calc
        _ = ((injectiveResolution Y).isoRightDerivedObj _ n).hom ≫
            ((((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex _ ⋙
              HomologicalComplex.homologyFunctor _ _ n).map φ) ≫
            ModuleCat.ofHom ((injectiveResolution Y').homologyLinearCoyonedaEquiv
              (k := k) (X := X) n).toLinearMap :=
          InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc g
            (injectiveResolution Y) (injectiveResolution Y') φ
            (InjectiveResolution.desc_commutes_zero g _ _) _ n _
        _ = _ := by
          congr 1
          ext x
          exact (injectiveResolution Y).homologyLinearCoyonedaEquiv_naturality
            (injectiveResolution Y')
            ⟨φ, by simp [φ]⟩ n x

/-- On each coefficient object the derived Hom comparison is computed by its chosen
injective resolution and the cocycle-to-Ext equivalence. -/
@[simp]
lemma rightDerivedLinearCoyonedaIsoExt_hom_app (n : ℕ) (Y : C) :
    (rightDerivedLinearCoyonedaIsoExt k X n).hom.app Y =
      ((injectiveResolution Y).isoRightDerivedObj _ n).hom ≫
        ModuleCat.ofHom ((injectiveResolution Y).homologyLinearCoyonedaEquiv
          (k := k) (X := X) n).toLinearMap :=
  (rfl)

/-- In degree zero, `rightDerivedLinearCoyonedaIsoExt` identifies the canonical map
`Hom(X, Y) ⟶ R⁰Hom(X, -)(Y)` with the inverse of `Ext.linearEquiv₀`. -/
@[reassoc]
lemma toRightDerivedZero_app_comp_rightDerivedLinearCoyonedaIsoExt_hom_app (Y : C) :
    ((linearCoyoneda k C).obj (Opposite.op X)).toRightDerivedZero.app Y ≫
        (rightDerivedLinearCoyonedaIsoExt k X 0).hom.app Y =
      ModuleCat.ofHom (Ext.linearEquiv₀ (R := k)).symm.toLinearMap := by
  rw [rightDerivedLinearCoyonedaIsoExt_hom_app,
    (injectiveResolution Y).toRightDerivedZero_eq ((linearCoyoneda k C).obj (Opposite.op X))]
  ext f
  let f₀ : X ⟶ Y := f
  let e := (injectiveResolution Y).isoRightDerivedObj
    ((linearCoyoneda k C).obj (Opposite.op X)) 0
  change (injectiveResolution Y).homologyLinearCoyonedaEquiv (k := k) (X := X) 0
      (e.hom (e.inv (((injectiveResolution Y).toRightDerivedZero'
        ((linearCoyoneda k C).obj (Opposite.op X)) ≫
        (CochainComplex.isoHomologyπ₀ _).hom) f))) = _
  -- `erw` identifies `homologyFunctor.obj` with native homology in the domain of `e.hom`.
  erw [Iso.inv_hom_id_apply]
  have hcyc : (((injectiveResolution Y).linearCoyonedaComplex k X).moduleCatCyclesToKer 0 1
      ((injectiveResolution Y).toRightDerivedZero' ((linearCoyoneda k C).obj (Opposite.op X))
        f)).val =
      f₀ ≫ (injectiveResolution Y).ι.f 0 := by
    rw [HomologicalComplex.coe_moduleCatCyclesToKer]
    erw [← ModuleCat.comp_apply, InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    rfl
  have hker : ((((injectiveResolution Y).linearCoyonedaComplex k X).d 0 1).hom)
      (f₀ ≫ (injectiveResolution Y).ι.f 0) = 0 := by
    change (f₀ ≫ (injectiveResolution Y).ι.f 0) ≫ (injectiveResolution Y).cocomplex.d 0 1 = 0
    rw [Category.assoc, (injectiveResolution Y).ι.comm 0 1]
    simp
  have hz : ((injectiveResolution Y).toRightDerivedZero'
        ((linearCoyoneda k C).obj (Opposite.op X)) ≫
      (CochainComplex.isoHomologyπ₀ _).hom) f =
      ((injectiveResolution Y).linearCoyonedaComplex k X).moduleCatKerHomologyClass
        (n := 0) (m := 1) (by simp) ⟨f₀ ≫ (injectiveResolution Y).ι.f 0, hker⟩ := by
    let K := (injectiveResolution Y).linearCoyonedaComplex k X
    erw [ModuleCat.comp_apply,
      ← K.moduleCatKerHomologyClass_moduleCatCyclesToKer (m := 1) (by simp)]
    exact congrArg _ (Subtype.ext hcyc)
  refine (congrArg ((injectiveResolution Y).homologyLinearCoyonedaEquiv (k := k) (X := X) 0)
    hz).trans ?_
  rw [InjectiveResolution.homologyLinearCoyonedaEquiv_moduleCatKerHomologyClass]
  exact (injectiveResolution Y).extMk_comp_ι_f_zero f₀

/-- The derived Hom-to-Ext comparison is natural in the contravariant Hom argument. -/
@[reassoc]
lemma rightDerivedLinearCoyonedaIsoExt_hom_naturality_left {X' : C} (g : X' ⟶ X) (n : ℕ) :
    ((linearCoyoneda k C).map g.op).rightDerived n ≫
        (rightDerivedLinearCoyonedaIsoExt k X' n).hom =
      (rightDerivedLinearCoyonedaIsoExt k X n).hom ≫
        (linearExtFunctor k C n).map g.op := by
  apply NatTrans.ext
  funext Y
  rw [NatTrans.comp_app, NatTrans.comp_app,
    (injectiveResolution Y).rightDerived_app_eq,
    rightDerivedLinearCoyonedaIsoExt_hom_app,
    rightDerivedLinearCoyonedaIsoExt_hom_app]
  ext x
  -- Normalize the bundled homology modules to the domains of the linear equivalences;
  -- these occur both as native homology objects and as `ModuleCat.of` their carriers.
  let e := (injectiveResolution Y).isoRightDerivedObj
    ((linearCoyoneda k C).obj (Opposite.op X')) n
  change (injectiveResolution Y).homologyLinearCoyonedaEquiv n
      (e.hom (e.inv (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((linearCoyoneda k C).map g.op) _).app
          (injectiveResolution Y).cocomplex) n
        (((injectiveResolution Y).isoRightDerivedObj
          ((linearCoyoneda k C).obj (Opposite.op X)) n).hom x)))) = _
  -- `erw` identifies `homologyFunctor.obj` with native homology in the argument of
  -- `homologyMap`; plain `rw` cannot typecheck that argument at reducible transparency.
  erw [Iso.inv_hom_id_apply]
  exact (injectiveResolution Y).homologyLinearCoyonedaEquiv_naturality_left g n _

end CategoryTheory
