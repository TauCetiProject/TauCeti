/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.CategoryTheory.Abelian.Injective.Ext
import Mathlib.LinearAlgebra.Isomorphisms
import TauCeti.Algebra.Homology.Opposite

/-!
# Computing Ext from projective resolutions and balancing left and right derived Hom

Mathlib's `CategoryTheory.ProjectiveResolution.extMk` sends a cocycle `f : Pₙ ⟶ Y` of a projective
resolution `P` of `X` to its class in `CategoryTheory.Abelian.Ext X Y n`, and
`CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff` characterizes coboundaries in positive
degrees `n = p + 1`. In degree zero there are no incoming differentials in the Hom complex, so the
class of a degree-zero cocycle vanishes only when the morphism itself vanishes
(`CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff_eq_zero`). Together these statements
identify `Abelian.Ext X Y n` with the cohomology of `P.complex.linearYonedaObj k Y` in every
degree (`CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv`), compatibly with chain maps
of projective resolutions and postcomposition in the second variable.

Combining this equivalence with `CategoryTheory.ProjectiveResolution.isoExt` identifies Mathlib's
left-derived functor `_root_.Ext k C n` with the derived-category bifunctor
`CategoryTheory.Abelian.linearExtFunctor k C n` naturally in both arguments
(`CategoryTheory.extIsoLinearExtFunctor`). When `C` has both enough projectives and enough
injectives, composing with `CategoryTheory.rightDerivedLinearCoyonedaIsoExt` balances left-derived
contravariant `Hom` and right-derived covariant `Hom`
(`CategoryTheory.extObjIsoRightDerivedLinearCoyoneda`).

## Main definitions

* `CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv`: the `k`-linear equivalence
  `(P.complex.linearYonedaObj k Y).homology n ≃ₗ[k] Abelian.Ext X Y n`.
* `CategoryTheory.extObjIsoLinearExtFunctor` and `CategoryTheory.extIsoLinearExtFunctor`: the
  natural isomorphism `_root_.Ext k C n ≅ Abelian.linearExtFunctor k C n`.
* `CategoryTheory.extObjIsoRightDerivedLinearCoyoneda`: the natural balance isomorphism
  `(_root_.Ext k C n).obj (op X) ≅ ((linearCoyoneda k C).obj (op X)).rightDerived n`.

## Main results

* `CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff_eq_zero`: a degree-zero cocycle of a
  projective resolution represents `0` in `Ext⁰` if and only if it is zero.
* `CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv_naturality` and
  `CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv_naturality_right`: compatibility
  with morphisms of projective resolutions and postcomposition in the target.
* `CategoryTheory.extObjIsoLinearExtFunctor_hom_naturality_left` and
  `CategoryTheory.extObjIsoRightDerivedLinearCoyoneda_hom_naturality_left`: naturality in the
  contravariant variable.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced Mathematics
  38, Cambridge University Press, 1994, Theorem 2.7.6 (balancing `Ext`) and Section 10.7.
-/

public section

universe w v u

open CategoryTheory Limits CochainComplex HomComplex Abelian Opposite

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (P : ProjectiveResolution X)

/-- The class of a degree-zero cocycle `f : P₀ ⟶ Y` of a projective resolution in `Ext⁰` vanishes
if and only if `f = 0`. This is the degree-zero counterpart of
`CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff`. -/
lemma extMk_eq_zero_iff_eq_zero (f : P.complex.X 0 ⟶ Y) (m : ℕ) (hm : 0 + 1 = m)
    (hf : P.complex.d m 0 ≫ f = 0) :
    P.extMk f m hm hf = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; simp⟩
  rw [← P.extEquivCohomologyClass.apply_eq_iff_eq, extEquivCohomologyClass_extMk,
    extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff,
    Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by lia)] at h
  obtain ⟨g, hg⟩ := h
  -- The cochain complex of a projective resolution is concentrated in nonpositive degrees.
  obtain rfl : g = 0 := (P.cochainComplex.isZero_of_isStrictlyLE 0 1).eq_of_src _ _
  rw [comp_zero] at hg
  exact (cancel_epi (P.cochainComplexXIso (-0) 0 rfl).hom).1 (hg.symm.trans comp_zero.symm)

variable {k : Type*} [Ring k] [Linear k C]

/-- The `Ext` class of a cocycle in the contravariant `Hom` complex of a projective resolution. -/
private noncomputable def linearYonedaCycleExt (n : ℕ) :
    LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom →ₗ[k] Ext.{w} X Y n where
  toFun z := P.extMk z.val (n + 1) rfl z.property
  map_add' z z' := (P.add_extMk z.val z'.val (n + 1) rfl z.property z'.property).symm
  map_smul' c z := (P.smul_extMk c z.val (n + 1) rfl z.property).symm

private lemma linearYonedaCycleExt_apply (n : ℕ)
    (z : LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom) :
    P.linearYonedaCycleExt n z = P.extMk z.val (n + 1) rfl z.property :=
  (rfl)

/-- Every `Ext` class is represented by a cocycle of the contravariant `Hom` complex. -/
private lemma linearYonedaCycleExt_surjective (n : ℕ) :
    Function.Surjective (P.linearYonedaCycleExt (k := k) (Y := Y) n) := by
  intro α
  obtain ⟨f, hf, hα⟩ := P.extMk_surjective α (n + 1) rfl
  exact ⟨⟨f, hf⟩, hα⟩

/-- The `Ext` class and the native homology class of a contravariant `Hom` cocycle vanish
together. -/
private lemma linearYonedaCycleExt_eq_zero_iff (n : ℕ)
    (z : LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom) :
    P.linearYonedaCycleExt n z = 0 ↔
      (P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass
        (n := n) (m := n + 1) (by simp) z = 0 := by
  rw [HomologicalComplex.moduleCatKerHomologyClass_eq_moduleCatHomologyClass,
    linearYonedaCycleExt_apply,
    (P.complex.linearYonedaObj k Y).moduleCatHomologyClass_eq_zero_iff
      (by simp) (Submodule.subtype _) (fun z ↦ z.property) rfl z]
  cases n with
  | zero =>
    have h := P.extMk_eq_zero_iff_eq_zero z.val 1 rfl z.property
    rw [CochainComplex.prev_nat_zero, (P.complex.linearYonedaObj k Y).shape 0 0 (by simp)]
    refine h.trans ?_
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, Submodule.subtype_apply]
    exact eq_comm
  | succ n =>
    rw [CochainComplex.prev_nat_succ]
    exact P.extMk_eq_zero_iff z.val (n + 1 + 1) rfl z.property n rfl

/-- The cohomology of `Hom(P, Y)` for a projective resolution `P` of `X` is `Abelian.Ext X Y n`,
`k`-linearly over any ring `k` making `C` linear. -/
noncomputable def homologyLinearYonedaEquiv (n : ℕ) :
    (P.complex.linearYonedaObj k Y).homology n ≃ₗ[k] Ext.{w} X Y n := by
  let a := (P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass
    (n := n) (m := n + 1) (by simp)
  let b := P.linearYonedaCycleExt (k := k) (Y := Y) n
  have ha : Function.Surjective a := by
    dsimp only [a]
    rw [HomologicalComplex.moduleCatKerHomologyClass_eq_moduleCatHomologyClass]
    exact (P.complex.linearYonedaObj k Y).moduleCatHomologyClass_surjective
      (by simp) (Submodule.subtype _) (fun z ↦ z.property) (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)
  have hab : LinearMap.ker a = LinearMap.ker b := by
    ext z
    exact (P.linearYonedaCycleExt_eq_zero_iff n z).symm
  exact (a.quotKerEquivOfSurjective ha).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hab ≪≫ₗ
      b.quotKerEquivOfSurjective (P.linearYonedaCycleExt_surjective n)

/-- `homologyLinearYonedaEquiv` sends the homology class of a cocycle to `extMk`. -/
@[simp↓]
lemma homologyLinearYonedaEquiv_moduleCatKerHomologyClass (n : ℕ)
    (z : LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom) :
    P.homologyLinearYonedaEquiv n
        ((P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass
          (n := n) (m := n + 1) (by simp) z) =
      P.extMk z.val (n + 1) rfl z.property := by
  dsimp only [homologyLinearYonedaEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  simp only [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact linearYonedaCycleExt_apply P n z

/-- `ProjectiveResolution.extMk` depends only on the underlying cocycle morphism. -/
private lemma extMk_congr {n : ℕ} {f f' : P.complex.X n ⟶ Y} (h : f = f') (m : ℕ)
    (hm : n + 1 = m) (hf : P.complex.d m n ≫ f = 0) :
    P.extMk f m hm hf = P.extMk f' m hm (h ▸ hf) := by
  subst h
  rfl

/-- Computing `Ext` from projective resolutions commutes with morphisms of resolutions. -/
lemma homologyLinearYonedaEquiv_naturality {X' : C} (P' : ProjectiveResolution X')
    {g : X' ⟶ X} (φ : Hom P' P g) (n : ℕ)
    (x : (P.complex.linearYonedaObj k Y).homology n) :
    P'.homologyLinearYonedaEquiv n
        (HomologicalComplex.homologyMap
          (K := P.complex.linearYonedaObj k Y) (L := P'.complex.linearYonedaObj k Y)
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.hom.op) n x) =
      (Ext.mk₀ g).comp (P.homologyLinearYonedaEquiv n x) (zero_add n) := by
  obtain ⟨y, rfl⟩ := (P.complex.linearYonedaObj k Y).moduleCat_homologyπ_surjective n x
  let z := (P.complex.linearYonedaObj k Y).moduleCatCyclesToKer n (n + 1) y
  have hz := ((P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass_moduleCatCyclesToKer
    (m := n + 1) (by simp) y).symm
  have hmap := HomologicalComplex.homologyMap_moduleCatKerHomologyClass (m := n + 1) (by simp)
    ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.hom.op) z
  refine (congrArg (P'.homologyLinearYonedaEquiv n) ((congrArg _ hz).trans hmap)).trans
    ((P'.homologyLinearYonedaEquiv_moduleCatKerHomologyClass n _).trans ?_)
  rw [hz, homologyLinearYonedaEquiv_moduleCatKerHomologyClass]
  exact (mk₀_comp_extMk z.val (n + 1) rfl z.property φ).symm

/-- Computing `Ext` from a projective resolution commutes with postcomposition in its second
argument. -/
lemma homologyLinearYonedaEquiv_naturality_right {Y' : C} (g : Y ⟶ Y') (n : ℕ)
    (x : (P.complex.linearYonedaObj k Y).homology n) :
    P.homologyLinearYonedaEquiv n
        (HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k g) n x) =
      (P.homologyLinearYonedaEquiv n x).comp (Ext.mk₀ g) (add_zero n) := by
  obtain ⟨y, rfl⟩ := (P.complex.linearYonedaObj k Y).moduleCat_homologyπ_surjective n x
  rw [← (P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass_moduleCatCyclesToKer
    (m := n + 1) (by simp) y]
  let z := (P.complex.linearYonedaObj k Y).moduleCatCyclesToKer n (n + 1) y
  rw [HomologicalComplex.homologyMap_moduleCatKerHomologyClass,
    homologyLinearYonedaEquiv_moduleCatKerHomologyClass,
    homologyLinearYonedaEquiv_moduleCatKerHomologyClass]
  exact (P.extMk_congr (P.complex.linearYonedaObjMap_f_hom_apply k g n z.val) (n + 1) rfl _).trans
    (P.extMk_comp_mk₀ z.val (n + 1) rfl z.property g).symm

section IsoExtNaturality

omit [HasExt.{w} C]
variable [EnoughProjectives C]

/-- `ProjectiveResolution.isoExt` is natural with respect to chain maps lifting morphisms in the
first variable. -/
@[reassoc]
lemma isoExt_hom_naturality_left {X' : C} (P' : ProjectiveResolution X') (f : X' ⟶ X)
    (φ : P'.complex ⟶ P.complex) (comm : φ.f 0 ≫ P.π.f 0 = P'.π.f 0 ≫ f) (n : ℕ) (Y : C) :
    ((_root_.Ext k C n).map f.op).app Y ≫ (P'.isoExt n Y).hom =
      (P.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
        (K := P.complex.linearYonedaObj k Y) (L := P'.complex.linearYonedaObj k Y)
        ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) n := by
  have hL := congrArg Quiver.Hom.unop (ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    f P' P φ comm ((linearYoneda k C).obj Y).rightOp n)
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).map φ) n
  -- `isoExt` is the unopposed inverse of `isoLeftDerivedObj` followed by `(homologyUnop _ n).inv`;
  -- composing the two squares in term mode avoids unfolding native homology to its short-complex
  -- presentation.
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hL).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn).trans (Category.assoc _ _ _).symm)))

/-- `ProjectiveResolution.isoExt` is natural with respect to morphisms in the second variable. -/
@[reassoc]
lemma isoExt_hom_naturality_right {Y' : C} (g : Y ⟶ Y') (n : ℕ) :
    ((_root_.Ext k C n).obj (op X)).map g ≫ (P.isoExt n Y').hom =
      (P.isoExt n Y).hom ≫
        HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k g) n := by
  let α := ((linearYoneda k C).map g).rightOp
  have hmap : P.complex.linearYonedaObjMap k g =
      (HomologicalComplex.unopFunctor _ _).map
        ((NatTrans.mapHomologicalComplex α _).app P.complex).op := by
    ext i (a : P.complex.X i ⟶ Y)
    exact P.complex.linearYonedaObjMap_f_hom_apply k g i a
  have hL := congrArg Quiver.Hom.unop (P.leftDerived_app_eq α n)
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((NatTrans.mapHomologicalComplex α _).app P.complex) n
  have hcancel : (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).hom.unop ≫
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop = 𝟙 _ := by
    rw [← unop_comp, Iso.inv_hom_id, unop_id]
  -- Cancel the inverse and forward components of `isoLeftDerivedObj` at `Y'` in term mode.
  have hmid :
      ((P.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop ≫
        ((NatTrans.mapHomologicalComplex α _).app P.complex |>
          (HomologicalComplex.homologyFunctor _ _ n).map).unop ≫
        (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).hom.unop) ≫
        (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop =
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α _).app P.complex) n).unop := by
    simp only [Category.assoc, hcancel, Category.comp_id]
    rfl
  rw [hmap]
  exact ((congrArg (· ≫ (P.isoExt n Y').hom) hL).trans (Category.assoc _ _ _).symm).trans
    (((congrArg (· ≫ _) hmid).trans (Category.assoc _ _ _)).trans
      ((congrArg (_ ≫ ·) hn).trans (Category.assoc _ _ _).symm))

end IsoExtNaturality

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  (k : Type*) [CommRing k] [Linear k C]

/-- `ProjectiveResolution.homologyLinearYonedaEquiv` packaged as an isomorphism in `ModuleCat k`. -/
noncomputable def ProjectiveResolution.homologyLinearYonedaIso {X Y : C}
    (P : ProjectiveResolution X) (n : ℕ) :
    (P.complex.linearYonedaObj k Y).homology n ≅
      ((Abelian.linearExtFunctor k C n).obj (op X)).obj Y :=
  (P.homologyLinearYonedaEquiv (k := k) (Y := Y) n).toModuleIso

@[simp↓]
lemma ProjectiveResolution.homologyLinearYonedaIso_hom_apply {X Y : C}
    (P : ProjectiveResolution X) (n : ℕ)
    (x : (P.complex.linearYonedaObj k Y).homology n) :
    (P.homologyLinearYonedaIso k n).hom x = P.homologyLinearYonedaEquiv n x :=
  (rfl)

variable [EnoughProjectives C]

/-- Left deriving the contravariant `Hom` functor computes `Abelian.linearExtFunctor`, naturally
in the second argument. -/
noncomputable def extObjIsoLinearExtFunctor (X : C) (n : ℕ) :
    (_root_.Ext k C n).obj (op X) ≅ (Abelian.linearExtFunctor k C n).obj (op X) :=
  NatIso.ofComponents
    (fun Y ↦ (projectiveResolution X).isoExt n Y ≪≫
      (projectiveResolution X).homologyLinearYonedaIso k (Y := Y) n)
    fun {Y Y'} g ↦ by
      simp only [Iso.trans_hom]
      rw [(projectiveResolution X).isoExt_hom_naturality_right_assoc g n, Category.assoc]
      congr 1
      ext x
      exact (projectiveResolution X).homologyLinearYonedaEquiv_naturality_right g n x

/-- On each target object `Y`, `extObjIsoLinearExtFunctor` is computed from the chosen projective
resolution of `X` and `homologyLinearYonedaIso`. -/
@[simp]
lemma extObjIsoLinearExtFunctor_hom_app (X : C) (n : ℕ) (Y : C) :
    (extObjIsoLinearExtFunctor k X n).hom.app Y =
      ((projectiveResolution X).isoExt n Y).hom ≫
        ((projectiveResolution X).homologyLinearYonedaIso k (Y := Y) n).hom :=
  (rfl)

/-- `extObjIsoLinearExtFunctor` is natural in the contravariant first argument. -/
@[reassoc]
lemma extObjIsoLinearExtFunctor_hom_naturality_left {X X' : C} (f : X' ⟶ X) (n : ℕ) :
    (_root_.Ext k C n).map f.op ≫ (extObjIsoLinearExtFunctor k X' n).hom =
      (extObjIsoLinearExtFunctor k X n).hom ≫ (Abelian.linearExtFunctor k C n).map f.op := by
  let φ := ProjectiveResolution.lift f (projectiveResolution X') (projectiveResolution X)
  have hcomm : φ.f 0 ≫ (projectiveResolution X).π.f 0 =
      (projectiveResolution X').π.f 0 ≫ f :=
    ProjectiveResolution.lift_commutes_zero f
      (projectiveResolution X') (projectiveResolution X)
  apply NatTrans.ext
  funext Y
  simp only [NatTrans.comp_app, extObjIsoLinearExtFunctor_hom_app]
  rw [(projectiveResolution X).isoExt_hom_naturality_left_assoc
    (projectiveResolution X') f φ hcomm n Y, Category.assoc]
  congr 1
  ext x
  exact (projectiveResolution X).homologyLinearYonedaEquiv_naturality (projectiveResolution X')
    ⟨φ, congr($(ProjectiveResolution.lift_commutes f
      (projectiveResolution X') (projectiveResolution X)).f 0)⟩ n x

/-- Mathlib's left-derived `_root_.Ext k C n` is naturally isomorphic as a bifunctor to the
derived-category functor `Abelian.linearExtFunctor k C n`. -/
noncomputable def extIsoLinearExtFunctor (n : ℕ) :
    _root_.Ext k C n ≅ Abelian.linearExtFunctor k C n :=
  NatIso.ofComponents (fun X ↦ extObjIsoLinearExtFunctor k X.unop n)
    fun f ↦ extObjIsoLinearExtFunctor_hom_naturality_left k f.unop n

@[simp]
lemma extIsoLinearExtFunctor_hom_app (n : ℕ) (X : Cᵒᵖ) :
    (extIsoLinearExtFunctor k n).hom.app X = (extObjIsoLinearExtFunctor k X.unop n).hom :=
  (rfl)

@[simp]
lemma extIsoLinearExtFunctor_inv_app (n : ℕ) (X : Cᵒᵖ) :
    (extIsoLinearExtFunctor k n).inv.app X = (extObjIsoLinearExtFunctor k X.unop n).inv :=
  (rfl)

section Balance

variable [EnoughInjectives C]

/-- **Balancing `Ext`.** In a `k`-linear abelian category with enough projectives and enough
injectives, left-derived contravariant `Hom` and right-derived covariant `Hom` are naturally
isomorphic in the second variable. -/
noncomputable def extObjIsoRightDerivedLinearCoyoneda (X : C) (n : ℕ) :
    (_root_.Ext k C n).obj (op X) ≅ ((linearCoyoneda k C).obj (op X)).rightDerived n :=
  extObjIsoLinearExtFunctor k X n ≪≫ (rightDerivedLinearCoyonedaIsoExt k X n).symm

/-- The balance isomorphism `extObjIsoRightDerivedLinearCoyoneda` is natural in the first
variable. -/
@[reassoc]
lemma extObjIsoRightDerivedLinearCoyoneda_hom_naturality_left {X X' : C} (f : X' ⟶ X) (n : ℕ) :
    (_root_.Ext k C n).map f.op ≫ (extObjIsoRightDerivedLinearCoyoneda k X' n).hom =
      (extObjIsoRightDerivedLinearCoyoneda k X n).hom ≫
        ((linearCoyoneda k C).map f.op).rightDerived n := by
  rw [← cancel_mono (rightDerivedLinearCoyonedaIsoExt k X' n).hom]
  dsimp only [extObjIsoRightDerivedLinearCoyoneda, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    extObjIsoLinearExtFunctor_hom_naturality_left, Category.assoc,
    rightDerivedLinearCoyonedaIsoExt_hom_naturality_left, Category.assoc, Iso.inv_hom_id_assoc]

end Balance

end CategoryTheory
