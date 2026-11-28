/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution
public import TauCeti.CategoryTheory.Abelian.Ext

/-!
# Comparing the left derived and derived-category `Ext` functors

Mathlib has two constructions of `Ext` in an abelian category `C` with enough projectives. The
functor `Ext k C n : Cᵒᵖ ⥤ C ⥤ ModuleCat k` of `Mathlib.CategoryTheory.Abelian.Ext` is the left
derived functor of `Hom(-, Y)`, computed from a projective resolution `P` of `X` as the
cohomology of the complex `Hom(P, Y)` (`CategoryTheory.ProjectiveResolution.isoExt`). The groups
`CategoryTheory.Abelian.Ext X Y n` are morphisms in the derived category, assembled into the
bifunctor `CategoryTheory.Abelian.linearExtFunctor k C n`. Mathlib's module `localCohomology` is
built from the first construction, while depth (`Ideal.depth`) and most of the homological algebra
of modules use the second.

This file provides two levels of comparison between the two constructions:

1. **Bifunctor isomorphism.** Combining `CategoryTheory.ProjectiveResolution.isoExt` with
   `CategoryTheory.ProjectiveResolution.homologyLinearYonedaIso` gives natural isomorphisms
   `CategoryTheory.extObjIsoLinearExtFunctor` and `CategoryTheory.extIsoLinearExtFunctor`
   identifying `_root_.Ext k C n` with `CategoryTheory.Abelian.linearExtFunctor k C n`.
2. **Vanishing equivalence.** Both constructions vanish together, because both vanish exactly when
   `Hom(P, Y)` is exact in degree `n`. In degree `n + 1` this says that every cocycle `f : Pₙ₊₁ ⟶ Y`
   is a coboundary; in degree `0` it says that every morphism `P₀ ⟶ Y` killed by `P₁ ⟶ P₀` is
   zero (`ChainComplex.exactAt_linearYonedaObj_zero_iff` and
   `ChainComplex.exactAt_linearYonedaObj_succ_iff`).

## Main definitions

* `CategoryTheory.extObjIsoLinearExtFunctor` and `CategoryTheory.extIsoLinearExtFunctor`: the
  natural isomorphism `_root_.Ext k C n ≅ CategoryTheory.Abelian.linearExtFunctor k C n`.

## Main results

* `CategoryTheory.extObjIsoLinearExtFunctor_hom_naturality_left`: naturality of the objectwise
  comparison in the contravariant first argument.
* `CategoryTheory.ProjectiveResolution.subsingleton_ext_iff_exactAt`: `Ext X Y n` vanishes if and
  only if `Hom(P, Y)` is exact in degree `n`.
* `CategoryTheory.ProjectiveResolution.isZero_Ext_iff_exactAt`: the same for the left derived
  functor `Ext k C n`.
* `CategoryTheory.Abelian.Ext.subsingleton_iff_isZero_Ext`: the two constructions of `Ext` vanish
  together.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5 (`Ext` via projective
  resolutions) and Section 10.7 (`Ext` as morphisms in the derived category).
-/

public section

universe w v u t

open CategoryTheory Limits

namespace CategoryTheory.ProjectiveResolution

open Abelian

section HasExt

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (P : ProjectiveResolution X)

/-- `Ext⁰(X, Y) = Hom(X, Y)` vanishes exactly when every morphism `P₀ ⟶ Y` killed by the
differential `P₁ ⟶ P₀` of a projective resolution `P` of `X` is zero. -/
theorem subsingleton_ext_zero_iff :
    Subsingleton (Ext.{w} X Y 0) ↔ ∀ f : P.complex.X 0 ⟶ Y, P.complex.d 1 0 ≫ f = 0 → f = 0 := by
  rw [Ext.homEquiv₀.subsingleton_congr]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X
  refine ⟨fun _ f hf ↦ ?_, fun h ↦ ⟨fun g g' ↦ ?_⟩⟩
  · -- `X` is the cokernel of `P₁ ⟶ P₀`, so `f` factors through `X`.
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork f hf
    rw [← hl, ← e.hom_inv_id_assoc l, Subsingleton.elim (e.inv ≫ l) 0]
    simp
  · refine sub_eq_zero.1 ((cancel_epi (P.π.f 0 ≫ e.hom)).1 ?_)
    rw [comp_zero]
    exact h _ (by simp only [Category.assoc, P.complex_d_comp_π_f_zero_assoc, zero_comp])

/-- `Extⁿ⁺¹(X, Y)` vanishes exactly when, for a projective resolution `P` of `X`, every cocycle
`Pₙ₊₁ ⟶ Y` of the complex `Hom(P, Y)` is a coboundary. -/
theorem subsingleton_ext_succ_iff (n : ℕ) :
    Subsingleton (Ext.{w} X Y (n + 1)) ↔
      ∀ f : P.complex.X (n + 1) ⟶ Y, P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  refine ⟨fun _ f hf ↦ ?_, fun h ↦ subsingleton_of_forall_eq 0 fun α ↦ ?_⟩
  · exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).1 (Subsingleton.elim _ _)
  · obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).2 (h f hf)

variable (k : Type t) [Ring k] [Linear k C]

/-- `Ext X Y n` vanishes exactly when the complex `Hom(P, Y)` is exact in degree `n`, for any
projective resolution `P` of `X`. -/
theorem subsingleton_ext_iff_exactAt (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) ↔ (P.complex.linearYonedaObj k Y).ExactAt n := by
  cases n with
  | zero => rw [subsingleton_ext_zero_iff P, ChainComplex.exactAt_linearYonedaObj_zero_iff]
  | succ n => rw [subsingleton_ext_succ_iff P, ChainComplex.exactAt_linearYonedaObj_succ_iff]

open CochainComplex HomComplex in
/-- In degree zero, the augmentation morphism `P₀ ⟶ X` of a projective resolution represents
the identity class `Ext.mk₀ (𝟙 X)` in `Ext⁰(X, X)`. -/
lemma extMk_π_f_zero (P : ProjectiveResolution X) :
    P.extMk (P.π.f 0) 1 rfl (by simp) = Ext.mk₀ (𝟙 X) := by
  have := HasDerivedCategory.standard C
  have hc : Cocycle.equivHomShift.symm
      (Cocycle.toSingleMk ((P.cochainComplexXIso (-((0 : ℕ) : ℤ)) 0 rfl).hom ≫ P.π.f 0)
        (by simp) (-((1 : ℕ) : ℤ)) (by lia) (by
          rw [P.cochainComplex_d (-((1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) 1 0 (by simp) rfl]
          simp)) =
      ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp) P.π' := by
    refine Cocycle.equivHomShift.injective ?_
    rw [AddEquiv.apply_symm_apply]
    refine Cocycle.ext (Cochain.ext _ _ fun p q hpq ↦ ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 0 := by simpa using hpq.symm
      simp [Cocycle.equivHomShift_apply, ShiftedHom.mk₀, shiftFunctorZero',
        Cochain.rightUnshift_v _ 0 _ _ _ _ _ rfl, ProjectiveResolution.π'_f_zero,
        CochainComplex.shiftFunctorZero_inv_app_f]
    · obtain rfl : p = q := by simpa using hpq
      rw [Cocycle.toSingleMk_coe, Cochain.toSingleMk_v_eq_zero _ _ p p hpq (by simpa using hp)]
      exact ((HomologicalComplex.isZero_single_obj_X _ 0 X p hp).eq_of_tgt _ _).symm
  ext
  rw [P.extMk_hom, hc, ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀,
    ShiftedHom.mk₀_comp_mk₀, Category.assoc, IsIso.inv_hom_id_assoc]
  erw [Iso.hom_inv_id_app]
  simp [Ext.mk₀_hom]

/-- In degree zero, the cocycle `P.π.f 0 ≫ f` of a projective resolution represents
`Ext.mk₀ f`. -/
lemma extMk_π_f_zero_comp (P : ProjectiveResolution X) (f : X ⟶ Y) :
    P.extMk (P.π.f 0 ≫ f) 1 rfl (by simp) = Ext.mk₀ f := by
  rw [← P.extMk_comp_mk₀ (P.π.f 0) 1 rfl (by simp) f, P.extMk_π_f_zero, Ext.mk₀_comp_mk₀,
    Category.id_comp]

end HasExt

/-- The left derived functor `Ext k C n` vanishes on `(X, Y)` exactly when the complex
`Hom(P, Y)` is exact in degree `n`, for any projective resolution `P` of `X`. -/
theorem isZero_Ext_iff_exactAt {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}
    (P : ProjectiveResolution X) (k : Type t) [Ring k] [Linear k C] [EnoughProjectives C] (n : ℕ) :
    IsZero (((_root_.Ext k C n).obj (Opposite.op X)).obj Y) ↔
      (P.complex.linearYonedaObj k Y).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h ↦ h.of_iso (P.isoExt n Y).symm, fun h ↦ h.of_iso (P.isoExt n Y)⟩

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughProjectives C]
  (k : Type t) [Ring k] [Linear k C]

/-- The derived-category `Ext X Y n` vanishes if and only if the left derived functor
`Ext k C n` vanishes on `(X, Y)`. -/
theorem subsingleton_iff_isZero_Ext (X Y : C) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) ↔ IsZero (((_root_.Ext k C n).obj (Opposite.op X)).obj Y) := by
  rw [(projectiveResolution X).subsingleton_ext_iff_exactAt k,
    (projectiveResolution X).isZero_Ext_iff_exactAt k]

end CategoryTheory.Abelian.Ext

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  (k : Type*) [CommRing k] [Linear k C] [EnoughProjectives C]

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
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        ProjectiveResolution.homologyLinearYonedaIso_hom_apply]
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
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ProjectiveResolution.homologyLinearYonedaIso_hom_apply]
  exact (projectiveResolution X).homologyLinearYonedaEquiv_naturality (projectiveResolution X')
    ⟨φ, congr($(ProjectiveResolution.lift_commutes f
      (projectiveResolution X') (projectiveResolution X)).f 0)⟩ n x

/-- Mathlib's left-derived `_root_.Ext k C n` is naturally isomorphic as a bifunctor to the
derived-category functor `Abelian.linearExtFunctor k C n`. -/
noncomputable def extIsoLinearExtFunctor (n : ℕ) :
    _root_.Ext k C n ≅ Abelian.linearExtFunctor k C n :=
  NatIso.ofComponents (fun X ↦ extObjIsoLinearExtFunctor k X.unop n)
    fun f ↦ extObjIsoLinearExtFunctor_hom_naturality_left k f.unop n

/-- The forward component of `extIsoLinearExtFunctor` at `X` is `extObjIsoLinearExtFunctor`. -/
@[simp]
lemma extIsoLinearExtFunctor_hom_app (n : ℕ) (X : Cᵒᵖ) :
    (extIsoLinearExtFunctor k n).hom.app X = (extObjIsoLinearExtFunctor k X.unop n).hom :=
  (rfl)

/-- The inverse of `extObjIsoLinearExtFunctor` at `X` is the inverse of
`extObjIsoLinearExtFunctor`. -/
@[simp]
lemma extIsoLinearExtFunctor_inv_app (n : ℕ) (X : Cᵒᵖ) :
    (extIsoLinearExtFunctor k n).inv.app X = (extObjIsoLinearExtFunctor k X.unop n).inv :=
  (rfl)

private lemma shortComplex_op_homologyπ_comp_homologyOpIso_hom {V : Type*} [Category* V]
    [HasZeroMorphisms V] (S : ShortComplex V) [S.HasHomology] :
    S.op.homologyπ ≫ S.homologyOpIso.hom = S.cyclesOpIso.hom ≫ S.homologyι.op := by
  dsimp only [ShortComplex.homologyOpIso, Iso.trans_hom, Iso.symm_hom, Iso.op]
  rw [ShortComplex.homologyπ_comp_leftHomologyIso_inv_assoc]
  erw [ShortComplex.LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom_assoc
    S.rightHomologyData.op]
  change S.cyclesOpIso.hom ≫ S.rightHomologyι.op ≫ S.rightHomologyIso.inv.op = _
  rw [← op_comp]
  rfl

private lemma shortComplex_homologyOpIso_inv_comp_op_homologyι_comp_opcyclesOpIso_hom
    {V : Type*} [Category* V] [HasZeroMorphisms V] (S : ShortComplex V) [S.HasHomology] :
    S.homologyOpIso.inv ≫ S.op.homologyι ≫ S.opcyclesOpIso.hom = S.homologyπ.op := by
  rw [← cancel_epi (S.op.homologyπ ≫ S.homologyOpIso.hom)]
  calc
    (S.op.homologyπ ≫ S.homologyOpIso.hom) ≫
        S.homologyOpIso.inv ≫ S.op.homologyι ≫ S.opcyclesOpIso.hom
      = S.op.homologyπ ≫ S.op.homologyι ≫ S.opcyclesOpIso.hom := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = S.op.iCycles ≫ S.op.pOpcycles ≫ S.opcyclesOpIso.hom := by
          rw [ShortComplex.homology_π_ι_assoc]
    _ = S.op.iCycles ≫ S.iCycles.op := by
          rw [ShortComplex.op_pOpcycles_opcyclesOpIso_hom]
    _ = S.cyclesOpIso.hom ≫ S.pOpcycles.op ≫ S.iCycles.op := by
          rw [← ShortComplex.cyclesOpIso_inv_op_iCycles, ← Category.assoc,
            Iso.hom_inv_id_assoc]
    _ = (S.op.homologyπ ≫ S.homologyOpIso.hom) ≫ S.homologyπ.op := by
          rw [← op_comp, ← ShortComplex.homology_π_ι, op_comp, ← Category.assoc,
            ← shortComplex_op_homologyπ_comp_homologyOpIso_hom, Category.assoc]

/-- In degree zero, `extObjIsoLinearExtFunctor` identifies `extZeroIso.inv : Hom(X, Y) ⟶ Ext⁰(X, Y)`
with the inverse of `Abelian.Ext.linearEquiv₀`. -/
@[reassoc]
lemma extZeroIso_inv_comp_extObjIsoLinearExtFunctor_hom_app (X Y : C) :
    (extZeroIso (k := k) X Y).inv ≫ (extObjIsoLinearExtFunctor k X 0).hom.app Y =
      ModuleCat.ofHom (Abelian.Ext.linearEquiv₀ (R := k)).symm.toLinearMap := by
  let P := projectiveResolution X
  let F := ((linearYoneda k C).obj Y).rightOp
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let K := P.complex.linearYonedaObj k Y
  let S := K.sc 0
  have hL : (extZeroIso (k := k) X Y).inv ≫ (P.isoExt 0 Y).hom =
      (P.fromLeftDerivedZero' F).unop ≫ (S.opcyclesOpIso.inv).unop ≫ K.homologyπ 0 := by
    have hfrom := congrArg Quiver.Hom.unop (P.fromLeftDerivedZero_eq F)
    have hcomp : S.op.homologyι.unop ≫ S.homologyOpIso.inv.unop =
        S.opcyclesOpIso.inv.unop ≫ S.homologyπ := by
      have h := congrArg Quiver.Hom.unop
        (shortComplex_homologyOpIso_inv_comp_op_homologyι_comp_opcyclesOpIso_hom S)
      have h' : S.opcyclesOpIso.hom.unop ≫
          (S.op.homologyι.unop ≫ S.homologyOpIso.inv.unop) = S.homologyπ := by
        simpa only [unop_comp, Category.assoc, Quiver.Hom.unop_op] using h
      have hinv : S.opcyclesOpIso.inv.unop ≫ S.opcyclesOpIso.hom.unop = 𝟙 _ := by
        rw [← unop_comp, Iso.hom_inv_id, unop_id]
      rw [← h', ← Category.assoc, hinv, Category.id_comp]
    rw [extZeroIso_inv]
    dsimp only [ProjectiveResolution.isoExt, Iso.trans_hom, Iso.symm_hom]
    have h1 : (((linearYoneda k C).obj Y).rightOp.fromLeftDerivedZero.app X).unop =
        (P.fromLeftDerivedZero' F).unop ≫ (ChainComplex.isoHomologyι₀ L).hom.unop ≫
          (P.isoLeftDerivedObj F 0).hom.unop := by
      simpa only [unop_comp, Category.assoc] using hfrom
    have hcancel : (P.isoLeftDerivedObj F 0).hom.unop ≫
        (P.isoLeftDerivedObj F 0).inv.unop = 𝟙 _ := by
      rw [← unop_comp, Iso.inv_hom_id, unop_id]
    erw [h1, Category.assoc, Category.assoc, reassoc_of% hcancel]
    exact congrArg ((P.fromLeftDerivedZero' F).unop ≫ ·) hcomp
  rw [extObjIsoLinearExtFunctor_hom_app, ← Category.assoc, hL]
  ext f
  let f₀ : X ⟶ Y := f
  let y : K.cycles 0 := (S.opcyclesOpIso.inv).unop ((P.fromLeftDerivedZero' F).unop f)
  have hy_val : (K.moduleCatCyclesToKer 0 1 y).val = P.π.f 0 ≫ f₀ := by
    rw [HomologicalComplex.coe_moduleCatCyclesToKer]
    have h1 : (S.opcyclesOpIso.inv).unop ≫ K.iCycles 0 = (L.pOpcycles 0).unop := by
      have h := congrArg Quiver.Hom.unop (ShortComplex.op_pOpcycles_opcyclesOpIso_hom S)
      have h' : (S.opcyclesOpIso.inv).unop ≫ K.iCycles 0 =
          ((S.opcyclesOpIso.inv).unop ≫ (S.opcyclesOpIso.hom).unop) ≫
            (S.op.pOpcycles).unop := by
        change (S.opcyclesOpIso.inv).unop ≫ S.iCycles = _
        rw [Category.assoc, ← unop_comp]
        exact congrArg (S.opcyclesOpIso.inv.unop ≫ ·) h.symm
      have hcancel : S.opcyclesOpIso.inv.unop ≫ S.opcyclesOpIso.hom.unop = 𝟙 _ := by
        rw [← unop_comp, Iso.hom_inv_id, unop_id]
      rw [h']
      erw [hcancel, Category.id_comp]
      rfl
    have h2 : (P.fromLeftDerivedZero' F).unop ≫ (L.pOpcycles 0).unop =
        (F.map (P.π.f 0)).unop := by
      rw [← unop_comp, P.pOpcycles_comp_fromLeftDerivedZero' F]
    have h3 : (K.iCycles 0) y = ((F.map (P.π.f 0)).unop) f := by
      change ((P.fromLeftDerivedZero' F).unop ≫ (S.opcyclesOpIso.inv).unop ≫ K.iCycles 0) f = _
      erw [h1, h2]
      rfl
    exact h3
  have hker : ((K.d 0 1).hom) (P.π.f 0 ≫ f₀) = 0 := by
    change P.complex.d 1 0 ≫ P.π.f 0 ≫ f₀ = 0
    simp
  have hz : K.homologyπ 0 y =
      K.moduleCatKerHomologyClass (n := 0) (m := 1) (by simp) ⟨P.π.f 0 ≫ f₀, hker⟩ := by
    rw [← K.moduleCatKerHomologyClass_moduleCatCyclesToKer (m := 1) (by simp) y]
    exact congrArg _ (Subtype.ext hy_val)
  erw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ProjectiveResolution.homologyLinearYonedaIso_hom_apply]
  refine (congrArg (P.homologyLinearYonedaEquiv (k := k) (Y := Y) 0) hz).trans ?_
  rw [ProjectiveResolution.homologyLinearYonedaEquiv_moduleCatKerHomologyClass]
  exact P.extMk_π_f_zero_comp f₀

end CategoryTheory
