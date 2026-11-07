/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.ModuleCat.Basic
import Mathlib.LinearAlgebra.Isomorphisms

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
The equivalence commutes with morphisms of resolutions and gives
`CategoryTheory.rightDerivedLinearCoyonedaIsoExt`, the natural identification of
derived covariant Hom with derived-category Ext.
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
  toFun z := R.extMk z.1 (n + 1) rfl z.2
  map_add' z z' := (R.add_extMk z.1 z'.1 (n + 1) rfl z.2 z'.2).symm
  map_smul' c z := (R.smul_extMk c z.1 (n + 1) rfl z.2).symm

private lemma linearCoyonedaCycleExt_apply (n : ℕ)
    (z : LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom) :
    R.linearCoyonedaCycleExt n z = R.extMk z.1 (n + 1) rfl z.2 :=
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
      (R.linearCoyonedaComplex k X).moduleCatHomologyClass
        (n := n) (m := n + 1) (by simp) (Submodule.subtype _) (fun z ↦ z.2) z = 0 := by
  rw [linearCoyonedaCycleExt_apply,
    (R.linearCoyonedaComplex k X).moduleCatHomologyClass_eq_zero_iff
      (by simp) (Submodule.subtype _) (fun z ↦ z.2) rfl z]
  cases n with
  | zero =>
    have h := R.extMk_eq_zero_iff_eq_zero z.1 1 rfl z.2
    rw [CochainComplex.prev_nat_zero]
    rw [(R.linearCoyonedaComplex k X).shape 0 0 (by simp)]
    refine h.trans ?_
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, Submodule.subtype_apply]
    exact eq_comm
  | succ n =>
    rw [CochainComplex.prev_nat_succ]
    exact R.extMk_eq_zero_iff z.1 (n + 1 + 1) rfl z.2 n rfl

/-- The cohomology of `Hom(X, I)` for an injective resolution `I` of `Y` is `Extⁿ(X,Y)`,
linearly over any ring making the category linear. -/
noncomputable def homologyLinearCoyonedaEquiv (n : ℕ) :
    (R.linearCoyonedaComplex k X).homology n ≃ₗ[k] Ext.{w} X Y n := by
  let a := (R.linearCoyonedaComplex k X).moduleCatHomologyClass
    (n := n) (m := n + 1) (by simp)
      (LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom).subtype (fun z ↦ z.2)
  let b := R.linearCoyonedaCycleExt (k := k) (X := X) n
  have ha : Function.Surjective a :=
    (R.linearCoyonedaComplex k X).moduleCatHomologyClass_surjective
      (by simp) (Submodule.subtype _) (fun z ↦ z.2) (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)
  have hab : LinearMap.ker a = LinearMap.ker b := by
    ext z
    exact (R.linearCoyonedaCycleExt_eq_zero_iff n z).symm
  exact (a.quotKerEquivOfSurjective ha).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hab ≪≫ₗ
      b.quotKerEquivOfSurjective (R.linearCoyonedaCycleExt_surjective n)

/-- The equivalence is characterized by sending a cocycle's homology class to `extMk`. -/
-- Rewrite before mapping a complex simplifies the type of the cocycle.
@[simp↓]
lemma homologyLinearCoyonedaEquiv_class (n : ℕ)
    (z : LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom) :
    R.homologyLinearCoyonedaEquiv n
        ((R.linearCoyonedaComplex k X).moduleCatHomologyClass
          (n := n) (m := n + 1) (by simp) (Submodule.subtype _) (fun z ↦ z.2) z) =
      R.extMk z.1 (n + 1) rfl z.2 := by
  dsimp only [homologyLinearCoyonedaEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  simp only [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact linearCoyonedaCycleExt_apply R n z

/-- Computing Ext by injective resolutions commutes with a morphism of resolutions. -/
lemma homologyLinearCoyonedaEquiv_naturality {Y' : C} (R' : InjectiveResolution Y')
    {g : Y ⟶ Y'} (φ : Hom R R' g) (n : ℕ)
    (x : (R.linearCoyonedaComplex k X).homology n) :
    R'.homologyLinearCoyonedaEquiv n
        (HomologicalComplex.homologyMap
          ((((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex _).map φ.hom) n x) =
      (R.homologyLinearCoyonedaEquiv n x).comp (Ext.mk₀ g) (add_zero n) := by
  obtain ⟨z, rfl⟩ := (R.linearCoyonedaComplex k X).moduleCatHomologyClass_surjective
    (n := n) (m := n + 1) (by simp)
    (LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom).subtype
    (fun z ↦ z.2) (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩) x
  let ψ : R.linearCoyonedaComplex k X ⟶ R'.linearCoyonedaComplex k X :=
    (((linearCoyoneda k C).obj (Opposite.op X)).mapHomologicalComplex _).map φ.hom
  let b := ((ψ.f n).hom.comp
    (LinearMap.ker ((R.linearCoyonedaComplex k X).d n (n + 1)).hom).subtype).codRestrict
      (LinearMap.ker ((R'.linearCoyonedaComplex k X).d n (n + 1)).hom) fun z ↦ by
        rw [LinearMap.mem_ker]
        have hz : (R.linearCoyonedaComplex k X).d n (n + 1) z.1 = 0 := z.2
        have h := ConcreteCategory.congr_hom (ψ.comm n (n + 1)) z.1
        simpa only [ModuleCat.comp_apply, hz, map_zero, LinearMap.comp_apply,
          Submodule.subtype_apply] using h
  rw [HomologicalComplex.homologyMap_moduleCatHomologyClass
    (K := R.linearCoyonedaComplex k X) (by simp) (Submodule.subtype _) (fun z ↦ z.2)
    ψ (Submodule.subtype _) (fun z ↦ z.2) b (fun _ ↦ rfl) z,
    homologyLinearCoyonedaEquiv_class, homologyLinearCoyonedaEquiv_class]
  exact (R.extMk_comp_mk₀ z.1 (n + 1) rfl z.2 φ).symm

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
      -- The linear equivalence rebundles native homology as a module object. Expose the
      -- composite morphisms to use the resolution comparison without unfolding homology.
      change (((linearCoyoneda k C).obj (Opposite.op X)).rightDerived n).map g ≫
          ((injectiveResolution Y').isoRightDerivedObj _ n).hom ≫
          ModuleCat.ofHom ((injectiveResolution Y').homologyLinearCoyonedaEquiv
            (k := k) (X := X) n).toLinearMap =
        ((injectiveResolution Y).isoRightDerivedObj _ n).hom ≫
          ModuleCat.ofHom ((injectiveResolution Y).homologyLinearCoyonedaEquiv
            (k := k) (X := X) n).toLinearMap ≫
          ((linearExtFunctor k C n).obj (Opposite.op X)).map g
      erw [← Category.assoc, InjectiveResolution.isoRightDerivedObj_hom_naturality g
        (injectiveResolution Y) (injectiveResolution Y') φ
        (InjectiveResolution.desc_commutes_zero g _ _) _ n, Category.assoc]
      congr 1
      ext x
      exact (injectiveResolution Y).homologyLinearCoyonedaEquiv_naturality
        (injectiveResolution Y')
        ⟨φ, by simpa using InjectiveResolution.desc_commutes_zero g _ _⟩ n x

/-- On each coefficient object the derived Hom comparison is computed by its chosen
injective resolution and the cocycle-to-Ext equivalence. -/
@[simp]
lemma rightDerivedLinearCoyonedaIsoExt_hom_app (n : ℕ) (Y : C) :
    (rightDerivedLinearCoyonedaIsoExt k X n).hom.app Y =
      ((injectiveResolution Y).isoRightDerivedObj _ n).hom ≫
        ModuleCat.ofHom ((injectiveResolution Y).homologyLinearCoyonedaEquiv
          (k := k) (X := X) n).toLinearMap :=
  (rfl)

end CategoryTheory
