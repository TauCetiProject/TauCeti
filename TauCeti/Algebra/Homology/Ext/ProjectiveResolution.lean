/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.Opposite
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Computing `Ext` from projective resolutions

Mathlib's `CategoryTheory.ProjectiveResolution.isoExt` computes `Extⁿ(X, Y)` from any projective
resolution `P` of `X`. When two resolutions of `X` are related by a chain map lying over
the identity of `X`, `isoExt_hom_comp_homologyMap` identifies the resulting computations; more
generally, `isoExt_hom_naturality_left` and `isoExt_hom_naturality_right` establish naturality of
`isoExt` in both variables.

Mathlib computes `Extⁿ(X, Y)` from a projective resolution `R` of `X` as the `n`-th cohomology of
the complex `Hom(R, Y)`: `CategoryTheory.ProjectiveResolution.extMk` builds a class from a cocycle,
`extMk_surjective` says every class arises that way, and `extMk_eq_zero_iff` identifies the
coboundaries in positive degrees. In degree zero there are no incoming differentials in the `Hom`
complex, so a degree-zero cocycle represents zero only when the morphism itself vanishes
(`CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff_eq_zero`). Together these statements
identify `Abelian.Ext X Y n` with the cohomology of `R.complex.linearYonedaObj k Y` in every degree
(`CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv` and
`CategoryTheory.ProjectiveResolution.homologyLinearYonedaIso`), compatibly with chain maps of
projective resolutions and postcomposition in the second variable.

This file also records the degenerate case of that computation. If the two differentials of `R`
adjacent to a degree `n + 1` die against `Y` -- that is, if `d (n + 2) (n + 1) ≫ f = 0` for every
`f : Rₙ₊₁ ⟶ Y` and `d (n + 1) n ≫ g = 0` for every `g : Rₙ ⟶ Y` -- then in that degree no cocycle
condition and no coboundary survives, and `Extⁿ⁺¹(X, Y)` *is* the term `Hom(Rₙ₊₁, Y)`, linearly
over the coefficient ring.

Degree `0` is deliberately excluded: there `Ext⁰(X, Y)` is `Hom(X, Y)`, which need not be
`Hom(R₀, Y)`.

At the other extreme, a resolution whose terms vanish from degree `n` on bounds the projective
dimension of `X` by `n`.

## Main definitions

* `CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv` and
  `CategoryTheory.ProjectiveResolution.homologyLinearYonedaIso`: the `k`-linear equivalence and
  `ModuleCat k`-isomorphism `(P.complex.linearYonedaObj k Y).homology n ≃ₗ[k] Abelian.Ext X Y n`.
* `CategoryTheory.ProjectiveResolution.extLinearEquiv`: the linear equivalence
  `Hom(Rₙ₊₁, Y) ≃ₗ Extⁿ⁺¹(X, Y)`, sending `f` to its class.

## Main results

* `CategoryTheory.ProjectiveResolution.isoExt_hom_comp_homologyMap`,
  `CategoryTheory.ProjectiveResolution.isoExt_hom_naturality_left`, and
  `CategoryTheory.ProjectiveResolution.isoExt_hom_naturality_right`: compatibility and naturality
  of `isoExt`.
* `CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff_eq_zero`: a degree-zero cocycle of a
  projective resolution represents `0` in `Ext⁰` if and only if it is zero.
* `CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv_naturality` and
  `CategoryTheory.ProjectiveResolution.homologyLinearYonedaEquiv_naturality_right`: compatibility
  with morphisms of projective resolutions and postcomposition in the target.
* `CategoryTheory.ProjectiveResolution.hasProjectiveDimensionLT`: a projective resolution whose
  terms vanish from degree `n` on gives `HasProjectiveDimensionLT X n`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.2 and 2.4, for independence of
  `Ext` from the resolution, and Section 2.5, for `Ext` computed from a projective resolution.
-/

public section

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Abelian

section Comparison

open Opposite

variable {R : Type*} [Ring R] {D : Type*} [Category* D] [Abelian D] [Linear R D]
  [EnoughProjectives D]

/-- Unfold Mathlib's `ProjectiveResolution.isoExt` as the unopposed inverse of
`isoLeftDerivedObj` followed by `(HomologicalComplex.homologyUnop _ n).inv`. -/
private lemma isoExt_hom_eq {X : D} (P : ProjectiveResolution X) (n : ℕ) (Y : D) :
    (P.isoExt (R := R) n Y).hom =
      (P.isoLeftDerivedObj ((linearYoneda R D).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyUnop _ n).inv :=
  rfl

/-- Lift a naturality square for `isoLeftDerivedObj` (unopposed) along `homologyUnop` to a
square for `ProjectiveResolution.isoExt`. -/
private lemma isoExt_hom_square {X₁ X₂ Y₁ Y₂ : D}
    (P₁ : ProjectiveResolution X₁) (P₂ : ProjectiveResolution X₂) (n : ℕ)
    (α : ((_root_.Ext R D n).obj (op X₁)).obj Y₁ ⟶ ((_root_.Ext R D n).obj (op X₂)).obj Y₂)
    (ψ : (((linearYoneda R D).obj Y₂).rightOp.mapHomologicalComplex _).obj P₂.complex ⟶
      (((linearYoneda R D).obj Y₁).rightOp.mapHomologicalComplex _).obj P₁.complex)
    {ψ' : (HomologicalComplex.unopFunctor _ _).obj (Opposite.op
        ((((linearYoneda R D).obj Y₁).rightOp.mapHomologicalComplex _).obj P₁.complex)) ⟶
      (HomologicalComplex.unopFunctor _ _).obj (Opposite.op
        ((((linearYoneda R D).obj Y₂).rightOp.mapHomologicalComplex _).obj P₂.complex))}
    (hψ : ψ' = (HomologicalComplex.unopFunctor _ _).map ψ.op)
    (hL : α ≫ (P₂.isoLeftDerivedObj ((linearYoneda R D).obj Y₂).rightOp n).inv.unop =
      (P₁.isoLeftDerivedObj ((linearYoneda R D).obj Y₁).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap ψ n).unop) :
    α ≫ (P₂.isoExt n Y₂).hom =
      (P₁.isoExt n Y₁).hom ≫ HomologicalComplex.homologyMap ψ' n := by
  subst hψ
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality ψ n
  have step1 : α ≫ (P₂.isoExt n Y₂).hom =
      (P₁.isoLeftDerivedObj ((linearYoneda R D).obj Y₁).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap ψ n).unop ≫
        (HomologicalComplex.homologyUnop _ n).inv :=
    (congrArg (α ≫ ·) (isoExt_hom_eq P₂ n Y₂)).trans
      ((Category.assoc _ _ _).symm.trans ((reassoc_of% hL) _))
  have step2 : (P₁.isoLeftDerivedObj ((linearYoneda R D).obj Y₁).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap ψ n).unop ≫
        (HomologicalComplex.homologyUnop _ n).inv =
      (P₁.isoExt n Y₁).hom ≫
        HomologicalComplex.homologyMap ((HomologicalComplex.unopFunctor _ _).map ψ.op) n := by
    rw [hn, isoExt_hom_eq P₁ n Y₁]
    exact (Category.assoc _ _ _).symm
  exact step1.trans step2

/-- **`Ext` computed from two resolutions related by a chain map.** If `φ : P ⟶ Q` is a chain map
between projective resolutions of `X` lying over the identity of `X`, then computing `Extⁿ(X, Y)`
from `Q` and precomposing with `φ` gives the computation from `P`. -/
theorem isoExt_hom_comp_homologyMap {X : D} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) (Y : D) :
    (Q.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ).op) n =
      (P.isoExt n Y).hom := by
  have h := isoLeftDerivedObj_hom_naturality (𝟙 X) P Q φ
    (comm.trans (Category.comp_id _).symm) ((linearYoneda R D).obj Y).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hP := congrArg Quiver.Hom.unop ((Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp _).2 h.symm))
  rw [unop_comp] at hP
  exact ((isoExt_hom_square Q P n (𝟙 _)
    ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ) rfl
    ((Category.id_comp _).trans hP.symm)).symm).trans (Category.id_comp _)

end Comparison

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C]

section SubsingletonHom

variable [HasExt.{w} C] {X Y : C}

/-- If the degree-`n` term of a projective resolution has no nonzero morphism to `Y`, then
`Extⁿ(X,Y)` vanishes. No condition on the neighboring terms is needed. -/
theorem subsingleton_ext_of_subsingleton_hom (R : ProjectiveResolution X) (n : ℕ)
    [Subsingleton (R.complex.X n ⟶ Y)] : Subsingleton (Ext.{w} X Y n) := by
  apply subsingleton_of_forall_eq 0
  intro α
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 1) rfl
  obtain rfl : f = 0 := Subsingleton.elim _ _
  simp

end SubsingletonHom

/-- A projective resolution of `X` whose terms vanish from degree `n` on shows that `X` has
projective dimension less than `n`. -/
theorem hasProjectiveDimensionLT {X : C} (R : ProjectiveResolution X) (n : ℕ)
    (h : ∀ i, n ≤ i → Limits.IsZero (R.complex.X i)) : HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  refine HasProjectiveDimensionLT.mk fun i hi Y e ↦ ?_
  have : Subsingleton (R.complex.X i ⟶ Y) := ⟨fun f g ↦ (h i hi).eq_of_src f g⟩
  have := R.subsingleton_ext_of_subsingleton_hom (Y := Y) i
  exact Subsingleton.elim _ _

section LinearEquiv

variable {k : Type t} [Ring k] [Linear k C] [HasExt.{w} C] {X Y : C}

/-- If the two differentials of a projective resolution `R` of `X` adjacent to degree `n + 1`
become zero after applying `Hom(-, Y)`, then `Extⁿ⁺¹(X, Y)` is the degree `n + 1` term of that
`Hom`-complex, `k`-linearly. The class of `f` is `CategoryTheory.ProjectiveResolution.extMk f`. -/
noncomputable def extLinearEquiv (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0) :
    (R.complex.X (n + 1) ⟶ Y) ≃ₗ[k] Ext.{w} X Y (n + 1) := by
  refine LinearEquiv.ofBijective
    { toFun := fun f => R.extMk f (n + 2) rfl (h₁ f)
      map_add' := fun f g => (R.add_extMk f g (n + 2) rfl (h₁ f) (h₁ g)).symm
      map_smul' := fun c f => ?_ } ⟨?_, ?_⟩
  · dsimp
    rw [Ext.smul_eq_comp_mk₀, R.extMk_comp_mk₀]
    congr 1
    rw [Linear.comp_smul, Category.comp_id]
  · rw [← LinearMap.ker_eq_bot]
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_bot, LinearMap.coe_mk, AddHom.coe_mk]
    rw [R.extMk_eq_zero_iff f (n + 2) rfl (h₁ f) n rfl]
    exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ h₂ g, fun hf ↦ ⟨0, by simp [hf]⟩⟩
  · intro α
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 2) rfl
    exact ⟨f, rfl⟩

@[simp]
theorem extLinearEquiv_apply (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0)
    (f : R.complex.X (n + 1) ⟶ Y) :
    extLinearEquiv (k := k) R n h₁ h₂ f = R.extMk f (n + 2) rfl (h₁ f) :=
  (rfl)

end LinearEquiv

section HomologyComparison

open Limits CochainComplex HomComplex Opposite

variable [HasExt.{w} C] {X Y : C} (P : ProjectiveResolution X)

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
  rw [(P.cochainComplex.isZero_of_isStrictlyLE 0 1).eq_of_src g 0, comp_zero] at hg
  exact (cancel_epi (P.cochainComplexXIso (-0) 0 rfl).hom).1 (hg.symm.trans comp_zero.symm)

variable {k : Type t} [Ring k] [Linear k C]

/-- The `Ext` class of a cocycle in the contravariant `Hom` complex of a projective resolution. -/
private noncomputable def linearYonedaCycleExt (n : ℕ) :
    LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom →ₗ[k] Ext.{w} X Y n where
  toFun z := P.extMk z.val (n + 1) rfl z.property
  map_add' z z' := (P.add_extMk z.val z'.val (n + 1) rfl z.property z'.property).symm
  map_smul' c z := (P.smul_extMk c z.val (n + 1) rfl z.property).symm

/-- Every `Ext` class is represented by a cocycle of the contravariant `Hom` complex. -/
private lemma linearYonedaCycleExt_surjective (n : ℕ) :
    Function.Surjective (P.linearYonedaCycleExt (k := k) (Y := Y) n) := fun α ↦
  let ⟨f, hf, hα⟩ := P.extMk_surjective α (n + 1) rfl; ⟨⟨f, hf⟩, hα⟩

/-- The `Ext` class and the native homology class of a contravariant `Hom` cocycle vanish
together. -/
private lemma linearYonedaCycleExt_eq_zero_iff (n : ℕ)
    (z : LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom) :
    P.linearYonedaCycleExt n z = 0 ↔
      (P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass
        (n := n) (m := n + 1) (by simp) z = 0 := by
  rw [HomologicalComplex.moduleCatKerHomologyClass_eq_moduleCatHomologyClass,
    (P.complex.linearYonedaObj k Y).moduleCatHomologyClass_eq_zero_iff
      (by simp) (Submodule.subtype _) (fun z ↦ z.property) rfl z]
  rcases n with _ | n
  · have h := P.extMk_eq_zero_iff_eq_zero z.val 1 rfl z.property
    rw [CochainComplex.prev_nat_zero, (P.complex.linearYonedaObj k Y).shape 0 0 (by simp)]
    refine h.trans ?_
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, Submodule.subtype_apply]
    exact eq_comm
  · rw [CochainComplex.prev_nat_succ]
    exact P.extMk_eq_zero_iff z.val (n + 1 + 1) rfl z.property n rfl

/-- The cohomology of `Hom(P, Y)` for a projective resolution `P` of `X` is `Abelian.Ext X Y n`,
`k`-linearly over any ring `k` making `C` linear. -/
noncomputable def homologyLinearYonedaEquiv (n : ℕ) :
    (P.complex.linearYonedaObj k Y).homology n ≃ₗ[k] Ext.{w} X Y n :=
  LinearMap.equivOfSurjectiveOfKerEq
    ((P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass (n := n) (m := n + 1) (by simp))
    (P.linearYonedaCycleExt (k := k) (Y := Y) n)
    (by
      rw [HomologicalComplex.moduleCatKerHomologyClass_eq_moduleCatHomologyClass]
      exact (P.complex.linearYonedaObj k Y).moduleCatHomologyClass_surjective
        (by simp) (Submodule.subtype _) (fun z ↦ z.property) (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩))
    (P.linearYonedaCycleExt_surjective n)
    (by ext z; exact (P.linearYonedaCycleExt_eq_zero_iff n z).symm)

/-- `homologyLinearYonedaEquiv` sends the homology class of a cocycle to `extMk`. -/
@[simp↓]
lemma homologyLinearYonedaEquiv_moduleCatKerHomologyClass (n : ℕ)
    (z : LinearMap.ker ((P.complex.linearYonedaObj k Y).d n (n + 1)).hom) :
    P.homologyLinearYonedaEquiv n
        ((P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass
          (n := n) (m := n + 1) (by simp) z) =
      P.extMk z.val (n + 1) rfl z.property :=
  LinearMap.equivOfSurjectiveOfKerEq_apply _ _ _ _ _ z

/-- `ProjectiveResolution.extMk` depends only on the underlying cocycle morphism. -/
private lemma extMk_congr {n : ℕ} {f f' : P.complex.X n ⟶ Y} (h : f = f') (m : ℕ)
    (hm : n + 1 = m) (hf : P.complex.d m n ≫ f = 0) :
    P.extMk f m hm hf = P.extMk f' m hm (h ▸ hf) := by
  subst h; rfl

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
  let z := (P.complex.linearYonedaObj k Y).moduleCatCyclesToKer n (n + 1) y
  rw [← (P.complex.linearYonedaObj k Y).moduleCatKerHomologyClass_moduleCatCyclesToKer
    (m := n + 1) (by simp) y, HomologicalComplex.homologyMap_moduleCatKerHomologyClass,
    homologyLinearYonedaEquiv_moduleCatKerHomologyClass,
    homologyLinearYonedaEquiv_moduleCatKerHomologyClass]
  exact (P.extMk_congr (P.complex.linearYonedaObjMap_f_hom_apply k g n z.val) (n + 1) rfl _).trans
    (P.extMk_comp_mk₀ z.val (n + 1) rfl z.property g).symm

end HomologyComparison

section IsoExtNaturality

open Opposite

variable {X Y : C} (P : ProjectiveResolution X) {k : Type t} [Ring k] [Linear k C]
  [EnoughProjectives C]

/-- `ProjectiveResolution.isoExt` is natural with respect to chain maps lifting morphisms in the
first variable. -/
@[reassoc]
lemma isoExt_hom_naturality_left {X' : C} (P' : ProjectiveResolution X') (f : X' ⟶ X)
    (φ : P'.complex ⟶ P.complex) (comm : φ.f 0 ≫ P.π.f 0 = P'.π.f 0 ≫ f) (n : ℕ) (Y : C) :
    ((_root_.Ext k C n).map f.op).app Y ≫ (P'.isoExt n Y).hom =
      (P.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
        (K := P.complex.linearYonedaObj k Y) (L := P'.complex.linearYonedaObj k Y)
        ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) n := by
  have hL : ((_root_.Ext k C n).map f.op).app Y ≫
      (P'.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop =
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap
          ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).map φ) n).unop := by
    have h := congrArg Quiver.Hom.unop (ProjectiveResolution.isoLeftDerivedObj_inv_naturality
      f P' P φ comm ((linearYoneda k C).obj Y).rightOp n)
    simp only [unop_comp] at h
    exact h
  exact isoExt_hom_square P P' n (((_root_.Ext k C n).map f.op).app Y)
    ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).map φ) rfl hL

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
    ext i (a : P.complex.X i ⟶ Y); exact P.complex.linearYonedaObjMap_f_hom_apply k g i a
  have hL : ((_root_.Ext k C n).obj (op X)).map g ≫
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop =
      (P.isoLeftDerivedObj ((linearYoneda k C).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α _).app P.complex) n).unop := by
    have h := congrArg Quiver.Hom.unop (P.leftDerived_app_eq α n)
    simp only [unop_comp] at h
    have hcancel : (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).hom.unop ≫
        (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop = 𝟙 _ := by
      rw [← unop_comp, Iso.inv_hom_id, unop_id]
    have h' := congrArg
      (· ≫ (P.isoLeftDerivedObj ((linearYoneda k C).obj Y').rightOp n).inv.unop) h
    simp only [Category.assoc, hcancel, Category.comp_id,
      HomologicalComplex.homologyFunctor_map] at h'
    exact h'
  exact isoExt_hom_square P P n (((_root_.Ext k C n).obj (op X)).map g)
    ((NatTrans.mapHomologicalComplex α _).app P.complex) hmap hL

end IsoExtNaturality

section HomologyIso

variable [HasExt.{v} C] (k : Type t) [CommRing k] [Linear k C]

/-- `ProjectiveResolution.homologyLinearYonedaEquiv` packaged as an isomorphism in `ModuleCat k`. -/
noncomputable def homologyLinearYonedaIso {X Y : C}
    (P : ProjectiveResolution X) (n : ℕ) :
    (P.complex.linearYonedaObj k Y).homology n ≅
      ((linearExtFunctor k C n).obj (Opposite.op X)).obj Y :=
  (P.homologyLinearYonedaEquiv (k := k) (Y := Y) n).toModuleIso

/-- `ProjectiveResolution.homologyLinearYonedaIso` acts as
`ProjectiveResolution.homologyLinearYonedaEquiv`. -/
@[simp↓]
lemma homologyLinearYonedaIso_hom_apply {X Y : C}
    (P : ProjectiveResolution X) (n : ℕ)
    (x : (P.complex.linearYonedaObj k Y).homology n) :
    (P.homologyLinearYonedaIso k n).hom x = P.homologyLinearYonedaEquiv n x :=
  (rfl)

end HomologyIso

end CategoryTheory.ProjectiveResolution
