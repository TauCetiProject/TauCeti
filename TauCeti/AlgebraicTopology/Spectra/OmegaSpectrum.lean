/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization
public import TauCeti.AlgebraicTopology.Spectra.Stabilization
public import TauCeti.AlgebraicTopology.Spectra.Tensor

import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Ω-spectra and stabilization mapping spaces

A symmetric spectrum `E` is an *Ω-spectrum* when every level `E_n` is a Kan complex and every
adjoint structure map `E_n ⟶ Ω E_(1+n)` is a weak equivalence of simplicial sets.

Using the free-spectrum smash comparison
`levelSmash ((free n).obj K) ≅ MonoidalCategory.tensorLeft K ⋙ free n`, uniqueness of right
adjoints identifies the pointed mapping space `Map(F_n K, E)` with the pointed mapping space
`Map_*(K, E_n)`, and in particular `Map(F_n S⁰, E) ≅ E_n`. Under these identifications,
precomposition along the stabilization map `freeStabilizationMap n K : F_(1+n)(S¹ ∧ K) ⟶ F_n K`
agrees with `Map_*(K, σ'_n) : Map_*(K, E_n) ⟶ Map_*(K, Ω E_(1+n))`, and for `K = S⁰` with
the adjoint structure map `σ'_n : E_n ⟶ Ω E_(1+n)` itself.

Consequently, `E` is an Ω-spectrum if and only if `E` is level fibrant (`E ⟶ ⊤` is a level
fibration, equivalently every `E_n` is a Kan complex) and every stabilization precomposition
`Map(F_n S⁰, E) ⟶ Map(F_(1+n)(S¹ ∧ S⁰), E)` is a weak equivalence of simplicial sets.

## Main definitions

* `SymmetricSequence.freeTensorFreeZeroIso`: the isomorphism `G_n K ⊗ G₀ L ≅ G_n (K ∧ L)`.
* `SymmetricSpectrum.levelSmashFreeIso`: the isomorphism `(F_n K) ∧ L ≅ F_n (K ∧ L)`.
* `SymmetricSpectrum.levelSmashFreeZeroIso`: the isomorphism `(F_n S⁰) ∧ L ≅ F_n L`.
* `SymmetricSpectrum.mappingSpaceFreeIso`: the isomorphism `Map(F_n K, E) ≅ Map_*(K, E_n)`.
* `SymmetricSpectrum.mappingSpaceFreeZeroIso`: the isomorphism `Map(F_n S⁰, E) ≅ E_n`.
* `SymmetricSpectrum.IsOmegaSpectrum`: the class of Ω-spectra.

## Main statements

* `SymmetricSpectrum.mappingSpace_freeStabilizationMap_eq`: precomposition along
  `freeStabilizationMap n K` identifies with `Map_*(K, E.smashPowAdjointStructureMap n)`.
* `SymmetricSpectrum.mappingSpace_freeStabilizationMap_unit_eq`: for `K = S⁰`, precomposition along
  `freeStabilizationMap n S⁰` identifies with `E.smashPowAdjointStructureMap n`.
* `SymmetricSpectrum.isOmegaSpectrum_iff_mappingSpace_freeStabilizationMap`: `E` is an Ω-spectrum
  precisely when every level is a Kan complex and precomposition along each
  `freeStabilizationMap n S⁰` is a weak equivalence on `Map(-, E)`.
* `SymmetricSpectrum.isOmegaSpectrum_iff_levelFibrations_and_mappingSpace`: `E` is an Ω-spectrum
  precisely when `E ⟶ ⊤` is a level fibration and precomposition along each
  `freeStabilizationMap n S⁰` is a weak equivalence on `Map(-, E)`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Definitions 1.2.5 and 3.4.3.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace TauCeti

open scoped DayFunctor

namespace SymmetricSequence

/-- The canonical comparison map `G_n (K ∧ L) ⟶ G_n K ⊗ G₀ L`, adjoint to the generator
inclusion `K ∧ L ⟶ (G_n K)_n ∧ L ≅ (G_n K ⊗ G₀ L)_n`. -/
private noncomputable def freeTensorFreeZeroHom (n : ℕ) (K L : PointedSSet.{0}) :
    (free n).obj (K ⊗ L) ⟶ (free n).obj K ⊗ (free 0).obj L :=
  ((freeEvaluationAdjunction n).homEquiv _ _).symm
    (freeι n K ▷ L ≫ tensorFreeZeroι ((free n).obj K) L n)

@[reassoc]
private lemma freeι_comp_freeTensorFreeZeroHom (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ (freeTensorFreeZeroHom n K L).natTrans.app (FiniteBijection.mk n) =
      freeι n K ▷ L ≫ tensorFreeZeroι ((free n).obj K) L n :=
  freeι_comp_homEquiv_symm n _

/-- Uniqueness of left adjoints relates `freeι n K` to the summand inclusion of `𝟙_` in the
underlying coproduct `∐ (fun _ : mk n ⟶ mk n ↦ K)` (since `freeι` is opaque outside `Free`). -/
private noncomputable def freeLeftAdjointSelfIso (n : ℕ) : free n ≅ free n :=
  (freeEvaluationAdjunction n).leftAdjointUniq
    ((evaluationAdjunctionRight PointedSSet.{0} (FiniteBijection.mk n)).comp
      (DayFunctor.equiv FiniteBijection PointedSSet.{0}).symm.toAdjunction)

private lemma freeι_comp_freeLeftAdjointSelfIso_hom_app (n : ℕ) (K : PointedSSet.{0}) :
    freeι n K ≫ ((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n) =
      Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) (𝟙 _) := by
  let adj' := (evaluationAdjunctionRight PointedSSet.{0} (FiniteBijection.mk n)).comp
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).symm.toAdjunction
  have h := Adjunction.unit_leftAdjointUniq_hom_app (freeEvaluationAdjunction n) adj' K
  rw [freeEvaluationAdjunction_unit_app] at h
  refine h.trans ?_
  simp only [Functor.id_obj, Equivalence.symm_functor, Functor.comp_obj, evaluation_obj_obj]
  exact Category.comp_id _

private lemma sigma_ι_comp_freeLeftAdjointSelfIso_inv (n : ℕ) (K : PointedSSet.{0})
    (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk n) :
    Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) σ ≫
        ((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n) =
      freeι n K ≫ ((free n).obj K).functor.map σ := by
  have hinv : freeι n K ≫
      ((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n) ≫
      ((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n) = freeι n K := by
    have hid : ((freeLeftAdjointSelfIso n).hom.app K ≫
        (freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n) = 𝟙 _ := by
      rw [Iso.hom_inv_id_app]; rfl
    rw [← NatTrans.comp_app, ← DayFunctor.comp_natTrans, hid, Category.comp_id]
  have hσ : Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) (𝟙 _) ≫
      ((free n).obj K).functor.map σ =
      Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) σ := by
    have hmap : ((free n).obj K).functor.map σ =
        Limits.Sigma.desc fun g ↦
          Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) (g ≫ σ) := by
      change ((evaluationLeftAdjoint PointedSSet.{0} (FiniteBijection.mk n)).obj K).map σ = _
      simp only [evaluationLeftAdjoint_obj_map]; rfl
    refine (congrArg (Limits.Sigma.ι (fun _ ↦ K) (𝟙 _) ≫ ·) hmap).trans ?_
    exact (Limits.Sigma.ι_comp_desc _ _).trans (by rw [Category.id_comp])
  have hnat := ((freeLeftAdjointSelfIso n).inv.app K).natTrans.naturality σ
  have h1 : freeι n K ≫
      ((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n) ≫
      ((free n).obj K).functor.map σ ≫
      ((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n) =
      freeι n K ≫ ((free n).obj K).functor.map σ := by
    rw [hnat, ← Category.assoc
      (((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n)),
      ← Category.assoc, hinv]
  have h2 := (Category.assoc
    (Limits.Sigma.ι (fun _ ↦ K) (𝟙 _) : K ⟶ ((free n).obj K).functor.obj (FiniteBijection.mk n))
    (((free n).obj K).functor.map σ)
    (((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n))).trans
    ((congrArg (fun g : K ⟶ ((free n).obj K).functor.obj (FiniteBijection.mk n) ↦
      g ≫ ((free n).obj K).functor.map σ ≫
        ((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n))
      (freeι_comp_freeLeftAdjointSelfIso_hom_app n K).symm).trans
      ((Category.assoc _ _ _).trans h1))
  exact (congrArg (· ≫ ((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n))
    hσ).symm.trans h2

private lemma freeι_comp_map_comp_freeLeftAdjointSelfIso_hom (n : ℕ) (K : PointedSSet.{0})
    (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk n) :
    freeι n K ≫ ((free n).obj K).functor.map σ ≫
        ((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n) =
      Limits.Sigma.ι (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk n ↦ K) σ := by
  have hid : ((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n) ≫
      ((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n) = 𝟙 _ := by
    have h : (((freeLeftAdjointSelfIso n).inv.app K ≫
        (freeLeftAdjointSelfIso n).hom.app K)).natTrans.app (FiniteBijection.mk n) = 𝟙 _ := by
      rw [Iso.inv_hom_id_app]; rfl
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using h
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n))
    (sigma_ι_comp_freeLeftAdjointSelfIso_inv n K σ).symm).trans ?_
  exact (Category.assoc
    (Limits.Sigma.ι (fun _ ↦ K) σ : K ⟶ ((free n).obj K).functor.obj (FiniteBijection.mk n))
    (((freeLeftAdjointSelfIso n).inv.app K).natTrans.app (FiniteBijection.mk n))
    (((freeLeftAdjointSelfIso n).hom.app K).natTrans.app (FiniteBijection.mk n))).trans
    ((congrArg (fun g : ((free n).obj K).functor.obj (FiniteBijection.mk n) ⟶ _ ↦
      (Limits.Sigma.ι (fun _ ↦ K) σ :
        K ⟶ ((free n).obj K).functor.obj (FiniteBijection.mk n)) ≫ g) hid).trans
      (Category.comp_id _))

private lemma sigma_ι_comp_fwdMap (m : ℕ) (K L : PointedSSet.{0})
    (σ : FiniteBijection.mk m ⟶ FiniteBijection.mk m) :
    Limits.Sigma.ι (fun _ ↦ K ⊗ L) σ ≫
        ((freeLeftAdjointSelfIso m).inv.app (K ⊗ L)).natTrans.app (FiniteBijection.mk m) ≫
        (freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
        inv (tensorFreeZeroι ((free m).obj K) L m) ≫
        ((freeLeftAdjointSelfIso m).hom.app K).natTrans.app (FiniteBijection.mk m) ▷ L =
      Limits.Sigma.ι (fun _ ↦ K) σ ▷ L := by
  let uK := ((freeLeftAdjointSelfIso m).hom.app K).natTrans.app (FiniteBijection.mk m)
  have hstep : (freeι m (K ⊗ L) ≫ ((free m).obj (K ⊗ L)).functor.map σ) ≫
      (freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
      inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L =
      (freeι m K ≫ ((free m).obj K).functor.map σ ≫ uK) ▷ L := by
    calc
      (freeι m (K ⊗ L) ≫ ((free m).obj (K ⊗ L)).functor.map σ) ≫
          (freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
          inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L
          = freeι m (K ⊗ L) ≫
            (freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
            ((free m).obj K ⊗ (free 0).obj L).functor.map σ ≫
            inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L := by
            simp only [Category.assoc]
            congr 1
            exact NatTrans.naturality_assoc (freeTensorFreeZeroHom m K L).natTrans σ _
      _ = (freeι m K ▷ L ≫ tensorFreeZeroι ((free m).obj K) L m) ≫
            ((free m).obj K ⊗ (free 0).obj L).functor.map σ ≫
            inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L := by
            rw [freeι_comp_freeTensorFreeZeroHom_assoc]; rfl
      _ = (freeι m K ▷ L ≫ ((free m).obj K).functor.map σ ▷ L) ≫
            (tensorFreeZeroι ((free m).obj K) L m ≫
              inv (tensorFreeZeroι ((free m).obj K) L m)) ≫ uK ▷ L := by
            simp only [Category.assoc, map_whiskerRight_comp_tensorFreeZeroι_assoc]; rfl
      _ = (freeι m K ≫ ((free m).obj K).functor.map σ ≫ uK) ▷ L := by
            rw [IsIso.hom_inv_id, Category.id_comp, ← comp_whiskerRight, ← comp_whiskerRight,
              Category.assoc]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg
    (fun g : K ⊗ L ⟶ ((free m).obj (K ⊗ L)).functor.obj (FiniteBijection.mk m) ↦
      g ≫ (freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
        inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L)
    (sigma_ι_comp_freeLeftAdjointSelfIso_inv m (K ⊗ L) σ)).trans ?_
  exact hstep.trans (congrArg (· ▷ L) (freeι_comp_map_comp_freeLeftAdjointSelfIso_hom m K σ))

private lemma isIso_freeTensorFreeZeroHom_app_self (m : ℕ) (K L : PointedSSet.{0}) :
    IsIso ((freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m)) := by
  let c₁ := Limits.coproductIsCoproduct
    (fun _ : FiniteBijection.mk m ⟶ FiniteBijection.mk m ↦ K ⊗ L)
  let c₂ := Limits.isColimitOfPreserves (tensorRight L)
    (Limits.coproductIsCoproduct (fun _ : FiniteBijection.mk m ⟶ FiniteBijection.mk m ↦ K))
  let invCocone : Limits.Cocone
      (Discrete.functor (fun _ : FiniteBijection.mk m ⟶ FiniteBijection.mk m ↦ K) ⋙
        tensorRight L) :=
    Limits.Cocone.mk (((free m).obj (K ⊗ L)).functor.obj (FiniteBijection.mk m))
      (Discrete.natTrans fun j ↦ Limits.Sigma.ι (fun _ ↦ K ⊗ L) j.as)
  let invMap := c₂.desc invCocone
  let uKL := ((freeLeftAdjointSelfIso m).inv.app (K ⊗ L)).natTrans.app (FiniteBijection.mk m)
  let uK := ((freeLeftAdjointSelfIso m).hom.app K).natTrans.app (FiniteBijection.mk m)
  let fwdMap := uKL ≫ (freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
    inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L
  have hfac (σ : FiniteBijection.mk m ⟶ FiniteBijection.mk m) :
      Limits.Sigma.ι (fun _ ↦ K) σ ▷ L ≫ invMap = Limits.Sigma.ι (fun _ ↦ K ⊗ L) σ :=
    c₂.fac invCocone ⟨σ⟩
  have hfwd_inv : fwdMap ≫ invMap = 𝟙 _ := by
    apply c₁.hom_ext
    intro ⟨σ⟩
    change Limits.Sigma.ι (fun _ ↦ K ⊗ L) σ ≫ fwdMap ≫ invMap =
      Limits.Sigma.ι (fun _ ↦ K ⊗ L) σ ≫ 𝟙 _
    exact (Category.assoc _ _ _).symm.trans
      (((sigma_ι_comp_fwdMap m K L σ =≫ invMap).trans (hfac σ)).trans (Category.comp_id _).symm)
  have hinv_fwd : invMap ≫ fwdMap = 𝟙 _ := by
    apply c₂.hom_ext
    intro ⟨σ⟩
    change Limits.Sigma.ι (fun _ ↦ K) σ ▷ L ≫ invMap ≫ fwdMap =
      Limits.Sigma.ι (fun _ ↦ K) σ ▷ L ≫ 𝟙 _
    rw [← Category.assoc, hfac σ, Category.comp_id]
    exact sigma_ι_comp_fwdMap m K L σ
  have : IsIso fwdMap := ⟨⟨invMap, hfwd_inv, hinv_fwd⟩⟩
  let evalM := (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
    (CategoryTheory.evaluation FiniteBijection PointedSSet.{0}).obj (FiniteBijection.mk m)
  have huKL : IsIso uKL := Functor.map_isIso evalM ((freeLeftAdjointSelfIso m).inv.app (K ⊗ L))
  have huK : IsIso uK := Functor.map_isIso evalM ((freeLeftAdjointSelfIso m).hom.app K)
  have : IsIso ((freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
      inv (tensorFreeZeroι ((free m).obj K) L m) ≫ uK ▷ L) :=
    IsIso.of_isIso_comp_left uKL _
  have : IsIso (((freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
      inv (tensorFreeZeroι ((free m).obj K) L m)) ≫ uK ▷ L) := by
    simpa only [Category.assoc] using this
  have : IsIso ((freeTensorFreeZeroHom m K L).natTrans.app (FiniteBijection.mk m) ≫
      inv (tensorFreeZeroι ((free m).obj K) L m)) :=
    IsIso.of_isIso_comp_right _ (uK ▷ L)
  exact IsIso.of_isIso_comp_right _ (inv (tensorFreeZeroι ((free m).obj K) L m))

private lemma isIso_freeTensorFreeZeroHom (n : ℕ) (K L : PointedSSet.{0}) :
    IsIso (freeTensorFreeZeroHom n K L) := by
  have hn : ∀ c : FiniteBijection, IsIso ((freeTensorFreeZeroHom n K L).natTrans.app c) := by
    rintro ⟨m⟩
    by_cases h : m = n
    · subst h
      exact isIso_freeTensorFreeZeroHom_app_self m K L
    · have hI₁ : Limits.IsInitial (((free n).obj (K ⊗ L)).functor.obj (FiniteBijection.mk m)) :=
        isInitialFreeObj (K ⊗ L) h
      have hI₂ : Limits.IsInitial
          (((free n).obj K ⊗ (free 0).obj L).functor.obj (FiniteBijection.mk m)) :=
        (Limits.IsInitial.isInitialObj (tensorRight L) _ (isInitialFreeObj K h)).ofIso
          (asIso (tensorFreeZeroι ((free n).obj K) L m))
      exact Limits.isIso_of_isInitial hI₁ hI₂ _
  have : IsIso ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
      (freeTensorFreeZeroHom n K L)) := by
    rw [DayFunctor.equiv_functor_map]
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hn
  exact isIso_of_reflects_iso _ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor

/-- Smashing a free symmetric sequence `G_n K` on the right with `G₀ L` is naturally isomorphic
in `L` to `G_n (K ∧ L)`. -/
noncomputable def freeTensorFreeZeroIso (n : ℕ) (K : PointedSSet.{0}) :
    free 0 ⋙ tensorLeft ((free n).obj K) ≅ tensorLeft K ⋙ free n :=
  NatIso.ofComponents
    (fun L ↦ have := isIso_freeTensorFreeZeroHom n K L; (asIso (freeTensorFreeZeroHom n K L)).symm)
    (fun {L L'} f ↦ by
      have := isIso_freeTensorFreeZeroHom n K L
      have := isIso_freeTensorFreeZeroHom n K L'
      have hnat : freeTensorFreeZeroHom n K L ≫ (free n).obj K ◁ (free 0).map f =
          (free n).map (K ◁ f) ≫ freeTensorFreeZeroHom n K L' := by
        apply ((freeEvaluationAdjunction n).homEquiv (K ⊗ L) _).injective
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, freeEvaluationAdjunction_unit_app]
        -- Expose `(freeEvaluationAdjunction n).right` evaluation at `mk n` as `.natTrans.app`.
        change freeι n (K ⊗ L) ≫
            (freeTensorFreeZeroHom n K L ≫ (free n).obj K ◁ (free 0).map f).natTrans.app
              (FiniteBijection.mk n) =
          freeι n (K ⊗ L) ≫
            ((free n).map (K ◁ f) ≫ freeTensorFreeZeroHom n K L').natTrans.app
              (FiniteBijection.mk n)
        have hnatι : freeι n (K ⊗ L) ≫
            ((free n).map (K ◁ f)).natTrans.app (FiniteBijection.mk n) =
          K ◁ f ≫ freeι n (K ⊗ L') := (freeι_naturality n (K ◁ f)).symm
        have htr := (tensorFreeZeroι_naturality_right ((free n).obj K) f n).symm
        rw [DayFunctor.comp_natTrans, NatTrans.comp_app, DayFunctor.comp_natTrans,
          NatTrans.comp_app, freeι_comp_freeTensorFreeZeroHom_assoc,
          ← Category.assoc (freeι n (K ⊗ L)), hnatι, Category.assoc,
          freeι_comp_freeTensorFreeZeroHom]
        dsimp only [free, Functor.comp_obj, Functor.comp_map] at htr ⊢
        rw [htr, ← whisker_exchange_assoc]
      rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv]
      dsimp only [Functor.comp_map]
      rw [← cancel_epi (freeTensorFreeZeroHom n K L), IsIso.hom_inv_id_assoc,
        ← cancel_mono (freeTensorFreeZeroHom n K L'), Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id]
      exact hnat)

/-- On the generating level `n`, `(freeTensorFreeZeroIso n K).inv.app L` sends the generator
`K ∧ L` to `(freeι n K ▷ L) ≫ tensorFreeZeroι ((free n).obj K) L n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_freeTensorFreeZeroIso_inv_app (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ ((freeTensorFreeZeroIso n K).inv.app L).natTrans.app (FiniteBijection.mk n) =
      freeι n K ▷ L ≫ tensorFreeZeroι ((free n).obj K) L n :=
  freeι_comp_freeTensorFreeZeroHom n K L

end SymmetricSequence

namespace SymmetricSpectrum

/-! ### Free smash comparisons and mapping spaces out of free spectra -/

/-- Smashing a free symmetric spectrum `F_n K` on the right with `L` is naturally isomorphic in
`L` to `F_n (K ∧ L)`. -/
noncomputable def levelSmashFreeIso (n : ℕ) (K : PointedSSet.{0}) :
    levelSmash ((free n).obj K) ≅ MonoidalCategory.tensorLeft K ⋙ free n :=
  Functor.isoWhiskerLeft (SymmetricSequence.free 0)
      (Mod.tensorLeftFreeIso (A := SymmetricSequence.sphere) ((SymmetricSequence.free n).obj K)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (SymmetricSequence.freeTensorFreeZeroIso n K)
      (freeMod SymmetricSequence.sphere) ≪≫
    Functor.associator _ _ _

/-- On the generating level `n`, `(levelSmashFreeIso n K).inv.app L` sends the generator
`K ∧ L` into `(F_n K)_n ∧ L ≅ (F_n K ∧ L)_n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_evaluation_map_levelSmashFreeIso_inv_app (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ (evaluation n).map ((levelSmashFreeIso n K).inv.app L) =
      freeι n K ▷ L ≫ SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n := by
  have hcomp : ((levelSmashFreeIso n K).inv.app L).hom =
      ((freeMod SymmetricSequence.sphere).map
        ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L)).hom ≫
      ((Mod.tensorLeftFreeIso (A := SymmetricSequence.sphere)
        ((SymmetricSequence.free n).obj K)).inv.app ((SymmetricSequence.free 0).obj L)).hom := by
    simp [levelSmashFreeIso]
  -- Expose `(evaluation n).map` on `SymmetricSpectrum` as
  -- `.hom.natTrans.app (FiniteBijection.mk n)`.
  change freeι n (K ⊗ L) ≫ (((levelSmashFreeIso n K).inv.app L).hom).natTrans.app
      (FiniteBijection.mk n) = _
  rw [hcomp, freeι_eq, DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc,
    Mod.tensorLeftFreeIso_inv_app_hom]
  have hmod : (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj (K ⊗ L))) ≫
      ((freeMod SymmetricSequence.sphere).map
        ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L)).hom ≫
      (α_ SymmetricSequence.sphere ((SymmetricSequence.free n).obj K)
        ((SymmetricSequence.free 0).obj L)).inv =
      ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L) ≫
        (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj K) ▷
          (SymmetricSequence.free 0).obj L) := by
    rw [← freeModι_naturality_assoc]
    dsimp only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj]
    rw [freeModι_tensor]
  have hmodApp := congrArg (fun g : (SymmetricSequence.free n).obj (K ⊗ L) ⟶ _ ↦
    g.natTrans.app (FiniteBijection.mk n)) hmod
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at hmodApp
  rw [hmodApp, SymmetricSequence.freeι_comp_freeTensorFreeZeroIso_inv_app_assoc,
    ← SymmetricSequence.tensorFreeZeroι_naturality_left, ← comp_whiskerRight_assoc,
    ← freeι_eq]
  rfl

/-- Smashing `F_n S⁰` with `L` is naturally isomorphic in `L` to `F_n L`. -/
noncomputable def levelSmashFreeZeroIso (n : ℕ) :
    levelSmash ((free n).obj (𝟙_ _)) ≅ free n :=
  levelSmashFreeIso n (𝟙_ _) ≪≫
    Functor.isoWhiskerRight (leftUnitorNatIso PointedSSet.{0}) (free n) ≪≫
    Functor.leftUnitor (free n)

/-- Mapping out of the free symmetric spectrum `F_n K` into `E` is naturally isomorphic to the
pointed mapping space `Map_*(K, E_n)`. -/
noncomputable def mappingSpaceFreeIso (n : ℕ) (K : PointedSSet.{0}) :
    mappingSpace ((free n).obj K) ≅ evaluation n ⋙ CategoryTheory.ihom K :=
  (levelSmashMappingSpaceAdjunction ((free n).obj K)).rightAdjointUniq
    (((CategoryTheory.ihom.adjunction K).comp (freeEvaluationAdjunction n)).ofNatIsoLeft
      (levelSmashFreeIso n K).symm)

/-- Mapping out of `F_n S⁰` into `E` is naturally isomorphic to level `E_n`. -/
noncomputable def mappingSpaceFreeZeroIso (n : ℕ) :
    mappingSpace ((free n).obj (𝟙_ _)) ≅ evaluation n :=
  mappingSpaceFreeIso n (𝟙_ _) ≪≫
    Functor.isoWhiskerLeft (evaluation n) MonoidalClosed.unitNatIso.symm

/-- For any two right adjoints to the same left adjoint, postcomposing the hom-set bijection with
the comparison `rightAdjointUniq` yields the second adjunction's hom-set bijection. -/
private lemma adjunction_homEquiv_comp_rightAdjointUniq_hom_app
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F ⊣ G') (L : C) (E : D) (f : F.obj L ⟶ E) :
    adj1.homEquiv L E f ≫ (adj1.rightAdjointUniq adj2).hom.app E = adj2.homEquiv L E f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (adj1.rightAdjointUniq adj2).hom.naturality f,
    Adjunction.unit_rightAdjointUniq_hom_app_assoc]

/-- Under `mappingSpaceFreeIso n K`, the adjunction bijection `F_n K ∧ L ⟶ E` corresponds to the
curried restriction of `K ∧ L ⟶ E_n` along the generator and `tensorFreeZeroι`. -/
private lemma homEquiv_comp_mappingSpaceFreeIso_hom_app (n : ℕ) (K L : PointedSSet.{0})
    (E : SymmetricSpectrum) (f : (levelSmash ((free n).obj K)).obj L ⟶ E) :
    (levelSmashMappingSpaceAdjunction ((free n).obj K)).homEquiv L E f ≫
        (mappingSpaceFreeIso n K).hom.app E =
      MonoidalClosed.curry (freeι n K ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n ≫ (evaluation n).map f) := by
  let adj2 := ((CategoryTheory.ihom.adjunction K).comp (freeEvaluationAdjunction n)).ofNatIsoLeft
    (levelSmashFreeIso n K).symm
  rw [mappingSpaceFreeIso, adjunction_homEquiv_comp_rightAdjointUniq_hom_app _ adj2]
  dsimp only [adj2]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, Iso.symm_hom]
  dsimp only [MonoidalCategory.curriedTensor_obj_obj]
  rw [Adjunction.homEquiv_unit (freeEvaluationAdjunction n), freeEvaluationAdjunction_unit_app,
    Functor.map_comp, freeι_comp_evaluation_map_levelSmashFreeIso_inv_app_assoc]
  rfl

/-- Passing across `tensorFreeZeroι` intertwines the structure map of `X` with the structure map
of `X ∧ L`. -/
private lemma tensorFreeZeroι_comp_levelSmash_dayStructureMap_aux
    (X : SymmetricSpectrum) (L : PointedSSet.{0}) (p q : FiniteBijection) :
    (α_ (SymmetricSequence.sphere.functor.obj p) (X.X.functor.obj q)
        (((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0))).hom ≫
        SymmetricSequence.sphere.functor.obj p ◁
          (DayFunctor.η X.X ((SymmetricSequence.free 0).obj L)).app (q, FiniteBijection.mk 0) ≫
        SymmetricSequence.sphere.functor.obj p ◁
          (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ q).hom ≫
        (DayFunctor.η SymmetricSequence.sphere (X.X ⊗ (SymmetricSequence.free 0).obj L)).app
          (p, q) ≫
        (α_ SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L)).inv.natTrans.app
          (p ⊗ q) ≫
        (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
          (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q) =
      (DayFunctor.η SymmetricSequence.sphere X.X).app (p, q) ▷
          ((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0) ≫
        (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X)).natTrans.app (p ⊗ q) ▷
          ((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0) ≫
        (DayFunctor.η X.X ((SymmetricSequence.free 0).obj L)).app (p ⊗ q, FiniteBijection.mk 0) ≫
        (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ (p ⊗ q)).hom := by
  have hη : SymmetricSequence.sphere.functor.obj p ◁
        (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ q).hom ≫
      (DayFunctor.η SymmetricSequence.sphere (X.X ⊗ (SymmetricSequence.free 0).obj L)).app (p, q) =
      (DayFunctor.η SymmetricSequence.sphere (X.X ⊗ (SymmetricSequence.free 0).obj L)).app
          (p, q ⊗ FiniteBijection.mk 0) ≫
        (SymmetricSequence.sphere ⊗ (X.X ⊗ (SymmetricSequence.free 0).obj L)).functor.map
          (p ◁ (ρ_ q).hom) := by
    simpa using (DayFunctor.η SymmetricSequence.sphere
      (X.X ⊗ (SymmetricSequence.free 0).obj L)).naturality
      ((𝟙 p, (ρ_ q).hom) : (p, q ⊗ FiniteBijection.mk 0) ⟶ (p, q))
  have hγNat : ((SymmetricSequence.sphere ⊗ X.X) ⊗ (SymmetricSequence.free 0).obj L).functor.map
        (ρ_ (p ⊗ q)).hom ≫
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
        (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q) =
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
          (SymmetricSequence.free 0).obj L).natTrans.app ((p ⊗ q) ⊗ FiniteBijection.mk 0) ≫
        (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ (p ⊗ q)).hom :=
    (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
      (SymmetricSequence.free 0).obj L).natTrans.naturality (ρ_ (p ⊗ q)).hom
  have hday := DayFunctor.whiskerLeft_η_app_comp_η_app_comp_associator_inv_natTrans_app_assoc
    SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L) p q (FiniteBijection.mk 0)
    (((SymmetricSequence.sphere ⊗ X.X) ⊗ (SymmetricSequence.free 0).obj L).functor.map
        (p ◁ (ρ_ q).hom) ≫
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
        (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q))
  slice_lhs 3 4 => rw [hη]
  slice_lhs 4 5 =>
    rw [(α_ SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L)).inv.natTrans.naturality
      ((p ◁ (ρ_ q).hom : p ⊗ q ⊗ FiniteBijection.mk 0 ⟶ p ⊗ q))]
  rw [Category.assoc
    ((α_ SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L)).inv.natTrans.app _)]
  rw [hday, Iso.hom_inv_id_assoc]
  congr 1
  slice_lhs 2 3 =>
    rw [← Functor.map_comp,
      show (α_ p q (FiniteBijection.mk 0)).hom ≫ p ◁ (ρ_ q).hom = (ρ_ (p ⊗ q)).hom by
        -- Expose `FiniteBijection.mk 0` as `𝟙_ FiniteBijection` so `monoidal` applies.
        change (α_ p q (𝟙_ FiniteBijection)).hom ≫ p ◁ (ρ_ q).hom = (ρ_ (p ⊗ q)).hom
        monoidal]
  slice_lhs 2 3 => rw [hγNat]
  rw [DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc]

private lemma tensorFreeZeroι_comp_levelSmash_smashPowStructureMap
    (X : SymmetricSpectrum) (L : PointedSSet.{0}) (n : ℕ) :
    X.smashPowStructureMap n ▷ L ≫
        SymmetricSequence.tensorFreeZeroι X.X L (1 + n) =
      (α_ PointedSSet.circle (X.X.functor.obj (FiniteBijection.mk n)) L).hom ≫
        PointedSSet.circle ◁ SymmetricSequence.tensorFreeZeroι X.X L n ≫
        ((levelSmash X).obj L).smashPowStructureMap n := by
  let p := FiniteBijection.mk 1
  let q := FiniteBijection.mk n
  have hday : (α_ (SymmetricSequence.sphere.functor.obj p) (X.X.functor.obj q) L).hom ≫
        SymmetricSequence.sphere.functor.obj p ◁ SymmetricSequence.tensorFreeZeroι X.X L n ≫
        ((levelSmash X).obj L).dayStructureMap p q =
      X.dayStructureMap p q ▷ L ≫
        SymmetricSequence.tensorFreeZeroι X.X L (1 + n) := by
    calc
      (α_ _ _ _).hom ≫ SymmetricSequence.sphere.functor.obj p ◁
            SymmetricSequence.tensorFreeZeroι X.X L n ≫
          ((levelSmash X).obj L).dayStructureMap p q
          = (SymmetricSequence.sphere.functor.obj p ⊗ X.X.functor.obj q) ◁
                SymmetricSequence.freeι 0 L ≫
              ((α_ (SymmetricSequence.sphere.functor.obj p) (X.X.functor.obj q)
                  (((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0))).hom ≫
                SymmetricSequence.sphere.functor.obj p ◁
                  (DayFunctor.η X.X ((SymmetricSequence.free 0).obj L)).app
                    (q, FiniteBijection.mk 0) ≫
                SymmetricSequence.sphere.functor.obj p ◁
                  (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ q).hom ≫
                (DayFunctor.η SymmetricSequence.sphere
                    (X.X ⊗ (SymmetricSequence.free 0).obj L)).app (p, q) ≫
                (α_ SymmetricSequence.sphere X.X
                    ((SymmetricSequence.free 0).obj L)).inv.natTrans.app (p ⊗ q) ≫
                (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
                  (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q)) := by
            simp only [SymmetricSequence.tensorFreeZeroι_def, Mod.dayStructureMap_def,
              Mod.tensorLeft_smul, DayFunctor.comp_natTrans, NatTrans.comp_app,
              whiskerLeft_comp, Category.assoc]
            rw [← associator_naturality_right_assoc]
      _ = X.dayStructureMap p q ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) := by
            rw [tensorFreeZeroι_comp_levelSmash_dayStructureMap_aux]
            rw [← comp_whiskerRight_assoc, ← Mod.dayStructureMap_def, whisker_exchange_assoc]
            congr 1
            exact (SymmetricSequence.tensorFreeZeroι_def X.X L (1 + n)).symm
  rw [Mod.smashPowStructureMap_def, Mod.smashPowStructureMap_def, comp_whiskerRight,
    Category.assoc, hday.symm, associator_naturality_left_assoc, whisker_exchange_assoc]

/-- Comparing `ihomCurryIso A 𝟙_` with `MonoidalClosed.unitNatIso.inv` recovers precomposition
with the inverse right unitor `(ρ_ A).inv`. -/
private lemma ihomCurryIso_hom_comp_unitNatIso_inv
    {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] (A Z : C) :
    (MonoidalClosed.ihomCurryIso A (𝟙_ C) Z).hom ≫
        MonoidalClosed.unitNatIso.inv.app ((CategoryTheory.ihom A).obj Z) =
      (MonoidalClosed.pre (ρ_ A).inv).app Z := by
  have hunitInv : MonoidalClosed.unitNatIso.inv.app ((CategoryTheory.ihom A).obj Z) =
      (λ_ _).inv ≫ (CategoryTheory.ihom.ev (𝟙_ C)).app ((CategoryTheory.ihom A).obj Z) := by
    simp [MonoidalClosed.unitNatIso]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre, MonoidalClosed.uncurry_eq, hunitInv,
    ← Category.assoc (MonoidalClosed.ihomCurryIso A (𝟙_ C) Z).hom,
    leftUnitor_inv_naturality, Category.assoc, whiskerLeft_comp, Category.assoc,
    ← MonoidalClosed.uncurry_eq, ← MonoidalClosed.uncurry_eq,
    MonoidalClosed.ihomCurryIso_hom, MonoidalClosed.uncurry_uncurry_ihomCurry]
  simp only [Functor.id_obj]
  rw [← Category.assoc]
  congr 1
  monoidal

private lemma uncurry_uncurry_comp_ihomCurryIso_hom
    {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    {A B X Z : C} (f : X ⟶ (CategoryTheory.ihom (A ⊗ B)).obj Z) :
    MonoidalClosed.uncurry
        (MonoidalClosed.uncurry (f ≫ (MonoidalClosed.ihomCurryIso A B Z).hom)) =
      (α_ A B X).inv ≫ MonoidalClosed.uncurry f := by
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.ihomCurryIso_hom, MonoidalClosed.uncurry_uncurry_ihomCurry,
    associator_inv_naturality_right_assoc, ← MonoidalClosed.uncurry_eq]

private lemma smashPowStructureMap_levelSmash_comp_aux (n : ℕ) {K L : PointedSSet.{0}}
    (X E : SymmetricSpectrum) (ι : K ⟶ (evaluation n).obj X)
    (ε : (levelSmash X).obj L ⟶ E) :
    ((PointedSSet.circle ◁ ι ≫ X.smashPowStructureMap n) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι X.X L (1 + n)) ≫
      (evaluation (1 + n)).map ε =
      (α_ PointedSSet.circle K L).hom ≫
        PointedSSet.circle ◁ (ι ▷ L ≫
          SymmetricSequence.tensorFreeZeroι X.X L n ≫ (evaluation n).map ε) ≫
        E.smashPowStructureMap n := by
  have hε : ((levelSmash X).obj L).smashPowStructureMap n ≫ (evaluation (1 + n)).map ε =
      PointedSSet.circle ◁ (evaluation n).map ε ≫ E.smashPowStructureMap n :=
    Mod.smashPowStructureMap_hom ε n
  rw [comp_whiskerRight_assoc, tensorFreeZeroι_comp_levelSmash_smashPowStructureMap,
    Category.assoc, Category.assoc, Category.assoc, associator_naturality_middle_assoc]
  congr 1
  rw [hε, whiskerLeft_comp, whiskerLeft_comp, Category.assoc, Category.assoc]

private lemma evaluation_map_levelSmashRight_comp_aux (n : ℕ) {K L : PointedSSet.{0}}
    {X Y : SymmetricSpectrum} (E : SymmetricSpectrum) (f : X ⟶ Y)
    (ιX : PointedSSet.circle ⊗ K ⟶ (evaluation (1 + n)).obj X)
    (ιY : K ⟶ (evaluation n).obj Y)
    (hι : ιX ≫ (evaluation (1 + n)).map f =
      PointedSSet.circle ◁ ιY ≫ Y.smashPowStructureMap n)
    (ε : (levelSmash Y).obj L ⟶ E) :
    ιX ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) ≫
        (evaluation (1 + n)).map ((levelSmashRight L).map f ≫ ε) =
      (α_ PointedSSet.circle K L).hom ≫
        PointedSSet.circle ◁ (ιY ▷ L ≫
          SymmetricSequence.tensorFreeZeroι Y.X L n ≫ (evaluation n).map ε) ≫
        E.smashPowStructureMap n := by
  rw [Functor.map_comp]
  dsimp only [levelSmashRight]
  have hnatL : ιX ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) ≫
      (evaluation (1 + n)).map ((Mod.tensorRight ((SymmetricSequence.free 0).obj L)).map f) =
      (ιX ≫ (evaluation (1 + n)).map f) ▷ L ≫ SymmetricSequence.tensorFreeZeroι Y.X L (1 + n) := by
    rw [comp_whiskerRight, Category.assoc]
    congr 1
    exact (SymmetricSequence.tensorFreeZeroι_naturality_left f.hom L (1 + n)).symm
  have h1 : ιX ▷ L ≫ SymmetricSequence.tensorFreeZeroι X.X L (1 + n) ≫
      (evaluation (1 + n)).map ((Mod.tensorRight ((SymmetricSequence.free 0).obj L)).map f) ≫
        (evaluation (1 + n)).map ε =
      ((PointedSSet.circle ◁ ιY ≫ Y.smashPowStructureMap n) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι Y.X L (1 + n)) ≫
      (evaluation (1 + n)).map ε := by
    rw [← Category.assoc _ _ ((evaluation (1 + n)).map ε), ← Category.assoc (ιX ▷ L)]
    congr 1
    rw [hnatL, hι]
  exact h1.trans (smashPowStructureMap_levelSmash_comp_aux n Y E ιY ε)

private lemma freeStabilizationMap_levelSmash_comp (n : ℕ) (K L : PointedSSet.{0})
    (E : SymmetricSpectrum) (ε : (levelSmash ((free n).obj K)).obj L ⟶ E) :
    freeι (1 + n) (PointedSSet.circle ⊗ K) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free (1 + n)).obj (PointedSSet.circle ⊗ K)).X L
          (1 + n) ≫
        (evaluation (1 + n)).map ((levelSmashRight L).map (freeStabilizationMap n K) ≫ ε) =
      (α_ PointedSSet.circle K L).hom ≫
        PointedSSet.circle ◁ (freeι n K ▷ L ≫
          SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n ≫ (evaluation n).map ε) ≫
        E.smashPowStructureMap n :=
  evaluation_map_levelSmashRight_comp_aux n E (freeStabilizationMap n K)
    (freeι (1 + n) (PointedSSet.circle ⊗ K)) (freeι n K) (freeι_stabilizationMap n K) ε

private lemma homEquiv_levelSmashRight_counit (n : ℕ) (K : PointedSSet.{0})
    (E : SymmetricSpectrum) :
    (levelSmashMappingSpaceAdjunction ((free (1 + n)).obj (PointedSSet.circle ⊗ K))).homEquiv
        ((mappingSpace ((free n).obj K)).obj E) E
        ((levelSmashRight ((mappingSpace ((free n).obj K)).obj E)).map
          (freeStabilizationMap n K) ≫
          (levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E) =
      (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E := by
  let ε : (levelSmashBifunctor.obj ((free n).obj K)).obj
      ((mappingSpace ((free n).obj K)).obj E) ⟶ E :=
    (levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E
  let p : ((mappingSpace ((free n).obj K)).obj E) ⟶
      ((mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ K))).obj E) :=
    (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E
  have h := levelSmashMappingSpaceAdjunction₂.homEquiv_naturality_one
    (freeStabilizationMap n K) ε
  dsimp only [ParametrizedAdjunction.homEquiv] at h
  rw [levelSmashMappingSpaceAdjunction₂_adj, levelSmashMappingSpaceAdjunction₂_adj] at h
  -- Express the `levelSmashMappingSpaceAdjunction₂` naturality RHS via `p` and `adj₀.counit.app`.
  change _ = (levelSmashMappingSpaceAdjunction ((free n).obj K)).homEquiv _ E
    ((levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E) ≫ p at h
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Category.id_comp] at h
  exact h

/-- Under `mappingSpaceFreeIso` and `ihomCurryIso`, precomposition along
`freeStabilizationMap n K : F_(1+n)(S¹ ∧ K) ⟶ F_n K` agrees with
`Map_*(K, E.smashPowAdjointStructureMap n)`. -/
theorem mappingSpace_freeStabilizationMap_eq (n : ℕ) (K : PointedSSet.{0})
    (E : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E ≫
        (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ K)).hom.app E ≫
        (MonoidalClosed.ihomCurryIso PointedSSet.circle K ((evaluation (1 + n)).obj E)).hom =
      (mappingSpaceFreeIso n K).hom.app E ≫
        (CategoryTheory.ihom K).map (E.smashPowAdjointStructureMap n) := by
  let L := (mappingSpace ((free n).obj K)).obj E
  let p : L ⟶ (mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ K))).obj E :=
    (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E
  let adj₀ := levelSmashMappingSpaceAdjunction ((free n).obj K)
  let adj₁ := levelSmashMappingSpaceAdjunction ((free (1 + n)).obj (PointedSSet.circle ⊗ K))
  let ε : (levelSmash ((free n).obj K)).obj L ⟶ E := adj₀.counit.app E
  have hε : adj₀.homEquiv L E ε = 𝟙 L := by
    rw [Adjunction.homEquiv_unit, adj₀.right_triangle_components]
  have hR₂ : MonoidalClosed.uncurry ((mappingSpaceFreeIso n K).hom.app E) =
      freeι n K ▷ L ≫ SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n ≫
        (evaluation n).map ε := by
    rw [← Category.id_comp ((mappingSpaceFreeIso n K).hom.app E), ← hε,
      homEquiv_comp_mappingSpaceFreeIso_hom_app, MonoidalClosed.uncurry_curry]
  have hassoc : (mappingSpaceBifunctor.map (freeStabilizationMap n K).op).app E ≫
      (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ K)).hom.app E ≫
      (MonoidalClosed.ihomCurryIso PointedSSet.circle K ((evaluation (1 + n)).obj E)).hom =
      (p ≫ (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ K)).hom.app E) ≫
      (MonoidalClosed.ihomCurryIso PointedSSet.circle K ((evaluation (1 + n)).obj E)).hom :=
    (Category.assoc _ _ _).symm
  rw [hassoc]
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_uncurry_comp_ihomCurryIso_hom]
  have hL' : p = adj₁.homEquiv L E ((levelSmashRight L).map (freeStabilizationMap n K) ≫ ε) :=
    (homEquiv_levelSmashRight_counit n K E).symm
  rw [hL', homEquiv_comp_mappingSpaceFreeIso_hom_app, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_right, hR₂, MonoidalClosed.uncurry_natural_left,
    Mod.uncurry_smashPowAdjointStructureMap, ← cancel_epi (α_ PointedSSet.circle K L).hom,
    Iso.hom_inv_id_assoc]
  exact freeStabilizationMap_levelSmash_comp n K L E ε

/-- For `K = S⁰`, precomposition along `freeStabilizationMap n S⁰` agrees under
`mappingSpaceFreeZeroIso n` and `mappingSpaceFreeIso (1 + n) (S¹ ∧ S⁰)` with the adjoint
structure map `E.smashPowAdjointStructureMap n`. -/
theorem mappingSpace_freeStabilizationMap_unit_eq (n : ℕ) (E : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E ≫
        (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
        (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E) =
      (mappingSpaceFreeZeroIso n).hom.app E ≫ E.smashPowAdjointStructureMap n := by
  let p : (mappingSpace ((free n).obj (𝟙_ _))).obj E ⟶
      (mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ 𝟙_ _))).obj E :=
    (mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E
  -- Expose `(mappingSpaceBifunctor.map ...).app E` as `p` so
  -- `mappingSpace_freeStabilizationMap_eq` matches.
  change p ≫ _ = _
  have h : p ≫ (mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
      (MonoidalClosed.ihomCurryIso PointedSSet.circle (𝟙_ _) ((evaluation (1 + n)).obj E)).hom =
      (mappingSpaceFreeIso n (𝟙_ _)).hom.app E ≫
        (CategoryTheory.ihom (𝟙_ _)).map (E.smashPowAdjointStructureMap n) :=
    mappingSpace_freeStabilizationMap_eq n (𝟙_ _) E
  have h' := congrArg
    (· ≫ MonoidalClosed.unitNatIso.inv.app
      ((CategoryTheory.ihom PointedSSet.circle).obj ((evaluation (1 + n)).obj E))) h
  simp only [Category.assoc] at h'
  rw [ihomCurryIso_hom_comp_unitNatIso_inv] at h'
  refine h'.trans ?_
  rw [mappingSpaceFreeZeroIso]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    MonoidalClosed.unitNatIso.inv.naturality, Functor.id_map]

/-! ### Ω-spectra -/

/-- A symmetric spectrum `E` is an *Ω-spectrum* when every level `E_n` is a Kan complex and every
adjoint structure map `σ'_n : E_n ⟶ Ω E_(1+n)` is a weak equivalence of simplicial sets. -/
@[mk_iff]
class IsOmegaSpectrum (E : SymmetricSpectrum) : Prop where
  kanComplex : ∀ n, SSet.KanComplex ((evaluation n).obj E).right
  weakEquivalence_adjointStructureMap :
    ∀ n, WeakEquivalence (E.smashPowAdjointStructureMap n).right

attribute [instance] IsOmegaSpectrum.kanComplex

/-- A symmetric spectrum `E` is an Ω-spectrum if and only if every level `E_n` is a Kan complex
and precomposition along every stabilization map `freeStabilizationMap n S⁰` is a weak
equivalence on `Map(-, E)`. -/
theorem isOmegaSpectrum_iff_mappingSpace_freeStabilizationMap (E : SymmetricSpectrum) :
    IsOmegaSpectrum E ↔
      (∀ n, SSet.KanComplex ((evaluation n).obj E).right) ∧
        ∀ n, WeakEquivalence
          ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right := by
  rw [isOmegaSpectrum_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun n ↦ ?_
  have : IsIso ((MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app
      ((evaluation (1 + n)).obj E)) :=
    Iso.isIso_hom ((MonoidalClosed.internalHom.mapIso (ρ_ PointedSSet.circle).symm.op).app
      ((evaluation (1 + n)).obj E))
  let f : ((mappingSpace ((free n).obj (𝟙_ _))).obj E).right ⟶
      ((mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ 𝟙_ _))).obj E).right :=
    ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right
  let e₀ : ((mappingSpace ((free n).obj (𝟙_ _))).obj E).right ⟶ ((evaluation n).obj E).right :=
    ((mappingSpaceFreeZeroIso n).hom.app E).right
  let e₁ : ((mappingSpace ((free (1 + n)).obj (PointedSSet.circle ⊗ 𝟙_ _))).obj E).right ⟶
      ((CategoryTheory.ihom PointedSSet.circle).obj ((evaluation (1 + n)).obj E)).right :=
    ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
      (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E)).right
  have heq : f ≫ e₁ = e₀ ≫ (E.smashPowAdjointStructureMap n).right :=
    congrArg PointedSSet.forgetBasepoint.map (mappingSpace_freeStabilizationMap_unit_eq n E)
  have : IsIso e₀ :=
    Functor.map_isIso PointedSSet.forgetBasepoint ((mappingSpaceFreeZeroIso n).hom.app E)
  have he₁ : IsIso ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
      (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E)) :=
    IsIso.comp_isIso
  have : IsIso e₁ :=
    Functor.map_isIso PointedSSet.forgetBasepoint
      ((mappingSpaceFreeIso (1 + n) (PointedSSet.circle ⊗ 𝟙_ _)).hom.app E ≫
        (MonoidalClosed.pre (ρ_ PointedSSet.circle).inv).app ((evaluation (1 + n)).obj E))
  -- Fold the mapping-space precomposition map into `f` so `cancel_right_of_respectsIso` applies.
  change WeakEquivalence (E.smashPowAdjointStructureMap n).right ↔ WeakEquivalence f
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  have h1 : (weakEquivalences SSet.{0}) (E.smashPowAdjointStructureMap n).right ↔
      (weakEquivalences SSet.{0}) (e₀ ≫ (E.smashPowAdjointStructureMap n).right) :=
    ((weakEquivalences SSet.{0}).cancel_left_of_respectsIso e₀ _).symm
  have h2 : (weakEquivalences SSet.{0}) (f ≫ e₁) ↔ (weakEquivalences SSet.{0}) f :=
    (weakEquivalences SSet.{0}).cancel_right_of_respectsIso f e₁
  rw [h1, ← heq, h2]

/-- A symmetric spectrum `E` is an Ω-spectrum if and only if `E ⟶ ⊤` is a level fibration and
precomposition along every stabilization map `freeStabilizationMap n S⁰` is a weak equivalence
on `Map(-, E)`. -/
theorem isOmegaSpectrum_iff_levelFibrations_and_mappingSpace (E : SymmetricSpectrum) :
    IsOmegaSpectrum E ↔
      levelFibrations (terminal.from E) ∧
        ∀ n, WeakEquivalence
          ((mappingSpaceBifunctor.map (freeStabilizationMap n (𝟙_ _)).op).app E).right := by
  rw [isOmegaSpectrum_iff_mappingSpace_freeStabilizationMap, levelFibrations_terminal_from_iff]

end SymmetricSpectrum

end TauCeti
