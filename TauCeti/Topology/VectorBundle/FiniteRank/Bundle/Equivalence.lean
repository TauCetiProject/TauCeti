/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Topology.Algebra.Module.TransferInstance

import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Equivalence between genuine variable-rank bundles and small coordinate atlases

Every `E : FiniteRankBundle.{w} 𝕜 X` induces a small coordinate atlas `E.toAtlas` with
`FiniteRankBundle.reconstructionHomeomorph`, yielding an additive, full, and faithful functor
`FiniteRankBundle.toAtlasFunctor`, `FiniteRankBundle.isIso_iff_bijective`, `LocallySmall`,
`EssentiallySmall`, `FiniteRankBundle.toAtlasOfBundleIso`, and
`FiniteRankBundle.essImage_ofCoreFunctor_toAtlas_iff`. Under `[Small.{w} 𝕜]`, shrinking fibres gives
`FiniteRankBundle.fromAtlasFunctor` and `FiniteRankBundle.atlasEquivalence`, complemented by
`FiniteRankBundle.uliftFunctor` and `FiniteRankBundle.changeUniverseEquivalence`.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti.FiniteRankBundle

universe w w' w₁ w₂ u v

section ToAtlas

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Present a genuine variable-rank bundle `E` by its small point-indexed `FiniteRankAtlas`. -/
@[expose] noncomputable def toAtlas (E : FiniteRankBundle.{w} 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 E.rank E.StratumFiber

@[simp] theorem rank_toAtlas (E : FiniteRankBundle.{w} 𝕜 X) : E.toAtlas.rank = E.rank := (rfl)
@[simp] theorem charts_toAtlas (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ) :
    E.toAtlas.charts n = pointIndexedCore 𝕜 (Fin n → 𝕜) (E.StratumFiber n) := (rfl)

/-- Preferred continuous linear equivalence between `E.toAtlas.Fiber x` and `E.Fiber x`. -/
noncomputable def reconstructionFiberEquiv (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    E.toAtlas.Fiber x ≃L[𝕜] E.Fiber x :=
  pointIndexedCoreFiberEquiv 𝕜 (Fin (E.rank x) → 𝕜) (E.StratumFiber (E.rank x)) ⟨x, rfl⟩

/-- Homeomorphism over `X` between `TotalSpace Unit E.toAtlas.Fiber` and `TotalSpace Unit E.Fiber`
acting fibrewise by `E.reconstructionFiberEquiv`. -/
noncomputable def reconstructionHomeomorph (E : FiniteRankBundle.{w} 𝕜 X) :
    TotalSpace Unit E.toAtlas.Fiber ≃ₜ TotalSpace Unit E.Fiber :=
  (FiniteRankAtlas.reconstructionHomeomorph 𝕜 E.rank E.StratumFiber).trans E.totalSpaceHomeomorph

@[simp] theorem reconstructionHomeomorph_apply (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit E.toAtlas.Fiber) :
    E.reconstructionHomeomorph p = ⟨p.proj, E.reconstructionFiberEquiv p.proj p.2⟩ :=
  (congrArg E.totalSpaceHomeomorph
    (FiniteRankAtlas.reconstructionHomeomorph_apply 𝕜 E.rank E.StratumFiber p)).trans
    (E.totalSpaceHomeomorph_apply _)

@[simp] theorem reconstructionHomeomorph_symm_apply (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit E.Fiber) :
    E.reconstructionHomeomorph.symm p = ⟨p.proj, (E.reconstructionFiberEquiv p.proj).symm p.2⟩ :=
  ((congrArg (FiniteRankAtlas.reconstructionHomeomorph 𝕜 E.rank E.StratumFiber).symm
    (E.totalSpaceHomeomorph_symm_apply p)).trans
    (FiniteRankAtlas.reconstructionHomeomorph_symm_apply 𝕜 E.rank E.StratumFiber
      (E.rank p.proj) ⟨⟨p.proj, rfl⟩, p.2⟩)).trans
    ((FiniteRankAtlas.ofBundles 𝕜 E.rank E.StratumFiber).totalSpaceHomeomorph_apply _)

theorem proj_reconstructionHomeomorph (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit E.toAtlas.Fiber) : (E.reconstructionHomeomorph p).proj = p.proj := by
  rw [reconstructionHomeomorph_apply]

variable (𝕜 X) in
/-- Additive, full, and faithful functor presenting genuine variable-rank vector bundles by small
variable-rank coordinate atlases. -/
@[expose] noncomputable def toAtlasFunctor : FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj E := E.toAtlas
  map {E F} f :=
    { fiberMap x := (F.reconstructionFiberEquiv x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (E.reconstructionFiberEquiv x).toLinearMap)
      continuous_totalSpaceMap := (F.reconstructionHomeomorph.symm.continuous.comp
        (f.continuous_totalSpaceMap.comp E.reconstructionHomeomorph.continuous)).congr fun p ↦ by
          rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_apply,
            F.reconstructionHomeomorph_symm_apply]; rfl }
  map_id E := FiniteRankAtlas.hom_ext fun x ↦
    LinearMap.ext (E.reconstructionFiberEquiv x).symm_apply_apply
  map_comp {_ F G} f g := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦
    (congrArg (G.reconstructionFiberEquiv x).symm (congrArg (g.fiberMap x)
      ((F.reconstructionFiberEquiv x).apply_symm_apply _))).symm

@[simp] theorem toAtlasFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).obj E = E.toAtlas := (rfl)
@[simp] theorem toAtlasFunctor_map_fiberMap {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (x : X)
    (v : E.toAtlas.Fiber x) :
    ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x v =
      (F.reconstructionFiberEquiv x).symm (f.fiberMap x (E.reconstructionFiberEquiv x v)) := (rfl)

instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {_ F f g} := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    (F.reconstructionFiberEquiv x).symm.map_add (f.fiberMap x _) (g.fiberMap x _)

instance : (toAtlasFunctor.{w} 𝕜 X).Faithful where
  map_injective {E F} f g h := hom_ext fun x ↦ LinearMap.ext fun w ↦
    (congrArg (f.fiberMap x) ((E.reconstructionFiberEquiv x).apply_symm_apply w)).symm.trans <|
      ((F.reconstructionFiberEquiv x).apply_symm_apply _).symm.trans <|
        (congrArg (fun k : E.toAtlas ⟶ F.toAtlas ↦
          F.reconstructionFiberEquiv x (k.fiberMap x ((E.reconstructionFiberEquiv x).symm w)))
          h).trans <| ((F.reconstructionFiberEquiv x).apply_symm_apply _).trans <|
          congrArg (g.fiberMap x) ((E.reconstructionFiberEquiv x).apply_symm_apply w)

instance : (toAtlasFunctor.{w} 𝕜 X).Full where
  map_surjective {E F} g := by
    let g' : E.toAtlas ⟶ F.toAtlas := g
    refine ⟨⟨fun x ↦ (F.reconstructionFiberEquiv x).toLinearMap.comp
        ((g'.fiberMap x).comp (E.reconstructionFiberEquiv x).symm.toLinearMap),
      (F.reconstructionHomeomorph.continuous.comp
        (g'.continuous_totalSpaceMap.comp E.reconstructionHomeomorph.symm.continuous)).congr
        fun p ↦ by
          rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_symm_apply,
            F.reconstructionHomeomorph_apply]; rfl⟩,
      FiniteRankAtlas.hom_ext (A := E.toAtlas) (D := F.toAtlas) fun x ↦ LinearMap.ext fun v ↦
        ((F.reconstructionFiberEquiv x).symm_apply_apply _).trans
          (congrArg (g'.fiberMap x) ((E.reconstructionFiberEquiv x).symm_apply_apply v))⟩

/-- A morphism of genuine variable-rank bundles is an isomorphism iff every fibre map is
bijective. -/
theorem isIso_iff_bijective {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  rw [← isIso_iff_of_reflects_iso f (toAtlasFunctor.{w} 𝕜 X), FiniteRankAtlas.isIso_iff_bijective]
  exact forall_congr' fun x ↦
    Iff.rfl.trans (((F.reconstructionFiberEquiv x).symm.bijective.of_comp_iff' _).trans
      ((E.reconstructionFiberEquiv x).bijective.of_comp_iff _))

instance : LocallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  locallySmall_of_faithful (toAtlasFunctor.{w} 𝕜 X)
instance : EssentiallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

section ConstantRank

variable (𝕜) (n : ℕ) (V : X → Type w)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) V)]
  [FiberBundle (Fin n → 𝕜) V] [VectorBundle 𝕜 (Fin n → 𝕜) V]

/-- Presenting `V` via `FiniteRankBundle.ofBundle` and `toAtlas` is canonically isomorphic to
presenting `V` via `FiniteRankBundleCore.ofBundle` and `FiniteRankAtlas.ofCoreFunctor`. -/
noncomputable def toAtlasOfBundleIso :
    (ofBundle 𝕜 n V).toAtlas ≅
      (FiniteRankAtlas.ofCoreFunctor 𝕜 X).obj (FiniteRankBundleCore.ofBundle 𝕜 n V) := by
  let B := ofBundle 𝕜 n V; let C := FiniteRankBundleCore.ofBundle 𝕜 n V
  let f1 := B.reconstructionHomeomorph; let f2 := ofBundleHomeomorph 𝕜 n V
  let f3 := (pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) V).symm
  let f4 := (FiniteRankAtlas.ofCoreHomeomorph C).symm
  refine FiniteRankAtlas.isoMk
    (fun x ↦ ((B.reconstructionFiberEquiv x).trans
      (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) V x).symm).toLinearEquiv)
    ((f4.continuous.comp (f3.continuous.comp (f2.continuous.comp f1.continuous))).congr fun p ↦ ?_)
    ((f1.symm.continuous.comp (f2.symm.continuous.comp
      (f3.symm.continuous.comp f4.symm.continuous))).congr fun p ↦ ?_)
  · exact (congrArg f4 (congrArg f3 ((congrArg f2 (B.reconstructionHomeomorph_apply p)).trans
      (ofBundleHomeomorph_apply 𝕜 n V _)))).trans ((congrArg f4
        (pointIndexedCoreHomeomorph_symm_apply 𝕜 (Fin n → 𝕜) V _)).trans
        (FiniteRankAtlas.ofCoreHomeomorph_symm_apply C _))
  · exact (congrArg f1.symm (congrArg f2.symm ((congrArg f3.symm
      (FiniteRankAtlas.ofCoreHomeomorph_apply C p)).trans
      (pointIndexedCoreHomeomorph_apply 𝕜 (Fin n → 𝕜) V _)))).trans
      ((congrArg f1.symm (ofBundleHomeomorph_symm_apply 𝕜 n V _)).trans
        (B.reconstructionHomeomorph_symm_apply _))

end ConstantRank

/-- `E.toAtlas` lies in `(FiniteRankAtlas.ofCoreFunctor 𝕜 X).essImage` iff `E.rank` is constant. -/
theorem essImage_ofCoreFunctor_toAtlas_iff (E : FiniteRankBundle.{w} 𝕜 X) :
    (FiniteRankAtlas.ofCoreFunctor 𝕜 X).essImage E.toAtlas ↔ ∃ n : ℕ, ∀ x : X, E.rank x = n :=
  FiniteRankAtlas.essImage_ofCoreFunctor_iff E.toAtlas

end ToAtlas

/-! ### Explicit inverse functor and equivalence under `[Small.{w} 𝕜]` -/

section FromAtlas

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Reconstruct a genuine `w`-universe variable-rank vector bundle from `A : FiniteRankAtlas 𝕜 X`
when `[Small.{w} 𝕜]` holds. -/
@[expose] noncomputable def fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    FiniteRankBundle.{w} 𝕜 X :=
  let e (n : ℕ) (x : {x : X // A.rank x = n}) :
      Shrink.{w} (A.Fiber x.1) ≃L[𝕜] (A.charts n).Fiber x :=
    (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x.1)).trans
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr x.2))
  letI τ (n : ℕ) : TopologicalSpace
      (TotalSpace (Fin n → 𝕜) fun x : {x : X // A.rank x = n} ↦ Shrink.{w} (A.Fiber x.1)) :=
    totalSpaceInduced (Fin n → 𝕜) (E := (A.charts n).Fiber) (e n)
  letI fb (n : ℕ) :
      FiberBundle (Fin n → 𝕜) fun x : {x : X // A.rank x = n} ↦ Shrink.{w} (A.Fiber x.1) :=
    FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := (A.charts n).Fiber) (e n) ⟨rfl⟩
  { rank := A.rank, Fiber x := Shrink.{w} (A.Fiber x), topologicalSpaceStratum := τ,
    fiberBundleStratum := fb, vectorBundleStratum n :=
      VectorBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := (A.charts n).Fiber) (e n) ⟨rfl⟩ }

@[simp] theorem rank_fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlas.{w} A).rank = A.rank := (rfl)
@[simp] theorem fiber_fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (fromAtlas.{w} A).Fiber x = Shrink.{w} (A.Fiber x) := (rfl)

/-- Homeomorphism over `X` between `TotalSpace Unit (fromAtlas A).Fiber` and
`TotalSpace Unit A.Fiber`. -/
noncomputable def fromAtlasHomeomorph [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (fromAtlas.{w} A).Fiber ≃ₜ TotalSpace Unit A.Fiber :=
  let e (n : ℕ) (x : {x : X // A.rank x = n}) :
      Shrink.{w} (A.Fiber x.1) ≃L[𝕜] (A.charts n).Fiber x :=
    (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x.1)).trans
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr x.2))
  { toFun p := ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.2⟩
    invFun p := ⟨p.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).symm p.2⟩
    left_inv := fun ⟨proj, snd⟩ ↦ congrArg (TotalSpace.mk proj)
      ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber proj)).symm_apply_apply snd)
    right_inv := fun ⟨proj, snd⟩ ↦ congrArg (TotalSpace.mk proj)
      ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber proj)).apply_symm_apply snd)
    continuous_toFun := by
      have hsigma : Continuous (fun q : (fromAtlas.{w} A).GluedTotalSpace ↦
          (⟨q.1, ⟨q.2.proj, e q.1 q.2.proj q.2.2⟩⟩ : A.GluedTotalSpace)) :=
        continuous_sigma fun _ ↦ continuous_sigmaMk.comp continuous_induced_dom
      refine (A.totalSpaceHomeomorph.continuous.comp
        (hsigma.comp (fromAtlas.{w} A).totalSpaceHomeomorph.symm.continuous)).congr fun p ↦ ?_
      rw [Function.comp_apply, Function.comp_apply,
        (fromAtlas.{w} A).totalSpaceHomeomorph_symm_apply, A.totalSpaceHomeomorph_apply]; rfl
    continuous_invFun := by
      have hsigma : Continuous (fun q : A.GluedTotalSpace ↦
          (⟨q.1, ⟨q.2.proj, (e q.1 q.2.proj).symm q.2.2⟩⟩ :
            (fromAtlas.{w} A).GluedTotalSpace)) :=
        continuous_sigma fun n ↦ continuous_sigmaMk.comp <| continuous_induced_rng.2 <|
          continuous_id.congr fun ⟨proj, snd⟩ ↦
            (congrArg (TotalSpace.mk proj) ((e n proj).apply_symm_apply snd)).symm
      refine ((fromAtlas.{w} A).totalSpaceHomeomorph.continuous.comp
        (hsigma.comp A.totalSpaceHomeomorph.symm.continuous)).congr fun p ↦ ?_
      rw [Function.comp_apply, Function.comp_apply, A.totalSpaceHomeomorph_symm_apply,
        (fromAtlas.{w} A).totalSpaceHomeomorph_apply]; rfl }

@[simp] theorem fromAtlasHomeomorph_apply [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (fromAtlas.{w} A).Fiber) :
    fromAtlasHomeomorph.{w} A p = ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.2⟩ :=
  (rfl)
@[simp] theorem fromAtlasHomeomorph_symm_apply [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit A.Fiber) :
    (fromAtlasHomeomorph.{w} A).symm p =
      ⟨p.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).symm p.2⟩ := (rfl)

variable (𝕜 X) in
/-- Additive reconstruction functor `FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X` when
`[Small.{w} 𝕜]`. -/
@[expose] noncomputable def fromAtlasFunctor [Small.{w} 𝕜] :
    FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X where
  obj A := fromAtlas.{w} A
  map {A D} g :=
    { fiberMap x := (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
        ((g.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap)
      continuous_totalSpaceMap := ((fromAtlasHomeomorph.{w} D).symm.continuous.comp
        (g.continuous_totalSpaceMap.comp (fromAtlasHomeomorph.{w} A).continuous)).congr fun p ↦ by
        rw [Function.comp_apply, Function.comp_apply, fromAtlasHomeomorph_apply,
          fromAtlasHomeomorph_symm_apply]; rfl }
  map_id A := hom_ext fun x ↦
    LinearMap.ext (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm_apply_apply
  map_comp {_ D C} f g := hom_ext fun x ↦ LinearMap.ext fun _ ↦
    (congrArg (Shrink.continuousLinearEquiv 𝕜 (C.Fiber x)).symm (congrArg (g.fiberMap x)
      ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).apply_symm_apply _))).symm

@[simp] theorem fromAtlasFunctor_obj [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlasFunctor.{w} 𝕜 X).obj A = fromAtlas.{w} A := (rfl)
@[simp] theorem fromAtlasFunctor_map_fiberMap [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X} (g : A ⟶ D)
    (x : X) (v : (fromAtlas.{w} A).Fiber x) :
    ((fromAtlasFunctor.{w} 𝕜 X).map g).fiberMap x v =
      (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
        (g.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) v)) := (rfl)

instance [Small.{w} 𝕜] : (fromAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {_ D f g} := hom_ext fun x ↦ LinearMap.ext fun _ ↦
    (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.map_add (f.fiberMap x _) (g.fiberMap x _)

/-- Component isomorphism `E ≅ fromAtlas E.toAtlas` of the unit of `atlasEquivalence`. -/
noncomputable def atlasUnitApp [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    E ≅ fromAtlas.{w} E.toAtlas :=
  isoMk (fun x ↦ ((E.reconstructionFiberEquiv x).symm.trans
      (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm).toLinearEquiv)
    (((fromAtlasHomeomorph.{w} E.toAtlas).symm.continuous.comp
      E.reconstructionHomeomorph.symm.continuous).congr fun p ↦ by
      rw [Function.comp_apply, E.reconstructionHomeomorph_symm_apply,
        fromAtlasHomeomorph_symm_apply]; rfl)
    ((E.reconstructionHomeomorph.continuous.comp
      (fromAtlasHomeomorph.{w} E.toAtlas).continuous).congr fun p ↦ by
      rw [Function.comp_apply, fromAtlasHomeomorph_apply, E.reconstructionHomeomorph_apply]; rfl)

@[simp] theorem atlasUnitApp_hom_fiberMap [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) (x : X)
    (v : E.Fiber x) :
    (atlasUnitApp.{w} E).hom.fiberMap x v =
      (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm
        ((E.reconstructionFiberEquiv x).symm v) :=
  DFunLike.congr_fun (fiberMap_isoMk_hom (F := fromAtlas.{w} E.toAtlas) _ _ _ x) v
@[simp] theorem atlasUnitApp_inv_fiberMap [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) (x : X)
    (v : (fromAtlas.{w} E.toAtlas).Fiber x) :
    (atlasUnitApp.{w} E).inv.fiberMap x v =
      E.reconstructionFiberEquiv x (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x) v) :=
  DFunLike.congr_fun (fiberMap_isoMk_inv (F := fromAtlas.{w} E.toAtlas) _ _ _ x) v

/-- Component isomorphism `(fromAtlas A).toAtlas ≅ A` of the counit of `atlasEquivalence`. -/
noncomputable def atlasCounitApp [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlas.{w} A).toAtlas ≅ A :=
  FiniteRankAtlas.isoMk (fun x ↦ (((fromAtlas.{w} A).reconstructionFiberEquiv x).trans
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x))).toLinearEquiv)
    (((fromAtlasHomeomorph.{w} A).continuous.comp
      (fromAtlas.{w} A).reconstructionHomeomorph.continuous).congr fun p ↦ by
      rw [Function.comp_apply, (fromAtlas.{w} A).reconstructionHomeomorph_apply,
        fromAtlasHomeomorph_apply]; rfl)
    (((fromAtlas.{w} A).reconstructionHomeomorph.symm.continuous.comp
      (fromAtlasHomeomorph.{w} A).symm.continuous).congr fun p ↦ by
      rw [Function.comp_apply, fromAtlasHomeomorph_symm_apply,
        (fromAtlas.{w} A).reconstructionHomeomorph_symm_apply]; rfl)

@[simp] theorem atlasCounitApp_hom_fiberMap [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (fromAtlas.{w} A).toAtlas.Fiber x) :
    (atlasCounitApp.{w} A).hom.fiberMap x v =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)
        ((fromAtlas.{w} A).reconstructionFiberEquiv x v) := by
  rw [atlasCounitApp, FiniteRankAtlas.fiberMap_isoMk_hom]; rfl
@[simp] theorem atlasCounitApp_inv_fiberMap [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X)
    (v : A.Fiber x) :
    (atlasCounitApp.{w} A).inv.fiberMap x v =
      ((fromAtlas.{w} A).reconstructionFiberEquiv x).symm
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm v) := by
  rw [atlasCounitApp, FiniteRankAtlas.fiberMap_isoMk_inv]; rfl

variable (𝕜 X) in
/-- Unit natural isomorphism `𝟭 _ ≅ toAtlasFunctor ⋙ fromAtlasFunctor`. -/
noncomputable def atlasUnitIso [Small.{w} 𝕜] :
    𝟭 (FiniteRankBundle.{w} 𝕜 X) ≅ toAtlasFunctor.{w} 𝕜 X ⋙ fromAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (fun E ↦ atlasUnitApp.{w} E) fun {E F} f ↦
    hom_ext fun x ↦ LinearMap.ext fun (v : E.Fiber x) ↦ by
      rw [fiberMap_comp, fiberMap_comp, LinearMap.comp_apply, LinearMap.comp_apply]
      dsimp only [Functor.id_map, Functor.comp_map]
      let sE := Shrink.continuousLinearEquiv.{w} 𝕜 (E.toAtlas.Fiber x)
      let sF := Shrink.continuousLinearEquiv.{w} 𝕜 (F.toAtlas.Fiber x)
      let k := ((fromAtlasFunctor.{w} 𝕜 X).map ((toAtlasFunctor.{w} 𝕜 X).map f)).fiberMap x
      exact (atlasUnitApp_hom_fiberMap F x (f.fiberMap x v)).trans
        ((congrArg (fun w ↦ sF.symm ((F.reconstructionFiberEquiv x).symm (f.fiberMap x w)))
          (((E.reconstructionFiberEquiv x).apply_symm_apply v).symm.trans
            (congrArg (E.reconstructionFiberEquiv x) (sE.apply_symm_apply _).symm))).trans
          (congrArg k (atlasUnitApp_hom_fiberMap E x v)).symm)

@[simp] theorem atlasUnitIso_hom_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).hom.app E = (atlasUnitApp.{w} E).hom := (rfl)
@[simp] theorem atlasUnitIso_inv_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).inv.app E = (atlasUnitApp.{w} E).inv := (rfl)

variable (𝕜 X) in
/-- Counit natural isomorphism `fromAtlasFunctor ⋙ toAtlasFunctor ≅ 𝟭 _`. -/
noncomputable def atlasCounitIso [Small.{w} 𝕜] :
    fromAtlasFunctor.{w} 𝕜 X ⋙ toAtlasFunctor.{w} 𝕜 X ≅ 𝟭 (FiniteRankAtlas 𝕜 X) :=
  NatIso.ofComponents (fun A ↦ atlasCounitApp.{w} A) fun {A D} g ↦
    FiniteRankAtlas.hom_ext (A := (fromAtlas.{w} A).toAtlas) (D := D) fun x ↦
      LinearMap.ext fun v ↦ by
        let sD := Shrink.continuousLinearEquiv.{w} 𝕜 (D.Fiber x)
        let rD := (fromAtlas.{w} D).reconstructionFiberEquiv x
        have hlhs := DFunLike.congr_fun (FiniteRankAtlas.fiberMap_comp
          ((toAtlasFunctor.{w} 𝕜 X).map ((fromAtlasFunctor.{w} 𝕜 X).map g))
          (atlasCounitApp.{w} D).hom x) v
        have hrhs := DFunLike.congr_fun
          (FiniteRankAtlas.fiberMap_comp (atlasCounitApp.{w} A).hom g x) v
        refine hlhs.trans ((atlasCounitApp_hom_fiberMap D x _).trans ?_)
        exact ((congrArg sD (rD.apply_symm_apply _)).trans (sD.apply_symm_apply _)).trans
          ((congrArg (g.fiberMap x) (atlasCounitApp_hom_fiberMap A x v)).symm.trans hrhs.symm)

@[simp] theorem atlasCounitIso_hom_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).hom.app A = (atlasCounitApp.{w} A).hom := (rfl)
@[simp] theorem atlasCounitIso_inv_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).inv.app A = (atlasCounitApp.{w} A).inv := (rfl)

variable (𝕜 X) in
/-- Explicit equivalence of categories `FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X` whenever
`[Small.{w} 𝕜]` holds. -/
noncomputable def atlasEquivalence [Small.{w} 𝕜] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X :=
  { functor := toAtlasFunctor.{w} 𝕜 X, inverse := fromAtlasFunctor.{w} 𝕜 X,
    unitIso := atlasUnitIso.{w} 𝕜 X, counitIso := atlasCounitIso.{w} 𝕜 X,
    functor_unitIso_comp E := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦ by
      have hcomp := DFunLike.congr_fun (FiniteRankAtlas.fiberMap_comp
        ((toAtlasFunctor.{w} 𝕜 X).map ((atlasUnitIso.{w} 𝕜 X).hom.app E))
        ((atlasCounitIso.{w} 𝕜 X).hom.app ((toAtlasFunctor.{w} 𝕜 X).obj E)) x) v
      let sE := Shrink.continuousLinearEquiv.{w} 𝕜 (E.toAtlas.Fiber x)
      let rE := (fromAtlas.{w} E.toAtlas).reconstructionFiberEquiv x
      have h1 := atlasCounitApp_hom_fiberMap E.toAtlas x
        (((toAtlasFunctor.{w} 𝕜 X).map (atlasUnitApp.{w} E).hom).fiberMap x v)
      have h2 := (rE.apply_symm_apply
        ((atlasUnitApp.{w} E).hom.fiberMap x (E.reconstructionFiberEquiv x v))).trans
        (atlasUnitApp_hom_fiberMap E x (E.reconstructionFiberEquiv x v))
      exact hcomp.trans (h1.trans ((congrArg sE h2).trans
        ((sE.apply_symm_apply _).trans ((E.reconstructionFiberEquiv x).symm_apply_apply v)))) }

instance [Small.{w} 𝕜] : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_functor
instance [Small.{w} 𝕜] : (fromAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_inverse

end FromAtlas

/-! ### Universe-lifting functor and change-of-universe equivalence -/

section UniversePolymorphism

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Lift the fibres of `E : FiniteRankBundle.{w} 𝕜 X` to `Type (max w w')` via `ULift`. -/
@[expose] noncomputable def ulift (E : FiniteRankBundle.{w} 𝕜 X) :
    FiniteRankBundle.{max w w'} 𝕜 X :=
  let e (n : ℕ) (x : {x : X // E.rank x = n}) :
      ULift.{w'} (E.Fiber x.1) ≃L[𝕜] E.StratumFiber n x := ContinuousLinearEquiv.ulift
  letI τ (n : ℕ) : TopologicalSpace
      (TotalSpace (Fin n → 𝕜) fun x : {x : X // E.rank x = n} ↦ ULift.{w'} (E.Fiber x.1)) :=
    totalSpaceInduced (Fin n → 𝕜) (E := E.StratumFiber n) (e n)
  letI fb (n : ℕ) :
      FiberBundle (Fin n → 𝕜) fun x : {x : X // E.rank x = n} ↦ ULift.{w'} (E.Fiber x.1) :=
    FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E.StratumFiber n) (e n) ⟨rfl⟩
  { rank := E.rank, Fiber x := ULift.{w'} (E.Fiber x), topologicalSpaceStratum := τ,
    fiberBundleStratum := fb, vectorBundleStratum n :=
      VectorBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E.StratumFiber n) (e n) ⟨rfl⟩ }

@[simp] theorem rank_ulift (E : FiniteRankBundle.{w} 𝕜 X) : (E.ulift.{w, w'}).rank = E.rank := (rfl)
@[simp] theorem fiber_ulift (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (E.ulift.{w, w'}).Fiber x = ULift.{w'} (E.Fiber x) := (rfl)

/-- Homeomorphism over `X` between the global total spaces of `E.ulift` and `E`. -/
def uliftHomeomorph (E : FiniteRankBundle.{w} 𝕜 X) :
    TotalSpace Unit (E.ulift.{w, w'}).Fiber ≃ₜ TotalSpace Unit E.Fiber where
  toFun p := ⟨p.proj, p.2.down⟩
  invFun p := ⟨p.proj, ULift.up p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun := by
    have hsigma : Continuous (fun q : (E.ulift.{w, w'}).GluedTotalSpace ↦
        (⟨q.1, ⟨q.2.proj, q.2.2.down⟩⟩ : E.GluedTotalSpace)) :=
      continuous_sigma fun _ ↦ continuous_sigmaMk.comp continuous_induced_dom
    refine (E.totalSpaceHomeomorph.continuous.comp
      (hsigma.comp (E.ulift.{w, w'}).totalSpaceHomeomorph.symm.continuous)).congr fun p ↦ ?_
    rw [Function.comp_apply, Function.comp_apply,
      (E.ulift.{w, w'}).totalSpaceHomeomorph_symm_apply, E.totalSpaceHomeomorph_apply]
  continuous_invFun := by
    have hsigma : Continuous (fun q : E.GluedTotalSpace ↦
        (⟨q.1, ⟨q.2.proj, ULift.up q.2.2⟩⟩ : (E.ulift.{w, w'}).GluedTotalSpace)) :=
      continuous_sigma fun n ↦ continuous_sigmaMk.comp
        (continuous_induced_rng.2 (continuous_id :
          Continuous (id : TotalSpace (Fin n → 𝕜) (E.StratumFiber n) → _)))
    refine ((E.ulift.{w, w'}).totalSpaceHomeomorph.continuous.comp
      (hsigma.comp E.totalSpaceHomeomorph.symm.continuous)).congr fun p ↦ ?_
    rw [Function.comp_apply, Function.comp_apply, E.totalSpaceHomeomorph_symm_apply,
      (E.ulift.{w, w'}).totalSpaceHomeomorph_apply]

@[simp] theorem uliftHomeomorph_apply (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit (E.ulift.{w, w'}).Fiber) :
    E.uliftHomeomorph.{w, w'} p = ⟨p.proj, p.2.down⟩ := (rfl)
@[simp] theorem uliftHomeomorph_symm_apply (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit E.Fiber) :
    (E.uliftHomeomorph.{w, w'}).symm p = ⟨p.proj, ULift.up p.2⟩ := (rfl)

variable (𝕜 X) in
/-- Additive, full, and faithful universe-lifting functor on genuine variable-rank bundles. -/
@[expose] noncomputable def uliftFunctor :
    FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankBundle.{max w w'} 𝕜 X where
  obj E := E.ulift.{w, w'}
  map {E F} f :=
    { fiberMap x :=
        (ULift.moduleEquiv : ULift.{w'} (F.Fiber x) ≃ₗ[𝕜] F.Fiber x).symm.toLinearMap.comp
          ((f.fiberMap x).comp
            (ULift.moduleEquiv : ULift.{w'} (E.Fiber x) ≃ₗ[𝕜] E.Fiber x).toLinearMap)
      continuous_totalSpaceMap := by
        refine ((F.uliftHomeomorph.{w, w'}).symm.continuous.comp
          (f.continuous_totalSpaceMap.comp (E.uliftHomeomorph.{w, w'}).continuous)).congr
          fun _ ↦ rfl }
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp] theorem uliftFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctor.{w, w'} 𝕜 X).obj E = E.ulift.{w, w'} := (rfl)
@[simp] theorem uliftFunctor_map_fiberMap {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (x : X)
    (v : ULift.{w'} (E.Fiber x)) :
    ((uliftFunctor.{w, w'} 𝕜 X).map f).fiberMap x v = ULift.up (f.fiberMap x v.down) := (rfl)

instance : (uliftFunctor.{w, w'} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
instance : (uliftFunctor.{w, w'} 𝕜 X).Faithful where
  map_injective {E F} _ _ h := hom_ext fun x ↦ LinearMap.ext fun v ↦ congrArg ULift.down
    (congrArg (fun k : E.ulift.{w, w'} ⟶ F.ulift.{w, w'} ↦ k.fiberMap x (ULift.up v)) h)
instance : (uliftFunctor.{w, w'} 𝕜 X).Full where
  map_surjective {E F} g := by
    refine ⟨⟨fun x ↦
        (ULift.moduleEquiv : ULift.{w'} (F.Fiber x) ≃ₗ[𝕜] F.Fiber x).toLinearMap.comp
          ((g.fiberMap x).comp
            (ULift.moduleEquiv : ULift.{w'} (E.Fiber x) ≃ₗ[𝕜] E.Fiber x).symm.toLinearMap),
      ((F.uliftHomeomorph.{w, w'}).continuous.comp
        (g.continuous_totalSpaceMap.comp (E.uliftHomeomorph.{w, w'}).symm.continuous)).congr
        fun _ ↦ rfl⟩, hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl⟩

/-- Component isomorphism `(E.ulift).toAtlas ≅ E.toAtlas` comparing coordinate presentations. -/
noncomputable def uliftToAtlasApp (E : FiniteRankBundle.{w} 𝕜 X) :
    (E.ulift.{w, w'}).toAtlas ≅ E.toAtlas :=
  FiniteRankAtlas.isoMk
    (fun x ↦ (((E.ulift.{w, w'}).reconstructionFiberEquiv x).trans
      ((ContinuousLinearEquiv.ulift : ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).trans
        (E.reconstructionFiberEquiv x).symm)).toLinearEquiv)
    ((E.reconstructionHomeomorph.symm.continuous.comp ((E.uliftHomeomorph.{w, w'}).continuous.comp
      (E.ulift.{w, w'}).reconstructionHomeomorph.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply,
        (E.ulift.{w, w'}).reconstructionHomeomorph_apply, uliftHomeomorph_apply,
        E.reconstructionHomeomorph_symm_apply]; rfl)
    (((E.ulift.{w, w'}).reconstructionHomeomorph.symm.continuous.comp
      ((E.uliftHomeomorph.{w, w'}).symm.continuous.comp
        E.reconstructionHomeomorph.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_apply,
        uliftHomeomorph_symm_apply, (E.ulift.{w, w'}).reconstructionHomeomorph_symm_apply]; rfl)

@[simp] theorem uliftToAtlasApp_hom_fiberMap (E : FiniteRankBundle.{w} 𝕜 X) (x : X)
    (v : (E.ulift.{w, w'}).toAtlas.Fiber x) :
    (uliftToAtlasApp.{w, w'} E).hom.fiberMap x v =
      (E.reconstructionFiberEquiv x).symm
        (((E.ulift.{w, w'}).reconstructionFiberEquiv x v).down) := by
  rw [uliftToAtlasApp, FiniteRankAtlas.fiberMap_isoMk_hom]; rfl
@[simp] theorem uliftToAtlasApp_inv_fiberMap (E : FiniteRankBundle.{w} 𝕜 X) (x : X)
    (v : E.toAtlas.Fiber x) :
    (uliftToAtlasApp.{w, w'} E).inv.fiberMap x v =
      ((E.ulift.{w, w'}).reconstructionFiberEquiv x).symm
        (ULift.up (E.reconstructionFiberEquiv x v)) := by
  rw [uliftToAtlasApp, FiniteRankAtlas.fiberMap_isoMk_inv]; rfl

variable (𝕜 X) in
/-- Natural isomorphism `uliftFunctor ⋙ toAtlasFunctor ≅ toAtlasFunctor`. -/
noncomputable def uliftFunctorCompToAtlasIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅ toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (fun E ↦ uliftToAtlasApp.{w, w'} E) fun {E F} f ↦
    FiniteRankAtlas.hom_ext (A := (E.ulift.{w, w'}).toAtlas) (D := F.toAtlas) fun x ↦
      LinearMap.ext fun v ↦ by
        let rF' := (F.ulift.{w, w'}).reconstructionFiberEquiv x
        let k := ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x
        have hlhs := DFunLike.congr_fun (FiniteRankAtlas.fiberMap_comp
          ((toAtlasFunctor.{max w w'} 𝕜 X).map ((uliftFunctor.{w, w'} 𝕜 X).map f))
          (uliftToAtlasApp.{w, w'} F).hom x) v
        have hrhs := DFunLike.congr_fun (FiniteRankAtlas.fiberMap_comp
          (uliftToAtlasApp.{w, w'} E).hom ((toAtlasFunctor.{w} 𝕜 X).map f) x) v
        refine hlhs.trans ((uliftToAtlasApp_hom_fiberMap F x _).trans ?_)
        refine (congrArg (fun u ↦ (F.reconstructionFiberEquiv x).symm u.down)
          (rF'.apply_symm_apply _)).trans ?_
        exact (congrArg (fun w ↦ (F.reconstructionFiberEquiv x).symm (f.fiberMap x w))
          ((E.reconstructionFiberEquiv x).apply_symm_apply _).symm).trans
          ((congrArg k (uliftToAtlasApp_hom_fiberMap E x v)).symm.trans hrhs.symm)

@[simp] theorem uliftFunctorCompToAtlasIso_hom_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).hom.app E = (uliftToAtlasApp.{w, w'} E).hom := (rfl)
@[simp] theorem uliftFunctorCompToAtlasIso_inv_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).inv.app E = (uliftToAtlasApp.{w, w'} E).inv := (rfl)

instance [Small.{w} 𝕜] : (uliftFunctor.{w, w'} 𝕜 X).IsEquivalence := by
  have : Small.{max w w'} 𝕜 := small_lift.{v, w', w} 𝕜
  have : (uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X).IsEquivalence :=
    Functor.isEquivalence_of_iso (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).symm
  exact Functor.isEquivalence_of_comp_right (uliftFunctor.{w, w'} 𝕜 X)
    (toAtlasFunctor.{max w w'} 𝕜 X)

variable (𝕜 X) in
/-- Equivalence `FiniteRankBundle.{w₁} 𝕜 X ≌ FiniteRankBundle.{w₂} 𝕜 X` under `[Small.{w₁} 𝕜]` and
`[Small.{w₂} 𝕜]`. -/
noncomputable def changeUniverseEquivalence [Small.{w₁} 𝕜] [Small.{w₂} 𝕜] :
    FiniteRankBundle.{w₁} 𝕜 X ≌ FiniteRankBundle.{w₂} 𝕜 X :=
  (atlasEquivalence.{w₁} 𝕜 X).trans (atlasEquivalence.{w₂} 𝕜 X).symm

end UniversePolymorphism

end TauCeti.FiniteRankBundle
