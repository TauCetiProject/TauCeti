/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Topology.Instances.Shrink
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Isomorphism
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# Small-model comparison and equivalence for variable-rank vector bundles

This file relates the universe-polymorphic category `TauCeti.FiniteRankBundle.{w} 𝕜 X` of genuine
variable-rank topological `𝕜`-vector bundles over `X` to the small coordinate category
`TauCeti.FiniteRankAtlas 𝕜 X`:

1. **Unconditional fully faithful comparison (`TauCeti.FiniteRankBundle.toAtlas`).**
   For every fibre universe `w`, every nontrivially normed field `𝕜 : Type v`, and every topological
   space `X : Type u` (without assuming `Small.{w} 𝕜`, `CompleteSpace 𝕜`, compactness, or bounded
   rank), `toAtlas 𝕜 X : FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X` sends a bundle `B` to
   `FiniteRankAtlas.ofBundles 𝕜 B.rank B.StratumFiber` and conjugates morphisms by the preferred
   coordinate equivalences `B.continuousLinearEquivCoord`. Because `B.toAtlasTotalSpaceHomeomorph`
   identifies the glued total spaces over `X`, `toAtlas 𝕜 X` is additive, `Full`, and `Faithful`.
   Consequently:
   * `FiniteRankBundle.{w} 𝕜 X` is unconditionally `LocallySmall.{max u v}` and
     `EssentiallySmall.{max u v}` (in particular `EssentiallySmall.{u}` over `ℝ` or `ℂ`, where
     `v = 0`);
   * a morphism in `FiniteRankBundle.{w} 𝕜 X` is an isomorphism if and only if it is bijective on
     every fibre (`TauCeti.FiniteRankBundle.isIso_iff_bijective`), for arbitrary `w` and without
     assuming `CompleteSpace 𝕜`.

2. **Explicit equivalence and change of fibre universe (`TauCeti.FiniteRankBundle.atlasEquivalence`,
   `TauCeti.FiniteRankBundle.changeUniverseEquivalence`).**
   Whenever `[Small.{w} 𝕜]` holds (which Mathlib synthesizes automatically for `𝕜 = ℝ` and `𝕜 = ℂ`
   in every universe `w`, as well as for any `𝕜 : Type v` when `w = v`),
   `TauCeti.FiniteRankAtlas.toBundle.{w}` reconstructs a `FiniteRankBundle.{w} 𝕜 X` with fibres
   `Shrink.{w} (A.Fiber x)` by transporting the stratum core bundles along
   `Shrink.continuousLinearEquiv`. This yields an explicit equivalence of categories
   `atlasEquivalence.{w} 𝕜 X : FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X` (without requiring
   `CompleteSpace 𝕜`) and a universe-change equivalence
   `changeUniverseEquivalence.{w, w'} 𝕜 X : FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankBundle.{w'} 𝕜 X`.
-/

public section

open Bundle CategoryTheory Topology VectorBundleCore

namespace TauCeti

universe w w' u v

namespace FiniteRankBundle

section ToAtlas

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- The small coordinate atlas extracted from the clopen rank strata of `B`. -/
-- Expose the wrapper so `(B.toAtlasObj).rank` reduces to `B.rank` in dependent coordinate fibres.
@[expose]
noncomputable def toAtlasObj (B : FiniteRankBundle.{w} 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 B.rank B.StratumFiber

@[simp]
theorem rank_toAtlasObj (B : FiniteRankBundle.{w} 𝕜 X) :
    B.toAtlasObj.rank = B.rank := (rfl)

private theorem pointIndexedCoreFiberEquiv_eq_coord_symm (B : FiniteRankBundle.{w} 𝕜 X)
    (x : X) (v : Fin (B.rank x) → 𝕜) :
    pointIndexedCoreFiberEquiv 𝕜 (Fin (B.rank x) → 𝕜) (B.StratumFiber (B.rank x)) ⟨x, rfl⟩ v =
      (B.continuousLinearEquivCoord x).symm v := by
  rw [B.continuousLinearEquivCoord_eq x, pointIndexedCoreFiberEquiv_apply]
  rfl

private theorem pointIndexedCoreFiberEquiv_symm_eq_coord (B : FiniteRankBundle.{w} 𝕜 X)
    (x : X) (v : B.Fiber x) :
    (pointIndexedCoreFiberEquiv 𝕜 (Fin (B.rank x) → 𝕜)
      (B.StratumFiber (B.rank x)) ⟨x, rfl⟩).symm v =
      B.continuousLinearEquivCoord x v := by
  rw [B.continuousLinearEquivCoord_eq x, pointIndexedCoreFiberEquiv_symm_apply]
  rfl

/-- Homeomorphism over `X` from the reconstructed total space of `B.toAtlasObj` to the glued total
space of `B`, acting on fibre `x` by `(B.continuousLinearEquivCoord x).symm`. -/
noncomputable def toAtlasTotalSpaceHomeomorph (B : FiniteRankBundle.{w} 𝕜 X) :
    TotalSpace Unit B.toAtlasObj.Fiber ≃ₜ TotalSpace Unit B.Fiber :=
  (FiniteRankAtlas.reconstructionHomeomorph 𝕜 B.rank B.StratumFiber).trans
    B.gluedTotalSpaceHomeomorph

@[simp]
theorem toAtlasTotalSpaceHomeomorph_apply (B : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit B.toAtlasObj.Fiber) :
    B.toAtlasTotalSpaceHomeomorph p =
      ⟨p.proj, (B.continuousLinearEquivCoord p.proj).symm p.2⟩ :=
  (congrArg B.gluedTotalSpaceHomeomorph
    (FiniteRankAtlas.reconstructionHomeomorph_apply 𝕜 B.rank B.StratumFiber p)).trans
    ((B.gluedTotalSpaceHomeomorph_apply _).trans
      (congrArg (TotalSpace.mk' Unit p.proj)
        (pointIndexedCoreFiberEquiv_eq_coord_symm B p.proj p.2)))

@[simp]
theorem toAtlasTotalSpaceHomeomorph_symm_apply (B : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit B.Fiber) :
    B.toAtlasTotalSpaceHomeomorph.symm p =
      ⟨p.proj, B.continuousLinearEquivCoord p.proj p.2⟩ :=
  (congrArg (FiniteRankAtlas.reconstructionHomeomorph 𝕜 B.rank B.StratumFiber).symm
    (B.gluedTotalSpaceHomeomorph_symm_apply p)).trans
    ((FiniteRankAtlas.reconstructionHomeomorph_symm_apply 𝕜 B.rank B.StratumFiber
      (B.rank p.proj) ⟨⟨p.proj, rfl⟩, p.2⟩).trans
      ((B.toAtlasObj.totalSpaceHomeomorph_apply _).trans
        (congrArg (TotalSpace.mk' Unit p.proj)
          (pointIndexedCoreFiberEquiv_symm_eq_coord B p.proj p.2))))

/-- Action of `toAtlas` on bundle morphisms, conjugating each fibre map by the preferred coordinate
equivalences. -/
noncomputable def toAtlasMap {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X} (f : B₁ ⟶ B₂) :
    B₁.toAtlasObj ⟶ B₂.toAtlasObj where
  fiberMap x := (B₂.continuousLinearEquivCoord x).toLinearMap.comp
    ((f.fiberMap x).comp (B₁.continuousLinearEquivCoord x).symm.toLinearMap)
  continuous_totalSpaceMap := by
    refine (B₂.toAtlasTotalSpaceHomeomorph.symm.continuous.comp
      (f.continuous_totalSpaceMap.comp B₁.toAtlasTotalSpaceHomeomorph.continuous)).congr ?_
    rintro ⟨x, v⟩
    exact (congrArg (fun q : TotalSpace Unit B₁.Fiber ↦
      B₂.toAtlasTotalSpaceHomeomorph.symm ⟨q.proj, f.fiberMap q.proj q.2⟩)
      (B₁.toAtlasTotalSpaceHomeomorph_apply ⟨x, v⟩)).trans
      (B₂.toAtlasTotalSpaceHomeomorph_symm_apply _)

@[simp]
theorem fiberMap_toAtlasMap {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X} (f : B₁ ⟶ B₂) (x : X) :
    (toAtlasMap f).fiberMap x =
      (B₂.continuousLinearEquivCoord x).toLinearMap.comp
        ((f.fiberMap x).comp (B₁.continuousLinearEquivCoord x).symm.toLinearMap) := (rfl)

theorem fiberMap_toAtlasMap_apply {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X} (f : B₁ ⟶ B₂) (x : X)
    (v : B₁.toAtlasObj.Fiber x) :
    (toAtlasMap f).fiberMap x v =
      B₂.continuousLinearEquivCoord x
        (f.fiberMap x ((B₁.continuousLinearEquivCoord x).symm v)) := (rfl)

@[simp]
theorem toAtlasMap_id (B : FiniteRankBundle.{w} 𝕜 X) :
    toAtlasMap (𝟙 B) = 𝟙 B.toAtlasObj :=
  FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦
    (B.continuousLinearEquivCoord x).apply_symm_apply v

@[simp]
theorem toAtlasMap_comp {B₁ B₂ B₃ : FiniteRankBundle.{w} 𝕜 X} (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃) :
    toAtlasMap (f ≫ g) = toAtlasMap f ≫ toAtlasMap g :=
  FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    congrArg (fun y ↦ B₃.continuousLinearEquivCoord x (g.fiberMap x y))
      ((B₂.continuousLinearEquivCoord x).symm_apply_apply _).symm

variable (𝕜 X) in
/-- Fully faithful additive functor extracting small point-indexed coordinate atlases from
variable-rank vector bundles in any fibre universe `w`. -/
-- Expose the object map so `((toAtlas 𝕜 X).obj B).Fiber x` reduces to `Fin (B.rank x) → 𝕜`.
@[expose, pp_with_univ]
noncomputable def toAtlas : FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj := toAtlasObj
  map := toAtlasMap
  map_id := toAtlasMap_id
  map_comp := toAtlasMap_comp

@[simp]
theorem toAtlas_obj (B : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlas.{w} 𝕜 X).obj B = B.toAtlasObj := (rfl)

@[simp]
theorem toAtlas_map {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X} (f : B₁ ⟶ B₂) :
    (toAtlas.{w} 𝕜 X).map f = toAtlasMap f := (rfl)

instance : (toAtlas.{w} 𝕜 X).Additive where
  map_add {_ B₂ _ _} := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    map_add (B₂.continuousLinearEquivCoord x) _ _

instance : (toAtlas.{w} 𝕜 X).Faithful where
  map_injective {B₁ B₂} f g h := hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    have hv : B₂.continuousLinearEquivCoord x
          (f.fiberMap x ((B₁.continuousLinearEquivCoord x).symm
            (B₁.continuousLinearEquivCoord x v))) =
        B₂.continuousLinearEquivCoord x
          (g.fiberMap x ((B₁.continuousLinearEquivCoord x).symm
            (B₁.continuousLinearEquivCoord x v))) :=
      congrArg (fun k ↦ k.fiberMap x (B₁.continuousLinearEquivCoord x v)) h
    rw [ContinuousLinearEquiv.symm_apply_apply] at hv
    exact (B₂.continuousLinearEquivCoord x).injective hv

/-- Inverse to `toAtlasMap` on morphisms, transporting an atlas morphism back along the preferred
coordinate equivalences of `B₁` and `B₂`. -/
noncomputable def ofAtlasMap {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X}
    (g : B₁.toAtlasObj ⟶ B₂.toAtlasObj) : B₁ ⟶ B₂ where
  fiberMap x := (B₂.continuousLinearEquivCoord x).symm.toLinearMap.comp
    ((g.fiberMap x).comp (B₁.continuousLinearEquivCoord x).toLinearMap)
  continuous_totalSpaceMap := by
    refine (B₂.toAtlasTotalSpaceHomeomorph.continuous.comp
      (g.continuous_totalSpaceMap.comp B₁.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr ?_
    rintro ⟨x, v⟩
    exact (congrArg (fun q : TotalSpace Unit B₁.toAtlasObj.Fiber ↦
      B₂.toAtlasTotalSpaceHomeomorph ⟨q.proj, g.fiberMap q.proj q.2⟩)
      (B₁.toAtlasTotalSpaceHomeomorph_symm_apply ⟨x, v⟩)).trans
      (B₂.toAtlasTotalSpaceHomeomorph_apply _)

@[simp]
theorem fiberMap_ofAtlasMap_apply {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X}
    (g : B₁.toAtlasObj ⟶ B₂.toAtlasObj) (x : X) (v : B₁.Fiber x) :
    (ofAtlasMap g).fiberMap x v =
      (B₂.continuousLinearEquivCoord x).symm
        (g.fiberMap x (B₁.continuousLinearEquivCoord x v)) := (rfl)

@[simp]
theorem toAtlasMap_ofAtlasMap {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X}
    (g : B₁.toAtlasObj ⟶ B₂.toAtlasObj) :
    toAtlasMap (ofAtlasMap g) = g :=
  FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦
    ((B₂.continuousLinearEquivCoord x).apply_symm_apply _).trans
      (congrArg (g.fiberMap x) ((B₁.continuousLinearEquivCoord x).apply_symm_apply v))

instance : (toAtlas.{w} 𝕜 X).Full where
  map_surjective g := ⟨ofAtlasMap g, toAtlasMap_ofAtlasMap g⟩

/-- `FiniteRankBundle.{w} 𝕜 X` is unconditionally locally `max u v`-small for every fibre universe
`w`. In particular, for `𝕜 = ℝ` or `𝕜 = ℂ` (`v = 0`), it is `LocallySmall.{u}`. -/
instance : LocallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  locallySmall_of_faithful (toAtlas.{w} 𝕜 X)

/-- `FiniteRankBundle.{w} 𝕜 X` is unconditionally `EssentiallySmall.{max u v}` for every fibre
universe `w`. In particular, for `𝕜 = ℝ` or `𝕜 = ℂ` (`v = 0`), it is `EssentiallySmall.{u}`. -/
instance : EssentiallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlas.{w} 𝕜 X)

section Isomorphism

variable {B₁ B₂ : FiniteRankBundle.{w} 𝕜 X}

/-- Over any nontrivially normed field, a morphism of variable-rank vector bundles in any fibre
universe `w` is an isomorphism if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective (f : B₁ ⟶ B₂) :
    IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun hf x ↦ ((fiberFunctor x).mapIso (asIso f)).toLinearEquiv.bijective, fun hf ↦ ?_⟩
  have : IsIso ((toAtlas.{w} 𝕜 X).map f) :=
    (FiniteRankAtlas.isIso_iff_bijective _).2 fun x ↦ by
      have hfn : ⇑(((toAtlas.{w} 𝕜 X).map f).fiberMap x) =
          ⇑(B₂.continuousLinearEquivCoord x) ∘ ⇑(f.fiberMap x) ∘
            ⇑(B₁.continuousLinearEquivCoord x).symm :=
        funext fun v ↦ fiberMap_toAtlasMap_apply f x v
      rw [hfn]
      exact (B₂.continuousLinearEquivCoord x).bijective.comp
        ((hf x).comp (B₁.continuousLinearEquivCoord x).symm.bijective)
  exact isIso_of_fully_faithful (toAtlas.{w} 𝕜 X) f

/-- Over any nontrivially normed field, upgrade a fibrewise-bijective bundle morphism to an
isomorphism in `FiniteRankBundle.{w} 𝕜 X`. -/
noncomputable def isoOfBijective (f : B₁ ⟶ B₂)
    (hf : ∀ x, Function.Bijective (f.fiberMap x)) : B₁ ≅ B₂ :=
  haveI : IsIso f := (isIso_iff_bijective f).2 hf
  asIso f

@[simp]
theorem isoOfBijective_hom (f : B₁ ⟶ B₂) (hf : ∀ x, Function.Bijective (f.fiberMap x)) :
    (isoOfBijective f hf).hom = f := (rfl)

@[simp]
theorem fiberMap_isoOfBijective_inv (f : B₁ ⟶ B₂)
    (hf : ∀ x, Function.Bijective (f.fiberMap x)) (x : X) :
    (isoOfBijective f hf).inv.fiberMap x =
      (LinearEquiv.ofBijective (f.fiberMap x) (hf x)).symm.toLinearMap := by
  ext v
  apply (hf x).1
  have hid := congrArg (fun k : B₂ ⟶ B₂ ↦ k.fiberMap x v) (isoOfBijective f hf).inv_hom_id
  simpa only [fiberMap_comp, fiberMap_id, isoOfBijective_hom, LinearMap.comp_apply,
    LinearMap.id_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.ofBijective_apply] using
    hid.trans ((LinearEquiv.ofBijective (f.fiberMap x) (hf x)).apply_symm_apply v).symm

end Isomorphism

end ToAtlas

end FiniteRankBundle

namespace FiniteRankAtlas

section ToBundle

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] [Small.{w} 𝕜]

/-- Continuous linear identification of the shrunk coordinate fibre over a point of the `n`th
stratum with the native core fibre `(A.charts n).Fiber x`. -/
@[pp_with_univ]
noncomputable def stratumShrinkEquiv (A : FiniteRankAtlas 𝕜 X) (n : ℕ)
    (x : {x : X // A.rank x = n}) :
    Shrink.{w} (A.Fiber x.1) ≃L[𝕜] (A.charts n).Fiber x :=
  (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x.1)).trans
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜) (finCongr x.2))

@[simp]
theorem stratumShrinkEquiv_refl_apply (A : FiniteRankAtlas 𝕜 X) (x : X)
    (v : Shrink.{w} (A.Fiber x)) :
    stratumShrinkEquiv.{w} A (A.rank x) ⟨x, rfl⟩ v =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) v := (rfl)

/-- Reconstruct a `FiniteRankBundle.{w} 𝕜 X` from a small coordinate atlas whenever `[Small.{w} 𝕜]`
holds (automatic for `ℝ` and `ℂ` in every universe `w`). -/
-- Expose `.rank` and `.Fiber` (`Shrink` is already unexposed in Mathlib) so strata match `A`.
@[expose, pp_with_univ]
noncomputable def toBundle (A : FiniteRankAtlas 𝕜 X) : FiniteRankBundle.{w} 𝕜 X where
  rank := A.rank
  Fiber x := Shrink.{w} (A.Fiber x)
  topologicalSpaceStratum n :=
    FiberBundle.transferTopologicalSpace (Fin n → 𝕜) (E := (A.charts n).Fiber)
      fun x ↦ ((stratumShrinkEquiv.{w} A n x).toHomeomorph).toEquiv
  fiberBundle n :=
    FiberBundle.transfer (Fin n → 𝕜) (E := (A.charts n).Fiber)
      fun x ↦ (stratumShrinkEquiv.{w} A n x).toHomeomorph
  vectorBundle n :=
    VectorBundle.transfer 𝕜 (Fin n → 𝕜) (E := (A.charts n).Fiber)
      (stratumShrinkEquiv.{w} A n)

@[simp]
theorem rank_toBundle (A : FiniteRankAtlas 𝕜 X) :
    (A.toBundle.{w}).rank = A.rank := (rfl)

/-- Continuous linear identification of the fibre of `A.toBundle.{w}` at `x` with `A.Fiber x`. -/
@[pp_with_univ]
noncomputable def toBundleFiberEquiv (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (A.toBundle.{w}).Fiber x ≃L[𝕜] A.Fiber x :=
  Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)

private noncomputable def stratumToBundleHomeomorph (A : FiniteRankAtlas 𝕜 X) (n : ℕ) :
    TotalSpace (Fin n → 𝕜) ((A.toBundle.{w}).StratumFiber n) ≃ₜ (A.charts n).TotalSpace :=
  FiberBundle.transferHomeomorph (Fin n → 𝕜) (E := (A.charts n).Fiber)
    fun x ↦ ((stratumShrinkEquiv.{w} A n x).toHomeomorph).toEquiv

private noncomputable def gluedToBundleHomeomorph (A : FiniteRankAtlas 𝕜 X) :
    (A.toBundle.{w}).GluedTotalSpace ≃ₜ A.GluedTotalSpace where
  toEquiv := Equiv.sigmaCongrRight fun n ↦ (stratumToBundleHomeomorph.{w} A n).toEquiv
  continuous_toFun := continuous_sigma fun n ↦
    continuous_sigmaMk.comp (stratumToBundleHomeomorph.{w} A n).continuous
  continuous_invFun := continuous_sigma fun n ↦
    continuous_sigmaMk.comp (stratumToBundleHomeomorph.{w} A n).symm.continuous

/-- Homeomorphism over `X` from the glued total space of `A.toBundle.{w}` to the reconstructed
total space of `A`, acting on fibre `x` by `A.toBundleFiberEquiv.{w} x`. -/
@[pp_with_univ]
noncomputable def toBundleTotalSpaceHomeomorph (A : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (A.toBundle.{w}).Fiber ≃ₜ TotalSpace Unit A.Fiber :=
  (A.toBundle.{w}).gluedTotalSpaceHomeomorph.symm.trans
    ((gluedToBundleHomeomorph.{w} A).trans A.totalSpaceHomeomorph)

@[simp]
theorem toBundleTotalSpaceHomeomorph_apply (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (A.toBundle.{w}).Fiber) :
    A.toBundleTotalSpaceHomeomorph.{w} p =
      ⟨p.proj, A.toBundleFiberEquiv.{w} p.proj p.2⟩ := by
  rcases p with ⟨x, v⟩
  dsimp only [toBundleTotalSpaceHomeomorph, Homeomorph.trans_apply]
  have h1 : gluedToBundleHomeomorph.{w} A
        ((A.toBundle.{w}).gluedTotalSpaceHomeomorph.symm ⟨x, v⟩) =
      ⟨A.rank x, ⟨⟨x, rfl⟩, stratumShrinkEquiv.{w} A (A.rank x) ⟨x, rfl⟩ v⟩⟩ :=
    congrArg (gluedToBundleHomeomorph.{w} A)
      ((A.toBundle.{w}).gluedTotalSpaceHomeomorph_symm_apply ⟨x, v⟩)
  exact (congrArg A.totalSpaceHomeomorph h1).trans
    ((A.totalSpaceHomeomorph_apply
      ⟨A.rank x, ⟨⟨x, rfl⟩, stratumShrinkEquiv.{w} A (A.rank x) ⟨x, rfl⟩ v⟩⟩).trans
      (congrArg (TotalSpace.mk' Unit x) (stratumShrinkEquiv_refl_apply A x v)))

@[simp]
theorem toBundleTotalSpaceHomeomorph_symm_apply (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit A.Fiber) :
    (A.toBundleTotalSpaceHomeomorph.{w}).symm p =
      ⟨p.proj, (A.toBundleFiberEquiv.{w} p.proj).symm p.2⟩ := by
  apply (A.toBundleTotalSpaceHomeomorph.{w}).injective
  have rhs_eq :
      A.toBundleTotalSpaceHomeomorph.{w}
        ⟨p.proj, (A.toBundleFiberEquiv.{w} p.proj).symm p.2⟩ = p :=
    (toBundleTotalSpaceHomeomorph_apply A
      ⟨p.proj, (A.toBundleFiberEquiv.{w} p.proj).symm p.2⟩).trans
      (congrArg (TotalSpace.mk' Unit p.proj)
        ((A.toBundleFiberEquiv.{w} p.proj).apply_symm_apply p.2))
  exact (Homeomorph.apply_symm_apply _ p).trans rhs_eq.symm

/-- Action of `toBundleFunctor.{w}` on atlas morphisms, conjugating each fibre map by
`toBundleFiberEquiv`. -/
@[pp_with_univ]
noncomputable def toBundleMap {A₁ A₂ : FiniteRankAtlas 𝕜 X} (g : A₁ ⟶ A₂) :
    A₁.toBundle.{w} ⟶ A₂.toBundle.{w} where
  fiberMap x := (A₂.toBundleFiberEquiv.{w} x).symm.toLinearMap.comp
    ((g.fiberMap x).comp (A₁.toBundleFiberEquiv.{w} x).toLinearMap)
  continuous_totalSpaceMap := by
    refine ((A₂.toBundleTotalSpaceHomeomorph.{w}).symm.continuous.comp
      (g.continuous_totalSpaceMap.comp (A₁.toBundleTotalSpaceHomeomorph.{w}).continuous)).congr ?_
    rintro ⟨x, v⟩
    exact (congrArg (fun q : TotalSpace Unit A₁.Fiber ↦
      (A₂.toBundleTotalSpaceHomeomorph.{w}).symm ⟨q.proj, g.fiberMap q.proj q.2⟩)
      (A₁.toBundleTotalSpaceHomeomorph_apply ⟨x, v⟩)).trans
      (A₂.toBundleTotalSpaceHomeomorph_symm_apply _)

@[simp]
theorem fiberMap_toBundleMap_apply {A₁ A₂ : FiniteRankAtlas 𝕜 X} (g : A₁ ⟶ A₂) (x : X)
    (v : (A₁.toBundle.{w}).Fiber x) :
    (toBundleMap.{w} g).fiberMap x v =
      (A₂.toBundleFiberEquiv.{w} x).symm
        (g.fiberMap x (A₁.toBundleFiberEquiv.{w} x v)) := (rfl)

@[simp]
theorem toBundleMap_id (A : FiniteRankAtlas 𝕜 X) :
    toBundleMap.{w} (𝟙 A) = 𝟙 (A.toBundle.{w}) :=
  FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun v ↦
    (A.toBundleFiberEquiv.{w} x).symm_apply_apply v

@[simp]
theorem toBundleMap_comp {A₁ A₂ A₃ : FiniteRankAtlas 𝕜 X} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    toBundleMap.{w} (f ≫ g) = toBundleMap.{w} f ≫ toBundleMap.{w} g :=
  FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    congrArg (fun y ↦ (A₃.toBundleFiberEquiv.{w} x).symm (g.fiberMap x y))
      ((A₂.toBundleFiberEquiv.{w} x).apply_symm_apply _).symm

variable (𝕜 X) in
/-- Additive reconstruction functor from small coordinate atlases to variable-rank vector bundles
with fibres in `Type w`. -/
-- Expose the functor projections `.obj` and `.map` so `((toBundleFunctor 𝕜 X).obj A)` reduces.
@[expose, pp_with_univ]
noncomputable def toBundleFunctor : FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X where
  obj := toBundle.{w}
  map := toBundleMap.{w}
  map_id := toBundleMap_id.{w}
  map_comp := toBundleMap_comp.{w}

@[simp]
theorem toBundleFunctor_obj (A : FiniteRankAtlas 𝕜 X) :
    (toBundleFunctor.{w} 𝕜 X).obj A = A.toBundle.{w} := (rfl)

@[simp]
theorem toBundleFunctor_map {A₁ A₂ : FiniteRankAtlas 𝕜 X} (g : A₁ ⟶ A₂) :
    (toBundleFunctor.{w} 𝕜 X).map g = toBundleMap.{w} g := (rfl)

instance : (toBundleFunctor.{w} 𝕜 X).Additive where
  map_add {_ A₂ _ _} := FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    map_add (A₂.toBundleFiberEquiv.{w} x).symm _ _

end ToBundle

end FiniteRankAtlas

namespace FiniteRankBundle

section Equivalence

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜]
  (X : Type u) [TopologicalSpace X] [Small.{w} 𝕜]

private noncomputable def atlasEquivUnitApp (B : FiniteRankBundle.{w} 𝕜 X) :
    B ≅ B.toAtlasObj.toBundle.{w} :=
  isoMk
    (fun x ↦ (B.continuousLinearEquivCoord x).toLinearEquiv.trans
      (B.toAtlasObj.toBundleFiberEquiv.{w} x).symm.toLinearEquiv)
    ((B.toAtlasTotalSpaceHomeomorph.symm.trans
      (B.toAtlasObj.toBundleTotalSpaceHomeomorph.{w}).symm).continuous.congr <| by
      rintro ⟨x, v⟩
      exact (congrArg (B.toAtlasObj.toBundleTotalSpaceHomeomorph.{w}).symm
        (B.toAtlasTotalSpaceHomeomorph_symm_apply ⟨x, v⟩)).trans
        (B.toAtlasObj.toBundleTotalSpaceHomeomorph_symm_apply _))
    (((B.toAtlasTotalSpaceHomeomorph.symm.trans
      (B.toAtlasObj.toBundleTotalSpaceHomeomorph.{w}).symm).symm).continuous.congr <| by
      rintro ⟨x, v⟩
      exact (congrArg B.toAtlasTotalSpaceHomeomorph
        (B.toAtlasObj.toBundleTotalSpaceHomeomorph_apply ⟨x, v⟩)).trans
        (B.toAtlasTotalSpaceHomeomorph_apply _))

private theorem fiberMap_atlasEquivUnitApp_hom (B : FiniteRankBundle.{w} 𝕜 X) (x : X)
    (v : B.Fiber x) :
    (atlasEquivUnitApp.{w} 𝕜 X B).hom.fiberMap x v =
      (B.toAtlasObj.toBundleFiberEquiv.{w} x).symm (B.continuousLinearEquivCoord x v) :=
  congrFun (congrArg DFunLike.coe (fiberMap_isoMk_hom _ _ _ x)) v

private noncomputable def atlasEquivCounitApp (A : FiniteRankAtlas 𝕜 X) :
    (A.toBundle.{w}).toAtlasObj ≅ A :=
  FiniteRankAtlas.isoMk
    (fun x ↦ ((A.toBundle.{w}).continuousLinearEquivCoord x).symm.toLinearEquiv.trans
      (A.toBundleFiberEquiv.{w} x).toLinearEquiv)
    (((A.toBundle.{w}).toAtlasTotalSpaceHomeomorph.trans
      A.toBundleTotalSpaceHomeomorph.{w}).continuous.congr <| by
      rintro ⟨x, v⟩
      exact (congrArg A.toBundleTotalSpaceHomeomorph.{w}
        ((A.toBundle.{w}).toAtlasTotalSpaceHomeomorph_apply ⟨x, v⟩)).trans
        (A.toBundleTotalSpaceHomeomorph_apply _))
    ((((A.toBundle.{w}).toAtlasTotalSpaceHomeomorph.trans
      A.toBundleTotalSpaceHomeomorph.{w}).symm).continuous.congr <| by
      rintro ⟨x, v⟩
      exact (congrArg (A.toBundle.{w}).toAtlasTotalSpaceHomeomorph.symm
        (A.toBundleTotalSpaceHomeomorph_symm_apply ⟨x, v⟩)).trans
        ((A.toBundle.{w}).toAtlasTotalSpaceHomeomorph_symm_apply _))

private theorem fiberMap_atlasEquivCounitApp_hom (A : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (A.toBundle.{w}).toAtlasObj.Fiber x) :
    (atlasEquivCounitApp.{w} 𝕜 X A).hom.fiberMap x v =
      A.toBundleFiberEquiv.{w} x (((A.toBundle.{w}).continuousLinearEquivCoord x).symm v) :=
  congrFun (congrArg DFunLike.coe (FiniteRankAtlas.fiberMap_isoMk_hom _ _ _ x)) v

private noncomputable def atlasEquivUnitIso :
    𝟭 (FiniteRankBundle.{w} 𝕜 X) ≅
      toAtlas.{w} 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (atlasEquivUnitApp.{w} 𝕜 X) fun {B₁ B₂} f ↦
    hom_ext fun x ↦ LinearMap.ext fun v ↦
      (fiberMap_atlasEquivUnitApp_hom.{w} 𝕜 X B₂ x (f.fiberMap x v)).trans
        ((congrArg (fun w ↦ (B₂.toAtlasObj.toBundleFiberEquiv.{w} x).symm
          (B₂.continuousLinearEquivCoord x (f.fiberMap x
            ((B₁.continuousLinearEquivCoord x).symm
              (B₁.toAtlasObj.toBundleFiberEquiv.{w} x w)))))
          (fiberMap_atlasEquivUnitApp_hom.{w} 𝕜 X B₁ x v)).trans
          (congrArg (fun w ↦ (B₂.toAtlasObj.toBundleFiberEquiv.{w} x).symm
            (B₂.continuousLinearEquivCoord x (f.fiberMap x w)))
            ((congrArg (B₁.continuousLinearEquivCoord x).symm
              ((B₁.toAtlasObj.toBundleFiberEquiv.{w} x).apply_symm_apply _)).trans
              ((B₁.continuousLinearEquivCoord x).symm_apply_apply v)))).symm

private noncomputable def atlasEquivCounitIso :
    FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X ⋙ toAtlas.{w} 𝕜 X ≅
      𝟭 (FiniteRankAtlas 𝕜 X) :=
  NatIso.ofComponents (atlasEquivCounitApp.{w} 𝕜 X) fun {A₁ A₂} g ↦
    FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦
      (fiberMap_atlasEquivCounitApp_hom.{w} 𝕜 X A₂ x _).trans
        (((congrArg (A₂.toBundleFiberEquiv.{w} x)
          (((A₂.toBundle.{w}).continuousLinearEquivCoord x).symm_apply_apply _)).trans
          ((A₂.toBundleFiberEquiv.{w} x).apply_symm_apply _)).trans
          (congrArg (g.fiberMap x) (fiberMap_atlasEquivCounitApp_hom.{w} 𝕜 X A₁ x v)).symm)

/-- Explicit equivalence between variable-rank `𝕜`-vector bundles over `X` with fibres in `Type w`
and the small coordinate atlas category `FiniteRankAtlas 𝕜 X`, assuming `[Small.{w} 𝕜]` (which is
automatic for `𝕜 = ℝ` and `𝕜 = ℂ` in every universe `w`, and for any `𝕜 : Type v` when `w = v`).
Does not require `CompleteSpace 𝕜` or any compactness/bounded-rank assumption on `X`. -/
@[pp_with_univ]
noncomputable def atlasEquivalence :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlas.{w} 𝕜 X
  inverse := FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X
  unitIso := atlasEquivUnitIso.{w} 𝕜 X
  counitIso := atlasEquivCounitIso.{w} 𝕜 X
  functor_unitIso_comp B := by
    have hcomp :
        (toAtlas.{w} 𝕜 X).map ((atlasEquivUnitIso.{w} 𝕜 X).hom.app B) ≫
            (atlasEquivCounitIso.{w} 𝕜 X).hom.app ((toAtlas.{w} 𝕜 X).obj B) =
          toAtlasMap (atlasEquivUnitApp.{w} 𝕜 X B).hom ≫
            (atlasEquivCounitApp.{w} 𝕜 X B.toAtlasObj).hom :=
      congrArg₂ CategoryStruct.comp
        (congrArg toAtlasMap (NatIso.ofComponents_hom_app _ _ B))
        (NatIso.ofComponents_hom_app _ _ ((toAtlas.{w} 𝕜 X).obj B))
    refine hcomp.trans (FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦ ?_)
    exact (fiberMap_atlasEquivCounitApp_hom.{w} 𝕜 X B.toAtlasObj x _).trans
      (((congrArg (B.toAtlasObj.toBundleFiberEquiv.{w} x)
        (((B.toAtlasObj.toBundle.{w}).continuousLinearEquivCoord x).symm_apply_apply _)).trans
        (congrArg (B.toAtlasObj.toBundleFiberEquiv.{w} x)
          (fiberMap_atlasEquivUnitApp_hom.{w} 𝕜 X B x _))).trans
        (((B.toAtlasObj.toBundleFiberEquiv.{w} x).apply_symm_apply _).trans
          ((B.continuousLinearEquivCoord x).apply_symm_apply v)))

@[simp]
theorem atlasEquivalence_functor :
    (atlasEquivalence.{w} 𝕜 X).functor = toAtlas.{w} 𝕜 X := (rfl)

@[simp]
theorem atlasEquivalence_inverse :
    (atlasEquivalence.{w} 𝕜 X).inverse = FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X := (rfl)

instance : (toAtlas.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_functor

instance : (FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_inverse

/-- Change of fibre universe for variable-rank topological vector bundles over `X`, constructed via
the small coordinate model `FiniteRankAtlas 𝕜 X`. For `𝕜 = ℝ` or `𝕜 = ℂ`, this equivalence applies
between any two universes `w` and `w'` without extra hypotheses. -/
@[pp_with_univ]
noncomputable def changeUniverseEquivalence [Small.{w'} 𝕜] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankBundle.{w'} 𝕜 X :=
  (atlasEquivalence.{w} 𝕜 X).trans (atlasEquivalence.{w'} 𝕜 X).symm

end Equivalence

end FiniteRankBundle

end TauCeti
