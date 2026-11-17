/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Equiv.ULift
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Topology.Algebra.Module.TransferInstance

import TauCeti.Topology.Algebra.Module.Equiv.Pi
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Equivalence between genuine variable-rank bundles and small coordinate atlases

Objects of `FiniteRankBundle.{w} 𝕜 X` carry genuine `Type w` fibres over `X : Type u` and therefore
live in `Type (max u v (w + 1))`, whereas `FiniteRankAtlas 𝕜 X` stores small coordinate-valued
transition data in `Type (max u v)`. Passing to point-indexed coordinate charts resolves this
universe-size obstruction without losing categorical information:

* **Coordinate presentation (unconditional):** Every `E : FiniteRankBundle.{w} 𝕜 X` induces a small
  coordinate atlas `E.toAtlas` together with `FiniteRankBundle.reconstructionFiberEquiv` and
  `FiniteRankBundle.reconstructionHomeomorph`. Conjugating fibre maps gives an additive, full, and
  faithful functor `FiniteRankBundle.toAtlasFunctor`, from which
  `FiniteRankBundle.isIso_iff_bijective`, `LocallySmall.{max u v}`, and
  `EssentiallySmall.{max u v}` follow without `Small` hypotheses.
  For a constant-rank `VectorBundle 𝕜 (Fin n → 𝕜) V`, `FiniteRankBundle.toAtlasOfBundleIso`
  identifies `(ofBundle 𝕜 n V).toAtlas` with
  `(FiniteRankAtlas.ofCoreFunctor 𝕜 X).obj (FiniteRankBundleCore.ofBundle 𝕜 n V)`, showing that the
  genuine and coordinate constant-rank embeddings commute up to canonical isomorphism (with the
  constant-rank essential image characterized by `FiniteRankAtlas.essImage_ofCoreFunctor_iff`).
* **Stratum bundle transport:** `FiniteRankBundle.ofBundles` and
  `FiniteRankBundle.ofBundlesHomeomorph` assemble a `FiniteRankBundle` and its global total-space
  comparison from stratumwise `VectorBundle`s and fibrewise continuous linear equivalences.
* **Equivalence under `[Small.{w} 𝕜]`:** Shrinking coordinate fibres into `Type w` yields the
  additive inverse functor `FiniteRankBundle.fromAtlasFunctor` and the explicit equivalence
  `FiniteRankBundle.atlasEquivalence : FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X`.
* **Universe polymorphism:** For arbitrary universes `w, w'`, `FiniteRankBundle.ulift` and the
  additive, full, and faithful `FiniteRankBundle.uliftFunctor` lift fibres to `Type (max w w')` and
  satisfy `uliftFunctor ⋙ toAtlasFunctor ≅ toAtlasFunctor`
  (`FiniteRankBundle.uliftFunctorCompToAtlasIso`), making `uliftFunctor` an equivalence when
  `[Small.{w} 𝕜]`. Under `[Small.{w₁} 𝕜] [Small.{w₂} 𝕜]`,
  `FiniteRankBundle.changeUniverseEquivalence` identifies `FiniteRankBundle.{w₁} 𝕜 X` with
  `FiniteRankBundle.{w₂} 𝕜 X`.

## References

* The coordinate presentation `toAtlas`, `reconstructionHomeomorph`, and `toAtlasFunctor` builds
  directly on `TauCeti.pointIndexedCore` (`pointIndexedCoreFiberEquiv`,
  `pointIndexedCoreHomeomorph`), `TauCeti.pointIndexedCoreHomEquiv`,
  `FiniteRankAtlas.ofBundles`, and `FiniteRankAtlas.reconstructionHomeomorph`.
* `FiniteRankBundle.isIso_iff_bijective` transports `FiniteRankAtlas.isIso_iff_bijective` (see
  Allen Hatcher, *Vector Bundles and K-Theory*, §1.1, Proposition 1.1).
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

/-- `E.reconstructionHomeomorph` covers the identity map on the base space `X`. -/
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
            F.reconstructionHomeomorph_symm_apply]
          rfl }
  map_id E := FiniteRankAtlas.hom_ext fun x ↦
    LinearMap.ext (E.reconstructionFiberEquiv x).symm_apply_apply
  map_comp {_ F _} _ _ := FiniteRankAtlas.hom_ext fun x ↦
    LinearMap.ext fun _ ↦ by simp [LinearMap.comp_apply]

@[simp] theorem toAtlasFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).obj E = E.toAtlas := (rfl)

@[simp] theorem fiberMap_toAtlasFunctor_map {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (x : X) :
    ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x =
      (F.reconstructionFiberEquiv x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (E.reconstructionFiberEquiv x).toLinearMap) := (rfl)

/-- `toAtlasFunctor` preserves addition of bundle morphisms. -/
instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {_ F f g} := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    (F.reconstructionFiberEquiv x).symm.map_add (f.fiberMap x _) (g.fiberMap x _)

/-- `toAtlasFunctor` is faithful because `reconstructionFiberEquiv` is an equivalence on each
fibre. -/
instance : (toAtlasFunctor.{w} 𝕜 X).Faithful where
  map_injective {E F} f₁ f₂ h := hom_ext fun x ↦ LinearMap.ext fun w ↦ by
    have hx : (F.reconstructionFiberEquiv x).symm
        (f₁.fiberMap x (E.reconstructionFiberEquiv x ((E.reconstructionFiberEquiv x).symm w))) =
      (F.reconstructionFiberEquiv x).symm
        (f₂.fiberMap x (E.reconstructionFiberEquiv x ((E.reconstructionFiberEquiv x).symm w))) :=
      congrArg (fun k ↦ k.fiberMap x ((E.reconstructionFiberEquiv x).symm w)) h
    rw [(E.reconstructionFiberEquiv x).apply_symm_apply] at hx
    exact (F.reconstructionFiberEquiv x).symm.injective hx

/-- `toAtlasFunctor` is full by conjugating coordinate morphisms along
`reconstructionHomeomorph`. -/
instance : (toAtlasFunctor.{w} 𝕜 X).Full where
  map_surjective {E F} g := by
    let g' : E.toAtlas ⟶ F.toAtlas := g
    refine ⟨⟨fun x ↦ (F.reconstructionFiberEquiv x).toLinearMap.comp
        ((g'.fiberMap x).comp (E.reconstructionFiberEquiv x).symm.toLinearMap),
      (F.reconstructionHomeomorph.continuous.comp
        (g'.continuous_totalSpaceMap.comp E.reconstructionHomeomorph.symm.continuous)).congr
        fun p ↦ by
          rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_symm_apply,
            F.reconstructionHomeomorph_apply]
          rfl⟩,
      FiniteRankAtlas.hom_ext (A := E.toAtlas) (D := F.toAtlas) fun x ↦ LinearMap.ext fun _ ↦ by
        simp [g', LinearMap.comp_apply]⟩

/-- A morphism of genuine variable-rank bundles is an isomorphism iff every fibre map is
bijective. -/
theorem isIso_iff_bijective {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  rw [← isIso_iff_of_reflects_iso f (toAtlasFunctor.{w} 𝕜 X), FiniteRankAtlas.isIso_iff_bijective]
  exact forall_congr' fun x ↦
    ((F.reconstructionFiberEquiv x).symm.bijective.of_comp_iff' _).trans
      ((E.reconstructionFiberEquiv x).bijective.of_comp_iff _)

/-- `FiniteRankBundle.{w} 𝕜 X` is locally small at `max u v` via `toAtlasFunctor`. -/
instance : LocallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  locallySmall_of_faithful (toAtlasFunctor.{w} 𝕜 X)

/-- `FiniteRankBundle.{w} 𝕜 X` is essentially small at `max u v` via `toAtlasFunctor`. -/
instance : EssentiallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

section ConstantRank

variable (𝕜) (n : ℕ) (V : X → Type w)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) V)]
  [FiberBundle (Fin n → 𝕜) V] [VectorBundle 𝕜 (Fin n → 𝕜) V]

@[simp] theorem reconstructionFiberEquiv_ofBundle (x : X) :
    (ofBundle 𝕜 n V).reconstructionFiberEquiv x =
      pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) V x :=
  DFunLike.ext _ _ fun v ↦
    (pointIndexedCoreFiberEquiv_apply 𝕜 (Fin n → 𝕜) ((ofBundle 𝕜 n V).StratumFiber n)
      ⟨x, rfl⟩ v).trans <| (trivializationAt_ofBundle_symm 𝕜 n V ⟨x, rfl⟩ v).trans
        (pointIndexedCoreFiberEquiv_apply 𝕜 (Fin n → 𝕜) V x v).symm

/-- Presenting `V` via `FiniteRankBundle.ofBundle` and `toAtlas` is canonically isomorphic to
presenting `V` via `FiniteRankBundleCore.ofBundle` and `FiniteRankAtlas.ofCoreFunctor`. -/
noncomputable def toAtlasOfBundleIso :
    (ofBundle 𝕜 n V).toAtlas ≅
      (FiniteRankAtlas.ofCoreFunctor 𝕜 X).obj (FiniteRankBundleCore.ofBundle 𝕜 n V) :=
  let B := ofBundle 𝕜 n V
  let C := FiniteRankBundleCore.ofBundle 𝕜 n V
  let f1 := B.reconstructionHomeomorph
  let f2 := ofBundleHomeomorph 𝕜 n V
  let f3 := (pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) V).symm
  let f4 := (FiniteRankAtlas.ofCoreHomeomorph C).symm
  FiniteRankAtlas.isoMk (fun _ ↦ LinearEquiv.refl 𝕜 (Fin n → 𝕜))
    ((f4.continuous.comp (f3.continuous.comp (f2.continuous.comp f1.continuous))).congr fun p ↦
      (congrArg (fun q ↦ f4 (f3 (f2 q))) (B.reconstructionHomeomorph_apply p)).trans <|
        (congrArg (fun q ↦ f4 (f3 q)) (ofBundleHomeomorph_apply 𝕜 n V _)).trans <|
          (congrArg f4 (pointIndexedCoreHomeomorph_symm_apply 𝕜 (Fin n → 𝕜) V _)).trans <|
            (FiniteRankAtlas.ofCoreHomeomorph_symm_apply C _).trans <|
              congrArg (TotalSpace.mk p.proj) <| by
                rw [reconstructionFiberEquiv_ofBundle]
                exact (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) V p.proj).symm_apply_apply p.2)
    ((f1.symm.continuous.comp (f2.symm.continuous.comp
      (f3.symm.continuous.comp f4.symm.continuous))).congr fun p ↦
      (congrArg (fun q ↦ f1.symm (f2.symm (f3.symm q)))
        (FiniteRankAtlas.ofCoreHomeomorph_apply C p)).trans <|
        (congrArg (fun q ↦ f1.symm (f2.symm q))
          (pointIndexedCoreHomeomorph_apply 𝕜 (Fin n → 𝕜) V _)).trans <|
          (congrArg f1.symm (ofBundleHomeomorph_symm_apply 𝕜 n V _)).trans <|
            (B.reconstructionHomeomorph_symm_apply _).trans <|
              congrArg (TotalSpace.mk p.proj) <| by
                rw [reconstructionFiberEquiv_ofBundle]
                exact (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) V p.proj).symm_apply_apply p.2)

@[simp] theorem fiberMap_toAtlasOfBundleIso_hom (x : X) :
    (toAtlasOfBundleIso 𝕜 n V).hom.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_hom (A := (ofBundle 𝕜 n V).toAtlas)
    (D := (FiniteRankAtlas.ofCoreFunctor 𝕜 X).obj (FiniteRankBundleCore.ofBundle 𝕜 n V)) _ _ _ x

@[simp] theorem fiberMap_toAtlasOfBundleIso_inv (x : X) :
    (toAtlasOfBundleIso 𝕜 n V).inv.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_inv (A := (ofBundle 𝕜 n V).toAtlas)
    (D := (FiniteRankAtlas.ofCoreFunctor 𝕜 X).obj (FiniteRankBundleCore.ofBundle 𝕜 n V)) _ _ _ x

end ConstantRank

end ToAtlas

/-! ### Stratumwise bundle transfer -/

section OfBundles

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]
variable (𝕜) (r : LocallyConstant X ℕ) (V : X → Type w')
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  (E : ∀ n : ℕ, {x : X // r x = n} → Type w)
  [∀ n x, AddCommMonoid (E n x)] [∀ n x, Module 𝕜 (E n x)]
  [∀ n x, TopologicalSpace (E n x)]
  [∀ n, TopologicalSpace (TotalSpace (Fin n → 𝕜) (E n))]
  [∀ n, FiberBundle (Fin n → 𝕜) (E n)]
  [∀ n, VectorBundle 𝕜 (Fin n → 𝕜) (E n)]
  (e : ∀ (n : ℕ) (x : {x : X // r x = n}), V x.1 ≃L[𝕜] E n x)

/-- Assemble a `FiniteRankBundle` with fibres `V` and rank `r` by transporting stratumwise
`VectorBundle`s `E n` along fibrewise continuous linear equivalences `e n`. -/
@[expose] noncomputable def ofBundles : FiniteRankBundle.{w'} 𝕜 X where
  rank := r
  Fiber := V
  topologicalSpaceStratum n := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
  fiberBundleStratum n :=
    letI := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
    FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E n) (e n)
      (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)
  vectorBundleStratum n :=
    letI := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
    letI := FiberBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E n) (e n)
      (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)
    VectorBundle.ofContinuousLinearEquiv (Fin n → 𝕜) (E := E n) (e n)
      (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)

@[simp] theorem rank_ofBundles : (ofBundles 𝕜 r V E e).rank = r := (rfl)

@[simp] theorem fiber_ofBundles (x : X) : (ofBundles 𝕜 r V E e).Fiber x = V x := (rfl)

@[simp] theorem reconstructionFiberEquiv_ofBundles (x : X) :
    (ofBundles 𝕜 r V E e).reconstructionFiberEquiv x =
      (pointIndexedCoreFiberEquiv 𝕜 (Fin (r x) → 𝕜) (E (r x)) ⟨x, rfl⟩).trans
        (e (r x) ⟨x, rfl⟩).symm :=
  let b : {y : X // r y = r x} := ⟨x, rfl⟩
  letI := totalSpaceInduced (Fin (r x) → 𝕜) (E := E (r x)) fun y ↦ e (r x) y
  let hind := isInducing_totalSpaceInduced (Fin (r x) → 𝕜) (E := E (r x)) fun y ↦ e (r x) y
  letI := FiberBundle.ofContinuousLinearEquiv (Fin (r x) → 𝕜) (E := E (r x)) (e (r x)) hind
  letI := VectorBundle.ofContinuousLinearEquiv (Fin (r x) → 𝕜) (E := E (r x)) (e (r x)) hind
  DFunLike.ext _ _ fun v ↦
    (pointIndexedCoreFiberEquiv_apply 𝕜 (Fin (r x) → 𝕜) (fun y : {y : X // r y = r x} ↦ V y.1)
      b v).trans <|
      (congrArg (fun t ↦ t.symm b v)
        (FiberBundle.trivializationAt_ofContinuousLinearEquiv
          (Fin (r x) → 𝕜) (E := E (r x)) (e (r x)) hind b)).trans <|
        (Trivialization.compContinuousLinearEquiv_symm
          (trivializationAt (Fin (r x) → 𝕜) (E (r x)) b) (e (r x)) hind
          (FiberBundle.mem_baseSet_trivializationAt (Fin (r x) → 𝕜) (E (r x)) b) v).trans <|
          congrArg (e (r x) b).symm
            (pointIndexedCoreFiberEquiv_apply 𝕜 (Fin (r x) → 𝕜) (E (r x)) b v).symm

private noncomputable def gluedOfBundlesHomeomorph :
    (ofBundles 𝕜 r V E e).GluedTotalSpace ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  letI (n : ℕ) := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
  { toEquiv := Equiv.sigmaCongrRight fun n ↦
      (totalSpaceHomeomorphOfContinuousLinearEquiv (Fin n → 𝕜) (e n)
        (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)).toEquiv
    continuous_toFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp
      (totalSpaceHomeomorphOfContinuousLinearEquiv (Fin n → 𝕜) (e n)
        (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)).continuous
    continuous_invFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp
      (totalSpaceHomeomorphOfContinuousLinearEquiv (Fin n → 𝕜) (e n)
        (isInducing_totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x)).symm.continuous }

/-- Homeomorphism over `X` between the global total space of `ofBundles 𝕜 r V E e` and the disjoint
union of the stratum total spaces `TotalSpace (Fin n → 𝕜) (E n)`. -/
noncomputable def ofBundlesHomeomorph :
    TotalSpace Unit (ofBundles 𝕜 r V E e).Fiber ≃ₜ Σ n : ℕ, TotalSpace (Fin n → 𝕜) (E n) :=
  (ofBundles 𝕜 r V E e).totalSpaceHomeomorph.symm.trans (gluedOfBundlesHomeomorph 𝕜 r V E e)

@[simp] theorem ofBundlesHomeomorph_apply (p : TotalSpace Unit (ofBundles 𝕜 r V E e).Fiber) :
    ofBundlesHomeomorph 𝕜 r V E e p =
      ⟨r p.proj, ⟨⟨p.proj, rfl⟩, e (r p.proj) ⟨p.proj, rfl⟩ p.2⟩⟩ :=
  letI := totalSpaceInduced (Fin (r p.proj) → 𝕜) (E := E (r p.proj)) fun x ↦ e (r p.proj) x
  (congrArg (gluedOfBundlesHomeomorph 𝕜 r V E e)
    ((ofBundles 𝕜 r V E e).totalSpaceHomeomorph_symm_apply p)).trans <|
    congrArg (Sigma.mk (r p.proj))
      (totalSpaceHomeomorphOfContinuousLinearEquiv_apply (Fin (r p.proj) → 𝕜) (e (r p.proj)) _ _)

@[simp] theorem ofBundlesHomeomorph_symm_apply (n : ℕ) (p : TotalSpace (Fin n → 𝕜) (E n)) :
    (ofBundlesHomeomorph 𝕜 r V E e).symm ⟨n, p⟩ = ⟨p.proj.1, (e n p.proj).symm p.2⟩ :=
  letI := totalSpaceInduced (Fin n → 𝕜) (E := E n) fun x ↦ e n x
  (congrArg (fun q ↦ (ofBundles 𝕜 r V E e).totalSpaceHomeomorph ⟨n, q⟩)
    (totalSpaceHomeomorphOfContinuousLinearEquiv_symm_apply (Fin n → 𝕜) (e n) _ p)).trans
    ((ofBundles 𝕜 r V E e).totalSpaceHomeomorph_apply _)

end OfBundles

/-! ### Explicit inverse functor and equivalence under `[Small.{w} 𝕜]` -/

section FromAtlas

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Reconstruct a genuine `w`-universe variable-rank vector bundle from `A : FiniteRankAtlas 𝕜 X`
when `[Small.{w} 𝕜]` holds. -/
@[expose] noncomputable def fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    FiniteRankBundle.{w} 𝕜 X :=
  ofBundles 𝕜 A.rank (fun x ↦ Shrink.{w} (A.Fiber x)) (fun n ↦ (A.charts n).Fiber)
    fun _ x ↦ (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x.1)).trans
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr x.2))

@[simp] theorem rank_fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlas.{w} A).rank = A.rank := (rfl)

@[simp] theorem fiber_fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (fromAtlas.{w} A).Fiber x = Shrink.{w} (A.Fiber x) := (rfl)

@[simp] theorem reconstructionFiberEquiv_fromAtlas [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (fromAtlas.{w} A).reconstructionFiberEquiv x =
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm := by
  have hcore : pointIndexedCoreFiberEquiv 𝕜 (Fin (A.rank x) → 𝕜)
      (A.charts (A.rank x)).Fiber ⟨x, rfl⟩ = ContinuousLinearEquiv.refl 𝕜 (Fin (A.rank x) → 𝕜) :=
    ContinuousLinearEquiv.symm_bijective.injective <| DFunLike.ext _ _ fun v ↦
      (pointIndexedCoreFiberEquiv_symm_apply 𝕜 (Fin (A.rank x) → 𝕜)
        (A.charts (A.rank x)).Fiber ⟨x, rfl⟩ v).trans <|
        congrArg Prod.snd (((A.charts (A.rank x)).toFiberBundleCore).localTrivAt_apply_mk
          ⟨x, rfl⟩ v)
  have hpi : ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin (A.rank x) ↦ 𝕜)
      (finCongr (rfl : A.rank x = A.rank x)) =
    ContinuousLinearEquiv.refl 𝕜 (Fin (A.rank x) → 𝕜) := by simp
  exact (reconstructionFiberEquiv_ofBundles 𝕜 A.rank (fun y ↦ Shrink.{w} (A.Fiber y))
    (fun n ↦ (A.charts n).Fiber) _ x).trans <| DFunLike.ext _ _ fun v ↦ by
      rw [hcore, hpi]
      rfl

/-- Homeomorphism over `X` between `TotalSpace Unit (fromAtlas A).Fiber` and
`TotalSpace Unit A.Fiber`. -/
noncomputable def fromAtlasHomeomorph [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (fromAtlas.{w} A).Fiber ≃ₜ TotalSpace Unit A.Fiber :=
  (ofBundlesHomeomorph 𝕜 A.rank (fun x ↦ Shrink.{w} (A.Fiber x)) (fun n ↦ (A.charts n).Fiber)
    fun _ x ↦ (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x.1)).trans
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr x.2))).trans
    A.totalSpaceHomeomorph

@[simp] theorem fromAtlasHomeomorph_apply [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (fromAtlas.{w} A).Fiber) :
    fromAtlasHomeomorph.{w} A p = ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.2⟩ :=
  (congrArg A.totalSpaceHomeomorph (ofBundlesHomeomorph_apply _ _ _ _ _ p)).trans <|
    (A.totalSpaceHomeomorph_apply _).trans <| congrArg (TotalSpace.mk p.proj) <| by
      simp only [finCongr_refl, ContinuousLinearEquiv.piCongrLeft_refl]
      rfl

@[simp] theorem fromAtlasHomeomorph_symm_apply [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit A.Fiber) :
    (fromAtlasHomeomorph.{w} A).symm p =
      ⟨p.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).symm p.2⟩ :=
  (congrArg (ofBundlesHomeomorph _ _ _ _ _).symm (A.totalSpaceHomeomorph_symm_apply p)).trans <|
    (ofBundlesHomeomorph_symm_apply _ _ _ _ _ _ _).trans <| congrArg (TotalSpace.mk p.proj) <| by
      simp only [finCongr_refl, ContinuousLinearEquiv.piCongrLeft_refl]
      rfl

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
          fromAtlasHomeomorph_symm_apply]
        rfl }
  map_id A := hom_ext fun x ↦
    LinearMap.ext (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm_apply_apply
  map_comp {A B C} f g := hom_ext fun x ↦ LinearMap.ext fun v ↦
    congrArg (fun w ↦ (Shrink.continuousLinearEquiv 𝕜 (C.Fiber x)).symm (g.fiberMap x w))
      ((Shrink.continuousLinearEquiv 𝕜 (B.Fiber x)).apply_symm_apply
        (f.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) v))).symm

@[simp] theorem fromAtlasFunctor_obj [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlasFunctor.{w} 𝕜 X).obj A = fromAtlas.{w} A := (rfl)

@[simp] theorem fiberMap_fromAtlasFunctor_map [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X}
    (g : A ⟶ D) (x : X) :
    ((fromAtlasFunctor.{w} 𝕜 X).map g).fiberMap x =
      (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
        ((g.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap) := (rfl)

/-- `fromAtlasFunctor` preserves addition of coordinate morphisms. -/
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
        fromAtlasHomeomorph_symm_apply]
      rfl)
    ((E.reconstructionHomeomorph.continuous.comp
      (fromAtlasHomeomorph.{w} E.toAtlas).continuous).congr fun p ↦ by
      rw [Function.comp_apply, fromAtlasHomeomorph_apply, E.reconstructionHomeomorph_apply]
      rfl)

@[simp] theorem fiberMap_atlasUnitApp_hom [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (atlasUnitApp.{w} E).hom.fiberMap x =
      ((E.reconstructionFiberEquiv x).symm.trans
        (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm).toLinearMap :=
  fiberMap_isoMk_hom (F := fromAtlas.{w} E.toAtlas) _ _ _ x

@[simp] theorem fiberMap_atlasUnitApp_inv [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (atlasUnitApp.{w} E).inv.fiberMap x =
      ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).trans
        (E.reconstructionFiberEquiv x)).toLinearMap :=
  (fiberMap_isoMk_inv (F := fromAtlas.{w} E.toAtlas) _ _ _ x).trans (LinearMap.ext fun _ ↦ rfl)

/-- Component isomorphism `(fromAtlas A).toAtlas ≅ A` of the counit of `atlasEquivalence`. -/
noncomputable def atlasCounitApp [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlas.{w} A).toAtlas ≅ A :=
  FiniteRankAtlas.isoMk (fun x ↦ LinearEquiv.refl 𝕜 (A.Fiber x))
    (((fromAtlasHomeomorph.{w} A).continuous.comp
      (fromAtlas.{w} A).reconstructionHomeomorph.continuous).congr fun p ↦ by
      rw [Function.comp_apply, (fromAtlas.{w} A).reconstructionHomeomorph_apply,
        fromAtlasHomeomorph_apply, reconstructionFiberEquiv_fromAtlas]
      exact congrArg (TotalSpace.mk p.proj)
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply p.2))
    (((fromAtlas.{w} A).reconstructionHomeomorph.symm.continuous.comp
      (fromAtlasHomeomorph.{w} A).symm.continuous).congr fun p ↦ by
      rw [Function.comp_apply, fromAtlasHomeomorph_symm_apply,
        (fromAtlas.{w} A).reconstructionHomeomorph_symm_apply, reconstructionFiberEquiv_fromAtlas]
      exact congrArg (TotalSpace.mk p.proj)
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply p.2))

@[simp] theorem fiberMap_atlasCounitApp_hom [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (atlasCounitApp.{w} A).hom.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_hom (A := (fromAtlas.{w} A).toAtlas) (D := A) _ _ _ x

@[simp] theorem fiberMap_atlasCounitApp_inv [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) (x : X) :
    (atlasCounitApp.{w} A).inv.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_inv (A := (fromAtlas.{w} A).toAtlas) (D := A) _ _ _ x

variable (𝕜 X) in
/-- Unit natural isomorphism `𝟭 _ ≅ toAtlasFunctor ⋙ fromAtlasFunctor`. -/
noncomputable def atlasUnitIso [Small.{w} 𝕜] :
    𝟭 (FiniteRankBundle.{w} 𝕜 X) ≅ toAtlasFunctor.{w} 𝕜 X ⋙ fromAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (fun E ↦ atlasUnitApp.{w} E) fun {E F} f ↦
    hom_ext fun x ↦ by
      rw [Functor.id_map, Functor.comp_map, fiberMap_comp, fiberMap_comp,
        fiberMap_atlasUnitApp_hom, fiberMap_atlasUnitApp_hom]
      exact LinearMap.ext fun v ↦
        congrArg (fun w ↦ (Shrink.continuousLinearEquiv 𝕜 (F.toAtlas.Fiber x)).symm
          ((F.reconstructionFiberEquiv x).symm (f.fiberMap x w))) <|
          ((E.reconstructionFiberEquiv x).apply_symm_apply v).symm.trans <|
            congrArg (E.reconstructionFiberEquiv x)
              ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).apply_symm_apply _).symm

@[simp] theorem atlasUnitIso_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).app E = atlasUnitApp.{w} E :=
  Iso.ext rfl

@[simp] theorem atlasUnitIso_hom_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).hom.app E = (atlasUnitApp.{w} E).hom := (rfl)

@[simp] theorem atlasUnitIso_inv_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).inv.app E = (atlasUnitApp.{w} E).inv := (rfl)

variable (𝕜 X) in
/-- Counit natural isomorphism `fromAtlasFunctor ⋙ toAtlasFunctor ≅ 𝟭 _`. -/
noncomputable def atlasCounitIso [Small.{w} 𝕜] :
    fromAtlasFunctor.{w} 𝕜 X ⋙ toAtlasFunctor.{w} 𝕜 X ≅ 𝟭 (FiniteRankAtlas 𝕜 X) :=
  NatIso.ofComponents (fun A ↦ atlasCounitApp.{w} A) fun {A D} g ↦
    FiniteRankAtlas.hom_ext (A := (fromAtlas.{w} A).toAtlas) (D := D) fun x ↦ by
      rw [Functor.comp_map, Functor.id_map, FiniteRankAtlas.fiberMap_comp,
        FiniteRankAtlas.fiberMap_comp, fiberMap_atlasCounitApp_hom, fiberMap_atlasCounitApp_hom]
      refine LinearMap.ext fun v ↦ ?_
      -- Evaluate the exposed `fromAtlasFunctor` and `toAtlasFunctor` actions on `v`.
      change ((fromAtlas.{w} D).reconstructionFiberEquiv x).symm
          ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
            (g.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)
              ((fromAtlas.{w} A).reconstructionFiberEquiv x v)))) =
        g.fiberMap x v
      rw [reconstructionFiberEquiv_fromAtlas, reconstructionFiberEquiv_fromAtlas]
      exact ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).apply_symm_apply _).trans <|
        congrArg (g.fiberMap x)
          ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).apply_symm_apply v)

@[simp] theorem atlasCounitIso_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).app A = atlasCounitApp.{w} A :=
  Iso.ext rfl

@[simp] theorem atlasCounitIso_hom_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).hom.app A = (atlasCounitApp.{w} A).hom := (rfl)

@[simp] theorem atlasCounitIso_inv_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).inv.app A = (atlasCounitApp.{w} A).inv := (rfl)

variable (𝕜 X) in
/-- Explicit equivalence of categories `FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X` whenever
`[Small.{w} 𝕜]` holds. -/
noncomputable def atlasEquivalence [Small.{w} 𝕜] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor.{w} 𝕜 X
  inverse := fromAtlasFunctor.{w} 𝕜 X
  unitIso := atlasUnitIso.{w} 𝕜 X
  counitIso := atlasCounitIso.{w} 𝕜 X
  functor_unitIso_comp E :=
    FiniteRankAtlas.hom_ext (A := E.toAtlas) (D := E.toAtlas) fun x ↦ by
      rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_id,
        atlasCounitIso_hom_app, fiberMap_atlasCounitApp_hom, atlasUnitIso_hom_app]
      refine LinearMap.ext fun (v : E.toAtlas.Fiber x) ↦ ?_
      change ((fromAtlas.{w} E.toAtlas).reconstructionFiberEquiv x).symm
          ((atlasUnitApp.{w} E).hom.fiberMap x (E.reconstructionFiberEquiv x v)) = v
      rw [reconstructionFiberEquiv_fromAtlas, fiberMap_atlasUnitApp_hom]
      exact ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).apply_symm_apply _).trans
        ((E.reconstructionFiberEquiv x).symm_apply_apply v)

@[simp] theorem atlasEquivalence_functor [Small.{w} 𝕜] :
    (atlasEquivalence.{w} 𝕜 X).functor = toAtlasFunctor.{w} 𝕜 X := (rfl)

@[simp] theorem atlasEquivalence_inverse [Small.{w} 𝕜] :
    (atlasEquivalence.{w} 𝕜 X).inverse = fromAtlasFunctor.{w} 𝕜 X := (rfl)

@[simp] theorem atlasEquivalence_unitIso [Small.{w} 𝕜] :
    (atlasEquivalence.{w} 𝕜 X).unitIso =
      atlasUnitIso.{w} 𝕜 X ≪≫
        eqToIso (by rw [atlasEquivalence_functor, atlasEquivalence_inverse]) :=
  (Iso.trans_refl _).symm

@[simp] theorem atlasEquivalence_counitIso [Small.{w} 𝕜] :
    (atlasEquivalence.{w} 𝕜 X).counitIso =
      eqToIso (by rw [atlasEquivalence_functor, atlasEquivalence_inverse]) ≪≫
        atlasCounitIso.{w} 𝕜 X :=
  (Iso.refl_trans _).symm

/-- The forward functor of `atlasEquivalence` is additive. -/
instance [Small.{w} 𝕜] : (atlasEquivalence.{w} 𝕜 X).functor.Additive := by
  rw [atlasEquivalence_functor]
  infer_instance

/-- Under `[Small.{w} 𝕜]`, `toAtlasFunctor` is an equivalence of categories. -/
instance [Small.{w} 𝕜] : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_functor

/-- Under `[Small.{w} 𝕜]`, `fromAtlasFunctor` is an equivalence of categories. -/
instance [Small.{w} 𝕜] : (fromAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_inverse

end FromAtlas

/-! ### Universe-lifting functor and change-of-universe equivalence -/

section UniversePolymorphism

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Lift the fibres of `E : FiniteRankBundle.{w} 𝕜 X` to `Type (max w w')` via `ULift`. -/
@[expose] noncomputable def ulift (E : FiniteRankBundle.{w} 𝕜 X) :
    FiniteRankBundle.{max w w'} 𝕜 X :=
  ofBundles 𝕜 E.rank (fun x ↦ ULift.{w'} (E.Fiber x)) E.StratumFiber
    fun _ _ ↦ ContinuousLinearEquiv.ulift

@[simp] theorem rank_ulift (E : FiniteRankBundle.{w} 𝕜 X) : (E.ulift.{w, w'}).rank = E.rank := (rfl)

@[simp] theorem fiber_ulift (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (E.ulift.{w, w'}).Fiber x = ULift.{w'} (E.Fiber x) := (rfl)

@[simp] theorem reconstructionFiberEquiv_ulift (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (E.ulift.{w, w'}).reconstructionFiberEquiv x =
      (E.reconstructionFiberEquiv x).trans ContinuousLinearEquiv.ulift.symm :=
  reconstructionFiberEquiv_ofBundles 𝕜 E.rank (fun y ↦ ULift.{w'} (E.Fiber y)) E.StratumFiber
    (fun _ _ ↦ ContinuousLinearEquiv.ulift) x

/-- Homeomorphism over `X` between the global total spaces of `E.ulift` and `E`. -/
noncomputable def uliftHomeomorph (E : FiniteRankBundle.{w} 𝕜 X) :
    TotalSpace Unit (E.ulift.{w, w'}).Fiber ≃ₜ TotalSpace Unit E.Fiber :=
  (ofBundlesHomeomorph 𝕜 E.rank (fun x ↦ ULift.{w'} (E.Fiber x)) E.StratumFiber
    fun _ _ ↦ ContinuousLinearEquiv.ulift).trans E.totalSpaceHomeomorph

@[simp] theorem uliftHomeomorph_apply (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit (E.ulift.{w, w'}).Fiber) :
    E.uliftHomeomorph.{w, w'} p = ⟨p.proj, p.2.down⟩ :=
  (congrArg E.totalSpaceHomeomorph (ofBundlesHomeomorph_apply _ _ _ _ _ p)).trans <|
    (E.totalSpaceHomeomorph_apply _).trans <|
      congrArg (TotalSpace.mk p.proj) (ContinuousLinearEquiv.ulift_apply p.2)

@[simp] theorem uliftHomeomorph_symm_apply (E : FiniteRankBundle.{w} 𝕜 X)
    (p : TotalSpace Unit E.Fiber) :
    (E.uliftHomeomorph.{w, w'}).symm p = ⟨p.proj, ULift.up p.2⟩ :=
  (congrArg (ofBundlesHomeomorph _ _ _ _ _).symm (E.totalSpaceHomeomorph_symm_apply p)).trans <|
    (ofBundlesHomeomorph_symm_apply _ _ _ _ _ _ _).trans <|
      congrArg (TotalSpace.mk p.proj) (ContinuousLinearEquiv.ulift_symm_apply p.2)

variable (𝕜 X) in
/-- Additive, full, and faithful universe-lifting functor on genuine variable-rank bundles. -/
@[expose] noncomputable def uliftFunctor :
    FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankBundle.{max w w'} 𝕜 X where
  obj E := E.ulift.{w, w'}
  map {E F} f :=
    { fiberMap x :=
        (ContinuousLinearEquiv.ulift : ULift.{w'} (F.Fiber x) ≃L[𝕜] F.Fiber x).symm.toLinearMap.comp
          ((f.fiberMap x).comp
            (ContinuousLinearEquiv.ulift : ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).toLinearMap)
      continuous_totalSpaceMap :=
        ((F.uliftHomeomorph.{w, w'}).symm.continuous.comp
          (f.continuous_totalSpaceMap.comp (E.uliftHomeomorph.{w, w'}).continuous)).congr
          fun p ↦ by
            rw [Function.comp_apply, Function.comp_apply, uliftHomeomorph_apply,
              uliftHomeomorph_symm_apply]
            rfl }
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp] theorem uliftFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctor.{w, w'} 𝕜 X).obj E = E.ulift.{w, w'} := (rfl)

@[simp] theorem fiberMap_uliftFunctor_map {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (x : X) :
    ((uliftFunctor.{w, w'} 𝕜 X).map f).fiberMap x =
      (ContinuousLinearEquiv.ulift : ULift.{w'} (F.Fiber x) ≃L[𝕜] F.Fiber x).symm.toLinearMap.comp
        ((f.fiberMap x).comp
          (ContinuousLinearEquiv.ulift : ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).toLinearMap) :=
  (rfl)

/-- `uliftFunctor` preserves addition of bundle morphisms. -/
instance : (uliftFunctor.{w, w'} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

/-- `uliftFunctor` is faithful because `ULift.up` and `ULift.down` are inverse equivalences. -/
instance : (uliftFunctor.{w, w'} 𝕜 X).Faithful where
  map_injective {_ _} _ _ h := hom_ext fun x ↦ LinearMap.ext fun v ↦
    ULift.up_injective (congrArg (fun k ↦ k.fiberMap x (ULift.up v)) h)

/-- `uliftFunctor` is full by conjugating morphisms along `uliftHomeomorph`. -/
instance : (uliftFunctor.{w, w'} 𝕜 X).Full where
  map_surjective {E F} g := by
    let g' : E.ulift.{w, w'} ⟶ F.ulift.{w, w'} := g
    refine ⟨⟨fun x ↦
        (ContinuousLinearEquiv.ulift : ULift.{w'} (F.Fiber x) ≃L[𝕜] F.Fiber x).toLinearMap.comp
          ((g'.fiberMap x).comp
            (ContinuousLinearEquiv.ulift :
              ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).symm.toLinearMap),
      ((F.uliftHomeomorph.{w, w'}).continuous.comp
        (g'.continuous_totalSpaceMap.comp (E.uliftHomeomorph.{w, w'}).symm.continuous)).congr
        fun p ↦ by
          rw [Function.comp_apply, Function.comp_apply, uliftHomeomorph_symm_apply,
            uliftHomeomorph_apply]
          rfl⟩,
      hom_ext (E := E.ulift.{w, w'}) (F := F.ulift.{w, w'}) fun _ ↦ LinearMap.ext fun _ ↦ rfl⟩

/-- Component isomorphism `(E.ulift).toAtlas ≅ E.toAtlas` comparing coordinate presentations. -/
noncomputable def uliftToAtlasApp (E : FiniteRankBundle.{w} 𝕜 X) :
    (E.ulift.{w, w'}).toAtlas ≅ E.toAtlas :=
  FiniteRankAtlas.isoMk (fun x ↦ LinearEquiv.refl 𝕜 (E.toAtlas.Fiber x))
    ((E.reconstructionHomeomorph.symm.continuous.comp ((E.uliftHomeomorph.{w, w'}).continuous.comp
      (E.ulift.{w, w'}).reconstructionHomeomorph.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply,
        (E.ulift.{w, w'}).reconstructionHomeomorph_apply, uliftHomeomorph_apply,
        E.reconstructionHomeomorph_symm_apply, reconstructionFiberEquiv_ulift]
      exact congrArg (TotalSpace.mk p.proj)
        ((E.reconstructionFiberEquiv p.proj).symm_apply_apply p.2))
    (((E.ulift.{w, w'}).reconstructionHomeomorph.symm.continuous.comp
      ((E.uliftHomeomorph.{w, w'}).symm.continuous.comp
        E.reconstructionHomeomorph.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_apply,
        uliftHomeomorph_symm_apply, (E.ulift.{w, w'}).reconstructionHomeomorph_symm_apply,
        reconstructionFiberEquiv_ulift]
      exact congrArg (TotalSpace.mk p.proj)
        ((E.reconstructionFiberEquiv p.proj).symm_apply_apply p.2))

@[simp] theorem fiberMap_uliftToAtlasApp_hom (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (uliftToAtlasApp.{w, w'} E).hom.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_hom (A := (E.ulift.{w, w'}).toAtlas) (D := E.toAtlas) _ _ _ x

@[simp] theorem fiberMap_uliftToAtlasApp_inv (E : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (uliftToAtlasApp.{w, w'} E).inv.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_inv (A := (E.ulift.{w, w'}).toAtlas) (D := E.toAtlas) _ _ _ x

variable (𝕜 X) in
/-- Natural isomorphism `uliftFunctor ⋙ toAtlasFunctor ≅ toAtlasFunctor`. -/
noncomputable def uliftFunctorCompToAtlasIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅ toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (fun E ↦ uliftToAtlasApp.{w, w'} E) fun {E F} f ↦
    FiniteRankAtlas.hom_ext (A := (E.ulift.{w, w'}).toAtlas) (D := F.toAtlas) fun x ↦ by
      rw [Functor.comp_map, FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp,
        fiberMap_uliftToAtlasApp_hom, fiberMap_uliftToAtlasApp_hom]
      refine LinearMap.ext fun v ↦ ?_
      -- Evaluate the exposed `uliftFunctor` and `toAtlasFunctor` actions on `v`.
      change ((F.ulift.{w, w'}).reconstructionFiberEquiv x).symm
          (ULift.up (f.fiberMap x (((E.ulift.{w, w'}).reconstructionFiberEquiv x v).down))) =
        (F.reconstructionFiberEquiv x).symm (f.fiberMap x (E.reconstructionFiberEquiv x v))
      rw [reconstructionFiberEquiv_ulift, reconstructionFiberEquiv_ulift]
      rfl

@[simp] theorem uliftFunctorCompToAtlasIso_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).app E = uliftToAtlasApp.{w, w'} E :=
  Iso.ext rfl

@[simp] theorem uliftFunctorCompToAtlasIso_hom_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).hom.app E = (uliftToAtlasApp.{w, w'} E).hom := (rfl)

@[simp] theorem uliftFunctorCompToAtlasIso_inv_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).inv.app E = (uliftToAtlasApp.{w, w'} E).inv := (rfl)

/-- Under `[Small.{w} 𝕜]`, `uliftFunctor` is an equivalence of categories. -/
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

@[simp] theorem changeUniverseEquivalence_functor [Small.{w₁} 𝕜] [Small.{w₂} 𝕜] :
    (changeUniverseEquivalence.{w₁, w₂} 𝕜 X).functor =
      toAtlasFunctor.{w₁} 𝕜 X ⋙ fromAtlasFunctor.{w₂} 𝕜 X := by
  simp [changeUniverseEquivalence]

@[simp] theorem changeUniverseEquivalence_inverse [Small.{w₁} 𝕜] [Small.{w₂} 𝕜] :
    (changeUniverseEquivalence.{w₁, w₂} 𝕜 X).inverse =
      toAtlasFunctor.{w₂} 𝕜 X ⋙ fromAtlasFunctor.{w₁} 𝕜 X := by
  simp [changeUniverseEquivalence]

/-- The forward functor of `changeUniverseEquivalence` is additive. -/
instance [Small.{w₁} 𝕜] [Small.{w₂} 𝕜] :
    (changeUniverseEquivalence.{w₁, w₂} 𝕜 X).functor.Additive := by
  rw [changeUniverseEquivalence_functor]
  infer_instance

end UniversePolymorphism

end TauCeti.FiniteRankBundle
