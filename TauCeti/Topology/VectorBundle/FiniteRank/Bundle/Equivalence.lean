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
  faithful functor `FiniteRankBundle.toAtlasFunctor` (acting on morphisms via
  `FiniteRankBundle.toAtlasMap`), from which `FiniteRankBundle.isIso_iff_bijective`,
  `LocallySmall.{max u v}`, and `EssentiallySmall.{max u v}` follow without `Small` hypotheses.
  For a constant-rank `VectorBundle 𝕜 (Fin n → 𝕜) V`, `FiniteRankBundle.toAtlasOfBundleIso`
  identifies `(ofBundle 𝕜 n V).toAtlas` with
  `FiniteRankAtlas.ofCore (FiniteRankBundleCore.ofBundle 𝕜 n V)` (matching
  `(FiniteRankAtlas.ofCoreFunctor 𝕜 X).obj` via `FiniteRankAtlas.ofCoreFunctor_obj`), showing that
  the genuine and coordinate constant-rank embeddings commute up to canonical isomorphism (with the
  constant-rank essential image characterized by `FiniteRankAtlas.essImage_ofCoreFunctor_iff`).
* **Stratum bundle transport:** `FiniteRankBundle.reconstructionFiberEquiv_ofBundles` identifies
  `reconstructionFiberEquiv` on the stratumwise transported bundle `FiniteRankBundle.ofBundles`
  (constructed in `TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic`).
* **Equivalence under `[Small.{w} 𝕜]`:** Shrinking coordinate fibres into `Type w` yields the
  additive inverse functor `FiniteRankBundle.fromAtlasFunctor` (acting on morphisms via
  `FiniteRankBundle.fromAtlasMap`) and the explicit equivalence
  `FiniteRankBundle.atlasEquivalence : FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X`.
* **Universe polymorphism:** For arbitrary universes `w, w'`, `FiniteRankBundle.ulift` and the
  additive, full, and faithful `FiniteRankBundle.uliftFunctor` (acting on morphisms via
  `FiniteRankBundle.uliftMap`) lift fibres to `Type (max w w')` and satisfy
  `uliftFunctor ⋙ toAtlasFunctor ≅ toAtlasFunctor`
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

/-- Present a morphism of genuine variable-rank bundles as a morphism of their small
point-indexed `FiniteRankAtlas`es by conjugating along `reconstructionFiberEquiv`. -/
noncomputable def toAtlasMap {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    E.toAtlas ⟶ F.toAtlas where
  fiberMap x := (F.reconstructionFiberEquiv x).symm.toLinearMap.comp
    ((f.fiberMap x).comp (E.reconstructionFiberEquiv x).toLinearMap)
  continuous_totalSpaceMap := (F.reconstructionHomeomorph.symm.continuous.comp
    (f.continuous_totalSpaceMap.comp E.reconstructionHomeomorph.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_apply,
        F.reconstructionHomeomorph_symm_apply]
      rfl

@[simp] theorem fiberMap_toAtlasMap {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (x : X) :
    (toAtlasMap f).fiberMap x =
      (F.reconstructionFiberEquiv x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (E.reconstructionFiberEquiv x).toLinearMap) := (rfl)

@[simp] theorem toAtlasMap_id (E : FiniteRankBundle.{w} 𝕜 X) :
    toAtlasMap (𝟙 E) = 𝟙 E.toAtlas :=
  FiniteRankAtlas.hom_ext fun x ↦
    LinearMap.ext (E.reconstructionFiberEquiv x).symm_apply_apply

@[simp] theorem toAtlasMap_comp {E F G : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (g : F ⟶ G) :
    toAtlasMap (f ≫ g) = toAtlasMap f ≫ toAtlasMap g :=
  FiniteRankAtlas.hom_ext fun x ↦
    LinearMap.ext fun _ ↦ by simp [LinearMap.comp_apply]

@[simp] theorem toAtlasMap_add {E F : FiniteRankBundle.{w} 𝕜 X} (f g : E ⟶ F) :
    toAtlasMap (f + g) = toAtlasMap f + toAtlasMap g :=
  FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    (F.reconstructionFiberEquiv x).symm.map_add (f.fiberMap x _) (g.fiberMap x _)

variable (𝕜 X) in
/-- Additive, full, and faithful functor presenting genuine variable-rank vector bundles by small
variable-rank coordinate atlases. -/
noncomputable def toAtlasFunctor : FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj E := E.toAtlas
  map := toAtlasMap
  map_id := toAtlasMap_id
  map_comp := toAtlasMap_comp

@[simp] theorem toAtlasFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).obj E = E.toAtlas := (rfl)

@[simp] theorem toAtlasFunctor_map {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    (toAtlasFunctor.{w} 𝕜 X).map f =
      eqToHom (toAtlasFunctor_obj E) ≫ toAtlasMap f ≫
        eqToHom (toAtlasFunctor_obj F).symm :=
  (rfl)

/-- `toAtlasFunctor` preserves addition of bundle morphisms. -/
instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {E F f g} := by
    simp only [toAtlasFunctor_map, toAtlasMap_add, Preadditive.comp_add, Preadditive.add_comp]

/-- `toAtlasFunctor` is faithful because `reconstructionFiberEquiv` is an equivalence on each
fibre. -/
instance : (toAtlasFunctor.{w} 𝕜 X).Faithful where
  map_injective {E F} f₁ f₂ h := by
    rw [toAtlasFunctor_map, toAtlasFunctor_map] at h
    have h' : toAtlasMap f₁ = toAtlasMap f₂ :=
      (cancel_mono (eqToHom (toAtlasFunctor_obj F).symm)).1 <|
        (cancel_epi (eqToHom (toAtlasFunctor_obj E))).1 h
    exact hom_ext fun x ↦ LinearMap.ext fun w ↦ by
      have hx := congrArg (fun k ↦ k.fiberMap x ((E.reconstructionFiberEquiv x).symm w)) h'
      simp only [fiberMap_toAtlasMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply] at hx
      exact (F.reconstructionFiberEquiv x).symm.injective hx

/-- `toAtlasFunctor` is full by conjugating coordinate morphisms along
`reconstructionHomeomorph`. -/
instance : (toAtlasFunctor.{w} 𝕜 X).Full where
  map_surjective {E F} g := by
    let g' : E.toAtlas ⟶ F.toAtlas :=
      eqToHom (toAtlasFunctor_obj E).symm ≫ g ≫ eqToHom (toAtlasFunctor_obj F)
    let f : E ⟶ F :=
      ⟨fun x ↦ (F.reconstructionFiberEquiv x).toLinearMap.comp
          ((g'.fiberMap x).comp (E.reconstructionFiberEquiv x).symm.toLinearMap),
        (F.reconstructionHomeomorph.continuous.comp
          (g'.continuous_totalSpaceMap.comp E.reconstructionHomeomorph.symm.continuous)).congr
          fun p ↦ by
            rw [Function.comp_apply, Function.comp_apply, E.reconstructionHomeomorph_symm_apply,
              F.reconstructionHomeomorph_apply]
            rfl⟩
    refine ⟨f, ?_⟩
    have hg : toAtlasMap f = g' :=
      FiniteRankAtlas.hom_ext (A := E.toAtlas) (D := F.toAtlas) fun x ↦ LinearMap.ext fun _ ↦ by
        simp [f, LinearMap.comp_apply]
    rw [toAtlasFunctor_map, hg]
    simp [g']

/-- A morphism of genuine variable-rank bundles is an isomorphism iff every fibre map is
bijective. -/
theorem isIso_iff_bijective {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  rw [← isIso_iff_of_reflects_iso f (toAtlasFunctor.{w} 𝕜 X), toAtlasFunctor_map,
    isIso_comp_left_iff, isIso_comp_right_iff, FiniteRankAtlas.isIso_iff_bijective]
  refine forall_congr' fun x ↦ ?_
  rw [fiberMap_toAtlasMap]
  exact ((F.reconstructionFiberEquiv x).symm.bijective.of_comp_iff' _).trans
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
presenting `V` via `FiniteRankBundleCore.ofBundle` and `FiniteRankAtlas.ofCore`. -/
noncomputable def toAtlasOfBundleIso :
    (ofBundle 𝕜 n V).toAtlas ≅
      FiniteRankAtlas.ofCore (FiniteRankBundleCore.ofBundle 𝕜 n V) :=
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
    (D := FiniteRankAtlas.ofCore (FiniteRankBundleCore.ofBundle 𝕜 n V)) _ _ _ x

@[simp] theorem fiberMap_toAtlasOfBundleIso_inv (x : X) :
    (toAtlasOfBundleIso 𝕜 n V).inv.fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_isoMk_inv (A := (ofBundle 𝕜 n V).toAtlas)
    (D := FiniteRankAtlas.ofCore (FiniteRankBundleCore.ofBundle 𝕜 n V)) _ _ _ x

end ConstantRank

end ToAtlas

/-! ### Compatibility with stratumwise bundle transfer -/

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

/-- Transport a morphism of variable-rank bundle atlases to a morphism of genuine `w`-universe
vector bundles via `fromAtlas` under `[Small.{w} 𝕜]`. -/
noncomputable def fromAtlasMap [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X} (g : A ⟶ D) :
    fromAtlas.{w} A ⟶ fromAtlas.{w} D where
  fiberMap x := (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
    ((g.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap)
  continuous_totalSpaceMap := ((fromAtlasHomeomorph.{w} D).symm.continuous.comp
    (g.continuous_totalSpaceMap.comp (fromAtlasHomeomorph.{w} A).continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply, fromAtlasHomeomorph_apply,
        fromAtlasHomeomorph_symm_apply]
      rfl

@[simp] theorem fiberMap_fromAtlasMap [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X}
    (g : A ⟶ D) (x : X) :
    (fromAtlasMap.{w} g).fiberMap x =
      (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
        ((g.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap) := (rfl)

@[simp] theorem fromAtlasMap_id [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    fromAtlasMap.{w} (𝟙 A) = 𝟙 (fromAtlas.{w} A) :=
  hom_ext fun x ↦
    LinearMap.ext (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm_apply_apply

@[simp] theorem fromAtlasMap_comp [Small.{w} 𝕜] {A B C : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ B) (g : B ⟶ C) :
    fromAtlasMap.{w} (f ≫ g) = fromAtlasMap.{w} f ≫ fromAtlasMap.{w} g :=
  hom_ext fun x ↦ LinearMap.ext fun v ↦
    congrArg (fun w ↦ (Shrink.continuousLinearEquiv 𝕜 (C.Fiber x)).symm (g.fiberMap x w))
      ((Shrink.continuousLinearEquiv 𝕜 (B.Fiber x)).apply_symm_apply
        (f.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) v))).symm

@[simp] theorem fromAtlasMap_add [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X} (f g : A ⟶ D) :
    fromAtlasMap.{w} (f + g) = fromAtlasMap.{w} f + fromAtlasMap.{w} g :=
  hom_ext fun x ↦ LinearMap.ext fun _ ↦
    (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.map_add (f.fiberMap x _) (g.fiberMap x _)

variable (𝕜 X) in
/-- Additive reconstruction functor `FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X` when
`[Small.{w} 𝕜]`. -/
noncomputable def fromAtlasFunctor [Small.{w} 𝕜] :
    FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X where
  obj A := fromAtlas.{w} A
  map := fromAtlasMap.{w}
  map_id := fromAtlasMap_id.{w}
  map_comp := fromAtlasMap_comp.{w}

@[simp] theorem fromAtlasFunctor_obj [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (fromAtlasFunctor.{w} 𝕜 X).obj A = fromAtlas.{w} A := (rfl)

@[simp] theorem fromAtlasFunctor_map [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X} (g : A ⟶ D) :
    (fromAtlasFunctor.{w} 𝕜 X).map g =
      eqToHom (fromAtlasFunctor_obj.{w} A) ≫ fromAtlasMap.{w} g ≫
        eqToHom (fromAtlasFunctor_obj.{w} D).symm :=
  (rfl)

/-- `fromAtlasFunctor` preserves addition of coordinate morphisms. -/
instance [Small.{w} 𝕜] : (fromAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {A D f g} := by
    simp only [fromAtlasFunctor_map, fromAtlasMap_add, Preadditive.comp_add, Preadditive.add_comp]

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

private theorem atlasUnitApp_naturality [Small.{w} 𝕜] {E F : FiniteRankBundle.{w} 𝕜 X}
    (f : E ⟶ F) :
    f ≫ (atlasUnitApp.{w} F).hom =
      (atlasUnitApp.{w} E).hom ≫ fromAtlasMap.{w} (toAtlasMap f) :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_atlasUnitApp_hom, fiberMap_atlasUnitApp_hom,
      fiberMap_fromAtlasMap, fiberMap_toAtlasMap]
    exact LinearMap.ext fun v ↦
      congrArg (fun w ↦ (Shrink.continuousLinearEquiv 𝕜 (F.toAtlas.Fiber x)).symm
        ((F.reconstructionFiberEquiv x).symm (f.fiberMap x w))) <|
        ((E.reconstructionFiberEquiv x).apply_symm_apply v).symm.trans <|
          congrArg (E.reconstructionFiberEquiv x)
            ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).apply_symm_apply _).symm

variable (𝕜 X) in
/-- Unit natural isomorphism `𝟭 _ ≅ toAtlasFunctor ⋙ fromAtlasFunctor`. -/
noncomputable def atlasUnitIso [Small.{w} 𝕜] :
    𝟭 (FiniteRankBundle.{w} 𝕜 X) ≅ toAtlasFunctor.{w} 𝕜 X ⋙ fromAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents
    (fun E ↦ atlasUnitApp.{w} E ≪≫
      eqToIso (by rw [Functor.comp_obj, toAtlasFunctor_obj, fromAtlasFunctor_obj]))
    fun {E F} f ↦ by
      rw [Functor.id_map, Functor.comp_map, toAtlasFunctor_map, Functor.map_comp,
        Functor.map_comp, eqToHom_map, eqToHom_map, fromAtlasFunctor_map]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [← Category.assoc f, atlasUnitApp_naturality, Category.assoc]

@[simp] theorem atlasUnitIso_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).app E =
      atlasUnitApp.{w} E ≪≫
        eqToIso (by rw [Functor.comp_obj, toAtlasFunctor_obj, fromAtlasFunctor_obj]) :=
  Iso.ext rfl

@[simp] theorem atlasUnitIso_hom_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).hom.app E =
      (atlasUnitApp.{w} E).hom ≫
        eqToHom (by rw [Functor.comp_obj, toAtlasFunctor_obj, fromAtlasFunctor_obj]) :=
  (rfl)

@[simp] theorem atlasUnitIso_inv_app [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    (atlasUnitIso.{w} 𝕜 X).inv.app E =
      eqToHom (by rw [Functor.comp_obj, toAtlasFunctor_obj, fromAtlasFunctor_obj]) ≫
        (atlasUnitApp.{w} E).inv :=
  (rfl)

private theorem atlasCounitApp_naturality [Small.{w} 𝕜] {A D : FiniteRankAtlas 𝕜 X}
    (g : A ⟶ D) :
    toAtlasMap (fromAtlasMap.{w} g) ≫ (atlasCounitApp.{w} D).hom =
      (atlasCounitApp.{w} A).hom ≫ g :=
  FiniteRankAtlas.hom_ext (A := (fromAtlas.{w} A).toAtlas) (D := D) fun x ↦ by
    rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp,
      fiberMap_atlasCounitApp_hom, fiberMap_atlasCounitApp_hom,
      fiberMap_toAtlasMap, fiberMap_fromAtlasMap,
      reconstructionFiberEquiv_fromAtlas, reconstructionFiberEquiv_fromAtlas]
    exact LinearMap.ext fun v ↦
      ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).apply_symm_apply _).trans <|
        congrArg (g.fiberMap x)
          ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).apply_symm_apply v)

variable (𝕜 X) in
/-- Counit natural isomorphism `fromAtlasFunctor ⋙ toAtlasFunctor ≅ 𝟭 _`. -/
noncomputable def atlasCounitIso [Small.{w} 𝕜] :
    fromAtlasFunctor.{w} 𝕜 X ⋙ toAtlasFunctor.{w} 𝕜 X ≅ 𝟭 (FiniteRankAtlas 𝕜 X) :=
  NatIso.ofComponents
    (fun A ↦ eqToIso (by rw [Functor.comp_obj, fromAtlasFunctor_obj, toAtlasFunctor_obj]) ≪≫
      atlasCounitApp.{w} A)
    fun {A D} g ↦ by
      rw [Functor.comp_map, Functor.id_map, fromAtlasFunctor_map, Functor.map_comp,
        Functor.map_comp, eqToHom_map, eqToHom_map, toAtlasFunctor_map]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      exact congrArg (eqToHom _ ≫ ·) (atlasCounitApp_naturality.{w} g)

@[simp] theorem atlasCounitIso_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).app A =
      eqToIso (by rw [Functor.comp_obj, fromAtlasFunctor_obj, toAtlasFunctor_obj]) ≪≫
        atlasCounitApp.{w} A :=
  Iso.ext rfl

@[simp] theorem atlasCounitIso_hom_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).hom.app A =
      eqToHom (by rw [Functor.comp_obj, fromAtlasFunctor_obj, toAtlasFunctor_obj]) ≫
        (atlasCounitApp.{w} A).hom :=
  (rfl)

@[simp] theorem atlasCounitIso_inv_app [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (atlasCounitIso.{w} 𝕜 X).inv.app A =
      (atlasCounitApp.{w} A).inv ≫
        eqToHom (by rw [Functor.comp_obj, fromAtlasFunctor_obj, toAtlasFunctor_obj]) :=
  (rfl)

private theorem toAtlasMap_atlasUnitApp_comp [Small.{w} 𝕜] (E : FiniteRankBundle.{w} 𝕜 X) :
    toAtlasMap (atlasUnitApp.{w} E).hom ≫ (atlasCounitApp.{w} E.toAtlas).hom = 𝟙 E.toAtlas :=
  FiniteRankAtlas.hom_ext (A := E.toAtlas) (D := E.toAtlas) fun x ↦ by
    rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_id,
      fiberMap_atlasCounitApp_hom, fiberMap_toAtlasMap,
      fiberMap_atlasUnitApp_hom, reconstructionFiberEquiv_fromAtlas]
    exact LinearMap.ext fun v ↦
      ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).apply_symm_apply _).trans
        ((E.reconstructionFiberEquiv x).symm_apply_apply v)

variable (𝕜 X) in
/-- Explicit equivalence of categories `FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X` whenever
`[Small.{w} 𝕜]` holds. -/
noncomputable def atlasEquivalence [Small.{w} 𝕜] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor.{w} 𝕜 X
  inverse := fromAtlasFunctor.{w} 𝕜 X
  unitIso := atlasUnitIso.{w} 𝕜 X
  counitIso := atlasCounitIso.{w} 𝕜 X
  functor_unitIso_comp E := by
    rw [atlasUnitIso_hom_app, atlasCounitIso_hom_app, Functor.map_comp, eqToHom_map,
      toAtlasFunctor_map]
    simp only [Category.assoc, eqToHom_trans_assoc]
    have h : ∀ {A : FiniteRankAtlas 𝕜 X} (hA : A = E.toAtlas),
        eqToHom (by rw [hA]) ≫ (atlasCounitApp.{w} A).hom =
          (atlasCounitApp.{w} E.toAtlas).hom ≫ eqToHom hA.symm := by
      rintro _ rfl; simp
    rw [h (toAtlasFunctor_obj E), ← Category.assoc (toAtlasMap _),
      toAtlasMap_atlasUnitApp_comp, Category.id_comp, eqToHom_trans, eqToHom_refl]

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

/-- Lift a morphism of genuine variable-rank bundles along `ULift` to `Type (max w w')`. -/
noncomputable def uliftMap {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    E.ulift.{w, w'} ⟶ F.ulift.{w, w'} where
  fiberMap x :=
    (ContinuousLinearEquiv.ulift : ULift.{w'} (F.Fiber x) ≃L[𝕜] F.Fiber x).symm.toLinearMap.comp
      ((f.fiberMap x).comp
        (ContinuousLinearEquiv.ulift : ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).toLinearMap)
  continuous_totalSpaceMap :=
    ((F.uliftHomeomorph.{w, w'}).symm.continuous.comp
      (f.continuous_totalSpaceMap.comp (E.uliftHomeomorph.{w, w'}).continuous)).congr
      fun p ↦ by
        rw [Function.comp_apply, Function.comp_apply, uliftHomeomorph_apply,
          uliftHomeomorph_symm_apply]
        rfl

@[simp] theorem fiberMap_uliftMap {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (x : X) :
    (uliftMap.{w, w'} f).fiberMap x =
      (ContinuousLinearEquiv.ulift : ULift.{w'} (F.Fiber x) ≃L[𝕜] F.Fiber x).symm.toLinearMap.comp
        ((f.fiberMap x).comp
          (ContinuousLinearEquiv.ulift : ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).toLinearMap) :=
  (rfl)

@[simp] theorem uliftMap_id (E : FiniteRankBundle.{w} 𝕜 X) :
    uliftMap.{w, w'} (𝟙 E) = 𝟙 (E.ulift.{w, w'}) :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp] theorem uliftMap_comp {E F G : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) (g : F ⟶ G) :
    uliftMap.{w, w'} (f ≫ g) = uliftMap.{w, w'} f ≫ uliftMap.{w, w'} g :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp] theorem uliftMap_add {E F : FiniteRankBundle.{w} 𝕜 X} (f g : E ⟶ F) :
    uliftMap.{w, w'} (f + g) = uliftMap.{w, w'} f + uliftMap.{w, w'} g :=
  hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

variable (𝕜 X) in
/-- Additive, full, and faithful universe-lifting functor on genuine variable-rank bundles. -/
noncomputable def uliftFunctor :
    FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankBundle.{max w w'} 𝕜 X where
  obj E := E.ulift.{w, w'}
  map := uliftMap.{w, w'}
  map_id := uliftMap_id.{w, w'}
  map_comp := uliftMap_comp.{w, w'}

@[simp] theorem uliftFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctor.{w, w'} 𝕜 X).obj E = E.ulift.{w, w'} := (rfl)

@[simp] theorem uliftFunctor_map {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    (uliftFunctor.{w, w'} 𝕜 X).map f =
      eqToHom (uliftFunctor_obj.{w, w'} E) ≫ uliftMap.{w, w'} f ≫
        eqToHom (uliftFunctor_obj.{w, w'} F).symm :=
  (rfl)

/-- `uliftFunctor` preserves addition of bundle morphisms. -/
instance : (uliftFunctor.{w, w'} 𝕜 X).Additive where
  map_add {E F f g} := by
    simp only [uliftFunctor_map, uliftMap_add, Preadditive.comp_add, Preadditive.add_comp]

/-- `uliftFunctor` is faithful because `ULift.up` and `ULift.down` are inverse equivalences. -/
instance : (uliftFunctor.{w, w'} 𝕜 X).Faithful where
  map_injective {E F} f₁ f₂ h := by
    rw [uliftFunctor_map, uliftFunctor_map] at h
    have h' : uliftMap.{w, w'} f₁ = uliftMap.{w, w'} f₂ :=
      (cancel_mono (eqToHom (uliftFunctor_obj.{w, w'} F).symm)).1 <|
        (cancel_epi (eqToHom (uliftFunctor_obj.{w, w'} E))).1 h
    exact hom_ext fun x ↦ LinearMap.ext fun v ↦
      ULift.up_injective <| by
        have hx := congrArg (fun k ↦ k.fiberMap x (ULift.up v)) h'
        rw [fiberMap_uliftMap, fiberMap_uliftMap] at hx
        exact hx

/-- `uliftFunctor` is full by conjugating morphisms along `uliftHomeomorph`. -/
instance : (uliftFunctor.{w, w'} 𝕜 X).Full where
  map_surjective {E F} g := by
    let g' : E.ulift.{w, w'} ⟶ F.ulift.{w, w'} :=
      eqToHom (uliftFunctor_obj.{w, w'} E).symm ≫ g ≫ eqToHom (uliftFunctor_obj.{w, w'} F)
    let f : E ⟶ F :=
      ⟨fun x ↦
          (ContinuousLinearEquiv.ulift : ULift.{w'} (F.Fiber x) ≃L[𝕜] F.Fiber x).toLinearMap.comp
            ((g'.fiberMap x).comp
              (ContinuousLinearEquiv.ulift :
                ULift.{w'} (E.Fiber x) ≃L[𝕜] E.Fiber x).symm.toLinearMap),
        ((F.uliftHomeomorph.{w, w'}).continuous.comp
          (g'.continuous_totalSpaceMap.comp (E.uliftHomeomorph.{w, w'}).symm.continuous)).congr
          fun p ↦ by
            rw [Function.comp_apply, Function.comp_apply, uliftHomeomorph_symm_apply,
              uliftHomeomorph_apply]
            rfl⟩
    refine ⟨f, ?_⟩
    have hg : uliftMap.{w, w'} f = g' := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
    rw [uliftFunctor_map, hg]
    simp [g']

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

private theorem uliftToAtlasApp_naturality {E F : FiniteRankBundle.{w} 𝕜 X} (f : E ⟶ F) :
    toAtlasMap (uliftMap.{w, w'} f) ≫ (uliftToAtlasApp.{w, w'} F).hom =
      (uliftToAtlasApp.{w, w'} E).hom ≫ toAtlasMap f :=
  FiniteRankAtlas.hom_ext (A := (E.ulift.{w, w'}).toAtlas) (D := F.toAtlas) fun x ↦ by
    rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp,
      fiberMap_uliftToAtlasApp_hom, fiberMap_uliftToAtlasApp_hom,
      fiberMap_toAtlasMap, fiberMap_toAtlasMap, fiberMap_uliftMap,
      reconstructionFiberEquiv_ulift, reconstructionFiberEquiv_ulift]
    exact LinearMap.ext fun _ ↦ rfl

variable (𝕜 X) in
/-- Natural isomorphism `uliftFunctor ⋙ toAtlasFunctor ≅ toAtlasFunctor`. -/
noncomputable def uliftFunctorCompToAtlasIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅ toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents
    (fun E ↦
      eqToIso (by rw [Functor.comp_obj, uliftFunctor_obj, toAtlasFunctor_obj]) ≪≫
        uliftToAtlasApp.{w, w'} E ≪≫ eqToIso (toAtlasFunctor_obj E).symm)
    fun {E F} f ↦ by
      rw [Functor.comp_map, uliftFunctor_map, Functor.map_comp, Functor.map_comp,
        eqToHom_map, eqToHom_map, toAtlasFunctor_map, toAtlasFunctor_map]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (toAtlasMap (uliftMap.{w, w'} f)), uliftToAtlasApp_naturality,
        Category.assoc]

@[simp] theorem uliftFunctorCompToAtlasIso_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).app E =
      eqToIso (by rw [Functor.comp_obj, uliftFunctor_obj, toAtlasFunctor_obj]) ≪≫
        uliftToAtlasApp.{w, w'} E ≪≫ eqToIso (toAtlasFunctor_obj E).symm :=
  Iso.ext rfl

@[simp] theorem uliftFunctorCompToAtlasIso_hom_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).hom.app E =
      eqToHom (by rw [Functor.comp_obj, uliftFunctor_obj, toAtlasFunctor_obj]) ≫
        (uliftToAtlasApp.{w, w'} E).hom ≫ eqToHom (toAtlasFunctor_obj E).symm :=
  (rfl)

@[simp] theorem uliftFunctorCompToAtlasIso_inv_app (E : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctorCompToAtlasIso.{w, w'} 𝕜 X).inv.app E =
      eqToHom (toAtlasFunctor_obj E) ≫ (uliftToAtlasApp.{w, w'} E).inv ≫
        eqToHom (by rw [Functor.comp_obj, uliftFunctor_obj, toAtlasFunctor_obj]) :=
  (rfl)

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
