/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import TauCeti.Topology.VectorBundle.ULift
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Categorical equivalence with small coordinate atlases and universe independence

Every `V : FiniteRankVectorBundle.{u, v, w} 𝕜 X` yields a small coordinate atlas
`V.toAtlas : FiniteRankAtlas 𝕜 X` via point-indexed stratum cores, defining an unconditionally
additive and fully faithful functor `toAtlasFunctor 𝕜 X` with no completeness assumption on `𝕜`
and no compactness, finite-cover, or separation hypotheses on `X`. Consequently:
* `FiniteRankVectorBundle.isIso_iff_bijective` characterizes isomorphisms over `[CompleteSpace 𝕜]`
  by fibrewise bijectivity;
* `FiniteRankVectorBundle.{u, v, w} 𝕜 X` is `EssentiallySmall.{max u v}` in every universe `w`;
* under `[UnivLE.{v, w}]`, `FiniteRankAtlas.toBundle` reconstructs a `Type w`-fibred bundle and
  `toAtlasFunctor 𝕜 X` becomes an equivalence `atlasEquivalence 𝕜 X`;
* `uliftFunctor 𝕜 X` is unconditionally additive and fully faithful, commutes with `toAtlasFunctor`
  up to `uliftToAtlasNatIso`, and yields `changeUniverseEquivalence` whenever `[UnivLE.{v, w}]` and
  `[UnivLE.{v, w'}]`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti

universe u v w w'

section ToAtlas

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankVectorBundle

/-- Encode a variable-rank vector bundle as a small coordinate atlas via point-indexed stratum
cores. -/
-- Expose the rank projection so `V.toAtlas.Fiber x` reduces to `Fin (V.rank x) → 𝕜`.
@[expose, implicit_reducible]
noncomputable def toAtlas (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 V.rank V.StratumFiber

@[simp] theorem rank_toAtlas (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    V.toAtlas.rank = V.rank := (rfl)

/-- The preferred-chart continuous linear equivalence between `V.Fiber x` and the coordinate fibre
`V.toAtlas.Fiber x = (Fin (V.rank x) → 𝕜)`. -/
noncomputable def toAtlasFiberEquiv (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X) :
    V.Fiber x ≃L[𝕜] V.toAtlas.Fiber x :=
  (pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x)) ⟨x, rfl⟩).symm

/-- The canonical homeomorphism over `X` between the glued total space of `V` and the reconstructed
total space of `V.toAtlas`. -/
noncomputable def toAtlasTotalSpaceHomeomorph (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    TotalSpace Unit V.Fiber ≃ₜ TotalSpace Unit V.toAtlas.Fiber :=
  ((FiniteRankAtlas.reconstructionHomeomorph 𝕜 V.rank V.StratumFiber).trans
    V.totalSpaceHomeomorph).symm

@[simp] theorem toAtlasTotalSpaceHomeomorph_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (p : TotalSpace Unit V.Fiber) :
    V.toAtlasTotalSpaceHomeomorph p = ⟨p.proj, V.toAtlasFiberEquiv p.proj p.2⟩ := by
  simp only [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_trans_apply,
    totalSpaceHomeomorph_symm_apply, FiniteRankAtlas.reconstructionHomeomorph_symm_apply,
    FiniteRankAtlas.totalSpaceHomeomorph_apply]
  rfl

@[simp] theorem toAtlasTotalSpaceHomeomorph_symm_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (q : TotalSpace Unit V.toAtlas.Fiber) :
    V.toAtlasTotalSpaceHomeomorph.symm q = ⟨q.proj, (V.toAtlasFiberEquiv q.proj).symm q.2⟩ := by
  simp only [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_symm, Homeomorph.trans_apply,
    FiniteRankAtlas.reconstructionHomeomorph_apply, totalSpaceHomeomorph_apply]
  rfl

variable (𝕜 X) in
/-- Pass from variable-rank vector bundles with fibres in `Type w` to small coordinate atlases by
reading fibres and morphisms in preferred stratum charts. -/
-- Expose the object assignment so evaluated morphisms act on `V.toAtlas.Fiber`.
@[expose, reducible]
noncomputable def toAtlasFunctor :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj V := V.toAtlas
  map {V W} f :=
    { fiberMap x := (W.toAtlasFiberEquiv x).toLinearMap.comp
        ((f.fiberMap x).comp (V.toAtlasFiberEquiv x).symm.toLinearMap)
      continuous_totalSpaceMap :=
        (W.toAtlasTotalSpaceHomeomorph.continuous.comp
          (f.totalSpaceMap.continuous.comp V.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr
          fun q ↦ by
            dsimp only [Function.comp_apply]
            rw [toAtlasTotalSpaceHomeomorph_symm_apply, Hom.totalSpaceMap_mk,
              toAtlasTotalSpaceHomeomorph_apply]; rfl }
  map_id V := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext (V.toAtlasFiberEquiv x).apply_symm_apply
  map_comp {V W U} f g := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    simp only [FiniteRankAtlas.fiberMap_comp, fiberMap_comp, LinearMap.comp_apply]
    -- Peel the outer linear maps so `symm_apply_apply` cancels the middle `W` chart equivalence.
    change U.toAtlasFiberEquiv x (g.fiberMap x (f.fiberMap x ((V.toAtlasFiberEquiv x).symm u))) =
      U.toAtlasFiberEquiv x (g.fiberMap x
        ((W.toAtlasFiberEquiv x).symm
          (W.toAtlasFiberEquiv x (f.fiberMap x ((V.toAtlasFiberEquiv x).symm u)))))
    rw [ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem toAtlasFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (toAtlasFunctor.{u, v, w} 𝕜 X).obj V = V.toAtlas := (rfl)

@[simp] theorem fiberMap_toAtlasFunctor_map {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (f : V ⟶ W) (x : X) (u : V.toAtlas.Fiber x) :
    ((toAtlasFunctor.{u, v, w} 𝕜 X).map f).fiberMap x u =
      W.toAtlasFiberEquiv x (f.fiberMap x ((V.toAtlasFiberEquiv x).symm u)) := (rfl)

instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Additive where
  map_add {_ _} _ _ := FiniteRankAtlas.hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    rw [FiniteRankAtlas.fiberMap_add, LinearMap.add_apply, fiberMap_toAtlasFunctor_map,
      fiberMap_toAtlasFunctor_map, fiberMap_toAtlasFunctor_map, fiberMap_add, LinearMap.add_apply,
      map_add]

variable (𝕜 X) in
/-- `toAtlasFunctor 𝕜 X` is unconditionally fully faithful in every fibre universe `w`. -/
noncomputable def fullyFaithfulToAtlasFunctor :
    (toAtlasFunctor.{u, v, w} 𝕜 X).FullyFaithful where
  preimage {V W} g :=
    { fiberMap x := (W.toAtlasFiberEquiv x).symm.toLinearMap.comp
        ((g.fiberMap x).comp (V.toAtlasFiberEquiv x).toLinearMap)
      continuous_totalSpaceMap :=
        (W.toAtlasTotalSpaceHomeomorph.symm.continuous.comp
          (g.totalSpaceMap.continuous.comp V.toAtlasTotalSpaceHomeomorph.continuous)).congr
          fun p ↦ by
            dsimp only [Function.comp_apply]
            rw [toAtlasTotalSpaceHomeomorph_apply, FiniteRankAtlas.Hom.totalSpaceMap_mk,
              toAtlasTotalSpaceHomeomorph_symm_apply]; rfl }
  map_preimage {V W} g := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    rw [fiberMap_toAtlasFunctor_map]
    change W.toAtlasFiberEquiv x ((W.toAtlasFiberEquiv x).symm
        (g.fiberMap x (V.toAtlasFiberEquiv x ((V.toAtlasFiberEquiv x).symm u)))) = g.fiberMap x u
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  preimage_map {V W} f := hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    change (W.toAtlasFiberEquiv x).symm (W.toAtlasFiberEquiv x
        (f.fiberMap x ((V.toAtlasFiberEquiv x).symm (V.toAtlasFiberEquiv x v)))) = f.fiberMap x v
    simp only [ContinuousLinearEquiv.symm_apply_apply]

instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Full := (fullyFaithfulToAtlasFunctor.{u, v, w} 𝕜 X).full

instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Faithful :=
  (fullyFaithfulToAtlasFunctor.{u, v, w} 𝕜 X).faithful

/-- Over a complete scalar field `𝕜`, a morphism of variable-rank vector bundles is an isomorphism
if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective [CompleteSpace 𝕜]
    {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X} (f : V ⟶ W) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  have hIso : IsIso f ↔ IsIso ((toAtlasFunctor.{u, v, w} 𝕜 X).map f) :=
    ⟨fun _ ↦ (toAtlasFunctor.{u, v, w} 𝕜 X).map_isIso f,
      fun _ ↦ isIso_of_fully_faithful (toAtlasFunctor.{u, v, w} 𝕜 X) f⟩
  rw [hIso, FiniteRankAtlas.isIso_iff_bijective]
  refine forall_congr' fun x ↦ ?_
  change Function.Bijective
      (⇑(W.toAtlasFiberEquiv x) ∘ ⇑(f.fiberMap x) ∘ ⇑(V.toAtlasFiberEquiv x).symm) ↔
    Function.Bijective (f.fiberMap x)
  rw [(W.toAtlasFiberEquiv x).bijective.of_comp_iff',
    (V.toAtlasFiberEquiv x).symm.bijective.of_comp_iff]

instance : EssentiallySmall.{max u v} (FiniteRankVectorBundle.{u, v, w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{u, v, w} 𝕜 X)

end FiniteRankVectorBundle

end ToAtlas

section Equivalence

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

/-- Realize a small coordinate atlas `A : FiniteRankAtlas 𝕜 X` as a variable-rank vector bundle
with fibres in `Type w` whenever `UnivLE.{v, w}` holds. -/
-- Expose the rank and fibre projections so `(A.toBundle).Fiber` reduces to `Shrink (A.Fiber ·)`.
@[expose, implicit_reducible]
noncomputable def FiniteRankAtlas.toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X :=
  let φ (n : ℕ) (y : {x : X // A.rank x = n}) :
      Shrink.{w} (A.Fiber y.1) ≃L[𝕜] (A.charts n).Fiber y :=
    (Shrink.continuousLinearEquiv 𝕜 (A.Fiber y.1)).trans
      { toFun u i := u (Fin.cast y.2.symm i)
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        invFun v i := v (Fin.cast y.2 i)
        left_inv u := funext fun _ ↦ by simp
        right_inv v := funext fun _ ↦ by simp
        continuous_toFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.2.symm i)
        continuous_invFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.2 i) }
  let ts (n : ℕ) : TopologicalSpace
      (TotalSpace (Fin n → 𝕜) (fun y : {x : X // A.rank x = n} ↦ Shrink.{w} (A.Fiber y.1))) :=
    TopologicalSpace.induced
      (fun p ↦ (⟨p.proj, φ n p.proj p.2⟩ : TotalSpace (Fin n → 𝕜) (A.charts n).Fiber)) inferInstance
  { rank := A.rank
    Fiber x := Shrink.{w} (A.Fiber x)
    topologicalSpaceStratumTotalSpace := ts
    fiberBundleStratum n :=
      @fiberBundleOfHomeomorph _ (Fin n → 𝕜) (A.charts n).Fiber (fun y ↦ Shrink.{w} (A.Fiber y.1))
        _ (ts n) _ _ _ _ _ (fun y ↦ (φ n y).toHomeomorph) ⟨rfl⟩
    vectorBundleStratum n := by
      let _ := ts n
      exact vectorBundleOfContinuousLinearEquiv 𝕜 (φ n) ⟨rfl⟩ }

@[simp] theorem FiniteRankAtlas.rank_toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] :
    (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).rank = A.rank := (rfl)

@[simp] theorem FiniteRankAtlas.fiber_toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] (x : X) :
    (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber x = Shrink.{w} (A.Fiber x) := (rfl)

/-- The glued total space of `A.toBundle` is homeomorphic over `X` to `TotalSpace Unit A.Fiber` via
`Shrink.continuousLinearEquiv` on each fibre. -/
noncomputable def FiniteRankAtlas.toBundleTotalSpaceHomeomorph (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] :
    TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit A.Fiber :=
  let φ (n : ℕ) (y : {x : X // A.rank x = n}) :
      Shrink.{w} (A.Fiber y.1) ≃ (A.charts n).Fiber y :=
    ((equivShrink (A.Fiber y.1)).symm).trans
      { toFun u i := u (Fin.cast y.2.symm i)
        invFun v i := v (Fin.cast y.2 i)
        left_inv u := funext fun _ ↦ by simp
        right_inv v := funext fun _ ↦ by simp }
  let hStratum (n : ℕ) :
      TotalSpace (Fin n → 𝕜)
          ((A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).StratumFiber n) ≃ₜ
        TotalSpace (Fin n → 𝕜) (A.charts n).Fiber :=
    totalSpaceHomeomorphOfIsInducing (Fin n → 𝕜) (φ n) ⟨rfl⟩
  let hGlued :
      (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).GluedTotalSpace ≃ₜ A.GluedTotalSpace :=
    { toFun q := ⟨q.1, hStratum q.1 q.2⟩
      invFun q := ⟨q.1, (hStratum q.1).symm q.2⟩
      left_inv := fun ⟨_, _⟩ ↦ by simp only [Homeomorph.symm_apply_apply]
      right_inv := fun ⟨_, _⟩ ↦ by simp only [Homeomorph.apply_symm_apply]
      continuous_toFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp (hStratum n).continuous
      continuous_invFun := continuous_sigma fun n ↦
        continuous_sigmaMk.comp (hStratum n).symm.continuous }
  (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).totalSpaceHomeomorph.symm.trans
    (hGlued.trans A.totalSpaceHomeomorph)

@[simp] theorem FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}]
    (p : TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber) :
    A.toBundleTotalSpaceHomeomorph p =
      ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.2⟩ := by
  simp only [toBundleTotalSpaceHomeomorph, Homeomorph.trans_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply, totalSpaceHomeomorphOfIsInducing_apply,
    FiniteRankAtlas.totalSpaceHomeomorph_apply]
  rfl

@[simp] theorem FiniteRankAtlas.toBundleTotalSpaceHomeomorph_symm_apply (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] (q : TotalSpace Unit A.Fiber) :
    (A.toBundleTotalSpaceHomeomorph :
        TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber ≃ₜ _).symm q =
      ⟨q.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber q.proj)).symm q.2⟩ := by
  simp only [toBundleTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    FiniteRankAtlas.totalSpaceHomeomorph_symm_apply, totalSpaceHomeomorphOfIsInducing_symm_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_apply]
  rfl

namespace FiniteRankVectorBundle

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundle ≅ A` in `FiniteRankAtlas 𝕜 X`. -/
noncomputable def toAtlasToBundleIso (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] :
    (toAtlasFunctor.{u, v, w} 𝕜 X).obj A.toBundle ≅ A :=
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  FiniteRankAtlas.isoMk
    (fun x ↦ ((V.toAtlasFiberEquiv x).symm.trans
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x))).toLinearEquiv)
    ((A.toBundleTotalSpaceHomeomorph.continuous.comp
        V.toAtlasTotalSpaceHomeomorph.symm.continuous).congr fun q ↦ by
      dsimp only [Function.comp_apply]
      rw [toAtlasTotalSpaceHomeomorph_symm_apply,
        FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply]; rfl)
    ((V.toAtlasTotalSpaceHomeomorph.continuous.comp
        A.toBundleTotalSpaceHomeomorph.symm.continuous).congr fun q ↦ by
      dsimp only [Function.comp_apply]
      rw [FiniteRankAtlas.toBundleTotalSpaceHomeomorph_symm_apply,
        toAtlasTotalSpaceHomeomorph_apply]; rfl)

instance [UnivLE.{v, w}] : (toAtlasFunctor.{u, v, w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundle, ⟨toAtlasToBundleIso A⟩⟩

instance [UnivLE.{v, w}] : (toAtlasFunctor.{u, v, w} 𝕜 X).IsEquivalence where

variable (𝕜 X) in
/-- When the fibre universe `w` is at least the scalar field universe `v`, variable-rank vector
bundles with fibres in `Type w` are categorically equivalent to small coordinate atlases. -/
noncomputable def atlasEquivalence [UnivLE.{v, w}] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X :=
  (toAtlasFunctor.{u, v, w} 𝕜 X).asEquivalence

end FiniteRankVectorBundle

end Equivalence

section ULift

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankVectorBundle

/-- Lift the fibres of a variable-rank vector bundle from `Type w` to `Type (max w w')`. -/
-- Expose the rank and fibre projections so `V.ulift.Fiber` reduces to `ULift (V.Fiber ·)`.
@[expose, implicit_reducible]
noncomputable def ulift (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X where
  rank := V.rank
  Fiber x := ULift.{w'} (V.Fiber x)

@[simp] theorem rank_ulift (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).rank = V.rank := (rfl)

@[simp] theorem fiber_ulift (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x =
      ULift.{w'} (V.Fiber x) := (rfl)

/-- The glued total space of `V.ulift` is homeomorphic over `X` to `TotalSpace Unit V.Fiber` via
`ULift.down` on fibres. -/
noncomputable def uliftTotalSpaceHomeomorph (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit V.Fiber :=
  let hGlued :
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).GluedTotalSpace ≃ₜ
        V.GluedTotalSpace :=
    { toFun q := ⟨q.1, TauCeti.uliftTotalSpaceHomeomorph (Fin q.1 → 𝕜) (V.StratumFiber q.1) q.2⟩
      invFun q :=
        ⟨q.1, (TauCeti.uliftTotalSpaceHomeomorph (Fin q.1 → 𝕜) (V.StratumFiber q.1)).symm q.2⟩
      left_inv := fun ⟨_, _⟩ ↦ by simp only [Homeomorph.symm_apply_apply]
      right_inv := fun ⟨_, _⟩ ↦ by simp only [Homeomorph.apply_symm_apply]
      continuous_toFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp
        (TauCeti.uliftTotalSpaceHomeomorph (Fin n → 𝕜) (V.StratumFiber n)).continuous
      continuous_invFun := continuous_sigma fun n ↦ continuous_sigmaMk.comp
        (TauCeti.uliftTotalSpaceHomeomorph (Fin n → 𝕜) (V.StratumFiber n)).symm.continuous }
  (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).totalSpaceHomeomorph.symm.trans
    (hGlued.trans V.totalSpaceHomeomorph)

@[simp] theorem uliftTotalSpaceHomeomorph_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (p : TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber) :
    V.uliftTotalSpaceHomeomorph p = ⟨p.proj, p.2.down⟩ := by
  simp only [uliftTotalSpaceHomeomorph, Homeomorph.trans_apply, totalSpaceHomeomorph_symm_apply,
    TauCeti.uliftTotalSpaceHomeomorph_apply, totalSpaceHomeomorph_apply]
  rfl

@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (p : TotalSpace Unit V.Fiber) :
    (V.uliftTotalSpaceHomeomorph :
        TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber ≃ₜ _).symm p =
      ⟨p.proj, ULift.up p.2⟩ := by
  simp only [uliftTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    totalSpaceHomeomorph_symm_apply, TauCeti.uliftTotalSpaceHomeomorph_symm_apply,
    totalSpaceHomeomorph_apply]
  rfl

variable (𝕜 X) in
/-- Lift variable-rank vector bundles and their morphisms from fibre universe `w` to `max w w'`. -/
-- Expose the object assignment so evaluated morphisms act on `ULift (V.Fiber ·)`.
@[expose, implicit_reducible]
noncomputable def uliftFunctor :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X where
  obj V := V.ulift
  map {V W} f :=
    { fiberMap x :=
        (ContinuousLinearEquiv.ulift : ULift.{w'} (W.Fiber x) ≃L[𝕜] W.Fiber x).symm.toLinearMap.comp
          ((f.fiberMap x).comp
            (ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).toLinearMap)
      continuous_totalSpaceMap :=
        (W.uliftTotalSpaceHomeomorph.symm.continuous.comp
          (f.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.continuous)).congr fun p ↦ by
            dsimp only [Function.comp_apply]
            rw [uliftTotalSpaceHomeomorph_apply, Hom.totalSpaceMap_mk,
              uliftTotalSpaceHomeomorph_symm_apply]; rfl }
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

@[simp] theorem uliftFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V =
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X) := (rfl)

@[simp] theorem fiberMap_uliftFunctor_map {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (f : V ⟶ W) (x : X) (v : ULift.{w'} (V.Fiber x)) :
    ((uliftFunctor.{u, v, w, w'} 𝕜 X).map f).fiberMap x v = ULift.up (f.fiberMap x v.down) := (rfl)

instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Additive where
  map_add {_ _} _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

variable (𝕜 X) in
/-- `uliftFunctor 𝕜 X` is unconditionally fully faithful in all universes `u, v, w, w'`. -/
noncomputable def fullyFaithfulUliftFunctor :
    (uliftFunctor.{u, v, w, w'} 𝕜 X).FullyFaithful where
  preimage {V W} g :=
    { fiberMap x :=
        (ContinuousLinearEquiv.ulift : ULift.{w'} (W.Fiber x) ≃L[𝕜] W.Fiber x).toLinearMap.comp
          ((g.fiberMap x).comp
            (ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).symm.toLinearMap)
      continuous_totalSpaceMap :=
        (W.uliftTotalSpaceHomeomorph.continuous.comp
          (g.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.symm.continuous)).congr
          fun p ↦ by
            dsimp only [Function.comp_apply]
            rw [uliftTotalSpaceHomeomorph_symm_apply, Hom.totalSpaceMap_mk,
              uliftTotalSpaceHomeomorph_apply]; rfl }
  map_preimage _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  preimage_map _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Full :=
  (fullyFaithfulUliftFunctor.{u, v, w, w'} 𝕜 X).full

instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Faithful :=
  (fullyFaithfulUliftFunctor.{u, v, w, w'} 𝕜 X).faithful

variable (𝕜 X) in
/-- `uliftFunctor` commutes with `toAtlasFunctor` up to canonical natural isomorphism. -/
noncomputable def uliftToAtlasNatIso :
    uliftFunctor.{u, v, w, w'} 𝕜 X ⋙ toAtlasFunctor.{u, v, max w w'} 𝕜 X ≅
      toAtlasFunctor.{u, v, w} 𝕜 X :=
  NatIso.ofComponents
    (fun V ↦
      let V' := (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V
      FiniteRankAtlas.isoMk
        (fun x ↦ ((V'.toAtlasFiberEquiv x).symm.trans
          ((ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).trans
            (V.toAtlasFiberEquiv x))).toLinearEquiv)
        ((V.toAtlasTotalSpaceHomeomorph.continuous.comp (V.uliftTotalSpaceHomeomorph.continuous.comp
            V'.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr fun q ↦ by
          dsimp only [Function.comp_apply]
          rw [toAtlasTotalSpaceHomeomorph_symm_apply, uliftTotalSpaceHomeomorph_apply,
            toAtlasTotalSpaceHomeomorph_apply]; rfl)
        ((V'.toAtlasTotalSpaceHomeomorph.continuous.comp
            (V.uliftTotalSpaceHomeomorph.symm.continuous.comp
              V.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr fun q ↦ by
          dsimp only [Function.comp_apply]
          rw [toAtlasTotalSpaceHomeomorph_symm_apply, uliftTotalSpaceHomeomorph_symm_apply,
            toAtlasTotalSpaceHomeomorph_apply]; rfl))
    fun {_ _} _ ↦ FiniteRankAtlas.hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
      simp only [Functor.comp_obj, Functor.comp_map, FiniteRankAtlas.fiberMap_comp,
        FiniteRankAtlas.fiberMap_isoMk_hom, LinearMap.comp_apply, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.symm_apply_apply, fiberMap_uliftFunctor_map]
      rfl

instance [UnivLE.{v, w}] : (uliftFunctor.{u, v, w, w'} 𝕜 X).IsEquivalence := by
  have : UnivLE.{v, max w w'} := @UnivLE.trans.{v, w, max w w'} ‹_› inferInstance
  have : (uliftFunctor.{u, v, w, w'} 𝕜 X ⋙ toAtlasFunctor.{u, v, max w w'} 𝕜 X).IsEquivalence :=
    Functor.isEquivalence_of_iso (uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).symm
  exact Functor.isEquivalence_of_comp_right
    (uliftFunctor.{u, v, w, w'} 𝕜 X) (toAtlasFunctor.{u, v, max w w'} 𝕜 X)

variable (𝕜 X) in
/-- Equivalence between variable-rank vector bundle categories in any two fibre universes `w, w'`
at least as large as the scalar field universe `v`. -/
noncomputable def changeUniverseEquivalence [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ≌ FiniteRankVectorBundle.{u, v, w'} 𝕜 X :=
  (atlasEquivalence.{u, v, w} 𝕜 X).trans (atlasEquivalence.{u, v, w'} 𝕜 X).symm

end FiniteRankVectorBundle

end ULift

end TauCeti
