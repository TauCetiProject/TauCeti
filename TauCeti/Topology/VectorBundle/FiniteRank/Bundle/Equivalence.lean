/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homeomorph.Sigma
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
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
  up to `uliftToAtlasNatIso`, and becomes an equivalence under `[UnivLE.{v, w}]`; composing
  `atlasEquivalence` in two fibre universes gives `changeUniverseEquivalence` whenever
  `[UnivLE.{v, w}]` and `[UnivLE.{v, w'}]`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti
open VariableRankBundle
universe u v w w'
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankVectorBundle

/-- Encode a variable-rank vector bundle as a small coordinate atlas via point-indexed stratum
cores. -/
-- Expose the rank projection so `V.toAtlas.Fiber x` reduces to `Fin (V.rank x) → 𝕜`.
@[expose, implicit_reducible]
noncomputable def toAtlas (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 V.rank V.StratumFiber
@[simp] theorem rank_toAtlas (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    V.toAtlas.rank = V.rank := by rfl
/-- On the preferred stratum at `x`, `pointIndexedCoreFiberEquiv` is the inverse of
`V.preferredChartEquiv x`. -/
@[simp] theorem pointIndexedCoreFiberEquiv_stratumFiber (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
      ⟨x, rfl⟩ = (V.preferredChartEquiv x).symm :=
  DFunLike.ext _ _ fun w ↦
    (pointIndexedCoreFiberEquiv_apply 𝕜 _ _ _ w).trans (V.preferredChartEquiv_symm_apply x w).symm

/-- The canonical homeomorphism over `X` between the glued total space of `V` and the reconstructed
total space of `V.toAtlas`. -/
noncomputable def toAtlasTotalSpaceHomeomorph (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    TotalSpace Unit V.Fiber ≃ₜ TotalSpace Unit V.toAtlas.Fiber :=
  ((FiniteRankAtlas.reconstructionHomeomorph 𝕜 V.rank V.StratumFiber).trans
    (totalSpaceHomeomorph V)).symm
@[simp] theorem toAtlasTotalSpaceHomeomorph_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (p : TotalSpace Unit V.Fiber) :
    V.toAtlasTotalSpaceHomeomorph p = ⟨p.proj, V.preferredChartEquiv p.proj p.2⟩ := by
  rw [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_trans_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply,
    FiniteRankAtlas.reconstructionHomeomorph_symm_apply]
  exact (FiniteRankAtlas.totalSpaceHomeomorph_rfl_apply V.toAtlas p.proj _).trans
    (congrArg (TotalSpace.mk p.proj) (DFunLike.congr_fun ((congrArg ContinuousLinearEquiv.symm
      (pointIndexedCoreFiberEquiv_stratumFiber V p.proj)).trans
      (V.preferredChartEquiv p.proj).symm_symm) p.2))
@[simp] theorem toAtlasTotalSpaceHomeomorph_symm_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (q : TotalSpace Unit V.toAtlas.Fiber) :
    V.toAtlasTotalSpaceHomeomorph.symm q = ⟨q.proj, (V.preferredChartEquiv q.proj).symm q.2⟩ := by
  rw [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_symm, Homeomorph.trans_apply]
  exact (congrArg (VariableRankBundle.totalSpaceHomeomorph V)
    (FiniteRankAtlas.reconstructionHomeomorph_apply 𝕜 V.rank V.StratumFiber q)).trans
    ((FiniteRankVectorBundle.totalSpaceHomeomorph_apply V (V.rank q.proj) _).trans
      (congrArg (TotalSpace.mk q.proj)
        (DFunLike.congr_fun (pointIndexedCoreFiberEquiv_stratumFiber V q.proj) q.2)))

variable (𝕜 X) in
/-- Pass from variable-rank vector bundles with fibres in `Type w` to small coordinate atlases by
reading fibres and morphisms in preferred stratum charts. -/
-- Expose the object assignment so evaluated morphisms act on `V.toAtlas.Fiber`.
@[expose, implicit_reducible]
noncomputable def toAtlasFunctor : FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj V := V.toAtlas
  map {V W} f :=
    { fiberMap x := (W.preferredChartEquiv x).toLinearMap.comp
        ((f.fiberMap x).comp (V.preferredChartEquiv x).symm.toLinearMap)
      continuous_totalSpaceMap := (W.toAtlasTotalSpaceHomeomorph.continuous.comp
        (f.totalSpaceMap.continuous.comp V.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr
        fun _ ↦ by simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply] }
  map_id V := hom_ext fun x ↦ LinearMap.ext (V.preferredChartEquiv x).apply_symm_apply
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]
@[simp] theorem toAtlasFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (toAtlasFunctor.{u, v, w} 𝕜 X).obj V = V.toAtlas := by rfl
@[simp] theorem fiberMap_toAtlasFunctor_map {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (f : V ⟶ W) (x : X) (u : V.toAtlas.Fiber x) :
    ((toAtlasFunctor.{u, v, w} 𝕜 X).map f).fiberMap x u =
      W.preferredChartEquiv x (f.fiberMap x ((V.preferredChartEquiv x).symm u)) := by rfl
/-- On the fibre over `x`, `(toAtlasFunctor 𝕜 X).map f` conjugates `f.fiberMap x` by
`preferredChartEquiv`. -/
theorem coe_fiberMap_toAtlasFunctor_map {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (f : V ⟶ W) (x : X) : ⇑(((toAtlasFunctor.{u, v, w} 𝕜 X).map f).fiberMap x) =
      ⇑(W.preferredChartEquiv x) ∘ ⇑(f.fiberMap x) ∘ ⇑(V.preferredChartEquiv x).symm :=
  funext (fiberMap_toAtlasFunctor_map f x)
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]

private noncomputable def toAtlasPreimage {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (g : (toAtlasFunctor.{u, v, w} 𝕜 X).obj V ⟶ (toAtlasFunctor.{u, v, w} 𝕜 X).obj W) : V ⟶ W where
  fiberMap x := (W.preferredChartEquiv x).symm.toLinearMap.comp
    ((g.fiberMap x).comp (V.preferredChartEquiv x).toLinearMap)
  continuous_totalSpaceMap := (W.toAtlasTotalSpaceHomeomorph.symm.continuous.comp
    (g.totalSpaceMap.continuous.comp V.toAtlasTotalSpaceHomeomorph.continuous)).congr
    fun _ ↦ by simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]
@[simp] private theorem fiberMap_toAtlasPreimage_apply {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (g : (toAtlasFunctor.{u, v, w} 𝕜 X).obj V ⟶ (toAtlasFunctor.{u, v, w} 𝕜 X).obj W) (x : X)
    (v : V.Fiber x) : (toAtlasPreimage g).fiberMap x v =
      (W.preferredChartEquiv x).symm (g.fiberMap x (V.preferredChartEquiv x v)) := by rfl

variable (𝕜 X) in
/-- `toAtlasFunctor 𝕜 X` is unconditionally fully faithful in every fibre universe `w`. -/
noncomputable def fullyFaithfulToAtlasFunctor :
    (toAtlasFunctor.{u, v, w} 𝕜 X).FullyFaithful where
  preimage := toAtlasPreimage
  map_preimage _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]
  preimage_map _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Full := (fullyFaithfulToAtlasFunctor.{u, v, w} 𝕜 X).full
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Faithful :=
  (fullyFaithfulToAtlasFunctor.{u, v, w} 𝕜 X).faithful

/-- Over a complete scalar field `𝕜`, a morphism of variable-rank vector bundles is an isomorphism
if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective [CompleteSpace 𝕜] {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (f : V ⟶ W) : IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  have hIso : IsIso f ↔ IsIso ((toAtlasFunctor.{u, v, w} 𝕜 X).map f) :=
    ⟨fun _ ↦ (toAtlasFunctor.{u, v, w} 𝕜 X).map_isIso f,
      fun _ ↦ isIso_of_fully_faithful (toAtlasFunctor.{u, v, w} 𝕜 X) f⟩
  rw [hIso, FiniteRankAtlas.isIso_iff_bijective]
  refine forall_congr' fun x ↦ ?_
  rw [coe_fiberMap_toAtlasFunctor_map, (W.preferredChartEquiv x).bijective.of_comp_iff',
    (V.preferredChartEquiv x).symm.bijective.of_comp_iff]
instance : EssentiallySmall.{max u v} (FiniteRankVectorBundle.{u, v, w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{u, v, w} 𝕜 X)

end FiniteRankVectorBundle

/-- Continuous linear equivalence between the shrunk coordinate fibre over `y.1` and the native
`n`-stratum coordinate fibre over `y`. -/
noncomputable def FiniteRankAtlas.toBundleStratumEquiv (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}]
    (n : ℕ) (y : {x : X // A.rank x = n}) : Shrink.{w} (A.Fiber y.1) ≃L[𝕜] (A.charts n).Fiber y :=
  (Shrink.continuousLinearEquiv 𝕜 (A.Fiber y.1)).trans
    { (stratumFiberEquiv A y).symm with
      continuous_toFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.2.symm i)
      continuous_invFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.2 i) }
@[simp] theorem FiniteRankAtlas.toBundleStratumEquiv_rfl_apply (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] (x : X) (u : Shrink.{w} (A.Fiber x)) :
    A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩ u =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u := by rfl
@[simp] theorem FiniteRankAtlas.toBundleStratumEquiv_rfl_symm_apply (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] (x : X) (v : (A.charts (A.rank x)).Fiber ⟨x, rfl⟩) :
    (A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩).symm v =
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm v := by rfl

/-- Realize a small coordinate atlas `A : FiniteRankAtlas 𝕜 X` as a variable-rank vector bundle
with fibres in `Type w` whenever `UnivLE.{v, w}` holds. -/
-- Expose the rank and fibre projections so `(A.toBundle).Fiber` reduces to `Shrink (A.Fiber ·)`.
@[expose, implicit_reducible]
noncomputable def FiniteRankAtlas.toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X :=
  let φ := FiniteRankAtlas.toBundleStratumEquiv.{u, v, w} A
  let ts (n : ℕ) : TopologicalSpace
      (TotalSpace (Fin n → 𝕜) (fun y : {x : X // A.rank x = n} ↦ Shrink.{w} (A.Fiber y.1))) :=
    TopologicalSpace.induced
      (fun p ↦ (⟨p.proj, φ n p.proj p.2⟩ : TotalSpace (Fin n → 𝕜) (A.charts n).Fiber)) inferInstance
  { rank := A.rank, Fiber x := Shrink.{w} (A.Fiber x), topologicalSpaceStratumTotalSpace := ts
    fiberBundleStratum n := @fiberBundleOfHomeomorph _ (Fin n → 𝕜) (A.charts n).Fiber
      (fun y ↦ Shrink.{w} (A.Fiber y.1)) _ (ts n) _ _ _ _ _ (fun y ↦ (φ n y).toHomeomorph) ⟨rfl⟩
    vectorBundleStratum n := by
      let _ := ts n; exact vectorBundleOfContinuousLinearEquiv 𝕜 (φ n) ⟨rfl⟩ }
@[simp] theorem FiniteRankAtlas.rank_toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] :
    (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).rank = A.rank := by rfl
@[simp] theorem FiniteRankAtlas.fiber_toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] (x : X) :
    (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber x = Shrink.{w} (A.Fiber x) := by rfl

/-- The glued total space of `A.toBundle` is homeomorphic over `X` to `TotalSpace Unit A.Fiber` via
`Shrink.continuousLinearEquiv` on each fibre. -/
noncomputable def FiniteRankAtlas.toBundleTotalSpaceHomeomorph (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] : TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit A.Fiber :=
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  (VariableRankBundle.totalSpaceHomeomorph V).symm.trans ((Homeomorph.sigmaCongrRight fun n ↦
    totalSpaceHomeomorphOfIsInducing (Fin n → 𝕜) (E' := V.StratumFiber n)
      (fun y ↦ (FiniteRankAtlas.toBundleStratumEquiv.{u, v, w} A n y).toEquiv) ⟨rfl⟩).trans
    (VariableRankBundle.totalSpaceHomeomorph A))
@[simp] theorem FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}]
    (p : TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber) :
    A.toBundleTotalSpaceHomeomorph p =
      ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.2⟩ := by
  rw [toBundleTotalSpaceHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply, Homeomorph.sigmaCongrRight_apply,
    totalSpaceHomeomorphOfIsInducing_apply]
  exact (FiniteRankAtlas.totalSpaceHomeomorph_rfl_apply A p.proj _).trans
    (congrArg (TotalSpace.mk p.proj) (FiniteRankAtlas.toBundleStratumEquiv_rfl_apply A p.proj p.2))
@[simp] theorem FiniteRankAtlas.toBundleTotalSpaceHomeomorph_symm_apply (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] (q : TotalSpace Unit A.Fiber) :
    (A.toBundleTotalSpaceHomeomorph :
        TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber ≃ₜ _).symm q =
      ⟨q.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber q.proj)).symm q.2⟩ := by
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  rw [toBundleTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, FiniteRankAtlas.totalSpaceHomeomorph_symm_apply]
  exact (congrArg (VariableRankBundle.totalSpaceHomeomorph V)
    ((Homeomorph.sigmaCongrRight_symm_apply _ _).trans (congrArg (Sigma.mk (A.rank q.proj))
      (totalSpaceHomeomorphOfIsInducing_symm_apply _ _ _ _)))).trans
    ((FiniteRankVectorBundle.totalSpaceHomeomorph_apply V (A.rank q.proj) _).trans
      (congrArg (TotalSpace.mk q.proj)
        (FiniteRankAtlas.toBundleStratumEquiv_rfl_symm_apply A q.proj q.2)))

namespace FiniteRankVectorBundle

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundle ≅ A` in `FiniteRankAtlas 𝕜 X`. -/
noncomputable def toAtlasToBundleIso (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}] :
    (toAtlasFunctor.{u, v, w} 𝕜 X).obj A.toBundle ≅ A :=
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  isoMk (fun x ↦ (V.preferredChartEquiv x).symm.toLinearEquiv.trans
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearEquiv)
    ((A.toBundleTotalSpaceHomeomorph.continuous.comp
        V.toAtlasTotalSpaceHomeomorph.symm.continuous).congr fun _ ↦ by
      simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply,
        -Shrink.continuousLinearEquiv_apply])
    ((V.toAtlasTotalSpaceHomeomorph.continuous.comp
        A.toBundleTotalSpaceHomeomorph.symm.continuous).congr fun _ ↦ by
      simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply,
        -Shrink.continuousLinearEquiv_symm_apply])
instance [UnivLE.{v, w}] : (toAtlasFunctor.{u, v, w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundle, ⟨toAtlasToBundleIso A⟩⟩
instance [UnivLE.{v, w}] : (toAtlasFunctor.{u, v, w} 𝕜 X).IsEquivalence where

variable (𝕜 X) in
/-- When the fibre universe `w` is at least the scalar field universe `v`, variable-rank vector
bundles with fibres in `Type w` are categorically equivalent to small coordinate atlases. -/
noncomputable def atlasEquivalence [UnivLE.{v, w}] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X :=
  (toAtlasFunctor.{u, v, w} 𝕜 X).asEquivalence
@[simp] theorem atlasEquivalence_functor [UnivLE.{v, w}] :
    (atlasEquivalence.{u, v, w} 𝕜 X).functor = toAtlasFunctor.{u, v, w} 𝕜 X := by rfl

/-- Lift the fibres of a variable-rank vector bundle from `Type w` to `Type (max w w')`. -/
-- Expose the rank and fibre projections so `V.ulift.Fiber` reduces to `ULift (V.Fiber ·)`.
@[expose, implicit_reducible]
noncomputable def ulift (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X :=
  { rank := V.rank, Fiber x := ULift.{w'} (V.Fiber x) }
@[simp] theorem rank_ulift (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).rank = V.rank := by rfl
@[simp] theorem fiber_ulift (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x =
      ULift.{w'} (V.Fiber x) := by rfl

/-- Continuous linear equivalence between the lifted fibre `(V.ulift).Fiber x` and `V.Fiber x`. -/
noncomputable def uliftFiberEquiv (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x ≃L[𝕜] V.Fiber x :=
  ContinuousLinearEquiv.ulift
@[simp] theorem uliftFiberEquiv_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X)
    (v : (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x) :
    uliftFiberEquiv.{u, v, w, w'} V x v = v.down := by rfl
@[simp] theorem uliftFiberEquiv_symm_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (x : X)
    (v : V.Fiber x) : (uliftFiberEquiv.{u, v, w, w'} V x).symm v = ULift.up.{w'} v := by rfl

/-- The glued total space of `V.ulift` is homeomorphic over `X` to `TotalSpace Unit V.Fiber` via
`ULift.down` on fibres. -/
noncomputable def uliftTotalSpaceHomeomorph (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit V.Fiber :=
  (VariableRankBundle.totalSpaceHomeomorph
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X)).symm.trans
    ((Homeomorph.sigmaCongrRight fun n ↦
        TauCeti.uliftTotalSpaceHomeomorph (Fin n → 𝕜) (V.StratumFiber n)).trans
      (VariableRankBundle.totalSpaceHomeomorph V))
@[simp] theorem uliftTotalSpaceHomeomorph_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (p : TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber) :
    V.uliftTotalSpaceHomeomorph p = ⟨p.proj, p.2.down⟩ := by
  rw [uliftTotalSpaceHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply, Homeomorph.sigmaCongrRight_apply]
  exact (congrArg (VariableRankBundle.totalSpaceHomeomorph V) (congrArg (Sigma.mk (V.rank p.proj))
    (TauCeti.uliftTotalSpaceHomeomorph_apply (Fin (V.rank p.proj) → 𝕜)
      (V.StratumFiber (V.rank p.proj)) ⟨⟨p.proj, rfl⟩, p.2⟩))).trans
    (FiniteRankVectorBundle.totalSpaceHomeomorph_apply V (V.rank p.proj) _)
@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (p : TotalSpace Unit V.Fiber) :
    (V.uliftTotalSpaceHomeomorph :
        TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber ≃ₜ _).symm p =
      ⟨p.proj, ULift.up p.2⟩ := by
  let U : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X := V.ulift
  rw [uliftTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply]
  exact (congrArg (VariableRankBundle.totalSpaceHomeomorph U)
    ((Homeomorph.sigmaCongrRight_symm_apply _ _).trans (congrArg (Sigma.mk (V.rank p.proj))
      (TauCeti.uliftTotalSpaceHomeomorph_symm_apply (Fin (V.rank p.proj) → 𝕜)
        (V.StratumFiber (V.rank p.proj)) ⟨⟨p.proj, rfl⟩, p.2⟩)))).trans
    (FiniteRankVectorBundle.totalSpaceHomeomorph_apply U (V.rank p.proj) _)

variable (𝕜 X) in
/-- Lift variable-rank vector bundles and their morphisms from fibre universe `w` to `max w w'`. -/
-- Expose the object assignment so evaluated morphisms act on `ULift (V.Fiber ·)`.
@[expose, implicit_reducible]
noncomputable def uliftFunctor :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X where
  obj V := V.ulift
  map {V W} f :=
    { fiberMap x := (uliftFiberEquiv.{u, v, w, w'} W x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (uliftFiberEquiv.{u, v, w, w'} V x).toLinearMap)
      continuous_totalSpaceMap := (W.uliftTotalSpaceHomeomorph.symm.continuous.comp
        (f.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.continuous)).congr
        fun _ ↦ by simp }
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ ULift.ext (by simp)
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ ULift.ext (by simp)
@[simp] theorem uliftFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V =
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X) := by rfl
@[simp] theorem fiberMap_uliftFunctor_map {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (f : V ⟶ W) (x : X) (v : ((uliftFunctor.{u, v, w, w'} 𝕜 X).obj V).Fiber x) :
    ((uliftFunctor.{u, v, w, w'} 𝕜 X).map f).fiberMap x v = ULift.up (f.fiberMap x v.down) := by rfl
instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [fiberMap_add, LinearMap.add_apply, fiberMap_uliftFunctor_map]
    exact (ULift.ext ULift.add_down).symm

private noncomputable def uliftPreimage {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (g : (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V ⟶ (uliftFunctor.{u, v, w, w'} 𝕜 X).obj W) :
    V ⟶ W where
  fiberMap x := (uliftFiberEquiv.{u, v, w, w'} W x).toLinearMap.comp
    ((g.fiberMap x).comp (uliftFiberEquiv.{u, v, w, w'} V x).symm.toLinearMap)
  continuous_totalSpaceMap := (W.uliftTotalSpaceHomeomorph.continuous.comp
    (g.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.symm.continuous)).congr
    fun _ ↦ by simp
@[simp] private theorem fiberMap_uliftPreimage_apply {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
    (g : (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V ⟶ (uliftFunctor.{u, v, w, w'} 𝕜 X).obj W) (x : X)
    (v : V.Fiber x) : (uliftPreimage g).fiberMap x v = (g.fiberMap x (ULift.up v)).down := by rfl

variable (𝕜 X) in
/-- `uliftFunctor 𝕜 X` is unconditionally fully faithful in all universes `u, v, w, w'`. -/
noncomputable def fullyFaithfulUliftFunctor : (uliftFunctor.{u, v, w, w'} 𝕜 X).FullyFaithful where
  preimage := uliftPreimage
  map_preimage _ := hom_ext fun _ ↦ LinearMap.ext fun v ↦ ULift.ext (by simp [ULift.up_down v])
  preimage_map _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp
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
      let V' : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X := V.ulift
      isoMk (fun x ↦ ((V'.preferredChartEquiv x).symm.trans
          ((uliftFiberEquiv.{u, v, w, w'} V x).trans (V.preferredChartEquiv x))).toLinearEquiv)
        ((V.toAtlasTotalSpaceHomeomorph.continuous.comp (V.uliftTotalSpaceHomeomorph.continuous.comp
            V'.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr fun _ ↦ by
          simp +zetaDelta [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply])
        ((V'.toAtlasTotalSpaceHomeomorph.continuous.comp
            (V.uliftTotalSpaceHomeomorph.symm.continuous.comp
              V.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr fun _ ↦ by
          simp +zetaDelta [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]))
    fun {_ _} _ ↦ hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
      dsimp only [Functor.comp_obj, uliftFunctor]
      simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]
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
@[simp] theorem changeUniverseEquivalence_functor [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    (changeUniverseEquivalence.{u, v, w, w'} 𝕜 X).functor =
      toAtlasFunctor.{u, v, w} 𝕜 X ⋙ (atlasEquivalence.{u, v, w'} 𝕜 X).inverse := by rfl

end FiniteRankVectorBundle
end TauCeti
