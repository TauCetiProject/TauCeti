/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic

/-!
# Forward atlas functor for variable-rank vector bundles

Every `V : FiniteRankVectorBundle.{u, v, w} 𝕜 X` yields a small coordinate atlas
`V.toAtlas : FiniteRankAtlas 𝕜 X` via point-indexed stratum cores, defining an unconditionally
additive and fully faithful functor `toAtlasFunctor 𝕜 X` with no completeness assumption on `𝕜`
and no compactness, finite-cover, or separation hypotheses on `X`. Consequently,
`FiniteRankVectorBundle.{u, v, w} 𝕜 X` is `EssentiallySmall.{max u v}` in every universe `w`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section
open Bundle CategoryTheory Topology
namespace TauCeti
open VariableRankBundle
universe u v w
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankVectorBundle
section ToAtlas
variable (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
/-- Encode a variable-rank vector bundle as a small coordinate atlas via point-indexed stratum
cores. -/
-- Expose the rank projection so `V.toAtlas.Fiber x` reduces to `Fin (V.rank x) → 𝕜`.
@[expose, implicit_reducible] noncomputable def toAtlas : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 V.rank V.StratumFiber
@[simp] theorem rank_toAtlas : V.toAtlas.rank = V.rank := by rfl
/-- On the preferred stratum at `x`, `pointIndexedCoreFiberEquiv` is the inverse of
`V.preferredChartEquiv x`. -/
@[simp] theorem pointIndexedCoreFiberEquiv_stratumFiber (x : X) :
    pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
      ⟨x, rfl⟩ = (V.preferredChartEquiv x).symm :=
  DFunLike.ext _ _ fun w ↦
    (pointIndexedCoreFiberEquiv_apply 𝕜 _ _ _ w).trans (V.preferredChartEquiv_symm_apply x w).symm

/-- The canonical homeomorphism over `X` between the glued total space of `V` and the reconstructed
total space of `V.toAtlas`. -/
noncomputable def toAtlasTotalSpaceHomeomorph :
    TotalSpace Unit V.Fiber ≃ₜ TotalSpace Unit V.toAtlas.Fiber :=
  ((FiniteRankAtlas.reconstructionHomeomorph 𝕜 V.rank V.StratumFiber).trans
    (totalSpaceHomeomorph V)).symm
@[simp] theorem toAtlasTotalSpaceHomeomorph_apply (p : TotalSpace Unit V.Fiber) :
    V.toAtlasTotalSpaceHomeomorph p = ⟨p.proj, V.preferredChartEquiv p.proj p.snd⟩ := by
  simp only [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_trans_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply,
    FiniteRankAtlas.reconstructionHomeomorph_symm_apply, pointIndexedCoreFiberEquiv_stratumFiber]
  exact FiniteRankAtlas.totalSpaceHomeomorph_rfl_apply V.toAtlas p.proj _
@[simp] theorem toAtlasTotalSpaceHomeomorph_symm_apply (q : TotalSpace Unit V.toAtlas.Fiber) :
    V.toAtlasTotalSpaceHomeomorph.symm q = ⟨q.proj, (V.preferredChartEquiv q.proj).symm q.snd⟩ := by
  simp only [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_symm, Homeomorph.trans_apply,
    FiniteRankAtlas.reconstructionHomeomorph_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_apply, pointIndexedCoreFiberEquiv_stratumFiber]
  -- Unify `V.toAtlas.rank q.proj` with `V.rank q.proj` in the dependent fibre type.
  rfl
end ToAtlas

variable (𝕜 X) in
/-- Pass from variable-rank vector bundles with fibres in `Type w` to small coordinate atlases by
reading fibres and morphisms in preferred stratum charts. -/
-- Expose the object assignment so evaluated morphisms act on `V.toAtlas.Fiber`.
@[expose, implicit_reducible] noncomputable def toAtlasFunctor :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj V := V.toAtlas
  map {V W} f :=
    { fiberMap x := (W.preferredChartEquiv x).toLinearMap.comp
        ((f.fiberMap x).comp (V.preferredChartEquiv x).symm.toLinearMap)
      continuous_totalSpaceMap := (W.toAtlasTotalSpaceHomeomorph.continuous.comp
        (f.totalSpaceMap.continuous.comp V.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr
        fun _ ↦ by simp }
  map_id V := hom_ext fun x ↦ LinearMap.ext (V.preferredChartEquiv x).apply_symm_apply
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp
@[simp] theorem toAtlasFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (toAtlasFunctor.{u, v, w} 𝕜 X).obj V = V.toAtlas := by rfl
variable {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
@[simp] theorem fiberMap_toAtlasFunctor_map_apply (f : V ⟶ W) (x : X) (u : V.toAtlas.Fiber x) :
    ((toAtlasFunctor.{u, v, w} 𝕜 X).map f).fiberMap x u =
      W.preferredChartEquiv x (f.fiberMap x ((V.preferredChartEquiv x).symm u)) := by rfl
/-- On the fibre over `x`, `(toAtlasFunctor 𝕜 X).map f` conjugates `f.fiberMap x` by
`preferredChartEquiv`. -/
theorem coe_fiberMap_toAtlasFunctor_map (f : V ⟶ W) (x : X) :
    ⇑(((toAtlasFunctor.{u, v, w} 𝕜 X).map f).fiberMap x) =
      ⇑(W.preferredChartEquiv x) ∘ ⇑(f.fiberMap x) ∘ ⇑(V.preferredChartEquiv x).symm :=
  funext (fiberMap_toAtlasFunctor_map_apply f x)
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

private noncomputable def toAtlasPreimage
    (g : (toAtlasFunctor.{u, v, w} 𝕜 X).obj V ⟶ (toAtlasFunctor.{u, v, w} 𝕜 X).obj W) : V ⟶ W where
  fiberMap x := (W.preferredChartEquiv x).symm.toLinearMap.comp
    ((g.fiberMap x).comp (V.preferredChartEquiv x).toLinearMap)
  continuous_totalSpaceMap := (W.toAtlasTotalSpaceHomeomorph.symm.continuous.comp
    (g.totalSpaceMap.continuous.comp V.toAtlasTotalSpaceHomeomorph.continuous)).congr
    fun _ ↦ by simp
@[simp] private theorem fiberMap_toAtlasPreimage_apply
    (g : (toAtlasFunctor.{u, v, w} 𝕜 X).obj V ⟶ (toAtlasFunctor.{u, v, w} 𝕜 X).obj W) (x : X)
    (v : V.Fiber x) : (toAtlasPreimage g).fiberMap x v =
      (W.preferredChartEquiv x).symm (g.fiberMap x (V.preferredChartEquiv x v)) := by rfl

variable (𝕜 X) in
/-- `toAtlasFunctor 𝕜 X` is unconditionally fully faithful in every fibre universe `w`. -/
noncomputable def fullyFaithfulToAtlasFunctor : (toAtlasFunctor.{u, v, w} 𝕜 X).FullyFaithful where
  preimage := toAtlasPreimage
  map_preimage _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp
  preimage_map _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Full := (fullyFaithfulToAtlasFunctor.{u, v, w} 𝕜 X).full
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).Faithful := (fullyFaithfulToAtlasFunctor 𝕜 X).faithful

instance : EssentiallySmall.{max u v} (FiniteRankVectorBundle.{u, v, w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{u, v, w} 𝕜 X)
end FiniteRankVectorBundle
end TauCeti
