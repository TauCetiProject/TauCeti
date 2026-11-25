/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic

/-!
# Forward atlas functor for variable-rank vector bundles

Every `E : FiniteRankBundle.{w} 𝕜 X` yields a small coordinate atlas
`E.toAtlas : FiniteRankAtlas 𝕜 X` via point-indexed stratum cores, defining an unconditionally
additive and fully faithful functor `FiniteRankBundle.toAtlasFunctor 𝕜 X` with no completeness
assumption on `𝕜` and no compactness, finite-cover, or separation hypotheses on `X`. Consequently,
`FiniteRankBundle.{w} 𝕜 X` is `EssentiallySmall.{max u v}` in every universe `w`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankBundle

section ToAtlas

variable (E : FiniteRankBundle.{w} 𝕜 X)

/-- Encode a variable-rank vector bundle as a small coordinate atlas via point-indexed stratum
cores. -/
-- Expose the rank projection so `E.toAtlas.Fiber x` reduces to `Fin (E.rank x) → 𝕜`.
@[expose, implicit_reducible] noncomputable def toAtlas : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 E.rank E.StratumFiber

@[simp] theorem rank_toAtlas : E.toAtlas.rank = E.rank := rfl

/-- The canonical homeomorphism over `X` between the glued total space of `E` and the reconstructed
total space of `E.toAtlas`. -/
noncomputable def toAtlasTotalSpaceHomeomorph :
    TotalSpace Unit E.Fiber ≃ₜ TotalSpace Unit E.toAtlas.Fiber :=
  ((FiniteRankAtlas.reconstructionHomeomorph 𝕜 E.rank E.StratumFiber).trans
    E.totalSpaceHomeomorph).symm

@[simp] theorem toAtlasTotalSpaceHomeomorph_apply (p : TotalSpace Unit E.Fiber) :
    E.toAtlasTotalSpaceHomeomorph p =
      ⟨p.proj, VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank p.proj) → 𝕜)
        (E.StratumFiber (E.rank p.proj)) ⟨p.proj, rfl⟩ p.snd⟩ := by
  simp only [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_trans_apply,
    FiniteRankBundle.totalSpaceHomeomorph_symm_apply,
    FiniteRankAtlas.reconstructionHomeomorph_symm_apply]
  refine (FiniteRankAtlas.totalSpaceHomeomorph_apply E.toAtlas _).trans
    (congrArg (TotalSpace.mk p.proj) ?_)
  exact ((pointIndexedCoreFiberEquiv_symm_apply 𝕜 (Fin (E.rank p.proj) → 𝕜)
      (E.StratumFiber (E.rank p.proj)) ⟨p.proj, rfl⟩ p.snd).trans
    (VectorBundle.continuousLinearEquivAt_apply 𝕜 (Fin (E.rank p.proj) → 𝕜)
      (E.StratumFiber (E.rank p.proj)) ⟨p.proj, rfl⟩ p.snd).symm)

@[simp] theorem toAtlasTotalSpaceHomeomorph_symm_apply (q : TotalSpace Unit E.toAtlas.Fiber) :
    E.toAtlasTotalSpaceHomeomorph.symm q =
      ⟨q.proj, (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank q.proj) → 𝕜)
        (E.StratumFiber (E.rank q.proj)) ⟨q.proj, rfl⟩).symm q.snd⟩ := by
  simp only [toAtlasTotalSpaceHomeomorph, Homeomorph.symm_symm, Homeomorph.trans_apply,
    FiniteRankAtlas.reconstructionHomeomorph_apply, FiniteRankBundle.totalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk q.proj)
    ((pointIndexedCoreFiberEquiv_apply 𝕜 (Fin (E.rank q.proj) → 𝕜)
        (E.StratumFiber (E.rank q.proj)) ⟨q.proj, rfl⟩ q.snd).trans
      (VectorBundle.continuousLinearEquivAt_symm_apply 𝕜 (Fin (E.rank q.proj) → 𝕜)
        (E.StratumFiber (E.rank q.proj)) ⟨q.proj, rfl⟩ q.snd).symm)

end ToAtlas

variable (𝕜 X) in
/-- Pass from variable-rank vector bundles with fibres in `Type w` to small coordinate atlases by
reading fibres and morphisms in preferred stratum charts. -/
-- Expose the object assignment so evaluated morphisms act on `E.toAtlas.Fiber`.
@[expose, implicit_reducible] noncomputable def toAtlasFunctor :
    FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj E := E.toAtlas
  map {E F} f :=
    { fiberMap x :=
        (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F.rank x) → 𝕜)
          (F.StratumFiber (F.rank x)) ⟨x, rfl⟩).toLinearMap.comp
        ((f.fiberMap x).comp
          (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
            (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).symm.toLinearMap)
      continuous_totalSpaceMap := (F.toAtlasTotalSpaceHomeomorph.continuous.comp
        (f.totalSpaceMap.continuous.comp E.toAtlasTotalSpaceHomeomorph.symm.continuous)).congr
        fun _ ↦ by
          simp only [Function.comp_apply, toAtlasTotalSpaceHomeomorph_symm_apply,
            FiniteRankBundle.Hom.totalSpaceMap_mk, toAtlasTotalSpaceHomeomorph_apply]
          rfl }
  map_id E := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext
    (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
      (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).apply_symm_apply
  map_comp {E F G} f g := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦
    congrArg (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (G.rank x) → 𝕜)
        (G.StratumFiber (G.rank x)) ⟨x, rfl⟩)
      (congrArg (g.fiberMap x)
        ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F.rank x) → 𝕜)
          (F.StratumFiber (F.rank x)) ⟨x, rfl⟩).symm_apply_apply _).symm)

@[simp] theorem toAtlasFunctor_obj (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).obj E = E.toAtlas := by rfl

variable {E F : FiniteRankBundle.{w} 𝕜 X}

@[simp] theorem fiberMap_toAtlasFunctor_map_apply (f : E ⟶ F) (x : X) (u : E.toAtlas.Fiber x) :
    ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x u =
      VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F.rank x) → 𝕜) (F.StratumFiber (F.rank x))
        ⟨x, rfl⟩ (f.fiberMap x ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
          (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).symm u)) := rfl

/-- On the fibre over `x`, `(toAtlasFunctor 𝕜 X).map f` conjugates `f.fiberMap x` by
`VectorBundle.continuousLinearEquivAt`. -/
theorem coe_fiberMap_toAtlasFunctor_map (f : E ⟶ F) (x : X) :
    ⇑(((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x) =
      ⇑(VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F.rank x) → 𝕜)
          (F.StratumFiber (F.rank x)) ⟨x, rfl⟩) ∘
        ⇑(f.fiberMap x) ∘
        ⇑(VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
          (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).symm :=
  funext (fiberMap_toAtlasFunctor_map_apply f x)

instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {_ _ _ _} := FiniteRankAtlas.hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [FiniteRankAtlas.fiberMap_add, FiniteRankBundle.fiberMap_add,
      LinearMap.add_apply, fiberMap_toAtlasFunctor_map_apply, map_add]
    rfl

private noncomputable def toAtlasPreimage
    (g : (toAtlasFunctor.{w} 𝕜 X).obj E ⟶ (toAtlasFunctor.{w} 𝕜 X).obj F) : E ⟶ F where
  fiberMap x :=
    (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F.rank x) → 𝕜)
      (F.StratumFiber (F.rank x)) ⟨x, rfl⟩).symm.toLinearMap.comp
    ((g.fiberMap x).comp
      (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
        (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).toLinearMap)
  continuous_totalSpaceMap := (F.toAtlasTotalSpaceHomeomorph.symm.continuous.comp
    (g.totalSpaceMap.continuous.comp E.toAtlasTotalSpaceHomeomorph.continuous)).congr
    fun p ↦ by
      simp only [Function.comp_apply, toAtlasTotalSpaceHomeomorph_apply]
      have hg : (g.totalSpaceMap ⟨p.proj, VectorBundle.continuousLinearEquivAt 𝕜
          (Fin (E.rank p.proj) → 𝕜) (E.StratumFiber (E.rank p.proj)) ⟨p.proj, rfl⟩ p.snd⟩) =
          ⟨p.proj, g.fiberMap p.proj (VectorBundle.continuousLinearEquivAt 𝕜
            (Fin (E.rank p.proj) → 𝕜) (E.StratumFiber (E.rank p.proj)) ⟨p.proj, rfl⟩ p.snd)⟩ :=
        FiniteRankAtlas.Hom.totalSpaceMap_mk g p.proj _
      rw [hg, toAtlasTotalSpaceHomeomorph_symm_apply]
      rfl

@[simp] private theorem fiberMap_toAtlasPreimage_apply
    (g : (toAtlasFunctor.{w} 𝕜 X).obj E ⟶ (toAtlasFunctor.{w} 𝕜 X).obj F) (x : X)
    (v : E.Fiber x) : (toAtlasPreimage g).fiberMap x v =
      (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F.rank x) → 𝕜) (F.StratumFiber (F.rank x))
        ⟨x, rfl⟩).symm (g.fiberMap x (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
          (E.StratumFiber (E.rank x)) ⟨x, rfl⟩ v)) := rfl

variable (𝕜 X) in
/-- `toAtlasFunctor 𝕜 X` is unconditionally fully faithful in every fibre universe `w`. -/
noncomputable def fullyFaithfulToAtlasFunctor : (toAtlasFunctor.{w} 𝕜 X).FullyFaithful where
  preimage := toAtlasPreimage
  map_preimage {E' F'} g := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    dsimp only [toAtlasFunctor] at g u ⊢
    exact ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F'.rank x) → 𝕜)
        (F'.StratumFiber (F'.rank x)) ⟨x, rfl⟩).apply_symm_apply _).trans
      (congrArg (g.fiberMap x) ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E'.rank x) → 𝕜)
        (E'.StratumFiber (E'.rank x)) ⟨x, rfl⟩).apply_symm_apply u))
  preimage_map {E' F'} f := hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    dsimp only [toAtlasFunctor]
    exact ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (F'.rank x) → 𝕜)
        (F'.StratumFiber (F'.rank x)) ⟨x, rfl⟩).symm_apply_apply _).trans
      (congrArg (f.fiberMap x) ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E'.rank x) → 𝕜)
        (E'.StratumFiber (E'.rank x)) ⟨x, rfl⟩).symm_apply_apply v))

instance : (toAtlasFunctor.{w} 𝕜 X).Full := (fullyFaithfulToAtlasFunctor.{w} 𝕜 X).full

instance : (toAtlasFunctor.{w} 𝕜 X).Faithful := (fullyFaithfulToAtlasFunctor 𝕜 X).faithful

instance : EssentiallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

end FiniteRankBundle

end TauCeti
