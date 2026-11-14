/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Equivalence between variable-rank vector bundles and small coordinate atlases

`TauCeti.FiniteRankVectorBundle.{w} 𝕜 X` lies in `Type (max u v (w + 1))`, whereas
`TauCeti.FiniteRankAtlas 𝕜 X` stores point-indexed coordinate transitions on the clopen rank strata
and lies in `Type (max u v)`. We show without compactness, bounded-rank, or completeness
hypotheses that `FiniteRankVectorBundle.toAtlasFunctor` is unconditionally additive, full, and
faithful, yielding `EssentiallySmall.{u} (FiniteRankVectorBundle.{w} 𝕜 X)` under `Small.{u} 𝕜` and
`isIso_iff_bijective` over a complete field. Reconstructing bundles via `FiniteRankAtlas.toBundle`
and `toBundleShrink.{w}` gives `atlasEquivalence`, `uliftToAtlasIso`,
`(uliftFunctor.{w, w'} 𝕜 X).IsEquivalence`, and `universeEquivalence.{w, w'}`.

## References

* M. F. Atiyah, *K-Theory*, W. A. Benjamin (1967), §1.1–1.2.
-/

public section

open Bundle CategoryTheory Set Topology

namespace TauCeti

universe w w' v u

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankVectorBundle

section ToAtlas

section Obj

variable (V : FiniteRankVectorBundle.{w} 𝕜 X)

/-- Small point-indexed coordinate atlas of a variable-rank vector bundle. -/
-- Expose the rank projection so coordinate fibres identify with `Fin (V.rank x) → 𝕜`.
@[expose, implicit_reducible]
noncomputable def toAtlas : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 V.rank V.StratumFiber

/-- Transporting fibres along continuous linear equivalences leaves the coordinate atlas literally
unchanged. -/
@[simp] theorem toAtlas_mapFibers {E₂ : X → Type w'}
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
    (e : ∀ x, V.Fiber x ≃L[𝕜] E₂ x) : (V.mapFibers e).toAtlas = V.toAtlas := by
  dsimp only [toAtlas, FiniteRankAtlas.ofBundles, rank_mapFibers]
  congr; funext n
  exact FiberwiseEquiv.pointIndexedCore_eq (𝕜 := 𝕜) (Fin n → 𝕜)
    (E₁ := V.StratumFiber n) (fun y => e y.1)

/-- Lifting the fibre universe via `ulift` leaves the coordinate atlas literally unchanged. -/
@[simp] theorem toAtlas_ulift : (ulift.{w, w'} V).toAtlas = V.toAtlas :=
  V.toAtlas_mapFibers fun x => (ContinuousLinearEquiv.ulift (R₁ := 𝕜) (M₁ := V.Fiber x)).symm

/-- Preferred-chart continuous linear equivalence between the coordinate fibre of `V.toAtlas` and
the actual fibre `V.Fiber x`. -/
noncomputable def atlasFiberEquiv (x : X) : V.toAtlas.Fiber x ≃L[𝕜] V.Fiber x :=
  pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x)) ⟨x, rfl⟩

/-- Homeomorphism over `X` between the reconstructed total space of `V.toAtlas` and the actual
glued total space of `V`. -/
noncomputable def atlasHomeomorph : TotalSpace Unit V.toAtlas.Fiber ≃ₜ TotalSpace Unit V.Fiber :=
  (FiniteRankAtlas.reconstructionHomeomorph 𝕜 V.rank V.StratumFiber).trans V.totalSpaceHomeomorph

@[simp] theorem atlasHomeomorph_apply (p : TotalSpace Unit V.toAtlas.Fiber) :
    V.atlasHomeomorph p = ⟨p.proj, V.atlasFiberEquiv p.proj p.2⟩ := by
  rw [atlasHomeomorph, Homeomorph.trans_apply, FiniteRankAtlas.reconstructionHomeomorph_apply,
    totalSpaceHomeomorph_apply]
  rfl

@[simp] theorem atlasHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    V.atlasHomeomorph.symm p = ⟨p.proj, (V.atlasFiberEquiv p.proj).symm p.2⟩ := by
  rw [atlasHomeomorph, Homeomorph.symm_trans_apply, totalSpaceHomeomorph_symm_apply,
    FiniteRankAtlas.reconstructionHomeomorph_symm_apply,
    FiniteRankAtlas.totalSpaceHomeomorph_apply]
  rfl

end Obj

variable (𝕜 X) in
/-- Fully faithful additive functor encoding a variable-rank vector bundle by its small
point-indexed coordinate atlas. -/
-- Expose the object assignment so composed functors see `V.toAtlas`.
@[expose, implicit_reducible]
noncomputable def toAtlasFunctor :
    FiniteRankVectorBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj V := V.toAtlas
  map {V W} f :=
    { fiberMap x := (W.atlasFiberEquiv x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (V.atlasFiberEquiv x).toLinearMap)
      continuous_totalSpaceMap :=
        (W.atlasHomeomorph.symm.continuous.comp
          (f.totalSpaceMap.continuous.comp V.atlasHomeomorph.continuous)).congr
          fun _ => by simp }
  map_id V := FiniteRankAtlas.hom_ext fun x => LinearMap.ext (V.atlasFiberEquiv x).symm_apply_apply
  map_comp _ _ := FiniteRankAtlas.hom_ext fun _ => LinearMap.ext fun _ => by simp

@[simp] theorem toAtlasFunctor_obj (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).obj V = V.toAtlas := (rfl)

@[simp] theorem fiberMap_toAtlasFunctor_map {V W : FiniteRankVectorBundle.{w} 𝕜 X}
    (f : V ⟶ W) (x : X) :
    ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x =
      (W.atlasFiberEquiv x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (V.atlasFiberEquiv x).toLinearMap) := (rfl)

instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add := FiniteRankAtlas.hom_ext fun _ => LinearMap.ext fun _ => by simp

instance : (toAtlasFunctor.{w} 𝕜 X).Faithful where
  map_injective {V W _ _} h := hom_ext fun x => LinearMap.ext fun v => by
    simpa using congrArg
      (fun φ : (toAtlasFunctor.{w} 𝕜 X).obj V ⟶ (toAtlasFunctor.{w} 𝕜 X).obj W =>
        W.atlasFiberEquiv x (φ.fiberMap x ((V.atlasFiberEquiv x).symm v))) h

instance : (toAtlasFunctor.{w} 𝕜 X).Full where
  map_surjective {V W} φ :=
    let ψ : V.toAtlas ⟶ W.toAtlas := φ
    ⟨{ fiberMap x := (W.atlasFiberEquiv x).toLinearMap.comp
         ((ψ.fiberMap x).comp (V.atlasFiberEquiv x).symm.toLinearMap)
       continuous_totalSpaceMap := (W.atlasHomeomorph.continuous.comp
         (ψ.totalSpaceMap.continuous.comp V.atlasHomeomorph.symm.continuous)).congr
         fun _ => by simp },
      FiniteRankAtlas.hom_ext fun _ => LinearMap.ext fun _ => by simp; rfl⟩

/-- Over a complete scalar field, a morphism of variable-rank vector bundles is a categorical
isomorphism if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective [CompleteSpace 𝕜] {V W : FiniteRankVectorBundle.{w} 𝕜 X}
    (f : V ⟶ W) : IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  refine ⟨fun _ x => ((fiberFunctor x).mapIso (asIso f)).toLinearEquiv.bijective, fun hbij => ?_⟩
  have : IsIso ((toAtlasFunctor.{w} 𝕜 X).map f) := (FiniteRankAtlas.isIso_iff_bijective _).2
    fun x => (W.atlasFiberEquiv x).symm.bijective.comp
      ((hbij x).comp (V.atlasFiberEquiv x).bijective)
  exact isIso_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X) f

instance : EssentiallySmall.{max u v} (FiniteRankVectorBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

instance [Small.{u} 𝕜] : EssentiallySmall.{u} (FiniteRankVectorBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

end ToAtlas

end FiniteRankVectorBundle

namespace FiniteRankAtlas

section ToBundle

variable (A : FiniteRankAtlas 𝕜 X)

/-- Reconstruct a genuine variable-rank vector bundle in `FiniteRankVectorBundle.{v} 𝕜 X` with
literal coordinate fibres `Fin (A.rank x) → 𝕜`. -/
-- Expose `rank` and `Fiber` projections so reconstructed fibres reduce to `A.Fiber`.
@[expose, implicit_reducible]
def toBundle : FiniteRankVectorBundle.{v} 𝕜 X where
  rank := A.rank
  Fiber := A.Fiber
  addCommGroupFiber _ := inferInstance
  moduleFiber _ := inferInstance
  topologicalSpaceFiber _ := inferInstance
  topologicalSpaceStratum n :=
    FiberwiseEquiv.totalSpaceTopology (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
      (fun y => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
        (finCongr y.2)).symm)
  fiberBundleStratum n :=
    FiberwiseEquiv.fiberBundle (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
      (fun y => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
        (finCongr y.2)).symm)
  vectorBundleStratum n :=
    FiberwiseEquiv.vectorBundle (𝕜 := 𝕜) (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
      (fun y => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
        (finCongr y.2)).symm)

@[simp] theorem rank_toBundle : A.toBundle.rank = A.rank := (rfl)

@[simp] theorem fiber_toBundle (x : X) : A.toBundle.Fiber x = A.Fiber x := (rfl)

/-- The glued total space of `A.toBundle` has the exact same topology as the reconstructed total
space of `A`, via the identity on every point and fibre. -/
def toBundleHomeomorph : TotalSpace Unit A.toBundle.Fiber ≃ₜ TotalSpace Unit A.Fiber where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (A.continuous_mk_iff_rankStrata A.toBundle.continuous_proj _).2 fun n =>
      ((FiberwiseEquiv.continuous_totalSpace_to (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
        (E₂ := A.toBundle.StratumFiber n) _).comp <|
        (A.toBundle.continuous_mk_iff_rankStrata A.toBundle.continuous_proj
          (fun p => p.2)).1 continuous_id n).congr fun ⟨⟨_, _⟩, hy⟩ => by cases hy; rfl
  continuous_invFun :=
    (A.toBundle.continuous_mk_iff_rankStrata A.continuous_proj _).2 fun n =>
      (FiberwiseEquiv.continuous_totalSpace_iff (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
        (E₂ := A.toBundle.StratumFiber n) _).2 <|
        ((A.continuous_mk_iff_rankStrata A.continuous_proj (fun p => p.2)).1
          continuous_id n).congr fun ⟨⟨_, _⟩, hy⟩ => by cases hy; rfl

@[simp] theorem toBundleHomeomorph_apply (p : TotalSpace Unit A.toBundle.Fiber) :
    A.toBundleHomeomorph p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem toBundleHomeomorph_symm_apply (p : TotalSpace Unit A.Fiber) :
    A.toBundleHomeomorph.symm p = ⟨p.proj, p.2⟩ := (rfl)

section Shrink

variable [Small.{w} 𝕜]

/-- Reconstruct a bundle in `FiniteRankVectorBundle.{w} 𝕜 X` for any `w` with `Small.{w} 𝕜`. -/
-- Expose `rank` and `Fiber` projections so shrunk fibres reduce to `Shrink (A.Fiber x)`.
@[expose, implicit_reducible] noncomputable def toBundleShrink :
    FiniteRankVectorBundle.{w} 𝕜 X :=
  A.toBundle.mapFibers fun x => (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).symm

/-- Homeomorphism between `TotalSpace Unit (A.toBundleShrink.{w}).Fiber` and
`TotalSpace Unit A.Fiber`. -/
noncomputable def toBundleShrinkHomeomorph :
    TotalSpace Unit (A.toBundleShrink.{w}).Fiber ≃ₜ TotalSpace Unit A.Fiber :=
  (A.toBundle.mapFibersHomeomorph fun x =>
    (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).symm).trans A.toBundleHomeomorph

@[simp] theorem toBundleShrinkHomeomorph_apply
    (p : TotalSpace Unit (A.toBundleShrink.{w}).Fiber) :
    A.toBundleShrinkHomeomorph.{w} p =
      ⟨p.proj, Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber p.proj) p.2⟩ := by
  rw [toBundleShrinkHomeomorph, Homeomorph.trans_apply,
    FiniteRankVectorBundle.mapFibersHomeomorph_apply, ContinuousLinearEquiv.symm_symm,
    toBundleHomeomorph_apply]

@[simp] theorem toBundleShrinkHomeomorph_symm_apply (p : TotalSpace Unit A.Fiber) :
    (A.toBundleShrinkHomeomorph.{w}).symm p =
      ⟨p.proj, (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber p.proj)).symm p.2⟩ := by
  rw [toBundleShrinkHomeomorph, Homeomorph.symm_trans_apply, toBundleHomeomorph_symm_apply]
  exact FiniteRankVectorBundle.mapFibersHomeomorph_symm_apply A.toBundle _ ⟨p.proj, p.2⟩

/-- Canonical atlas isomorphism `(A.toBundleShrink.{w}).toAtlas ≅ A`. -/
noncomputable def toAtlasToBundleShrinkIso : (A.toBundleShrink.{w}).toAtlas ≅ A :=
  isoMk
    (fun x => ((A.toBundleShrink.{w}).atlasFiberEquiv x).toLinearEquiv.trans
      (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).toLinearEquiv)
    (((A.toBundleShrinkHomeomorph.{w}).continuous.comp
      (A.toBundleShrink.{w}).atlasHomeomorph.continuous).congr fun _ => by
      simp only [Function.comp_apply, FiniteRankVectorBundle.atlasHomeomorph_apply,
        toBundleShrinkHomeomorph_apply, LinearEquiv.trans_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv])
    (((A.toBundleShrink.{w}).atlasHomeomorph.symm.continuous.comp
      (A.toBundleShrinkHomeomorph.{w}).symm.continuous).congr fun _ => by
      simp only [Function.comp_apply, toBundleShrinkHomeomorph_symm_apply,
        FiniteRankVectorBundle.atlasHomeomorph_symm_apply, LinearEquiv.symm_trans_apply]; rfl)

end Shrink

end ToBundle

end FiniteRankAtlas

namespace FiniteRankVectorBundle

instance [Small.{w} 𝕜] : (toAtlasFunctor.{w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundleShrink.{w}, ⟨A.toAtlasToBundleShrinkIso.{w}⟩⟩

instance [Small.{w} 𝕜] : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence where

variable (𝕜 X) in
/-- Categorical equivalence between variable-rank vector bundles in `Type w` and coordinate atlases
when `Small.{w} 𝕜`. -/
noncomputable def atlasEquivalence [Small.{w} 𝕜] :
    FiniteRankVectorBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X :=
  (toAtlasFunctor.{w} 𝕜 X).asEquivalence

private noncomputable def uliftToAtlasComponentIso (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (ulift.{w, w'} V).toAtlas ≅ V.toAtlas :=
  FiniteRankAtlas.isoMk
    (fun x => ((ulift.{w, w'} V).atlasFiberEquiv x).toLinearEquiv.trans
      ((ULift.moduleEquiv : ULift.{w'} (V.Fiber x) ≃ₗ[𝕜] V.Fiber x).trans
        (V.atlasFiberEquiv x).symm.toLinearEquiv))
    ((V.atlasHomeomorph.symm.continuous.comp <|
      (uliftHomeomorph.{w, w'} V).continuous.comp
        (ulift.{w, w'} V).atlasHomeomorph.continuous).congr fun _ => by
      simp only [Function.comp_apply, atlasHomeomorph_apply, uliftHomeomorph_apply,
        atlasHomeomorph_symm_apply, LinearEquiv.trans_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]; rfl)
    (((ulift.{w, w'} V).atlasHomeomorph.symm.continuous.comp <|
      (uliftHomeomorph.{w, w'} V).symm.continuous.comp
        V.atlasHomeomorph.continuous).congr fun _ => by
      simp only [Function.comp_apply, atlasHomeomorph_apply, uliftHomeomorph_symm_apply,
        atlasHomeomorph_symm_apply, LinearEquiv.symm_trans_apply]; rfl)

private theorem fiberMap_uliftToAtlasComponentIso_hom (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : (ulift.{w, w'} V).toAtlas.Fiber x) :
    (uliftToAtlasComponentIso.{w, w'} V).hom.fiberMap x v =
      (V.atlasFiberEquiv x).symm (((ulift.{w, w'} V).atlasFiberEquiv x v).down) := by
  rw [uliftToAtlasComponentIso, FiniteRankAtlas.fiberMap_isoMk_hom]; rfl

variable (𝕜 X) in
/-- Natural isomorphism identifying `uliftFunctor ⋙ toAtlasFunctor` with `toAtlasFunctor`. -/
noncomputable def uliftToAtlasIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅ toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (fun V => uliftToAtlasComponentIso.{w, w'} V) fun {V W} f => by
    refine FiniteRankAtlas.hom_ext fun x => LinearMap.ext fun v => ?_
    let z : V.Fiber x := ((ulift.{w, w'} V).atlasFiberEquiv x v).down
    have hL := fiberMap_uliftToAtlasComponentIso_hom.{w, w'} W x
      (((uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X).map f).fiberMap x v)
    have hR := congrArg (((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x)
      (fiberMap_uliftToAtlasComponentIso_hom.{w, w'} V x v)
    exact hL.trans <| (congrArg (W.atlasFiberEquiv x).symm <|
      (congrArg ULift.down (((ulift.{w, w'} W).atlasFiberEquiv x).apply_symm_apply
        (ULift.up (f.fiberMap x z)))).trans
        (congrArg (f.fiberMap x) ((V.atlasFiberEquiv x).apply_symm_apply z)).symm).trans hR.symm

theorem fiberMap_uliftToAtlasIso_hom_app (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : (ulift.{w, w'} V).toAtlas.Fiber x) :
    ((uliftToAtlasIso.{w, w'} 𝕜 X).hom.app V).fiberMap x v =
      (V.atlasFiberEquiv x).symm (((ulift.{w, w'} V).atlasFiberEquiv x v).down) :=
  fiberMap_uliftToAtlasComponentIso_hom.{w, w'} V x v

theorem fiberMap_uliftToAtlasIso_inv_app (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : V.toAtlas.Fiber x) :
    ((uliftToAtlasIso.{w, w'} 𝕜 X).inv.app V).fiberMap x v =
      ((ulift.{w, w'} V).atlasFiberEquiv x).symm (ULift.up (V.atlasFiberEquiv x v)) := by
  change ((uliftToAtlasComponentIso.{w, w'} V).inv.fiberMap x) v = _
  rw [uliftToAtlasComponentIso, FiniteRankAtlas.fiberMap_isoMk_inv]; rfl

instance [Small.{w} 𝕜] : (uliftFunctor.{w, w'} 𝕜 X).IsEquivalence :=
  let ⟨⟨_, ⟨e⟩⟩⟩ := ‹Small.{w} 𝕜›
  let _ : Small.{max w w'} 𝕜 := Small.mk' (e.trans (Equiv.ulift.{w'}).symm)
  let _ : (uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X).IsEquivalence :=
    Functor.isEquivalence_of_iso (uliftToAtlasIso.{w, w'} 𝕜 X).symm
  Functor.isEquivalence_of_comp_right (uliftFunctor.{w, w'} 𝕜 X) (toAtlasFunctor.{max w w'} 𝕜 X)

variable (𝕜 X) in
/-- Categorical equivalence between variable-rank vector bundles in any two fibre universes `w` and
`w'` admitting `Small` scalars. -/
noncomputable def universeEquivalence [Small.{w} 𝕜] [Small.{w'} 𝕜] :
    FiniteRankVectorBundle.{w} 𝕜 X ≌ FiniteRankVectorBundle.{w'} 𝕜 X :=
  (atlasEquivalence.{w} 𝕜 X).trans (atlasEquivalence.{w'} 𝕜 X).symm

end FiniteRankVectorBundle

end TauCeti
