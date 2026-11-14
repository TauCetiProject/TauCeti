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

`TauCeti.FiniteRankVectorBundle.{w} 𝕜 X` has arbitrary actual fibres in `Type w`, so its objects
lie in `Type (max u v (w + 1))`. By contrast, `TauCeti.FiniteRankAtlas 𝕜 X` stores only
point-indexed coordinate transition data (`TauCeti.pointIndexedCore`) on the clopen rank strata and
lies in `Type (max u v)` (with `EssentiallySmall.{u}` whenever `Small.{u} 𝕜`).

This file connects the two categories without any compactness, bounded-rank, nonemptiness, or
completeness assumptions on the base or scalar field:

* `FiniteRankVectorBundle.toAtlasFunctor` encodes every variable-rank bundle by its point-indexed
  coordinate atlas (`FiniteRankAtlas.ofBundles`), and is unconditionally additive, full, and
  faithful, using `atlasHomeomorph` to transport total-space continuity back and forth.
* Consequently `FiniteRankVectorBundle.{w} 𝕜 X` is `EssentiallySmall.{max u v}` for every fibre
  universe `w`, and `EssentiallySmall.{u}` whenever `Small.{u} 𝕜` (in particular for `𝕜 = ℝ` or `ℂ`
  over `X : Type u`). Over a complete scalar field, categorical isomorphisms are characterized
  purely by fibrewise bijectivity (`FiniteRankVectorBundle.isIso_iff_bijective`).
* `FiniteRankAtlas.toBundle` reconstructs a genuine `FiniteRankVectorBundle.{v} 𝕜 X` with literal
  coordinate fibres `Fin (A.rank x) → 𝕜`, and `FiniteRankAtlas.toBundleShrink.{w}` transports its
  fibres into any universe `w` satisfying `Small.{w} 𝕜` via `Shrink.continuousLinearEquiv`.
* `FiniteRankVectorBundle.atlasEquivalence` establishes the categorical equivalence
  `FiniteRankVectorBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X` whenever `Small.{w} 𝕜`.
* `FiniteRankVectorBundle.uliftToAtlasIso` identifies `uliftFunctor ⋙ toAtlasFunctor` with
  `toAtlasFunctor`, showing that `uliftFunctor.{w, w'}` is an equivalence whenever `Small.{w} 𝕜`,
  and `universeEquivalence.{w, w'}` equates any two fibre universes `w, w'` admitting `Small`
  scalars.

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

/-- Small point-indexed coordinate atlas of a variable-rank vector bundle. -/
-- Expose the rank projection so reconstructed coordinate fibres identify with `Fin (V.rank x) → 𝕜`.
@[expose, implicit_reducible]
noncomputable def toAtlas (V : FiniteRankVectorBundle.{w} 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 V.rank V.StratumFiber

/-- Transporting fibres along continuous linear equivalences leaves the coordinate atlas literally
unchanged. -/
@[simp] theorem toAtlas_mapFibers (V : FiniteRankVectorBundle.{w} 𝕜 X) {E₂ : X → Type w'}
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
    (e : ∀ x, V.Fiber x ≃L[𝕜] E₂ x) : (V.mapFibers e).toAtlas = V.toAtlas := by
  have hcharts : (fun n => pointIndexedCore 𝕜 (Fin n → 𝕜) ((V.mapFibers e).StratumFiber n)) =
      (fun n => pointIndexedCore 𝕜 (Fin n → 𝕜) (V.StratumFiber n)) :=
    funext fun n => FiberwiseEquiv.pointIndexedCore_eq (𝕜 := 𝕜) (Fin n → 𝕜)
      (E₁ := V.StratumFiber n) (fun y => e y.1)
  let c₁ : { c : ∀ n, VectorBundleCore 𝕜 {x : X // V.rank x = n} (Fin n → 𝕜)
      {x : X // V.rank x = n} // ∀ n x, (c n).indexAt x = x } :=
    ⟨fun n => pointIndexedCore 𝕜 (Fin n → 𝕜) ((V.mapFibers e).StratumFiber n),
      fun n => pointIndexedCore_indexAt 𝕜 (Fin n → 𝕜) ((V.mapFibers e).StratumFiber n)⟩
  let c₂ : { c : ∀ n, VectorBundleCore 𝕜 {x : X // V.rank x = n} (Fin n → 𝕜)
      {x : X // V.rank x = n} // ∀ n x, (c n).indexAt x = x } :=
    ⟨fun n => pointIndexedCore 𝕜 (Fin n → 𝕜) (V.StratumFiber n),
      fun n => pointIndexedCore_indexAt 𝕜 (Fin n → 𝕜) (V.StratumFiber n)⟩
  exact congrArg
    (fun c : { c : ∀ n, VectorBundleCore 𝕜 {x : X // V.rank x = n} (Fin n → 𝕜)
        {x : X // V.rank x = n} // ∀ n x, (c n).indexAt x = x } =>
      ({ rank := V.rank, charts := c.1, indexAt_eq := c.2 } : FiniteRankAtlas 𝕜 X))
    (Subtype.ext (a1 := c₁) (a2 := c₂) hcharts)

/-- Lifting the fibre universe via `ulift` leaves the coordinate atlas literally unchanged. -/
@[simp] theorem toAtlas_ulift (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (ulift.{w, w'} V).toAtlas = V.toAtlas :=
  V.toAtlas_mapFibers fun x => (ContinuousLinearEquiv.ulift (R₁ := 𝕜) (M₁ := V.Fiber x)).symm

/-- Preferred-chart continuous linear equivalence between the coordinate fibre of `V.toAtlas` and
the actual fibre `V.Fiber x`. -/
noncomputable def atlasFiberEquiv (V : FiniteRankVectorBundle.{w} 𝕜 X) (x : X) :
    V.toAtlas.Fiber x ≃L[𝕜] V.Fiber x :=
  pointIndexedCoreFiberEquiv 𝕜 (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x)) ⟨x, rfl⟩

/-- Homeomorphism over `X` between the reconstructed total space of `V.toAtlas` and the actual
glued total space of `V`. -/
noncomputable def atlasHomeomorph (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    TotalSpace Unit V.toAtlas.Fiber ≃ₜ TotalSpace Unit V.Fiber :=
  (FiniteRankAtlas.reconstructionHomeomorph 𝕜 V.rank V.StratumFiber).trans V.totalSpaceHomeomorph

@[simp] theorem atlasHomeomorph_apply (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (p : TotalSpace Unit V.toAtlas.Fiber) :
    V.atlasHomeomorph p = ⟨p.proj, V.atlasFiberEquiv p.proj p.2⟩ := by
  rw [atlasHomeomorph, Homeomorph.trans_apply, FiniteRankAtlas.reconstructionHomeomorph_apply,
    totalSpaceHomeomorph_apply]
  rfl

@[simp] theorem atlasHomeomorph_symm_apply (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (p : TotalSpace Unit V.Fiber) :
    V.atlasHomeomorph.symm p = ⟨p.proj, (V.atlasFiberEquiv p.proj).symm p.2⟩ := by
  rw [atlasHomeomorph, Homeomorph.symm_trans_apply, totalSpaceHomeomorph_symm_apply,
    FiniteRankAtlas.reconstructionHomeomorph_symm_apply, FiniteRankAtlas.totalSpaceHomeomorph_apply]
  rfl

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
          (f.totalSpaceMap.continuous.comp V.atlasHomeomorph.continuous)).congr fun p => by
          simp only [Function.comp_apply, atlasHomeomorph_apply, Hom.totalSpaceMap_mk,
            atlasHomeomorph_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
            ContinuousLinearEquiv.coe_toLinearEquiv] }
  map_id V := by
    apply FiniteRankAtlas.hom_ext
    intro x
    apply LinearMap.ext
    exact (V.atlasFiberEquiv x).symm_apply_apply
  map_comp {V W U} f g := by
    apply FiniteRankAtlas.hom_ext
    intro x
    apply LinearMap.ext
    intro v
    simp only [fiberMap_comp, FiniteRankAtlas.fiberMap_comp, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem toAtlasFunctor_obj (V : FiniteRankVectorBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).obj V = V.toAtlas := (rfl)

@[simp] theorem fiberMap_toAtlasFunctor_map {V W : FiniteRankVectorBundle.{w} 𝕜 X}
    (f : V ⟶ W) (x : X) :
    ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x =
      (W.atlasFiberEquiv x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (V.atlasFiberEquiv x).toLinearMap) := (rfl)

instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add {V W f g} := by
    apply FiniteRankAtlas.hom_ext
    intro x
    apply LinearMap.ext
    intro v
    exact map_add (W.atlasFiberEquiv x).symm
      (f.fiberMap x (V.atlasFiberEquiv x v)) (g.fiberMap x (V.atlasFiberEquiv x v))

instance : (toAtlasFunctor.{w} 𝕜 X).Faithful where
  map_injective {V W f g} h := by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    have hv := congrArg
      (fun φ : (toAtlasFunctor.{w} 𝕜 X).obj V ⟶ (toAtlasFunctor.{w} 𝕜 X).obj W =>
        W.atlasFiberEquiv x (φ.fiberMap x ((V.atlasFiberEquiv x).symm v))) h
    simpa only [fiberMap_toAtlasFunctor_map, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply] using hv

instance : (toAtlasFunctor.{w} 𝕜 X).Full where
  map_surjective {V W} φ := by
    let ψ : V.toAtlas ⟶ W.toAtlas := φ
    refine ⟨{
      fiberMap x := (W.atlasFiberEquiv x).toLinearMap.comp
        ((ψ.fiberMap x).comp (V.atlasFiberEquiv x).symm.toLinearMap)
      continuous_totalSpaceMap :=
        (W.atlasHomeomorph.continuous.comp
          (ψ.totalSpaceMap.continuous.comp V.atlasHomeomorph.symm.continuous)).congr fun p => by
          simp only [Function.comp_apply, atlasHomeomorph_symm_apply,
            FiniteRankAtlas.Hom.totalSpaceMap_mk, atlasHomeomorph_apply, LinearMap.comp_apply,
            LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] }, ?_⟩
    apply FiniteRankAtlas.hom_ext
    intro x
    apply LinearMap.ext
    intro v
    simp only [fiberMap_toAtlasFunctor_map, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.symm_apply_apply]
    rfl

/-- Over a complete scalar field, a morphism of variable-rank vector bundles is a categorical
isomorphism if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective [CompleteSpace 𝕜] {V W : FiniteRankVectorBundle.{w} 𝕜 X}
    (f : V ⟶ W) : IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  constructor
  · intro hf x
    refine ⟨Function.HasLeftInverse.injective ⟨(inv f).fiberMap x, fun v => ?_⟩,
      Function.HasRightInverse.surjective ⟨(inv f).fiberMap x, fun v => ?_⟩⟩
    · simpa only [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply] using
        congrArg (fun k : V ⟶ V => k.fiberMap x v) (IsIso.hom_inv_id f)
    · simpa only [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply] using
        congrArg (fun k : W ⟶ W => k.fiberMap x v) (IsIso.inv_hom_id f)
  · intro hbij
    have hiso : IsIso ((toAtlasFunctor.{w} 𝕜 X).map f) := by
      rw [FiniteRankAtlas.isIso_iff_bijective]
      intro x
      exact (W.atlasFiberEquiv x).symm.bijective.comp
        ((hbij x).comp (V.atlasFiberEquiv x).bijective)
    exact isIso_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X) f

instance : EssentiallySmall.{max u v} (FiniteRankVectorBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

instance [Small.{u} 𝕜] : EssentiallySmall.{u} (FiniteRankVectorBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X)

end ToAtlas

end FiniteRankVectorBundle

namespace FiniteRankAtlas

/-- Reconstruct a genuine variable-rank vector bundle in `FiniteRankVectorBundle.{v} 𝕜 X` with
literal coordinate fibres `Fin (A.rank x) → 𝕜`. -/
-- Expose `rank` and `Fiber` projections so reconstructed fibres reduce to `A.Fiber`.
@[expose, implicit_reducible]
def toBundle (A : FiniteRankAtlas 𝕜 X) : FiniteRankVectorBundle.{v} 𝕜 X where
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

@[simp] theorem rank_toBundle (A : FiniteRankAtlas 𝕜 X) : A.toBundle.rank = A.rank := (rfl)

@[simp] theorem fiber_toBundle (A : FiniteRankAtlas 𝕜 X) (x : X) :
    A.toBundle.Fiber x = A.Fiber x := (rfl)

/-- The glued total space of `A.toBundle` has the exact same topology as the reconstructed total
space of `A`, via the identity on every point and fibre. -/
def toBundleHomeomorph (A : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit A.toBundle.Fiber ≃ₜ TotalSpace Unit A.Fiber where
  toFun p := ⟨p.proj, p.2⟩
  invFun p := ⟨p.proj, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply (A.continuous_mk_iff_rankStrata A.toBundle.continuous_proj _).2
    intro n
    have hn := (A.toBundle.continuous_mk_iff_rankStrata A.toBundle.continuous_proj
      (fun p => p.2)).1 continuous_id n
    exact ((@Homeomorph.continuous _ _ (A.toBundle.topologicalSpaceStratum n) _
      (FiberwiseEquiv.totalSpaceHomeomorph (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
        (E₂ := A.toBundle.StratumFiber n)
        (fun y => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
          (finCongr y.2)).symm))).comp hn).congr fun y =>
      (FiberwiseEquiv.totalSpaceHomeomorph_apply (Fin n → 𝕜)
        (E₁ := (A.charts n).Fiber) (E₂ := A.toBundle.StratumFiber n)
        (fun z => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
          (finCongr z.2)).symm) ⟨⟨y.1.proj, y.2⟩, y.1.2⟩).trans <| by
        rcases y with ⟨⟨x, v⟩, rfl⟩
        rfl
  continuous_invFun := by
    apply (A.toBundle.continuous_mk_iff_rankStrata A.continuous_proj _).2
    intro n
    have hn := (A.continuous_mk_iff_rankStrata A.continuous_proj (fun p => p.2)).1 continuous_id n
    exact ((@Homeomorph.continuous _ _ _ (A.toBundle.topologicalSpaceStratum n)
      (@Homeomorph.symm _ _ (A.toBundle.topologicalSpaceStratum n) _
        (FiberwiseEquiv.totalSpaceHomeomorph (Fin n → 𝕜) (E₁ := (A.charts n).Fiber)
          (E₂ := A.toBundle.StratumFiber n)
          (fun y => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
            (finCongr y.2)).symm)))).comp hn).congr
      fun y => (FiberwiseEquiv.totalSpaceHomeomorph_symm_apply (Fin n → 𝕜)
        (E₁ := (A.charts n).Fiber) (E₂ := A.toBundle.StratumFiber n)
        (fun z => (ContinuousLinearEquiv.piCongrLeft (R := 𝕜) (fun _ : Fin n => 𝕜)
          (finCongr z.2)).symm)
        ⟨⟨y.1.proj, y.2⟩, fun i => y.1.2 (Fin.cast y.2.symm i)⟩).trans <| by
        rcases y with ⟨⟨x, v⟩, rfl⟩
        rfl

@[simp] theorem toBundleHomeomorph_apply (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit A.toBundle.Fiber) :
    A.toBundleHomeomorph p = ⟨p.proj, p.2⟩ := (rfl)

@[simp] theorem toBundleHomeomorph_symm_apply (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit A.Fiber) :
    A.toBundleHomeomorph.symm p = ⟨p.proj, p.2⟩ := (rfl)

/-- Reconstruct a variable-rank vector bundle in `FiniteRankVectorBundle.{w} 𝕜 X` for any fibre
universe `w` with `Small.{w} 𝕜`. -/
-- Expose `rank` and `Fiber` projections so shrunk fibres reduce to `Shrink (A.Fiber x)`.
@[expose, implicit_reducible] noncomputable def toBundleShrink [Small.{w} 𝕜]
    (A : FiniteRankAtlas 𝕜 X) : FiniteRankVectorBundle.{w} 𝕜 X :=
  A.toBundle.mapFibers fun x => (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).symm

/-- Homeomorphism between the total space of `A.toBundleShrink.{w}` and
`TotalSpace Unit A.Fiber`. -/
noncomputable def toBundleShrinkHomeomorph [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (A.toBundleShrink.{w}).Fiber ≃ₜ TotalSpace Unit A.Fiber :=
  (A.toBundle.mapFibersHomeomorph fun x =>
    (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).symm).trans A.toBundleHomeomorph

@[simp] theorem toBundleShrinkHomeomorph_apply [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (A.toBundleShrink.{w}).Fiber) :
    A.toBundleShrinkHomeomorph.{w} p =
      ⟨p.proj, Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber p.proj) p.2⟩ := by
  rw [toBundleShrinkHomeomorph, Homeomorph.trans_apply,
    FiniteRankVectorBundle.mapFibersHomeomorph_apply, ContinuousLinearEquiv.symm_symm,
    toBundleHomeomorph_apply]

@[simp] theorem toBundleShrinkHomeomorph_symm_apply [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit A.Fiber) :
    (A.toBundleShrinkHomeomorph.{w}).symm p =
      ⟨p.proj, (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber p.proj)).symm p.2⟩ := by
  rw [toBundleShrinkHomeomorph, Homeomorph.symm_trans_apply, toBundleHomeomorph_symm_apply]
  exact FiniteRankVectorBundle.mapFibersHomeomorph_symm_apply A.toBundle
    (fun x => (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).symm) ⟨p.proj, p.2⟩

/-- Canonical atlas isomorphism `(A.toBundleShrink.{w}).toAtlas ≅ A`. -/
noncomputable def toAtlasToBundleShrinkIso [Small.{w} 𝕜] (A : FiniteRankAtlas 𝕜 X) :
    (A.toBundleShrink.{w}).toAtlas ≅ A :=
  isoMk
    (fun x => ((A.toBundleShrink.{w}).atlasFiberEquiv x).toLinearEquiv.trans
      (Shrink.continuousLinearEquiv.{w} 𝕜 (A.Fiber x)).toLinearEquiv)
    (((A.toBundleShrinkHomeomorph.{w}).continuous.comp
      (A.toBundleShrink.{w}).atlasHomeomorph.continuous).congr fun p => by
      simp only [Function.comp_apply, FiniteRankVectorBundle.atlasHomeomorph_apply,
        toBundleShrinkHomeomorph_apply, LinearEquiv.trans_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv])
    (((A.toBundleShrink.{w}).atlasHomeomorph.symm.continuous.comp
      (A.toBundleShrinkHomeomorph.{w}).symm.continuous).congr fun p => by
      simp only [Function.comp_apply, toBundleShrinkHomeomorph_symm_apply,
        FiniteRankVectorBundle.atlasHomeomorph_symm_apply, LinearEquiv.symm_trans_apply]
      rfl)

end FiniteRankAtlas

namespace FiniteRankVectorBundle

instance [Small.{w} 𝕜] : (toAtlasFunctor.{w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundleShrink.{w}, ⟨A.toAtlasToBundleShrinkIso.{w}⟩⟩

instance [Small.{w} 𝕜] : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence where

variable (𝕜 X) in
/-- Categorical equivalence between variable-rank finite-rank vector bundles in `Type w` and small
point-indexed coordinate atlases, whenever `Small.{w} 𝕜`. -/
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
        (ulift.{w, w'} V).atlasHomeomorph.continuous).congr fun p => by
      simp only [Function.comp_apply, atlasHomeomorph_apply, uliftHomeomorph_apply,
        atlasHomeomorph_symm_apply, LinearEquiv.trans_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv]
      rfl)
    (((ulift.{w, w'} V).atlasHomeomorph.symm.continuous.comp <|
      (uliftHomeomorph.{w, w'} V).symm.continuous.comp
        V.atlasHomeomorph.continuous).congr fun p => by
      simp only [Function.comp_apply, atlasHomeomorph_apply, uliftHomeomorph_symm_apply,
        atlasHomeomorph_symm_apply, LinearEquiv.symm_trans_apply]
      rfl)

private theorem fiberMap_uliftToAtlasComponentIso_hom (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : (ulift.{w, w'} V).toAtlas.Fiber x) :
    (uliftToAtlasComponentIso.{w, w'} V).hom.fiberMap x v =
      (V.atlasFiberEquiv x).symm (((ulift.{w, w'} V).atlasFiberEquiv x v).down) := by
  rw [uliftToAtlasComponentIso, FiniteRankAtlas.fiberMap_isoMk_hom]
  rfl

variable (𝕜 X) in
/-- Natural isomorphism identifying `uliftFunctor ⋙ toAtlasFunctor` with `toAtlasFunctor`. -/
noncomputable def uliftToAtlasIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅ toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents
    (fun V => uliftToAtlasComponentIso.{w, w'} V)
    fun {V W} f => by
      apply FiniteRankAtlas.hom_ext
      intro x
      apply LinearMap.ext
      intro v
      let z : V.Fiber x := ((ulift.{w, w'} V).atlasFiberEquiv x v).down
      have hL := fiberMap_uliftToAtlasComponentIso_hom.{w, w'} W x
        (((uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X).map f).fiberMap x v)
      have hR := congrArg (((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x)
        (fiberMap_uliftToAtlasComponentIso_hom.{w, w'} V x v)
      exact hL.trans <|
        (congrArg (W.atlasFiberEquiv x).symm <|
          (congrArg ULift.down (((ulift.{w, w'} W).atlasFiberEquiv x).apply_symm_apply
            (ULift.up (f.fiberMap x z)))).trans
            (congrArg (f.fiberMap x) ((V.atlasFiberEquiv x).apply_symm_apply z)).symm).trans
          hR.symm

theorem fiberMap_uliftToAtlasIso_hom_app (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : (ulift.{w, w'} V).toAtlas.Fiber x) :
    ((uliftToAtlasIso.{w, w'} 𝕜 X).hom.app V).fiberMap x v =
      (V.atlasFiberEquiv x).symm (((ulift.{w, w'} V).atlasFiberEquiv x v).down) :=
  fiberMap_uliftToAtlasComponentIso_hom.{w, w'} V x v

private theorem fiberMap_uliftToAtlasComponentIso_inv (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : V.toAtlas.Fiber x) :
    (uliftToAtlasComponentIso.{w, w'} V).inv.fiberMap x v =
      ((ulift.{w, w'} V).atlasFiberEquiv x).symm (ULift.up (V.atlasFiberEquiv x v)) := by
  rw [uliftToAtlasComponentIso, FiniteRankAtlas.fiberMap_isoMk_inv]
  rfl

theorem fiberMap_uliftToAtlasIso_inv_app (V : FiniteRankVectorBundle.{w} 𝕜 X)
    (x : X) (v : V.toAtlas.Fiber x) :
    ((uliftToAtlasIso.{w, w'} 𝕜 X).inv.app V).fiberMap x v =
      ((ulift.{w, w'} V).atlasFiberEquiv x).symm (ULift.up (V.atlasFiberEquiv x v)) :=
  fiberMap_uliftToAtlasComponentIso_inv.{w, w'} V x v

instance [Small.{w} 𝕜] : (uliftFunctor.{w, w'} 𝕜 X).IsEquivalence :=
  let ⟨⟨_, ⟨e⟩⟩⟩ := ‹Small.{w} 𝕜›
  let _ : Small.{max w w'} 𝕜 := Small.mk' (e.trans (Equiv.ulift.{w'}).symm)
  let _ : (uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X).IsEquivalence :=
    Functor.isEquivalence_of_iso (uliftToAtlasIso.{w, w'} 𝕜 X).symm
  Functor.isEquivalence_of_comp_right (uliftFunctor.{w, w'} 𝕜 X)
    (toAtlasFunctor.{max w w'} 𝕜 X)

variable (𝕜 X) in
/-- Categorical equivalence between variable-rank vector bundles in any two fibre universes `w` and
`w'` admitting `Small` scalars. -/
noncomputable def universeEquivalence [Small.{w} 𝕜] [Small.{w'} 𝕜] :
    FiniteRankVectorBundle.{w} 𝕜 X ≌ FiniteRankVectorBundle.{w'} 𝕜 X :=
  (atlasEquivalence.{w} 𝕜 X).trans (atlasEquivalence.{w'} 𝕜 X).symm

end FiniteRankVectorBundle

end TauCeti
