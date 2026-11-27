/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.CoordinateHom
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Atlas

import TauCeti.Topology.FiberBundle.Pullback

/-!
# Isomorphism criteria for variable-rank vector bundles

A morphism in `TauCeti.FiniteRankBundle.{w} 𝕜 X` is a categorical isomorphism if and only if it is
bijective on every fibre (`FiniteRankBundle.isIso_iff_bijective`), deduced via `toAtlasFunctor` from
`FiniteRankAtlas.isIso_iff_bijective` with no completeness assumption on `𝕜`. Moreover, a
variable-rank bundle is isomorphic to `FiniteRankBundle.ofBundle 𝕜 n V` for some constant-rank
Mathlib vector bundle `V` over `X` if and only if its rank function is constantly `n`
(`FiniteRankBundle.exists_iso_ofBundle_iff`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankBundle

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]
  {E F : FiniteRankBundle.{w} 𝕜 X}

/-- A morphism of variable-rank vector bundles is an isomorphism if and only if it is bijective on
every fibre. -/
theorem isIso_iff_bijective (f : E ⟶ F) :
    IsIso f ↔ ∀ x : X, Function.Bijective (f.fiberMap x) := by
  have hIso : IsIso f ↔ IsIso ((toAtlasFunctor.{w} 𝕜 X).map f) :=
    ⟨fun _ ↦ (toAtlasFunctor.{w} 𝕜 X).map_isIso f,
      fun _ ↦ isIso_of_fully_faithful (toAtlasFunctor.{w} 𝕜 X) f⟩
  rw [hIso, FiniteRankAtlas.isIso_iff_bijective]
  refine forall_congr' fun x ↦ ?_
  -- `E.toAtlas.Fiber x` and `F.toAtlas.Fiber x` agree with `Fin (E.rank x) → 𝕜` and
  -- `Fin (F.rank x) → 𝕜` by the `rfl` lemma `FiniteRankAtlas.rank_ofBundles`.
  have hcomp :
      ⇑(((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x) =
        ⇑(F.fiberContinuousLinearEquiv x) ∘
          ⇑(f.fiberMap x) ∘
          ⇑(E.fiberContinuousLinearEquiv x).symm :=
    funext fun v ↦ fiberMap_toAtlasMap_apply E f x v
  rw [hcomp]
  have hL : Function.Bijective (F.fiberContinuousLinearEquiv x) :=
    ContinuousLinearEquiv.bijective _
  have hR : Function.Bijective (E.fiberContinuousLinearEquiv x).symm :=
    ContinuousLinearEquiv.bijective _
  exact (hL.of_comp_iff' _).trans (hR.of_comp_iff _)

private noncomputable def constStratumMap (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ)
    (hn : E.rank = LocallyConstant.const X n) : C(X, {x : X // E.rank x = n}) :=
  ⟨fun x ↦ ⟨x, congrFun (congrArg DFunLike.coe hn) x⟩, continuous_id.subtype_mk _⟩

private abbrev constStratumPullback (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ)
    (hn : E.rank = LocallyConstant.const X n) : X → Type w :=
  (constStratumMap E n hn : X → _) *ᵖ (E.StratumFiber n)

private instance instAddCommGroupConstStratumPullback (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ)
    (hn : E.rank = LocallyConstant.const X n) (x : X) :
    AddCommGroup (constStratumPullback E n hn x) :=
  E.addCommGroupFiber x

private instance instModuleConstStratumPullback (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ)
    (hn : E.rank = LocallyConstant.const X n) (x : X) :
    @Module 𝕜 (constStratumPullback E n hn x) _
      (instAddCommGroupConstStratumPullback E n hn x).toAddCommMonoid :=
  E.moduleFiber x

private noncomputable instance instFiberBundleConstStratumPullback (E : FiniteRankBundle.{w} 𝕜 X)
    (n : ℕ) (hn : E.rank = LocallyConstant.const X n) :
    FiberBundle (Fin n → 𝕜) (constStratumPullback E n hn) :=
  FiberBundle.pullback (constStratumMap E n hn)

private noncomputable instance instVectorBundleConstStratumPullback (E : FiniteRankBundle.{w} 𝕜 X)
    (n : ℕ) (hn : E.rank = LocallyConstant.const X n) :
    @VectorBundle 𝕜 X (Fin n → 𝕜) (constStratumPullback E n hn) _
      (fun x ↦ (instAddCommGroupConstStratumPullback E n hn x).toAddCommMonoid)
      (instModuleConstStratumPullback E n hn) _ _ _ _ _
      (instFiberBundleConstStratumPullback E n hn) :=
  VectorBundle.pullback 𝕜 (constStratumMap E n hn)

private noncomputable def ofBundleConstWitness (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ)
    (hn : E.rank = LocallyConstant.const X n) :
    Σ' (V : X → Type w) (i1 : ∀ x, AddCommGroup (V x)) (i2 : ∀ x, Module 𝕜 (V x))
        (i3 : ∀ x, TopologicalSpace (V x)) (i4 : TopologicalSpace (TotalSpace (Fin n → 𝕜) V))
        (i5 : FiberBundle (Fin n → 𝕜) V) (i6 : VectorBundle 𝕜 (Fin n → 𝕜) V),
      @ofBundle 𝕜 _ X _ n V i1 i2 i3 i4 i5 i6 ≅ E := by
  let B := ofBundle 𝕜 n (constStratumPullback E n hn)
  let hB : TotalSpace Unit B.Fiber ≃ₜ
      TotalSpace (Fin n → 𝕜) (constStratumPullback E n hn) :=
    ofBundleHomeomorph 𝕜 n (constStratumPullback E n hn)
  have hfwd : Continuous fun p : TotalSpace Unit B.Fiber ↦
      (⟨p.proj, p.snd⟩ : TotalSpace Unit E.Fiber) := by
    refine ((E.isOpenEmbedding_stratum n).continuous.comp
      ((Pullback.continuous_lift (Fin n → 𝕜) (E.StratumFiber n) (constStratumMap E n hn)).comp
        hB.continuous)).congr fun p ↦ ?_
    rw [Function.comp_apply, Function.comp_apply, ofBundleHomeomorph_apply,
      totalSpaceHomeomorph_apply]
    -- `Pullback.lift` and `(E.isOpenEmbedding_stratum n)` preserve the underlying fibre point
    -- `p.snd : (ofBundle ...).Fiber p.proj = E.Fiber p.proj` definitionally.
    rfl
  have hbwd : Continuous fun p : TotalSpace Unit E.Fiber ↦
      (⟨p.proj, p.snd⟩ : TotalSpace Unit B.Fiber) := by
    have hstr : Continuous fun p : TotalSpace Unit E.Fiber ↦
        (⟨constStratumMap E n hn p.proj, p.snd⟩ :
          TotalSpace (Fin n → 𝕜) (E.StratumFiber n)) :=
      ((E.continuous_mk_iff_rankStrata E.continuous_proj fun p ↦ p.snd).1 continuous_id n).comp
        (continuous_id.subtype_mk fun p ↦ (constStratumMap E n hn p.proj).property)
    have hpb : Continuous fun p : TotalSpace Unit E.Fiber ↦
        (⟨p.proj, p.snd⟩ : TotalSpace (Fin n → 𝕜) (constStratumPullback E n hn)) :=
      Bundle.Pullback.continuous_iff.2 ⟨E.continuous_proj, hstr⟩
    exact (hB.symm.continuous.comp hpb).congr fun p ↦ by
      rw [Function.comp_apply]
      exact ofBundleHomeomorph_symm_apply 𝕜 n (constStratumPullback E n hn) ⟨p.proj, p.snd⟩
  exact ⟨constStratumPullback E n hn, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    isoMk (fun x ↦ LinearEquiv.refl 𝕜 (E.Fiber x)) hfwd hbwd⟩

/-- A variable-rank vector bundle is isomorphic to `ofBundle 𝕜 n V` for some constant-rank
Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) V` over `X` if and only if its rank function is constantly
`n`. -/
theorem exists_iso_ofBundle_iff (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ) :
    (∃ (V : X → Type w) (_ : ∀ x, AddCommGroup (V x)) (_ : ∀ x, Module 𝕜 (V x))
        (_ : ∀ x, TopologicalSpace (V x)) (_ : TopologicalSpace (TotalSpace (Fin n → 𝕜) V))
        (_ : FiberBundle (Fin n → 𝕜) V) (_ : VectorBundle 𝕜 (Fin n → 𝕜) V),
      Nonempty (ofBundle 𝕜 n V ≅ E)) ↔ E.rank = LocallyConstant.const X n := by
  refine ⟨fun ⟨_, _, _, _, _, _, _, ⟨e⟩⟩ ↦ e.symm.finiteRankBundle_rank_eq, fun hn ↦ ?_⟩
  rcases ofBundleConstWitness E n hn with ⟨V, i1, i2, i3, i4, i5, i6, e⟩
  exact ⟨V, i1, i2, i3, i4, i5, i6, ⟨e⟩⟩

end TauCeti.FiniteRankBundle
