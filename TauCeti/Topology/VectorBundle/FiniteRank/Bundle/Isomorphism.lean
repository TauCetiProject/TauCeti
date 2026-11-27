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
  rw [toAtlasFunctor_map, fiberMap_toAtlasMap]
  change Function.Bijective
      (⇑(F.fiberContinuousLinearEquiv x) ∘
        ⇑(f.fiberMap x) ∘
        ⇑(E.fiberContinuousLinearEquiv x).symm) ↔ _
  have hL : Function.Bijective (F.fiberContinuousLinearEquiv x) :=
    ContinuousLinearEquiv.bijective _
  have hR : Function.Bijective (E.fiberContinuousLinearEquiv x).symm :=
    ContinuousLinearEquiv.bijective _
  exact (hL.of_comp_iff' _).trans (hR.of_comp_iff _)

private noncomputable def ofBundleConstWitness (E : FiniteRankBundle.{w} 𝕜 X) (n : ℕ)
    (hn : E.rank = LocallyConstant.const X n) :
    Σ' (V : X → Type w) (i1 : ∀ x, AddCommGroup (V x)) (i2 : ∀ x, Module 𝕜 (V x))
        (i3 : ∀ x, TopologicalSpace (V x)) (i4 : TopologicalSpace (TotalSpace (Fin n → 𝕜) V))
        (i5 : FiberBundle (Fin n → 𝕜) V) (i6 : VectorBundle 𝕜 (Fin n → 𝕜) V),
      @ofBundle 𝕜 _ X _ n V i1 i2 i3 i4 i5 i6 ≅ E := by
  have hnx (x : X) : E.rank x = n := congrFun (congrArg DFunLike.coe hn) x
  let toStratum : C(X, {x : X // E.rank x = n}) :=
    ⟨fun x ↦ ⟨x, hnx x⟩, continuous_id.subtype_mk _⟩
  let hts : TopologicalSpace (TotalSpace (Fin n → 𝕜) ((toStratum : X → _) *ᵖ (E.StratumFiber n))) :=
    inferInstance
  let hfb : FiberBundle (Fin n → 𝕜) ((toStratum : X → _) *ᵖ (E.StratumFiber n)) :=
    FiberBundle.pullback toStratum
  let hvb : VectorBundle 𝕜 (Fin n → 𝕜) ((toStratum : X → _) *ᵖ (E.StratumFiber n)) :=
    VectorBundle.pullback 𝕜 toStratum
  letI : ∀ x, AddCommGroup (((toStratum : X → _) *ᵖ (E.StratumFiber n)) x) :=
    fun x ↦ E.addCommGroupFiber x
  let B := @ofBundle 𝕜 _ X _ n ((toStratum : X → _) *ᵖ (E.StratumFiber n))
    _ (fun x ↦ E.moduleFiber x) (fun x ↦ E.topologicalSpaceFiber x) hts hfb hvb
  let hB : TotalSpace Unit B.Fiber ≃ₜ
      TotalSpace (Fin n → 𝕜) ((toStratum : X → _) *ᵖ (E.StratumFiber n)) :=
    @ofBundleHomeomorph 𝕜 _ X _ n ((toStratum : X → _) *ᵖ (E.StratumFiber n))
      _ (fun x ↦ E.moduleFiber x) (fun x ↦ E.topologicalSpaceFiber x) hts hfb hvb
  have hfwd : Continuous fun p : TotalSpace Unit B.Fiber ↦
      (⟨p.proj, p.snd⟩ : TotalSpace Unit E.Fiber) := by
    refine ((E.isOpenEmbedding_stratum n).continuous.comp
      ((Pullback.continuous_lift (Fin n → 𝕜) (E.StratumFiber n) toStratum).comp
        hB.continuous)).congr fun p ↦ ?_
    rw [Function.comp_apply, Function.comp_apply,
      @ofBundleHomeomorph_apply 𝕜 _ X _ n ((toStratum : X → _) *ᵖ (E.StratumFiber n))
        _ (fun x ↦ E.moduleFiber x) (fun x ↦ E.topologicalSpaceFiber x) hts hfb hvb p,
      totalSpaceHomeomorph_apply]
    rfl
  have hbwd : Continuous fun p : TotalSpace Unit E.Fiber ↦
      (⟨p.proj, p.snd⟩ : TotalSpace Unit B.Fiber) := by
    have hstr : Continuous fun p : TotalSpace Unit E.Fiber ↦
        (⟨⟨p.proj, hnx p.proj⟩, p.snd⟩ : TotalSpace (Fin n → 𝕜) (E.StratumFiber n)) :=
      ((E.continuous_mk_iff_rankStrata E.continuous_proj fun p ↦ p.snd).1 continuous_id n).comp
        (continuous_id.subtype_mk fun p ↦ hnx p.proj)
    have hpb : Continuous fun p : TotalSpace Unit E.Fiber ↦
        (⟨p.proj, p.snd⟩ : TotalSpace (Fin n → 𝕜) ((toStratum : X → _) *ᵖ (E.StratumFiber n))) :=
      Bundle.Pullback.continuous_iff.2 ⟨E.continuous_proj, hstr⟩
    exact (hB.symm.continuous.comp hpb).congr fun p ↦ by
      change hB.symm ⟨p.proj, p.snd⟩ = ⟨p.proj, p.snd⟩
      exact @ofBundleHomeomorph_symm_apply 𝕜 _ X _ n ((toStratum : X → _) *ᵖ (E.StratumFiber n))
        _ (fun x ↦ E.moduleFiber x) (fun x ↦ E.topologicalSpaceFiber x) hts hfb hvb ⟨p.proj, p.snd⟩
  exact ⟨(toStratum : X → _) *ᵖ (E.StratumFiber n), _, fun x ↦ E.moduleFiber x,
    fun x ↦ E.topologicalSpaceFiber x, hts, hfb, hvb,
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
