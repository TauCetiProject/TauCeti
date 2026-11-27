/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Atlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Basic

import TauCeti.Topology.FiberBundle.TotalSpace

/-!
# Comparison of universe lifting with the forward atlas functor

`FiniteRankBundle.uliftFunctor 𝕜 X` commutes unconditionally with
`FiniteRankBundle.toAtlasFunctor 𝕜 X` up to the canonical natural isomorphism
`FiniteRankBundle.uliftToAtlasNatIso`, which is the identity on every coordinate fibre.
Combining this with full faithfulness of `toAtlasFunctor 𝕜 X` shows that `uliftFunctor 𝕜 X` is
unconditionally fully faithful (`FiniteRankBundle.fullyFaithfulUliftFunctor`). For the
conditional equivalence instance when `[UnivLE.{v, w}]` holds, see
`TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Equivalence`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankBundle

universe w w' u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

private noncomputable def uliftToAtlasIso (V : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{max w w'} 𝕜 X).obj V.ulift ≅ (toAtlasFunctor.{w} 𝕜 X).obj V :=
  FiniteRankAtlas.isoMk (fun x ↦ LinearEquiv.refl 𝕜 (V.toAtlas.Fiber x))
    (continuous_totalSpace_conj V.ulift.toAtlasHomeomorph.symm.continuous
      (V.toAtlasHomeomorph.continuous.comp V.uliftTotalSpaceHomeomorph.continuous)
      (f := fun q ↦ q.snd) (toAtlasHomeomorph_symm_apply V.ulift)
      (fun q ↦ by
        simp only [Function.comp_apply, uliftTotalSpaceHomeomorph_apply, toAtlasHomeomorph_apply]
        rfl)
      (fun p ↦ by
        -- `erw` bridges `V.ulift.toAtlas.Fiber x = V.toAtlas.Fiber x` and
        -- `V.ulift.Fiber x = ULift (V.Fiber x)` across the `rfl` lemmas `rank_ulift`,
        -- `FiniteRankAtlas.rank_ofBundles`, and `fiber_ulift`.
        erw [fiberContinuousLinearEquiv_ulift.{w, w'} V p.proj,
          ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.ulift_symm_apply,
          ContinuousLinearEquiv.apply_symm_apply]
        rfl)
      continuous_id)
    (continuous_totalSpace_conj V.toAtlasHomeomorph.symm.continuous
      (V.ulift.toAtlasHomeomorph.continuous.comp V.uliftTotalSpaceHomeomorph.symm.continuous)
      (f := fun q ↦ q.snd) (toAtlasHomeomorph_symm_apply V)
      (fun q ↦ by
        simp only [Function.comp_apply, uliftTotalSpaceHomeomorph_symm_apply,
          toAtlasHomeomorph_apply]
        rfl)
      (fun p ↦ by
        -- Same `rfl` wrapper alignment as in the forward continuity proof above.
        erw [fiberContinuousLinearEquiv_ulift.{w, w'} V p.proj]
        exact ((V.fiberContinuousLinearEquiv p.proj).apply_symm_apply _).symm)
      continuous_id)

@[simp] private theorem fiberMap_uliftToAtlasIso_hom (V : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (uliftToAtlasIso.{w, w'} V).hom.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [uliftToAtlasIso]
    erw [FiniteRankAtlas.fiberMap_isoMk_hom]
    rfl

@[simp] private theorem fiberMap_uliftToAtlasIso_inv (V : FiniteRankBundle.{w} 𝕜 X) (x : X) :
    (uliftToAtlasIso.{w, w'} V).inv.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [uliftToAtlasIso]
    erw [FiniteRankAtlas.fiberMap_isoMk_inv]
    rfl

private theorem fiberMap_toAtlas_uliftFunctor_map_apply {V W : FiniteRankBundle.{w} 𝕜 X}
    (f : V ⟶ W) (x : X) (u : V.toAtlas.Fiber x) :
    ((toAtlasFunctor.{max w w'} 𝕜 X).map ((uliftFunctor.{w, w'} 𝕜 X).map f)).fiberMap x u =
      ((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x u := by
  rw [toAtlasFunctor_map, toAtlasFunctor_map]
  -- `erw` bridges `V.ulift.toAtlas.Fiber x = V.toAtlas.Fiber x` and
  -- `V.ulift.Fiber x = ULift (V.Fiber x)` across `rank_ulift`, `FiniteRankAtlas.rank_ofBundles`,
  -- and `fiber_ulift`.
  erw [fiberMap_toAtlasMap_apply, fiberMap_toAtlasMap_apply, fiberMap_uliftFunctor_map_apply,
    fiberContinuousLinearEquiv_ulift.{w, w'} V x,
    fiberContinuousLinearEquiv_ulift.{w, w'} W x, ContinuousLinearEquiv.symm_trans_apply]
  rfl

variable (𝕜 X)

/-- `uliftFunctor` commutes with `toAtlasFunctor` up to canonical natural isomorphism,
given by the identity on every coordinate fibre. -/
noncomputable def uliftToAtlasNatIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅
      toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents uliftToAtlasIso fun {V W} f ↦
    FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp,
        LinearMap.comp_apply, LinearMap.comp_apply]
      -- `erw` bridges `V.ulift.toAtlas.Fiber x = V.toAtlas.Fiber x` across `rank_ulift` and
      -- `FiniteRankAtlas.rank_ofBundles`.
      erw [fiberMap_uliftToAtlasIso_hom W x, fiberMap_uliftToAtlasIso_hom V x,
        LinearMap.id_apply (R := 𝕜), LinearMap.id_apply (R := 𝕜)]
      exact fiberMap_toAtlas_uliftFunctor_map_apply f x u

variable {𝕜 X}

/-- On every coordinate fibre, the forward component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_hom_app (V : FiniteRankBundle.{w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{w, w'} 𝕜 X).hom.app V).fiberMap x = LinearMap.id :=
  fiberMap_uliftToAtlasIso_hom V x

/-- On every coordinate fibre, the inverse component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_inv_app (V : FiniteRankBundle.{w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{w, w'} 𝕜 X).inv.app V).fiberMap x = LinearMap.id :=
  fiberMap_uliftToAtlasIso_inv V x

variable (𝕜 X) in
/-- `uliftFunctor 𝕜 X` is unconditionally fully faithful in all universes `w, w', u, v`. -/
noncomputable def fullyFaithfulUliftFunctor : (uliftFunctor.{w, w'} 𝕜 X).FullyFaithful :=
  ((fullyFaithfulToAtlasFunctor.{w} (𝕜 := 𝕜) (X := X)).ofIso
    (uliftToAtlasNatIso.{w, w'} 𝕜 X).symm).ofCompFaithful

instance : (uliftFunctor.{w, w'} 𝕜 X).Full := (fullyFaithfulUliftFunctor 𝕜 X).full

instance : (uliftFunctor.{w, w'} 𝕜 X).Faithful := (fullyFaithfulUliftFunctor 𝕜 X).faithful

end TauCeti.FiniteRankBundle
