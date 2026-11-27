/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Atlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Basic

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

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- `uliftFunctor` commutes with `toAtlasFunctor` up to canonical natural isomorphism,
given by the identity on every coordinate fibre. -/
noncomputable def uliftToAtlasNatIso :
    uliftFunctor.{w, w'} 𝕜 X ⋙ toAtlasFunctor.{max w w'} 𝕜 X ≅
      toAtlasFunctor.{w} 𝕜 X :=
  NatIso.ofComponents (fun V ↦
    let V' : FiniteRankBundle.{max w w'} 𝕜 X := V.ulift
    FiniteRankAtlas.isoMk (fun x ↦ LinearEquiv.refl 𝕜 (V.toAtlas.Fiber x))
      ((V.toAtlasHomeomorph.continuous.comp
        (V.uliftTotalSpaceHomeomorph.continuous.comp
          V'.toAtlasHomeomorph.symm.continuous)).congr fun p ↦ by
        simp only [V', Function.comp_apply, toAtlasHomeomorph_symm_apply,
          uliftTotalSpaceHomeomorph_apply, toAtlasHomeomorph_apply]
        erw [fiberContinuousLinearEquiv_ulift.{w, w'} V p.proj,
          ContinuousLinearEquiv.symm_trans_apply,
          ContinuousLinearEquiv.ulift_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
        exact congrArg (TotalSpace.mk p.proj) (LinearEquiv.refl_apply (R := 𝕜) p.snd).symm)
      ((V'.toAtlasHomeomorph.continuous.comp
        (V.uliftTotalSpaceHomeomorph.symm.continuous.comp
          V.toAtlasHomeomorph.symm.continuous)).congr fun p ↦ by
        simp only [V', Function.comp_apply, toAtlasHomeomorph_symm_apply,
          uliftTotalSpaceHomeomorph_symm_apply, toAtlasHomeomorph_apply]
        erw [fiberContinuousLinearEquiv_ulift.{w, w'} V p.proj,
          ContinuousLinearEquiv.trans_apply]
        exact congrArg (TotalSpace.mk p.proj)
          ((V.fiberContinuousLinearEquiv p.proj).apply_symm_apply _)))
    fun {V W} f ↦ FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp]
      dsimp only [LinearMap.comp_apply]
      erw [FiniteRankAtlas.fiberMap_isoMk_hom, FiniteRankAtlas.fiberMap_isoMk_hom]
      -- `change` reduces the `LinearEquiv.refl` identities on both sides and realigns
      -- `V.ulift.toAtlas.Fiber x` and `W.ulift.toAtlas.Fiber x` with `V.toAtlas.Fiber x` and
      -- `W.toAtlas.Fiber x` across the `rfl` lemmas `rank_ulift` and
      -- `FiniteRankAtlas.rank_ofBundles` (which `rw`/`simp` do not unify at `implicit`
      -- transparency).
      change (((toAtlasFunctor.{max w w'} 𝕜 X).map
            ((uliftFunctor.{w, w'} 𝕜 X).map f)).fiberMap x) u =
        (((toAtlasFunctor.{w} 𝕜 X).map f).fiberMap x) u
      erw [toAtlasFunctor_map, toAtlasFunctor_map, fiberMap_toAtlasMap_apply,
        fiberMap_toAtlasMap_apply, fiberMap_uliftFunctor_map_apply]
      erw [fiberContinuousLinearEquiv_ulift.{w, w'} V x,
        fiberContinuousLinearEquiv_ulift.{w, w'} W x]
      rfl

variable {𝕜 X}

/-- On every coordinate fibre, the forward component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_hom_app (V : FiniteRankBundle.{w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{w, w'} 𝕜 X).hom.app V).fiberMap x = LinearMap.id := by
  dsimp only [uliftToAtlasNatIso, NatIso.ofComponents_hom_app]
  erw [FiniteRankAtlas.fiberMap_isoMk_hom]
  rfl

/-- On every coordinate fibre, the inverse component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_inv_app (V : FiniteRankBundle.{w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{w, w'} 𝕜 X).inv.app V).fiberMap x = LinearMap.id := by
  dsimp only [uliftToAtlasNatIso, NatIso.ofComponents_inv_app]
  erw [FiniteRankAtlas.fiberMap_isoMk_inv]
  rfl

variable (𝕜 X) in
/-- `uliftFunctor 𝕜 X` is unconditionally fully faithful in all universes `w, w', u, v`. -/
noncomputable def fullyFaithfulUliftFunctor : (uliftFunctor.{w, w'} 𝕜 X).FullyFaithful :=
  ((fullyFaithfulToAtlasFunctor.{w} (𝕜 := 𝕜) (X := X)).ofIso
    (uliftToAtlasNatIso.{w, w'} 𝕜 X).symm).ofCompFaithful

instance : (uliftFunctor.{w, w'} 𝕜 X).Full := (fullyFaithfulUliftFunctor 𝕜 X).full

instance : (uliftFunctor.{w, w'} 𝕜 X).Faithful := (fullyFaithfulUliftFunctor 𝕜 X).faithful

end TauCeti.FiniteRankBundle
