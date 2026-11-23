/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.OfAtlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ToAtlas

/-!
# Categorical equivalence with small coordinate atlases and universe independence

Under `[UnivLE.{v, w}]`, `FiniteRankAtlas.toBundle` (from `Bundle/OfAtlas.lean`) reconstructs a
`Type w`-fibred variable-rank vector bundle from a small coordinate atlas
`A : FiniteRankAtlas 𝕜 X`, and the forward functor `FiniteRankVectorBundle.toAtlasFunctor 𝕜 X`
from `Bundle/ToAtlas.lean` becomes an equivalence `FiniteRankVectorBundle.atlasEquivalence 𝕜 X`.
Composing `atlasEquivalence` in two fibre universes gives
`FiniteRankVectorBundle.changeUniverseEquivalence` whenever `[UnivLE.{v, w}]` and
`[UnivLE.{v, w'}]`.

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
section Equivalence
variable [UnivLE.{v, w}]
section
variable (A : FiniteRankAtlas 𝕜 X)

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundle ≅ A` in `FiniteRankAtlas 𝕜 X`,
given by the identity on every coordinate fibre. -/
noncomputable def toAtlasToBundleIso : (toAtlasFunctor.{u, v, w} 𝕜 X).obj A.toBundle ≅ A :=
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  isoOfTotalSpaceHomeomorph (fun x ↦ LinearEquiv.refl 𝕜 (A.Fiber x))
    (V.toAtlasTotalSpaceHomeomorph.symm.trans A.toBundleTotalSpaceHomeomorph) fun x v ↦ by
      simp only [V, Homeomorph.trans_apply, toAtlasTotalSpaceHomeomorph_symm_apply,
        FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply, preferredChartEquiv_toBundle,
        ContinuousLinearEquiv.apply_symm_apply]
      exact congrArg (TotalSpace.mk x) (LinearEquiv.refl_apply (R := 𝕜) (v : A.Fiber x)).symm
/-- The forward morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_hom (x : X) :
    (toAtlasToBundleIso.{u, v, w} A).hom.fiberMap x = LinearMap.id := by
  rw [toAtlasToBundleIso, fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.refl_toLinearMap]
/-- The inverse morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_inv (x : X) :
    (toAtlasToBundleIso.{u, v, w} A).inv.fiberMap x = LinearMap.id := by
  simpa only [fiberMap_comp, fiberMap_toAtlasToBundleIso_hom, LinearMap.id_comp, fiberMap_id] using
    congrArg (fun k : A ⟶ A ↦ k.fiberMap x) (toAtlasToBundleIso.{u, v, w} A).inv_hom_id
end

instance : (toAtlasFunctor.{u, v, w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundle, ⟨toAtlasToBundleIso A⟩⟩
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).IsEquivalence where
variable (𝕜 X) in
/-- When the fibre universe `w` is at least the scalar field universe `v`, variable-rank vector
bundles with fibres in `Type w` are categorically equivalent to small coordinate atlases. -/
noncomputable def atlasEquivalence : FiniteRankVectorBundle.{u, v, w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X :=
  (toAtlasFunctor.{u, v, w} 𝕜 X).asEquivalence
@[simp] theorem atlasEquivalence_functor :
    (atlasEquivalence.{u, v, w} 𝕜 X).functor = toAtlasFunctor.{u, v, w} 𝕜 X := by rfl
end Equivalence

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
