/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

/-!
# Diffeomorphism invariance of smooth singular chain comparisons

Mutually inverse smooth maps between charted spaces induce isomorphisms of both smooth singular
subcomplexes and singular simplicial sets intertwining the inclusions of smooth chains into
singular chains. Consequently, the quasi-isomorphism property of the smooth-to-singular chain map
is invariant under mutually inverse smooth maps
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv`) and in
particular under smooth diffeomorphisms
(`Diffeomorph.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff`).

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv`: mutually inverse
  smooth maps transport the quasi-isomorphism property of the inclusion of smooth singular chains
  into singular chains.
* `Diffeomorph.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff`: a smooth diffeomorphism
  preserves and reflects whether the inclusion of smooth singular chains into singular chains is a
  quasi-isomorphism.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
  [CategoryWithHomology C] (R : C)

/-- Mutually inverse smooth maps transport the quasi-isomorphism property of the inclusion of
smooth singular chains into singular chains. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv
    {f : M → N} {g : N → M} (hf : ContMDiff I J ∞ f) (hg : ContMDiff J I ∞ g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hN : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have hgf_top : (TopCat.ofHom ⟨f, hf.continuous⟩ : TopCat.of M ⟶ TopCat.of N) ≫
      TopCat.ofHom ⟨g, hg.continuous⟩ = 𝟙 (TopCat.of M) := by ext x; exact hgf x
  have hfg_top : (TopCat.ofHom ⟨g, hg.continuous⟩ : TopCat.of N ⟶ TopCat.of M) ≫
      TopCat.ofHom ⟨f, hf.continuous⟩ = 𝟙 (TopCat.of N) := by ext y; exact hfg y
  let eS : (smoothSingularSubcomplex I M : SSet) ≅ (smoothSingularSubcomplex J N : SSet) :=
    { hom := smoothSingularSubcomplexMap f hf
      inv := smoothSingularSubcomplexMap g hg
      hom_inv_id := by
        rw [← cancel_mono (smoothSingularSubcomplex I M).ι]
        simp [← Functor.map_comp, hgf_top]
      inv_hom_id := by
        rw [← cancel_mono (smoothSingularSubcomplex J N).ι]
        simp [← Functor.map_comp, hfg_top] }
  let eT : TopCat.of M ≅ TopCat.of N :=
    ⟨TopCat.ofHom ⟨f, hf.continuous⟩, TopCat.ofHom ⟨g, hg.continuous⟩, hgf_top, hfg_top⟩
  refine quasiIso_of_arrow_mk_iso
    (SSet.chainComplexMap (smoothSingularSubcomplex J N).ι R)
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
    (Arrow.isoMk (((SSet.chainComplexFunctor C).obj R).mapIso eS.symm)
      (((SSet.chainComplexFunctor C).obj R).mapIso (TopCat.toSSet.mapIso eT.symm)) ?_)
  dsimp only [Arrow.mk_hom, Functor.mapIso_hom, Iso.symm_hom, eS, eT]
  exact (((SSet.chainComplexFunctor C).obj R).map_comp _ _).symm.trans
    ((congrArg (((SSet.chainComplexFunctor C).obj R).map)
      (smoothSingularSubcomplexMap_ι hg)).trans
      (((SSet.chainComplexFunctor C).obj R).map_comp _ _))

end TauCeti

namespace Diffeomorph

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] [CategoryWithHomology C]

/-- A smooth diffeomorphism preserves and reflects whether the inclusion of smooth singular chains
into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff (e : M ≃ₘ⟮I, J⟯ N) (R : C) :
    QuasiIso (SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex I M).ι R) ↔
      QuasiIso (SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex J N).ι R) :=
  ⟨TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R
      e.symm.contMDiff e.contMDiff e.apply_symm_apply e.symm_apply_apply,
    TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R
      e.contMDiff e.symm.contMDiff e.symm_apply_apply e.apply_symm_apply⟩

end Diffeomorph
