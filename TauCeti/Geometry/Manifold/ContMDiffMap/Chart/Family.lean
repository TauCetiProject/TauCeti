/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Jet
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Smooth families in the source-chart weak Whitney topology

A jointly `C^n` vector-valued map on a product of manifolds gives a continuous family of
`C^n` maps for the source-chart weak Whitney topology. Both manifolds may have boundary or
corners. In coordinates, spatial derivatives are restrictions of total derivatives to
directions in the source factor; unique differentiation on extended chart targets makes
this valid even at boundary points. Compact-open currying then gives the continuous family.

This applies to manifold parameters and sources, using the topology in
`ContMDiffMap.Chart.Jet`. It is the vector-valued coordinate-family construction used for
smooth families of manifold maps.
Only the forward implication is asserted, with no differentiability claimed for an
arbitrary continuous family in the function-space topology.

Use `open scoped TauCeti.ChartWeakWhitney` to select the source-chart topology when
forming continuous maps into the smooth-map space or using `ContMDiffMap.chartWeakWhitneyCurry`.
For normed spaces, `modelWithCornersSelf_prod` and `chartedSpaceSelf_prod` identify the
product manifold structure with the global chart, and
`ContMDiffMap.chartWeakWhitneyTopology_self` identifies the resulting function-space topology
with the global weak Whitney topology.

The weak topology convention follows M. Hirsch, *Differential Topology*, GTM 33,
Chapter 2, §1.
-/

public section

open Set Topology
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n P]

open scoped TauCeti.ChartWeakWhitney

/-- Joint `C^n` regularity gives continuity into the source-chart weak Whitney topology.
Neither compactness nor absence of boundary is required of the parameter or source manifold. -/
theorem ContMDiff.continuous_chartWeakWhitney
    {f : P → C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    (hf : ContMDiff (J.prod I) 𝓘(𝕜, F) n (fun z : P × M ↦ f z.1 z.2)) :
    Continuous f := by
  apply ContMDiffMap.continuous_chartWeakWhitney_iff.mpr
  intro x m hm
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcoord : ContDiffOn 𝕜 n
      (fun z : E' × E ↦ f ((extChartAt J p).symm z.1) ((extChartAt I x).symm z.2))
      ((extChartAt J p).target ×ˢ (extChartAt I x).target) := by
    have h := hf.comp_contMDiffOn ((contMDiffOn_extChartAt_symm p).prodMap
      (contMDiffOn_extChartAt_symm x))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  have hderiv := hcoord.continuousOn_iteratedFDerivWithin_prod_right
    ((uniqueDiffOn_extChartAt_target p).prod (uniqueDiffOn_extChartAt_target x))
    m hm
  have hjet : ContinuousOn
      (fun a : E' ↦ ContMDiffMap.chartIteratedFDeriv
        (f ((extChartAt J p).symm a)) x m hm) (extChartAt J p).target := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have h := hderiv.comp_continuous
      (continuous_subtype_val.prodMap continuous_subtype_val)
      (fun z ↦ ⟨z.1.property, z.2.property⟩)
    convert h using 1
    funext z
    refine (ContMDiffMap.chartIteratedFDeriv_apply
      (f ((extChartAt J p).symm z.1)) x m hm z.2).trans ?_
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, Function.comp_def, id_eq, Prod.map_fst, Prod.map_snd]
  have hlocal := hjet.comp (continuousOn_extChartAt p) (extChartAt J p).mapsTo
  have hlocal' : ContinuousOn (fun q ↦ ContMDiffMap.chartIteratedFDeriv (f q) x m hm)
      (extChartAt J p).source := hlocal.congr fun q hq ↦ by
    simp only [Function.comp_apply, (extChartAt J p).left_inv hq]
  exact hlocal'.continuousAt (extChartAt_source_mem_nhds p)

namespace ContMDiffMap

/-- Curry a jointly `C^n` vector-valued map on two manifolds into a continuous family,
using the source-chart weak Whitney topology on the space of `C^n` maps. -/
noncomputable def chartWeakWhitneyCurry
    (f : C^n⟮J.prod I, P × M; 𝓘(𝕜, F), F⟯) :
    C(P, C^n⟮I, M; 𝓘(𝕜, F), F⟯) where
  toFun p := ⟨fun x ↦ f (p, x),
    f.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)⟩
  continuous_toFun := f.contMDiff.continuous_chartWeakWhitney

/-- Evaluating the curried family at `p` and `x` recovers `f (p, x)`. -/
@[simp]
theorem chartWeakWhitneyCurry_apply
    (f : C^n⟮J.prod I, P × M; 𝓘(𝕜, F), F⟯) (p : P) (x : M) :
    chartWeakWhitneyCurry f p x = f (p, x) := (rfl)

end ContMDiffMap
