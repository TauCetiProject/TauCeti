/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Germ
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Analytic germs under changes of charts

The scalar analytic germ rings in two analytic charts at the same manifold point are
canonically isomorphic. `ModelWithCorners.analyticGermsEquiv` is pullback by the analytic
change of extended charts. It has an explicit representative formula, reverses when the
charts are exchanged, and satisfies the identity and cocycle laws. Thus local analytic
functions can be transported without retaining a particular chart or neighborhood.

For a scalar analytic function on the manifold,
`analyticGermsEquiv_ofAnalyticAt_comp_extend_symm_of_contMDiffAt` identifies its two chart
representatives. In particular, equality of the local functions can be tested
in either chart.

The model is boundaryless so that the transition domains are neighborhoods in the full
normed model space. No finite-dimensionality or countability assumption is needed.
The construction uses `TauCeti.analyticGerms.pullback` and its local-inverse equivalence;
complexification compatibility is consequently given by
`TauCeti.analyticGerms.complexify_pullback` for real finite-coordinate models.
-/

public section

open Filter Function IsManifold Topology
open scoped ContDiff Manifold

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {e e' e'' : OpenPartialHomeomorph M H} {x : M}

/-- Pullback by a change of analytic charts identifies the analytic germ rings at the two
coordinates of the same point. The direction is from the second chart to the first. -/
def analyticGermsEquiv (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    TauCeti.analyticGerms 𝕜 (I (e' x)) ≃+* TauCeti.analyticGerms 𝕜 (I (e x)) :=
  TauCeti.analyticGerms.equivOfInverse (I.extendCoordChange e e') (I.extendCoordChange e' e)
    (I.analyticAt_extendCoordChange he he' hx hx')
    (I.analyticAt_extendCoordChange he' he hx' hx)
    (I.extendCoordChange_apply hx)
    (by
      filter_upwards [I.extendCoordChange_source_mem_nhds hx hx'] with y hy
      exact (I.extendCoordChange e e').left_inv hy)
    (by
      filter_upwards [I.extendCoordChange_source_mem_nhds hx' hx] with y hy
      exact (I.extendCoordChange e' e).left_inv hy)

/-- Chart transport acts by analytic pullback along the transition map. -/
@[simp]
theorem analyticGermsEquiv_apply (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (φ : TauCeti.analyticGerms 𝕜 (I (e' x))) :
    I.analyticGermsEquiv he he' hx hx' φ =
      TauCeti.analyticGerms.pullback (I.extendCoordChange e e')
        (I.analyticAt_extendCoordChange he he' hx hx')
        (I.extendCoordChange_apply hx) φ := by
  unfold analyticGermsEquiv
  exact TauCeti.analyticGerms.equivOfInverse_apply _ _ _ _ _ _ _ φ

/-- Exchanging the two charts gives the inverse germ equivalence. -/
@[simp]
theorem analyticGermsEquiv_symm (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (I.analyticGermsEquiv he he' hx hx').symm = I.analyticGermsEquiv he' he hx' hx := by
  apply RingEquiv.ext
  intro φ
  unfold analyticGermsEquiv
  exact (TauCeti.analyticGerms.equivOfInverse_symm_apply _ _ _ _ _ _ _ φ).trans
    (TauCeti.analyticGerms.equivOfInverse_apply _ _ _ _ _ _ _ φ).symm

/-- Transport from a chart to itself fixes every analytic germ. -/
@[simp 1100]
theorem analyticGermsEquiv_self_apply (he : e ∈ maximalAtlas I ω M) (hx : x ∈ e.source)
    (φ : TauCeti.analyticGerms 𝕜 (I (e x))) :
    I.analyticGermsEquiv he he hx hx φ = φ := by
  obtain ⟨f, hf, rfl⟩ := TauCeti.analyticGerms.exists_ofAnalyticAt φ
  rw [analyticGermsEquiv_apply, TauCeti.analyticGerms.pullback_ofAnalyticAt]
  apply TauCeti.analyticGerms.ofAnalyticAt_congr
  filter_upwards [I.extendCoordChange_source_mem_nhds hx hx] with y hy
  exact congrArg f ((e.extend I).right_inv hy.1)

/-- Transport identifies any two analytic chart representatives of the same scalar function. -/
theorem analyticGermsEquiv_ofAnalyticAt_comp_extend_symm
    (he : e ∈ maximalAtlas I ω M) (he' : e' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (f : M → 𝕜)
    (hf' : AnalyticAt 𝕜 (f ∘ (e'.extend I).symm) (I (e' x)))
    (hf : AnalyticAt 𝕜 (f ∘ (e.extend I).symm) (I (e x))) :
    I.analyticGermsEquiv he he' hx hx'
        (TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e'.extend I).symm) hf') =
      TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e.extend I).symm) hf := by
  rw [analyticGermsEquiv_apply, TauCeti.analyticGerms.pullback_ofAnalyticAt]
  exact TauCeti.analyticGerms.ofAnalyticAt_congr
    ((I.extend_symm_comp_extendCoordChange_eventuallyEq hx hx').fun_comp f)

/-- The cocycle law for chart transport: passing through an intermediate chart does not change
the resulting germ. -/
@[simp]
theorem analyticGermsEquiv_trans (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (he'' : e'' ∈ maximalAtlas I ω M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hx'' : x ∈ e''.source) :
    (I.analyticGermsEquiv he' he'' hx' hx'').trans (I.analyticGermsEquiv he he' hx hx') =
      I.analyticGermsEquiv he he'' hx hx'' := by
  apply RingEquiv.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := TauCeti.analyticGerms.exists_ofAnalyticAt φ
  rw [RingEquiv.trans_apply, I.analyticGermsEquiv_apply he' he'',
    TauCeti.analyticGerms.pullback_ofAnalyticAt, I.analyticGermsEquiv_apply he he'',
    TauCeti.analyticGerms.pullback_ofAnalyticAt]
  -- A transition representative is the representative of the function read in the final chart.
  exact I.analyticGermsEquiv_ofAnalyticAt_comp_extend_symm he he' hx hx' (f ∘ e''.extend I)
    (hf.comp_of_eq (I.analyticAt_extendCoordChange he' he'' hx' hx'')
      (I.extendCoordChange_apply hx'))
    (hf.comp_of_eq (I.analyticAt_extendCoordChange he he'' hx hx'')
      (I.extendCoordChange_apply hx))

/-- The chart representatives of an analytic scalar function correspond under chart transport.
Thus the represented local analytic function does not depend on the choice of chart. -/
theorem analyticGermsEquiv_ofAnalyticAt_comp_extend_symm_of_contMDiffAt {f : M → 𝕜}
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) ω f x) (he : e ∈ maximalAtlas I ω M)
    (he' : e' ∈ maximalAtlas I ω M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    I.analyticGermsEquiv he he' hx hx'
        (TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e'.extend I).symm)
          (hf.analyticAt_comp_extend_symm he' hx')) =
      TauCeti.analyticGerms.ofAnalyticAt (f ∘ (e.extend I).symm)
        (hf.analyticAt_comp_extend_symm he hx) :=
  I.analyticGermsEquiv_ofAnalyticAt_comp_extend_symm he he' hx hx' f
    (hf.analyticAt_comp_extend_symm he' hx') (hf.analyticAt_comp_extend_symm he hx)

end ModelWithCorners
