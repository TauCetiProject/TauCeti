/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Inverse maps read in extended charts

An open partial homeomorphism `e` between model spaces is read in the model vector spaces as
`I' ∘ e ∘ I.symm`, and its inverse as `I ∘ e.symm ∘ I'.symm`. Near a point of the range of `I`
in the preimage of the source of `e`, reading `e` and then reading `e.symm` back is the identity
(`OpenPartialHomeomorph.eventually_left_inverse_modelWithCorners`). The same holds for a
homeomorphism between charted spaces read in the preferred extended charts
(`Homeomorph.eventually_writtenInExtChartAt_left_inverse`).

These are the forms in which a local inverse of a chart reading is found, without any
differentiability or piecewise-linearity assumption.
-/

public section

open Set Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M']

/-- Near a point `w` of the range of `I` whose preimage lies in the source of `e`, reading `e` in
the model vector spaces and then reading `e.symm` back is the identity. -/
theorem OpenPartialHomeomorph.eventually_left_inverse_modelWithCorners
    (e : OpenPartialHomeomorph H H') {w : E} (hw : I.symm w ∈ e.source) :
    ∀ᶠ z in 𝓝[range I] w, (I ∘ e.symm ∘ I'.symm) ((I' ∘ e ∘ I.symm) z) = z := by
  filter_upwards [inter_mem_nhdsWithin (range I)
    ((e.open_source.preimage I.continuous_symm).mem_nhds hw)] with z ⟨⟨v, hv⟩, hzs⟩
  subst hv
  simp only [mem_preimage, I.left_inv] at hzs
  simp [e.left_inv hzs]

/-- Near the extended chart image of `x`, reading a homeomorphism `φ` in the extended charts at
`x` and `φ x` and then reading `φ.symm` back is the identity. -/
theorem Homeomorph.eventually_writtenInExtChartAt_left_inverse (φ : M ≃ₜ M') (x : M) :
    ∀ᶠ z in 𝓝[range I] extChartAt I x x,
      writtenInExtChartAt I' I (φ x) φ.symm (writtenInExtChartAt I I' x φ z) = z := by
  have := OpenPartialHomeomorph.eventually_left_inverse_modelWithCorners (I := I) (I' := I')
    (((chartAt H x).symm.trans φ.toOpenPartialHomeomorph).trans (chartAt H' (φ x)))
    (w := I (chartAt H x x)) (by simp [mem_chart_source])
  simpa [writtenInExtChartAt, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.coe_trans_symm, Function.comp_assoc] using this
