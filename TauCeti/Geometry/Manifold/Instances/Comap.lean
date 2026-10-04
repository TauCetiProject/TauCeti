/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Charts pulled back along a local homeomorphism

Let `p : M → B` be a local homeomorphism onto a charted space `B`. Each point `x : M` has an open
neighbourhood that `p` maps homeomorphically onto an open subset of `B`; following this
homeomorphism by the preferred chart of `B` at `p x` gives a chart of `M` at `x`. These charts form
the pulled-back charted-space structure `IsLocalHomeomorph.chartedSpaceComap`. Every chart of `M`
reads a point `y` as the chart of `B` at `p x` reads `p y`.

This is how a covering space of a manifold, such as the universal cover, receives its atlas. Mathlib
pushes charts forward along a surjective local homeomorphism
(`IsLocalHomeomorph.chartedSpaceOfRightInverse`); this file supplies the dual construction.

The transition maps of the pulled-back atlas are restrictions of transition maps of `B`, so the
pulled-back charts form a `C^n` manifold whenever `B` is one, and `p` is then a `C^n` local
diffeomorphism. A map into `M` is `C^n` exactly when it is continuous and its composite with `p` is
`C^n`: in the pulled-back charts the two composites have the same coordinate expression.

## Main definitions

* `IsLocalHomeomorph.chartedSpaceComap`: the charts of `B` pulled back along `p`.

## Main results

* `IsLocalHomeomorph.isManifold_chartedSpaceComap`: the pulled-back charts of a `C^n` manifold form
  a `C^n` manifold.
* `IsLocalHomeomorph.contMDiff_chartedSpaceComap_iff`: a map into `M` is `C^n` if and only if it is
  continuous and its composite with `p` is `C^n`; also in `Within`, `At` and `On` forms.
* `IsLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap`: `p` is a `C^n` local diffeomorphism
  for the pulled-back charts.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4, "Smooth Covering Maps".
-/

public section

open Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

namespace IsLocalHomeomorph

variable {M : Type*} [TopologicalSpace M] {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {p : M → B} (hp : IsLocalHomeomorph p)

/-- The charted-space structure on the source of a local homeomorphism `p : M → B` pulled back
from `B`: the chart at `x` is the local inverse of `p` at `x`, inverted, followed by the chart of
`B` at `p x`. -/
@[instance_reducible]
noncomputable def chartedSpaceComap : ChartedSpace H M where
  atlas := range fun x : M ↦ (hp.localInverseAt x).symm.trans (chartAt H (p x))
  chartAt x := (hp.localInverseAt x).symm.trans (chartAt H (p x))
  mem_chart_source x := by simp
  chart_mem_atlas x := mem_range_self x

/-- The pulled-back chart at `x` is the local inverse of `p` at `x`, inverted, followed by the
chart of `B` at `p x`. -/
theorem chartAt_chartedSpaceComap (x : M) :
    letI := hp.chartedSpaceComap (H := H)
    chartAt H x = (hp.localInverseAt x).symm.trans (chartAt H (p x)) :=
  (rfl)

/-- The pulled-back chart at `x` reads `y` as the chart of `B` at `p x` reads `p y`. -/
@[simp]
theorem chartAt_chartedSpaceComap_apply (x y : M) :
    letI := hp.chartedSpaceComap (H := H)
    chartAt H x y = chartAt H (p x) (p y) := by
  simp [chartAt_chartedSpaceComap]

/-- The pulled-back extended chart at `x` reads `y` as the extended chart of `B` at `p x` reads
`p y`. -/
theorem extChartAt_chartedSpaceComap_apply (x y : M) :
    letI := hp.chartedSpaceComap (H := H)
    extChartAt I x y = extChartAt I (p x) (p y) := by
  let := hp.chartedSpaceComap (H := H)
  simp only [extChartAt_coe, Function.comp_apply, hp.chartAt_chartedSpaceComap_apply]

/-- The charts of a `C^n` manifold pulled back along a local homeomorphism form a `C^n` manifold:
their transition maps are restrictions of transition maps of the base. -/
theorem isManifold_chartedSpaceComap [IsManifold I n B] :
    letI := hp.chartedSpaceComap (H := H)
    IsManifold I n M := by
  let := hp.chartedSpaceComap (H := H)
  refine isManifold_of_contDiffOn I n M ?_
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  refine (contDiffOn_ext_coord_change (I := I) (n := n) (p y) (p x)).congr_mono ?_ ?_
  · rintro u ⟨hu, -⟩
    simp only [mfld_simps, localInverseAt_symm] at hu ⊢
    rw [hp.apply_localInverseAt_of_mem hu.1.2]
  · rintro u ⟨hu, huI⟩
    simp only [mfld_simps, localInverseAt_symm] at hu ⊢
    refine ⟨⟨huI, hu.1.1⟩, ?_⟩
    rw [← hp.apply_localInverseAt_of_mem hu.1.2]
    exact hu.2.2

section ContMDiff

variable {f : N → M} {s : Set N} {z : N}

/-- A map into the source of a local homeomorphism `p` is `C^n` within `s` at `z` for the
pulled-back charts if and only if it is continuous within `s` at `z` and its composite with `p` is
`C^n` within `s` at `z`. -/
theorem contMDiffWithinAt_chartedSpaceComap_iff :
    letI := hp.chartedSpaceComap (H := H)
    ContMDiffWithinAt I' I n f s z ↔ ContinuousWithinAt f s z ∧ ContMDiffWithinAt I' I n (p ∘ f) s z
    := by
  let := hp.chartedSpaceComap (H := H)
  have h : extChartAt I (f z) ∘ f = extChartAt I (p (f z)) ∘ (p ∘ f) := by
    ext1 y
    simp
  rw [contMDiffWithinAt_iff, contMDiffWithinAt_iff, Function.comp_apply, ← Function.comp_assoc, h,
    Function.comp_assoc]
  exact ⟨fun h ↦ ⟨h.1, hp.continuous.continuousAt.comp_continuousWithinAt h.1, h.2⟩,
    fun h ↦ ⟨h.1, h.2.2⟩⟩

/-- A map into the source of a local homeomorphism `p` is `C^n` at `z` for the pulled-back charts
if and only if it is continuous at `z` and its composite with `p` is `C^n` at `z`. -/
theorem contMDiffAt_chartedSpaceComap_iff :
    letI := hp.chartedSpaceComap (H := H)
    ContMDiffAt I' I n f z ↔ ContinuousAt f z ∧ ContMDiffAt I' I n (p ∘ f) z := by
  simpa only [← contMDiffWithinAt_univ, continuousWithinAt_univ] using
    hp.contMDiffWithinAt_chartedSpaceComap_iff (I := I) (I' := I') (n := n) (f := f) (s := univ)

/-- A map into the source of a local homeomorphism `p` is `C^n` on `s` for the pulled-back charts
if and only if it is continuous on `s` and its composite with `p` is `C^n` on `s`. -/
theorem contMDiffOn_chartedSpaceComap_iff :
    letI := hp.chartedSpaceComap (H := H)
    ContMDiffOn I' I n f s ↔ ContinuousOn f s ∧ ContMDiffOn I' I n (p ∘ f) s := by
  let := hp.chartedSpaceComap (H := H)
  simp only [ContMDiffOn, ContinuousOn, hp.contMDiffWithinAt_chartedSpaceComap_iff, ← forall₂_and]

/-- A map into the source of a local homeomorphism `p` is `C^n` for the pulled-back charts if and
only if it is continuous and its composite with `p` is `C^n`. -/
theorem contMDiff_chartedSpaceComap_iff :
    letI := hp.chartedSpaceComap (H := H)
    ContMDiff I' I n f ↔ Continuous f ∧ ContMDiff I' I n (p ∘ f) := by
  let := hp.chartedSpaceComap (H := H)
  simp only [ContMDiff, continuous_iff_continuousAt, hp.contMDiffAt_chartedSpaceComap_iff,
    forall_and]

end ContMDiff

/-- A local homeomorphism is `C^n` for the charts it pulls back. -/
theorem contMDiff_chartedSpaceComap :
    letI := hp.chartedSpaceComap (H := H)
    ContMDiff I I n p := by
  let := hp.chartedSpaceComap (H := H)
  exact (hp.contMDiff_chartedSpaceComap_iff.1 (contMDiff_id (I := I) (n := n))).2

/-- A local homeomorphism onto a `C^n` manifold is a `C^n` local diffeomorphism for the charts it
pulls back. -/
theorem isLocalDiffeomorph_chartedSpaceComap :
    letI := hp.chartedSpaceComap (H := H)
    IsLocalDiffeomorph I I n p := by
  let := hp.chartedSpaceComap (H := H)
  intro x
  set L := hp.localInverseAt x
  have hLs : ⇑L.symm = p := hp.localInverseAt_symm x
  have hL : ContMDiffOn I I n L L.source :=
    hp.contMDiffOn_chartedSpaceComap_iff.2 ⟨L.continuousOn,
      contMDiffOn_id.congr fun y hy ↦ hp.apply_localInverseAt_of_mem hy⟩
  let Φ : PartialDiffeomorph I I M B n :=
    { toPartialEquiv := L.symm.toPartialEquiv.copy p hLs L rfl L.target rfl L.source rfl
      open_source := L.open_target
      open_target := L.open_source
      contMDiffOn_toFun := hp.contMDiff_chartedSpaceComap.contMDiffOn
      contMDiffOn_invFun := hL }
  exact Φ.isLocalDiffeomorphAt I I n hp.self_mem_localInverseAt_target

end IsLocalHomeomorph
