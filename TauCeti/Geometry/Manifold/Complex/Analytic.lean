/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Complex manifolds are analytic

A complex manifold is a manifold modelled on a finite-dimensional complex normed space whose
transition maps are holomorphic, that is `C^1` over `ℂ`. By the several-variable Cauchy integral
formula, a function of finitely many complex variables which is complex differentiable on an open
set is analytic there (`DifferentiableOn.analyticOnNhd_of_finiteDimensional`). This file draws the
manifold consequences of that fact, for a model without boundary.

* The `C^n` groupoids over `ℂ` coincide for all `n ≠ 0`, so a complex manifold of class `C^1` is
  automatically of class `C^n` for every `n`, including `n = ω`, with the same maximal atlas.
* Restricting scalars, a complex manifold modelled on `𝓘(ℂ, E)` is a real-analytic manifold
  modelled on `𝓘(ℝ, E)`, and each of its holomorphic charts is a real-analytic chart. This is the
  smooth structure underlying the real differential geometry of complex manifolds.
* A map between complex manifolds is holomorphic on an open set if and only if it is `C^n` there,
  for any `n ≠ 0`; holomorphy near a point is equivalent to being `C^n` at that point.

## Main results

* `TauCeti.contDiffGroupoid_le_of_ne_zero`, `TauCeti.contDiffGroupoid_eq_of_ne_zero`: the `C^m`
  and `C^n` groupoids of a boundaryless model on a finite-dimensional complex space agree for
  `m, n ≠ 0`.
* `IsManifold.of_ne_zero`: a complex `C^m` manifold, `m ≠ 0`, is a complex `C^n` manifold for
  every `n`.
* `IsManifold.maximalAtlas_eq_of_ne_zero`: its maximal atlases for all orders `n ≠ 0` agree.
* `IsManifold.restrictScalars_of_ne_zero`: a complex manifold modelled on `𝓘(ℂ, E)` is a real
  `C^n` manifold modelled on `𝓘(ℝ, E)` for every `n`, in particular a real-analytic one.
* `IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero`: its holomorphic charts belong to the
  real-analytic maximal atlas.
* `MDifferentiableOn.contMDiffOn`, `MDifferentiable.contMDiff`: a holomorphic map between complex
  manifolds is `C^n` for every `n`.
* `TauCeti.contMDiffOn_iff_mdifferentiableOn`, `TauCeti.contMDiff_iff_mdifferentiable`,
  `TauCeti.contMDiffAt_iff_eventually_mdifferentiableAt`: the corresponding characterizations of
  holomorphy.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m n : ℕ∞ω}

/-! ### The groupoids and atlases of a complex manifold -/

/-- For a boundaryless model on a finite-dimensional complex space, the `C^1` groupoid is contained
in the `C^n` groupoid for every `n`: a holomorphic open partial homeomorphism is analytic. -/
private theorem contDiffGroupoid_one_le : contDiffGroupoid 1 I ≤ contDiffGroupoid n I := by
  have key {g : E → E} {u : Set H} (hu : IsOpen u) (hg : ContDiffOn ℂ 1 g (I.symm ⁻¹' u)) :
      ContDiffOn ℂ n g (I.symm ⁻¹' u) :=
    have := FiniteDimensional.complete ℂ E
    (hg.differentiableOn one_ne_zero).contDiffOn_of_finiteDimensional
      (hu.preimage I.continuous_symm)
  refine StructureGroupoid.le_iff.2 fun e he ↦ ?_
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at he ⊢
  simp only [contDiffPregroupoid, I.range_eq_univ, inter_univ] at he ⊢
  exact ⟨key e.open_source he.1, key e.open_target he.2⟩

/-- For a boundaryless model on a finite-dimensional complex space, the `C^m` groupoid is contained
in the `C^n` groupoid for every `n` as soon as `m ≠ 0`. -/
theorem contDiffGroupoid_le_of_ne_zero (hm : m ≠ 0) :
    contDiffGroupoid m I ≤ contDiffGroupoid n I :=
  (contDiffGroupoid_le (ENat.one_le_iff_ne_zero_withTop.2 hm)).trans contDiffGroupoid_one_le

/-- For a boundaryless model on a finite-dimensional complex space, the `C^m` and `C^n` groupoids
agree whenever `m` and `n` are nonzero. -/
theorem contDiffGroupoid_eq_of_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) :
    contDiffGroupoid m I = contDiffGroupoid n I :=
  le_antisymm (contDiffGroupoid_le_of_ne_zero hm) (contDiffGroupoid_le_of_ne_zero hn)

variable (n) in
/-- A complex manifold of class `C^m` for some `m ≠ 0`, modelled without boundary on a
finite-dimensional space, is a complex manifold of class `C^n` for every `n`, including
`n = ω`. -/
theorem _root_.IsManifold.of_ne_zero (hm : m ≠ 0) (h : IsManifold I m M) : IsManifold I n M :=
  { hasGroupoid_of_le h.toHasGroupoid (contDiffGroupoid_le_of_ne_zero hm) with }

/-- The maximal atlases of a complex manifold, modelled without boundary on a finite-dimensional
space, agree for all nonzero orders of smoothness. -/
theorem _root_.IsManifold.maximalAtlas_eq_of_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) :
    IsManifold.maximalAtlas I m M = IsManifold.maximalAtlas I n M := by
  rw [IsManifold.maximalAtlas, IsManifold.maximalAtlas, contDiffGroupoid_eq_of_ne_zero hm hn]

/-! ### The underlying real-analytic manifold -/

section RestrictScalars

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

variable (n) in
/-- **A complex manifold is a real-analytic manifold.** A complex manifold modelled on
`𝓘(ℂ, E)`, of class `C^m` for some `m ≠ 0` with `E` finite-dimensional, is with the same charts a
real `C^n` manifold modelled on `𝓘(ℝ, E)` for every `n`; for `n = ω` it is real-analytic. -/
theorem _root_.IsManifold.restrictScalars_of_ne_zero (hm : m ≠ 0) (h : IsManifold 𝓘(ℂ, E) m M) :
    IsManifold 𝓘(ℝ, E) n M :=
  (h.of_ne_zero n hm).restrictScalars ℝ

variable (n) in
/-- Every holomorphic chart of a complex manifold modelled on `𝓘(ℂ, E)`, with `E`
finite-dimensional, is a chart of the real `C^n` maximal atlas for every `n`; for `n = ω` it is a
real-analytic chart. -/
theorem _root_.IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero (hm : m ≠ 0) :
    IsManifold.maximalAtlas 𝓘(ℂ, E) m M ⊆ IsManifold.maximalAtlas 𝓘(ℝ, E) n M := by
  rw [IsManifold.maximalAtlas_eq_of_ne_zero hm (n := ω) (by simp)]
  exact (IsManifold.maximalAtlas_subset_restrictScalars ℝ).trans
    (StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le le_top))

end RestrictScalars

/-! ### Holomorphic maps -/

section Maps

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M] [IsManifold I' 1 M']
  {f : M → M'} {s : Set M} {x : M}

/-- A map between complex manifolds which is holomorphic on an open set is `C^n` on it for every
`n`, including `n = ω`. The source is modelled without boundary on a finite-dimensional space; the
target only needs a complete model space. -/
theorem _root_.MDifferentiableOn.contMDiffOn (hf : MDifferentiableOn I I' f s) (hs : IsOpen s) :
    ContMDiffOn I I' n f s := by
  intro x hx
  obtain ⟨hc, hd⟩ := mdifferentiableOn_iff.1 hf
  -- The coordinates near `extChartAt I x x` on which the chart representative of `f` is defined
  -- form an open set, on which this representative is complex differentiable.
  set t := (extChartAt I x).target ∩
    (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source)
  have ht : IsOpen t := (continuousOn_extChartAt_symm x).isOpen_inter_preimage
    (isOpen_extChartAt_target x) (hc.isOpen_inter_preimage hs (isOpen_extChartAt_source (f x)))
  have hxt : extChartAt I x x ∈ t :=
    ⟨mem_extChartAt_target x, by
      rw [mem_preimage, extChartAt_to_inv]
      exact ⟨hx, mem_extChartAt_source (f x)⟩⟩
  refine (contMDiffAt_iff.2 ⟨hc.continuousAt (hs.mem_nhds hx), ?_⟩).contMDiffWithinAt
  rw [I.range_eq_univ, contDiffWithinAt_univ]
  exact ((hd x (f x)).contDiffOn_of_finiteDimensional ht).contDiffAt (ht.mem_nhds hxt)

/-- A holomorphic map between complex manifolds is `C^n` for every `n`, including `n = ω`. -/
theorem _root_.MDifferentiable.contMDiff (hf : MDifferentiable I I' f) : ContMDiff I I' n f := by
  rw [← contMDiffOn_univ]
  exact hf.mdifferentiableOn.contMDiffOn isOpen_univ

/-- On an open set, a map between complex manifolds is `C^n`, for any `n ≠ 0`, if and only if it
is holomorphic. -/
theorem contMDiffOn_iff_mdifferentiableOn (hn : n ≠ 0) (hs : IsOpen s) :
    ContMDiffOn I I' n f s ↔ MDifferentiableOn I I' f s :=
  ⟨fun h ↦ h.mdifferentiableOn hn, fun h ↦ h.contMDiffOn hs⟩

/-- A map between complex manifolds is `C^n`, for any `n ≠ 0`, if and only if it is
holomorphic. -/
theorem contMDiff_iff_mdifferentiable (hn : n ≠ 0) :
    ContMDiff I I' n f ↔ MDifferentiable I I' f :=
  ⟨fun h ↦ h.mdifferentiable hn, fun h ↦ h.contMDiff⟩

/-- A map between complex manifolds is `C^n` at a point, for any `n ≠ 0`, if and only if it is
holomorphic at every point of a neighbourhood. This is the manifold form of
`Complex.analyticAt_iff_eventually_differentiableAt`. -/
theorem contMDiffAt_iff_eventually_mdifferentiableAt (hn : n ≠ 0) :
    ContMDiffAt I I' n f x ↔ ∀ᶠ y in 𝓝 x, MDifferentiableAt I I' f y := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨u, hu, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1
      (hf.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn))
    filter_upwards [eventually_mem_nhds_iff.2 hu] with y hy
    exact (hfu.contMDiffAt hy).mdifferentiableAt one_ne_zero
  · obtain ⟨t, hft, ht, hxt⟩ := eventually_nhds_iff.1 hf
    exact (MDifferentiableOn.contMDiffOn (fun y hy ↦ (hft y hy).mdifferentiableWithinAt) ht)
      |>.contMDiffAt (ht.mem_nhds hxt)

end Maps

end TauCeti
