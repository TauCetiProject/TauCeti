/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Finite sums and differences of harmonic functions

Mathlib's `InnerProductSpace.HarmonicAt.add` and `InnerProductSpace.HarmonicOnNhd.add` show that
harmonic functions are closed under addition. This file extends this to finite sums, shows that
continuous linear maps are harmonic, and shows that two `C²` functions with the same Laplacian
near a point differ by a harmonic function there.

## Main declarations

* `InnerProductSpace.HarmonicAt.sum`, `InnerProductSpace.HarmonicOnNhd.sum`: a finite sum of
  harmonic functions is harmonic.
* `ContinuousLinearMap.harmonicAt`, `ContinuousLinearMap.harmonicOnNhd`: continuous linear maps
  are harmonic.
* `ContDiffAt.harmonicAt_sub_of_laplacian_eventuallyEq`: two `C²` functions whose Laplacians agree
  near `x` differ by a function harmonic at `x`.
-/

public section

namespace InnerProductSpace

open Laplacian Filter Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ι → E → F} {u : Finset ι} {x : E}
  {s : Set E}

/-- A finite sum of functions harmonic at `x` is harmonic at `x`. -/
theorem HarmonicAt.sum (h : ∀ i ∈ u, HarmonicAt (f i) x) :
    HarmonicAt (fun y => ∑ i ∈ u, f i y) x := by
  rw [← Finset.sum_fn]
  exact Finset.sum_induction _ (HarmonicAt · x) (fun _ _ => .add) (harmonicAt_const 0) h

/-- A finite sum of functions harmonic on a neighborhood of `s` is harmonic there. -/
theorem HarmonicOnNhd.sum (h : ∀ i ∈ u, HarmonicOnNhd (f i) s) :
    HarmonicOnNhd (fun y => ∑ i ∈ u, f i y) s :=
  fun x hx => HarmonicAt.sum fun i hi => h i hi x hx

/-- A continuous linear map is harmonic at every point: its second derivative vanishes. -/
@[simp]
theorem _root_.ContinuousLinearMap.harmonicAt (l : E →L[ℝ] F) : HarmonicAt l x :=
  ⟨l.contDiff.contDiffAt, Eventually.of_forall fun y => by
    have hl : fderiv ℝ l = fun _ => l := funext fun _ => l.fderiv
    simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply, hl]⟩

/-- A continuous linear map is harmonic on every set. -/
@[simp]
theorem _root_.ContinuousLinearMap.harmonicOnNhd (l : E →L[ℝ] F) : HarmonicOnNhd l s :=
  fun _ _ => l.harmonicAt

/-- Two functions of class `C²` at `x` whose Laplacians agree near `x` differ by a function
harmonic at `x`. -/
theorem _root_.ContDiffAt.harmonicAt_sub_of_laplacian_eventuallyEq {g h : E → F}
    (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x) (hgh : Δ g =ᶠ[𝓝 x] Δ h) :
    HarmonicAt (g - h) x := by
  refine ⟨hg.sub hh, ?_⟩
  filter_upwards [hg.laplacian_sub_nhds hh, hgh] with y hy hy'
  rw [hy, Pi.sub_apply, hy', sub_self, Pi.zero_apply]

end InnerProductSpace
