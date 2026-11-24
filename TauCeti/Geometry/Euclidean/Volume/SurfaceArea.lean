/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Affine
import TauCeti.Analysis.Calculus.FDeriv.InfDist
import TauCeti.Analysis.Convex.Parallel
import TauCeti.Analysis.Convex.Topology
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.InnerProductSpace.Projection.Minimal
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.DiamFrontier
import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import TauCeti.Topology.MetricSpace.Thickening

/-!
# The surface area of convex bodies and the derivative of parallel volume

Let `E` be a finite-dimensional real inner product space of dimension `n`, and measure surfaces
with the normalized Euclidean Hausdorff measure `Hⁿ⁻¹ = μHE[n - 1]`. This file identifies the
surface area `Hⁿ⁻¹(frontier K)` of a bounded convex set `K` with nonempty interior as the right
derivative at `t = 0` of its outer parallel volume:

`d/dt|_{t = 0⁺} |K + t • closedBall 0 1| = Hⁿ⁻¹(frontier K)`

(`Convex.hasDerivWithinAt_volume_real_add_smul_closedBall`).

This is the classical definition of the surface area of a convex body as the first variation of
its volume under outer parallel enlargement. The De Giorgi perimeter `P(K)` has the same right
derivative (`Convex.hasDerivWithinAt_measureReal_add_smul_closedBall`), so uniqueness of the
derivative identifies the perimeter of a convex body with the Hausdorff measure of its frontier
(`Convex.perimeter_eq_euclideanHausdorffMeasure_frontier` in
`TauCeti.Analysis.BoundedVariation.ParallelVolume`). Isoperimetric and Brunn–Minkowski arguments
phrased with perimeter thus apply to Hausdorff surface area on convex bodies, and conversely.

## Main results

* `Convex.hausdorffMeasure_frontier_le` and `Convex.euclideanHausdorffMeasure_frontier_le`: the
  Hausdorff measure of the frontier is monotone under inclusion of a convex set in a bounded set.
  The nearest-point map onto the closure of the convex set is `1`-Lipschitz, and the image of the
  frontier of the larger set under it contains the frontier of the smaller one.
* `TauCeti.volume_cthickening_sdiff_closure_eq_setLIntegral_euclideanHausdorffMeasure`: for every
  set `s`, the volume of the closed shell `cthickening r s \ closure s` is the integral over
  `0 < t ≤ r` of the `Hⁿ⁻¹` measure of the level set `{x | infDist x s = t}`. This is the coarea
  formula for the distance function, whose gradient has norm one off the closure of `s`.
* `Convex.euclideanHausdorffMeasure_frontier_lt_top`: a bounded convex set has finite surface
  area.
* `Convex.hasDerivWithinAt_volume_real_add_smul_closedBall`: the first variation of the parallel
  volume of a convex body is its surface area.

## The argument

For a convex set `K` and `t > 0`, the level set `{x | infDist x K = t}` is the frontier of the
convex parallel set `K_t = cthickening t K`. Monotonicity gives `Hⁿ⁻¹(frontier K) ≤
Hⁿ⁻¹(frontier K_t)`. If `K` contains the closed ball of radius `ρ` about `x₀`, then `K_t` lies in
the dilate of `K` about `x₀` by `(ρ + t) / ρ`, so monotonicity and scaling give
`Hⁿ⁻¹(frontier K_t) ≤ ((ρ + t) / ρ) ^ (n - 1) Hⁿ⁻¹(frontier K)`. The shell formula then squeezes
`|K_t \ K| / t` between `Hⁿ⁻¹(frontier K)` and `((ρ + t) / ρ) ^ (n - 1) Hⁿ⁻¹(frontier K)`. A
bounded convex set has the same frontier as its compact closure (`Convex.frontier_closure`), and
the same parallel volumes, since the frontiers of convex sets are null.

The interior hypothesis cannot be dropped: a segment in the plane has surface area equal to its
length, while the right derivative of its parallel area is twice its length (see
`TauCeti.hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_one_eq`).

## References

* J. A. Tropp, *Lectures on Convex Geometry*, Lecture 8, for outer parallel volumes and surface
  area of convex bodies.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4, for the coarea formula.
-/

public section

open MeasureTheory Measure Metric Set Filter Module
open scoped ENNReal NNReal Pointwise Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The case of `Convex.hausdorffMeasure_frontier_le` for a closed convex set `A`. -/
private theorem Convex.hausdorffMeasure_frontier_le_of_isClosed {A B : Set E} (hA : Convex ℝ A)
    (hAc : IsClosed A) (hAB : A ⊆ B) (hB : Bornology.IsBounded B) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (frontier A) ≤ μH[d] (frontier B) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨P, hPL, hP⟩ := hA.exists_lipschitzWith_one_forall_inner_le_zero hAc.isComplete hne
  have hfix (a : E) (ha : a ∈ A) : P a = a :=
    (sub_eq_zero.1 (real_inner_self_nonpos.1 ((hP a).2 a ha))).symm
  -- The nearest point `q = P z` of a point `z ∉ A` is also the nearest point of every point of the
  -- ray from `q` through `z`, and this ray leaves the bounded set `B` through its frontier.
  have hray (z : E) (hz : z ∉ A) : P z ∈ P '' frontier B := by
    set q := P z
    have hq : q ∈ A := (hP z).1
    set γ : ℝ → E := fun s => q + s • (z - q)
    have hγP (s : ℝ) (hs : 0 ≤ s) : P (γ s) = q := by
      have h' : ⟪γ s - q, P (γ s) - q⟫ ≤ 0 := by
        simp only [γ, add_sub_cancel_left, real_inner_smul_left]
        exact mul_nonpos_of_nonneg_of_nonpos hs ((hP z).2 _ (hP (γ s)).1)
      simpa [sub_eq_zero] using
        TauCeti.norm_sub_le_norm_sub_of_inner_sub_le_zero ((hP (γ s)).2 q hq) h'
    obtain ⟨s, hs, hsB⟩ := hB.exists_add_smul_mem_frontier (hAB hq)
      (sub_ne_zero.2 fun h : z = q => hz (h ▸ hq))
    exact ⟨γ s, hsB, hγP s hs⟩
  have hcompact : IsCompact (frontier B) :=
    hB.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  -- Every frontier point of `A` is a limit of points outside `A`, whose nearest points lie in the
  -- compact image of the frontier of `B`.
  have himage : frontier A ⊆ P '' frontier B := by
    intro a ha
    have hcl : a ∈ closure Aᶜ := by
      rw [frontier_eq_closure_inter_closure] at ha
      exact ha.2
    have hmem := image_closure_subset_closure_image hPL.continuous (mem_image_of_mem P hcl)
    rw [hfix a (hAc.frontier_subset ha)] at hmem
    exact (hcompact.image hPL.continuous).isClosed.closure_subset_iff.2
      (by rintro _ ⟨z, hz, rfl⟩; exact hray z hz) hmem
  calc μH[d] (frontier A) ≤ μH[d] (P '' frontier B) := measure_mono himage
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ d * μH[d] (frontier B) := hPL.hausdorffMeasure_image_le hd _
    _ = μH[d] (frontier B) := by simp

/-- **Monotonicity of the Hausdorff measure of the frontier for convex sets.** If a convex set `A`
lies in a bounded set `B`, then the frontier of `A` has `d`-dimensional Hausdorff measure at most
that of the frontier of `B`. -/
theorem Convex.hausdorffMeasure_frontier_le {A B : Set E} (hA : Convex ℝ A) (hAB : A ⊆ B)
    (hB : Bornology.IsBounded B) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (frontier A) ≤ μH[d] (frontier B) := by
  rw [← hA.frontier_closure]
  exact (hA.closure.hausdorffMeasure_frontier_le_of_isClosed isClosed_closure (closure_mono hAB)
    hB.closure hd).trans (measure_mono frontier_closure_subset)

/-- **Monotonicity of the surface area of convex sets.** If a convex set `A` lies in a bounded set
`B`, then the frontier of `A` has `k`-dimensional Euclidean Hausdorff measure at most that of the
frontier of `B`. -/
theorem Convex.euclideanHausdorffMeasure_frontier_le {A B : Set E} (hA : Convex ℝ A)
    (hAB : A ⊆ B) (hB : Bornology.IsBounded B) (k : ℕ) :
    μHE[k] (frontier A) ≤ μHE[k] (frontier B) := by
  simp only [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact mul_le_mul' le_rfl (hA.hausdorffMeasure_frontier_le hAB hB (Nat.cast_nonneg k))

namespace TauCeti

/-- **The volume of a closed parallel shell is the integral of the areas of the level sets of the
distance.** For every set `s` and every `r`, the volume of the shell `cthickening r s \ closure s`
is the integral over `0 < t ≤ r` of the `(n - 1)`-dimensional Euclidean Hausdorff measure of the
level set `{x | infDist x s = t}`. -/
theorem volume_cthickening_sdiff_closure_eq_setLIntegral_euclideanHausdorffMeasure
    (s : Set E) (r : ℝ) :
    volume (cthickening r s \ closure s) =
      ∫⁻ t in Ioc 0 r, μHE[finrank ℝ E - 1] {x | infDist x s = t} := by
  rcases lt_or_ge r 0 with hr | hr
  · simp [cthickening_of_nonpos hr.le, Ioc_eq_empty (not_lt.2 hr.le)]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [setLIntegral_congr_fun measurableSet_Ioc (g := 0) fun t ht => by simp [ht.1.ne]]
    simp
  set f : E → ℝ := (infDist · s)
  have hshell : cthickening r s \ closure s = f ⁻¹' Ioc 0 r := by
    ext x
    rw [Set.mem_sdiff, mem_cthickening_iff_infDist_le hs hr, mem_closure_iff_infDist_zero hs]
    exact ⟨fun h => ⟨lt_of_le_of_ne infDist_nonneg (Ne.symm h.2), h.1⟩,
      fun h => ⟨h.2, h.1.ne'⟩⟩
  have hmeas : MeasurableSet (f ⁻¹' Ioc 0 r) :=
    (continuous_infDist_pt s).measurable measurableSet_Ioc
  have hcoarea := (lipschitz_infDist_pt s)
    |>.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      hmeas.nullMeasurableSet
  rw [finrank_self] at hcoarea
  -- Off the closure of `s` the distance has gradient of norm one.
  have hjac : ∀ᵐ x ∂volume.restrict (f ⁻¹' Ioc 0 r),
      ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet = 1 := by
    filter_upwards [ae_restrict_of_ae (lipschitz_infDist_pt s).ae_differentiableAt,
      ae_restrict_mem hmeas] with x hd hx
    rw [ContinuousLinearMap.normDet_adjoint_eq_norm, norm_fderiv_infDist_eq_one hs
      (fun hcl => hx.1.ne' ((mem_closure_iff_infDist_zero hs).1 hcl)) hd, ENNReal.ofReal_one]
  have hfiber (y : ℝ) : μHE[finrank ℝ E - 1] (f ⁻¹' Ioc 0 r ∩ f ⁻¹' {y}) =
      (Ioc 0 r).indicator (fun t => μHE[finrank ℝ E - 1] {x | infDist x s = t}) y := by
    by_cases hy : y ∈ Ioc 0 r
    · rw [indicator_of_mem hy, inter_eq_right.2 fun x hx => by
        rw [mem_preimage, mem_singleton_iff.1 hx]; exact hy]
      simp only [f, preimage, mem_singleton_iff]
    · rw [indicator_of_notMem hy, ← preimage_inter, inter_singleton_eq_empty.2 hy,
        preimage_empty, measure_empty]
  rw [hshell, ← setLIntegral_one, ← lintegral_congr_ae hjac, ← hcoarea,
    lintegral_congr hfiber, lintegral_indicator measurableSet_Ioc]

/-- For a compact convex set `K`, the surface area of `K` times `t` is at most the volume of the
shell `cthickening t K \ K`, since every level set of the distance to `K` at a positive level is
the frontier of a convex set containing `K`. -/
private theorem euclideanHausdorffMeasure_frontier_mul_le_volume_cthickening_sdiff {K : Set E}
    (hKc : Convex ℝ K) (hK : IsCompact K) (t : ℝ) :
    μHE[finrank ℝ E - 1] (frontier K) * ENNReal.ofReal t ≤ volume (cthickening t K \ K) := by
  have hshell := volume_cthickening_sdiff_closure_eq_setLIntegral_euclideanHausdorffMeasure K t
  rw [hK.isClosed.closure_eq] at hshell
  rw [hshell]
  calc μHE[finrank ℝ E - 1] (frontier K) * ENNReal.ofReal t
      = ∫⁻ _ in Ioc 0 t, μHE[finrank ℝ E - 1] (frontier K) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
    _ ≤ _ := by
      refine setLIntegral_mono' measurableSet_Ioc fun τ hτ => ?_
      rw [← hKc.frontier_cthickening hτ.1]
      exact hKc.euclideanHausdorffMeasure_frontier_le (self_subset_cthickening K)
        hK.isBounded.cthickening _

/-- If a compact convex set `K` contains the closed ball of radius `ρ > 0` about `x₀`, then for
`t > 0` the level set of the distance to `K` at level `t` has surface area at most
`((ρ + t) / ρ) ^ (n - 1)` times that of `K`: it is the frontier of the parallel set
`cthickening t K`, which lies in the dilate of `K` about `x₀` by `(ρ + t) / ρ`. -/
private theorem euclideanHausdorffMeasure_setOf_infDist_eq_le {K : Set E} (hKc : Convex ℝ K)
    (hK : IsCompact K) {x₀ : E} {ρ t : ℝ} (hρ : 0 < ρ) (hρK : closedBall x₀ ρ ⊆ K) (ht : 0 < t) :
    μHE[finrank ℝ E - 1] {x | infDist x K = t} ≤
      ENNReal.ofReal (((ρ + t) / ρ) ^ (finrank ℝ E - 1)) * μHE[finrank ℝ E - 1] (frontier K) := by
  set c := (ρ + t) / ρ
  have hc : 0 < c := by positivity
  set H := AffineMap.homothety x₀ c
  have hH : Continuous H := AffineMap.homothety_continuous x₀ c
  have hsub : cthickening t K ⊆ H '' K := by
    rw [← hK.add_smul_closedBall_eq_cthickening ht.le]
    exact hKc.add_smul_closedBall_subset_image_homothety hρ hρK ht.le
  -- The homothety is an open map, so it carries interior points of `K` to interior points.
  have hfr : frontier (H '' K) ⊆ H '' frontier K := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (hK.image hH).isClosed.frontier_subset hy
    refine ⟨k, ⟨subset_closure hk, fun hint => hy.2 ?_⟩, rfl⟩
    exact (AffineMap.homothety_isOpenMap x₀ c hc.ne').image_interior_subset K ⟨k, hint, rfl⟩
  rw [← hKc.frontier_cthickening ht]
  calc μHE[finrank ℝ E - 1] (frontier (cthickening t K))
      ≤ μHE[finrank ℝ E - 1] (frontier (H '' K)) :=
        (hKc.cthickening t).euclideanHausdorffMeasure_frontier_le hsub (hK.image hH).isBounded _
    _ ≤ μHE[finrank ℝ E - 1] (H '' frontier K) := measure_mono hfr
    _ = _ := by
        rw [euclideanHausdorffMeasure_homothety_image _ _ hc.ne', ENNReal.smul_def, smul_eq_mul,
          ENNReal.ofReal_pow hc.le, ENNReal.coe_pow, Real.nnNorm_of_nonneg hc.le,
          ENNReal.ofReal_eq_coe_nnreal hc.le]

/-- If a compact convex set `K` contains the closed ball of radius `ρ > 0` about `x₀`, then the
volume of the shell `cthickening t K \ K` is at most `((ρ + t) / ρ) ^ (n - 1) t` times the
surface area of `K`. -/
private theorem volume_cthickening_sdiff_le {K : Set E} (hKc : Convex ℝ K) (hK : IsCompact K)
    {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ) (hρK : closedBall x₀ ρ ⊆ K) (t : ℝ) :
    volume (cthickening t K \ K) ≤ ENNReal.ofReal (((ρ + t) / ρ) ^ (finrank ℝ E - 1)) *
      μHE[finrank ℝ E - 1] (frontier K) * ENNReal.ofReal t := by
  have hshell := volume_cthickening_sdiff_closure_eq_setLIntegral_euclideanHausdorffMeasure K t
  rw [hK.isClosed.closure_eq] at hshell
  rw [hshell]
  calc ∫⁻ τ in Ioc 0 t, μHE[finrank ℝ E - 1] {x | infDist x K = τ}
      ≤ ∫⁻ _ in Ioc 0 t, ENNReal.ofReal (((ρ + t) / ρ) ^ (finrank ℝ E - 1)) *
          μHE[finrank ℝ E - 1] (frontier K) := by
        refine setLIntegral_mono' measurableSet_Ioc fun τ hτ => ?_
        refine (euclideanHausdorffMeasure_setOf_infDist_eq_le hKc hK hρ hρK hτ.1).trans ?_
        gcongr
        · exact div_nonneg (by linarith [hτ.1]) hρ.le
        · exact hτ.2
    _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]

/-- **Bounded convex sets have finite surface area.** The frontier of a bounded convex set has
finite `(n - 1)`-dimensional Euclidean Hausdorff measure. -/
theorem _root_.Convex.euclideanHausdorffMeasure_frontier_lt_top {K : Set E} (hKc : Convex ℝ K)
    (hK : Bornology.IsBounded K) : μHE[finrank ℝ E - 1] (frontier K) < ∞ := by
  have h := euclideanHausdorffMeasure_frontier_mul_le_volume_cthickening_sdiff hKc.closure
    hK.isCompact_closure 1
  rw [ENNReal.ofReal_one, mul_one, hKc.frontier_closure] at h
  exact h.trans_lt
    ((measure_mono sdiff_subset).trans_lt hK.isCompact_closure.cthickening.measure_lt_top)

/-- The case of `Convex.hasDerivWithinAt_volume_real_add_smul_closedBall` for a compact convex
set `K`. -/
private theorem hasDerivWithinAt_volume_real_add_smul_closedBall_of_isCompact {K : Set E}
    (hKc : Convex ℝ K) (hK : IsCompact K) (hKi : (interior K).Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K + t • closedBall (0 : E) 1))
      (μHE[finrank ℝ E - 1] (frontier K)).toReal (Ici 0) 0 := by
  obtain ⟨x₀, hx₀⟩ := hKi
  obtain ⟨ρ, hρ, hρK⟩ := nhds_basis_closedBall.mem_iff.1 (mem_interior_iff_mem_nhds.1 hx₀)
  set A := μHE[finrank ℝ E - 1] (frontier K)
  set C : ℝ → ℝ := fun t => ((ρ + t) / ρ) ^ (finrank ℝ E - 1)
  have hA : A ≠ ∞ := (hKc.euclideanHausdorffMeasure_frontier_lt_top hK.isBounded).ne
  -- The parallel volume exceeds `|K|` by the volume of the shell `cthickening t K \ K`.
  have hV (t : ℝ) (ht : 0 ≤ t) : volume.real (K + t • closedBall (0 : E) 1) =
      volume.real K + volume.real (cthickening t K \ K) := by
    rw [hK.add_smul_closedBall_eq_cthickening ht, measureReal_sdiff (self_subset_cthickening K)
      hK.isClosed.measurableSet hK.cthickening.measure_lt_top.ne]
    ring
  -- The shell bounds squeeze the difference quotients of the parallel volume at `0`.
  have hslope : ∀ t ∈ Ioi (0 : ℝ), A.toReal ≤ slope (fun t : ℝ =>
      volume.real (K + t • closedBall (0 : E) 1)) 0 t ∧ slope (fun t : ℝ =>
      volume.real (K + t • closedBall (0 : E) 1)) 0 t ≤ C t * A.toReal := by
    intro t (ht : 0 < t)
    have hfin : volume (cthickening t K \ K) ≠ ∞ :=
      ((measure_mono sdiff_subset).trans_lt hK.cthickening.measure_lt_top).ne
    have hlow := ENNReal.toReal_mono hfin
      (euclideanHausdorffMeasure_frontier_mul_le_volume_cthickening_sdiff hKc hK t)
    have hup := ENNReal.toReal_mono (by finiteness) (volume_cthickening_sdiff_le hKc hK hρ hρK t)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le] at hlow
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le,
      ENNReal.toReal_ofReal (by positivity)] at hup
    have hslope_eq : slope (fun t : ℝ => volume.real (K + t • closedBall (0 : E) 1)) 0 t =
        volume.real (cthickening t K \ K) / t := by
      rw [slope_def_field, hV t ht.le, hV 0 le_rfl]
      simp [hK.isClosed.closure_eq]
    rw [hslope_eq, le_div_iff₀ ht, div_le_iff₀ ht]
    exact ⟨hlow, hup⟩
  have hC : Tendsto (fun t => C t * A.toReal) (𝓝[>] 0) (𝓝 A.toReal) := by
    have hcont : ContinuousAt (fun t => C t * A.toReal) 0 := by
      simp only [C]
      fun_prop (disch := exact hρ.ne')
    simpa [C, hρ.ne'] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
    (eventually_nhdsWithin_of_forall fun t ht => (hslope t ht).1)
    (eventually_nhdsWithin_of_forall fun t ht => (hslope t ht).2)

/-- **The first variation of the parallel volume of a convex body is its surface area.** A bounded
convex set `K` with nonempty interior has outer parallel volume `t ↦ |K + t • closedBall 0 1|` with
right derivative `Hⁿ⁻¹(frontier K)` at `t = 0`, where `Hⁿ⁻¹ = μHE[n - 1]` is the normalized
Euclidean Hausdorff measure. The interior hypothesis cannot be dropped: for a segment in the plane
the right derivative is twice its length. -/
theorem _root_.Convex.hasDerivWithinAt_volume_real_add_smul_closedBall {K : Set E}
    (hKc : Convex ℝ K) (hK : Bornology.IsBounded K) (hKi : (interior K).Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K + t • closedBall (0 : E) 1))
      (μHE[finrank ℝ E - 1] (frontier K)).toReal (Ici 0) 0 := by
  -- The parallel sets of `K` and of its closure differ by subsets of null frontiers.
  have hV (t : ℝ) : volume (K + t • closedBall (0 : E) 1) =
      volume (closure K + t • closedBall (0 : E) 1) := by
    have hS : Convex ℝ (K + t • closedBall (0 : E) 1) :=
      hKc.add ((convex_closedBall 0 1).smul t)
    refine le_antisymm (measure_mono (add_subset_add_right subset_closure)) ?_
    rw [← measure_closure_of_null_frontier (hS.addHaar_frontier volume)]
    refine measure_mono ?_
    rintro _ ⟨k, hk, b, hb, rfl⟩
    exact map_mem_closure₂ continuous_add hk (subset_closure hb) fun _ ha _ hb => add_mem_add ha hb
  rw [← hKc.frontier_closure]
  simp only [measureReal_def, hV]
  exact hasDerivWithinAt_volume_real_add_smul_closedBall_of_isCompact hKc.closure
    hK.isCompact_closure (hKi.mono (interior_mono subset_closure))

end TauCeti
