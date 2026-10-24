/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.LocallyFlat.Concordance.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
public import TauCeti.KnotTheory.Slice.Basic

/-!
# Knots concordant to the unknot are slice

A knot is slice when it bounds a disc in the four-ball, and two knots are concordant when they
cobound an annulus in `S³ × [0, 1]`. The two notions are tied together by the observation that a
knot concordant to the unknot is slice: glue the flat disc bounded by the unknot onto the
concordance annulus. This is one half of the statement that the slice knots form the identity
class of the knot concordance group.

This file proves it for topological concordance and topological sliceness: a smooth circle
embedding `K : S¹ → Sⁿ` in the unit sphere of an `(n + 1)`-dimensional real inner product space
`E`, topologically concordant (`TauCeti.TopologicallyConcordant`) to a great circle `ι S¹`, bounds a
locally flat disc in the closed unit ball (`TauCeti.IsTopologicallySlice`). The concordance may use
any real normed model spaces of the right dimensions, `1` for the circle and `n - 1` for its normal
directions.

The disc is built in polar coordinates. A topological concordance is a locally flat collared track
`Φ : S¹ × ℝ → Sⁿ × ℝ`: it is the product of the great circle with the identity for times `t ≤ 0`,
and the product of `K` with the identity for times close to `1` and beyond. Reading the time `t` as
the radius `exp (t - 1)` on both sides turns the track into a map from the punctured plane to the
complement of the origin in `E`. Over the punctured unit disc it lands in the punctured unit ball,
it meets the unit sphere exactly over the unit circle, and near the origin it is the linear map
`ι`; filling in the origin gives the disc. It is locally flat for a different reason in each of
three regions:

* near the centre it is the flat disc `ι D²`, which is locally flat
  (`TauCeti.isTopologicalSliceDisc_greatCircle_unitClosedBallMap`);
* over the open punctured disc it is the track read in polar coordinates, locally flat with
  tangential model the plane, which embeds openly in the half-plane
  (`TauCeti.IsLocallyFlat.transIsOpenEmbedding`);
* near the boundary circle it is the cone `r • K u` over `K`. In the radial collar
  `(u, s) ↦ exp (-s) • u` of the boundary sphere of the ball, modelled on the half-line
  `EuclideanHalfSpace 1`, the cone is the product of `K` with the identity of the half-line, and
  `K` is locally flat in the sphere because it is smooth
  (`TauCeti.IsLocallyFlat.of_isSmoothEmbedding_of_sub_eq`). So the disc is flat up to the boundary
  sphere.

The converse, that a topologically slice knot is topologically concordant to the unknot, needs a
ball about an interior point of the slice disc whose complement is a product, and is not proved
here.

## Main results

* `TauCeti.TopologicallyConcordant.isTopologicallySlice`: a knot topologically concordant to a
  great circle is topologically slice.
* `TauCeti.isTopologicallySlice_of_topologicallyConcordant_unknot`: a knot in `S³` topologically
  concordant to the unknot is topologically slice.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  slice knots and knot cobordism (concordance).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for the concordance group and its identity class.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Topology Module
open scoped EuclideanSpace Manifold

/-! ### Radial coordinates -/

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Polar coordinates on the complement of the origin, with time `t` on the sphere of radius
`exp (t - 1)`: time `1` is the unit sphere, and the times `t ≤ 1` fill the punctured closed unit
ball. -/
private def polar (q : sphere (0 : V) 1 × ℝ) : V :=
  Real.exp (q.2 - 1) • (q.1 : V)

private theorem polar_apply (q : sphere (0 : V) 1 × ℝ) :
    polar q = Real.exp (q.2 - 1) • (q.1 : V) :=
  (rfl)

private theorem norm_polar (q : sphere (0 : V) 1 × ℝ) : ‖polar q‖ = Real.exp (q.2 - 1) := by
  rw [polar_apply, norm_smul, norm_eq_of_mem_sphere q.1, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

private theorem polar_ne_zero (q : sphere (0 : V) 1 × ℝ) : polar q ≠ 0 := by
  rw [← norm_pos_iff, norm_polar]
  exact Real.exp_pos _

private theorem isOpenEmbedding_polar : IsOpenEmbedding (polar (V := V)) :=
  (Real.isOpenEmbedding_exp.comp (Homeomorph.subRight (1 : ℝ)).isOpenEmbedding).smul_coe_sphere
    fun _ => Real.exp_pos _

private theorem mem_range_polar {v : V} (hv : v ≠ 0) : v ∈ range (polar (V := V)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨(⟨‖v‖⁻¹ • v, by simp [norm_smul, hv'.ne']⟩, 1 + Real.log ‖v‖), ?_⟩
  simp [polar_apply, Real.exp_log hv', smul_smul, hv'.ne']

/-- The radial collar of the boundary sphere of the closed unit ball, parametrized by the
half-line model `EuclideanHalfSpace 1`: the point at normal coordinate `s ≥ 0` above `u` is
`exp (-s) • u`. -/
private def ballCollar (q : sphere (0 : V) 1 × EuclideanHalfSpace 1) : closedBall (0 : V) 1 :=
  ⟨Real.exp (-q.2.1 0) • (q.1 : V), by
    rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere q.1, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 q.2.2)⟩

private theorem coe_ballCollar (q : sphere (0 : V) 1 × EuclideanHalfSpace 1) :
    (ballCollar q : V) = Real.exp (-q.2.1 0) • (q.1 : V) :=
  (rfl)

private theorem range_ballCollar :
    range (ballCollar (V := V)) = {y : closedBall (0 : V) 1 | (y : V) ≠ 0} := by
  ext y
  refine ⟨?_, fun hy => ?_⟩
  · rintro ⟨q, rfl⟩
    rw [mem_ofPred_eq, coe_ballCollar]
    exact smul_ne_zero (Real.exp_pos _).ne' (ne_zero_of_mem_unit_sphere q.1)
  have hy' : 0 < ‖(y : V)‖ := norm_pos_iff.2 hy
  have hlog : Real.log ‖(y : V)‖ ≤ 0 :=
    Real.log_nonpos (norm_nonneg _) (mem_closedBall_zero_iff.1 y.2)
  refine ⟨(⟨‖(y : V)‖⁻¹ • (y : V), by simp [norm_smul, hy'.ne']⟩,
    EuclideanHalfSpace.normalRay (-Real.log ‖(y : V)‖)), Subtype.ext ?_⟩
  rw [coe_ballCollar, EuclideanHalfSpace.normalRay_coe_apply, max_eq_left (neg_nonneg.2 hlog),
    neg_neg, Real.exp_log hy']
  simp [smul_smul, hy'.ne']

private theorem isOpenEmbedding_ballCollar : IsOpenEmbedding (ballCollar (V := V)) := by
  -- Read in `V`, the collar is the open embedding `(u, r) ↦ exp r • u` after the embedding
  -- `s ↦ -s` of the half-line into the real line.
  have hcoord : IsEmbedding fun s : EuclideanHalfSpace 1 => -s.1 0 :=
    Function.LeftInverse.isEmbedding (f := fun r : ℝ => EuclideanHalfSpace.normalRay (-r))
      (fun s => by simp) (EuclideanHalfSpace.continuous_normalRay.comp continuous_neg)
      (by fun_prop)
  have hexp : IsEmbedding fun q : sphere (0 : V) 1 × ℝ => Real.exp q.2 • (q.1 : V) :=
    (Real.isOpenEmbedding_exp.smul_coe_sphere Real.exp_pos).isEmbedding
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.1 (hexp.comp (IsEmbedding.id.prodMap hcoord)), ?_⟩
  rw [range_ballCollar]
  exact isOpen_ne_fun continuous_subtype_val continuous_const

omit [NormedSpace ℝ V] in
/-- An open subset of the closed unit ball avoiding the unit sphere is an open subset of the
ambient space. -/
private theorem isOpenEmbedding_coe_coe {U : Set (closedBall (0 : V) 1)} (hU : IsOpen U)
    (h : ∀ z ∈ U, ‖(z : V)‖ < 1) :
    IsOpenEmbedding fun z : U => ((z : closedBall (0 : V) 1) : V) := by
  refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hU
  have hrange : range (fun z : (Subtype.val ⁻¹' O : Set (closedBall (0 : V) 1)) =>
      ((z : closedBall (0 : V) 1) : V)) = O ∩ ball 0 1 := by
    ext v
    refine ⟨?_, fun hv => ⟨⟨⟨v, ball_subset_closedBall hv.2⟩, hv.1⟩, rfl⟩⟩
    rintro ⟨z, rfl⟩
    exact ⟨z.2, mem_ball_zero_iff.2 (h z z.2)⟩
  rw [hrange]
  exact hO.inter isOpen_ball

end Radial

/-! ### Capping a collared track -/

section Cap

/-- The polar coordinates `TauCeti.polar` of the punctured plane, read on the standard circle. -/
private def polarC (q : Circle × ℝ) : ℂ :=
  Real.exp (q.2 - 1) • (q.1 : ℂ)

private theorem polarC_apply (q : Circle × ℝ) : polarC q = Real.exp (q.2 - 1) • (q.1 : ℂ) :=
  (rfl)

private theorem norm_polarC (q : Circle × ℝ) : ‖polarC q‖ = Real.exp (q.2 - 1) :=
  norm_polar (V := ℂ) q

private theorem polarC_ne_zero (q : Circle × ℝ) : polarC q ≠ 0 :=
  polar_ne_zero (V := ℂ) q

private theorem isOpenEmbedding_polarC : IsOpenEmbedding polarC :=
  isOpenEmbedding_polar (V := ℂ)

private theorem mem_range_polarC {z : ℂ} (hz : z ≠ 0) : z ∈ range polarC :=
  mem_range_polar hz

/-- The radial collar `TauCeti.ballCollar` of the boundary circle of the closed unit disc, read on
the standard circle. -/
private def ballCollarC (q : Circle × EuclideanHalfSpace 1) : closedBall (0 : ℂ) 1 :=
  ballCollar (V := ℂ) q

private theorem coe_ballCollarC (q : Circle × EuclideanHalfSpace 1) :
    (ballCollarC q : ℂ) = polarC (q.1, 1 - q.2.1 0) := by
  rw [polarC_apply, sub_sub_cancel_left]
  -- `ballCollarC` is `ballCollar` read on the circle; `coe_ballCollar` cannot be rewritten with
  -- here because its argument lives on the sphere of `ℂ`, which is `Circle` only up to unfolding.
  exact coe_ballCollar (V := ℂ) q

private theorem isOpenEmbedding_ballCollarC : IsOpenEmbedding ballCollarC :=
  isOpenEmbedding_ballCollar (V := ℂ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Classical in
/-- The cone on a track `Φ : S¹ × ℝ → S × ℝ`, read in polar coordinates on both sides: the point
`polarC q` of the plane goes to `polar (Φ q)`, and the origin to the origin. -/
private def capMap (Φ : Circle × ℝ → sphere (0 : E) 1 × ℝ) (z : ℂ) : E :=
  if h : z ∈ range polarC then
    polar (Φ (isOpenEmbedding_polarC.isEmbedding.toHomeomorph.symm ⟨z, h⟩))
  else 0

variable {Φ : Circle × ℝ → sphere (0 : E) 1 × ℝ}

private theorem capMap_coe (z : range polarC) :
    capMap Φ z = polar (Φ (isOpenEmbedding_polarC.isEmbedding.toHomeomorph.symm z)) := by
  rw [capMap, dite_eq_left z.2]

private theorem capMap_polarC (q : Circle × ℝ) : capMap Φ (polarC q) = polar (Φ q) := by
  rw [capMap, dite_eq_left (mem_range_self q), IsEmbedding.toHomeomorph_symm_apply]

private theorem capMap_zero : capMap Φ 0 = 0 := by
  rw [capMap, dite_eq_right]
  rintro ⟨q, hq⟩
  exact polarC_ne_zero q hq

/-- The cone on an injective track is injective. -/
private theorem capMap_injective (hΦ : Function.Injective Φ) : Function.Injective (capMap Φ) := by
  intro z z' h
  rcases eq_or_ne z 0 with rfl | hz <;> rcases eq_or_ne z' 0 with rfl | hz'
  · rfl
  · obtain ⟨q', rfl⟩ := mem_range_polarC hz'
    rw [capMap_zero, capMap_polarC] at h
    exact absurd h.symm (polar_ne_zero _)
  · obtain ⟨q, rfl⟩ := mem_range_polarC hz
    rw [capMap_zero, capMap_polarC] at h
    exact absurd h (polar_ne_zero _)
  · obtain ⟨q, rfl⟩ := mem_range_polarC hz
    obtain ⟨q', rfl⟩ := mem_range_polarC hz'
    rw [capMap_polarC, capMap_polarC] at h
    rw [hΦ (isOpenEmbedding_polar.injective h)]

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}
  {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- A collared track stays below time `1` exactly below time `1`. -/
private theorem snd_le_one_iff
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) (x : Circle) (t : ℝ) :
    (Φ (x, t)).2 ≤ 1 ↔ t ≤ 1 := by
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  simpa only [not_lt] using (hΦ.lt_snd_apply_iff x (t := t) h1).not

/-- A collared track reaches time `1` exactly at time `1`. -/
private theorem snd_eq_one_iff
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) (x : Circle) (t : ℝ) :
    (Φ (x, t)).2 = 1 ↔ t = 1 := by
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  refine ⟨fun h => ?_, by rintro rfl; rw [hΦ.apply_one]⟩
  rcases lt_trichotomy t 1 with ht | ht | ht
  · linarith [(hΦ.snd_apply_lt_iff x h1).2 ht]
  · exact ht
  · linarith [(hΦ.lt_snd_apply_iff x h1).2 ht]

/-- Near the origin the cone on a track starting at the great circle `ι S¹` is the flat disc
`ι D²`: the track is the product of the great circle with the identity for times `t ≤ 0`. -/
private theorem capMap_eq_of_norm_le
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-1)) : capMap Φ z = ι z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [capMap_zero, map_zero]
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC hz0
  have ht : t ≤ 0 := by
    rw [norm_polarC, Real.exp_le_exp] at hz
    linarith
  rw [capMap_polarC, hΦ.apply_of_nonpos x ht, polar_apply, polarC_apply,
    SmoothCircleEmbedding.coe_greatCircle_apply, LinearIsometry.map_smul]

/-- The cone on a collared track stays in the closed unit ball over the closed unit disc. -/
private theorem norm_capMap_le_one
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : ‖capMap Φ z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [capMap_zero]
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC hz0
  rw [norm_polarC, Real.exp_le_one_iff, sub_nonpos] at hz
  rw [capMap_polarC, norm_polar, Real.exp_le_one_iff, sub_nonpos, snd_le_one_iff hΦ]
  exact hz

/-- The cone on a collared track meets the unit sphere exactly over the unit circle. -/
private theorem norm_capMap_eq_one_iff
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) (z : ℂ) :
    ‖capMap Φ z‖ = 1 ↔ ‖z‖ = 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [capMap_zero]
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC hz0
  rw [capMap_polarC, norm_polar, norm_polarC, Real.exp_eq_one_iff, Real.exp_eq_one_iff,
    sub_eq_zero, sub_eq_zero, snd_eq_one_iff hΦ]

/-- The cone on a collared track, restricted to the closed unit disc. -/
private def capDisc (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    (z : closedBall (0 : ℂ) 1) : closedBall (0 : E) 1 :=
  ⟨capMap Φ z, mem_closedBall_zero_iff.2 (norm_capMap_le_one hΦ (mem_closedBall_zero_iff.1 z.2))⟩

private theorem coe_capDisc
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    (z : closedBall (0 : ℂ) 1) : (capDisc hΦ z : E) = capMap Φ z :=
  (rfl)

end Cap

/-! ### Local flatness of the capped disc -/

section LocallyFlat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E} {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  {Φ : Circle × ℝ → sphere (0 : E) 1 × ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Near the origin the capped disc is the flat disc `ι D²`, which is locally flat. -/
private theorem isLocallyFlat_capDisc_comp_coe_of_lt
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) :
    IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
      (capDisc hΦ ∘ ((↑) : {z : closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < Real.exp (-1)} → _)) := by
  have hU : IsOpen {z : closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < Real.exp (-1)} :=
    isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  convert (isTopologicalSliceDisc_greatCircle_unitClosedBallMap (n := n) ι).isLocallyFlat.restrict
    hU using 1
  funext z
  exact Subtype.ext ((capMap_eq_of_norm_le hΦ z.2.le).trans
    (ι.coe_unitClosedBallMap_apply _).symm)

/-- Away from the origin and from the boundary circle the capped disc is the track read in polar
coordinates, hence locally flat; its tangential model `F × ℝ ≅ ℝ²` sits openly in the
half-plane. -/
private theorem isLocallyFlat_capDisc_comp_coe_of_pos_of_lt (hF : finrank ℝ F = 1)
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    (hΦ' : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1))) Φ) :
    IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
      (capDisc hΦ ∘
        ((↑) : {z : closedBall (0 : ℂ) 1 | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1} → _)) := by
  set U := {z : closedBall (0 : ℂ) 1 | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1}
  set B := {y : closedBall (0 : E) 1 | ‖(y : E)‖ < 1}
  have hcont : Continuous fun z : closedBall (0 : ℂ) 1 => ‖(z : ℂ)‖ := by fun_prop
  have hU : IsOpen U := (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hB : IsOpen B := isOpen_lt (by fun_prop) continuous_const
  have hmem (z : U) : capDisc hΦ z ∈ B := by
    have h1 := norm_capMap_le_one hΦ (mem_closedBall_zero_iff.1 z.1.2)
    have h2 := (norm_capMap_eq_one_iff hΦ (z : ℂ)).not.2 z.2.2.ne
    exact lt_of_le_of_ne h1 h2
  -- The track in polar coordinates, on the range of the polar coordinates of the plane.
  have h1 := (hΦ'.isOpenEmbedding_comp isOpenEmbedding_polar).comp_homeomorph
    isOpenEmbedding_polarC.isEmbedding.toHomeomorph.symm
  have hj : IsOpenEmbedding fun z : U =>
      (⟨((z : closedBall (0 : ℂ) 1) : ℂ), mem_range_polarC (norm_pos_iff.1 z.2.1)⟩ :
        range polarC) :=
    (IsOpenEmbedding.of_comp_iff _ isOpenEmbedding_polarC.isOpen_range.isOpenEmbedding_subtypeVal).1
      (isOpenEmbedding_coe_coe hU fun z hz => hz.2)
  have h2 : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1)))
      fun z : U => (⟨capDisc hΦ z, hmem z⟩ : B) := by
    refine IsLocallyFlat.of_isOpenEmbedding_comp (isOpenEmbedding_coe_coe hB fun y hy => hy) ?_
    convert h1.comp_isOpenEmbedding hj using 1
    funext z
    simp only [Function.comp_apply, coe_capDisc]
    exact capMap_coe (Φ := Φ) ⟨_, mem_range_polarC (norm_pos_iff.1 z.2.1)⟩
  -- The tangential model `F × ℝ ≅ ℝ²` of the track embeds openly in the half-plane.
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  let L : (F × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (1 + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hF])
  exact (h2.isOpenEmbedding_comp hB.isOpenEmbedding_subtypeVal).transIsOpenEmbedding
    ((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding 1).comp L.toHomeomorph.isOpenEmbedding)

/-- Near the boundary circle the capped disc is the cone `r • K u` over the knot, which is locally
flat up to the boundary sphere: in the radial collar of the ball it is the product of `K`, locally
flat in the sphere, with the identity of the half-line. -/
private theorem exists_isLocallyFlat_capDisc_comp_coe_of_norm_eq_one
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    {x : closedBall (0 : ℂ) 1} (hx : ‖(x : ℂ)‖ = 1) :
    ∃ U : Set (closedBall (0 : ℂ) 1), IsOpen U ∧ x ∈ U ∧
      IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
        (capDisc hΦ ∘ ((↑) : U → _)) := by
  obtain ⟨ε, hε, hεΦ⟩ := hΦ.exists_pos_apply_eq_right
  have hK : IsLocallyFlat (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin (n - 1))) K :=
    IsLocallyFlat.of_isSmoothEmbedding_of_sub_eq K.isSmoothEmbedding rfl
  have h1 := (hK.prodMap_of_isOpenEmbedding (G := EuclideanHalfSpace 1)
    (IsOpenEmbedding.id (X := EuclideanHalfSpace 1))).isOpenEmbedding_comp
    (isOpenEmbedding_ballCollar (V := E))
  set W := {q : Circle × EuclideanHalfSpace 1 | q.2.1 0 < ε}
  have hW : IsOpen W := isOpen_lt (by fun_prop) continuous_const
  have hc : IsOpenEmbedding fun q : W => ballCollarC q :=
    isOpenEmbedding_ballCollarC.comp hW.isOpenEmbedding_subtypeVal
  -- Over the collar `W` the capped disc is the cone over `K`.
  have hcap : (capDisc hΦ ∘ fun q : W => ballCollarC q) =
      ballCollar ∘ Prod.map K id ∘ ((↑) : W → _) := by
    funext ⟨⟨w, s⟩, hs⟩
    refine Subtype.ext ?_
    simp only [Function.comp_apply, coe_capDisc, coe_ballCollarC, capMap_polarC, Prod.map_apply,
      id_eq, coe_ballCollar, polar_apply]
    rw [hεΦ w _ (by have : s.1 0 < ε := hs; linarith), sub_sub_cancel_left]
  refine ⟨range fun q : W => ballCollarC q, hc.isOpen_range, ⟨⟨(⟨x, ?_⟩, 0), ?_⟩, ?_⟩, ?_⟩
  · exact mem_sphere_zero_iff_norm.2 hx
  · simpa [W] using hε
  · refine Subtype.ext ?_
    simp [coe_ballCollarC, polarC_apply]
  have h2 := (hcap ▸ h1.restrict hW).comp_homeomorph hc.isEmbedding.toHomeomorph.symm
  convert h2.transIsOpenEmbedding
    (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) 1).toHomeomorph.isOpenEmbedding using 1
  funext u
  simp only [Function.comp_apply]
  congr
  exact (congrArg Subtype.val (hc.isEmbedding.toHomeomorph.apply_symm_apply u)).symm

/-- Every point of the closed unit disc has an open neighbourhood on which the capped disc is
locally flat, with tangential model the half-plane. -/
private theorem exists_isLocallyFlat_capDisc_comp_coe (hF : finrank ℝ F = 1)
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    (hΦ' : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1))) Φ)
    (x : closedBall (0 : ℂ) 1) :
    ∃ U : Set (closedBall (0 : ℂ) 1), IsOpen U ∧ x ∈ U ∧
      IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
        (capDisc hΦ ∘ ((↑) : U → _)) := by
  have hcont : Continuous fun z : closedBall (0 : ℂ) 1 => ‖(z : ℂ)‖ := by fun_prop
  by_cases h0 : ‖(x : ℂ)‖ < Real.exp (-1)
  · exact ⟨_, isOpen_lt hcont continuous_const, h0, isLocallyFlat_capDisc_comp_coe_of_lt hΦ⟩
  by_cases h1 : ‖(x : ℂ)‖ < 1
  · exact ⟨_, (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const),
      ⟨(Real.exp_pos _).trans_le (not_lt.1 h0), h1⟩,
      isLocallyFlat_capDisc_comp_coe_of_pos_of_lt hF hΦ hΦ'⟩
  exact exists_isLocallyFlat_capDisc_comp_coe_of_norm_eq_one hΦ
    (le_antisymm (mem_closedBall_zero_iff.1 x.2) (not_lt.1 h1))

/-- **Capping a track from a great circle.** If `Φ` is a locally flat collared track from the
great circle `ι S¹` to `K`, then the cone on it, read in polar coordinates and filled in by the flat
disc `ι D²` near the centre, is a locally flat slice disc for `K`. -/
private theorem isTopologicalSliceDisc_capDisc (hF : finrank ℝ F = 1)
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    (hΦ' : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1))) Φ) :
    IsTopologicalSliceDisc K (capDisc hΦ) := by
  have hloc := exists_isLocallyFlat_capDisc_comp_coe hF hΦ hΦ'
  have hcont : Continuous (capDisc hΦ) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨U, hU, hxU, hflat⟩ := hloc x
    exact (continuousOn_iff_continuous_domRestrict.2 hflat.continuous).continuousAt
      (hU.mem_nhds hxU)
  have hinj : Function.Injective (capDisc hΦ) := fun z z' h =>
    Subtype.ext (capMap_injective hΦ'.injective (congrArg Subtype.val h))
  have : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  refine ⟨.of_forall_exists_isOpen (hcont.isClosedEmbedding hinj).isEmbedding hloc,
    fun x => norm_capMap_eq_one_iff hΦ x, fun z => ?_⟩
  have hz : ((Set.inclusion sphere_subset_closedBall z : closedBall (0 : ℂ) 1) : ℂ) =
      polarC (z, 1) := by
    simp [polarC_apply]
  rw [coe_capDisc, hz, capMap_polarC, hΦ.apply_one, polar_apply, sub_self, Real.exp_zero,
    one_smul]

end LocallyFlat

/-! ### Knots concordant to the unknot are slice -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']

/-- **A knot topologically concordant to a great circle is topologically slice.** If `K` is
topologically concordant to the great circle `ι S¹` of `Sⁿ`, for real normed model spaces `F` of
the circle and `F'` of its normal directions, of dimensions `1` and `n - 1`, then `K` bounds a
locally flat disc in `Dⁿ⁺¹`: cap the concordance off with the flat disc `ι D²`. -/
theorem TopologicallyConcordant.isTopologicallySlice (hF : finrank ℝ F = 1)
    (hF' : finrank ℝ F' = n - 1) {ι : ℂ →ₗᵢ[ℝ] E}
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h : TopologicallyConcordant F F' (SmoothCircleEmbedding.greatCircle (n := n) ι) K) :
    IsTopologicallySlice K := by
  obtain ⟨Φ⟩ := topologicallyConcordant_iff_nonempty.1 h
  let L : F' ≃L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hF'])
  exact (isTopologicalSliceDisc_capDisc hF Φ.isCollaredTrack
    (Φ.isLocallyFlat.transHomeomorph L.toHomeomorph (by simp))).isTopologicallySlice

/-- **A knot in `S³` topologically concordant to the unknot is topologically slice.** -/
theorem isTopologicallySlice_of_topologicallyConcordant_unknot (hF : finrank ℝ F = 1)
    (hF' : finrank ℝ F' = 2)
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    (h : TopologicallyConcordant F F' unknot K) : IsTopologicallySlice K := by
  rw [unknot_eq_greatCircle] at h
  exact h.isTopologicallySlice hF hF'

end TauCeti
