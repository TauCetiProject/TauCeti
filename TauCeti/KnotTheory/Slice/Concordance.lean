/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Geometry.Manifold.Boundary.Collar.ClosedBall
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.LocallyFlat.Ball
public import TauCeti.Geometry.Manifold.LocallyFlat.Concordance.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.Slice.Basic

import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.Geometry.Manifold.ImmersionDiff
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Topological sliceness is a topological concordance invariant

A knot is slice when it bounds a disc in the four-ball, and two knots are concordant when they
cobound an annulus in `S³ × [0, 1]`. Gluing a slice disc of one knot to a concordance annulus gives
a slice disc of the other knot, so sliceness is constant on concordance classes. In particular a
knot concordant to the unknot is slice, which is one half of the statement that the slice knots form
the identity class of the knot concordance group.

This file proves it for topological concordance and topological sliceness: if a smooth circle
embedding `K₀ : S¹ → Sⁿ` in the unit sphere of an `(n + 1)`-dimensional real inner product space
`E` bounds a locally flat disc in the closed unit ball (`TauCeti.IsTopologicallySlice`), and is
topologically concordant (`TauCeti.TopologicallyConcordant`) to `K`, then `K` bounds one too. The
concordance may use any real normed model spaces of the right dimensions, `1` for the circle and
`n - 1` for its normal directions. Taking for `K₀` a great circle `ι S¹`, which bounds the flat
disc `ι D²`, a knot concordant to a great circle is topologically slice.

The new disc is built in polar coordinates. A topological concordance is a locally flat collared
track `Φ : S¹ × ℝ → Sⁿ × ℝ`: it is the product of `K₀` with the identity for times close to `0` and
below, and the product of `K` with the identity for times close to `1` and beyond. Reading the time
`t` as the radius `exp (t - 1)` on both sides turns the track into a map from the punctured plane to
the complement of the origin in `E`, which over the punctured unit disc lands in the punctured unit
ball and meets the unit sphere exactly over the unit circle. Inside the circle of radius
`exp (-1)` it is replaced by a slice disc `Ψ` of `K₀`, shrunk by the factor `exp (-1)`. The glued
disc is locally flat for a different reason in each of three regions:

* near the seam circle of radius `exp (-1)`, and inside it, it is the shrunk **cone extension** of
  `Ψ`: the map of the plane which is `Ψ` on the unit disc and the cone `r • K₀ u` on the knot for
  `r ≥ 1`. A chart `φ` flattening `Ψ` near a point of the unit sphere sends the sphere into the
  boundary hyperplane of the half-space model, by invariance of domain
  (`OpenPartialHomeomorph.coe_fst_apply_zero_eq_zero_of_notMem_interior`). So it extends past the
  sphere, by `r • v ↦ φ v - log r • e₀` for `r ≥ 1` and `v` on the sphere, to a continuous injection
  of an open subset of `E`, which by invariance of domain again is an open embedding. It carries the
  cone extension onto the coordinate plane, so the cone extension is locally flat;
* over the open annulus between the seam and the unit circle it is the track read in polar
  coordinates, locally flat with tangential model the plane, which embeds openly in the half-plane
  (`TauCeti.IsLocallyFlat.transIsOpenEmbedding`);
* near the boundary circle it is the cone `r • K u` over `K`. In the radial collar
  `(u, s) ↦ exp (-s) • u` of the boundary sphere of the ball, modelled on the half-line
  `EuclideanHalfSpace 1`, the cone is the product of `K` with the identity of the half-line, and
  `K` is locally flat in the sphere because it is smooth
  (`TauCeti.IsLocallyFlat.of_isSmoothEmbedding_of_sub_eq`). So the disc is flat up to the boundary
  sphere.

The converse of the great-circle case, that a topologically slice knot is topologically concordant
to the unknot, needs a ball about an interior point of the slice disc whose complement is a
product, and is not proved here.

For a smooth concordance (`TauCeti.SmoothEmbedding.Concordance`) from a great circle to `K`, the
same cone is a smooth embedding of the whole plane into `E`
(`TauCeti.SmoothEmbedding.Concordance.exists_isSmoothEmbedding_cap`). Near the origin it is the
linear isometry `ι`. Away from the origin, precomposing it with exponential polar coordinates of
the plane, a local diffeomorphism, gives the track followed by exponential polar coordinates of
`E`, another local diffeomorphism (`TauCeti.isLocalDiffeomorph_polar`); so it is smooth with
injective differential there. It preserves the norm outside the unit disc, so it is proper, hence
a closed embedding. Near the unit circle and beyond it is the cone `s • K u` over `K`. That its
restriction to the closed unit disc is a smooth embedding of manifolds with boundary, which would
make `K` smoothly slice, needs smooth charts of the closed ball at the boundary sphere and is not
proved here.

## Main results

* `TauCeti.IsTopologicallySlice.of_topologicallyConcordant`: a knot topologically concordant to a
  topologically slice knot is topologically slice.
* `TauCeti.TopologicallyConcordant.isTopologicallySlice_iff`: topologically concordant knots are
  topologically slice together.
* `TauCeti.TopologicallyConcordant.isTopologicallySlice`: a knot topologically concordant to a
  great circle is topologically slice.
* `TauCeti.isTopologicallySlice_of_topologicallyConcordant_unknot`: a knot in `S³` topologically
  concordant to the unknot is topologically slice.
* `TauCeti.SmoothEmbedding.Concordance.exists_isSmoothEmbedding_cap`: the cap of a smooth
  concordance from a great circle to `K` is a smooth embedding of the plane, equal to `ι` near the
  origin and to the cone over `K` near the unit circle and beyond.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  slice knots and knot cobordism (concordance).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for the concordance group and its identity class.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2B.3, for invariance
  of domain.
-/

public section

noncomputable section

open Metric Set Topology Module Manifold
open scoped EuclideanSpace Manifold ContDiff

namespace TauCeti

/-! ### Capping a collared track -/

section Cap

/-- The polar coordinates `TauCeti.polar` of the punctured plane, read on the standard circle.
The `Circle`-typed adapters below let `rw` match without unfolding `Circle` to the complex sphere
at its restricted transparency level. Their proofs reuse the generic radial-coordinate API. -/
private def polarC (q : Circle × ℝ) : ℂ :=
  polar (V := ℂ) q

private theorem polarC_apply (q : Circle × ℝ) : polarC q = Real.exp (q.2 - 1) • (q.1 : ℂ) :=
  polar_apply (V := ℂ) q

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

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]
  {K₀ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- A collared track stays below time `1` exactly below time `1`. -/
private theorem snd_le_one_iff (hΦ : IsCollaredTrack K₀ K Φ) (x : Circle) (t : ℝ) :
    (Φ (x, t)).2 ≤ 1 ↔ t ≤ 1 := by
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  simpa only [not_lt] using (hΦ.lt_snd_apply_iff x (t := t) h1).not

/-- A collared track reaches time `1` exactly at time `1`. -/
private theorem snd_eq_one_iff (hΦ : IsCollaredTrack K₀ K Φ) (x : Circle) (t : ℝ) :
    (Φ (x, t)).2 = 1 ↔ t = 1 := by
  have h1 : (1 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.2
  refine ⟨fun h => ?_, by rintro rfl; rw [hΦ.apply_one]⟩
  rcases lt_trichotomy t 1 with ht | ht | ht
  · linarith [(hΦ.snd_apply_lt_iff x h1).2 ht]
  · exact ht
  · linarith [(hΦ.lt_snd_apply_iff x h1).2 ht]

/-- The cone on a collared track meets the closed unit ball exactly over the closed unit disc. -/
private theorem norm_capMap_le_one_iff (hΦ : IsCollaredTrack K₀ K Φ) (z : ℂ) :
    ‖capMap Φ z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [capMap_zero]
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC hz0
  rw [capMap_polarC, norm_polar, norm_polarC, Real.exp_le_one_iff, Real.exp_le_one_iff, sub_nonpos,
    sub_nonpos, snd_le_one_iff hΦ]

/-- The cone on a collared track meets the unit sphere exactly over the unit circle. -/
private theorem norm_capMap_eq_one_iff (hΦ : IsCollaredTrack K₀ K Φ) (z : ℂ) :
    ‖capMap Φ z‖ = 1 ↔ ‖z‖ = 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [capMap_zero]
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC hz0
  rw [capMap_polarC, norm_polar, norm_polarC, Real.exp_eq_one_iff, Real.exp_eq_one_iff,
    sub_eq_zero, sub_eq_zero, snd_eq_one_iff hΦ]

/-- Outside the circle of radius `exp (-1)`, the cone on a collared track stays outside the ball of
radius `exp (-1)`: the track keeps positive times positive. -/
private theorem exp_neg_one_lt_norm_capMap (hΦ : IsCollaredTrack K₀ K Φ) {z : ℂ}
    (hz : Real.exp (-1) < ‖z‖) : Real.exp (-1) < ‖capMap Φ z‖ := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans hz)
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC hz0
  have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h => lt_irrefl _ h.1
  rw [norm_polarC, Real.exp_lt_exp] at hz
  rw [capMap_polarC, norm_polar, Real.exp_lt_exp]
  linarith [(hΦ.lt_snd_apply_iff x h0).2 (by linarith : 0 < t)]

/-- The cone on a collared track, restricted to the closed unit disc. -/
private def capDisc (hΦ : IsCollaredTrack K₀ K Φ) (z : closedBall (0 : ℂ) 1) :
    closedBall (0 : E) 1 :=
  ⟨capMap Φ z,
    mem_closedBall_zero_iff.2 ((norm_capMap_le_one_iff hΦ z).2 (mem_closedBall_zero_iff.1 z.2))⟩

private theorem coe_capDisc (hΦ : IsCollaredTrack K₀ K Φ) (z : closedBall (0 : ℂ) 1) :
    (capDisc hΦ z : E) = capMap Φ z :=
  (rfl)

end Cap

/-! ### Extending a slice disc by the cone on its boundary knot -/

section ConeExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {K₀ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  {Ψ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1}

/-- The extension of a disc `Ψ` by the cone on its boundary: `Ψ` on the closed unit disc, and
`r • Ψ u` at the point `r • u` for `r ≥ 1` and `u` on the unit circle. -/
private def coneExt (Ψ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1) (z : ℂ) : E :=
  max ‖z‖ 1 • (Ψ (radialRetractionToClosedBall zero_le_one z) : E)

private theorem continuous_coneExt (hΨ : Continuous Ψ) : Continuous (coneExt Ψ) :=
  (continuous_norm.max continuous_const).smul
    (continuous_subtype_val.comp (hΨ.comp (continuous_radialRetractionToClosedBall zero_le_one)))

/-- For a slice disc, the cone extension has `max ‖·‖ 1` equal to that of its argument. -/
private theorem max_norm_coneExt (hΨ : IsTopologicalSliceDisc K₀ Ψ) (z : ℂ) :
    max ‖coneExt Ψ z‖ 1 = max ‖z‖ 1 := by
  have hle : ‖(Ψ (radialRetractionToClosedBall zero_le_one z) : E)‖ ≤ 1 :=
    mem_closedBall_zero_iff.1 (Ψ (radialRetractionToClosedBall zero_le_one z)).2
  rcases le_total ‖z‖ 1 with hz | hz
  · rw [coneExt, max_eq_right hz, one_smul, max_eq_right hle]
  · have h1 : ‖(Ψ (radialRetractionToClosedBall zero_le_one z) : E)‖ = 1 :=
      (hΨ.norm_eq_one_iff _).2
        (by rw [norm_radialRetractionToClosedBall zero_le_one, min_eq_right hz])
    rw [coneExt, max_eq_left hz, norm_smul, h1, mul_one, Real.norm_of_nonneg (by linarith),
      max_eq_left hz]

/-- For a slice disc, the cone extension retracts radially onto the disc. -/
private theorem radialRetractionToClosedBall_coneExt (hΨ : IsTopologicalSliceDisc K₀ Ψ) (z : ℂ) :
    radialRetractionToClosedBall zero_le_one (coneExt Ψ z) =
      Ψ (radialRetractionToClosedBall zero_le_one z) := by
  have hpos : 0 < max ‖z‖ 1 := lt_max_of_lt_right one_pos
  have h := max_norm_one_smul_radialRetraction_one (coneExt Ψ z)
  rw [max_norm_coneExt hΨ, coneExt] at h
  rw [← coe_radialRetractionToClosedBall zero_le_one] at h
  exact Subtype.ext (smul_right_injective E hpos.ne' h)

private theorem norm_coneExt_le (hΨ : IsTopologicalSliceDisc K₀ Ψ) (z : ℂ) :
    ‖coneExt Ψ z‖ ≤ max ‖z‖ 1 :=
  (le_max_left _ _).trans (max_norm_coneExt hΨ z).le

private theorem coneExt_injective (hΨ : IsTopologicalSliceDisc K₀ Ψ) :
    Function.Injective (coneExt Ψ) := by
  intro z z' h
  have hr' : radialRetractionToClosedBall zero_le_one z =
      radialRetractionToClosedBall zero_le_one z' :=
    hΨ.isEmbedding.injective (by
      rw [← radialRetractionToClosedBall_coneExt hΨ, h, radialRetractionToClosedBall_coneExt hΨ])
  have hr : radialRetraction (1 : ℝ) z = radialRetraction 1 z' := by
    simpa only [coe_radialRetractionToClosedBall] using congrArg Subtype.val hr'
  have hm : max ‖z‖ 1 = max ‖z'‖ 1 := by
    rw [← max_norm_coneExt hΨ, h, max_norm_coneExt hΨ]
  rw [← max_norm_one_smul_radialRetraction_one z, ← max_norm_one_smul_radialRetraction_one z',
    hr, hm]

/-- For a slice disc, the cone extension is a closed embedding of the plane: it is proper, since
it does not decrease norms outside the unit disc. -/
private theorem isClosedEmbedding_coneExt (hΨ : IsTopologicalSliceDisc K₀ Ψ) :
    IsClosedEmbedding (coneExt Ψ) := by
  have hc := continuous_coneExt hΨ.continuous
  have hproper : IsProperMap (coneExt Ψ) := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hc, fun C hC => ?_⟩
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
    refine (isCompact_closedBall (0 : ℂ) (max R 1)).of_isClosed_subset
      (hC.isClosed.preimage hc) fun z hz => ?_
    have hzR := mem_closedBall_zero_iff.1 (hR hz)
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ ≤ max ‖z‖ 1 := le_max_left _ _
      _ = max ‖coneExt Ψ z‖ 1 := (max_norm_coneExt hΨ z).symm
      _ ≤ max R 1 := max_le_max hzR le_rfl
  exact .of_continuous_injective_isClosedMap hc (coneExt_injective hΨ) hproper.isClosedMap

/-- A space with a locally flat disc in the closed unit ball of `E` has dimension at least `2`: an
open disc of the plane embeds in `E`. -/
private theorem one_le_of_isTopologicalSliceDisc (hΨ : IsTopologicalSliceDisc K₀ Ψ) : 1 ≤ n := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have : Nonempty (ball (0 : ℂ) 1) := ⟨⟨0, mem_ball_self one_pos⟩⟩
  have hle := isOpen_ball.isOpenEmbedding_subtypeVal.finrank_le_of_isEmbedding
    (X := ball (0 : ℂ) 1) (IsEmbedding.subtypeVal.comp
      (hΨ.isEmbedding.comp (IsEmbedding.inclusion ball_subset_closedBall)))
  rw [Complex.finrank_real_complex, (Fact.out : finrank ℝ E = n + 1)] at hle
  omega

/-- Near every point of the plane, the cone extension of a slice disc is locally flat. A
flattening chart `φ` of the ball at the point `Ψ (radialRetractionToClosedBall zero_le_one z)`
sends the sphere into the boundary hyperplane of the half-space
(`OpenPartialHomeomorph.coe_fst_apply_zero_eq_zero_of_notMem_interior`), so it extends past the
sphere by `r • v ↦ φ v - log r • e₀`. By invariance of domain this extension is an open
embedding, and it carries the cone extension to the coordinate plane. -/
private theorem exists_isLocallyFlat_coneExt_comp_coe (hΨ : IsTopologicalSliceDisc K₀ Ψ)
    (z : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
        (coneExt Ψ ∘ ((↑) : U → ℂ)) := by
  set V' := EuclideanSpace ℝ (Fin (n - 1))
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have hn := one_le_of_isTopologicalSliceDisc hΨ
  have hdim : finrank ℝ E = 2 + finrank ℝ V' := by
    rw [finrank_euclideanSpace_fin, (Fact.out : finrank ℝ E = n + 1)]
    omega
  have hdim' : finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin 2) × V') := by
    rw [finrank_prod, finrank_euclideanSpace_fin, hdim]
  obtain ⟨φ, hφz, hφ⟩ :=
    hΨ.isLocallyFlat.exists_isSliceChart (radialRetractionToClosedBall zero_le_one z)
  -- The chart `φ` sends the unit sphere into the boundary hyperplane.
  have hsphere {w : closedBall (0 : E) 1} (hw : w ∈ φ.source) (hw1 : ‖(w : E)‖ = 1) :
      (φ w).1.1 0 = 0 :=
    φ.coe_fst_apply_zero_eq_zero_of_notMem_interior hdim hw (by
      rw [interior_closedBall _ one_ne_zero, mem_ball_zero_iff, hw1]
      exact lt_irrefl 1)
  -- The extended chart `Θ` on the open set `W` of points retracting into the source of `φ`.
  set W : Set E := radialRetractionToClosedBall zero_le_one ⁻¹' φ.source
  have hW : IsOpen W :=
    (continuous_radialRetractionToClosedBall zero_le_one).isOpen_preimage _ φ.open_source
  let Θ : E → EuclideanSpace ℝ (Fin 2) × V' := fun y =>
    ((φ (radialRetractionToClosedBall zero_le_one y)).1.1 -
        Real.log (max ‖y‖ 1) • EuclideanSpace.single 0 1,
      (φ (radialRetractionToClosedBall zero_le_one y)).2)
  have hΘc : ContinuousOn Θ W := by
    have hφr : ContinuousOn (fun y => φ (radialRetractionToClosedBall zero_le_one y)) W :=
      φ.continuousOn.comp (continuous_radialRetractionToClosedBall zero_le_one).continuousOn
        fun _ hy => hy
    have hlog : Continuous fun y : E => Real.log (max ‖y‖ 1) :=
      (continuous_norm.max continuous_const).log fun y =>
        (lt_max_of_lt_right one_pos).ne'
    exact (((continuous_subtype_val.comp_continuousOn (continuous_fst.comp_continuousOn hφr)).sub
      ((hlog.smul continuous_const).continuousOn))).prodMk (continuous_snd.comp_continuousOn hφr)
  -- The zeroth coordinate of `Θ` recovers `log (max ‖y‖ 1)`, so `Θ` is injective on `W`.
  have hlogΘ {y : E} (hy : y ∈ W) : Real.log (max ‖y‖ 1) = max (-(Θ y).1 0) 0 := by
    have hcoord : (Θ y).1 0 =
        (φ (radialRetractionToClosedBall zero_le_one y)).1.1 0 - Real.log (max ‖y‖ 1) := by
      simp [Θ]
    rcases le_or_gt ‖y‖ 1 with hy1 | hy1
    · rw [hcoord, max_eq_right hy1, Real.log_one, sub_zero]
      exact (max_eq_right (neg_nonpos.2 (φ (radialRetractionToClosedBall zero_le_one y)).1.2)).symm
    · have h0 := hsphere hy
        (by rw [norm_radialRetractionToClosedBall zero_le_one, min_eq_right hy1.le])
      have hlogpos : 0 < Real.log ‖y‖ := Real.log_pos hy1
      rw [hcoord, h0, max_eq_left hy1.le, zero_sub, neg_neg, max_eq_left hlogpos.le]
  have hΘinj : InjOn Θ W := by
    intro y hy y' hy' h
    have hlog : Real.log (max ‖y‖ 1) = Real.log (max ‖y'‖ 1) := by
      rw [hlogΘ hy, hlogΘ hy', h]
    have hφeq : φ (radialRetractionToClosedBall zero_le_one y) =
        φ (radialRetractionToClosedBall zero_le_one y') := by
      have h2 : (Θ y).2 = (Θ y').2 := congrArg Prod.snd h
      refine Prod.ext (Subtype.ext ?_) h2
      have h1 := congrArg Prod.fst h
      simp only [Θ, hlog] at h1
      exact sub_left_injective h1
    have hr : radialRetraction (1 : ℝ) y = radialRetraction 1 y' :=
      by simpa only [coe_radialRetractionToClosedBall] using
        congrArg Subtype.val (φ.injOn hy hy' hφeq)
    have hm : max ‖y‖ 1 = max ‖y'‖ 1 :=
      Real.log_injOn_pos (lt_max_of_lt_right one_pos) (lt_max_of_lt_right one_pos) hlog
    rw [← max_norm_one_smul_radialRetraction_one y, ← max_norm_one_smul_radialRetraction_one y',
      hr, hm]
  -- By invariance of domain, `Θ` is an open embedding on `W`.
  have hΘW : IsOpenEmbedding (W.domRestrict Θ) :=
    hW.isOpenEmbedding_domRestrict_of_continuousOn_of_injOn hΘc hΘinj hdim'
  -- On the preimage `U` of `W`, the cone extension is carried by `Θ` into the coordinate plane.
  set U : Set ℂ := coneExt Ψ ⁻¹' W
  have hc := continuous_coneExt hΨ.continuous
  have hU : IsOpen U := hc.isOpen_preimage _ hW
  have hzU : z ∈ U := by
    simp only [U, W, Set.mem_preimage]
    rwa [radialRetractionToClosedBall_coneExt hΨ]
  have hslice {w : ℂ} (hw : w ∈ U) : (Θ (coneExt Ψ w)).2 = 0 := by
    have hw' : Ψ (radialRetractionToClosedBall zero_le_one w) ∈ φ.source := by
      rw [← radialRetractionToClosedBall_coneExt hΨ]
      exact hw
    have := (hφ.mem_iff hw').1 (mem_range_self _)
    simp only [Θ, radialRetractionToClosedBall_coneExt hΨ]
    exact this.2
  let h₀ : ℂ → EuclideanSpace ℝ (Fin 2) := fun w => (Θ (coneExt Ψ w)).1
  have hΘext {w : ℂ} (hw : w ∈ U) : Θ (coneExt Ψ w) = (h₀ w, 0) :=
    Prod.ext rfl (hslice hw)
  have hh₀c : ContinuousOn h₀ U :=
    continuous_fst.comp_continuousOn (hΘc.comp hc.continuousOn fun _ hw => hw)
  have hh₀inj : InjOn h₀ U := by
    intro w hw w' hw' h
    refine coneExt_injective hΨ (hΘinj hw hw' ?_)
    rw [hΘext hw, hΘext hw', h]
  have hh₀ : IsOpenEmbedding (U.domRestrict h₀) :=
    hU.isOpenEmbedding_domRestrict_of_continuousOn_of_injOn (E := ℂ)
      (F := EuclideanSpace ℝ (Fin 2)) hh₀c hh₀inj (by simp [Complex.finrank_real_complex])
  -- Assemble: the coordinate plane is locally flat, and `Θ` pulls it back to the cone extension.
  have h1 : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) V'
      ((fun x : EuclideanSpace ℝ (Fin 2) => (x, (0 : V'))) ∘ U.domRestrict h₀) :=
    isLocallyFlat_prodMkLeft.comp_isOpenEmbedding hh₀
  let cW : U → W := fun w => ⟨coneExt Ψ w, w.2⟩
  have hcW : W.domRestrict Θ ∘ cW =
      (fun x : EuclideanSpace ℝ (Fin 2) => (x, (0 : V'))) ∘ U.domRestrict h₀ := by
    funext w
    exact hΘext w.2
  have h2 : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) V' (coneExt Ψ ∘ ((↑) : U → ℂ)) :=
    (IsLocallyFlat.of_isOpenEmbedding_comp hΘW (hcW ▸ h1)).isOpenEmbedding_comp
      hW.isOpenEmbedding_subtypeVal
  exact ⟨U, hU, hzU,
    h2.transIsOpenEmbedding (EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding 1)⟩

/-- **The cone extension of a locally flat slice disc is locally flat.** Extending a locally flat
slice disc `Ψ` of `K₀` beyond the unit circle by the cone `r • K₀ u`, `r ≥ 1`, gives a locally
flat embedding of the plane into `E`. -/
private theorem isLocallyFlat_coneExt (hΨ : IsTopologicalSliceDisc K₀ Ψ) :
    IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1))) (coneExt Ψ) :=
  .of_forall_exists_isOpen (isClosedEmbedding_coneExt hΨ).isEmbedding
    (exists_isLocallyFlat_coneExt_comp_coe hΨ)

end ConeExtension

/-! ### Local flatness of the capped disc -/

section LocallyFlat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {K₀ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  {Φ : Circle × ℝ → sphere (0 : E) 1 × ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ψ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1}

/-- On an open subset of the open punctured disc the capped disc is the track read in polar
coordinates, hence locally flat; its tangential model `F × ℝ ≅ ℝ²` sits openly in the
half-plane. -/
private theorem isLocallyFlat_capDisc_comp_coe_of_pos_of_lt (hF : finrank ℝ F = 1)
    (hΦ : IsCollaredTrack K₀ K Φ)
    (hΦ' : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1))) Φ)
    {U : Set (closedBall (0 : ℂ) 1)} (hU : IsOpen U)
    (hU₀ : ∀ z ∈ U, 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1) :
    IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
      (capDisc hΦ ∘ ((↑) : U → _)) := by
  have hmem (z : U) : ‖(capDisc hΦ z : E)‖ < 1 :=
    lt_of_le_of_ne ((norm_capMap_le_one_iff hΦ z).2 (mem_closedBall_zero_iff.1 z.1.2))
      ((norm_capMap_eq_one_iff hΦ (z : ℂ)).not.2 (hU₀ z z.2).2.ne)
  -- The track in polar coordinates, on the range of the polar coordinates of the plane.
  have h1 := (hΦ'.isOpenEmbedding_comp isOpenEmbedding_polar).comp_homeomorph
    isOpenEmbedding_polarC.isEmbedding.toHomeomorph.symm
  have hj : IsOpenEmbedding fun z : U =>
      (⟨((z : closedBall (0 : ℂ) 1) : ℂ), mem_range_polarC (norm_pos_iff.1 (hU₀ z z.2).1)⟩ :
        range polarC) :=
    (IsOpenEmbedding.of_comp_iff _ isOpenEmbedding_polarC.isOpen_range.isOpenEmbedding_subtypeVal).1
      (hU.isOpenEmbedding_coe_openSubset_closedBall fun z hz => (hU₀ z hz).2)
  have h2 : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1)))
      fun z : U => (capDisc hΦ z : E) := by
    convert h1.comp_isOpenEmbedding hj using 1
    funext z
    simp only [Function.comp_apply, coe_capDisc]
    exact capMap_coe (Φ := Φ) ⟨_, mem_range_polarC (norm_pos_iff.1 (hU₀ z z.2).1)⟩
  -- The tangential model `F × ℝ ≅ ℝ²` of the track embeds openly in the half-plane.
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  let L : (F × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (1 + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hF])
  exact IsLocallyFlat.of_coe_closedBall hmem (h2.transIsOpenEmbedding
    ((EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding 1).comp L.toHomeomorph.isOpenEmbedding))

/-- Near the boundary circle the capped disc is the cone `r • K u` over the knot, which is locally
flat up to the boundary sphere: in the radial collar of the ball it is the product of `K`, locally
flat in the sphere, with the identity of the half-line. The neighbourhood can be taken outside the
circle of radius `exp (-1)`. -/
private theorem exists_isLocallyFlat_capDisc_comp_coe_of_norm_eq_one
    (hΦ : IsCollaredTrack K₀ K Φ) {x : closedBall (0 : ℂ) 1} (hx : ‖(x : ℂ)‖ = 1) :
    ∃ U : Set (closedBall (0 : ℂ) 1), IsOpen U ∧ x ∈ U ∧
      (∀ z ∈ U, Real.exp (-1) < ‖(z : ℂ)‖) ∧
      IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
        (capDisc hΦ ∘ ((↑) : U → _)) := by
  obtain ⟨ε₀, hε₀, hεΦ₀⟩ := hΦ.exists_pos_apply_eq_right
  set ε := min ε₀ 1
  have hε : 0 < ε := lt_min hε₀ one_pos
  have hεΦ (w : Circle) (t : ℝ) (ht : 1 - ε ≤ t) : Φ (w, t) = (K w, t) :=
    hεΦ₀ w t (by linarith [min_le_left ε₀ 1])
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
  refine ⟨range fun q : W => ballCollarC q, hc.isOpen_range, ⟨⟨(⟨x, ?_⟩, 0), ?_⟩, ?_⟩, ?_, ?_⟩
  · exact mem_sphere_zero_iff_norm.2 hx
  · simpa [W] using hε
  · refine Subtype.ext ?_
    simp [coe_ballCollarC, polarC_apply]
  · rintro _ ⟨⟨⟨w, s⟩, hs⟩, rfl⟩
    have hs' : s.1 0 < ε := hs
    rw [coe_ballCollarC, norm_polarC, Real.exp_lt_exp]
    linarith [min_le_right ε₀ 1]
  have h2 := (hcap ▸ h1.restrict hW).comp_homeomorph hc.isEmbedding.toHomeomorph.symm
  convert h2.transIsOpenEmbedding
    (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) 1).toHomeomorph.isOpenEmbedding using 1
  funext u
  simp only [Function.comp_apply]
  congr
  exact (congrArg Subtype.val (hc.isEmbedding.toHomeomorph.apply_symm_apply u)).symm

open scoped Classical in
/-- The disc glued from a slice disc `Ψ` for `K₀`, shrunk into the ball of radius `exp (-1)`, and
the cone on a collared track `Φ` from `K₀` to `K`, read in polar coordinates outside that ball. -/
private def glueMap (Ψ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1)
    (Φ : Circle × ℝ → sphere (0 : E) 1 × ℝ) (z : ℂ) : E :=
  if ‖z‖ ≤ Real.exp (-1) then Real.exp (-1) • coneExt Ψ (Real.exp 1 • z) else capMap Φ z

private theorem glueMap_of_le {z : ℂ} (hz : ‖z‖ ≤ Real.exp (-1)) :
    glueMap Ψ Φ z = Real.exp (-1) • coneExt Ψ (Real.exp 1 • z) :=
  ite_eq_left hz

private theorem glueMap_of_lt {z : ℂ} (hz : Real.exp (-1) < ‖z‖) : glueMap Ψ Φ z = capMap Φ z :=
  ite_eq_right hz.not_ge

private theorem norm_glueMap_le_exp_neg_one (hΨ : IsTopologicalSliceDisc K₀ Ψ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-1)) : ‖glueMap Ψ Φ z‖ ≤ Real.exp (-1) := by
  have hez : ‖Real.exp 1 • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos 1).le]
    calc Real.exp 1 * ‖z‖ ≤ Real.exp 1 * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left hz (Real.exp_pos 1).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [glueMap_of_le hz, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-1) * ‖coneExt Ψ (Real.exp 1 • z)‖ ≤ Real.exp (-1) * 1 :=
        mul_le_mul_of_nonneg_left ((norm_coneExt_le hΨ _).trans (max_le hez le_rfl))
          (Real.exp_pos _).le
    _ = Real.exp (-1) := mul_one _

/-- Inside the circle of radius `exp (ε - 1)`, `ε ≤ 1` a collar width of the initial end, the glued
disc is the cone extension of the slice disc, shrunk by `exp (-1)`. -/
private theorem glueMap_eq_of_norm_le {ε : ℝ} (hΨ : IsTopologicalSliceDisc K₀ Ψ)
    (hΦ : ∀ (x : Circle) (t : ℝ), t ≤ ε → Φ (x, t) = (K₀ x, t)) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (ε - 1)) :
    glueMap Ψ Φ z = Real.exp (-1) • coneExt Ψ (Real.exp 1 • z) := by
  rcases le_or_gt ‖z‖ (Real.exp (-1)) with hz1 | hz1
  · exact glueMap_of_le hz1
  rw [glueMap_of_lt hz1]
  -- Write `z = exp (t - 1) • u` with `u` on the unit circle and `0 < t ≤ ε`.
  obtain ⟨⟨u, t⟩, rfl⟩ := mem_range_polarC (norm_pos_iff.1 ((Real.exp_pos _).trans hz1))
  rw [norm_polarC, Real.exp_le_exp] at hz
  rw [norm_polarC, Real.exp_lt_exp] at hz1
  have hsmul : Real.exp 1 • polarC (u, t) = Real.exp t • (u : ℂ) := by
    rw [polarC_apply, smul_smul, ← Real.exp_add, add_sub_cancel]
  have hnorm : ‖Real.exp t • (u : ℂ)‖ = Real.exp t := by
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (Real.exp_pos t).le]
  have her : 1 ≤ Real.exp t := Real.one_le_exp (by linarith)
  have hret : radialRetractionToClosedBall zero_le_one (Real.exp t • (u : ℂ)) =
      Set.inclusion sphere_subset_closedBall u := by
    refine Subtype.ext ?_
    rw [coe_radialRetractionToClosedBall zero_le_one,
      radialRetraction_of_le_norm (by rw [hnorm]; exact her), hnorm, smul_smul,
      one_div_mul_cancel (Real.exp_pos t).ne', one_smul]
  rw [capMap_polarC, hΦ u t (by linarith), polar_apply, hsmul, coneExt, hnorm, max_eq_left her,
    hret, hΨ.apply_inclusion, smul_smul, ← Real.exp_add, neg_add_eq_sub]

private theorem norm_glueMap_le_one (hΨ : IsTopologicalSliceDisc K₀ Ψ) (hΦ : IsCollaredTrack K₀ K Φ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖glueMap Ψ Φ z‖ ≤ 1 := by
  rcases le_or_gt ‖z‖ (Real.exp (-1)) with hz1 | hz1
  · exact (norm_glueMap_le_exp_neg_one hΨ hz1).trans (Real.exp_le_one_iff.2 (by norm_num))
  · rw [glueMap_of_lt hz1]
    exact (norm_capMap_le_one_iff hΦ z).2 hz

private theorem norm_glueMap_eq_one_iff (hΨ : IsTopologicalSliceDisc K₀ Ψ)
    (hΦ : IsCollaredTrack K₀ K Φ) (z : ℂ) : ‖glueMap Ψ Φ z‖ = 1 ↔ ‖z‖ = 1 := by
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  rcases le_or_gt ‖z‖ (Real.exp (-1)) with hz1 | hz1
  · exact iff_of_false ((norm_glueMap_le_exp_neg_one hΨ hz1).trans_lt he).ne
      (hz1.trans_lt he).ne
  · rw [glueMap_of_lt hz1]
    exact norm_capMap_eq_one_iff hΦ z

private theorem glueMap_injective (hΨ : IsTopologicalSliceDisc K₀ Ψ)
    (hΦ : IsCollaredTrack K₀ K Φ) (hΦi : Function.Injective Φ) :
    Function.Injective (glueMap Ψ Φ) := by
  have hinner : Function.Injective fun z : ℂ => Real.exp (-1) • coneExt Ψ (Real.exp 1 • z) :=
    (smul_right_injective E (Real.exp_pos _).ne').comp
      ((coneExt_injective hΨ).comp (smul_right_injective ℂ (Real.exp_pos 1).ne'))
  intro z z' h
  rcases le_or_gt ‖z‖ (Real.exp (-1)) with hz | hz <;>
    rcases le_or_gt ‖z'‖ (Real.exp (-1)) with hz' | hz'
  · rw [glueMap_of_le hz, glueMap_of_le hz'] at h
    exact hinner h
  · have := norm_glueMap_le_exp_neg_one (Φ := Φ) hΨ hz
    rw [h, glueMap_of_lt hz'] at this
    exact absurd this (exp_neg_one_lt_norm_capMap hΦ hz').not_ge
  · have := norm_glueMap_le_exp_neg_one (Φ := Φ) hΨ hz'
    rw [← h, glueMap_of_lt hz] at this
    exact absurd this (exp_neg_one_lt_norm_capMap hΦ hz).not_ge
  · rw [glueMap_of_lt hz, glueMap_of_lt hz'] at h
    exact capMap_injective hΦi h

/-- The glued disc, restricted to the closed unit disc. -/
private def glueDisc (hΨ : IsTopologicalSliceDisc K₀ Ψ) (hΦ : IsCollaredTrack K₀ K Φ)
    (z : closedBall (0 : ℂ) 1) : closedBall (0 : E) 1 :=
  ⟨glueMap Ψ Φ z,
    mem_closedBall_zero_iff.2 (norm_glueMap_le_one hΨ hΦ (mem_closedBall_zero_iff.1 z.2))⟩

private theorem coe_glueDisc (hΨ : IsTopologicalSliceDisc K₀ Ψ) (hΦ : IsCollaredTrack K₀ K Φ)
    (z : closedBall (0 : ℂ) 1) : (glueDisc hΨ hΦ z : E) = glueMap Ψ Φ z :=
  (rfl)

/-- Outside the circle of radius `exp (-1)` the glued disc is the capped disc. -/
private theorem glueDisc_eq_capDisc (hΨ : IsTopologicalSliceDisc K₀ Ψ)
    (hΦ : IsCollaredTrack K₀ K Φ) {U : Set (closedBall (0 : ℂ) 1)}
    (hU : ∀ z ∈ U, Real.exp (-1) < ‖(z : ℂ)‖) :
    glueDisc hΨ hΦ ∘ ((↑) : U → _) = capDisc hΦ ∘ ((↑) : U → _) := by
  funext z
  exact Subtype.ext (glueMap_of_lt (hU z z.2))

/-- Every point of the closed unit disc has an open neighbourhood on which the glued disc is
locally flat, with tangential model the half-plane. -/
private theorem exists_isLocallyFlat_glueDisc_comp_coe (hF : finrank ℝ F = 1)
    (hΨ : IsTopologicalSliceDisc K₀ Ψ) (hΦ : IsCollaredTrack K₀ K Φ)
    (hΦ' : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1))) Φ)
    (x : closedBall (0 : ℂ) 1) :
    ∃ U : Set (closedBall (0 : ℂ) 1), IsOpen U ∧ x ∈ U ∧
      IsLocallyFlat (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin (n - 1)))
        (glueDisc hΨ hΦ ∘ ((↑) : U → _)) := by
  have hcont : Continuous fun z : closedBall (0 : ℂ) 1 => ‖(z : ℂ)‖ := by fun_prop
  obtain ⟨ε₀, hε₀, hεΦ₀⟩ := hΦ.exists_pos_apply_eq_left
  set ε := min ε₀ (1 / 2)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεΦ (w : Circle) (t : ℝ) (ht : t ≤ ε) : Φ (w, t) = (K₀ w, t) :=
    hεΦ₀ w t (ht.trans (min_le_left _ _))
  have hρ : Real.exp (ε - 1) < 1 := Real.exp_lt_one_iff.2 (by linarith [min_le_right ε₀ (1 / 2)])
  have hρ' : Real.exp (-1) < Real.exp (ε - 1) := Real.exp_lt_exp.2 (by linarith)
  by_cases h0 : ‖(x : ℂ)‖ < Real.exp (ε - 1)
  · -- Near the centre: the shrunk cone extension of the slice disc.
    set U := {z : closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < Real.exp (ε - 1)}
    have hU : IsOpen U := isOpen_lt hcont continuous_const
    have hι : IsOpenEmbedding fun z : U => ((z : closedBall (0 : ℂ) 1) : ℂ) :=
      hU.isOpenEmbedding_coe_openSubset_closedBall fun z hz => hz.trans hρ
    have hS := (((isLocallyFlat_coneExt hΨ).homeomorph_comp
      (Homeomorph.smulOfNeZero (Real.exp (-1)) (Real.exp_pos _).ne')).comp_homeomorph
      (Homeomorph.smulOfNeZero (Real.exp 1) (Real.exp_pos _).ne')).comp_isOpenEmbedding hι
    refine ⟨U, hU, h0, IsLocallyFlat.of_coe_closedBall (fun z => ?_) ?_⟩
    · exact lt_of_le_of_ne (norm_glueMap_le_one hΨ hΦ (mem_closedBall_zero_iff.1 z.1.2))
        ((norm_glueMap_eq_one_iff hΨ hΦ _).not.2 (z.2.trans hρ).ne)
    · convert hS using 1
      funext z
      exact glueMap_eq_of_norm_le hΨ hεΦ z.2.le
  by_cases h1 : ‖(x : ℂ)‖ < 1
  · -- In the open annulus: the capped disc, the track read in polar coordinates.
    set U := {z : closedBall (0 : ℂ) 1 | Real.exp (-1) < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1}
    have hU : IsOpen U :=
      (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
    refine ⟨U, hU, ⟨hρ'.trans_le (not_lt.1 h0), h1⟩, ?_⟩
    rw [glueDisc_eq_capDisc hΨ hΦ fun z (hz : z ∈ U) => hz.1]
    exact isLocallyFlat_capDisc_comp_coe_of_pos_of_lt hF hΦ hΦ' hU
      fun z hz => ⟨(Real.exp_pos _).trans hz.1, hz.2⟩
  -- Near the boundary circle: the cone on `K`.
  obtain ⟨U, hU, hxU, hUe, hflat⟩ := exists_isLocallyFlat_capDisc_comp_coe_of_norm_eq_one hΦ
    (le_antisymm (mem_closedBall_zero_iff.1 x.2) (not_lt.1 h1))
  exact ⟨U, hU, hxU, glueDisc_eq_capDisc hΨ hΦ hUe ▸ hflat⟩

/-- **Gluing a slice disc to a concordance.** If `Ψ` is a locally flat slice disc for `K₀` and `Φ`
is a locally flat collared track from `K₀` to `K`, then the glued disc is a locally flat slice disc
for `K`. -/
private theorem isTopologicalSliceDisc_glueDisc (hF : finrank ℝ F = 1)
    (hΨ : IsTopologicalSliceDisc K₀ Ψ) (hΦ : IsCollaredTrack K₀ K Φ)
    (hΦ' : IsLocallyFlat (F × ℝ) (EuclideanSpace ℝ (Fin (n - 1))) Φ) :
    IsTopologicalSliceDisc K (glueDisc hΨ hΦ) := by
  have hloc := exists_isLocallyFlat_glueDisc_comp_coe hF hΨ hΦ hΦ'
  have hcont : Continuous (glueDisc hΨ hΦ) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨U, hU, hxU, hflat⟩ := hloc x
    exact (continuousOn_iff_continuous_domRestrict.2 hflat.continuous).continuousAt
      (hU.mem_nhds hxU)
  have hinj : Function.Injective (glueDisc hΨ hΦ) := fun z z' h =>
    Subtype.ext (glueMap_injective hΨ hΦ hΦ'.injective (congrArg Subtype.val h))
  have : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  refine ⟨.of_forall_exists_isOpen (hcont.isClosedEmbedding hinj).isEmbedding hloc,
    fun x => norm_glueMap_eq_one_iff hΨ hΦ x, fun z => ?_⟩
  have hz : ((Set.inclusion sphere_subset_closedBall z : closedBall (0 : ℂ) 1) : ℂ) =
      polarC (z, 1) := by
    simp [polarC_apply]
  have hz1 : Real.exp (-1) < ‖polarC (z, 1)‖ := by
    rw [norm_polarC, sub_self, Real.exp_zero]
    exact Real.exp_lt_one_iff.2 (by norm_num)
  rw [coe_glueDisc, hz, glueMap_of_lt hz1, capMap_polarC, hΦ.apply_one, polar_apply, sub_self,
    Real.exp_zero, one_smul]

end LocallyFlat

/-! ### Topological sliceness is a topological concordance invariant -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {K₀ K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- **A knot topologically concordant to a topologically slice knot is topologically slice.** If
`K₀` is topologically slice and topologically concordant to `K`, for real normed model spaces `F` of
the circle and `F'` of its normal directions, of dimensions `1` and `n - 1`, then `K` bounds a
locally flat disc in `Dⁿ⁺¹`: glue a slice disc of `K₀` to the concordance. -/
theorem IsTopologicallySlice.of_topologicallyConcordant (hF : finrank ℝ F = 1)
    (hF' : finrank ℝ F' = n - 1) (h₀ : IsTopologicallySlice K₀)
    (h : TopologicallyConcordant F F' K₀ K) : IsTopologicallySlice K := by
  obtain ⟨Ψ, hΨ⟩ := h₀.elim
  obtain ⟨Φ⟩ := topologicallyConcordant_iff_nonempty.1 h
  let L : F' ≃L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hF'])
  exact (isTopologicalSliceDisc_glueDisc hF hΨ Φ.isCollaredTrack
    (Φ.isLocallyFlat.transHomeomorph L.toHomeomorph (by simp))).isTopologicallySlice

/-- **Topological sliceness is invariant under topological concordance.** -/
theorem TopologicallyConcordant.isTopologicallySlice_iff (hF : finrank ℝ F = 1)
    (hF' : finrank ℝ F' = n - 1) (h : TopologicallyConcordant F F' K₀ K) :
    IsTopologicallySlice K₀ ↔ IsTopologicallySlice K :=
  ⟨fun h₀ => h₀.of_topologicallyConcordant hF hF' h,
    fun h₁ => h₁.of_topologicallyConcordant hF hF' h.symm⟩

/-- **A knot topologically concordant to a great circle is topologically slice.** If `K` is
topologically concordant to the great circle `ι S¹` of `Sⁿ`, for real normed model spaces `F` of
the circle and `F'` of its normal directions, of dimensions `1` and `n - 1`, then `K` bounds a
locally flat disc in `Dⁿ⁺¹`: cap the concordance off with the flat disc `ι D²`. -/
theorem TopologicallyConcordant.isTopologicallySlice (hF : finrank ℝ F = 1)
    (hF' : finrank ℝ F' = n - 1) {ι : ℂ →ₗᵢ[ℝ] E}
    (h : TopologicallyConcordant F F' (SmoothCircleEmbedding.greatCircle (n := n) ι) K) :
    IsTopologicallySlice K :=
  (isTopologicallySlice_greatCircle ι).of_topologicallyConcordant hF hF' h

/-- **A knot in `S³` topologically concordant to the unknot is topologically slice.** -/
theorem isTopologicallySlice_of_topologicallyConcordant_unknot (hF : finrank ℝ F = 1)
    (hF' : finrank ℝ F' = 2)
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    (h : TopologicallyConcordant F F' unknot K) : IsTopologicallySlice K := by
  rw [unknot_eq_greatCircle] at h
  exact h.isTopologicallySlice hF hF'

/-! ### Capping a smooth concordance -/

section Smooth

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E} {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  {Φ : Circle × ℝ → sphere (0 : E) 1 × ℝ}

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

/-- Exponential polar coordinates of the punctured plane, read on the standard circle, are a local
diffeomorphism. -/
private theorem isLocalDiffeomorph_polarC :
    IsLocalDiffeomorph ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ polarC :=
  isLocalDiffeomorph_polar (V := ℂ) (n := 1)

/-- Read in polar coordinates, the cone on a track is the track read in polar coordinates. -/
private theorem capMap_comp_polarC : capMap Φ ∘ polarC = polar ∘ Φ :=
  funext capMap_polarC

/-- Near the origin the cone on a track starting at the great circle `ι S¹` is `ι`. -/
private theorem capMap_eventuallyEq_of_norm_lt
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) {w : ℂ}
    (hw : ‖w‖ < Real.exp (-1)) : capMap Φ =ᶠ[𝓝 w] ι :=
  Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hw)
    fun _ hz => capMap_eq_of_norm_le hΦ (le_of_lt hz)

/-- Beyond the collar width `ε` of the final end, the cone on a track ending at `K` is the cone
`s • K u` over `K`. -/
private theorem capMap_smul_of_exp_neg_le {ε : ℝ}
    (hε : ∀ (x : Circle) (t : ℝ), 1 - ε ≤ t → Φ (x, t) = (K x, t)) (u : Circle) {s : ℝ}
    (hs : Real.exp (-ε) ≤ s) : capMap Φ (s • (u : ℂ)) = s • (K u : E) := by
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  have hlog : -ε ≤ Real.log s := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hs
  have h : s • (u : ℂ) = polarC (u, 1 + Real.log s) := by
    rw [polarC_apply, add_sub_cancel_left, Real.exp_log hs0]
  rw [h, capMap_polarC, hε u _ (by linarith), polar_apply, add_sub_cancel_left, Real.exp_log hs0]

/-- Outside the open unit disc the cone on a track ending at `K` preserves the norm. -/
private theorem norm_capMap_of_one_le
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ) {z : ℂ}
    (hz : 1 ≤ ‖z‖) : ‖capMap Φ z‖ = ‖z‖ := by
  obtain ⟨⟨x, t⟩, rfl⟩ := mem_range_polarC (norm_pos_iff.1 (one_pos.trans_le hz))
  rw [norm_polarC, Real.one_le_exp_iff, sub_nonneg] at hz
  rw [capMap_polarC, hΦ.apply_of_one_le x hz, norm_polar, norm_polarC]

/-- The cone on an injective collared track ending at `K` is a closed embedding: it is proper,
since it preserves the norm outside the unit disc. -/
private theorem isClosedEmbedding_capMap
    (hΦ : IsCollaredTrack (SmoothCircleEmbedding.greatCircle (n := n) ι) K Φ)
    (hinj : Function.Injective Φ) (hcont : Continuous (capMap Φ)) :
    IsClosedEmbedding (capMap Φ) := by
  have hprop : IsProperMap (capMap Φ) :=
    isProperMap_iff_tendsto_cocompact.2 ⟨hcont, Filter.tendsto_cocompact_cocompact_of_norm
      fun R => ⟨max R 1, fun z hz => by
        rw [norm_capMap_of_one_le hΦ ((le_max_right _ _).trans hz.le)]
        exact (le_max_left _ _).trans_lt hz⟩⟩
  exact .of_continuous_injective_isClosedMap hcont (capMap_injective hinj) hprop.isClosedMap

variable (F : SmoothEmbedding.Concordance (SmoothCircleEmbedding.greatCircle (n := n) ι) K)

/-- Away from the origin the cone on a smooth concordance is smooth with injective differential:
precomposed with polar coordinates of the plane, a local diffeomorphism, it is the track followed
by polar coordinates of `E`, a local diffeomorphism. -/
private theorem contMDiffAt_capMap_and_injective_mfderiv {w : ℂ} (hw : w ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (capMap F) w ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (capMap F) w) := by
  obtain ⟨q, rfl⟩ := mem_range_polarC hw
  have hp := isLocalDiffeomorph_polarC q
  refine ⟨(hp.contMDiffAt_comp_iff le_rfl).1 ?_, ?_⟩
  · rw [capMap_comp_polarC]
    exact (isLocalDiffeomorph_polar (F q)).contMDiffAt.comp q (F.toSmoothEmbedding.contMDiff q)
  · refine ((IsDiffImmersionAt.comp_isLocalDiffeomorphAt_left_iff rfl hp (by simp)).2 ?_)
      |>.mfderiv_injective
    rw [capMap_comp_polarC]
    exact ((isLocalDiffeomorph_polar (F q)).isDiffImmersionAt (by simp)).comp
      (F.toSmoothEmbedding.isImmersion.isDiffImmersionAt (by simp) q)

/-- The cone on a smooth concordance is an immersion at every point: near the origin it is the
linear isometry `ι`, and away from the origin its differential is injective. -/
private theorem isImmersionAt_capMap (w : ℂ) :
    IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (capMap F) w := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hΦ := F.isCollaredTrack
  by_cases hw : ‖w‖ < Real.exp (-1)
  · have hs : IsOpen (ball (0 : ℂ) (Real.exp (-1))) := isOpen_ball
    have hon : ContDiffOn ℝ ∞ (capMap F) (ball (0 : ℂ) (Real.exp (-1))) :=
      ι.contDiff.contDiffOn.congr fun z hz =>
        capMap_eq_of_norm_le hΦ (le_of_lt (mem_ball_zero_iff.1 hz))
    refine (hon.isImmersionAt_iff_injective_fderiv hs (mem_ball_zero_iff.2 hw) (by simp)).2 ?_
    -- `ι` coerces to the function of its continuous linear map, whose derivative is itself.
    have hι : fderiv ℝ ι w = ι.toContinuousLinearMap := ι.toContinuousLinearMap.fderiv
    rw [(capMap_eventuallyEq_of_norm_lt hΦ hw).fderiv_eq, hι]
    exact ι.injective
  · have hw0 : w ≠ 0 := by
      rintro rfl
      exact hw (by simpa using Real.exp_pos (-1))
    have hon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (capMap F) {0}ᶜ := fun z hz =>
      (contMDiffAt_capMap_and_injective_mfderiv F hz).1.contMDiffWithinAt
    exact (hon.isImmersionAt_iff_injective_mfderiv isOpen_compl_singleton hw0 (by simp)).2
      (contMDiffAt_capMap_and_injective_mfderiv F hw0).2

/-- **The cap of a smooth concordance from a great circle is a smooth embedding of the plane.**
If `F` is a smooth concordance from the great circle `ι S¹` to a knot `K` in `Sⁿ`, there is a
smooth embedding `c : ℂ → E` such that

* near the origin, on the closed disc of radius `exp (-1)`, `c` is the linear isometry `ι`;
* for some `r < 1` and all radii `s ≥ r`, `c (s • u) = s • K u`: near the unit circle and beyond,
  `c` is the cone over `K`;
* `c` meets the closed unit ball exactly over the closed unit disc, and the unit sphere exactly
  over the unit circle.

The witness is constructed from the track of `F` read in exponential polar coordinates
`(u, t) ↦ exp (t - 1) • u` (see the module docstring), but the statement only records the
properties above: on the closed unit disc, `c` is `ι` on the disc of radius `exp (-1)` and the cone
over `K` on the annulus `r ≤ ‖z‖ ≤ 1`. -/
theorem SmoothEmbedding.Concordance.exists_isSmoothEmbedding_cap
    (F : SmoothEmbedding.Concordance (SmoothCircleEmbedding.greatCircle (n := n) ι) K) :
    ∃ c : ℂ → E, IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ c ∧
      (∀ z : ℂ, ‖z‖ ≤ Real.exp (-1) → c z = ι z) ∧
      (∃ r < 1, ∀ (u : Circle) (s : ℝ), r ≤ s → c (s • (u : ℂ)) = s • (K u : E)) ∧
      (∀ z : ℂ, ‖c z‖ ≤ 1 ↔ ‖z‖ ≤ 1) ∧ (∀ z : ℂ, ‖c z‖ = 1 ↔ ‖z‖ = 1) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hΦ := F.isCollaredTrack
  have himm : IsImmersion 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (capMap F) :=
    isImmersion_iff_forall_isImmersionAt.2 (isImmersionAt_capMap F)
  obtain ⟨ε, hε, hεF⟩ := hΦ.exists_pos_apply_eq_right
  refine ⟨capMap F, ⟨himm, (isClosedEmbedding_capMap hΦ F.toSmoothEmbedding.isEmbedding.injective
      himm.contMDiff.continuous).isEmbedding⟩,
    fun z hz => capMap_eq_of_norm_le hΦ hz, ⟨Real.exp (-ε), ?_, fun u s hs =>
      capMap_smul_of_exp_neg_le hεF u hs⟩, norm_capMap_le_one_iff hΦ, norm_capMap_eq_one_iff hΦ⟩
  simpa using hε

end Smooth

end TauCeti
