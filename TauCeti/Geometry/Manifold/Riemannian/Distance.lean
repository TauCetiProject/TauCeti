/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Finiteness of the Riemannian distance, and the induced metric space

`Manifold.riemannianEDist I x y` is the infimum of the lengths of `C¹` paths from `x` to `y`, an
*extended* distance: it is `∞` as soon as no such path exists. This file identifies exactly when it
is finite, and uses that to promote the extended metric space structure
`EMetricSpace.ofRiemannianMetric` of a preconnected Riemannian manifold to an ordinary metric space
structure, which is what statements about `dist`, `ProperSpace` and `CompleteSpace` need.

The key point is that `{y | riemannianEDist I x y < ∞}` is clopen: it is open because nearby points
are at small Riemannian distance (`eventually_riemannianEDist_lt`), and its complement is open for
the same reason. Hence it contains the connected component of `x`. Conversely a `C¹` path is in
particular continuous, so a point at finite Riemannian distance from `x` lies in the connected
component of `x`. Together these give
`riemannianEDist_lt_top_iff_mem_connectedComponent`, of which finiteness on a preconnected manifold
is the special case that matters downstream.

## Main results

* `TauCeti.Manifold.riemannianEDist_lt_top_iff_mem_connectedComponent`: the Riemannian distance from
  `x` to `y` is finite if and only if `y` lies in the connected component of `x`.
* `TauCeti.Manifold.riemannianEDist_ne_top`: on a preconnected manifold the Riemannian distance is
  never `∞`.
* `TauCeti.PseudoMetricSpace.ofRiemannianMetric` and `TauCeti.MetricSpace.ofRiemannianMetric`: the
  (pseudo)metric space structures of a preconnected Riemannian manifold, refining
  `PseudoEMetricSpace.ofRiemannianMetric` and `EMetricSpace.ofRiemannianMetric`; both satisfy
  `IsRiemannianManifold I M`.
* `TauCeti.IsRiemannianManifold.edist_le_pathELength` and
  `TauCeti.IsRiemannianManifold.dist_le_toReal_pathELength`: the ambient (extended) distance of a
  Riemannian manifold, read through `IsRiemannianManifold.out`, is bounded by the length of any
  `C¹` path.
* `TauCeti.IsRiemannianManifold.edist_le_of_norm_mfderiv_le`: the mean-value inequality for a
  `C¹` map from a normed space into a Riemannian manifold along a segment.
* `TauCeti.Manifold.le_riemannianEDist_of_forall_le_pathELength`: the extended distance is bounded
  below by any bound valid for the lengths of *all* `C¹` curves joining two points, since it is the
  infimum of those lengths.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Distance compatibility and finiteness".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 §2, Def. 2.4.
* `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` (S. Gouëzel):
  `PseudoEMetricSpace.ofRiemannianMetric`, `EMetricSpace.ofRiemannianMetric`, and their
  `IsRiemannianManifold` instances, which the (pseudo)metric constructions here adapt.
-/

public section

open Bundle Manifold Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

section Finiteness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Two points at finite Riemannian distance are joined by a path: a `C¹` path witnessing any
strict upper bound on the distance is in particular continuous. -/
theorem joined_of_riemannianEDist_lt_top {x y : M} (h : riemannianEDist I x y < ⊤) :
    Joined x y := by
  obtain ⟨γ, hγ0, hγ1, hγ, -⟩ := exists_lt_of_riemannianEDist_lt h
  exact (JoinedIn.ofLine (F := univ) hγ.continuousOn hγ0 hγ1 (subset_univ _)).joined

/-- The Riemannian extended distance is bounded below by any bound that is valid for the lengths
of *all* `C¹` curves joining the two points: it is the infimum of those lengths. -/
theorem le_riemannianEDist_of_forall_le_pathELength {x y : M} {c : ℝ≥0∞}
    (h : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → CMDiff[Icc 0 1] 1 γ →
      c ≤ pathELength I γ 0 1) :
    c ≤ riemannianEDist I x y := by
  by_contra hle
  rw [not_le] at hle
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hle
  obtain ⟨γ, h0, h1, hγ, hl⟩ := exists_lt_of_riemannianEDist_lt hr1
  exact absurd ((h γ h0 h1 hγ).trans hl.le) (not_le.2 hr2)

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is open: any point close enough to a
point `y` of this set is at Riemannian distance `< 1` from `y`, hence at finite distance from `x` by
the triangle inequality. -/
theorem isOpen_setOfPred_riemannianEDist_lt_top (x : M) :
    IsOpen {y | riemannianEDist I x y < ⊤} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_riemannianEDist_lt I y zero_lt_one] with z hz
  exact (riemannianEDist_triangle (y := y)).trans_lt
    (ENNReal.add_lt_top.2 ⟨hy, hz.trans_le le_top⟩)

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is closed: if `y` is at infinite
Riemannian distance from `x`, then so is any point close enough to `y`, again by the triangle
inequality. -/
theorem isClosed_setOfPred_riemannianEDist_lt_top (x : M) :
    IsClosed {y | riemannianEDist I x y < ⊤} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_riemannianEDist_lt I y zero_lt_one] with z hz hz'
  refine hy ((riemannianEDist_triangle (y := z)).trans_lt (ENNReal.add_lt_top.2 ⟨hz', ?_⟩))
  rw [riemannianEDist_comm]
  exact hz.trans_le le_top

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is clopen. -/
theorem isClopen_setOfPred_riemannianEDist_lt_top (x : M) :
    IsClopen {y | riemannianEDist I x y < ⊤} :=
  ⟨isClosed_setOfPred_riemannianEDist_lt_top I x, isOpen_setOfPred_riemannianEDist_lt_top I x⟩

variable (I) in
/-- Two points of a preconnected set are at finite Riemannian distance. -/
theorem riemannianEDist_lt_top_of_isPreconnected {s : Set M} (hs : IsPreconnected s) {x y : M}
    (hx : x ∈ s) (hy : y ∈ s) : riemannianEDist I x y < ⊤ :=
  hs.subset_isClopen (isClopen_setOfPred_riemannianEDist_lt_top I x)
    ⟨x, hx, by simp [riemannianEDist_self]⟩ hy

variable (I) in
/-- The Riemannian distance from `x` to `y` is finite exactly when `y` lies in the connected
component of `x`. -/
theorem riemannianEDist_lt_top_iff_mem_connectedComponent {x y : M} :
    riemannianEDist I x y < ⊤ ↔ y ∈ connectedComponent x :=
  ⟨fun h ↦ pathComponent_subset_component x (joined_of_riemannianEDist_lt_top h),
    riemannianEDist_lt_top_of_isPreconnected I isPreconnected_connectedComponent
      mem_connectedComponent⟩

variable (I) in
/-- On a preconnected manifold, the Riemannian distance between any two points is finite. -/
theorem riemannianEDist_lt_top [PreconnectedSpace M] (x y : M) : riemannianEDist I x y < ⊤ :=
  riemannianEDist_lt_top_of_isPreconnected I isPreconnected_univ (mem_univ x) (mem_univ y)

variable (I) in
/-- On a preconnected manifold, the Riemannian distance between any two points is finite. This is
the hypothesis needed to turn `EMetricSpace.ofRiemannianMetric` into a genuine metric space. -/
@[aesop (rule_sets := [finiteness]) safe apply, simp]
theorem riemannianEDist_ne_top [PreconnectedSpace M] (x y : M) : riemannianEDist I x y ≠ ⊤ :=
  (riemannianEDist_lt_top I x y).ne

end Finiteness

end Manifold

namespace IsRiemannianManifold

section PseudoEMetric

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- In a Riemannian manifold, the ambient extended distance between the endpoints of a `C¹` path
is at most the length of that path. This is `Manifold.riemannianEDist_le_pathELength` read through
`IsRiemannianManifold.out`. -/
theorem edist_le_pathELength {γ : ℝ → M} {a b : ℝ} (hγ : CMDiff[Icc a b] 1 γ) (hab : a ≤ b) :
    edist (γ a) (γ b) ≤ pathELength I γ a b := by
  rw [IsRiemannianManifold.out (I := I) (γ a) (γ b)]
  exact riemannianEDist_le_pathELength hγ rfl rfl hab

/-- **The mean-value inequality for maps into a Riemannian manifold.** Let `f` be a map from a real
normed space to a Riemannian manifold which is `C¹` at every point of the segment from `a` to `b`.
If its differential along that segment sends `b - a` to vectors of norm at most `C`, then `f a` and
`f b` are at extended distance at most `C`. -/
theorem edist_le_of_norm_mfderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → M} {a b : F} {C : ℝ}
    (hf : ∀ z ∈ segment ℝ a b, ContMDiffAt 𝓘(ℝ, F) I 1 f z)
    (hC : ∀ z ∈ segment ℝ a b, ‖mfderiv 𝓘(ℝ, F) I f z (b - a)‖ ≤ C) :
    edist (f a) (f b) ≤ ENNReal.ofReal C := by
  let c : ℝ → F := fun τ ↦ a + τ • (b - a)
  have hcseg : MapsTo c (Icc 0 1) (segment ℝ a b) := fun τ hτ ↦ by
    rw [segment_eq_image']
    exact ⟨τ, hτ, rfl⟩
  have hcderiv : ∀ τ, HasDerivAt c (b - a) τ := fun τ ↦
    (((hasDerivAt_id' τ).smul_const (b - a)).const_add a).congr_deriv (one_smul ℝ _)
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 c := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hsmooth : CMDiff[Icc 0 1] 1 (f ∘ c) := fun τ hτ ↦
    (hf _ (hcseg hτ)).comp_contMDiffWithinAt τ hc.contMDiffAt.contMDiffWithinAt
  have hlen := edist_le_pathELength hsmooth zero_le_one
  have h0 : c 0 = a := by simp [c]
  have h1 : c 1 = b := by simp [c]
  simp only [Function.comp_apply, h0, h1] at hlen
  calc
    edist (f a) (f b) ≤ pathELength I (f ∘ c) 0 1 := hlen
    _ = ∫⁻ τ in Ioo 0 1, ‖mfderiv 𝓘(ℝ, ℝ) I (f ∘ c) τ (1 : ℝ)‖ₑ :=
      pathELength_eq_lintegral_mfderiv_Ioo
    _ ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal C := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun τ hτ ↦ ?_
      have hτ' : c τ ∈ segment ℝ a b := hcseg (Ioo_subset_Icc_self hτ)
      rw [← Manifold.curveVelocity_apply,
        ((hf _ hτ').mdifferentiableAt one_ne_zero).curveVelocity_comp_mfderiv (hcderiv τ),
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _ hτ')
    _ = ENNReal.ofReal C := by simp

end PseudoEMetric

section PseudoMetric

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, that distance is the real
part of the Riemannian extended distance. -/
theorem dist_eq_toReal_riemannianEDist (x y : M) : dist x y = (riemannianEDist I x y).toReal := by
  rw [dist_edist, IsRiemannianManifold.out (I := I) x y]

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, the distance is bounded
above by the length of any `C¹` path of finite length between the two points. -/
theorem dist_le_toReal_pathELength {γ : ℝ → M} {a b : ℝ} {x y : M} (hγ : CMDiff[Icc a b] 1 γ)
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) (h : pathELength I γ a b ≠ ⊤) :
    dist x y ≤ (pathELength I γ a b).toReal := by
  subst ha hb
  rw [dist_edist]
  exact ENNReal.toReal_mono h (edist_le_pathELength hγ hab)

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, any bound `r` on the
distance from `x` to `y` is witnessed by a `C¹` path on `[0, 1]` of length `< ENNReal.ofReal r`. -/
theorem exists_pathELength_lt_of_dist_lt {x y : M} {r : ℝ} (hr : dist x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧
      pathELength I γ 0 1 < ENNReal.ofReal r := by
  apply exists_lt_of_riemannianEDist_lt
  rw [← IsRiemannianManifold.out (I := I) x y, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hr)).2 hr

end PseudoMetric

end IsRiemannianManifold

section OfRiemannianMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The pseudometric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `PseudoEMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory, one
should rather assume that there is an already existing pseudometric space structure, satisfying
additionally the predicate `IsRiemannianManifold I M`. -/
@[reducible] def PseudoMetricSpace.ofRiemannianMetric [RegularSpace M] [PreconnectedSpace M] :
    PseudoMetricSpace M :=
  letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

/-- The distance of `PseudoMetricSpace.ofRiemannianMetric` is the infimum of the lengths of `C¹`
paths, i.e. the resulting pseudometric space satisfies the `IsRiemannianManifold I M` predicate. -/
instance [RegularSpace M] [PreconnectedSpace M] :
    letI : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
  -- `PseudoEMetricSpace.toPseudoMetricSpace` is set up so that the extended distance is preserved
  -- definitionally (its `edist` field is literally `edist`), and the extended distance of
  -- `PseudoEMetricSpace.ofRiemannianMetric` is `riemannianEDist I` by construction. So the
  -- predicate holds by `rfl`, exactly as for the extended structure it refines.
  exact ⟨fun _ _ ↦ rfl⟩

variable (I M) in
/-- The metric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `EMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory, one
should rather assume that there is an already existing metric space structure, satisfying
additionally the predicate `IsRiemannianManifold I M`. -/
@[reducible] def MetricSpace.ofRiemannianMetric [T3Space M] [PreconnectedSpace M] :
    MetricSpace M :=
  letI : EMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

/-- The distance of `MetricSpace.ofRiemannianMetric` is the infimum of the lengths of `C¹` paths,
i.e. the resulting metric space satisfies the `IsRiemannianManifold I M` predicate. -/
instance [T3Space M] [PreconnectedSpace M] :
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : MetricSpace M := MetricSpace.ofRiemannianMetric I M
  -- As above: `EMetricSpace.toMetricSpace` preserves the extended distance definitionally, and the
  -- extended distance of `EMetricSpace.ofRiemannianMetric` is `riemannianEDist I` by construction.
  exact ⟨fun _ _ ↦ rfl⟩

end OfRiemannianMetric

end TauCeti
