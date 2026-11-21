/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Broken
public import TauCeti.Topology.PathSpace.Moore.ArcStraightening
import TauCeti.Data.Fin.Basic

/-!
# Compact families of free loops are homotopic to broken geodesics through their samples

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r` be a radius
such that the tangent ball of radius `r` at every point is a normal domain. Abouzaid's
finite-dimensional approximation of the free loop space `𝓛M` compares a free loop `γ` with the
closed broken geodesic `geoⁿ (evₙ₊₁ γ)` through its `n + 1` equally spaced samples
`evₙ₊₁ γ = (γ 0, γ (L / (n + 1)), …, γ (n L / (n + 1)))`, `L` being the duration of `γ`
(`TauCeti.Manifold.sampleBrokenGeodesicLoop`). It is defined on the free loops whose `n + 1` arcs
are shorter than `r`, in the sense that every point of an arc is at distance less than `r` from the
initial vertex of the arc (`TauCeti.MooreFreeLoopSpace.arcsWithin`).

On these loops the inclusion is homotopic to `geoⁿ ∘ evₙ₊₁`
(`TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy`), through two homotopies.

* The first one straightens every arc to the minimizing geodesic between its end points, inside the
  normal ball around its initial vertex, keeping the duration `L` and the vertices
  (`TauCeti.MooreFreeLoopSpace.arcStraightening`, for the radial geodesics as path interpolation,
  `TauCeti.Manifold.isPathInterpolation_geodesicInterpolation`). It ends at the broken geodesic
  through the samples, each arc run in the time `L / (n + 1)`.
* The second one reparametrizes this broken path to the unit-speed broken geodesic `G = geoⁿ q`
  through the samples `q`, of length `d = ∑ᵢ d(qᵢ, qᵢ₊₁)`. The equally parametrized broken path is
  at its parameter `s` at the point of `G` of time `σ(s) = ∑ₖ d(qₖ, qₖ₊₁) clamp((n + 1) s - k)`, and
  at time `t` the homotopy runs along `s ↦ G((1 - t) σ(s) + t d s)` in the duration
  `(1 - t) L + t d`.

For a compact family `K` of free loops and cut-offs `δ` bounded below by a positive constant and
above by `r`, every sufficiently fine sampling maps `K` into the distance cut `𝓛ⁿM` of `δ`
(`TauCeti.MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut`), and the composite
`geoⁿ ∘ evₙ₊₁` on `K` is homotopic to the inclusion of `K`
(`TauCeti.Manifold.exists_homotopic_cyclicDistanceCutBrokenGeodesic_comp_sample`). This is the
compact-family approximation lemma. Applied to the image of a sphere, it is the input for the
surjectivity on homotopy groups of the map from the colimit of the distance cuts to the free loop
space.

No geometric length enters: the homotopies are stated for the duration of Moore loops, which is
continuous on `𝓛M`.

## Main definitions

* `TauCeti.Manifold.geodesicInterpolation`: the radial geodesics between points at distance less
  than `r`, as a path interpolation.
* `TauCeti.Manifold.sampleBrokenGeodesicLoop`: the map `γ ↦ geoⁿ (evₙ₊₁ γ)` on the free loops whose
  arcs are shorter than `r`.
* `TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy`: the homotopy from the inclusion to it.

## Main results

* `TauCeti.Manifold.isPathInterpolation_geodesicInterpolation`: radial geodesics interpolate.
* `TauCeti.Manifold.exists_homotopic_cyclicDistanceCutBrokenGeodesic_comp_sample`: the
  compact-family approximation lemma.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public section

open Bundle Manifold Metric Set
open TauCeti.MooreFreeLoopSpace (arcsWithin)
open unitInterval (arcPoint toNNReal)
open scoped ContDiff Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))

/-! ### Radial geodesics as a path interpolation -/

section Interpolation

include hr

/-- **The geodesic interpolation**: the radial geodesic `s ↦ exp_x (s • log_x y)` on the unit
interval from `x` to `y` when `dist x y < r`, and the constant path at `x` otherwise. On the pairs
at distance less than `r` it is a path interpolation
(`TauCeti.Manifold.isPathInterpolation_geodesicInterpolation`). -/
def geodesicInterpolation (p : M × M) : C(unitInterval, M) :=
  if h : dist p.1 p.2 < r then geodesicSegmentUnitPath hr ⟨p, h⟩ else ContinuousMap.const _ p.1

theorem geodesicInterpolation_of_dist_lt {p : M × M} (h : dist p.1 p.2 < r) :
    geodesicInterpolation hr p = geodesicSegmentUnitPath hr ⟨p, h⟩ :=
  dite_eq_left h

/-- **Radial geodesics interpolate** between the pairs of points at distance less than `r`. -/
theorem isPathInterpolation_geodesicInterpolation :
    IsPathInterpolation (geodesicInterpolation hr) {p : M × M | dist p.1 p.2 < r} where
  continuousOn := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((geodesicSegmentUnitPath hr).continuous.comp
      (continuous_subtypeVal.subtype_mk fun p ↦ p.property)).congr fun p ↦ ?_
    exact (geodesicInterpolation_of_dist_lt hr p.property).symm
  apply_zero p hp := by
    rw [geodesicInterpolation_of_dist_lt hr hp, geodesicSegmentUnitPath_zero]
  apply_one p hp := by
    rw [geodesicInterpolation_of_dist_lt hr hp, geodesicSegmentUnitPath_one]
  apply_diag x hx := by
    ext s
    rw [geodesicInterpolation_of_dist_lt hr hx, geodesicSegmentUnitPath_of_eq hr _ rfl,
      ContinuousMap.const_apply]

end Interpolation

/-! ### The unit-speed time of the equally parametrized broken path -/

section ArcTime

variable {n : ℕ}

/-- The time `∑ₖ d(qₖ, qₖ₊₁) clamp((n + 1) s - k)` at which the closed broken geodesic through `q`,
run at unit speed, is at the point of parameter `s` of the closed broken path through `q` whose
`n + 1` arcs are run in equal parameter intervals. -/
private def arcTime (q : Fin (n + 1) → M) (s : unitInterval) : ℝ≥0 :=
  ∑ k : Fin (n + 1), nndist (q k) (q (k + 1)) *
    toNNReal (projIcc 0 1 zero_le_one (((n + 1 : ℕ) : ℝ) * s - (k : ℕ)))

private theorem continuous_arcTime :
    Continuous fun p : (Fin (n + 1) → M) × unitInterval ↦ arcTime p.1 p.2 := by
  unfold arcTime
  fun_prop

/-- On the `i`-th arc, the closed broken geodesic is at the parameter `a` of the arc at the time
`d(q 0, q 1) + ⋯ + d(q (i - 1), q i) + a d(q i, q (i + 1))`. -/
private theorem arcTime_arcPoint (q : Fin (n + 1) → M) (i : Fin (n + 1)) (a : unitInterval) :
    arcTime q (arcPoint (n + 1) i a) =
      Fin.partialSum (fun k ↦ nndist (q k) (q (k + 1))) i.castSucc +
        nndist (q i) (q (i + 1)) * toNNReal a := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hterm : ∀ k : Fin (n + 1), nndist (q k) (q (k + 1)) *
      toNNReal (projIcc 0 1 zero_le_one
        (((n + 1 : ℕ) : ℝ) * (arcPoint (n + 1) i a : ℝ) - (k : ℕ))) =
      (if k ∈ Finset.Iio i then nndist (q k) (q (k + 1)) else 0) +
        if k = i then nndist (q k) (q (k + 1)) * toNNReal a else 0 := by
    intro k
    rw [unitInterval.coe_arcPoint i.isLt, mul_div_cancel₀ _ hn]
    rcases lt_trichotomy k i with h | rfl | h
    · have hki : ((k : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast Fin.lt_def.1 h
      rw [projIcc_of_right_le _ (by linarith [a.property.1]), ite_eq_left (Finset.mem_Iio.2 h),
        ite_eq_right h.ne]
      simp
    · rw [add_sub_cancel_left, projIcc_val, ite_eq_right (by simp), ite_eq_left rfl,
        zero_add]
    · have hik : ((i : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast Fin.lt_def.1 h
      rw [projIcc_of_le_left _ (by linarith [a.property.2]), ite_eq_right (by simpa using h.le),
        ite_eq_right h.ne']
      simp
  rw [arcTime, Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ, ite_eq_left (Finset.mem_univ _), Fintype.sum_ite_mem,
    Fin.partialSum_castSucc]

private theorem arcTime_zero (q : Fin (n + 1) → M) : arcTime q 0 = 0 := by
  simpa using arcTime_arcPoint q 0 0

/-- At the end of the parameter interval the time is the length of the closed broken geodesic. -/
private theorem arcTime_one (q : Fin (n + 1) → M) :
    arcTime q 1 = ∑ k, nndist (q k) (q (k + 1)) := by
  have h := arcTime_arcPoint q (Fin.last n) 1
  rw [Fin.val_last, unitInterval.arcPoint_one, unitInterval.arcPoint_self_zero n.succ_pos,
    unitInterval.toNNReal_one, mul_one, ← Fin.partialSum_succ, Fin.succ_last,
    Fin.partialSum_last] at h
  exact h

/-- If the closed broken geodesic through `q` has length zero, the time is constantly zero. -/
private theorem arcTime_eq_zero (q : Fin (n + 1) → M) (h : ∑ k, nndist (q k) (q (k + 1)) = 0)
    (s : unitInterval) : arcTime q s = 0 := by
  rw [Finset.sum_eq_zero_iff] at h
  exact Finset.sum_eq_zero fun k hk ↦ by rw [h k hk, zero_mul]

end ArcTime

/-! ### Broken geodesics through the samples of a free loop -/

section Sample

variable (n : ℕ)

include hr

/-- **The broken geodesics through the samples**, `γ ↦ geoⁿ (evₙ₊₁ γ)`: the closed broken geodesic
through the `n + 1` equally spaced samples of a free loop whose `n + 1` arcs are shorter than `r`,
as a continuous map to the free loop space. -/
def sampleBrokenGeodesicLoop :
    C(arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1),
      MooreFreeLoopSpace M) where
  toFun γ := brokenGeodesicLoop hr n ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
    (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property)
  continuous_toFun := (continuous_brokenGeodesicLoop hr n).comp
    (((MooreFreeLoopSpace.continuous_sample _).comp continuous_subtypeVal).subtype_mk
      fun γ ↦ MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property)

@[simp]
theorem sampleBrokenGeodesicLoop_apply
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    sampleBrokenGeodesicLoop hr n γ =
      brokenGeodesicLoop hr n ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
        (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property) :=
  (rfl)

/-- The length of the broken geodesic through the samples is the sum of the distances between
consecutive samples, the last one followed by the first one. -/
theorem length_sampleBrokenGeodesicLoop
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (sampleBrokenGeodesicLoop hr n γ).length =
      ∑ k, nndist ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) k)
        ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) (k + 1)) := by
  rw [sampleBrokenGeodesicLoop_apply, length_brokenGeodesicLoop_eq_partialSum,
    Fin.partialSum_last]

/-- The length of the broken geodesic through the samples varies continuously with the loop. -/
theorem continuous_length_sampleBrokenGeodesicLoop :
    Continuous fun γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
      (sampleBrokenGeodesicLoop hr n γ).length :=
  MooreFreeLoopSpace.continuous_length.comp (sampleBrokenGeodesicLoop hr n).continuous

/-- The broken geodesic through the samples of a free loop of duration zero has length zero. -/
private theorem length_sampleBrokenGeodesicLoop_eq_zero
    {γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)}
    (h : (γ : MooreFreeLoopSpace M).length = 0) : (sampleBrokenGeodesicLoop hr n γ).length = 0 := by
  rw [length_sampleBrokenGeodesicLoop]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  simp [MoorePath.sample_apply, h]

/-- The equally parametrized broken path through the samples of a free loop, along radial
geodesics, is the unit-speed broken geodesic through the samples, reparametrized by `arcTime`. -/
private theorem sampleBrokenGeodesicLoop_apply_arcTime
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) (s : unitInterval) :
    (sampleBrokenGeodesicLoop hr n γ).toMoorePath
        (arcTime ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1)) s) =
      brokenPath (geodesicInterpolation hr) (n + 1)
        (γ : MooreFreeLoopSpace M).toMoorePath.toUnitPath s := by
  obtain ⟨i, a, rfl⟩ : ∃ (i : Fin (n + 1)) (a : unitInterval), arcPoint (n + 1) i a = s :=
    ⟨⟨_, unitInterval.arcIndex_lt n.succ_pos s⟩, _,
      unitInterval.arcPoint_arcIndex_arcParam n.succ_pos s⟩
  have hγ := MooreFreeLoopSpace.mem_arcsWithin.1 γ.property
  -- The end points of the `i`-th arc of the unit-interval path are the samples `i` and `i + 1`.
  have hi : (γ : MooreFreeLoopSpace M).toMoorePath.toUnitPath (arcPoint (n + 1) i 0) =
      (γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) i :=
    (MoorePath.sample_eq_toUnitPath_arcPoint _ i).symm
  have hi' : (γ : MooreFreeLoopSpace M).toMoorePath.toUnitPath (arcPoint (n + 1) (i + 1) 0) =
      (γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) (i + 1) := by
    rw [← unitInterval.arcPoint_one, MooreFreeLoopSpace.sample_add_one_eq_toUnitPath_arcPoint]
  rw [arcTime_arcPoint, brokenPath_arcPoint_of_arcsWithin
      (isPathInterpolation_geodesicInterpolation hr) hγ i.isLt a,
    sampleBrokenGeodesicLoop_apply, brokenGeodesicLoop_apply_partialSum_add hr n _ _ i
      (mul_le_of_le_one_right zero_le (by exact_mod_cast a.property.2)),
    geodesicSegment_apply_nndist_mul, hi, hi', geodesicInterpolation_of_dist_lt hr
      (dist_add_one_lt_of_forall_dist_sub_one_lt
        (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property) i)]

/-! ### Reparametrizing the broken path to unit speed -/

/-- The time of the reparametrization at time `t`: the convex combination
`(1 - t) σ(s) + t d s` of the time `σ(s)` at which the unit-speed broken geodesic is at the point of
parameter `s` of the equally parametrized one and of the time `d s`, `d` being its length. -/
private def reparamTime (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) (s : unitInterval) : ℝ≥0 :=
  toNNReal (unitInterval.symm t) *
      arcTime ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1)) s +
    toNNReal t * ((sampleBrokenGeodesicLoop hr n γ).length * toNNReal s)

/-- The duration of the reparametrization at time `t`: the convex combination of the duration of
the loop and of the length of the broken geodesic through its samples. -/
private def reparamLength (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) : ℝ≥0 :=
  toNNReal (unitInterval.symm t) * (γ : MooreFreeLoopSpace M).length +
    toNNReal t * (sampleBrokenGeodesicLoop hr n γ).length

private theorem continuous_reparamTime :
    Continuous fun p : (unitInterval × arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1))
      × unitInterval ↦ reparamTime hr n p.1.1 p.1.2 p.2 := by
  have hσ := (continuous_arcTime (M := M) (n := n)).comp
    ((((MooreFreeLoopSpace.continuous_sample _).comp continuous_subtypeVal).comp
      (continuous_snd.comp continuous_fst)).prodMk
    (continuous_snd : Continuous fun p : (unitInterval × MooreFreeLoopSpace.arcsWithin
      {p : M × M | dist p.1 p.2 < r} (n + 1)) × unitInterval ↦ p.2))
  unfold reparamTime
  exact ((by fun_prop : Continuous _).mul hσ).add ((by fun_prop : Continuous _).mul
    (((continuous_length_sampleBrokenGeodesicLoop hr n).comp
      (continuous_snd.comp continuous_fst)).mul (by fun_prop)))

private theorem continuous_reparamLength :
    Continuous fun p : unitInterval × arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
      reparamLength hr n p.1 p.2 := by
  unfold reparamLength
  exact ((by fun_prop : Continuous _).mul
    (MooreFreeLoopSpace.continuous_length.comp (continuous_subtypeVal.comp continuous_snd))).add
    ((by fun_prop : Continuous _).mul
      ((continuous_length_sampleBrokenGeodesicLoop hr n).comp continuous_snd))

private theorem reparamTime_zero (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    reparamTime hr n t γ 0 = 0 := by
  simp [reparamTime, arcTime_zero]

private theorem reparamTime_one (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    reparamTime hr n t γ 1 = (sampleBrokenGeodesicLoop hr n γ).length := by
  rw [reparamTime, arcTime_one, ← length_sampleBrokenGeodesicLoop hr n γ,
    unitInterval.toNNReal_one, mul_one,
    ← add_mul, unitInterval.toNNReal_symm_add_toNNReal, one_mul]

/-- Where the duration of the reparametrization vanishes, so does its time. -/
private theorem reparamTime_eq_zero {t : unitInterval}
    {γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)}
    (h : reparamLength hr n t γ = 0) (s : unitInterval) : reparamTime hr n t γ s = 0 := by
  rw [reparamLength, add_eq_zero, mul_eq_zero, mul_eq_zero] at h
  -- The broken geodesic through the samples has length zero: either the loop has duration zero,
  -- or `t = 1`.
  have hd : (sampleBrokenGeodesicLoop hr n γ).length = 0 := by
    rcases h with ⟨h₁ | h₁, h₂ | h₂⟩
    · have h₁₂ := unitInterval.toNNReal_add_toNNReal_symm t
      rw [h₁, h₂, add_zero] at h₁₂
      exact absurd h₁₂ zero_ne_one
    · exact h₂
    · exact length_sampleBrokenGeodesicLoop_eq_zero hr n h₁
    · exact h₂
  rw [reparamTime, arcTime_eq_zero _ (by rw [← length_sampleBrokenGeodesicLoop hr n γ, hd]), hd]
  simp

/-- The reparametrized broken path on the unit interval, as a continuous map of the time, the loop
and the parameter. -/
private def reparamUnitPath :
    C((unitInterval × arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) × unitInterval, M) where
  toFun p := (sampleBrokenGeodesicLoop hr n p.1.2).toMoorePath (reparamTime hr n p.1.1 p.1.2 p.2)
  continuous_toFun := MoorePath.continuous_eval.comp
    (((MooreFreeLoopSpace.continuous_toMoorePath.comp
      (sampleBrokenGeodesicLoop hr n).continuous).comp
        (continuous_snd.comp continuous_fst)).prodMk (continuous_reparamTime hr n))

private theorem reparamUnitPath_apply (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) (s : unitInterval) :
    reparamUnitPath hr n ((t, γ), s) =
      (sampleBrokenGeodesicLoop hr n γ).toMoorePath (reparamTime hr n t γ s) :=
  (rfl)

/-- The reparametrization homotopy, as Moore paths: at time `t` the Moore path of duration
`reparamLength t γ` running along `s ↦ G (reparamTime t γ s)`, `G` being the broken geodesic
through the samples of `γ`. -/
private def reparamMap :
    C(unitInterval × arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1), MoorePath M) where
  toFun p := (MoorePath.ofUnitPath ((reparamUnitPath hr n).curry p)).rescale
    (reparamLength hr n p.1 p.2)
  continuous_toFun := by
    refine (MoorePath.continuous_ofUnitPath.comp (reparamUnitPath hr n).curry.continuous)
      |>.moorePath_rescale_of_forall_eq_source (continuous_reparamLength hr n) fun p hp s ↦ ?_
    -- Where the duration vanishes, the time vanishes, and the path is constant.
    obtain ⟨t, γ⟩ := p
    simp only [Function.comp_apply, MoorePath.ofUnitPath_apply, MoorePath.source_ofUnitPath,
      ContinuousMap.curry_apply]
    rw [reparamUnitPath_apply, reparamUnitPath_apply, reparamTime_eq_zero hr n hp,
      reparamTime_eq_zero hr n hp]

private theorem reparamMap_apply (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    reparamMap hr n (t, γ) =
      (MoorePath.ofUnitPath ((reparamUnitPath hr n).curry (t, γ))).rescale
        (reparamLength hr n t γ) :=
  (rfl)

/-- The reparametrization homotopy keeps the loops closed. -/
private theorem target_reparamMap (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (reparamMap hr n (t, γ)).target = (reparamMap hr n (t, γ)).source := by
  rw [reparamMap_apply]
  rcases eq_or_ne (reparamLength hr n t γ) 0 with h | h
  · rw [h, MoorePath.rescale_zero, MoorePath.target_refl, MoorePath.source_refl]
  · rw [MoorePath.target_rescale _ h, MoorePath.source_rescale, MoorePath.target_ofUnitPath,
      MoorePath.source_ofUnitPath, ContinuousMap.curry_apply, ContinuousMap.curry_apply,
      reparamUnitPath_apply, reparamUnitPath_apply, reparamTime_one, reparamTime_zero,
      ← MooreFreeLoopSpace.length_toMoorePath, ← MoorePath.target_def, ← MoorePath.source_def,
      MooreFreeLoopSpace.target_toMoorePath, MooreFreeLoopSpace.source_toMoorePath]

/-- The reparametrization homotopy, as free Moore loops. -/
private def reparamLoopMap :
    C(unitInterval × arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1),
      MooreFreeLoopSpace M) where
  toFun p := ⟨reparamMap hr n p, target_reparamMap hr n p.1 p.2⟩
  continuous_toFun := MooreFreeLoopSpace.isEmbedding_toMoorePath.continuous_iff.2
    (reparamMap hr n).continuous

private theorem toMoorePath_reparamLoopMap (t : unitInterval)
    (γ : arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (reparamLoopMap hr n (t, γ)).toMoorePath = reparamMap hr n (t, γ) :=
  (rfl)

/-- **Reparametrizing the broken path to unit speed**: on the free loops whose arcs are shorter than
`r`, a homotopy from the broken loops through the samples along radial geodesics, with arcs run in
equal times, to the unit-speed broken geodesics through the samples. -/
private def reparamHomotopy :
    ContinuousMap.Homotopy
      (MooreFreeLoopSpace.brokenPathMap (isPathInterpolation_geodesicInterpolation hr) n.succ_pos)
      (sampleBrokenGeodesicLoop hr n) where
  toContinuousMap := reparamLoopMap hr n
  map_zero_left γ := by
    ext1
    rw [ContinuousMap.toFun_eq_coe, toMoorePath_reparamLoopMap,
      MooreFreeLoopSpace.toMoorePath_brokenPathMap,
      ← MoorePath.ofUnitPath_toUnitPath_rescale_length (MoorePath.brokenPathMap _ _ _),
      reparamMap_apply]
    congr 2
    · ext s
      rw [ContinuousMap.curry_apply, reparamUnitPath_apply, MoorePath.toUnitPath_brokenPathMap,
        MooreFreeLoopSpace.coe_toArcsWithin, ← sampleBrokenGeodesicLoop_apply_arcTime]
      simp [reparamTime]
    · simp [reparamLength]
  map_one_left γ := by
    ext1
    rw [ContinuousMap.toFun_eq_coe, toMoorePath_reparamLoopMap,
      ← MoorePath.ofUnitPath_toUnitPath_rescale_length
        (sampleBrokenGeodesicLoop hr n γ).toMoorePath,
      reparamMap_apply]
    congr 2
    · ext s
      rw [ContinuousMap.curry_apply, reparamUnitPath_apply, MoorePath.toUnitPath_apply]
      simp [reparamTime]
    · simp [reparamLength]

/-- **Free loops with short arcs are homotopic to the broken geodesics through their samples**: on
the free loops whose `n + 1` arcs are shorter than `r`, a homotopy from the inclusion to
`γ ↦ geoⁿ (evₙ₊₁ γ)`. It first straightens the arcs to radial geodesics keeping their times, then
reparametrizes the resulting broken path to unit speed. -/
def sampleBrokenGeodesicLoopHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.subtypeVal _) (sampleBrokenGeodesicLoop hr n) :=
  (MooreFreeLoopSpace.arcStraightening (isPathInterpolation_geodesicInterpolation hr)
    n.succ_pos).trans (reparamHomotopy hr n)

end Sample

/-! ### Compact families -/

section Compact

include hr

/-- **The compact-family approximation of the free loop space by broken geodesics.** Let `K` be a
compact family of free loops in `M` and `ε > 0`. There is `N` such that for every `n ≥ N` and all
cut-offs `ε ≤ δ i < r`, the samples `evₙ₊₁` map `K` into the distance cut `𝓛ⁿM` of `δ`, and the
composite `geoⁿ ∘ evₙ₊₁ : K → 𝓛M` with the closed broken geodesics
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`) is homotopic to the inclusion of `K`. -/
theorem exists_homotopic_cyclicDistanceCutBrokenGeodesic_comp_sample
    {K : Set (MooreFreeLoopSpace M)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ : Fin (n + 1) → ℝ, (∀ i, ε ≤ δ i) → ∀ hδ : ∀ i, δ i < r,
      ∃ hKδ : MapsTo (fun γ : MooreFreeLoopSpace M ↦ γ.toMoorePath.sample (n + 1)) K
          (cyclicDistanceCut δ),
        ((cyclicDistanceCutBrokenGeodesic hr hδ).comp
          ⟨hKδ.restrict, (MooreFreeLoopSpace.continuous_sample _).restrict hKδ⟩).Homotopic
          (ContinuousMap.subtypeVal K) := by
  rcases le_or_gt r ε with hrε | hrε
  · -- No cut-offs lie between `ε` and `r`.
    exact ⟨0, fun n _ δ hεδ hδ ↦ absurd ((hεδ 0).trans_lt (hδ 0)) hrε.not_gt⟩
  obtain ⟨N₁, -, hN₁⟩ := MoorePath.exists_subset_arcsWithin
    (hK.image MooreFreeLoopSpace.continuous_toMoorePath)
    (Metric.dist_mem_uniformity (hε.trans hrε))
  obtain ⟨N₂, hN₂⟩ := MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut hK hε
  refine ⟨max N₁ N₂, fun n hn δ hεδ hδ ↦ ⟨hN₂ n (le_of_max_le_right hn) δ hεδ, ?_⟩⟩
  have hKU : K ⊆ arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) :=
    fun γ hγ ↦ MooreFreeLoopSpace.mem_arcsWithin.2
      (MoorePath.mem_arcsWithin.1 (hN₁ (n + 1) (by omega) ⟨γ, hγ, rfl⟩))
  let g : C(K, arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :=
    ⟨inclusion hKU, continuous_inclusion hKU⟩
  exact ⟨(((sampleBrokenGeodesicLoopHomotopy hr n).compContinuousMap g).cast
    (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun γ ↦ by simp [g])).symm⟩

end Compact

end TauCeti.Manifold
