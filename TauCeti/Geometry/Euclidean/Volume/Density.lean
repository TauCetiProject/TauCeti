/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Covering.EssentialBoundary.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Densities for the Euclidean Hausdorff measure under bi-Lipschitz maps and in `k`-planes

The `k`-dimensional density of a set `S` in a metric space at a point `x` compares
`μHE[k] (S ∩ closedBall x r)` with `ω_k r ^ k`, the volume of a ball of radius `r` in
`EuclideanSpace ℝ (Fin k)`. This file proves general facts about these densities, none of which
involves rectifiability:

* a map that is `b`-Lipschitz on `G` with `a`-Lipschitz inverse moves a point of density one of `G`
  to a point of `ψ '' G` whose upper and lower densities lie between `(a b) ^ (-k)` and
  `(a b) ^ k`;
* **Lebesgue's density theorem in a `k`-plane**: every subset of an isometric copy of
  `EuclideanSpace ℝ (Fin k)` has density one at almost every one of its points. This is
  transported from Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`;
* combining the two, every subset of a bi-Lipschitz image of a subset of a `k`-plane has its
  densities between `(a b) ^ (-k)` and `(a b) ^ k` almost everywhere;
* removing a part of density zero from a set does not lower its upper density;
* along an antilipschitz map out of a finite-dimensional real inner product space, source volume is
  controlled by target `μHE[dim U]` measure, transferring vanishing density quotients back to the
  source, while at a Lebesgue density-one point shifted sub-balls cannot have density tending to
  zero (yielding directional derivative bounds under `LipschitzOnWith`), an inverse-Lipschitz
  differentiable parametrization has positive directional lower Hausdorff density along `range A`
  (forcing `range A` into every density-zero cone), and a set of positive upper ambient density
  cannot have density zero outside every cone around a proper subspace.

Together with the zero-density theorem
`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`, these are the ingredients of
the density theorem, approximate tangent plane uniqueness, and tangential differentiation on
rectifiable sets.

## Main results

* `LipschitzOnWith.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le` and
  `LipschitzOnWith.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div`: densities under
  bi-Lipschitz maps.
* `Isometry.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: Lebesgue's density theorem
  for subsets of an isometric copy of `k`-dimensional Euclidean space.
* `Isometry.ae_limsup_le_and_le_liminf_euclideanHausdorffMeasure_inter_closedBall_div`: density
  bounds almost everywhere on a bi-Lipschitz image of a subset of a `k`-plane.
* `TauCeti.limsup_measure_inter_div_le_of_tendsto_diff`: a part of a set with density zero does not
  contribute to the upper density.
* `TauCeti.volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith`,
  `TauCeti.tendsto_volume_inter_closedBall_div_of_mem_nhds`,
  `TauCeti.tendsto_volume_div_zero_of_antilipschitzWith`,
  `TauCeti.not_tendsto_volume_inter_shifted_closedBall_div_zero`,
  `TauCeti.not_tendsto_outside_cone_top_of_lt_top`, and
  `HasFDerivWithinAt.norm_comp_le_of_lipschitzOnWith`: antilipschitz volume comparison,
  neighborhood density one, density-zero pullback, non-vanishing shifted-ball density,
  proper-subspace cone obstruction, and the resulting density-one directional derivative bound.
* `HasFDerivWithinAt.liminf_euclideanHausdorffMeasure_directional_closedBall_pos`,
  `HasFDerivWithinAt.limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos`, and
  `HasFDerivWithinAt.range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div`: directional
  lower and upper Hausdorff density and cone containment of derivative ranges in normed targets.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §§11–12.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapters 15–16.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal Pointwise Topology

namespace TauCeti

/-- Scaling the radius of a closed ball in `EuclideanSpace ℝ (Fin k)` by `c ≥ 0` scales its volume
by `c ^ k`. -/
private lemma volume_closedBall_mul (k : ℕ) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (c * r)) =
      ENNReal.ofReal c ^ k * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
  rw [addHaar_closedBall_mul volume 0 hc hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hc]

/-- Rescaling the radius in a `k`-dimensional density quotient. -/
theorem div_volume_closedBall_eq_mul (k : ℕ) (m : ℝ≥0∞) {c : ℝ≥0} (hc : 0 < c) {r : ℝ}
    (hr : 0 ≤ r) :
    m / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) =
      (c : ℝ≥0∞) ^ k * (m / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (c * r))) := by
  rw [volume_closedBall_mul k c.coe_nonneg hr, ENNReal.ofReal_coe_nnreal, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (ENNReal.coe_ne_zero.2 hc.ne'))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)]

/-- Discarding a part of `E` whose density quotients tend to zero does not lower the upper
density: if `μ (E \ S ∩ t r) / d r → 0`, then the limsup of `μ (E ∩ t r) / d r` is at most that of
`μ (E ∩ S ∩ t r) / d r`. -/
theorem limsup_measure_inter_div_le_of_tendsto_diff {α X : Type*} [MeasurableSpace X]
    {μ : Measure X} {E S : Set X} {t : α → Set X} {d : α → ℝ≥0∞} {l : Filter α}
    (h : Tendsto (fun r => μ (E \ S ∩ t r) / d r) l (𝓝 0)) :
    limsup (fun r => μ (E ∩ t r) / d r) l ≤ limsup (fun r => μ (E ∩ S ∩ t r) / d r) l :=
  calc limsup (fun r => μ (E ∩ t r) / d r) l
      ≤ limsup (fun r => μ (E ∩ S ∩ t r) / d r + μ (E \ S ∩ t r) / d r) l := by
        refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
        rw [← ENNReal.add_div]
        gcongr
        refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
        by_cases hzS : z ∈ S
        exacts [Or.inl ⟨⟨hz.1, hzS⟩, hz.2⟩, Or.inr ⟨⟨hz.1, hzS⟩, hz.2⟩]
    _ = _ := ENNReal.limsup_add_of_right_tendsto_zero h _

/-- Along an `L`-antilipschitz restriction `s.domRestrict f`,
`volume t ≤ L ^ dim U * μHE[dim U] (f '' t)` for any `t ⊆ s`. -/
theorem volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U]
    [BorelSpace U] [MetricSpace V] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s t : Set U}
    {L : ℝ≥0} (hi : AntilipschitzWith L (s.domRestrict f)) (hts : t ⊆ s) :
    volume t ≤ (L : ℝ≥0∞) ^ finrank ℝ U * μHE[finrank ℝ U] (f '' t) := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact (AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [Subtype.dist_eq, domRestrict_apply] using
      hi.le_mul_dist ⟨x, hts x.property⟩ ⟨y, hts y.property⟩ :
    AntilipschitzWith L (t.domRestrict f)).le_euclideanHausdorffMeasure_image_of_domRestrict _

/-- Every neighborhood `s ∈ 𝓝 x` has density one at `x` with respect to a locally finite additive
Haar volume measure. -/
theorem tendsto_volume_inter_closedBall_div_of_mem_nhds {E : Type*} [NormedAddCommGroup E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    [IsLocallyFiniteMeasure (volume : Measure E)] {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall (0 : E) r))
      (𝓝[>] 0) (𝓝 1) :=
  (hasDensityAt_iff.mp (hasDensityAt_one_of_mem_nhds (μ := volume) hs)).congr
    fun _ => by rw [addHaar_closedBall_center]

/-- At a Lebesgue density-one point `x₀` of `s`, shifted sub-balls
`closedBall (x₀ + (ρ / 2) • u) ((η / 4) * ρ)` cannot have density in `s` tending to zero. -/
theorem not_tendsto_volume_inter_shifted_closedBall_div_zero {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] {s : Set U}
    {x₀ u : U} {η : ℝ}
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1)) (hu : ‖u‖ = 1) (hη0 : 0 < η) (hη_half : η ≤ 1 / 2) :
    ¬ Tendsto (fun ρ => volume (s ∩ closedBall (x₀ + (ρ / 2) • u) ((η / 4) * ρ)) /
        volume (closedBall (0 : U) ρ)) (𝓝[>] 0) (𝓝 0) := by
  intro hD0; have : Nontrivial U := ⟨⟨u, 0, fun h => by simp [h] at hu⟩⟩
  set D := fun ρ => closedBall (x₀ + (ρ / 2) • u) ((η / 4) * ρ)
  let V₀ (ρ : ℝ) := volume (closedBall (0 : U) ρ)
  set α : ℝ≥0∞ := ENNReal.ofReal (η / 4) ^ finrank ℝ U
  have hineq : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      volume (s ∩ closedBall x₀ ρ) / V₀ ρ + α ≤ volume (s ∩ D ρ) / V₀ ρ + 1 := by
    filter_upwards [eventually_mem_nhdsWithin] with ρ (hρ0 : 0 < ρ)
    have hD_sub : D ρ ⊆ closedBall x₀ ρ := fun x hx => mem_closedBall.mpr <| by
      have h2 : dist (x₀ + (ρ / 2) • u) x₀ = ρ / 2 := by
        simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ρ / 2), hu]
      linarith [mem_closedBall.mp hx, h2, dist_triangle x (x₀ + (ρ / 2) • u) x₀,
        mul_le_mul_of_nonneg_right hη_half hρ0.le]
    have hV_pos : 0 < V₀ ρ := measure_closedBall_pos volume 0 hρ0
    have hV_top : V₀ ρ ≠ ∞ := measure_closedBall_lt_top.ne
    have hadd : volume (s ∩ closedBall x₀ ρ) + α * V₀ ρ ≤ volume (s ∩ D ρ) + V₀ ρ := by
      rw [← (by rw [addHaar_closedBall_center, addHaar_closedBall_mul volume 0 (by positivity)
        hρ0.le, ENNReal.ofReal_pow (by positivity)] : volume (D ρ) = α * V₀ ρ)]
      dsimp only [V₀]; rw [← addHaar_closedBall_center volume x₀, ← sdiff_union_of_subset hD_sub,
        measure_union disjoint_sdiff_self_left measurableSet_closedBall, ← add_assoc]
      gcongr; refine le_trans (measure_mono ?_) (measure_union_le _ _); rintro x ⟨hxs, hxB⟩
      exact hxB.elim Or.inr (fun h => Or.inl ⟨hxs, h⟩)
    simpa only [ENNReal.add_div, ENNReal.mul_div_cancel_right hV_pos.ne' hV_top,
      ENNReal.div_self hV_pos.ne' hV_top] using ENNReal.div_le_div_right hadd (V₀ ρ)
  exact (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity : 0 < η / 4))
      (finrank ℝ U)).not_ge <| (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp <| by
    simpa only [zero_add, add_zero] using le_of_tendsto_of_tendsto (hdens.add tendsto_const_nhds)
      (hD0.add tendsto_const_nhds) hineq

/-- Along an `L`-antilipschitz restriction `s.domRestrict f`, if `f '' (s ∩ A ρ) ⊆ T (C * ρ)`
eventually and `T` has zero `(finrank ℝ U)`-dimensional density at `0`, then
`volume (s ∩ A ρ) / volume (closedBall (0 : U) ρ) → 0`. -/
theorem tendsto_volume_div_zero_of_antilipschitzWith {U V : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
    [MetricSpace V] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U} {L C : ℝ≥0}
    (hi : AntilipschitzWith L (s.domRestrict f)) (hC : 0 < C) {A : ℝ → Set U} {T : ℝ → Set V}
    (hT : Tendsto (fun r => μHE[finrank ℝ U] (T r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hinc : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), f '' (s ∩ A ρ) ⊆ T (C * ρ)) :
    Tendsto (fun ρ => volume (s ∩ A ρ) / volume (closedBall (0 : U) ρ)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (hT.comp (tendsto_iff_comap.2 (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 hC)).ge))
      (Or.inr (ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := L * C)) (n := finrank ℝ U))))
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_mem_nhdsWithin, hinc] with ρ (hρ0 : 0 < ρ) hsub
  rw [volume_closedBall_eq_of_finrank_eq finrank_euclideanSpace_fin.symm (0 : U) 0 ρ]
  refine (ENNReal.div_le_div_right
    ((volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hi
      inter_subset_left).trans (mul_le_mul' le_rfl (measure_mono hsub))) _).trans_eq ?_
  rw [mul_div_assoc, div_volume_closedBall_eq_mul (finrank ℝ U) _ hC hρ0.le, ← mul_assoc, ← mul_pow,
    ← ENNReal.coe_mul]; rfl

private lemma euclideanHausdorffMeasure_closedBall_slab_div_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (x : V)
    (K₀ : Submodule ℝ V) (ε r : ℝ) (hr : 0 < r) :
    μHE[finrank ℝ V] {z ∈ closedBall x r | infDist (z - x) (K₀ : Set V) ≤ ε * r} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r) ≤
      volume {w ∈ closedBall (0 : V) 1 | infDist w (K₀ : Set V) ≤ ε} /
        volume (closedBall (0 : V) 1) := by
  let S : Set V := {w ∈ closedBall (0 : V) 1 | infDist w (K₀ : Set V) ≤ ε}
  have hinc : {z ∈ closedBall x r | infDist (z - x) (K₀ : Set V) ≤ ε * r} ⊆
      (IsometryEquiv.vaddConst x) '' (r • S) := fun z ⟨hzB, hzK⟩ => by
    refine ⟨z - x, ⟨r⁻¹ • (z - x), ⟨?_, ?_⟩, smul_inv_smul₀ hr.ne' (z - x)⟩,
      by simp [IsometryEquiv.vaddConst]⟩
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
        ← dist_eq_norm]
      exact (inv_mul_le_iff₀ hr).mpr (by simpa using mem_closedBall.mp hzB)
    · rw [← K₀.dist_starProjection_eq_infDist, dist_eq_norm, map_smul, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ← dist_eq_norm,
        K₀.dist_starProjection_eq_infDist]
      exact (inv_mul_le_iff₀ hr).mpr (by linarith)
  refine (ENNReal.div_le_div_right (measure_mono hinc) _).trans_eq ?_
  rw [(IsometryEquiv.vaddConst x).isometry.euclideanHausdorffMeasure_image,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume, addHaar_smul_of_nonneg volume hr.le,
    ← volume_closedBall_eq_of_finrank_eq finrank_euclideanSpace_fin.symm (0 : V) 0 r, (by
      simpa only [mul_one, ENNReal.ofReal_pow hr.le] using addHaar_closedBall_mul volume (0 : V)
        hr.le zero_le_one : volume (closedBall (0 : V) r) = ENNReal.ofReal (r ^ finrank ℝ V) *
          volume (closedBall (0 : V) 1)), ENNReal.mul_div_mul_left _ _
      (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' ENNReal.ofReal_ne_top]

/-- A set `E` of positive upper `(finrank ℝ V)`-dimensional density at `x` cannot have density zero
outside every cone around a proper subspace `K₀ < ⊤`. -/
theorem not_tendsto_outside_cone_top_of_lt_top {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {E : Set V}
    {x : V} {K₀ : Submodule ℝ V} (hK₀ : K₀ < ⊤)
    (hpos : 0 < limsup (fun r => μHE[finrank ℝ V] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ V] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (K₀ : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)) (𝓝[>] 0) (𝓝 0)) :
    False := by
  let S (ε : ℝ) : Set V := {w ∈ closedBall (0 : V) 1 | infDist w (K₀ : Set V) ≤ ε}
  let B₀ (r : ℝ) := volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ V))) r)
  have hlimsup_le (ε : ℝ) (hε : 0 < ε) :
      limsup (fun r => μHE[finrank ℝ V] (E ∩ closedBall x r) / B₀ r) (𝓝[>] 0) ≤
        volume (S ε) / volume (closedBall (0 : V) 1) := by
    refine ((limsup_le_limsup (.of_forall fun r => ?_)).trans_eq
      (ENNReal.limsup_add_of_right_tendsto_zero (hcone ε hε) _)).trans
      ((limsup_le_limsup (eventually_mem_nhdsWithin.mono
        (euclideanHausdorffMeasure_closedBall_slab_div_le x K₀ ε))).trans_eq (limsup_const _))
    dsimp only [Pi.add_apply, B₀]; rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ((measure_mono ?_).trans (measure_union_le _ _)) _
    rintro z ⟨hzE, hzr⟩
    by_cases hz : ε * dist z x < infDist (z - x) (K₀ : Set V)
    exacts [Or.inr ⟨⟨hzE, hzr⟩, hz⟩,
      Or.inl ⟨hzr, (not_lt.mp hz).trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp hzr) hε.le)⟩]
  let seq (n : ℕ) : Set V := S (1 / ((n : ℝ) + 1))
  have htend : Tendsto (volume ∘ seq) atTop (𝓝 0) :=
    (measure_mono_null (fun w hw => (K₀.isClosed_of_finiteDimensional.mem_iff_infDist_zero ⟨0,
      K₀.zero_mem⟩).mpr <| le_antisymm (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat
      fun n => (mem_iInter.mp hw n : w ∈ S _).2) infDist_nonneg) (addHaar_submodule volume K₀
        hK₀.ne)) ▸ tendsto_measure_iInter_atTop
      (fun _ => (measurableSet_closedBall.inter (isClosed_le (continuous_infDist_pt (K₀ : Set V))
        continuous_const).measurableSet).nullMeasurableSet)
      (fun _ _ hmn _ hw => ⟨hw.1, hw.2.trans (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hmn 1))⟩)
      ⟨0, ((measure_mono (fun _ (h : _ ∈ seq 0) => h.1)).trans_lt measure_closedBall_lt_top).ne⟩
  have hV1_pos : 0 < volume (closedBall (0 : V) 1) := measure_closedBall_pos volume 0 zero_lt_one
  exact (ENNReal.mul_pos hpos.ne' hV1_pos.ne').not_ge <| ge_of_tendsto' htend fun _ =>
    (ENNReal.le_div_iff_mul_le (.inl hV1_pos.ne') (.inl measure_closedBall_lt_top.ne)).mp
      (hlimsup_le _ Nat.one_div_pos_of_nat)

end TauCeti

/-- Directional bound `‖B v‖ ≤ K * ‖A v‖` at a Lebesgue density-one point under
`LipschitzOnWith`. -/
theorem HasFDerivWithinAt.norm_comp_le_of_lipschitzOnWith {U V W : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → V} {s : Set U} {A : U →L[ℝ] V} {u₀ : U}
    {E : Set V} {g : V → W} {B : U →L[ℝ] W} {K : ℝ≥0}
    (hf : HasFDerivWithinAt f A s u₀) (hu₀ : u₀ ∈ s) (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall u₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hgf : HasFDerivWithinAt (g ∘ f) B s u₀) (hg : LipschitzOnWith K g E) (v : U) :
    ‖B v‖ ≤ K * ‖A v‖ := by
  by_cases hv0 : v = 0; · simp [hv0]
  let w : U := ‖v‖⁻¹ • v; have hw : ‖w‖ = 1 := norm_smul_inv_norm hv0
  let η (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hη_half (n : ℕ) : η n ≤ 1 / 2 :=
    one_div_le_one_div_of_le zero_lt_two (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hex (n : ℕ) :
      ∃ ρ ∈ Ioo 0 (η n), (s ∩ closedBall (u₀ + (ρ / 2) • w) ((η n / 4) * ρ)).Nonempty := by
    by_contra! hemp
    exact TauCeti.not_tendsto_volume_inter_shifted_closedBall_div_zero hdens hw (by positivity)
      (hη_half n) (tendsto_const_nhds.congr' (Filter.mem_of_superset
        (Ioo_mem_nhdsGT (by positivity : 0 < η n)) fun ρ hρ => by simp [hemp ρ hρ]))
  choose ρ hρ u husD using hex; let d (n : ℕ) : U := u n - u₀
  let c (n : ℕ) : ℝ := ‖v‖ * (ρ n / 2)⁻¹
  have hy (n : ℕ) : ‖d n - (ρ n / 2) • w‖ ≤ (η n / 4) * ρ n := by
    simpa only [d, dist_eq_norm, sub_sub] using mem_closedBall.mp (husD n).2
  have htend_η : Tendsto η atTop (𝓝 0) := by
    simpa only [η, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      using tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hdlim : Tendsto d atTop (𝓝 0) := squeeze_zero_norm (fun n => calc
    ‖d n‖ = ‖(d n - (ρ n / 2) • w) + (ρ n / 2) • w‖ := by abel_nf
    _ ≤ (η n / 4) * ρ n + (ρ n / 2) * 1 := (norm_add_le _ _).trans (add_le_add (hy n)
        (by rw [norm_smul, Real.norm_of_nonneg (half_pos (hρ n).1).le, hw]))
    _ ≤ η n := by nlinarith [hη_half n, (hρ n).1, (hρ n).2]) htend_η
  have hcd : Tendsto (fun n => c n • d n) atTop (𝓝 v) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun n => ?_) (by simpa using htend_η.const_mul (‖v‖ / 2))
    have hρ0 := (hρ n).1; have hc0 : 0 ≤ c n := by positivity
    nth_rw 1 [← (by simp only [c, w, smul_smul, mul_assoc]; rw [inv_mul_cancel_left₀ (half_pos
      hρ0).ne', mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul] : c n • ((ρ n / 2) • w) = v)]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (hy n) hc0).trans_eq (by simp only [c]; field_simp; ring)
  have hdtop : ∀ᶠ n in atTop, u₀ + d n ∈ s := .of_forall fun n => by simpa [d] using (husD n).1
  exact le_of_tendsto_of_tendsto (hgf.lim hdlim hdtop hcd).norm ((hf.lim hdlim hdtop
    hcd).norm.const_mul (K : ℝ)) <| .of_forall fun n => by
      dsimp only; rw [norm_smul, norm_smul, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa only [comp_apply, ← dist_eq_norm] using hg.dist_le_mul _ (hsub (mem_image_of_mem f
        (by simpa [d] using (husD n).1))) _ (hsub (mem_image_of_mem f hu₀))

namespace LipschitzOnWith

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {ψ : X → Y} {G : Set X} {a b : ℝ≥0} {k : ℕ} {x : X}

/-- **Upper density under a bi-Lipschitz map.** Let `ψ` be `b`-Lipschitz on `G` with
`a`-Lipschitz inverse. If `G` has `k`-dimensional density one at `x ∈ G`, then the upper
`k`-dimensional density of `ψ '' G` at `ψ x` is at most `(a b) ^ k`. -/
theorem limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le
    (hψ : LipschitzOnWith b ψ G) (hψ' : AntilipschitzWith a (G.domRestrict ψ)) (ha : 0 < a)
    (hx : x ∈ G)
    (hG : Tendsto (fun r => μHE[k] (G ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1)) :
    limsup (fun r => μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
        ((a * b : ℝ≥0) : ℝ≥0∞) ^ k := by
  have hlim : Tendsto (fun r => ((a * b : ℝ≥0) : ℝ≥0∞) ^ k *
      (μHE[k] (G ∩ closedBall x (a * r)) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (a * r)))) (𝓝[>] 0)
      (𝓝 (((a * b : ℝ≥0) : ℝ≥0∞) ^ k)) := by
    have := ENNReal.Tendsto.const_mul
      (hG.comp (tendsto_iff_comap.2 (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 ha)).ge))
      (Or.inr (ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := a * b)) (n := k)))
    rwa [mul_one] at this
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) => ?_)
  -- A point of `ψ '' G` within `r` of `ψ x` is the image of a point of `G` within `a r` of `x`.
  have hsub : ψ '' G ∩ closedBall (ψ x) r ⊆ ψ '' (G ∩ closedBall x (a * r)) := by
    rintro _ ⟨⟨x', hx', rfl⟩, hd⟩
    refine ⟨x', ⟨hx', ?_⟩, rfl⟩
    have h := hψ'.le_mul_dist ⟨x', hx'⟩ ⟨x, hx⟩
    rw [Subtype.dist_eq] at h
    rw [mem_closedBall] at hd ⊢
    exact h.trans (by gcongr; exact hd)
  calc μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
      ≤ (b : ℝ≥0∞) ^ k * μHE[k] (G ∩ closedBall x (a * r)) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
        gcongr
        exact (measure_mono hsub).trans
          ((hψ.mono inter_subset_left).euclideanHausdorffMeasure_image_le k)
    _ = _ := by
        rw [mul_div_assoc, TauCeti.div_volume_closedBall_eq_mul k _ ha hr.le]
        push_cast
        ring

/-- **Lower density under a bi-Lipschitz map.** Let `ψ` be `b`-Lipschitz on `G` with
`a`-Lipschitz inverse. If `G` has `k`-dimensional density one at `x ∈ G`, then the lower
`k`-dimensional density of `ψ '' G` at `ψ x` is at least `(a b) ^ (-k)`. -/
theorem le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div
    (hψ : LipschitzOnWith b ψ G) (hψ' : AntilipschitzWith a (G.domRestrict ψ)) (ha : 0 < a)
    (hb : 0 < b) (hx : x ∈ G)
    (hG : Tendsto (fun r => μHE[k] (G ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1)) :
    (((a * b : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤ liminf (fun r => μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
  have hab : ((a * b : ℝ≥0) : ℝ≥0∞) ^ k ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  rw [ENNReal.inv_le_iff_le_mul (fun _ => pow_ne_zero _ (ENNReal.coe_ne_zero.2 (mul_pos ha hb).ne'))
      (fun h => absurd h hab),
    ← ENNReal.liminf_const_mul_of_ne_top hab]
  -- The inverse of `ψ` on `ψ '' G` is `a`-Lipschitz.
  classical
  have : Nonempty X := ⟨x⟩
  have hinj : InjOn ψ G := injOn_iff_injective.2 hψ'.injective
  have hφ : LipschitzOnWith a (invFunOn ψ G) (ψ '' G) :=
    lipschitzOnWith_iff_restrict.2 (hψ'.to_rightInvOn' (fun _ hy => invFunOn_mem hy)
      fun _ hy => invFunOn_eq hy)
  have hlim := hG.comp (tendsto_iff_comap.2
    (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 (inv_pos.2 hb))).ge)
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) => ?_)
  -- Points of `G` within `r / b` of `x` are mapped within `r` of `ψ x`.
  have hr' : (b : ℝ) * ((b⁻¹ : ℝ≥0) * r) = r := by
    rw [NNReal.coe_inv, mul_inv_cancel_left₀ (NNReal.coe_pos.2 hb).ne']
  set S := G ∩ closedBall x ((b⁻¹ : ℝ≥0) * r)
  have hS : ψ '' S ⊆ ψ '' G ∩ closedBall (ψ x) r := by
    rintro _ ⟨x', ⟨hx', hd⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hx', ?_⟩
    rw [mem_closedBall] at hd ⊢
    calc dist (ψ x') (ψ x) ≤ b * dist x' x := hψ.dist_le_mul x' hx' x hx
      _ ≤ b * ((b⁻¹ : ℝ≥0) * r) := by gcongr
      _ = r := hr'
  have hmeas : μHE[k] S ≤ (a : ℝ≥0∞) ^ k * μHE[k] (ψ '' G ∩ closedBall (ψ x) r) :=
    calc μHE[k] S = μHE[k] (invFunOn ψ G '' (ψ '' S)) := by
          rw [hinj.leftInvOn_invFunOn.image_image' inter_subset_left]
      _ ≤ (a : ℝ≥0∞) ^ k * μHE[k] (ψ '' S) :=
          (hφ.mono (image_mono inter_subset_left)).euclideanHausdorffMeasure_image_le k
      _ ≤ _ := by gcongr
  dsimp only [comp_apply]
  rw [TauCeti.div_volume_closedBall_eq_mul k _ hb (by positivity), hr']
  calc _ ≤ (b : ℝ≥0∞) ^ k * ((a : ℝ≥0∞) ^ k * μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) := by gcongr
    _ = _ := by
        rw [mul_div_assoc]
        push_cast
        ring

end LipschitzOnWith

namespace Isometry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

/-- **Lebesgue's density theorem in a `k`-plane.** Let `ι` be an isometry from `k`-dimensional
Euclidean space into `X`. Every subset `S` of its range has `k`-dimensional density one at
`μHE[k]`-almost every point of `S`. No measurability of `S` is needed. -/
theorem ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    {ι : EuclideanSpace ℝ (Fin k) → X} (hι : Isometry ι) {S : Set X} (hS : S ⊆ range ι) :
    ∀ᵐ x ∂μHE[k], x ∈ S → Tendsto (fun r => μHE[k] (S ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  set T := ι ⁻¹' S
  -- Balls about points of the range of `ι` meet `S` in isometric images of balls meeting `T`.
  have key (z : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
      μHE[k] (S ∩ closedBall (ι z) r) = volume (T ∩ closedBall z r) := by
    have : S ∩ closedBall (ι z) r = ι '' (T ∩ closedBall z r) := by
      ext y
      constructor
      · rintro ⟨hy, hyr⟩
        obtain ⟨w, rfl⟩ := hS hy
        exact ⟨w, ⟨hy, by rwa [mem_closedBall, ← hι.dist_eq]⟩, rfl⟩
      · rintro ⟨w, ⟨hw, hwr⟩, rfl⟩
        exact ⟨hw, by rwa [mem_closedBall, hι.dist_eq]⟩
    rw [this, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hT := ae_iff.1 (Besicovitch.ae_tendsto_measure_inter_div volume T)
  have hN := nonpos_iff_eq_zero.1 ((le_restrict_apply T _).trans_eq hT)
  rw [ae_iff]
  have himg (N : Set (EuclideanSpace ℝ (Fin k))) (h : volume N = 0) : μHE[k] (ι '' N) = 0 := by
    rwa [hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  refine measure_mono_null ?_ (himg _ hN)
  intro y hy
  replace hy := not_imp.1 hy
  obtain ⟨z, rfl⟩ := hS hy.1
  refine ⟨z, ⟨fun h => hy.2 (h.congr fun r => ?_), hy.1⟩, rfl⟩
  rw [key, addHaar_closedBall_center volume z r]

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Densities of a bi-Lipschitz image of a subset of a `k`-plane.** Let `ι` be an isometry from
`k`-dimensional Euclidean space into `X`, and let `ψ` be `b`-Lipschitz on a subset `G` of its range
with `a`-Lipschitz inverse. Then every subset `T` of `ψ '' G` has upper density at most `(a b) ^ k`
and lower density at least `(a b) ^ (-k)` at `μHE[k]`-almost every point of `T`. -/
theorem ae_limsup_le_and_le_liminf_euclideanHausdorffMeasure_inter_closedBall_div
    {ι : EuclideanSpace ℝ (Fin k) → X} (hι : Isometry ι) {G : Set X} (hGι : G ⊆ range ι)
    {ψ : X → Y} {a b : ℝ≥0} (hψ : LipschitzOnWith b ψ G)
    (hψ' : AntilipschitzWith a (G.domRestrict ψ)) (ha : 0 < a) (hb : 0 < b) {T : Set Y}
    (hT : T ⊆ ψ '' G) :
    ∀ᵐ y ∂μHE[k], y ∈ T →
      limsup (fun r => μHE[k] (T ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
          ((a * b : ℝ≥0) : ℝ≥0∞) ^ k ∧
      (((a * b : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤ liminf (fun r => μHE[k] (T ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
  -- `T` is the image of the part `G'` of `G` that `ψ` maps into `T`.
  obtain ⟨G', hG'G, rfl⟩ : ∃ G' ⊆ G, ψ '' G' = T := by
    refine ⟨G ∩ ψ ⁻¹' T, inter_subset_left, Subset.antisymm ?_ fun y hy => ?_⟩
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · obtain ⟨x, hx, rfl⟩ := hT hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hψ₁ := hψ.mono hG'G
  have hψ₁' : AntilipschitzWith a (G'.domRestrict ψ) :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      simpa only [Subtype.dist_eq, domRestrict_apply] using
        hψ'.le_mul_dist ⟨x, hG'G x.property⟩ ⟨y, hG'G y.property⟩
  have hdens := ae_iff.1 (hι.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    (hG'G.trans hGι))
  -- The image of the points of `G'` where `G'` does not have density one is null.
  have himg (N : Set X) (hN : N ⊆ G') (h0 : μHE[k] N = 0) : μHE[k] (ψ '' N) = 0 :=
    nonpos_iff_eq_zero.1 (((hψ₁.mono hN).euclideanHausdorffMeasure_image_le k).trans_eq
      (by rw [h0, mul_zero]))
  rw [ae_iff]
  refine measure_mono_null ?_
    (himg _ inter_subset_right (measure_mono_null inter_subset_left hdens))
  intro y hy
  obtain ⟨⟨x, hx, rfl⟩, hy⟩ := not_imp.1 hy
  exact ⟨x, ⟨fun h => hy ⟨hψ₁.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le
    hψ₁' ha hx (h hx), hψ₁.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div
      hψ₁' ha hb hx (h hx)⟩, hx⟩, rfl⟩

end Isometry

namespace HasFDerivWithinAt

section DirectionalDensity

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {E : Set V} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
  [BorelSpace V] in
private lemma exists_pos_forall_norm_apply_add_smul_sub_le (hf : HasFDerivWithinAt f A s x₀)
    (u : U) {c η₀ : ℝ} (hc0 : 0 ≤ c) (hη₀ : 0 < η₀) (hcA : ‖A‖ * c ≤ η₀ / 2) :
    ∃ ρ > 0, ∀ r ∈ Ioo 0 ρ, ∀ w ∈ closedBall u c, x₀ + r • w ∈ s →
      ‖f (x₀ + r • w) - f x₀ - r • A u‖ ≤ r * η₀ := by
  set R₀ := ‖u‖ + c + 1
  have hR₀ : 0 < R₀ := by positivity
  -- Choose `δ` so the first-order Taylor error on `s ∩ ball x₀ δ` is at most `(η₀ / (2 R₀))`.
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp (hf.isLittleO.bound (div_pos hη₀ (mul_pos two_pos hR₀))))
  refine ⟨δ / R₀, div_pos hδ hR₀, fun r ⟨hr0, hrδ⟩ w hw hxs => ?_⟩
  have hwu : ‖w - u‖ ≤ c := mem_closedBall_iff_norm.1 hw
  have hwR : ‖w‖ ≤ R₀ := by
    have := (norm_add_le u (w - u)).trans (add_le_add_right hwu ‖u‖)
    rw [add_sub_cancel] at this; dsimp [R₀]; linarith
  have hxδ : x₀ + r • w ∈ ball x₀ δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
    exact (mul_le_mul_of_nonneg_left hwR hr0.le).trans_lt ((lt_div_iff₀ hR₀).1 hrδ)
  -- Combine the Taylor remainder `h1` and the linear perturbation `h2` around `A u`.
  have h1 : ‖f (x₀ + r • w) - f x₀ - A (r • w)‖ ≤ r * (η₀ / 2) := by
    have hb := hδb (x₀ + r • w) hxδ hxs
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwR hr0.le)
      (by positivity)).trans_eq (by field_simp))
  have h2 : ‖A (r • w) - r • A u‖ ≤ r * (η₀ / 2) := by
    rw [← map_smul, ← map_sub, ← smul_sub, map_smul, norm_smul, Real.norm_of_nonneg hr0.le]
    exact mul_le_mul_of_nonneg_left
      ((A.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hwu (norm_nonneg _)).trans hcA)) hr0.le
  exact (by congr 1; abel : ‖f (x₀ + r • w) - f x₀ - r • A u‖ =
    ‖(f (x₀ + r • w) - f x₀ - A (r • w)) + (A (r • w) - r • A u)‖).trans_le
    ((norm_add_le _ _).trans (by linarith))

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
  [BorelSpace V] in
private lemma image_inter_smul_closedBall_subset (hf : HasFDerivWithinAt f A s x₀)
    (hfs : f '' s ⊆ E) {u : U} (hu : ‖A u‖ < 1) {η c : ℝ} (hη : 0 < η)
    (hc0 : 0 ≤ c) (hcA : ‖A‖ * c ≤ min η (1 - ‖A u‖) / 2) :
    ∃ ρ > 0, ∀ r ∈ Ioo 0 ρ, f '' (s ∩ ({x₀} + r • closedBall u c)) ⊆
      {z ∈ E ∩ closedBall (f x₀) r | ‖z - f x₀ - r • A u‖ ≤ r * η} := by
  obtain ⟨ρ, hρ, herr⟩ :=
    hf.exists_pos_forall_norm_apply_add_smul_sub_le u hc0 (lt_min hη (sub_pos.2 hu)) hcA
  refine ⟨ρ, hρ, fun r hr _ => ?_⟩
  -- Unpack membership in `{x₀} + r • closedBall u c` via `singleton_add` and `mem_smul_set`.
  rintro ⟨_, ⟨hxs, hxB⟩, rfl⟩
  rw [singleton_add, mem_image] at hxB
  obtain ⟨_, hz, rfl⟩ := hxB
  obtain ⟨w, hw, rfl⟩ := mem_smul_set.1 hz
  have hle := herr r hr w hw hxs
  refine ⟨⟨hfs (mem_image_of_mem f hxs), ?_⟩,
    hle.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hr.1.le)⟩
  -- Bound `‖f (x₀ + r • w) - f x₀‖ ≤ r` from `‖A u‖ + (1 - ‖A u‖) = 1`.
  rw [mem_closedBall, dist_eq_norm]
  calc ‖f (x₀ + r • w) - f x₀‖ = ‖r • A u + (f (x₀ + r • w) - f x₀ - r • A u)‖ := by congr 1; abel
    _ ≤ ‖r • A u‖ + ‖f (x₀ + r • w) - f x₀ - r • A u‖ := norm_add_le _ _
    _ ≤ r * ‖A u‖ + r * (1 - ‖A u‖) := by
        rw [norm_smul, Real.norm_of_nonneg hr.1.le]
        exact add_le_add le_rfl (hle.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hr.1.le))
    _ = r := by ring

/-- **Directional lower Hausdorff density of an inverse-Lipschitz differentiable image** along
`A u` (`‖A u‖ < 1`, `η > 0`). -/
theorem liminf_euclideanHausdorffMeasure_directional_closedBall_pos
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f))
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {u : U} (hu : ‖A u‖ < 1) {η : ℝ} (hη : 0 < η) :
    0 < liminf (fun r => μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r |
      ‖z - f x₀ - r • A u‖ ≤ r * η} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) := by
  set k := finrank ℝ U
  set c : ℝ := min η (1 - ‖A u‖) / (2 * (‖A‖ + 1))
  have hc : 0 < c := div_pos (lt_min hη (sub_pos.2 hu)) (by positivity)
  have hcA : ‖A‖ * c ≤ min η (1 - ‖A u‖) / 2 :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hc.le).trans_eq
      (by dsimp [c]; field_simp)
  set c' : ℝ≥0 := Real.toNNReal c
  have hc' : 0 < c' := Real.toNNReal_pos.2 hc
  obtain ⟨ρ, hρ, hsub⟩ := hf.image_inter_smul_closedBall_subset hfs hu hη hc.le hcA
  set B := closedBall u c
  set M : ℝ → Set V := fun r => {z ∈ E ∩ closedBall (f x₀) r | ‖z - f x₀ - r • A u‖ ≤ r * η}
  have hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1) := hdens.congr fun _ => by rw [addHaar_closedBall_center volume x₀]
  have hlim : Tendsto (fun r : ℝ => (c' : ℝ≥0∞) ^ k *
      (volume (s ∩ ({x₀} + r • B)) / volume ({x₀} + r • B))) (𝓝[>] 0) (𝓝 ((c' : ℝ≥0∞) ^ k)) := by
    simpa only [mul_one] using ENNReal.Tendsto.const_mul
      (tendsto_addHaar_inter_smul_one_of_density_one volume s x₀ hs B measurableSet_closedBall
        (measure_closedBall_pos volume u hc).ne' measure_closedBall_lt_top.ne)
      (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
  have hineq : (c' : ℝ≥0∞) ^ k ≤ (L : ℝ≥0∞) ^ k *
      liminf (fun r => μHE[k] (M r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r))
        (𝓝[>] 0) := by
    rw [← ENNReal.liminf_const_mul_of_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      ← hlim.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    have hvol : volume (s ∩ ({x₀} + r • B)) ≤ (L : ℝ≥0∞) ^ k * μHE[k] (M r) :=
      (TauCeti.volume_le_mul_euclideanHausdorffMeasure_image_of_antilipschitzWith hi
        inter_subset_left).trans (by gcongr; exact hsub r hr)
    have hvolB : volume ({x₀} + r • B) =
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (c * r)) := by
      rw [show ({x₀} : Set U) + r • B = closedBall (x₀ + r • u) (c * r) by
          rw [smul_closedBall' hr.1.ne', Real.norm_of_nonneg hr.1.le, mul_comm r c, singleton_add]
          simpa only [← image_vadd, vadd_eq_add] using Metric.vadd_closedBall x₀ (r • u) (c * r),
        TauCeti.volume_closedBall_eq_of_finrank_eq finrank_euclideanSpace_fin.symm _ 0 _]
    rw [hvolB, ← Real.coe_toNNReal c hc.le,
      ← TauCeti.div_volume_closedBall_eq_mul k _ hc' hr.1.le, ← mul_div_assoc]; gcongr
  refine pos_iff_ne_zero.2 fun h0 => (ENNReal.pow_pos (ENNReal.coe_pos.2 hc') k).ne' ?_
  rw [h0, mul_zero, nonpos_iff_eq_zero] at hineq; exact hineq

/-- Positive upper `(dim U)`-density of `E` at `f x₀` on an inverse-Lipschitz patch. -/
theorem limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f))
    (hsub : f '' s ⊆ E)
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1)) :
    0 < limsup (fun r => μHE[finrank ℝ U] (E ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) :=
  (hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hdens hsub (u := 0) (by simp)
    zero_lt_one).trans_le ((liminf_le_limsup).trans (limsup_le_limsup
      (Eventually.of_forall fun _ => by gcongr; exact sep_subset _ _)))

/-- **Derivative range lies in every density-zero cone.** If `E` contains `f '' s` and has
`(finrank ℝ U)`-density zero outside every cone around a closed subspace `P`, then `range A ≤ P`. -/
theorem range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f))
    (hdens : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall (0 : U) r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {P : Submodule ℝ V} (hP : IsClosed (P : Set V))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r | ε * dist z (f x₀) <
        infDist (z - f x₀) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    LinearMap.range A.toLinearMap ≤ P := by
  rintro _ ⟨u₀, rfl⟩; by_contra hu₀P
  have hpos : 0 < ‖A u₀‖ := norm_pos_iff.2 fun h0 => hu₀P (h0 ▸ P.zero_mem)
  set u := (2 * ‖A u₀‖)⁻¹ • u₀
  have hAu_norm : ‖A u‖ < 1 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
    have : (2 * ‖A u₀‖)⁻¹ * ‖A u₀‖ = 1 / 2 := by field_simp
    linarith
  have hAuP : A u ∉ (P : Set V) := fun hmem => hu₀P <| by
    have : (2 * ‖A u₀‖) • A u = A u₀ := by rw [map_smul, smul_inv_smul₀ (by positivity)]
    exact this ▸ P.smul_mem _ hmem
  set d := infDist (A u) (P : Set V)
  have hd : 0 < d := (hP.notMem_iff_infDist_pos ⟨0, P.zero_mem⟩).1 hAuP
  have hlow := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hdens hfs
    hAu_norm (show 0 < d / 3 by positivity)
  refine hlow.ne' (le_antisymm ((hcone (d / 3) (by positivity)).liminf_eq ▸ liminf_le_liminf ?_)
    zero_le)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hinc : {z ∈ E ∩ closedBall (f x₀) r | ‖z - f x₀ - r • A u‖ ≤ r * (d / 3)} ⊆
      {z ∈ E ∩ closedBall (f x₀) r | d / 3 * dist z (f x₀) < infDist (z - f x₀) (P : Set V)} := by
    rintro z ⟨hzE, hzd⟩; refine ⟨hzE, ?_⟩
    have hrd : r * d ≤ infDist (r • A u) (P : Set V) :=
      (le_infDist ⟨0, P.zero_mem⟩).2 fun p hp => by
        have h1 : d ≤ dist (A u) (r⁻¹ • p) := infDist_le_dist_of_mem (P.smul_mem r⁻¹ hp)
        rw [show dist (r • A u) p = r * dist (A u) (r⁻¹ • p) by
          rw [dist_eq_norm, dist_eq_norm, ← smul_inv_smul₀ hr.ne' p, ← smul_sub,
            inv_smul_smul₀ hr.ne', norm_smul, Real.norm_of_nonneg hr.le]]
        exact mul_le_mul_of_nonneg_left h1 hr.le
    have hdist_u : dist (r • A u) (z - f x₀) ≤ r * (d / 3) := by rwa [dist_comm, dist_eq_norm]
    calc d / 3 * dist z (f x₀)
        ≤ r * (d / 3) := mul_comm (d / 3) r ▸
            mul_le_mul_of_nonneg_left (mem_closedBall.1 hzE.2) (by positivity)
      _ < r * d - r * (d / 3) := by linarith [mul_pos hr hd, (by ring : r * (d / 3) = r * d / 3)]
      _ ≤ infDist (r • A u) (P : Set V) - dist (r • A u) (z - f x₀) := sub_le_sub hrd hdist_u
      _ ≤ infDist (z - f x₀) (P : Set V) :=
          sub_le_iff_le_add.2 (infDist_le_infDist_add_dist (x := r • A u) (y := z - f x₀) (s := P))
  gcongr

end DirectionalDensity

end HasFDerivWithinAt
