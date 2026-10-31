/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.MeasureTheory.Function.Jacobian.Decomposition

/-!
# The density theorem for rectifiable sets

Let `E` be a countably `k`-rectifiable subset of a finite-dimensional real inner product space,
measurable for the normalized Euclidean Hausdorff measure `μHE[k]`, with locally finite `μHE[k]`
measure. The **density theorem** states that `E` has `k`-dimensional density one at
`μHE[k]`-almost every point of `E`:

`μHE[k] (E ∩ closedBall x r) / (ω_k r ^ k) → 1` as `r → 0⁺`,

where `ω_k r ^ k` is the volume of a ball of radius `r` in `EuclideanSpace ℝ (Fin k)`
(`TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`).
Local finiteness cannot be dropped: in the plane, the union of the lines through pairs of points of
a countable dense set is countably `1`-rectifiable but has infinite `μHE[1]` measure in every ball.

The density theorem is the first step towards approximate tangent planes of rectifiable sets, and
the form in which the structure theorem for sets of finite perimeter identifies the perimeter
measure with Hausdorff measure on the reduced boundary.

## Main results

* `TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: the
  density theorem.

## The argument

Up to a null set, `E` is covered by images of Borel pieces on which a Lipschitz parametrization is
within a relative error `δ` of an injective linear map `A`
(`LipschitzWith.exists_linear_approximation_cover`). On each piece, the parametrization is
`(1 + δ)`-Lipschitz with `(1 - δ)⁻¹`-Lipschitz inverse when read from the image of the piece under
the approximating injective linear map `A`
(`TauCeti.lipschitzOnWith_and_antilipschitzWith_of_approx`).
This image lies in the `k`-plane `range A`, so the upper and lower densities of `E` on the piece
lie between `((1 + δ) / (1 - δ)) ^ (±k)` almost everywhere
(`Isometry.ae_limsup_le_and_le_liminf_euclideanHausdorffMeasure_inter_closedBall_div`), since the
part of `E` outside the piece has density zero at almost every point of the piece
(`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div` and
`TauCeti.limsup_measure_inter_div_le_of_tendsto_diff`). Letting `δ → 0` gives density one.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (the density of rectifiable sets).
* H. Federer, *Geometric Measure Theory*, 3.2.18 and 3.2.19 (decomposition of Lipschitz maps into
  pieces close to linear maps, and densities of rectifiable sets).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 16.2.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

omit [FiniteDimensional ℝ V] in
/-- On a piece `f '' P` where the Lipschitz map `f` is within relative error `ε < 1` of an injective
linear map, a set `E` of finite measure has upper density at most `((1 - ε)⁻¹ (1 + ε)) ^ k` and
lower density at least the inverse, at almost every point of `E ∩ f '' P`. -/
private theorem ae_density_bounds_of_approx (hEm : NullMeasurableSet E μHE[k])
    (hfin : μHE[k] E ≠ ∞) {f : EuclideanSpace ℝ (Fin k) → V} {K : ℝ≥0} (hf : LipschitzWith K f)
    {P : Set (EuclideanSpace ℝ (Fin k))} (hPm : MeasurableSet P)
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] V} (hA : P.Nonempty → Injective A) {ε : ℝ≥0} (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    ∀ᵐ y ∂μHE[k], y ∈ E ∩ f '' P →
      limsup (fun r => μHE[k] (E ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
          (((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k ∧
      ((((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤
        liminf (fun r => μHE[k] (E ∩ closedBall y r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · exact ae_of_all _ fun y hy => by simp at hy
  obtain ⟨L, hL⟩ := exists_antilipschitzWith_domRestrict_of_approx hA (by exact_mod_cast hε) happ
  replace hA := hA hP
  obtain ⟨hlip, hanti⟩ := lipschitzOnWith_and_antilipschitzWith_of_approx hA hε happ
  obtain ⟨ι, hιA⟩ := (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] V).exists_linearIsometry_range_eq hA
  -- Read through `A`, the piece is a bi-Lipschitz image of the subset `A '' P` of a `k`-plane.
  have himage : (f ∘ invFun A) '' (A '' P) = f '' P := by
    rw [image_image]
    exact image_congr fun x _ => by rw [comp_apply, leftInverse_invFun hA x]
  have hdens := ι.isometry.ae_limsup_le_and_le_liminf_euclideanHausdorffMeasure_inter_closedBall_div
    (hιA ▸ image_subset_range _ _) hlip hanti (inv_pos.2 (tsub_pos_of_lt hε))
    (add_pos_of_pos_of_nonneg one_pos (by positivity)) (T := E ∩ f '' P)
    (himage ▸ inter_subset_right)
  -- The part of `E` off the piece has density zero at almost every point of the piece.
  have hmeas : MeasurableSet (f '' P) :=
    hPm.image_of_continuousOn_injOn hf.continuous.continuousOn (injOn_iff_injective.2 hL.injective)
  have hzero := ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div k
    (hEm.diff hmeas.nullMeasurableSet) (ne_top_of_le_ne_top hfin (measure_mono sdiff_subset))
  filter_upwards [hdens, hzero] with y h1 h2 hy
  refine ⟨(limsup_measure_inter_div_le_of_tendsto_diff (h2 fun h => h.2 hy.2)).trans (h1 hy).1,
    (h1 hy).2.trans (liminf_le_liminf (Eventually.of_forall fun r => ?_))⟩
  gcongr
  exact inter_subset_left

/-- For a fixed relative error `0 < ε < 1`, a rectifiable set `E` of finite measure has upper
density at most `((1 - ε)⁻¹ (1 + ε)) ^ k` and lower density at least the inverse at almost every
point of `E`. -/
private theorem CountablyRectifiable.ae_density_bounds (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) (hfin : μHE[k] E ≠ ∞) {ε : ℝ≥0} (hε0 : 0 < ε)
    (hε : ε < 1) :
    ∀ᵐ y ∂μHE[k], y ∈ E →
      limsup (fun r => μHE[k] (E ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
          (((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k ∧
      ((((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤
        liminf (fun r => μHE[k] (E ∩ closedBall y r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
  obtain ⟨F, hF, hcover⟩ := hE.exists_lipschitzWith_cover
  choose KF hKF using hF
  choose P A hPm _ hAinj happ hPcover using fun m =>
    (hKF m).exists_linear_approximation_cover (NNReal.coe_pos.2 hε0)
  -- Almost every point of `E` lies in one of the pieces `F m '' P m j`.
  have hcov : μHE[k] (E \ ⋃ m, ⋃ j, F m '' P m j) = 0 := by
    have h (m : ℕ) : μHE[k] (range (F m) \ ⋃ j, F m '' P m j) = 0 := by
      simpa only [finrank_euclideanSpace_fin] using hPcover m
    refine measure_mono_null (fun y ⟨hyE, hy⟩ => ?_)
      (measure_union_null hcover (measure_iUnion_null h))
    by_cases hyF : y ∈ ⋃ m, range (F m)
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hyF
      exact Or.inr (mem_iUnion.2 ⟨m, hm, fun h' => hy (mem_iUnion.2 ⟨m, h'⟩)⟩)
    · exact Or.inl ⟨hyE, hyF⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 fun m => ae_all_iff.2 fun j =>
    ae_density_bounds_of_approx hEm hfin (hKF m) (hPm m j) (hAinj m j) hε (happ m j)]
    with y hcovy hpy hyE
  obtain ⟨m, j, hy⟩ := mem_iUnion₂.1 (not_not.1 fun h => hcovy ⟨hyE, h⟩)
  exact hpy m j ⟨hyE, hy⟩

/-- The density theorem for a rectifiable set of finite measure. -/
private theorem CountablyRectifiable.ae_tendsto_of_ne_top (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) (hfin : μHE[k] E ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∈ E → Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  -- Relative errors `ε n → 0` and the resulting distortion constants `c n → 1`.
  obtain ⟨ε, hε0, hε1, hεlim⟩ : ∃ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) ∧ (∀ n, ε n < 1) ∧
      Tendsto ε atTop (𝓝 0) := by
    refine ⟨fun n => ((n : ℝ≥0) + 1)⁻¹ / 2, fun n => by positivity, fun n => ?_, by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).div_const 2⟩
    calc ((n : ℝ≥0) + 1)⁻¹ / 2 ≤ 1 / 2 := by
          gcongr
          exact inv_le_one_of_one_le₀ le_add_self
      _ < 1 := by norm_num
  set c : ℕ → ℝ≥0∞ := fun n => (((1 - ε n)⁻¹ * (1 + ε n) : ℝ≥0) : ℝ≥0∞) ^ k
  have hclim : Tendsto c atTop (𝓝 1) := by
    have h : Tendsto (fun n => (1 - ε n)⁻¹ * (1 + ε n)) atTop (𝓝 ((1 - 0)⁻¹ * (1 + 0))) :=
      ((tendsto_const_nhds.sub hεlim).inv₀ (by simp)).mul (tendsto_const_nhds.add hεlim)
    have := ((ENNReal.continuous_pow k).tendsto _).comp ((ENNReal.continuous_coe.tendsto _).comp h)
    rwa [tsub_zero, inv_one, add_zero, mul_one, ENNReal.coe_one, one_pow] at this
  filter_upwards [ae_all_iff.2 fun n => hE.ae_density_bounds hEm hfin (hε0 n) (hε1 n)]
    with y hy hyE
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · have hinv := tendsto_inv_iff.2 hclim
    rw [inv_one] at hinv
    exact le_of_tendsto' hinv fun n => (hy n hyE).2
  · exact ge_of_tendsto' hclim fun n => (hy n hyE).1

/-- **The density theorem for rectifiable sets.** A countably `k`-rectifiable subset `E` of a
finite-dimensional real inner product space, measurable for `μHE[k]` and with locally finite
`μHE[k]` measure, has `k`-dimensional density one at `μHE[k]`-almost every point of `E`:
`μHE[k] (E ∩ closedBall x r) / (ω_k r ^ k) → 1` as `r → 0⁺`, where `ω_k r ^ k` is the volume of a
ball of radius `r` in `EuclideanSpace ℝ (Fin k)`. -/
theorem CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  -- Localize to the bounded pieces `E ∩ ball 0 n`, which have finite measure.
  have hfin (n : ℕ) : μHE[k] (E ∩ ball 0 n) ≠ ∞ := by
    rw [inter_comm, ← Measure.restrict_apply measurableSet_ball]
    exact measure_ball_lt_top.ne
  filter_upwards [ae_all_iff.2 fun n => (hE.mono inter_subset_left).ae_tendsto_of_ne_top
    (hEm.inter measurableSet_ball.nullMeasurableSet) (hfin n)] with x hx hxE
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hxn : x ∈ ball (0 : V) n := mem_ball_zero_iff.2 hn
  refine (hx n ⟨hxE, hxn⟩).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_closedBall_subset (isOpen_ball.mem_nhds hxn))] with r hr
  rw [inter_assoc, inter_eq_right.2 hr]

end TauCeti
