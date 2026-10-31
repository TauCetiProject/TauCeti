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
the approximating injective linear map `A`. This image lies in the `k`-plane `range A`, where
Lebesgue's density theorem gives density one almost everywhere
(`Isometry.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`). The distortion estimates
(`LipschitzOnWith.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le` and
`LipschitzOnWith.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div`) then bound the
upper and lower densities of `E` by `((1 + δ) / (1 - δ)) ^ (±k)` almost everywhere on each piece,
since the part of `E` outside the piece has density zero at almost every point of the
piece (`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`). Letting `δ → 0`
gives density one.

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

section Pieces

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {k : ℕ}

/-- Bounds on the densities of a subset `T` of the bi-Lipschitz image `ψ '' G` of a subset `G` of a
`k`-plane, at almost every point of `T`. -/
private theorem ae_limsup_le_and_le_liminf {ι : EuclideanSpace ℝ (Fin k) → X} (hι : Isometry ι)
    {G : Set X} (hGι : G ⊆ range ι) {ψ : X → Y} {a b : ℝ≥0} (hψ : LipschitzOnWith b ψ G)
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
        hψ'.le_mul_dist ⟨x, hG'G x.2⟩ ⟨y, hG'G y.2⟩
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

end Pieces

section Approximation

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {f : U → V} {P : Set U} {A : U →L[ℝ] V} {ε : ℝ≥0}

/-- A map within relative error `ε < 1` of an injective linear map `A` on `P`, read through `A`,
is `(1 + ε)`-Lipschitz on `A '' P` with `(1 - ε)⁻¹`-Lipschitz inverse. -/
private lemma lipschitzOnWith_and_antilipschitzWith_of_approx (hA : Injective A) (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    LipschitzOnWith (1 + ε) (f ∘ invFun A) (A '' P) ∧
      AntilipschitzWith (1 - ε)⁻¹ ((A '' P).domRestrict (f ∘ invFun A)) := by
  have hinv (x : U) : invFun A (A x) = x := leftInverse_invFun hA x
  have hε' : (0 : ℝ) < ((1 - ε : ℝ≥0) : ℝ) := NNReal.coe_pos.2 (tsub_pos_of_lt hε)
  refine ⟨LipschitzOnWith.of_dist_le_mul ?_, AntilipschitzWith.of_le_mul_dist ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := happ x hx y hy
    rw [map_sub] at h
    simp only [comp_apply, hinv, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
    calc ‖f x - f y‖ = ‖(f x - f y - (A x - A y)) + (A x - A y)‖ := by rw [sub_add_cancel]
      _ ≤ ε * ‖A x - A y‖ + ‖A x - A y‖ := norm_add_le_of_le h le_rfl
      _ = (1 + ε) * ‖A x - A y‖ := by ring
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    simp only [Subtype.dist_eq, domRestrict_apply, comp_apply, hinv, dist_eq_norm, NNReal.coe_inv]
    rw [le_inv_mul_iff₀ hε', NNReal.coe_sub hε.le, NNReal.coe_one]
    exact one_sub_mul_norm_sub_le_norm_sub happ hx hy

/-- A map within relative error `ε < 1` of an injective linear map on `P` is injective on `P`. -/
private lemma injOn_of_approx (hA : Injective A) (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) : InjOn f P := by
  intro x hx y hy hxy
  have h := one_sub_mul_norm_sub_le_norm_sub happ hx hy
  rw [hxy, sub_self, norm_zero] at h
  have hε' : (0 : ℝ) < 1 - ε := sub_pos.2 (by exact_mod_cast hε)
  exact hA (sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm
    (nonpos_of_mul_nonpos_right h hε') (norm_nonneg _))))

end Approximation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

omit [FiniteDimensional ℝ V] in
/-- On a piece `f '' P` where the Lipschitz map `f` is within relative error `ε < 1` of an injective
linear map, a set `E` of finite measure has its densities controlled almost everywhere: the part of
`E` in the piece has upper density at most `((1 - ε)⁻¹ (1 + ε)) ^ k` and lower density at least the
inverse, and the part of `E` off the piece has density zero. -/
private theorem ae_density_bounds_of_approx (hEm : NullMeasurableSet E μHE[k])
    (hfin : μHE[k] E ≠ ∞) {f : EuclideanSpace ℝ (Fin k) → V} {K : ℝ≥0} (hf : LipschitzWith K f)
    {P : Set (EuclideanSpace ℝ (Fin k))} (hPm : MeasurableSet P)
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] V} (hA : P.Nonempty → Injective A) {ε : ℝ≥0} (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    ∀ᵐ y ∂μHE[k], y ∈ E ∩ f '' P →
      limsup (fun r => μHE[k] (E ∩ f '' P ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
          (((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k ∧
      ((((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤
        liminf (fun r => μHE[k] (E ∩ f '' P ∩ closedBall y r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ∧
      Tendsto (fun r => μHE[k] (E \ f '' P ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · exact ae_of_all _ fun y hy => by simp at hy
  replace hA := hA hP
  obtain ⟨hlip, hanti⟩ := lipschitzOnWith_and_antilipschitzWith_of_approx hA hε happ
  obtain ⟨ι, hιA⟩ := (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] V).exists_linearIsometry_range_eq hA
  -- Read through `A`, the piece is a bi-Lipschitz image of the subset `A '' P` of a `k`-plane.
  have himage : (f ∘ invFun A) '' (A '' P) = f '' P := by
    rw [image_image]
    exact image_congr fun x _ => by rw [comp_apply, leftInverse_invFun hA x]
  have hdens := ae_limsup_le_and_le_liminf ι.isometry (hιA ▸ image_subset_range _ _) hlip hanti
    (inv_pos.2 (tsub_pos_of_lt hε)) (add_pos_of_pos_of_nonneg one_pos (by positivity))
    (T := E ∩ f '' P) (himage ▸ inter_subset_right)
  -- The part of `E` off the piece has density zero at almost every point of the piece.
  have hmeas : MeasurableSet (f '' P) :=
    hPm.image_of_continuousOn_injOn hf.continuous.continuousOn (injOn_of_approx hA hε happ)
  have hzero := ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div k
    (hEm.diff hmeas.nullMeasurableSet) (ne_top_of_le_ne_top hfin (measure_mono sdiff_subset))
  filter_upwards [hdens, hzero] with y h1 h2 hy
  exact ⟨(h1 hy).1, (h1 hy).2, h2 fun h => h.2 hy.2⟩

/-- The density theorem for a rectifiable set of finite measure. -/
private theorem CountablyRectifiable.ae_tendsto_of_ne_top (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) (hfin : μHE[k] E ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∈ E → Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  classical
  set D : Set V → V → ℝ → ℝ≥0∞ := fun S y r =>
    μHE[k] (S ∩ closedBall y r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
  obtain ⟨F, hF, hcover⟩ := hE.exists_lipschitzWith_cover
  choose KF hKF using hF
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
  choose P A hPm _ hAinj happ hPcover using fun n m =>
    (hKF m).exists_linear_approximation_cover (NNReal.coe_pos.2 (hε0 n))
  -- On each piece `F m '' P n m j`, the densities of `E` are controlled almost everywhere.
  have hpiece (n m j : ℕ) := ae_density_bounds_of_approx hEm hfin (hKF m) (hPm n m j)
    (hAinj n m j) (hε1 n) (happ n m j)
  -- Almost every point of `E` lies in a piece for every `n`.
  have hcov : ∀ᵐ y ∂μHE[k], y ∈ E → ∀ n, ∃ m j, y ∈ F m '' P n m j := by
    have h2 (n m : ℕ) : μHE[k] (range (F m) \ ⋃ j, F m '' P n m j) = 0 := by
      simpa only [finrank_euclideanSpace_fin] using hPcover n m
    rw [ae_iff]
    refine measure_mono_null ?_ (measure_union_null hcover
      (measure_iUnion_null fun n => measure_iUnion_null fun m => h2 n m))
    intro y hy
    obtain ⟨hyE, hy⟩ := not_imp.1 hy
    simp only [not_forall, not_exists] at hy
    obtain ⟨n, hn⟩ := hy
    by_cases hyF : y ∈ ⋃ m, range (F m)
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hyF
      exact Or.inr (mem_iUnion₂.2 ⟨n, m, hm, fun h => by
        obtain ⟨j, hj⟩ := mem_iUnion.1 h
        exact hn m j hj⟩)
    · exact Or.inl ⟨hyE, hyF⟩
  filter_upwards [hcov, ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun j =>
    hpiece n m j] with y hcovy hpy hyE
  have hbounds (n : ℕ) : limsup (D E y) (𝓝[>] 0) ≤ c n ∧ (c n)⁻¹ ≤ liminf (D E y) (𝓝[>] 0) := by
    obtain ⟨m, j, hy⟩ := hcovy hyE n
    obtain ⟨hsup, hinf, hzero⟩ := hpy n m j ⟨hyE, hy⟩
    refine ⟨?_, hinf.trans (liminf_le_liminf (Eventually.of_forall fun r => ?_))⟩
    · calc limsup (D E y) (𝓝[>] 0)
          ≤ limsup (D (E ∩ F m '' P n m j) y + D (E \ F m '' P n m j) y) (𝓝[>] 0) := by
            refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
            simp only [D, Pi.add_apply]
            rw [← ENNReal.add_div]
            gcongr
            refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
            by_cases hzF : z ∈ F m '' P n m j
            exacts [Or.inl ⟨⟨hz.1, hzF⟩, hz.2⟩, Or.inr ⟨⟨hz.1, hzF⟩, hz.2⟩]
        _ = limsup (D (E ∩ F m '' P n m j) y) (𝓝[>] 0) :=
            ENNReal.limsup_add_of_right_tendsto_zero hzero _
        _ ≤ c n := hsup
    · simp only [D]
      gcongr
      exact inter_subset_left
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact le_of_tendsto' (by simpa using tendsto_inv_iff.2 hclim) fun n => (hbounds n).2
  · exact ge_of_tendsto' hclim fun n => (hbounds n).1

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
