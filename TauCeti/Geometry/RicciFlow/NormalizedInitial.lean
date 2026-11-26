/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CurvatureNorm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.SmallBalls
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Rescale
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Norm.Operator
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Normalized initial Riemannian metrics

A compact Hausdorff boundaryless smooth manifold admits a metric with full Riemann curvature
norm at most one, curvature endomorphism bounded below by minus the identity on every bivector,
and at least
half the Euclidean ball volume at every intrinsic radius at most one. Any supplied metric
can be brought into this normalization by an arbitrarily large constant rescaling.

The normalization conditions follow J. Morgan and G. Tian, *Ricci Flow and the Poincaré
Conjecture*, Definition 4.10, with the curvature operator in the native sign convention.

The normalization arguments are adapted from the formalizations in
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle CovariantDerivative MeasureTheory
open scoped ContDiff ENNReal Manifold NNReal RealInnerProductSpace

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Initial metric normalization: full curvature at most one, curvature endomorphism at least
minus the identity, and half-Euclidean volume at every radius in `(0, 1]`. -/
structure IsNormalizedInitial [T3Space M] [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) : Prop where
  /-- The full Riemann curvature norm is at most one. -/
  riemannCurvatureNorm_le : ∀ x, g.riemannCurvatureNorm x ≤ 1
  /-- The curvature operator is bounded below by minus the identity on all bivectors. -/
  curvatureEndomorphism_ge :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) :=
      Bundle.instIsContMDiffRiemannianBundle g
    ∀ (x : M) (z : ⋀[ℝ]^2 (TangentSpace I x)),
      -(‖z‖ ^ 2) ≤
        ⟪(leviCivitaConnection I M).curvatureEndomorphism
          (isMetricCompatible_leviCivitaConnection I) x z, z⟫
  /-- Intrinsic balls of radius at most one have at least half the Euclidean volume. -/
  riemannianVolume_eball_ge :
    letI : EMetricSpace (TauCeti.WithMetric g) :=
      .ofRiemannianMetric I (TauCeti.WithMetric g)
    ∀ (x : TauCeti.WithMetric g) (r : ℝ), 0 < r → r ≤ 1 →
      (1 / 2 : ℝ≥0∞) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) *
          ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        TauCeti.riemannianVolume I _ (Metric.eball x (ENNReal.ofReal r))

/-- A sufficiently small full-curvature bound implies both curvature requirements in initial
normalization, including the bound on arbitrary bivectors. -/
private theorem normalized_curvature_bounds_of_riemannCurvatureNorm_le [T2Space M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hRm : ∀ x, g.riemannCurvatureNorm x ≤
      1 / (((Module.finrank ℝ E).choose 2 : ℝ) ^ 2 + 1)) :
    (∀ x, g.riemannCurvatureNorm x ≤ 1) ∧
      (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
       letI : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) :=
         Bundle.instIsContMDiffRiemannianBundle g
       ∀ (x : M) (z : ⋀[ℝ]^2 (TangentSpace I x)),
         -(‖z‖ ^ 2) ≤
           ⟪(leviCivitaConnection I M).curvatureEndomorphism
             (isMetricCompatible_leviCivitaConnection I) x z, z⟫) := by
  let K : ℝ := ((Module.finrank ℝ E).choose 2 : ℝ) ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hone : 1 ≤ K := by dsimp [K]; nlinarith [sq_nonneg ((Module.finrank ℝ E).choose 2 : ℝ)]
  constructor
  · intro x
    exact (hRm x).trans ((div_le_one hK).mpr hone)
  · let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) :=
      Bundle.instIsContMDiffRiemannianBundle g
    intro x z
    have hquad := (leviCivitaConnection I M).abs_inner_curvatureEndomorphism_le
      (isMetricCompatible_leviCivitaConnection I) x z
    rw [← g.riemannCurvatureNorm_def] at hquad
    have hnorm : ((Module.finrank ℝ E).choose 2 : ℝ) ^ 2 *
        g.riemannCurvatureNorm x ≤ 1 := by
      have hmul := (le_div_iff₀ hK).mp (hRm x)
      have hnonneg := g.riemannCurvatureNorm_nonneg x
      dsimp [K] at hmul
      nlinarith
    simpa only [one_mul] using neg_le_of_abs_le (hquad.trans
      (mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖z‖)))

/-- Every smooth metric on a compact boundaryless manifold admits arbitrarily large positive
constant rescalings satisfying all three initial normalization conditions simultaneously. -/
theorem exists_rescale_isNormalizedInitial [T2Space M] [CompactSpace M] [I.Boundaryless]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (A : ℝ) :
    ∃ (c : ℝ) (hc : 0 < c), A < c ∧
      (g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc)).IsNormalizedInitial := by
  obtain ⟨R, hR, hsmall⟩ :=
    g.exists_pos_riemannianVolume_eball_lower_bound (c := 1 / 2) (by norm_num)
  let K : ℝ := ((Module.finrank ℝ E).choose 2 : ℝ) ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨c, hc, hlarge, hRm⟩ := g.exists_rescale_riemannCurvatureNorm_le
    (one_div_pos.mpr hK) (max A ((R⁻¹) ^ 2))
  refine ⟨c, hc, (le_max_left A ((R⁻¹) ^ 2)).trans_lt hlarge, ?_⟩
  obtain ⟨hfull, hoperator⟩ :=
    normalized_curvature_bounds_of_riemannCurvatureNorm_le _ hRm
  refine IsNormalizedInitial.mk hfull hoperator ?_
  have hRinv : R⁻¹ < Real.sqrt c :=
    (Real.lt_sqrt (inv_nonneg.mpr hR.le)).mpr
      ((le_max_right A ((R⁻¹) ^ 2)).trans_lt hlarge)
  have hradius : 1 ≤ Real.sqrt c * R := by
    have h := mul_le_mul_of_nonneg_right hRinv.le hR.le
    simpa only [inv_mul_cancel₀ hR.ne'] using h
  have hvol := g.riemannianVolume_eball_lower_bound_rescale_const hc
    (a := (1 / 2 : ℝ≥0∞) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1))
    (R := R) (by simpa using hsmall)
  exact fun x r hr hr1 ↦ hvol x r hr (hr1.trans hradius)

/-- Every compact Hausdorff boundaryless smooth manifold carries a normalized initial metric.
No connectedness, nonemptiness, measurability choice, or dimension-three assumption is needed. -/
theorem exists_isNormalizedInitial [T2Space M] [CompactSpace M] [I.Boundaryless] :
    ∃ g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x),
      g.IsNormalizedInitial := by
  obtain ⟨g⟩ := TauCeti.nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤)
    (F := E) (E := fun x : M ↦ TangentSpace I x)
  obtain ⟨c, hc, -, h⟩ := g.exists_rescale_isNormalizedInitial 0
  exact ⟨g.rescale (fun _ ↦ c) contMDiff_const (fun _ ↦ hc), h⟩

end Bundle.ContMDiffRiemannianMetric
