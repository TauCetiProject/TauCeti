/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Distance comparison and completeness for Riemannian metrics

If a Riemannian metric `g` uniformly dominates the given tangent norms on `M`, the
identification `ofWithMetric : WithMetric g → M` is Lipschitz for Riemannian extended distance.
When `M` is complete for that distance, the copy carrying `g` is complete as well. Symmetrically,
if the given tangent norms dominate `g`, then `toWithMetric g` is Lipschitz, and if `g` is a
constant multiple `C²` of the given squared norms, the Riemannian extended distance of the copy is
exactly `C` times that of `M` (`TauCeti.WithMetric.riemannianEDist_toWithMetric_eq_mul`).
Extended distances allow points in distinct connected components to be infinitely far apart.

`riemannianEDist_toWithMetric_le_mul_toWithMetric` compares the intrinsic distances of two
bundled metrics on the same manifold from a pointwise quadratic-form bound.

The constant-rescaling law is adapted from the formalizations in
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).

The carrier and tangent-norm comparison are provided by `TauCeti.WithMetric`.
See M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Lemma 3.3.
-/

public section

open Bundle Manifold MeasureTheory Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}

section TwoMetrics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- A pointwise quadratic-form comparison bounds intrinsic distances between the copies
carrying the two metrics. The factor is positive to allow infinitely distant components. -/
theorem riemannianEDist_toWithMetric_le_mul_toWithMetric {C : ℝ≥0} (hC0 : C ≠ 0)
    (hgg' : ∀ x (v : TangentSpace I x), g'.inner x v v ≤ (C : ℝ) ^ 2 * g.inner x v v)
    (x y : M) :
    riemannianEDist I (toWithMetric g' x) (toWithMetric g' y) ≤
      C * riemannianEDist I (toWithMetric g x) (toWithMetric g y) := by
  have hnorm (z : WithMetric g) (v : TangentSpace I z) :
      ‖mfderiv I I (diffeomorphWithMetric g g' 1) z v‖ ≤ C * ‖v‖ := by
    have hd : mfderiv I I (diffeomorphWithMetric g g' 1) z v = v :=
      congrArg (fun L : TangentSpace I z →L[ℝ] TangentSpace I z ↦ L v)
        (mfderiv_diffeomorphWithMetric g' 1 z)
    apply (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg C.coe_nonneg (norm_nonneg _)) two_ne_zero).1
    rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_def, inner_def]
    erw [mfderiv_ofWithMetric_apply, mfderiv_ofWithMetric_apply,
      hd]
    erw [diffeomorphWithMetric_apply, ofWithMetric_toWithMetric]
    exact hgg' z.ofWithMetric v
  simpa only [diffeomorphWithMetric_apply, ofWithMetric_toWithMetric] using
    Manifold.riemannianEDist_le_mul (diffeomorphWithMetric g g' 1).contMDiff hC0 hnorm
      (toWithMetric g x) (toWithMetric g y)

end TwoMetrics

section Intrinsic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- If the given squared tangent norms are bounded by `C²` times `g`, forgetting the copy
carrying `g` increases Riemannian extended distance by at most the positive factor `C`. -/
theorem riemannianEDist_ofWithMetric_le_mul {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v)
    (x y : WithMetric g) :
    riemannianEDist I x.ofWithMetric y.ofWithMetric ≤ C * riemannianEDist I x y :=
  Manifold.riemannianEDist_le_mul contMDiff_ofWithMetric hC0
    (fun x v ↦ norm_mfderiv_ofWithMetric_le_mul
      (hg x.ofWithMetric (mfderiv I I ofWithMetric x v))) x y

/-- If `g` is bounded by `C²` times the given squared tangent norms, passing to the copy carrying
`g` increases Riemannian extended distance by at most the positive factor `C`. -/
theorem riemannianEDist_toWithMetric_le_mul {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), g.inner x v v ≤ (C : ℝ) ^ 2 * ‖v‖ ^ 2) (x y : M) :
    riemannianEDist I (toWithMetric g x) (toWithMetric g y) ≤ C * riemannianEDist I x y := by
  refine Manifold.riemannianEDist_le_mul contMDiff_toWithMetric hC0 (fun x v ↦ ?_) x y
  have h : ‖mfderiv I I (toWithMetric g) x v‖ ^ 2 ≤ ((C : ℝ) * ‖v‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_def, mfderiv_ofWithMetric_mfderiv_toWithMetric,
      mul_pow]
    exact hg x v
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg C.coe_nonneg (norm_nonneg _))
    two_ne_zero).1 h

/-- If `g` is `C²` times the given squared tangent norms, for a positive constant `C`, then the
Riemannian extended distance of the copy carrying `g` is `C` times that of `M`. For instance,
rescaling a metric by a constant `c > 0` multiplies its Riemannian distance by `√c`. -/
theorem riemannianEDist_toWithMetric_eq_mul {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), g.inner x v v = (C : ℝ) ^ 2 * ‖v‖ ^ 2) (x y : M) :
    riemannianEDist I (toWithMetric g x) (toWithMetric g y) = C * riemannianEDist I x y := by
  refine le_antisymm (riemannianEDist_toWithMetric_le_mul hC0 (fun x v ↦ (hg x v).le) x y) ?_
  -- The reverse inequality is the comparison along `ofWithMetric`, with the factor `C⁻¹`.
  have hle := riemannianEDist_ofWithMetric_le_mul (g := g) (inv_ne_zero hC0) (fun x v ↦ by
    rw [hg, NNReal.coe_inv, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hC0),
      one_pow, one_mul]) (toWithMetric g x) (toWithMetric g y)
  rw [ofWithMetric_toWithMetric, ofWithMetric_toWithMetric] at hle
  calc (C : ℝ≥0∞) * riemannianEDist I x y
      ≤ C * (C⁻¹ * riemannianEDist I (toWithMetric g x) (toWithMetric g y)) := by gcongr
    _ = riemannianEDist I (toWithMetric g x) (toWithMetric g y) := by
      rw [← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ hC0, ENNReal.coe_one, one_mul]

end Intrinsic

section Ambient

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

/-- If the given squared tangent norms are bounded by `C²` times `g` and the copy is equipped
with its Riemannian distance, `ofWithMetric` is `C`-Lipschitz for positive `C`. -/
theorem lipschitzWith_ofWithMetric [PseudoEMetricSpace (WithMetric g)]
    [IsRiemannianManifold I (WithMetric g)] {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v) :
    LipschitzWith C (ofWithMetric : WithMetric g → M) := by
  intro x y
  rw [IsRiemannianManifold.out (I := I), IsRiemannianManifold.out (I := I)]
  exact riemannianEDist_ofWithMetric_le_mul hC0 hg x y

/-- A metric uniformly dominating a complete Riemannian metric is complete for its own
Riemannian extended distance. -/
theorem completeSpace_of_sq_norm_le_mul [CompleteSpace M] {C : ℝ≥0} (hC0 : C ≠ 0)
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v) :
    letI : PseudoEMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
    CompleteSpace (WithMetric g) := by
  let : PseudoEMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  exact CompleteSpace.of_comp_eq_id (toWithMetric g) ofWithMetric rfl
    continuous_toWithMetric (lipschitzWith_ofWithMetric hC0 hg).uniformContinuous

end Ambient

end TauCeti.WithMetric

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}

/-- Multiplying a bundled metric by `c²`, for `c > 0`, multiplies its intrinsic extended
distances by `c`, including infinite distances between components. -/
theorem riemannianEDist_rescale_const_sq
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (x y : M) :
    riemannianEDist I
        (toWithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const (fun _ ↦ sq_pos_of_pos hc)) x)
        (toWithMetric (g.rescale (fun _ ↦ c ^ 2) contMDiff_const (fun _ ↦ sq_pos_of_pos hc)) y) =
      ENNReal.ofReal c * riemannianEDist I (toWithMetric g x) (toWithMetric g y) := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let C : ℝ≥0 := NNReal.mk c hc.le
  have hC : C ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    simpa only [C, NNReal.coe_mk] using hc.ne'
  have hnew := riemannianEDist_toWithMetric_eq_mul
    (g := g.rescale (fun _ ↦ c ^ 2) contMDiff_const (fun _ ↦ sq_pos_of_pos hc)) hC
    (fun x v ↦ by
      rw [ContMDiffRiemannianMetric.rescale_inner]
      simp only [C, NNReal.coe_mk]
      rw [← g.inner_riemannianBundle, real_inner_self_eq_norm_sq]) x y
  have hold := riemannianEDist_toWithMetric_eq_mul (g := g) one_ne_zero
    (fun x v ↦ by
      rw [← g.inner_riemannianBundle, real_inner_self_eq_norm_sq, NNReal.coe_one,
        one_pow, one_mul]) x y
  rw [ENNReal.coe_one, one_mul] at hold
  rw [hold, hnew]
  dsimp only [C]
  rw [ENNReal.ofReal_eq_coe_nnreal hc.le]

end Bundle.ContMDiffRiemannianMetric

end
