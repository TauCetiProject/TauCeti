/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Topology.Instances.NNReal
import TauCeti.Data.ENNReal.Mul
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Uniform lower volume bounds for small Riemannian balls

On a smooth Riemannian manifold, sufficiently small metric balls have volume at least any
fixed fraction less than one of the Euclidean ball volume. The radius can be chosen uniformly
on an open neighbourhood of any compact set of centres. No completeness or curvature bound
is required, and the result includes dimension zero and the empty compact set.

The proof uses one normal chart near each centre, continuity of its Riemannian Jacobian at
the origin, and the change-of-variables formula for the native Riemannian volume. Coordinate
balls about nearby centres give the local uniform estimate; a finite cover gives a common
radius. In dimension three the coefficient `1 / 2` is the volume condition used when choosing
a normalized initial metric.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Definition 4.10.
* Public formalizations:
  [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology NNReal

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

/-- A smooth Riemannian bundle has the continuity needed to form its native volume. -/
local instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)

omit [IsRiemannianManifold I M] in
/-- A coordinate ball inside a Lipschitz chart gives a lower bound for the volume of the
corresponding metric ball whenever the chart Jacobian has a lower bound. -/
private theorem riemannianVolume_eball_lower_bound_of_chart
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ F) (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {f : F → M} {R : ℝ} {C : ℝ≥0} (hC : 1 < C)
    (hinj : InjOn f (Metric.ball 0 R))
    (hf : ∀ z ∈ Metric.ball (0 : F) R, MDifferentiableAt 𝓘(ℝ, F) I f z)
    (hLip : LipschitzOnWith C f (Metric.ball 0 R)) {a : ℝ}
    (hJ : ∀ z ∈ Metric.ball (0 : F) R, a ≤ riemannianJacobian (I := I) b f z)
    {w : F} (hw : w ∈ Metric.ball 0 (R / 2)) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R / 2) :
    ENNReal.ofReal a * b.addHaar (Metric.ball w (r / (C : ℝ))) ≤
      riemannianVolume I M (Metric.eball (f w) (ENNReal.ofReal r)) := by
  have hC0 : 0 < (C : ℝ) := by exact_mod_cast zero_lt_one.trans hC
  have hfrac : r / (C : ℝ) ≤ R / 2 :=
    (div_le_self hr.le (by exact_mod_cast hC.le)).trans hrR
  have hsub : Metric.ball w (r / (C : ℝ)) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball' (by linarith [Metric.mem_ball.mp hw])
  have hwR : w ∈ Metric.ball (0 : F) R :=
    Metric.ball_subset_ball (by have := Metric.pos_of_mem_ball hw; linarith) hw
  have himage : f '' Metric.ball w (r / (C : ℝ)) ⊆
      Metric.eball (f w) (ENNReal.ofReal r) := by
    rintro _ ⟨z, hz, rfl⟩
    refine (hLip (hsub hz) hwR).trans_lt ?_
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by
      have := (lt_div_iff₀ hC0).mp (Metric.mem_ball.mp hz)
      simpa only [mul_comm] using this)
  have hcov := b.setLIntegral_riemannianVolume_image_of_injOn hdim
    Metric.isOpen_ball.measurableSet (hinj.mono hsub) (fun z hz ↦ hf z (hsub hz)) (fun _ ↦ 1)
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at hcov
  calc
    _ = ∫⁻ _ in Metric.ball w (r / (C : ℝ)), ENNReal.ofReal a ∂b.addHaar := by simp
    _ ≤ ∫⁻ z in Metric.ball w (r / (C : ℝ)),
        ENNReal.ofReal (riemannianJacobian (I := I) b f z) ∂b.addHaar :=
      setLIntegral_mono' Metric.isOpen_ball.measurableSet
        (fun z hz ↦ ENNReal.ofReal_le_ofReal (hJ z (hsub hz)))
    _ = riemannianVolume I M (f '' Metric.ball w (r / (C : ℝ))) := hcov.symm
    _ ≤ _ := measure_mono himage

variable [I.Boundaryless]

omit [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] in
/-- The Jacobian of a normal chart is one at its centre and stays above any prescribed
constant less than one on a sufficiently small normal ball with a prescribed Lipschitz bound. -/
private theorem exists_normal_ball_jacobian_lower_bound (p : M) {C : ℝ≥0} (hC : 1 < C)
    {a : ℝ} (ha : a < 1)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p)) :
    ∃ R > 0, IsNormalDomain I M p (Metric.ball 0 R) ∧
      LipschitzOnWith C (riemannianExp I M p) (Metric.ball 0 R) ∧
      ∀ z ∈ Metric.ball (0 : TangentSpace I p) R,
        a ≤ riemannianJacobian (I := I) b.toBasis (riemannianExp I M p) z := by
  have hJ0 : riemannianJacobian (I := I) b.toBasis (riemannianExp I M p) 0 = 1 := by
    rw [riemannianJacobian_eq_sqrt_det_gram]
    simp only [OrthonormalBasis.coe_toBasis, mfderiv_riemannianExp_apply_zero]
    rw [riemannianExp_zero]
    rw [Matrix.gram_eq_one_iff_orthonormal.mpr b.orthonormal]
    simp
  have hcont := continuousOn_riemannianJacobian (I := I) b.toBasis
    ((contMDiffOn_riemannianExp (I := I) (M := M) p).of_le (by simp))
    (isOpen_expDomain p)
  have hnear : ∀ᶠ z in 𝓝 (0 : TangentSpace I p),
      a < riemannianJacobian (I := I) b.toBasis (riemannianExp I M p) z :=
    (hcont.continuousAt ((isOpen_expDomain p).mem_nhds (zero_mem_expDomain p))).eventually_const_lt
      (by simpa only [hJ0] using ha)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  obtain ⟨R, hR, hn, hLip⟩ :=
    exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp (I := I) p hC
  have hmin : 0 < min R δ := lt_min hR hδ
  have hsub := Metric.ball_subset_ball (x := (0 : TangentSpace I p)) (min_le_left R δ)
  refine ⟨min R δ, hmin, hn.ball hsub hmin, hLip.mono hsub, fun z hz ↦ ?_⟩
  exact (hδbound z (Metric.ball_subset_ball (min_le_right R δ) hz)).le

/-- Every centre has a neighbourhood on which all sufficiently small Riemannian balls have
volume at least a prescribed fraction `c < 1` of the Euclidean ball volume. The same radius
works for all centres in the neighbourhood and for every smaller positive radius. -/
theorem exists_pos_eventually_riemannianVolume_eball_lower_bound (p : M)
    {c : ℝ≥0} (hc : c < 1) :
    ∃ R > 0, ∀ᶠ y in 𝓝 p, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) *
        ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolume I M (Metric.eball y (ENNReal.ofReal r)) := by
  let a : ℝ := ((c : ℝ) + 1) / 2
  have ha : a < 1 := by
    have hc' : (c : ℝ) < 1 := by exact_mod_cast hc
    dsimp [a]
    linarith
  have hmargin : c < (c + 1) / 2 := by
    have hc' : (c : ℝ) < 1 := by exact_mod_cast hc
    apply NNReal.coe_lt_coe.1
    push_cast
    linarith
  obtain ⟨C, hC, hCa⟩ := NNReal.exists_one_lt_mul_pow_lt c hmargin (Module.finrank ℝ E)
  have hCa' : (c : ℝ≥0∞) * (C : ℝ≥0∞) ^ Module.finrank ℝ E ≤ ENNReal.ofReal a := by
    have hreal : (c : ℝ) * (C : ℝ) ^ Module.finrank ℝ E ≤ a := by
      exact_mod_cast hCa.le
    simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_pow C.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hreal
  have hC0 : 0 < (C : ℝ) := by exact_mod_cast zero_lt_one.trans hC
  let b := (stdOrthonormalBasis ℝ (TangentSpace I p)).reindex
    (finCongr (finrank_tangentSpace (I := I) p))
  obtain ⟨R, hR, hn, hLip, hJ⟩ := exists_normal_ball_jacobian_lower_bound p hC ha b
  let : MeasurableSpace (TangentSpace I p) := borel (TangentSpace I p)
  let : BorelSpace (TangentSpace I p) := ⟨rfl⟩
  have hunit : b.toBasis.addHaar (Metric.ball (0 : TangentSpace I p) 1) =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
    rw [b.addHaar_eq_volume]
    have h := b.measurePreserving_repr.measure_preimage
      (s := Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1)
      Metric.isOpen_ball.measurableSet.nullMeasurableSet
    rw [LinearIsometryEquiv.preimage_ball, map_zero] at h
    exact h
  refine ⟨R / 2, half_pos hR, ?_⟩
  filter_upwards [(hn.ball (Metric.ball_subset_ball (by linarith)) (half_pos hR)).image_mem_nhds]
    with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  intro r hr hrR
  have h := riemannianVolume_eball_lower_bound_of_chart b.toBasis
    (finrank_tangentSpace (I := I) p) hC hn.injOn
    (fun z hz ↦ (contMDiffAt_riemannianExp (hn.subset_expDomain hz)).mdifferentiableAt (by simp))
    hLip hJ hw hr hrR
  rw [Measure.addHaar_ball_of_pos _ _ (div_pos hr hC0),
    finrank_tangentSpace (I := I) p, hunit] at h
  have hscalar := ENNReal.mul_mul_pow_le_mul_div_pow_mul
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1))
    (NNReal.coe_ne_zero.1 hC0.ne') hCa' (r := ENNReal.ofReal r)
  rw [← @ENNReal.ofReal_coe_nnreal C, ← ENNReal.ofReal_div_of_pos hC0,
    ← ENNReal.ofReal_pow (div_nonneg hr.le C.coe_nonneg)] at hscalar
  exact hscalar.trans h

/-- Uniform small-ball volume lower bounds hold on an open neighbourhood of a compact set of
centres. Any coefficient `c < 1` is allowed, with one positive radius for every centre and all
smaller positive radii. The compact set may be empty and the dimension may be zero. -/
theorem _root_.IsCompact.exists_pos_exists_isOpen_superset_riemannianVolume_eball_lower_bound
    {K : Set M} (hK : IsCompact K) {c : ℝ≥0} (hc : c < 1) :
    ∃ R > 0, ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) *
        ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolume I M (Metric.eball x (ENNReal.ofReal r)) := by
  classical
  choose R hR hbound using fun x : M ↦
    exists_pos_eventually_riemannianVolume_eball_lower_bound (I := I) x hc
  choose U hUsub hUopen hUmem using fun x ↦ mem_nhds_iff.mp (hbound x)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUopen (fun x _ ↦ mem_iUnion.mpr ⟨x, hUmem x⟩)
  refine ⟨s.fold min 1 R, (Finset.lt_fold_min (0 : ℝ)).mpr
    ⟨zero_lt_one, fun x _ ↦ hR x⟩, ⋃ x ∈ s, U x, isOpen_iUnion fun x ↦
      isOpen_iUnion fun _ ↦ hUopen x, hs, ?_⟩
  intro x hx r hr hrR
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  exact hUsub y hxy r hr (hrR.trans
    ((Finset.fold_min_le (R y)).mpr (Or.inr ⟨y, hy, le_rfl⟩)))

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

/-- A smooth metric on a compact manifold has a uniform lower Euclidean volume ratio on all
sufficiently small intrinsic balls. Taking `c = 1 / 2` gives the small-ball input for initial
metric normalization before rescaling. The statement uses the metric's native Riemannian
volume on `WithMetric g` and allows disconnected and empty manifolds. -/
theorem exists_pos_riemannianVolume_eball_lower_bound
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {c : ℝ≥0} (hc : c < 1) :
    letI : EMetricSpace (TauCeti.WithMetric g) := .ofRiemannianMetric I (TauCeti.WithMetric g)
    ∃ R > 0, ∀ x : TauCeti.WithMetric g, ∀ r : ℝ, 0 < r → r ≤ R →
      (c : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) *
        ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          TauCeti.riemannianVolume I (TauCeti.WithMetric g)
            (Metric.eball x (ENNReal.ofReal r)) := by
  let : EMetricSpace (TauCeti.WithMetric g) := .ofRiemannianMetric I (TauCeti.WithMetric g)
  obtain ⟨R, hR, U, -, hU, hbound⟩ :=
    IsCompact.exists_pos_exists_isOpen_superset_riemannianVolume_eball_lower_bound
      (I := I) (isCompact_univ (X := TauCeti.WithMetric g)) hc
  exact ⟨R, hR, fun x ↦ hbound x (hU (mem_univ x))⟩

end Bundle.ContMDiffRiemannianMetric
