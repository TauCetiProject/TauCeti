/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.ConformalLaplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Harmonic
import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Uniqueness of nonpositive constant scalar curvature in a conformal class

On a connected closed manifold of dimension greater than two, a metric of constant nonpositive
scalar curvature is conformal to another constant-scalar-curvature metric only by a homothety.
If the two metrics have the same volume, they coincide. In particular, there is at most one
unit-volume constant-scalar-curvature metric in such a conformal class.

Write the second metric as `u ^ (4 / (n - 2)) g`. The scalar-curvature transformation gives
`aₙ (-Δu) + c u = d u ^ (pₙ - 1)`. At the minimum of `u` it forces `d ≤ 0`. If `d < 0`, the
maximum and minimum inequalities force those extrema to agree. If `d = 0`, they force `c = 0`,
and the equation makes `u` harmonic; Green's identity and connectedness then make it constant.
Thus the scalar-flat case is included, not inferred from a strict comparison principle.

The metrics are native `Bundle.ContMDiffRiemannianMetric` values. Only the first metric is
installed as an instance in the analytic argument. Volumes are taken on their distinct
`TauCeti.WithMetric` copies, so the statement never installs incompatible metric instances on
one carrier. Neither existence of a Yamabe minimizer nor a sign theorem for the Yamabe invariant
is assumed or proved here.

## Main results

In the namespace `Bundle.ContMDiffRiemannianMetric`:

* `exists_rescale_const_eq_of_mem_conformalClass_of_scalarCurvature_nonpos`:
  constant-scalar-curvature metrics conformal to a nonpositive one are homothetic.
* `eq_of_mem_conformalClass_of_scalarCurvature_nonpos_of_volume_eq`:
  equal volume removes that homothety.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module TauCeti TauCeti.Manifold TauCeti.Yamabe
open scoped ContDiff Manifold

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- Dividing the conformal factor equation by its positive unknown isolates the strictly
increasing power `u ^ (pₙ - 2)`. -/
private theorem conformalLaplacian_eq_div {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {c d : ℝ} (hScal : ∀ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x = c)
    (heq : ∀ x, conformalLaplacian I u x = d * u x ^ (criticalExponent (finrank ℝ E) - 1))
    (x : M) :
    conformalCoefficient (finrank ℝ E) * -laplaceBeltrami I u x / u x + c =
      d * u x ^ (criticalExponent (finrank ℝ E) - 2) := by
  have hpow : u x ^ (criticalExponent (finrank ℝ E) - 1) =
      u x ^ (criticalExponent (finrank ℝ E) - 2) * u x := by
    rw [← Real.rpow_add_one (hu_pos x).ne']
    congr 1
    ring
  have h := heq x
  rw [conformalLaplacian_def, hScal x, hpow] at h
  field_simp [(hu_pos x).ne']
  nlinarith

/-- A positive Yamabe conformal factor over a nonpositive constant-scalar-curvature metric is
constant whenever the new scalar curvature is constant. -/
private theorem exists_pos_eq_const_of_conformalLaplacian_eq (hn : 2 < finrank ℝ E)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu_pos : ∀ x, 0 < u x) {c d : ℝ}
    (hc : c ≤ 0) (hScal : ∀ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x = c)
    (heq : ∀ x, conformalLaplacian I u x = d * u x ^ (criticalExponent (finrank ℝ E) - 1)) :
    ∃ t > 0, ∀ x, u x = t := by
  obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuous.continuousOn
  obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hu.continuous.continuousOn
  have hΔa := laplaceBeltrami_nonneg_of_isLocalMin hu.contMDiffAt (ha.isLocalMin Filter.univ_mem)
  have hΔb := laplaceBeltrami_nonpos_of_isLocalMax hu.contMDiffAt (hb.isLocalMax Filter.univ_mem)
  have hA := conformalCoefficient_pos hn
  have hmin : d * u a ^ (criticalExponent (finrank ℝ E) - 2) ≤ c := by
    rw [← conformalLaplacian_eq_div hu_pos hScal heq a]
    have : conformalCoefficient (finrank ℝ E) * -laplaceBeltrami I u a / u a ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA.le (neg_nonpos.mpr hΔa))
        (hu_pos a).le
    linarith
  have hmax : c ≤ d * u b ^ (criticalExponent (finrank ℝ E) - 2) := by
    rw [← conformalLaplacian_eq_div hu_pos hScal heq b]
    have : 0 ≤ conformalCoefficient (finrank ℝ E) * -laplaceBeltrami I u b / u b :=
      div_nonneg (mul_nonneg hA.le (neg_nonneg.mpr hΔb)) (hu_pos b).le
    linarith
  have hd : d ≤ 0 := by
    have := Real.rpow_pos_of_pos (hu_pos a) (criticalExponent (finrank ℝ E) - 2)
    nlinarith
  refine ⟨u a, hu_pos a, ?_⟩
  rcases hd.eq_or_lt with hd | hd
  · have hc0 : c = 0 := by simp only [hd, zero_mul] at hmin; linarith
    have hΔ (x : M) : laplaceBeltrami I u x = 0 := by
      have h := heq x
      simp only [conformalLaplacian_def, hScal x, hc0, hd, zero_mul, add_zero] at h
      nlinarith
    exact fun x ↦ apply_eq_of_laplaceBeltrami_eq_zero hu hΔ x a
  · have hp := sub_pos.mpr (two_lt_criticalExponent hn)
    have hpow : u b ^ (criticalExponent (finrank ℝ E) - 2) ≤
        u a ^ (criticalExponent (finrank ℝ E) - 2) := by nlinarith
    have hba := (Real.rpow_le_rpow_iff (hu_pos b).le (hu_pos a).le hp).mp hpow
    exact fun x ↦ le_antisymm ((hb (Set.mem_univ x)).trans hba) (ha (Set.mem_univ x))

end TauCeti.Yamabe

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- On a connected closed manifold of dimension greater than two, a constant-scalar-curvature
metric conformal to a metric of constant nonpositive scalar curvature is a positive constant
rescaling of that metric. No sign assumption is needed on the second scalar curvature. -/
theorem exists_rescale_const_eq_of_mem_conformalClass_of_scalarCurvature_nonpos
    (hn : 2 < finrank ℝ E)
    {g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hconf : g' ∈ g.conformalClass) {c d : ℝ} (hc : c ≤ 0)
    (hg : ∀ x, g.scalarCurvature x = c) (hg' : ∀ x, g'.scalarCurvature x = d) :
    ∃ t : ℝ, ∃ ht : 0 < t, g.rescale (fun _ ↦ t) contMDiff_const (fun _ ↦ ht) = g' := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega :
    finrank ℝ E ≠ 2))
  have hp : 4 / ((finrank ℝ E : ℝ) - 2) ≠ 0 := div_ne_zero four_ne_zero hn'
  obtain ⟨u, hu, hu_pos, rfl⟩ := (mem_conformalClass_iff_exists_rpow hp).mp hconf
  borelize M
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  obtain ⟨t, ht, hut⟩ := exists_pos_eq_const_of_conformalLaplacian_eq hn
    (hu.of_le (by simp)) hu_pos hc
    (fun x ↦ (g.scalarCurvature_def x).symm.trans (hg x))
    (fun x ↦ (scalarCurvature_rescale_eq_iff_conformalLaplacian_eq g (by omega) hu_pos d x).mp
      (hg' x))
  refine ⟨t ^ (4 / ((finrank ℝ E : ℝ) - 2)), Real.rpow_pos_of_pos ht _, ?_⟩
  ext x v w
  simp only [rescale_inner, hut]

/-- On a connected closed manifold of dimension greater than two, conformal metrics with
constant scalar curvatures coincide if the first scalar curvature is nonpositive and their
volumes agree. In particular the unit-volume metric is unique. -/
theorem eq_of_mem_conformalClass_of_scalarCurvature_nonpos_of_volume_eq
    (hn : 2 < finrank ℝ E)
    {g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hconf : g' ∈ g.conformalClass) {c d : ℝ} (hc : c ≤ 0)
    (hg : ∀ x, g.scalarCurvature x = c) (hg' : ∀ x, g'.scalarCurvature x = d)
    (hvol : riemannianTotalVolume I (WithMetric g) = riemannianTotalVolume I (WithMetric g')) :
    g = g' := by
  obtain ⟨t, ht, rfl⟩ := g.exists_rescale_const_eq_of_mem_conformalClass_of_scalarCurvature_nonpos
    hn hconf hc hg hg'
  have hscale : t ^ ((finrank ℝ E : ℝ) / 2) = 1 := by
    have : Nonempty (WithMetric g) := Nonempty.map (WithMetric.toWithMetric g) inferInstance
    have hV := riemannianTotalVolume_pos (I := I) (M := WithMetric g)
    rw [WithMetric.riemannianTotalVolume_rescale, integral_const, smul_eq_mul,
      ← riemannianTotalVolume_def] at hvol
    nlinarith
  have hnpos : (0 : ℝ) < finrank ℝ E := by exact_mod_cast (by omega : 0 < finrank ℝ E)
  have ht1 : t = 1 := (Real.rpow_left_inj ht.le (by norm_num)
    (ne_of_gt (div_pos hnpos two_pos))).mp (by simpa using hscale)
  subst t
  exact g.rescale_one.symm

end Bundle.ContMDiffRiemannianMetric
