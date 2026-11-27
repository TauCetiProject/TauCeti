/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.OneForm.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.OneForm.Trajectory
public import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import Mathlib.Topology.Order.Compact

/-!
# Length of negative-dual trajectories away from zeros

A lower bound `c > 0` for the norm of a one-form's metric dual bounds trajectory length by the
potential drop divided by `c`. The bound also applies to just the times spent away from zeros,
even when the trajectory returns to a critical neighborhood between those times. A compact
region disjoint from the zero locus supplies a uniform positive lower bound. On a Riemannian
covering the same constant applies to trajectories on every sheet over this region.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  §1.3, p. 212.
-/

public noncomputable section

open Bundle Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]
  {α : RoughForm I M ℝ 1} {f : M → ℝ} {U K : Set M} {γ : ℝ → M}
  {s T : Set ℝ} {a b c : ℝ}

/-- A continuous one-form has a uniformly positive dual norm on any compact region without
zeros, including the empty region. -/
theorem IsSmoothForm.exists_pos_le_norm_metricDual (hα : IsSmoothForm I 0 α)
    (hK : IsCompact K) (hne : ∀ x ∈ K, α x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ ‖α.metricDual x‖ := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0)
  have : IsManifold I ((0 : ℕ∞ω) + 1) M := by
    simpa only [zero_add] using (inferInstance : IsManifold I 1 M)
  have hnorm : Continuous (fun x ↦ ‖α.metricDual x‖) :=
    (continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp
      hα.contMDiff_metricDual.continuous
  exact hK.exists_forall_le' hnorm.continuousOn fun x hx ↦
    norm_pos_iff.mpr (mt RoughForm.metricDual_eq_zero_iff.mp (hne x hx))

/-- On any measurable selection of interior times where the dual norm is at least `c > 0`,
the length of a negative-dual trajectory is bounded by its total potential drop divided by `c`.
The primitive is only required on the region containing the finite trajectory segment. -/
theorem IsPrimitiveOn.setLIntegral_enorm_curveVelocity_le_of_le_norm_metricDual
    (hf : IsPrimitiveOn α f U) (hα : IsSmoothForm I 0 α)
    (hγ : IsMIntegralCurveOn γ (-α.metricDual) s) (hU : MapsTo γ (Icc a b) U)
    (hab : a ≤ b) (hseg : Icc a b ⊆ s) (hT : MeasurableSet T) (hTab : T ⊆ Ioo a b)
    (hc : 0 < c) (hbound : ∀ t ∈ T, c ≤ ‖α.metricDual (γ t)‖) :
    (∫⁻ t in T, ‖Manifold.curveVelocity I γ t‖ₑ) ≤
      ENNReal.ofReal ((f (γ a) - f (γ b)) / c) := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0)
  have : IsManifold I ((0 : ℕ∞ω) + 1) M := by
    simpa only [zero_add] using (inferInstance : IsManifold I 1 M)
  have hcont : ContinuousOn (fun t ↦ ‖α.metricDual (γ t)‖ ^ 2 / c) (Icc a b) :=
    (((continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp_continuousOn
      (hα.contMDiff_metricDual.continuous.comp_continuousOn hγ.continuousOn)).pow 2
      |>.div_const c).mono hseg
  have hint := (hcont.integrableOn_compact (μ := volume) isCompact_Icc).mono_set Ioo_subset_Icc_self
  have heq : (∫ t in Ioo a b, ‖α.metricDual (γ t)‖ ^ 2 / c) =
      (f (γ a) - f (γ b)) / c := by
    rw [integral_div]
    have he := hf.integral_norm_metricDual_sq_eq_sub hα (hγ.mono hseg) hU (a := a) (b := b)
      (by rw [uIcc_of_le hab])
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at he
    rw [he]
  calc
    (∫⁻ t in T, ‖Manifold.curveVelocity I γ t‖ₑ) ≤
        ∫⁻ t in T, ENNReal.ofReal (‖α.metricDual (γ t)‖ ^ 2 / c) := by
      apply setLIntegral_mono' hT
      intro t ht
      have ht' := hTab ht
      have hs : s ∈ 𝓝 t := mem_of_superset (Ioo_mem_nhds ht'.1 ht'.2)
        (Ioo_subset_Icc_self.trans hseg)
      have hv : Manifold.curveVelocity I γ t = -α.metricDual (γ t) := by
        rw [← Manifold.curveVelocityWithin_univ]
        exact Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
          (hγ.isMIntegralCurveAt hs).hasMFDerivAt.hasMFDerivWithinAt uniqueDiffWithinAt_univ
      rw [hv, eNorm_neg, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hc]
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg (α.metricDual (γ t)))
    _ ≤ ∫⁻ t in Ioo a b, ENNReal.ofReal (‖α.metricDual (γ t)‖ ^ 2 / c) :=
      lintegral_mono_set hTab
    _ = ENNReal.ofReal ((f (γ a) - f (γ b)) / c) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun t ↦ div_nonneg (sq_nonneg _) hc.le), heq]

/-- If a whole trajectory segment stays where the dual norm is at least `c > 0`, its native
Riemannian path length is bounded by the potential drop divided by `c`. -/
theorem IsPrimitiveOn.pathELength_le_of_le_norm_metricDual
    (hf : IsPrimitiveOn α f U) (hα : IsSmoothForm I 0 α)
    (hγ : IsMIntegralCurveOn γ (-α.metricDual) s) (hU : MapsTo γ (Icc a b) U)
    (hab : a ≤ b) (hseg : Icc a b ⊆ s) (hc : 0 < c)
    (hbound : ∀ t ∈ Ioo a b, c ≤ ‖α.metricDual (γ t)‖) :
    Manifold.pathELength I γ a b ≤ ENNReal.ofReal ((f (γ a) - f (γ b)) / c) := by
  rw [Manifold.pathELength_eq_setLIntegral_enorm_curveVelocity_Ioo]
  exact hf.setLIntegral_enorm_curveVelocity_le_of_le_norm_metricDual hα hγ hU hab hseg
    measurableSet_Ioo Subset.rfl hc hbound

end TauCeti

namespace TauCeti.IsLocalRiemannianIsometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J 1 N] [T2Space N] [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 0 F (fun y : N ↦ TangentSpace J y)]
  {p : M → N} {α : RoughForm J N ℝ 1} {K : Set N}

/-- A compact region of the base avoiding zeros gives one bound for the length spent over that
region by every descending trajectory for the pulled-back one-form. The constant is determined
on the base, and the potential drop is measured on the lift. -/
theorem exists_pos_setLIntegral_enorm_curveVelocity_le_of_isCompact
    (hp : IsLocalRiemannianIsometry I J p) (hα : IsSmoothForm J 0 α)
    (hK : IsCompact K) (hK₀ : ∀ y ∈ K, α y ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ {f : M → ℝ} {U : Set M},
      IsPrimitiveOn (mpullback I J p α) f U →
      ∀ {γ : ℝ → M} {a b : ℝ}, a ≤ b →
        IsMIntegralCurveOn γ (-(mpullback I J p α).metricDual) (Icc a b) →
        MapsTo γ (Icc a b) U →
        (∫⁻ t in Ioo a b ∩ (p ∘ γ) ⁻¹' K, ‖Manifold.curveVelocity I γ t‖ₑ) ≤
          ENNReal.ofReal ((f (γ a) - f (γ b)) / c) := by
  obtain ⟨c, hc, hmin⟩ := hα.exists_pos_le_norm_metricDual hK hK₀
  have hαp : IsSmoothForm I 0 (mpullback I J p α) :=
    hα.mpullback (hp.contMDiff.of_le (by simp))
  refine ⟨c, hc, fun {f U} hf {γ a b} hab hγ hU ↦ ?_⟩
  have hproj := hp.contMDiff.continuous.comp_continuousOn (hγ.continuousOn.mono Ioo_subset_Icc_self)
  have hW := hproj.isOpen_inter_preimage isOpen_Ioo hK.isClosed.isOpen_compl
  have hT : MeasurableSet (Ioo a b ∩ (p ∘ γ) ⁻¹' K) := by
    convert (measurableSet_Ioo (a := a) (b := b)).diff hW.measurableSet using 1
    ext t
    simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff]
    tauto
  refine hf.setLIntegral_enorm_curveVelocity_le_of_le_norm_metricDual hαp hγ hU hab
    Subset.rfl hT inter_subset_left hc fun t ht ↦ ?_
  have hd := hp.norm_mfderiv (γ t) ((mpullback I J p α).metricDual (γ t))
  rw [hp.mfderiv_metricDual_mpullback] at hd
  rw [← hd]
  exact hmin _ ht.2

end TauCeti.IsLocalRiemannianIsometry
