/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Calibration.Immersion
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The Fundamental Theorem of Calibrations and Volume Minimization

This file proves the fundamental theorem of calibrated geometry (Harvey and Lawson, Theorem II.4.2)
together with its equality characterization, its Stokes-theoretic consequences on closed manifolds,
and concrete calibrated immersions.

For a smooth calibration `φ` on a Riemannian manifold `(M, g)` (which need not be
finite-dimensional) and a smooth immersion `f : N → M` of a compact oriented `k`-manifold `(N, o)`,
the integrated calibration inequality gives `∫_N f*φ ≤ immersionVolume g f hf hinj o`. Because
`f*φ = topFormDensity o (f*φ) • vol_{f*g}` with continuous density bounded above by `1`, equality
holds if and only if `topFormDensity o (f*φ) = 1` everywhere, that is, if and only if `(f, o)` is
calibrated by `φ`
(`TauCeti.integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion`).

Combining this with calibration of `(f, o)` (`immersionVolume g f hf hinj o = ∫_N f*φ`) yields:
* `TauCeti.immersionVolume_le_of_isCalibratedImmersion`: if `(f, o)` is calibrated by `φ` and a
  second immersion `(f', o')` of a compact oriented `k`-manifold `N'` has the same periods as
  `(f, o)` on every smooth closed `k`-form on `M` (for instance when `(f, o)` and `(f', o')`
  represent the same real homology class on closed manifolds, or share a common boundary cancelled
  by Stokes' theorem), then `immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o'`.
* `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion`: under the same hypotheses, the competing
  immersion `(f', o')` achieves equal volume if and only if `(f', o')` is also calibrated by `φ`.
* `TauCeti.IsCalibratedImmersion.mextDeriv_ne` and
  `TauCeti.IsCalibratedImmersion.deRhamCohomology_mk_ne_zero` (Harvey and Lawson, Corollary II.4.3):
  a form that calibrates an immersion of a nonempty closed Hausdorff manifold cannot be exact, so
  the de Rham class of the calibration is nonzero.
* `TauCeti.immersionVolume_le_of_homotopy` and
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy`: on a closed oriented
  Hausdorff manifold `N`, a calibrated immersion minimizes volume in its smooth homotopy class, with
  equality if and only if the homotopic immersion is itself calibrated by `φ`.
* `TauCeti.isCalibratedImmersion_id_riemannianVolumeForm` and
  `TauCeti.isCalibratedImmersion_linearIsometry_const`: the identity of an oriented Riemannian
  manifold is calibrated by its Riemannian volume form, and every linear isometric immersion of an
  oriented inner product space into a finite-dimensional real inner product space is calibrated by
  the associated simple constant calibration.

## References

* F. R. Harvey and H. B. Lawson Jr., *Calibrated geometries*, Acta Math. 148 (1982), 47–157,
  Theorem II.4.2 and Corollary II.4.3.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. 6 (1998), 705–747.
-/

public section

noncomputable section

open Bundle Set exteriorPower
open scoped Manifold ContDiff Topology

namespace TauCeti

section EqualityCase

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] [CompactSpace N] {k : ℕ}
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {φ : RoughForm I M ℝ k}
  (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
  (o : Manifold.Orientation I' N (Fin k))

/-- **Equality in the integrated calibration inequality**: on a compact oriented `k`-manifold `N`
(possibly with boundary or corners, and in every dimension `k ≥ 0`), `∫_N f*φ` equals
`immersionVolume g f hf hinj o` for a calibration `φ` if and only if `(f, o)` is calibrated by
`φ`. -/
theorem integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion
    (hφ : IsCalibration g φ) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o := by
  refine ⟨fun heq ↦ ?_, fun hcal ↦ hcal.integralTopForm_mpullback_eq⟩
  let gN := g.pullback f (by simpa using hf) hinj
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I' ∞ E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  have : IsContMDiffRiemannianBundle I' 0 E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsManifold I' (∞ + 1) N := by simpa using (inferInstance : IsManifold I' ∞ N)
  have hpull : IsCalibration gN (mpullback I' I f φ) := hφ.mpullback f hf hinj
  have hcont : Continuous (topFormDensity o (mpullback I' I f φ)) :=
    (hpull.isSmoothForm.contMDiff_topFormDensity o).continuous
  have hle (x : N) : topFormDensity o (mpullback I' I f φ) x ≤ 1 :=
    (le_abs_self _).trans ((abs_topFormDensity o _ x).trans_le (hpull.norm_le_one x))
  rw [eq_topFormDensity_smul_riemannianVolumeForm o (mpullback I' I f φ), immersionVolume_def]
    at heq
  have heq' : integralTopForm o (fun x ↦ topFormDensity o (mpullback I' I f φ) x •
      riemannianVolumeForm o x) =
        integralTopForm o (fun x ↦ (1 : ℝ) • riemannianVolumeForm o x) := by
    simpa only [one_smul] using heq
  rw [isCalibratedImmersion_def, eq_riemannianVolumeForm_iff_topFormDensity_eq_one]
  exact (integralTopForm_smul_riemannianVolumeForm_eq_iff_of_le o hcont continuous_const hle).1 heq'

/-- **Equality in the two-sided integrated calibration inequality**: on a compact oriented
`k`-manifold `N`, `|∫_N f*φ| = immersionVolume g f hf hinj o` for a calibration `φ` if and only if
`(f, o)` is calibrated by `φ` or by `-φ`. -/
theorem abs_integralTopForm_mpullback_eq_immersionVolume_iff (hφ : IsCalibration g φ) :
    |integralTopForm o (mpullback I' I f φ)| = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o ∨ IsCalibratedImmersion g (-φ) f hf hinj o := by
  have hnn : 0 ≤ immersionVolume g f hf hinj o := immersionVolume_nonneg g f hf hinj o
  have hneg : integralTopForm o (mpullback I' I f (-φ)) =
      -integralTopForm o (mpullback I' I f φ) := by
    have hpull : mpullback I' I f (-φ) = (-1 : ℝ) • mpullback I' I f φ := by
      funext x
      ext v
      simp
    rw [hpull, integralTopForm_smul, neg_one_mul]
  rw [← integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g f hf hinj o hφ,
    ← integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g f hf hinj o hφ.neg,
    hneg]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases abs_choice (integralTopForm o (mpullback I' I f φ)) with hpos | hneg'
    · exact Or.inl (hpos.symm.trans h)
    · exact Or.inr (hneg'.symm.trans h)
  · rcases h with h | h
    · rw [h, abs_of_nonneg hnn]
    · rw [neg_eq_iff_eq_neg.1 h, abs_neg, abs_of_nonneg hnn]

end EqualityCase

section FundamentalTheorem

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N]
  {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' ∞ N'] [CompactSpace N'] {k : ℕ}

/-- **Single-form volume minimization**: if `(f, o)` is calibrated by a calibration `φ` and a
competing immersion `(f', o')` of a compact oriented `k`-manifold `N'` has the same `φ`-period
`∫_N f*φ = ∫_{N'} f'*φ`, then `immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o'`.
Neither `N` nor `N'` need be boundaryless once the period equality is given. -/
theorem immersionVolume_le_of_integralTopForm_mpullback_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  calc immersionVolume g f hf hinj o
      = integralTopForm o (mpullback I' I f φ) := hcal.integralTopForm_mpullback_eq.symm
    _ = integralTopForm o' (mpullback I'' I f' φ) := hperiod
    _ ≤ immersionVolume g f' hf' hinj' o' :=
        integralTopForm_mpullback_le_immersionVolume g f' hf' hinj' o' hφ

/-- **Equality case of single-form volume minimization**: under the hypotheses of
`immersionVolume_le_of_integralTopForm_mpullback_eq`, the competing immersion `(f', o')` has the
same volume as `(f, o)` if and only if `(f', o')` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' := by
  rw [← hcal.integralTopForm_mpullback_eq, hperiod,
    integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g f' hf' hinj' o' hφ]

/-- **The fundamental theorem of calibrations** (Harvey and Lawson, Theorem II.4.2): an oriented
immersion `(f, o)` calibrated by a smooth calibration `φ` has volume at most that of every
competing immersion `(f', o')` of a compact oriented `k`-manifold `N'` that pairs with every smooth
closed `k`-form on `M` as `(f, o)` does. Boundarylessness and Hausdorffness of the sources are only
needed when establishing the closed-form period hypothesis via Stokes' theorem (for example in
`immersionVolume_le_of_homotopy`), so they are not assumed here. -/
theorem immersionVolume_le_of_isCalibratedImmersion
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  immersionVolume_le_of_integralTopForm_mpullback_eq g φ hφ f hf hinj o hcal f' hf' hinj' o'
    (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

/-- **Equality in the fundamental theorem of calibrations** (Harvey and Lawson, Theorem II.4.2):
a competing immersion `(f', o')` of a compact oriented `k`-manifold `N'` with the same smooth
closed-form periods as a `φ`-calibrated immersion `(f, o)` has the same volume if and only if
`(f', o')` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' :=
  immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq g φ hφ f hf hinj o
    hcal f' hf' hinj' o' (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

end FundamentalTheorem

section StokesAndHomotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] [BoundarylessManifold I' N] [T2Space N] [CompactSpace N]

/-- **Non-exactness of forms calibrating a closed submanifold** (Harvey and Lawson,
Corollary II.4.3): if an `(n + 1)`-form `φ` calibrates an immersion `(f, o)` of a nonempty compact
boundaryless Hausdorff manifold `N`, then `φ` is not the exterior derivative of any `C¹` `n`-form
`α` on `M`. -/
theorem IsCalibratedImmersion.mextDeriv_ne [Nonempty N] {n : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ (n + 1)} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin (n + 1))}
    (hcal : IsCalibratedImmersion g φ f hf hinj o)
    {α : RoughForm I M ℝ n} (hα : IsSmoothForm I 1 α) :
    mextDeriv α ≠ φ := by
  intro h
  have hpull : mpullback I' I f φ = mextDeriv (mpullback I' I f α) := by
    rw [← h, mpullback_mextDeriv (hf.of_le (by simp)) ((isSmoothBundleForm_def 1 α).2 hα.contMDiff)]
  have hzero : integralTopForm o (mpullback I' I f φ) = 0 := by
    rw [hpull]
    exact integralTopForm_mextDeriv_eq_zero o (hα.mpullback (hf.of_le (by simp)))
      (isClosed_tsupport _).isCompact
  exact (immersionVolume_pos g f hf hinj o).ne'
    (hcal.integralTopForm_mpullback_eq.symm.trans hzero)

/-- **Cohomological nontriviality of calibrations** (Harvey and Lawson, Corollary II.4.3): if a
smooth calibration `φ` calibrates an immersion `(f, o)` of a nonempty compact boundaryless
Hausdorff `k`-manifold `N` (in any degree `k ≥ 0`), then the de Rham cohomology class of `φ` in
`deRhamCohomology I M k` is nonzero. -/
theorem IsCalibratedImmersion.deRhamCohomology_mk_ne_zero [Nonempty N] {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ) {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    deRhamCohomology.mk I k
        ⟨hφ.toSmoothForm, (mem_closedForms I _).2 (by
          rw [hφ.coe_toSmoothForm]
          exact hφ.mextDeriv_eq_zero)⟩ ≠
      0 := by
  rw [Ne, deRhamCohomology.mk_eq_zero_iff]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot]
    intro hzero
    have hφ0 : φ = 0 := hφ.coe_toSmoothForm.symm.trans (congrArg Subtype.val hzero)
    have hint : integralTopForm o (mpullback I' I f φ) = 0 := by simp [hφ0]
    exact (immersionVolume_pos g f hf hinj o).ne'
      (hcal.integralTopForm_mpullback_eq.symm.trans hint)
  | succ n =>
    rw [exactForms_succ, LinearMap.mem_range]
    rintro ⟨α, hα⟩
    exact hcal.mextDeriv_ne (α.isSmoothForm.of_le (by simp))
      (by simpa [mextDerivₗ_apply] using (congrArg Subtype.val hα).trans hφ.coe_toSmoothForm)

/-- On a compact boundaryless Hausdorff oriented `k`-manifold `N`, smoothly homotopic maps
`f, f' : N → M` have equal periods on every smooth closed `k`-form `η` on `M`. -/
theorem integralTopForm_mpullback_eq_of_homotopy {k : ℕ}
    (o : Manifold.Orientation I' N (Fin k))
    {f f' : N → M} (hf : ContMDiff I' I ∞ f) (hf' : ContMDiff I' I ∞ f')
    {F : N × Icc (0 : ℝ) 1 → M} (hF : ContMDiff (I'.prod (𝓡∂ 1)) I ∞ F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x)
    {η : RoughForm I M ℝ k} (hη : IsSmoothForm I ∞ η) (hclosed : mextDeriv η = 0) :
    integralTopForm o (mpullback I' I f η) = integralTopForm o (mpullback I' I f' η) := by
  let ηc : closedForms I M k := ⟨⟨η, hη.mem_smoothBundleForms⟩, (mem_closedForms I _).2 hclosed⟩
  have hmap := LinearMap.congr_fun (deRhamCohomology.map_eq_of_homotopy hf hf' hF h₀ h₁ k)
    (deRhamCohomology.mk I k ηc)
  rw [deRhamCohomology.map_mk, deRhamCohomology.map_mk, ← sub_eq_zero, ← map_sub,
    deRhamCohomology.mk_eq_zero_iff] at hmap
  have hexact : SmoothForm.mpullback f hf ηc.1 - SmoothForm.mpullback f' hf' ηc.1 ∈
      exactForms I' N k := by
    simpa only [Submodule.coe_sub, closedForms.coe_mpullback] using hmap
  have hint0 : integralTopForm o
      (SmoothForm.mpullback f hf ηc.1 - SmoothForm.mpullback f' hf' ηc.1).1 = 0 := by
    cases k with
    | zero =>
      rw [exactForms_zero, Submodule.mem_bot] at hexact
      rw [hexact]
      exact integralTopForm_zero o
    | succ n =>
      rw [exactForms_succ, LinearMap.mem_range] at hexact
      obtain ⟨β, hβ⟩ := hexact
      rw [← hβ, mextDerivₗ_apply]
      exact integralTopForm_mextDeriv_eq_zero o (β.isSmoothForm.of_le (by simp))
        (isClosed_tsupport _).isCompact
  have hpullf : (SmoothForm.mpullback f hf ηc.1).1 = mpullback I' I f η :=
    SmoothForm.coe_mpullback f hf ηc.1
  have hpullf' : (SmoothForm.mpullback f' hf' ηc.1).1 = mpullback I' I f' η :=
    SmoothForm.coe_mpullback f' hf' ηc.1
  have hsub : (SmoothForm.mpullback f hf ηc.1 - SmoothForm.mpullback f' hf' ηc.1).1 =
      mpullback I' I f η + (-1 : ℝ) • mpullback I' I f' η := by
    rw [Submodule.coe_sub, hpullf, hpullf', sub_eq_add_neg, neg_one_smul]
  rw [hsub, integralTopForm_add_of_compactSpace o
    ((hη.of_le (by simp)).mpullback (hf.of_le (by simp)))
    (((hη.of_le (by simp)).mpullback (hf'.of_le (by simp))).smul (-1)),
    integralTopForm_smul, neg_one_mul, add_neg_eq_zero] at hint0
  exact hint0

/-- **Smooth-homotopy volume minimization**: on a compact boundaryless Hausdorff oriented
`k`-manifold `N`, an immersion `(f, o)` calibrated by a smooth calibration `φ` minimizes volume
among all smooth immersions `f' : N → M` smoothly homotopic to `f`. -/
theorem immersionVolume_le_of_homotopy {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N → M) (hf' : ContMDiff I' I ∞ f') (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
    {F : N × Icc (0 : ℝ) 1 → M} (hF : ContMDiff (I'.prod (𝓡∂ 1)) I ∞ F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o :=
  immersionVolume_le_of_isCalibratedImmersion g φ hφ f hf hinj o hcal f' hf' hinj' o
    fun _ hη hclosed ↦ integralTopForm_mpullback_eq_of_homotopy o hf hf' hF h₀ h₁ hη hclosed

/-- **Equality in smooth-homotopy volume minimization**: a smooth immersion `f' : N → M` smoothly
homotopic to a `φ`-calibrated immersion `(f, o)` on a compact boundaryless Hausdorff oriented
`k`-manifold `N` has equal volume if and only if `(f', o)` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N → M) (hf' : ContMDiff I' I ∞ f') (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
    {F : N × Icc (0 : ℝ) 1 → M} (hF : ContMDiff (I'.prod (𝓡∂ 1)) I ∞ F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o ↔
      IsCalibratedImmersion g φ f' hf' hinj' o :=
  immersionVolume_eq_iff_isCalibratedImmersion g φ hφ f hf hinj o hcal f' hf' hinj' o
    fun _ hη hclosed ↦ integralTopForm_mpullback_eq_of_homotopy o hf hf' hF h₀ h₁ hη hclosed

end StokesAndHomotopy

section Examples

/-- On any oriented Riemannian manifold `(M, g, o)`, the identity immersion `id : M → M` is
calibrated by `riemannianVolumeForm o` in every dimension `m ≥ 0`. -/
theorem isCalibratedImmersion_id_riemannianVolumeForm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {m : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibratedImmersion g (riemannianVolumeForm o) id contMDiff_id
      (fun x ↦ by simpa [mfderiv_id] using Function.injective_id) o := by
  let rb₁ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let hinj : ∀ x : M, Function.Injective (mfderiv I I id x) :=
    fun x ↦ by simpa [mfderiv_id] using Function.injective_id
  let gid := g.pullback id (by simpa using contMDiff_id) hinj
  let rb₂ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gid.toRiemannianMetric⟩
  rw [isCalibratedImmersion_def]
  exact @mpullback_riemannianVolumeForm_of_isOrientationPreservingAt
    E H M _ _ _ _ I _ _ _ rb₁ m
    E H M _ _ _ _ I _ _ _ rb₂ o o id
    (Manifold.Orientation.isOrientationPreservingAt_id o) fun x u w ↦ by
      rw [ContMDiffRiemannianMetric.inner_riemannianBundle g,
        ContMDiffRiemannianMetric.inner_riemannianBundle gid,
        ContMDiffRiemannianMetric.pullback_inner]

/-- For any orthonormal frame `u : Fin k → V` in a finite-dimensional real inner product space `V`,
the constant smooth `k`-form `SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k u))` is a
calibration on `(V, (riemannianMetricVectorSpace V).ofLE le_top)`. -/
theorem _root_.Orthonormal.isCalibration_const_alternatingFormEquiv_ιMulti
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    {u : Fin k → V} (hu : Orthonormal ℝ u) :
    IsCalibration ((riemannianMetricVectorSpace V).ofLE le_top)
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k u))).1 := by
  rw [isCalibration_const_iff, hu.norm_alternatingFormEquiv_ιMulti]

/-- Every linear isometry between real normed spaces is a smooth immersion: its manifold derivative
at every point is injective. -/
theorem _root_.LinearIsometry.injective_mfderiv
    {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : F →ₗᵢ[ℝ] V) (x : F) :
    Function.Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, V) L x) := by
  have hfderiv : fderiv ℝ (L : F → V) x = L.toContinuousLinearMap :=
    L.toContinuousLinearMap.fderiv
  rw [mfderiv_eq_fderiv, hfderiv]
  exact L.injective

/-- **Every oriented linear isometric subspace is calibrated**: for any linear isometry
`L : F →ₗᵢ[ℝ] V` from an oriented `k`-dimensional real inner product space `(F, oF)` into a
finite-dimensional real inner product space `V` and any positively oriented orthonormal basis `b` of
`F`, the immersion `L : F → V` is calibrated by the constant simple calibration
`SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))` in every dimension `k ≥ 0`. -/
theorem isCalibratedImmersion_linearIsometry_const
    {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (L : F →ₗᵢ[ℝ] V) (oF : Orientation ℝ F (Fin k))
    (b : OrthonormalBasis (Fin k) ℝ F) (hb : b.toBasis.orientation = oF) :
    IsCalibratedImmersion ((riemannianMetricVectorSpace V).ofLE le_top)
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))).1
      L L.contDiff.contMDiff L.injective_mfderiv
      (Manifold.Orientation.model (I := 𝓘(ℝ, F)) oF
        (Module.finrank_eq_card_basis b.toBasis).symm) := by
  let hk : Fintype.card (Fin k) = Module.finrank ℝ F :=
    (Module.finrank_eq_card_basis b.toBasis).symm
  let gV := (riemannianMetricVectorSpace V).ofLE (le_top : ∞ ≤ ⊤)
  let gF := gV.pullback L (by simpa using L.contDiff.contMDiff) L.injective_mfderiv
  let : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) := ⟨gF.toRiemannianMetric⟩
  let oM := Manifold.Orientation.model (I := 𝓘(ℝ, F)) oF hk
  have hmf (x : F) (u : TangentSpace 𝓘(ℝ, F) x) :
      NormedSpace.fromTangentSpace (L x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, V) L x u) =
        L (NormedSpace.fromTangentSpace x u) := by
    have hfderiv : fderiv ℝ (L : F → V) x = L.toContinuousLinearMap :=
      L.toContinuousLinearMap.fderiv
    rw [mfderiv_eq_fderiv, hfderiv]
    rfl
  have hnorm (x : F) (u : TangentSpace 𝓘(ℝ, F) x) :
      ‖(NormedSpace.fromTangentSpace x u : F)‖ = ‖u‖ := by
    let : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
      ⟨(riemannianMetricVectorSpace V).toRiemannianMetric⟩
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    symm
    rw [← real_inner_self_eq_norm_sq, ContMDiffRiemannianMetric.inner_riemannianBundle gF,
      ContMDiffRiemannianMetric.pullback_inner, ContMDiffRiemannianMetric.ofLE_inner,
      ← ContMDiffRiemannianMetric.inner_riemannianBundle (riemannianMetricVectorSpace V),
      real_inner_self_eq_norm_sq, norm_tangentSpace_vectorSpace, hmf, L.norm_map]
  have : Fact (Module.finrank ℝ F = k) := ⟨by simpa using hk.symm⟩
  let A : F [⋀^Fin k]→L[ℝ] ℝ :=
    (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b))).compContinuousLinearMap L.toContinuousLinearMap
  have hAb : A b = 1 := by
    change alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)) (L ∘ b) = 1
    rw [alternatingFormEquiv_apply, real_inner_self_eq_norm_sq,
      (L.orthonormal_comp_iff.2 b.orthonormal).norm_ιMulti, one_pow]
  have hAvol : A = oF.volumeFormL := oF.eq_volumeFormL_of_apply_orthonormal A b hb hAb
  rw [isCalibratedImmersion_def]
  funext x
  let := oM.fact_finrank_tangentSpace x
  let e : TangentSpace 𝓘(ℝ, F) x ≃ₗᵢ[ℝ] F :=
    { (NormedSpace.fromTangentSpace x).toLinearEquiv with norm_map' := hnorm x }
  ext v
  have hlhs : mpullback 𝓘(ℝ, F) 𝓘(ℝ, V) L
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))).1 x v = A (e ∘ v) := by
    rw [mpullback_apply, SmoothForm.const_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact congrArg _ (funext fun i ↦ hmf x (v i))
  have hrhs : riemannianVolumeForm oM x v = oF.volumeFormL (e ∘ v) := by
    rw [riemannianVolumeForm_apply, ← Manifold.Orientation.map_orientationAt_model oF hk x,
      Orientation.volumeFormL_apply]
    exact ((oM.orientationAt x).volumeForm_map e (e ∘ v)).symm.trans
      (congrArg _ (funext fun i ↦ (e.symm_apply_apply (v i)).symm))
  rw [hlhs, hrhs, hAvol]

end Examples

end TauCeti
