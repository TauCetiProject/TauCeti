/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Calibration.Immersion
public import TauCeti.Geometry.Manifold.DeRham.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The Fundamental Theorem of Calibrations and Volume Minimization

This file proves the fundamental theorem of calibrated geometry (Harvey and Lawson, Theorem II.4.2)
together with its equality characterization and Stokes-theoretic consequences on closed manifolds.

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
  represent the same real homology class on closed manifolds, or more generally when the difference
  of the immersed chains bounds a suitable `(k + 1)`-chain so Stokes' theorem establishes period
  equality), then `immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o'`.
* `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion`: under the same hypotheses, the competing
  immersion `(f', o')` achieves equal volume if and only if `(f', o')` is also calibrated by `φ`.
* `TauCeti.IsCalibratedImmersion.mextDeriv_ne` and
  `TauCeti.IsCalibratedImmersion.deRhamCohomology_mk_ne_zero` (Harvey and Lawson, Corollary II.4.3):
  a form that calibrates an immersion of a nonempty closed Hausdorff manifold cannot be exact, so
  the de Rham class of any smooth closed form calibrating such an immersion is nonzero (with no
  global comass bound required).
* `TauCeti.immersionVolume_le_of_homotopy` and
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy`: on a closed oriented
  Hausdorff manifold `N`, a calibrated immersion minimizes volume among all smooth immersions
  `C²`-homotopic to it, with equality if and only if the homotopic immersion is itself calibrated
  by `φ`.

## References

* F. R. Harvey and H. B. Lawson Jr., *Calibrated geometries*, Acta Math. 148 (1982), 47–157,
  Theorem II.4.2 and Corollary II.4.3.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. 6 (1998), 705–747.
-/

public section

noncomputable section

open Bundle Set
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
  have := Bundle.instIsContMDiffRiemannianBundle gN
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  have : IsContMDiffRiemannianBundle I' 0 E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsManifold I' (∞ + 1) N := by simpa using (inferInstance : IsManifold I' ∞ N)
  have hpull := hφ.mpullback f hf hinj
  have hcont := (hpull.isSmoothForm.contMDiff_topFormDensity o).continuous
  have hle (x : N) :=
    (le_abs_self _).trans ((abs_topFormDensity o _ x).trans_le (hpull.norm_le_one x))
  rw [eq_topFormDensity_smul_riemannianVolumeForm o (mpullback I' I f φ),
    immersionVolume_def] at heq
  rw [isCalibratedImmersion_def, eq_riemannianVolumeForm_iff_topFormDensity_eq_one]
  exact (integralTopForm_smul_riemannianVolumeForm_eq_iff_of_le o hcont continuous_const hle).1
    (by simpa only [one_smul] using heq)

/-- **Equality in the two-sided integrated calibration inequality**: on a compact oriented
`k`-manifold `N`, `|∫_N f*φ| = immersionVolume g f hf hinj o` for a calibration `φ` if and only if
`(f, o)` is calibrated by `φ` or by `-φ`. -/
theorem abs_integralTopForm_mpullback_eq_immersionVolume_iff (hφ : IsCalibration g φ) :
    |integralTopForm o (mpullback I' I f φ)| = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o ∨ IsCalibratedImmersion g (-φ) f hf hinj o := by
  have hneg : integralTopForm o (mpullback I' I f (-φ)) =
      -integralTopForm o (mpullback I' I f φ) := by
    have hpull : mpullback I' I f (-φ) = (-1 : ℝ) • mpullback I' I f φ := by funext x; ext v; simp
    rw [hpull, integralTopForm_smul, neg_one_mul]
  rw [abs_eq (immersionVolume_nonneg g f hf hinj o),
    ← integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g f hf hinj o hφ,
    ← integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g f hf hinj o hφ.neg,
    hneg, neg_eq_iff_eq_neg]

end EqualityCase

section FundamentalTheorem

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' ∞ N'] [CompactSpace N'] {k : ℕ}
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
  (hφ : IsCalibration g φ) (f : N → M) (hf : ContMDiff I' I ∞ f)
  (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) (o : Manifold.Orientation I' N (Fin k))
  (hcal : IsCalibratedImmersion g φ f hf hinj o) (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
  (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
  (o' : Manifold.Orientation I'' N' (Fin k))

include hφ hcal

/-- **Single-form volume minimization**: if `(f, o)` is calibrated by a calibration `φ` and a
competing immersion `(f', o')` of a compact oriented `k`-manifold `N'` has the same `φ`-period
`∫_N f*φ = ∫_{N'} f'*φ`, then `immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o'`.
Neither `N` nor `N'` need be boundaryless once the period equality is given. -/
theorem immersionVolume_le_of_integralTopForm_mpullback_eq
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  (hcal.integralTopForm_mpullback_eq.symm.trans hperiod).trans_le
    (integralTopForm_mpullback_le_immersionVolume g f' hf' hinj' o' hφ)

/-- **Equality case of single-form volume minimization**: under the hypotheses of
`immersionVolume_le_of_integralTopForm_mpullback_eq`, the competing immersion `(f', o')` has the
same volume as `(f, o)` if and only if `(f', o')` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq
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
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' :=
  immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq g φ hφ f hf hinj o
    hcal f' hf' hinj' o' (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

end FundamentalTheorem

section StokesAndHomotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
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
    {o : Manifold.Orientation I' N (Fin (n + 1))} (hcal : IsCalibratedImmersion g φ f hf hinj o)
    {α : RoughForm I M ℝ n} (hα : IsSmoothForm I 1 α) : mextDeriv α ≠ φ := by
  intro h
  have hzero : integralTopForm o (mpullback I' I f φ) = 0 := by
    rw [← h, mpullback_mextDeriv (hf.of_le (by simp)) ((isSmoothBundleForm_def 1 α).2 hα.contMDiff)]
    exact integralTopForm_mextDeriv_eq_zero o (hα.mpullback (hf.of_le (by simp)))
      (isClosed_tsupport _).isCompact
  exact (immersionVolume_pos g f hf hinj o).ne'
    (hcal.integralTopForm_mpullback_eq.symm.trans hzero)

/-- **Cohomological nontriviality of calibrated closed forms** (Harvey and Lawson,
Corollary II.4.3): if a smooth closed `k`-form `φ` calibrates an immersion `(f, o)` of a nonempty
compact boundaryless Hausdorff `k`-manifold `N` (in any degree `k ≥ 0`), then the de Rham
cohomology class of `φ` in `deRhamCohomology I M k` is nonzero. No global comass bound on `φ` is
required. -/
theorem IsCalibratedImmersion.deRhamCohomology_mk_ne_zero [Nonempty N] {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : closedForms I M k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)} {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ.1.1 f hf hinj o) :
    deRhamCohomology.mk I k φ ≠ 0 := by
  rw [Ne, deRhamCohomology.mk_eq_zero_iff]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot]; intro hzero
    have hφ0 : φ.1.1 = 0 := congrArg Subtype.val hzero
    exact (immersionVolume_pos g f hf hinj o).ne'
      (hcal.integralTopForm_mpullback_eq.symm.trans (by simp [hφ0]))
  | succ n =>
    rw [exactForms_succ, LinearMap.mem_range]; rintro ⟨α, hα⟩
    exact hcal.mextDeriv_ne (α.isSmoothForm.of_le (by simp))
      (by simpa [mextDerivₗ_apply] using congrArg Subtype.val hα)

section Homotopy

variable {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (φ : RoughForm I M ℝ k) (hφ : IsCalibration g φ) (f : N → M) (hf : ContMDiff I' I ∞ f)
  (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) (o : Manifold.Orientation I' N (Fin k))
  (hcal : IsCalibratedImmersion g φ f hf hinj o) (f' : N → M) (hf' : ContMDiff I' I ∞ f')
  (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
  {F : N × Icc (0 : ℝ) 1 → M} (hF : ContMDiff (I'.prod (𝓡∂ 1)) I 2 F)
  (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x)

include hφ hcal hF h₀ h₁

/-- **Homotopy volume minimization**: on a compact boundaryless Hausdorff oriented `k`-manifold `N`,
an immersion `(f, o)` calibrated by a smooth calibration `φ` minimizes volume among all smooth
immersions `f' : N → M` `C²`-homotopic to `f`. -/
theorem immersionVolume_le_of_homotopy :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o :=
  immersionVolume_le_of_isCalibratedImmersion g φ hφ f hf hinj o hcal f' hf' hinj' o
    fun _ hη hclosed ↦ integralTopForm_mpullback_eq_of_homotopy o hF h₀ h₁
      (hη.of_le (by simp)) hclosed

/-- **Equality in homotopy volume minimization**: a smooth immersion `f' : N → M` `C²`-homotopic to
a `φ`-calibrated immersion `(f, o)` on a compact boundaryless Hausdorff oriented `k`-manifold `N`
has equal volume if and only if `(f', o)` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o ↔
      IsCalibratedImmersion g φ f' hf' hinj' o :=
  immersionVolume_eq_iff_isCalibratedImmersion g φ hφ f hf hinj o hcal f' hf' hinj' o
    fun _ hη hclosed ↦ integralTopForm_mpullback_eq_of_homotopy o hF h₀ h₁
      (hη.of_le (by simp)) hclosed

end Homotopy

end StokesAndHomotopy

end TauCeti
