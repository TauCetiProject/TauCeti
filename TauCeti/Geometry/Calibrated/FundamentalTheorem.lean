/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Calibrated.Basic
public import TauCeti.Geometry.Calibrated.Immersion
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The fundamental theorem of calibrations

On any oriented smooth immersion `f : N → M` in every degree `k : ℕ`, a form `φ` of comass at most
`1` at `f x` satisfies the pointwise calibration inequalities `|f^* φ(v)| ≤ |dvol_{f^* g}(v)|` on
arbitrary tangent `k`-tuples `v` and `|f^* φ(c)| ≤ dvol_{f^* g}(c)` on positively oriented tangent
bases `c`, specializing the intrinsic top-form bounds from
`TauCeti.Geometry.Manifold.Riemannian.VolumeForm`.

On a compact source `N` (`[CompactSpace N]`, which is already equivalent to
`IntegrableTopForm (riemannianVolumeForm o)` under `integralTopForm`'s compact-support convention),
integrating yields `∫_N f^* φ ≤ Vol(f)` and `|∫_N f^* φ| ≤ Vol(f)` for every rough `k`-form `φ` of
comass at most `1` along `f` (`TauCeti.integralTopForm_mpullback_le_immersionVolume`,
`TauCeti.abs_integralTopForm_mpullback_le_immersionVolume`; when `f^* φ` is not integrable, the
left-hand side evaluates to `0` by `integralTopForm`'s fallback and the inequality holds by
nonnegativity of `immersionVolume`). When `φ` is continuous (`IsSmoothForm I 0 φ`), equality holds
if and only if `f` is calibrated by `φ`
(`TauCeti.integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion`), specializing the
intrinsic compact-manifold comass theorems from
`TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral`.

Combining the compact-source bound on `f' : N' → M` with closedness of a calibration `φ` gives
`TauCeti.immersionVolume_le_of_isCalibratedImmersion` and
`TauCeti.immersionVolume_eq_iff_isCalibratedImmersion` for any calibrated immersion `f : N → M` and
compact competitor `f' : N' → M` (allowing boundary or corners) that have equal `integralTopForm`
periods on all smooth closed `k`-forms. When `N` is also compact, `immersionVolume` agrees with
`riemannianTotalVolume` (`TauCeti.immersionVolume_eq_riemannianTotalVolume`), specializing on closed
sources to Harvey–Lawson's homological volume-minimization theorem (whereas on noncompact `N`,
`immersionVolume` and `integralTopForm o (mpullback I' I f φ)` both evaluate to `0` by
`integralTopForm`'s compact-support fallback).

## Main results

* `TauCeti.abs_mpullback_apply_le_abs_riemannianVolumeForm`,
  `TauCeti.abs_mpullback_apply_le_riemannianVolumeForm`, and
  `TauCeti.mpullback_apply_le_riemannianVolumeForm`: pointwise calibration inequalities in every
  degree `k : ℕ`.
* `TauCeti.integralTopForm_mpullback_le_immersionVolume` and
  `TauCeti.abs_integralTopForm_mpullback_le_immersionVolume`: integrated calibration inequalities on
  compact sources.
* `TauCeti.integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion`: equality in the
  compact-source integrated bound holds iff the immersion is calibrated by `φ`.
* `TauCeti.immersionVolume_le_of_isCalibratedImmersion` and
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion`: the fundamental theorem of calibrations
  and its equality characterization.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.4.2.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Section 2.1.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998), 705–747,
  Section 1, p. 706.
-/

public section

noncomputable section

open Bundle Manifold
open scoped Bundle ContDiff Manifold

namespace TauCeti

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]

/-! ### Pointwise and integrated calibration inequalities -/

/-- **Pointwise calibration inequality** on arbitrary tangent `k`-tuples: in every degree `k : ℕ`,
if `φ` has comass at most `1` for `g` at `f x`, then `|f^* φ(v)| ≤ |dvol_{f^* g}(v)|` for every
`v : Fin k → T_x N`. -/
theorem abs_mpullback_apply_le_abs_riemannianVolumeForm {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (hcomass : ∀ v : Fin k → TangentSpace I (f x),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1)
    (v : Fin k → TangentSpace I' x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
    |mpullback I' I f φ x v| ≤ |riemannianVolumeForm o x v| := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  exact abs_apply_le_abs_riemannianVolumeForm o x (mpullback I' I f φ x)
    (fun u hu ↦ by
      rw [mpullback_apply]
      exact hcomass (mfderiv I' I f x ∘ u) ((g.orthonormal_pullback_iff f hf hinj x u).1 hu))
    v

/-- **Pointwise calibration inequality** on positively oriented tangent bases: in every degree
`k : ℕ`, if `φ` has comass at most `1` for `g` at `f x`, then `|f^* φ(c)| ≤ dvol_{f^* g}(c)` on
every positively oriented tangent basis `c` of `T_x N`. -/
theorem abs_mpullback_apply_le_riemannianVolumeForm {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (hcomass : ∀ v : Fin k → TangentSpace I (f x),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I' x)) (hc : c.orientation = o.orientationAt x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
    |mpullback I' I f φ x c| ≤ riemannianVolumeForm o x c := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  exact abs_apply_le_riemannianVolumeForm o x (mpullback I' I f φ x)
    (fun u hu ↦ by
      rw [mpullback_apply]
      exact hcomass (mfderiv I' I f x ∘ u) ((g.orthonormal_pullback_iff f hf hinj x u).1 hu))
    c hc

/-- Signed pointwise calibration inequality in every degree `k : ℕ`: if `φ` has comass at most `1`
for `g` at `f x`, then `f^* φ(c) ≤ dvol_{f^* g}(c)` on every positively oriented tangent basis `c`
of `T_x N`. -/
theorem mpullback_apply_le_riemannianVolumeForm {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (hcomass : ∀ v : Fin k → TangentSpace I (f x),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I' x)) (hc : c.orientation = o.orientationAt x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
    mpullback I' I f φ x c ≤ riemannianVolumeForm o x c :=
  (le_abs_self _).trans (abs_mpullback_apply_le_riemannianVolumeForm g f hf hinj o x hcomass c hc)

/-- **Integrated calibration inequality** on a compact source: if `φ` has comass at most `1` for `g`
at `f x` for every `x : N`, then `∫_N f^* φ ≤ Vol(f)`. When `f^* φ` is not integrable, the
left-hand side evaluates to `0` and the inequality holds by nonnegativity of `immersionVolume`. -/
theorem integralTopForm_mpullback_le_immersionVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
    (hcomass : ∀ x (v : Fin k → TangentSpace I (f x)),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1) :
    integralTopForm o (mpullback I' I f φ) ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace I' y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_def]
  exact integralTopForm_le_riemannianVolumeForm o fun x v hv ↦ by
    rw [mpullback_apply]
    exact hcomass x (mfderiv I' I f x ∘ v) ((g.orthonormal_pullback_iff f hf hinj x v).1 hv)

/-- Absolute integrated calibration inequality on a compact source: if `φ` has comass at most `1`
for `g` at `f x` for every `x : N`, then `|∫_N f^* φ| ≤ Vol(f)`. When `f^* φ` is not integrable,
the left-hand side evaluates to `0` and the inequality holds by nonnegativity of
`immersionVolume`. -/
theorem abs_integralTopForm_mpullback_le_immersionVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
    (hcomass : ∀ x (v : Fin k → TangentSpace I (f x)),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1) :
    |integralTopForm o (mpullback I' I f φ)| ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace I' y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_def]
  exact abs_integralTopForm_le_riemannianVolumeForm o fun x v hv ↦ by
    rw [mpullback_apply]
    exact hcomass x (mfderiv I' I f x ∘ v) ((g.orthonormal_pullback_iff f hf hinj x v).1 hv)

/-- **Equality case of the integrated calibration inequality** on a compact source: for a continuous
`k`-form `φ` (`IsSmoothForm I 0 φ`) of comass at most `1` for `g` along `f`, `∫_N f^* φ = Vol(f)`
holds if and only if the immersion `f` is calibrated by `φ` with its orientation `o`. -/
theorem integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion [CompactSpace N]
    {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
    (hcomass : ∀ x (v : Fin k → TangentSpace I (f x)),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace I' y) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  have : IsManifold I' (0 + 1) N := by simpa using ‹IsManifold I' 1 N›
  rw [immersionVolume_def, isCalibratedImmersion_iff]
  exact integralTopForm_eq_riemannianVolumeForm_iff o (hφ.mpullback (hf.of_le (by simp)))
    fun x v hv ↦ by
      rw [mpullback_apply]
      exact hcomass x (mfderiv I' I f x ∘ v) ((g.orthonormal_pullback_iff f hf hinj x v).1 hv)

end Immersions

/-! ### The fundamental theorem of calibrations -/

section FundamentalTheorem

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]
  {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace N']
  [ChartedSpace H'' N'] [IsManifold I'' 1 N']

/-- **The fundamental theorem of calibrations**: an oriented immersion `f : N → M` calibrated by a
smooth calibration `φ` has `immersionVolume` at most that of every compact oriented immersion
`f' : N' → M` (allowing boundary or corners) whose `integralTopForm` periods agree with those of `f`
on every smooth closed `k`-form `η` (Harvey–Lawson 1982, Theorem II.4.2; McLean 1998, Section 1,
p. 706).
Holds in every degree `k : ℕ`, including degree zero. When `N` is also compact (`[CompactSpace N]`),
both sides equal the total Riemannian volumes of `f^* g` and `f'^* g`
(`immersionVolume_eq_riemannianTotalVolume`), recovering Riemannian volume minimization within a
real homology class on closed sources; on noncompact `N`, `immersionVolume g f hf hinj o` evaluates
to `0` (`immersionVolume_eq_zero_of_not_compactSpace`). -/
theorem immersionVolume_le_of_isCalibratedImmersion {k : ℕ} [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' := by
  calc immersionVolume g f hf hinj o
      = integralTopForm o (mpullback I' I f φ) :=
        hcal.integralTopForm_mpullback_eq_immersionVolume.symm
    _ = integralTopForm o' (mpullback I'' I f' φ) :=
        hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero
    _ ≤ immersionVolume g f' hf' hinj' o' :=
        integralTopForm_mpullback_le_immersionVolume g f' hf' hinj' o'
          fun x ↦ hφ.abs_apply_le_one (f' x)

/-- **Equality case of the fundamental theorem of calibrations**: under equal `integralTopForm`
periods on smooth closed `k`-forms for a calibrated immersion `f : N → M` and a compact oriented
competitor `f' : N' → M`, `immersionVolume g f ... = immersionVolume g f' ...` holds if and only if
`f'` is itself calibrated by `φ` with its orientation `o'`. When `N` is also compact, this
characterizes equality of total Riemannian volumes (`immersionVolume_eq_riemannianTotalVolume`),
whereas on noncompact `N` the left-hand side is `0`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion {k : ℕ} [CompactSpace N']
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
      IsCalibratedImmersion g φ f' hf' hinj' o' := by
  rw [← hcal.integralTopForm_mpullback_eq_immersionVolume,
    hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero,
    integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g
      (hφ.isSmoothForm.of_le (by simp)) f' hf' hinj' o' fun x ↦ hφ.abs_apply_le_one (f' x)]

end FundamentalTheorem

end TauCeti
