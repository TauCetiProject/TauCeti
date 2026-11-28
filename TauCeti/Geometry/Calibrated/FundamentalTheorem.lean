/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Calibrated.Basic
public import TauCeti.Geometry.Calibrated.Immersion
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
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
if and only if `f` is calibrated by `φ` (or by `±φ` in the absolute bound;
`TauCeti.integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion`,
`TauCeti.abs_integralTopForm_mpullback_eq_immersionVolume_iff`), specializing the intrinsic
compact-manifold comass theorems from `TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral`.

Combining the compact-source bound on `f' : N' → M` with calibration of `f` gives single-form
period minimization (`TauCeti.immersionVolume_le_of_integralTopForm_mpullback_eq`,
`TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq`) and, for a
closed calibration `φ`, `TauCeti.immersionVolume_le_of_isCalibratedImmersion` and
`TauCeti.immersionVolume_eq_iff_isCalibratedImmersion` for any calibrated immersion `f : N → M` and
compact competitor `f' : N' → M` (allowing boundary or corners) that have equal `integralTopForm`
periods on all smooth closed `k`-forms. When `N` is also compact, `immersionVolume` agrees with
`riemannianTotalVolume` (`TauCeti.immersionVolume_eq_riemannianTotalVolume`), specializing on closed
sources to Harvey–Lawson's homological volume-minimization theorem (whereas on noncompact `N`,
`immersionVolume` and `integralTopForm o (mpullback I' I f φ)` both evaluate to `0` by
`integralTopForm`'s compact-support fallback).

Applying Stokes' theorem away from the boundary yields two further consequences:
* **Cohomological nontriviality** (`TauCeti.IsCalibratedImmersion.mextDeriv_ne`,
  `TauCeti.IsCalibratedImmersion.deRhamCohomology_mk_ne_zero`; Harvey–Lawson, Corollary II.4.3): a
  form calibrating a nonempty closed Hausdorff manifold cannot be exact, so the de Rham cohomology
  class of any smooth closed form calibrating such an immersion is nonzero (with no global comass
  bound required).
* **Homotopy volume minimization** (`TauCeti.immersionVolume_le_of_homotopy_disjoint_boundary`,
  `TauCeti.immersionVolume_le_of_homotopy`, and their equality characterizations): on a compact
  Hausdorff oriented smooth manifold `N` (possibly with boundary or corners), a calibrated immersion
  minimizes volume among all smooth immersions joined to it by a `C²` homotopy stationary near
  `I'.boundary N` (unconditionally when `N` is boundaryless), with equality if and only if the
  competitor is also calibrated by `φ`.

## Main results

* `TauCeti.abs_mpullback_apply_le_abs_riemannianVolumeForm`,
  `TauCeti.abs_mpullback_apply_le_riemannianVolumeForm`, and
  `TauCeti.mpullback_apply_le_riemannianVolumeForm`: pointwise calibration inequalities in every
  degree `k : ℕ`.
* `TauCeti.integralTopForm_mpullback_le_immersionVolume` and
  `TauCeti.abs_integralTopForm_mpullback_le_immersionVolume`: integrated calibration inequalities on
  compact sources.
* `TauCeti.integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion` and
  `TauCeti.abs_integralTopForm_mpullback_eq_immersionVolume_iff`: equality cases of the integrated
  calibration inequalities.
* `TauCeti.immersionVolume_le_of_integralTopForm_mpullback_eq`,
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq`,
  `TauCeti.immersionVolume_le_of_isCalibratedImmersion`, and
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion`: single-form and closed-period volume
  minimization and their equality characterizations.
* `TauCeti.IsCalibratedImmersion.mextDeriv_ne` and
  `TauCeti.IsCalibratedImmersion.deRhamCohomology_mk_ne_zero`: non-exactness and nonzero de Rham
  class of forms calibrating closed submanifolds.
* `TauCeti.immersionVolume_le_of_homotopy_disjoint_boundary`,
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy_disjoint_boundary`,
  `TauCeti.immersionVolume_le_of_homotopy`, and
  `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy`: volume minimization under
  interior-supported and boundaryless `C²` homotopies.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.4.2 and Corollary II.4.3.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Section 2.1.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998), 705–747,
  Section 1, p. 706.
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped Bundle ContDiff Manifold Topology

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

/-- **Equality case of the absolute integrated calibration inequality** on a compact source: for a
continuous `k`-form `φ` (`IsSmoothForm I 0 φ`) of comass at most `1` for `g` along `f`,
`|∫_N f^* φ| = Vol(f)` holds if and only if `(f, o)` is calibrated by `φ` or by `-φ`. -/
theorem abs_integralTopForm_mpullback_eq_immersionVolume_iff [CompactSpace N]
    {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
    (hcomass : ∀ x (v : Fin k → TangentSpace I (f x)),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |φ (f x) v| ≤ 1) :
    |integralTopForm o (mpullback I' I f φ)| = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o ∨ IsCalibratedImmersion g (-φ) f hf hinj o := by
  have hneg : integralTopForm o (mpullback I' I f (-φ)) =
      -integralTopForm o (mpullback I' I f φ) := by
    rw [← neg_one_smul ℝ φ, mpullback_smul, integralTopForm_smul, neg_one_mul]
  have hcomass_neg : ∀ x (v : Fin k → TangentSpace I (f x)),
      (∀ i j, g.inner (f x) (v i) (v j) = if i = j then 1 else 0) → |(-φ) (f x) v| ≤ 1 :=
    fun x v hv ↦ by
      simpa only [Pi.neg_apply, ContinuousAlternatingMap.neg_apply, abs_neg] using hcomass x v hv
  rw [abs_eq (immersionVolume_nonneg g f hf hinj o),
    ← integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g hφ f hf hinj o
      hcomass,
    ← integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g hφ.neg f hf hinj o
      hcomass_neg,
    hneg, neg_eq_iff_eq_neg]

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

/-- **Single-form volume minimization**: if an oriented immersion `f : N → M` is calibrated by `φ`
and a compact oriented competitor `f' : N' → M` (allowing boundary or corners) satisfies
`∫_N f^* φ = ∫_{N'} f'^* φ` with `φ` of comass at most `1` along `f'`, then
`immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o'`. -/
theorem immersionVolume_le_of_integralTopForm_mpullback_eq {k : ℕ} [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hcomass : ∀ x (v : Fin k → TangentSpace I (f' x)),
      (∀ i j, g.inner (f' x) (v i) (v j) = if i = j then 1 else 0) → |φ (f' x) v| ≤ 1)
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  (hcal.integralTopForm_mpullback_eq_immersionVolume.symm.trans hperiod).trans_le
    (integralTopForm_mpullback_le_immersionVolume g f' hf' hinj' o' hcomass)

/-- **Equality case of single-form volume minimization**: under equal `φ`-periods for a
`φ`-calibrated immersion `f` and a compact oriented competitor `f'` along which the continuous form
`φ` (`IsSmoothForm I 0 φ`) has comass at most `1`, the equality
`immersionVolume g f ... = immersionVolume g f' ...` holds if and only if `f'` is also calibrated by
`φ` with its orientation `o'`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq {k : ℕ}
    [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {φ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I 0 φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hcomass : ∀ x (v : Fin k → TangentSpace I (f' x)),
      (∀ i j, g.inner (f' x) (v i) (v j) = if i = j then 1 else 0) → |φ (f' x) v| ≤ 1)
    (hperiod : integralTopForm o (mpullback I' I f φ) =
      integralTopForm o' (mpullback I'' I f' φ)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' := by
  rw [← hcal.integralTopForm_mpullback_eq_immersionVolume, hperiod,
    integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion g hφ f' hf' hinj' o'
      hcomass]

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
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' :=
  immersionVolume_le_of_integralTopForm_mpullback_eq g φ f hf hinj o hcal f' hf' hinj' o'
    (fun x ↦ hφ.abs_apply_le_one (f' x)) (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

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
      IsCalibratedImmersion g φ f' hf' hinj' o' :=
  immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq g
    (hφ.isSmoothForm.of_le (by simp)) f hf hinj o hcal f' hf' hinj' o'
    (fun x ↦ hφ.abs_apply_le_one (f' x)) (hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero)

end FundamentalTheorem

/-! ### Stokes consequences: non-exactness and homotopy volume minimization -/

section StokesAndHomotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] [T2Space N] [CompactSpace N]

/-- **Non-exactness of forms calibrating a closed submanifold** (Harvey–Lawson 1982,
Corollary II.4.3): if an `(n + 1)`-form `φ` calibrates an immersion `(f, o)` of a nonempty compact
boundaryless Hausdorff smooth manifold `N`, then `φ` is not the exterior derivative of any `C¹`
`n`-form `α` on `M`. -/
theorem IsCalibratedImmersion.mextDeriv_ne [BoundarylessManifold I' N] [Nonempty N] {n : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ (n + 1)} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin (n + 1))} (hcal : IsCalibratedImmersion g φ f hf hinj o)
    {α : RoughForm I M ℝ n} (hα : IsSmoothForm I 1 α) : mextDeriv α ≠ φ := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  intro h
  have hzero : integralTopForm o (mpullback I' I f φ) = 0 := by
    rw [← h, mpullback_mextDeriv (hf.of_le (by simp)) ((isSmoothBundleForm_def 1 α).2 hα.contMDiff)]
    exact integralTopForm_mextDeriv_eq_zero o (hα.mpullback (hf.of_le (by simp)))
      (isClosed_tsupport _).isCompact
  exact (immersionVolume_pos g f hf hinj o).ne'
    (hcal.integralTopForm_mpullback_eq_immersionVolume.symm.trans hzero)

/-- **Cohomological nontriviality of calibrated closed forms** (Harvey–Lawson 1982,
Corollary II.4.3): if a smooth closed `k`-form `φ` calibrates an immersion `(f, o)` of a nonempty
compact boundaryless Hausdorff smooth `k`-manifold `N` (in any degree `k ≥ 0`), then the de Rham
cohomology class of `φ` in `deRhamCohomology I M k` is nonzero. No global comass bound on `φ` is
required. -/
theorem IsCalibratedImmersion.deRhamCohomology_mk_ne_zero [BoundarylessManifold I' N] [Nonempty N]
    {k : ℕ} {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : closedForms I M k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)} {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ.val.val f hf hinj o) :
    deRhamCohomology.mk I k φ ≠ 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  rw [Ne, deRhamCohomology.mk_eq_zero_iff]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot]; intro hzero
    have hφ0 : φ.val.val = 0 := congrArg Subtype.val hzero
    exact (immersionVolume_pos g f hf hinj o).ne'
      (hcal.integralTopForm_mpullback_eq_immersionVolume.symm.trans (by simp [hφ0]))
  | succ n =>
    rw [exactForms_succ, LinearMap.mem_range]; rintro ⟨α, hα⟩
    exact hcal.mextDeriv_ne (α.isSmoothForm.of_le (by simp))
      (by simpa only [mextDerivₗ_apply] using congrArg Subtype.val hα)

section Homotopy

variable {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (φ : RoughForm I M ℝ k) (hφ : IsCalibration g φ) (f : N → M) (hf : ContMDiff I' I ∞ f)
  (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) (o : Manifold.Orientation I' N (Fin k))
  (hcal : IsCalibratedImmersion g φ f hf hinj o) (f' : N → M) (hf' : ContMDiff I' I ∞ f')
  (hinj' : ∀ x, Function.Injective (mfderiv I' I f' x))
  {F : N × Icc (0 : ℝ) 1 → M} (hF : ContMDiff (I'.prod (𝓡∂ 1)) I 2 F)
  (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x)

include hφ hcal hF h₀ h₁

/-- **Interior-homotopy volume minimization**: on a compact Hausdorff oriented smooth `k`-manifold
`N` (possibly with boundary or corners), an immersion `(f, o)` calibrated by a smooth calibration
`φ` minimizes volume among all smooth immersions `f' : N → M` joined to `f` by a `C²` homotopy `F`
whose time-varying locus has closure disjoint from `I'.boundary N`. -/
theorem immersionVolume_le_of_homotopy_disjoint_boundary
    (hd : Disjoint (closure {x : N | ∃ t, F (x, t) ≠ F (x, 0)}) (I'.boundary N)) :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
    haveI : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  exact immersionVolume_le_of_integralTopForm_mpullback_eq g φ f hf hinj o hcal f' hf' hinj' o
    (fun x ↦ hφ.abs_apply_le_one (f' x))
    (integralTopForm_mpullback_eq_of_disjoint_boundary o hF h₀ h₁ hd
      (hφ.isSmoothForm.of_le (by simp)) hφ.mextDeriv_eq_zero)

/-- **Equality in interior-homotopy volume minimization**: under the hypotheses of
`immersionVolume_le_of_homotopy_disjoint_boundary`, `f'` achieves equal volume if and only if
`(f', o)` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy_disjoint_boundary
    (hd : Disjoint (closure {x : N | ∃ t, F (x, t) ≠ F (x, 0)}) (I'.boundary N)) :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
    haveI : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o ↔
      IsCalibratedImmersion g φ f' hf' hinj' o := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  exact immersionVolume_eq_iff_isCalibratedImmersion_of_integralTopForm_mpullback_eq g
    (hφ.isSmoothForm.of_le (by simp)) f hf hinj o hcal f' hf' hinj' o
    (fun x ↦ hφ.abs_apply_le_one (f' x))
    (integralTopForm_mpullback_eq_of_disjoint_boundary o hF h₀ h₁ hd
      (hφ.isSmoothForm.of_le (by simp)) hφ.mextDeriv_eq_zero)

/-- **Homotopy volume minimization**: on a compact boundaryless Hausdorff oriented smooth
`k`-manifold `N`, an immersion `(f, o)` calibrated by a smooth calibration `φ` minimizes volume
among all smooth immersions `f' : N → M` `C²`-homotopic to `f`. -/
theorem immersionVolume_le_of_homotopy [BoundarylessManifold I' N] :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
    haveI : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o :=
  immersionVolume_le_of_homotopy_disjoint_boundary g φ hφ f hf hinj o hcal f' hf' hinj' hF h₀ h₁
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

/-- **Equality in homotopy volume minimization**: a smooth immersion `f' : N → M` `C²`-homotopic to
a `φ`-calibrated immersion `(f, o)` on a compact boundaryless Hausdorff oriented smooth `k`-manifold
`N` has equal volume if and only if `(f', o)` is also calibrated by `φ`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy [BoundarylessManifold I' N] :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
    haveI : IsManifold I' 1 N := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o ↔
      IsCalibratedImmersion g φ f' hf' hinj' o :=
  immersionVolume_eq_iff_isCalibratedImmersion_of_homotopy_disjoint_boundary g φ hφ f hf hinj o hcal
    f' hf' hinj' hF h₀ h₁
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

end Homotopy

end StokesAndHomotopy

end TauCeti
