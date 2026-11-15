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
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ZeroDim
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The fundamental theorem of calibrations

On any oriented smooth immersion `f : N → M` in every degree `k : ℕ`, a form `φ` of pointwise
comass at most `1` satisfies the pointwise calibration inequalities
`|f^* φ(v)| ≤ |dvol_{f^* g}(v)|` on arbitrary tangent `k`-tuples `v` and
`|f^* φ(c)| ≤ dvol_{f^* g}(c)` on positively oriented tangent bases `c`.

On a compact source `N` (`[CompactSpace N]`, which is already equivalent to
`IntegrableTopForm (riemannianVolumeForm o)` under `integralTopForm`'s compact-support convention),
integrating yields `∫_N f^* φ ≤ Vol(f)` and `|∫_N f^* φ| ≤ Vol(f)` for every rough `k`-form `φ` of
pointwise comass at most `1` (`TauCeti.integralTopForm_mpullback_le_immersionVolume`,
`TauCeti.abs_integralTopForm_mpullback_le_immersionVolume`; when `f^* φ` is not integrable, the
left-hand side evaluates to `0` by `integralTopForm`'s fallback and the inequality holds by
nonnegativity of `immersionVolume`). When `φ` is continuous (`IsSmoothForm I 0 φ`), equality holds
if and only if `f` is calibrated by `φ`
(`TauCeti.integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion`). Positive degree
uses positivity of top-form integration (`TauCeti.integralTopForm_nonneg`,
`TauCeti.integralTopForm_pos`), while degree zero evaluates directly as a finite signed sum
(`TauCeti.integralTopForm_finite_zeroDim`).

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
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Theorem 2.2.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998), 705–747,
  Section 2 (smooth-immersion formulation of the homological volume bound).
-/

public section

noncomputable section

open Bundle Manifold Set TopologicalSpace
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
if `φ` has pointwise comass at most `1` for `g`, then `|f^* φ(v)| ≤ |dvol_{f^* g}(v)|` for every
`v : Fin k → T_x N`. -/
theorem abs_mpullback_apply_le_abs_riemannianVolumeForm {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (v : Fin k → TangentSpace I' x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    |mpullback I' I f φ x v| ≤ |riemannianVolumeForm o x v| := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  let b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex
      (finCongr (by simpa using o.finrank_tangentSpace_eq x))
  have hφb : |mpullback I' I f φ x b.toBasis| ≤ 1 := by
    rw [mpullback_apply, b.coe_toBasis]
    exact hcomass (f x) (mfderiv I' I f x ∘ b) fun i j ↦ by
      dsimp only [Function.comp_apply]
      rw [← ContMDiffRiemannianMetric.pullback_inner,
        ← ContMDiffRiemannianMetric.inner_riemannianBundle]
      exact orthonormal_iff_ite.mp b.orthonormal i j
  have hvolb : |riemannianVolumeForm o x b.toBasis| = 1 := by
    rw [b.coe_toBasis]
    exact abs_riemannianVolumeForm_apply_orthonormal o x b
  rw [ContinuousAlternatingMap.apply_eq_det_mul (mpullback I' I f φ x) b.toBasis v,
    ContinuousAlternatingMap.apply_eq_det_mul (riemannianVolumeForm o x) b.toBasis v,
    abs_mul, abs_mul, hvolb, mul_one]
  exact mul_le_of_le_one_right (abs_nonneg _) hφb

/-- **Pointwise calibration inequality** on positively oriented tangent bases: in every degree
`k : ℕ`, if `φ` has pointwise comass at most `1` for `g`, then `|f^* φ(c)| ≤ dvol_{f^* g}(c)` on
every positively oriented tangent basis `c` of `T_x N`. -/
theorem abs_mpullback_apply_le_riemannianVolumeForm {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I' x)) (hc : c.orientation = o.orientationAt x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    |mpullback I' I f φ x c| ≤ riemannianVolumeForm o x c := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  have hpos : 0 < riemannianVolumeForm o x c := by
    rw [riemannianVolumeForm_apply]
    exact _root_.Orientation.volumeForm_apply_pos_iff.2 hc
  exact (abs_mpullback_apply_le_abs_riemannianVolumeForm g hcomass f hf hinj o x c).trans_eq
    (abs_of_pos hpos)

/-- Signed pointwise calibration inequality in every degree `k : ℕ`: `f^* φ(c) ≤ dvol_{f^* g}(c)`
on every positively oriented tangent basis `c` of `T_x N`. -/
theorem mpullback_apply_le_riemannianVolumeForm {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I' x)) (hc : c.orientation = o.orientationAt x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    mpullback I' I f φ x c ≤ riemannianVolumeForm o x c :=
  (le_abs_self _).trans
    (abs_mpullback_apply_le_riemannianVolumeForm g hcomass f hf hinj o x c hc)

private theorem zeroDim_summand_le
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ 0}
    (hcomass : ∀ y (v : Fin 0 → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin 0)) (b : Module.Basis (Fin 0) ℝ E') (x : N) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    (Orientation.signBasis (o.orientationAt x) b : ℝ) * mpullback I' I f φ x ![] ≤
      (Orientation.signBasis (o.orientationAt x) b : ℝ) * riemannianVolumeForm o x ![] := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  -- `TangentSpace I' x` is definitionally `E'`, so `b` is also a tangent basis at `x`.
  let bT : Module.Basis (Fin 0) ℝ (TangentSpace I' x) := b
  rw [riemannianVolumeForm_zeroDim_apply_eq_signBasis o b x ![]]
  change (Orientation.signBasis (o.orientationAt x) bT : ℝ) * mpullback I' I f φ x ![] ≤
    (Orientation.signBasis (o.orientationAt x) bT : ℝ) *
      (Orientation.signBasis (o.orientationAt x) bT : ℝ)
  rw [_root_.Orientation.signBasis_cast_mul_self, mpullback_apply,
    Subsingleton.elim (fun j : Fin 0 ↦ mfderiv I' I f x (![] j)) ![]]
  have hbdd : |φ (f x) ![]| ≤ 1 := by
    simpa [Subsingleton.elim (fun j : Fin 0 ↦ j.elim0) ![]] using
      hcomass (f x) (fun j ↦ j.elim0) fun j ↦ j.elim0
  rcases Int.units_eq_one_or (Orientation.signBasis (o.orientationAt x) bT) with hs | hs
  · rw [hs, Units.val_one, Int.cast_one, one_mul]
    exact (le_abs_self _).trans hbdd
  · rw [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact (neg_le_abs _).trans hbdd

/-- **Integrated calibration inequality** on a compact source: if `φ` has pointwise comass at most
`1` for `g`, then `∫_N f^* φ ≤ Vol(f)`. When `f^* φ` is not integrable, the left-hand side
evaluates to `0` and the inequality holds by nonnegativity of `immersionVolume`. -/
theorem integralTopForm_mpullback_le_immersionVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    integralTopForm o (mpullback I' I f φ) ≤ immersionVolume g f hf hinj o := by
  by_cases hφi : IntegrableTopForm (mpullback I' I f φ)
  · let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    have : IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace I' y) :=
      IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
    rw [immersionVolume_def]
    rcases k with - | k
    · have hcard : Module.finrank ℝ E' = 0 := by simpa using o.card_eq.symm
      have : Subsingleton E' := Module.finrank_zero_iff.mp hcard
      have : DiscreteTopology N := discreteTopology_of_zeroDim I'
      have : Finite N := finite_of_compact_of_discrete
      let : Fintype N := Fintype.ofFinite N
      let b := Module.finBasisOfFinrankEq ℝ E' hcard
      rw [integralTopForm_finite_zeroDim o b, integralTopForm_finite_zeroDim o b]
      exact Finset.sum_le_sum fun x _ ↦ zeroDim_summand_le g hcomass f hf hinj o b x
    · have hvi : IntegrableTopForm (riemannianVolumeForm o) :=
        (integrableTopForm_riemannianVolumeForm_iff_compactSpace o).2 inferInstance
      have hnonneg : 0 ≤ integralTopForm o (riemannianVolumeForm o - mpullback I' I f φ) :=
        integralTopForm_nonneg o fun x c hc ↦ by
          rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_nonneg]
          exact mpullback_apply_le_riemannianVolumeForm g hcomass f hf hinj o x c hc
      rw [sub_eq_add_neg, integralTopForm_add_of_integrable o hvi hφi.neg,
        ← neg_one_smul ℝ (mpullback I' I f φ), integralTopForm_smul, neg_one_mul,
        ← sub_eq_add_neg, sub_nonneg] at hnonneg
      exact hnonneg
  · rw [integralTopForm_eq_zero_of_not_integrable o _ hφi]
    exact immersionVolume_nonneg g f hf hinj o

/-- Absolute integrated calibration inequality on a compact source: if `φ` has pointwise comass at
most `1` for `g`, then `|∫_N f^* φ| ≤ Vol(f)`. When `f^* φ` is not integrable, the left-hand side
evaluates to `0` and the inequality holds by nonnegativity of `immersionVolume`. -/
theorem abs_integralTopForm_mpullback_le_immersionVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    |integralTopForm o (mpullback I' I f φ)| ≤ immersionVolume g f hf hinj o := by
  refine abs_le.2 ⟨?_, integralTopForm_mpullback_le_immersionVolume g hcomass f hf hinj o⟩
  have hneg := integralTopForm_mpullback_le_immersionVolume g
    (φ := -φ) (fun y v hv ↦ by simpa [abs_neg] using hcomass y v hv) f hf hinj o
  rw [← neg_one_smul ℝ φ, mpullback_smul, integralTopForm_smul, neg_one_mul] at hneg
  linarith

/-- **Equality case of the integrated calibration inequality** on a compact source: for a continuous
`k`-form `φ` of pointwise comass at most `1` for `g`, `∫_N f^* φ = Vol(f)` holds if and only if the
immersion `f` is calibrated by `φ` with its orientation `o`. -/
theorem integralTopForm_mpullback_eq_immersionVolume_iff_isCalibratedImmersion [CompactSpace N]
    {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o ↔
      IsCalibratedImmersion g φ f hf hinj o := by
  refine ⟨fun hint ↦ ?_, fun hcal ↦ hcal.integralTopForm_mpullback_eq_immersionVolume⟩
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rcases k with - | k
  · have hcard : Module.finrank ℝ E' = 0 := by simpa using o.card_eq.symm
    have : Subsingleton E' := Module.finrank_zero_iff.mp hcard
    have : DiscreteTopology N := discreteTopology_of_zeroDim I'
    have : Finite N := finite_of_compact_of_discrete
    let : Fintype N := Fintype.ofFinite N
    let b := Module.finBasisOfFinrankEq ℝ E' hcard
    rw [immersionVolume_def, integralTopForm_finite_zeroDim o b,
      integralTopForm_finite_zeroDim o b] at hint
    rw [isCalibratedImmersion_iff]
    ext x v
    have hterm := (Finset.sum_eq_sum_iff_of_le fun y _ ↦
      zeroDim_summand_le g hcomass f hf hinj o b y).1 hint x (Finset.mem_univ x)
    have hsign_ne : ((Orientation.signBasis (o.orientationAt x) b : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast (Orientation.signBasis (o.orientationAt x) b).ne_zero
    rw [Subsingleton.elim v ![]]
    exact mul_left_cancel₀ hsign_ne hterm
  · have : IsContMDiffRiemannianBundle I' 0 E' (fun y : N ↦ TangentSpace I' y) :=
      (IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
        (F := E') (V := fun y : N ↦ TangentSpace I' y)).toIsContMDiffZero
    have : IsManifold I' (0 + 1) N := by simpa using ‹IsManifold I' 1 N›
    rw [immersionVolume_def] at hint
    have hsm1 : IsSmoothForm I' 0 (riemannianVolumeForm o) :=
      isSmoothForm_riemannianVolumeForm (n := 0) o
    have hsm2 : IsSmoothForm I' 0 (mpullback I' I f φ) :=
      hφ.mpullback (by simpa using hf.of_le (by simp))
    have hdiff_zero :
        integralTopForm o (riemannianVolumeForm o - mpullback I' I f φ) = 0 := by
      rw [sub_eq_add_neg, integralTopForm_add_of_compactSpace o hsm1 hsm2.neg,
        ← neg_one_smul ℝ (mpullback I' I f φ), integralTopForm_smul, neg_one_mul,
        ← sub_eq_add_neg, hint, sub_self]
    rw [isCalibratedImmersion_iff_forall_orthonormal_basis]
    intro x b hb horth
    by_contra hne
    have hle : φ (f x) (mfderiv I' I f x ∘ b) ≤ 1 :=
      (le_abs_self _).trans (hcomass (f x) (mfderiv I' I f x ∘ b) horth)
    have hlt : φ (f x) (mfderiv I' I f x ∘ b) < 1 := lt_of_le_of_ne hle hne
    have hb_orth : Orthonormal ℝ b := orthonormal_iff_ite.2 fun i j ↦ by
      rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
        ContMDiffRiemannianMetric.pullback_inner]
      exact horth i j
    let b' := b.toOrthonormalBasis hb_orth
    have hb' : b'.toBasis.orientation = o.orientationAt x := by
      rwa [b.toBasis_toOrthonormalBasis]
    have hvol_b : riemannianVolumeForm o x b = 1 := by
      rw [← b.coe_toOrthonormalBasis]
      exact riemannianVolumeForm_apply_orthonormal o x b' hb'
    have hpos_val : 0 < (riemannianVolumeForm o - mpullback I' I f φ) x b := by
      rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hvol_b, mpullback_apply]
      exact sub_pos.2 hlt
    have hsm : IsSmoothForm I' 0 (riemannianVolumeForm o - mpullback I' I f φ) := by
      rw [sub_eq_add_neg]
      exact hsm1.add hsm2.neg
    have hpos_int : 0 < integralTopForm o (riemannianVolumeForm o - mpullback I' I f φ) :=
      integralTopForm_pos o hsm (isClosed_tsupport _).isCompact
        (fun y c hc ↦ by
          rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_nonneg]
          exact mpullback_apply_le_riemannianVolumeForm g hcomass f hf hinj o y c hc)
        ⟨x, b, hb, hpos_val⟩
    linarith

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
on every smooth closed `k`-form `η` (Harvey–Lawson 1982, Theorem II.4.2; McLean 1998, Section 2).
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
        integralTopForm_mpullback_le_immersionVolume g hφ.abs_apply_le_one f' hf' hinj' o'

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
      (hφ.isSmoothForm.of_le (by simp)) hφ.abs_apply_le_one f' hf' hinj' o']

end FundamentalTheorem

end TauCeti
