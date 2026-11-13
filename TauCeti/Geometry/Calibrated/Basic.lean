/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Smooth calibrations on Riemannian manifolds

A **calibration** on a Riemannian manifold `(M, g)` is a smooth closed real `k`-form `φ` whose
pointwise comass is at most `1`, meaning `|φ_x(v)| ≤ 1` for every `g_x`-orthonormal `k`-frame `v`
of `T_x M`. In positive degree this is equivalent to the one-sided bound `φ_x(v) ≤ 1` on
orthonormal frames; in degree zero a calibration is a locally constant function taking values in
`[-1, 1]`. Calibrations are preserved under pullback along smooth immersions (for the pulled-back
metric), restriction to open submanifolds, and Riemannian isometries.

## Main definitions

* `TauCeti.IsCalibration`: a smooth closed real `k`-form of pointwise comass at most `1`.

## Main results

* `TauCeti.isCalibration_iff_opNorm_le_one`: equivalence with the operator-norm comass bound
  `‖φ x‖ ≤ 1` in the metric inner product.
* `TauCeti.isCalibration_iff_apply_le_one`: in positive degree, the one-sided bound `φ_x(v) ≤ 1`
  on orthonormal frames suffices.
* `TauCeti.isCalibration_zero_iff`: degree-zero calibrations are locally constant functions into
  `[-1, 1]`.
* `TauCeti.IsCalibration.pullback`, `TauCeti.IsCalibration.restrictOpenTangentSpace`,
  `TauCeti.IsCalibration.of_riemannianIsometry`: functoriality under immersions, open restriction,
  and Riemannian isometries.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Definition 2.1.
-/

public section

noncomputable section

open Bundle Manifold TopologicalSpace
open scoped Bundle ContDiff Manifold RealInnerProductSpace

namespace TauCeti

/-! ### Smooth calibrations -/

section Calibrations

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- A smooth calibration for the smooth Riemannian metric `g` on `M`: a smooth closed real
`k`-form `φ` of comass at most one at every point, that is `|φ_x(v)| ≤ 1` for every
`g_x`-orthonormal frame `v` of `T_x M`. In degree zero this is a locally constant function with
values in `[-1, 1]`. -/
def IsCalibration (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {k : ℕ}
    (φ : RoughForm I M ℝ k) : Prop :=
  IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
    ∀ x (v : Fin k → TangentSpace I x),
      (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → |φ x v| ≤ 1

/-- Unfolding characterization of `IsCalibration`. -/
theorem isCalibration_iff (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {k : ℕ} (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔ IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
      ∀ x (v : Fin k → TangentSpace I x),
        (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → |φ x v| ≤ 1 :=
  Iff.rfl

namespace IsCalibration

variable {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {k : ℕ} {φ : RoughForm I M ℝ k}

/-- A calibration is a smooth differential form. -/
theorem isSmoothForm (hφ : IsCalibration g φ) : IsSmoothForm I ∞ φ := hφ.1

/-- A calibration is closed. -/
theorem mextDeriv_eq_zero (hφ : IsCalibration g φ) : mextDeriv φ = 0 := hφ.2.1

/-- At every point, a calibration evaluates to at most `1` in absolute value on every
`g`-orthonormal frame. -/
theorem abs_apply_le_one (hφ : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) : |φ x v| ≤ 1 :=
  hφ.2.2 x v hv

/-- At every point, a calibration evaluates to at most `1` on every `g`-orthonormal frame. -/
theorem apply_le_one (hφ : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) : φ x v ≤ 1 :=
  (le_abs_self _).trans (hφ.abs_apply_le_one x v hv)

/-- At every point, a calibration evaluates to at least `-1` on every `g`-orthonormal frame. -/
theorem neg_one_le_apply (hφ : IsCalibration g φ) (x : M) (v : Fin k → TangentSpace I x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) : -1 ≤ φ x v :=
  neg_le_of_abs_le (hφ.abs_apply_le_one x v hv)

/-- With `g` installed as the Riemannian bundle metric, a calibration has operator norm at most
`1` at every point. -/
theorem opNorm_le_one (hφ : IsCalibration g φ) (x : M) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    ‖φ x‖ ≤ 1 := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  refine (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).2 fun v hv ↦ ?_
  rw [Real.norm_eq_abs]
  exact hφ.abs_apply_le_one x v fun i j ↦ (orthonormal_iff_ite.mp hv i j)

/-- The zero form is a calibration for every smooth Riemannian metric. -/
@[simp]
protected theorem zero (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {k : ℕ} :
    IsCalibration g (0 : RoughForm I M ℝ k) :=
  ⟨IsSmoothForm.zero ∞, mextDeriv_zero, fun _ _ _ ↦ by simp⟩

/-- The negative of a calibration is a calibration. -/
protected theorem neg (hφ : IsCalibration g φ) : IsCalibration g (-φ) :=
  ⟨hφ.isSmoothForm.neg, by simp [hφ.mextDeriv_eq_zero], fun x v hv ↦ by
    simpa [abs_neg] using hφ.abs_apply_le_one x v hv⟩

end IsCalibration

/-- A smooth closed form is a calibration exactly when its pointwise operator norm (comass) in
the Riemannian metric `g` is at most `1` everywhere. -/
theorem isCalibration_iff_opNorm_le_one
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {k : ℕ} (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔ IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
      ∀ x, (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖φ x‖ ≤ 1) := by
  refine ⟨fun h ↦ ⟨h.isSmoothForm, h.mextDeriv_eq_zero, h.opNorm_le_one⟩, ?_⟩
  rintro ⟨hs, hd, hn⟩
  refine ⟨hs, hd, fun x v hv ↦ ?_⟩
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hvo : Orthonormal ℝ v := orthonormal_iff_ite.2 hv
  simpa [Real.norm_eq_abs] using (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal
    zero_le_one).1 (hn x) v hvo

/-- Negating a form preserves the calibration property. -/
@[simp]
theorem isCalibration_neg_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {k : ℕ} (φ : RoughForm I M ℝ k) :
    IsCalibration g (-φ) ↔ IsCalibration g φ :=
  ⟨fun h ↦ by simpa using h.neg, IsCalibration.neg⟩

/-- In positive degree, the absolute comass bound `|φ_x(v)| ≤ 1` in `IsCalibration` is
equivalent to the one-sided bound `φ_x(v) ≤ 1` on orthonormal frames. -/
theorem isCalibration_iff_apply_le_one [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔ IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
      ∀ x (v : Fin k → TangentSpace I x),
        (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → φ x v ≤ 1 := by
  refine ⟨fun h ↦ ⟨h.isSmoothForm, h.mextDeriv_eq_zero, fun x v hv ↦ h.apply_le_one x v hv⟩,
    fun ⟨hs, hd, hle⟩ ↦ ⟨hs, hd, fun x v hv ↦ abs_le.2 ⟨?_, hle x v hv⟩⟩⟩
  -- Negating the first vector reverses the sign of `φ x` while preserving orthonormality.
  let v' : Fin k → TangentSpace I x := Function.update v 0 (-v 0)
  have hv' : ∀ i j, g.inner x (v' i) (v' j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · simpa [v', hi, hj] using hv 0 0
    · simp [v', hi, hj, hv 0 j, Ne.symm hj]
    · simp [v', hi, hj, hv i 0]
    · simpa [v', hi, hj] using hv i j
  have hval : φ x v' = -φ x v := by
    have hsmul := (φ x).map_update_smul v 0 (-1 : ℝ) (v 0)
    simpa [v', Function.update_eq_self] using hsmul
  have hbound := hle x v' hv'
  linarith

/-- In degree zero, a calibration is a locally constant function with values in `[-1, 1]`. -/
theorem isCalibration_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ 0) :
    IsCalibration g φ ↔ IsLocallyConstant (fun x ↦ φ x ![]) ∧ ∀ x, |φ x ![]| ≤ 1 := by
  rw [isCalibration_iff]
  have hfn : φ = RoughForm.ofFunction I (fun x ↦ φ x ![]) := by
    refine (RoughForm.eq_ofFunction φ).trans ?_
    congr 1
    ext x
    congr 1
    exact Subsingleton.elim _ _
  constructor
  · rintro ⟨hsm, hd, hbd⟩
    rw [hfn, isSmoothForm_ofFunction_iff] at hsm
    rw [hfn] at hd
    refine ⟨(mextDeriv_ofFunction_eq_zero_iff (hsm.mdifferentiable (by simp))).1 hd, fun x ↦ ?_⟩
    exact hbd x ![] fun i ↦ i.elim0
  · rintro ⟨hlc, hbd⟩
    have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ φ x ![]) := hlc.contMDiff
    refine ⟨?_, ?_, fun x v _ ↦ ?_⟩
    · rw [hfn, isSmoothForm_ofFunction_iff]
      exact hsm
    · rw [hfn]
      exact (mextDeriv_ofFunction_eq_zero_iff (hsm.mdifferentiable (by simp))).2 hlc
    · have hv : v = ![] := Subsingleton.elim v ![]
      simpa [hv] using hbd x

section Functoriality

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Pulling back a calibration along a smooth immersion yields a calibration for the pulled-back
metric. -/
theorem IsCalibration.pullback [FiniteDimensional ℝ E'] [IsManifold I 2 M] [IsManifold I' 2 N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ)
    {f : N → M} (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) :
    IsCalibration (g.pullback f (by simpa using hf) hinj) (mpullback I' I f φ) := by
  refine ⟨hφ.isSmoothForm.mpullback (by simpa using hf), ?_, fun x v hv ↦ ?_⟩
  · have hφ1 : IsSmoothBundleForm I ℝ (Trivial M ℝ) 1 φ :=
      (isSmoothBundleForm_def 1 φ).mpr (hφ.isSmoothForm.contMDiff.of_le (by simp))
    rw [← mpullback_mextDeriv (hf.of_le (by simp)) hφ1, hφ.mextDeriv_eq_zero, mpullback_zero]
  · rw [mpullback_apply]
    exact hφ.abs_apply_le_one (f x) (mfderiv I' I f x ∘ v) fun i j ↦ by
      simpa [ContMDiffRiemannianMetric.pullback_inner] using hv i j

/-- Restricting a calibration to an open submanifold yields a calibration for the restricted
metric. -/
theorem IsCalibration.restrictOpenTangentSpace [FiniteDimensional ℝ E] [IsManifold I 2 M]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ) (U : Opens M) :
    IsCalibration (g.restrictOpenTangentSpace U) (mpullback I I (Subtype.val : U → M) φ) := by
  rw [ContMDiffRiemannianMetric.restrictOpenTangentSpace_eq_pullback]
  exact hφ.pullback contMDiff_subtype_val (Manifold.mfderiv_subtype_val_injective (I := I))

/-- Pulling back a calibration along a smooth Riemannian isometry yields a calibration on the
source manifold. -/
theorem IsCalibration.of_riemannianIsometry [FiniteDimensional ℝ E'] [IsManifold I 2 M]
    [IsManifold I' 2 N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (fun x : N ↦ TangentSpace I' x))
    (Φ : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
      RiemannianIsometry I' I N M)
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ) :
    IsCalibration g' (mpullback I' I Φ φ) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
  have hpull := hφ.pullback Φ.toDiffeomorph.contMDiff
    fun x ↦ (Φ.toDiffeomorph.isInvertible_mfderiv (x := x) (by simp)).injective
  refine ⟨hpull.isSmoothForm, hpull.mextDeriv_eq_zero, fun x v hv ↦ ?_⟩
  refine hpull.abs_apply_le_one x v fun i j ↦ ?_
  rw [ContMDiffRiemannianMetric.pullback_inner]
  change inner ℝ (mfderiv I' I Φ x (v i)) (mfderiv I' I Φ x (v j)) = if i = j then 1 else 0
  rw [Φ.inner_mfderiv]
  exact hv i j

end Functoriality

end Calibrations

end TauCeti
