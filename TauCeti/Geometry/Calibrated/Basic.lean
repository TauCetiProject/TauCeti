/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Smooth calibrations on Riemannian manifolds

A **calibration** on a Riemannian manifold `(M, g)` is a smooth closed real `k`-form `φ` whose
pointwise comass is at most `1`, meaning `|φ_x(v)| ≤ 1` for every `g_x`-orthonormal `k`-frame `v`
of `T_x M`. In positive degree this is equivalent to the one-sided bound `φ_x(v) ≤ 1` on
orthonormal frames; in degree zero a calibration is a locally constant function taking values in
`[-1, 1]`. Calibrations form a balanced convex set, satisfy the pointwise linear calibration
inequality `|φ_x(v)| ≤ ‖v₁ ∧ ⋯ ∧ vₖ‖`, include the Riemannian volume form in top degree and
constant forms of comass at most `1` on flat inner product spaces, and are preserved under pullback
along smooth immersions (for the pulled-back metric), restriction to open submanifolds, and
Riemannian isometries.

## Main definitions

* `TauCeti.IsCalibration`: a smooth closed real `k`-form of pointwise comass at most `1`.
* `TauCeti.IsCalibration.toSmoothForm`: a calibration bundled as a `SmoothForm`.

## Main results

* `TauCeti.isCalibration_iff_opNorm_le_one` and `TauCeti.IsCalibration.abs_apply_le_norm_ιMulti`:
  equivalence with the operator-norm comass bound `‖φ x‖ ≤ 1` and the resulting pointwise linear
  calibration inequality `|φ x v| ≤ ‖v₁ ∧ ⋯ ∧ vₖ‖`.
* `TauCeti.isCalibration_iff_apply_le_one`: in positive degree, the one-sided bound `φ_x(v) ≤ 1`
  on orthonormal frames suffices.
* `TauCeti.IsCalibration.smul_of_abs_le_one` and `TauCeti.IsCalibration.convex_combo`: closure of
  calibrations under contractions `|c| ≤ 1` and subconvex combinations.
* `TauCeti.isCalibration_ofFunction_iff` and
  `TauCeti.isCalibration_iff_isLocallyConstant_and_abs_apply_le_one`: degree-zero calibrations are
  locally constant functions into `[-1, 1]`.
* `TauCeti.isCalibration_riemannianVolumeForm`, `TauCeti.isCalibration_const_iff`, and
  `Orthonormal.isCalibration_const_alternatingFormEquiv_ιMulti`: the Riemannian volume form and
  constant forms of comass at most `1` (in particular simple constant calibrations) are
  calibrations.
* `TauCeti.IsCalibration.mpullback_of_inner_eq`, `TauCeti.IsCalibration.pullback`,
  `TauCeti.IsCalibration.restrictOpenTangentSpace`,
  `TauCeti.IsCalibration.mpullback_riemannianIsometry`, and
  `TauCeti.isCalibration_mpullback_riemannianIsometry_iff`: functoriality under metric-preserving
  smooth maps, immersions, open restriction, and Riemannian isometries.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Definition 2.1.
-/

public section

noncomputable section

open Bundle Manifold TopologicalSpace exteriorPower
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
  {k : ℕ} {φ ψ : RoughForm I M ℝ k}

/-- A calibration is a smooth differential form. -/
theorem isSmoothForm (hφ : IsCalibration g φ) : IsSmoothForm I ∞ φ := hφ.1

/-- A calibration is closed. -/
theorem mextDeriv_eq_zero (hφ : IsCalibration g φ) : mextDeriv φ = 0 := hφ.2.1

/-- Bundle a calibration as a `SmoothForm`. -/
def toSmoothForm (hφ : IsCalibration g φ) : SmoothForm I M ℝ k :=
  ⟨φ, hφ.isSmoothForm.mem_smoothBundleForms⟩

/-- Coercing `hφ.toSmoothForm` back to a rough form recovers `φ`. -/
@[simp]
theorem coe_toSmoothForm (hφ : IsCalibration g φ) :
    (hφ.toSmoothForm : RoughForm I M ℝ k) = φ := (rfl)

/-- Bundled as a `SmoothForm`, a calibration is closed. -/
theorem isClosed_toSmoothForm (hφ : IsCalibration g φ) : hφ.toSmoothForm.IsClosed :=
  (SmoothForm.isClosed_def hφ.toSmoothForm).2 hφ.mextDeriv_eq_zero

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
  exact hφ.abs_apply_le_one x v fun i j ↦
    (g.inner_riemannianBundle x (v i) (v j)).symm.trans (orthonormal_iff_ite.mp hv i j)

/-- **Pointwise linear calibration inequality**: for a calibration `φ` on `(M, g)` and any `k`-tuple
`v` of tangent vectors at `x`, `|φ x v| ≤ ‖v₁ ∧ ⋯ ∧ vₖ‖` in the metric induced by `g_x` on the
exterior power `⋀[ℝ]^k (T_x M)`. -/
theorem abs_apply_le_norm_ιMulti [FiniteDimensional ℝ E] (hφ : IsCalibration g φ) (x : M)
    (v : Fin k → TangentSpace I x) :
    |φ x v| ≤
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖ιMulti ℝ k v‖) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  refine (Real.norm_eq_abs _).symm.trans_le (((φ x).le_opNorm_mul_norm_ιMulti v).trans ?_)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hφ.opNorm_le_one x) (norm_nonneg _)

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

/-- Scaling a calibration by a real constant `c` with `|c| ≤ 1` yields a calibration. -/
theorem smul_of_abs_le_one (hφ : IsCalibration g φ) {c : ℝ} (hc : |c| ≤ 1) :
    IsCalibration g (c • φ) := by
  refine ⟨hφ.isSmoothForm.smul c, by rw [mextDeriv_smul, hφ.mextDeriv_eq_zero, smul_zero],
    fun x v hv ↦ ?_⟩
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hφ.abs_apply_le_one x v hv) (abs_nonneg c)).trans
    (by rwa [mul_one])

/-- **Convexity of calibrations**: if `0 ≤ a`, `0 ≤ b`, and `a + b ≤ 1` (in particular for convex
combinations `a + b = 1`), then `a • φ + b • ψ` is a calibration whenever `φ` and `ψ` are. -/
theorem convex_combo (hφ : IsCalibration g φ) (hψ : IsCalibration g ψ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) : IsCalibration g (a • φ + b • ψ) := by
  refine ⟨(hφ.isSmoothForm.smul a).add (hψ.isSmoothForm.smul b),
    (SmoothForm.isClosed_def (a • hφ.toSmoothForm + b • hψ.toSmoothForm)).1
      ((hφ.isClosed_toSmoothForm.smul a).add (hψ.isClosed_toSmoothForm.smul b)),
    fun x v hv ↦ ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  linarith [mul_le_mul_of_nonneg_left (hφ.abs_apply_le_one x v hv) ha,
    mul_le_mul_of_nonneg_left (hψ.abs_apply_le_one x v hv) hb]

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
  have hvo : Orthonormal ℝ v := orthonormal_iff_ite.2 fun i j ↦
    (g.inner_riemannianBundle x (v i) (v j)).trans (hv i j)
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
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let v' : Fin k → TangentSpace I x := Function.update v 0 (-v 0)
  have hvo : Orthonormal ℝ v := orthonormal_iff_ite.2 fun i j ↦
    (g.inner_riemannianBundle x (v i) (v j)).trans (hv i j)
  have hv' : ∀ i j, g.inner x (v' i) (v' j) = if i = j then 1 else 0 := by
    have hvo' : Orthonormal ℝ v' :=
      hvo.orthonormal_of_forall_eq_or_eq_neg fun i ↦ by
        rcases eq_or_ne i 0 with rfl | hi
        · exact Or.inr (Function.update_self 0 (-v 0) v)
        · exact Or.inl (Function.update_of_ne hi (-v 0) v)
    intro i j
    exact (g.inner_riemannianBundle x (v' i) (v' j)).symm.trans (orthonormal_iff_ite.1 hvo' i j)
  have hval : φ x v' = -φ x v := by
    have hsmul := (φ x).map_update_smul v 0 (-1 : ℝ) (v 0)
    simpa [v', Function.update_eq_self] using hsmul
  have hbound := hle x v' hv'
  linarith

/-- **Degree-zero calibrations from functions**: `RoughForm.ofFunction I f` is a calibration on
`(M, g)` if and only if `f` is locally constant and takes values in `[-1, 1]`. -/
theorem isCalibration_ofFunction_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (f : M → ℝ) :
    IsCalibration g (RoughForm.ofFunction I f) ↔ IsLocallyConstant f ∧ ∀ x, |f x| ≤ 1 := by
  rw [isCalibration_iff]
  refine ⟨fun ⟨hsm, hd, hbd⟩ ↦ ?_, fun ⟨hlc, hbd⟩ ↦ ?_⟩
  · have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := isSmoothForm_ofFunction_iff.1 hsm
    refine ⟨(mextDeriv_ofFunction_eq_zero_iff (hf.mdifferentiable (by simp))).1 hd, fun x ↦ ?_⟩
    simpa only [RoughForm.ofFunction_apply] using hbd x ![] fun i ↦ i.elim0
  · have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hlc.contMDiff
    exact ⟨isSmoothForm_ofFunction_iff.2 hf,
      (mextDeriv_ofFunction_eq_zero_iff (hf.mdifferentiable (by simp))).2 hlc,
      fun x _ _ ↦ by simpa only [RoughForm.ofFunction_apply] using hbd x⟩

/-- In degree zero, a calibration is a locally constant function with values in `[-1, 1]`. -/
theorem isCalibration_iff_isLocallyConstant_and_abs_apply_le_one
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ 0) :
    IsCalibration g φ ↔ IsLocallyConstant (fun x ↦ φ x ![]) ∧ ∀ x, |φ x ![]| ≤ 1 := by
  have hfn : φ = RoughForm.ofFunction I (fun x ↦ φ x ![]) := by
    simpa only [Subsingleton.elim (0 : Fin 0 → _) ![]] using RoughForm.eq_ofFunction φ
  conv_lhs => rw [hfn]
  exact isCalibration_ofFunction_iff g (fun x ↦ φ x ![])

section TopDegree

/-- **The Riemannian volume form is a calibration** in every dimension `m`, including `m = 0` and on
manifolds with boundary or corners. -/
theorem isCalibration_riemannianVolumeForm [FiniteDimensional ℝ E] [IsManifold I ∞ M] {m : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibration g (riemannianVolumeForm o) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  refine (isCalibration_iff_opNorm_le_one g (riemannianVolumeForm o)).2
    ⟨isSmoothForm_riemannianVolumeForm o,
      mextDeriv_eq_zero_of_finrank_le (by simpa using o.card_eq.ge) _, fun x ↦ ?_⟩
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def, (o.orientationAt x).norm_volumeFormL]

end TopDegree

section Functoriality

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Pulling back a calibration along a smooth map whose differential preserves the Riemannian inner
products yields a calibration on the source manifold, without assuming finite-dimensionality. -/
theorem IsCalibration.mpullback_of_inner_eq [IsManifold I 2 M] [IsManifold I' 2 N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g' : ContMDiffRiemannianMetric I' ∞ E' (fun x : N ↦ TangentSpace I' x)}
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ)
    {f : N → M} (hf : ContMDiff I' I ∞ f)
    (hinner : ∀ x (v w : TangentSpace I' x),
      g.inner (f x) (mfderiv I' I f x v) (mfderiv I' I f x w) = g'.inner x v w) :
    IsCalibration g' (mpullback I' I f φ) := by
  have : IsManifold I' 1 N := IsManifold.of_le (n := 2) (by norm_num)
  refine ⟨hφ.isSmoothForm.mpullback hf,
    (hφ.isSmoothForm.of_le (by simp)).mextDeriv_mpullback_eq_zero hφ.mextDeriv_eq_zero
      (hf.of_le (by simp)),
    fun x v hv ↦ ?_⟩
  rw [mpullback_apply]
  exact hφ.abs_apply_le_one (f x) (mfderiv I' I f x ∘ v) fun i j ↦ by
    rw [Function.comp_apply, Function.comp_apply, hinner, hv i j]

/-- Pulling back a calibration along a smooth immersion yields a calibration for the pulled-back
metric. -/
theorem IsCalibration.pullback [FiniteDimensional ℝ E'] [IsManifold I 2 M] [IsManifold I' 2 N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ)
    {f : N → M} (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) :
    IsCalibration (g.pullback f hf hinj) (mpullback I' I f φ) :=
  hφ.mpullback_of_inner_eq hf fun x v w ↦
    (ContMDiffRiemannianMetric.pullback_inner g f hf hinj x v w).symm

/-- Restricting a calibration to an open submanifold yields a calibration for the restricted
metric. -/
theorem IsCalibration.restrictOpenTangentSpace [IsManifold I 2 M]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ) (U : Opens M) :
    IsCalibration (g.restrictOpenTangentSpace U) (mpullback I I (Subtype.val : U → M) φ) :=
  hφ.mpullback_of_inner_eq contMDiff_subtypeVal fun x v w ↦ by
    rw [ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
      TauCeti.Manifold.mfderiv_subtype_val]
    rfl

/-- Pulling back a calibration along a smooth Riemannian isometry yields a calibration on the
source manifold. -/
theorem IsCalibration.mpullback_riemannianIsometry [IsManifold I 2 M] [IsManifold I' 2 N]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (g' : ContMDiffRiemannianMetric I' ∞ E' (fun x : N ↦ TangentSpace I' x))
    (Φ : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
      RiemannianIsometry I' I N M)
    {k : ℕ} {φ : RoughForm I M ℝ k} (hφ : IsCalibration g φ) :
    IsCalibration g' (mpullback I' I Φ φ) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
  refine hφ.mpullback_of_inner_eq (by simpa only [RiemannianIsometry.coe_toDiffeomorph] using
    Φ.toDiffeomorph.contMDiff) fun x v w ↦ ?_
  rw [← ContMDiffRiemannianMetric.inner_riemannianBundle g,
    ← ContMDiffRiemannianMetric.inner_riemannianBundle g']
  exact Φ.inner_mfderiv x v w

/-- Pulling back along a smooth Riemannian isometry preserves the calibration property in both
directions. -/
@[simp]
theorem isCalibration_mpullback_riemannianIsometry_iff [IsManifold I 2 M] [IsManifold I' 2 N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (fun x : N ↦ TangentSpace I' x))
    (Φ : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
      RiemannianIsometry I' I N M)
    {k : ℕ} (φ : RoughForm I M ℝ k) :
    IsCalibration g' (mpullback I' I Φ φ) ↔ IsCalibration g φ := by
  have : IsManifold I' 1 N := IsManifold.of_le (n := 2) (by norm_num)
  refine ⟨fun h ↦ ?_, fun h ↦ h.mpullback_riemannianIsometry g' Φ⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
  have hsymm := h.mpullback_riemannianIsometry g Φ.symm
  rwa [Φ.coe_symm, ← Φ.coe_toDiffeomorph, mpullback_symm_mpullback (by simp)] at hsymm

end Functoriality

section VectorSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}

/-- On a real inner product space `V` equipped with its standard flat metric
`(riemannianMetricVectorSpace V).ofLE le_top`, the constant smooth `k`-form `SmoothForm.const A` is
a calibration if and only if `A` has comass `‖A‖ ≤ 1`. -/
@[simp]
theorem isCalibration_const_iff (A : V [⋀^Fin k]→L[ℝ] ℝ) :
    IsCalibration ((riemannianMetricVectorSpace V).ofLE le_top) (SmoothForm.const A).val ↔
      ‖A‖ ≤ 1 := by
  rw [isCalibration_iff, and_iff_right (SmoothForm.const A).isSmoothForm,
    and_iff_right ((SmoothForm.isClosed_def (SmoothForm.const A)).1 (SmoothForm.isClosed_const A)),
    A.opNorm_le_iff_le_orthonormal zero_le_one]
  refine ⟨fun h u hu ↦ ?_, fun h x v hv ↦ ?_⟩
  · rw [Real.norm_eq_abs]
    have h0 := h 0 (fun i ↦ (NormedSpace.fromTangentSpace 0).symm (u i)) fun i j ↦ by
      rw [ContMDiffRiemannianMetric.ofLE_inner, riemannianMetricVectorSpace_inner,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
      exact orthonormal_iff_ite.1 hu i j
    rw [SmoothForm.const_apply] at h0
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h0
  · rw [SmoothForm.const_apply, ← Real.norm_eq_abs]
    refine h (fun i ↦ NormedSpace.fromTangentSpace x (v i)) (orthonormal_iff_ite.2 fun i j ↦ ?_)
    rw [← riemannianMetricVectorSpace_inner x (v i) (v j), ← hv i j,
      ContMDiffRiemannianMetric.ofLE_inner]

end VectorSpace

end Calibrations

end TauCeti

namespace Orthonormal

open scoped ContDiff

/-- For any orthonormal frame `u : Fin k → V` in a finite-dimensional real inner product space `V`,
the constant smooth `k`-form `SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k u))` is a
calibration on `(V, (riemannianMetricVectorSpace V).ofLE le_top)`. -/
theorem isCalibration_const_alternatingFormEquiv_ιMulti {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ} {u : Fin k → V}
    (hu : Orthonormal ℝ u) :
    TauCeti.IsCalibration ((riemannianMetricVectorSpace V).ofLE le_top)
      (TauCeti.SmoothForm.const
        (TauCeti.alternatingFormEquiv V k (exteriorPower.ιMulti ℝ k u))).val := by
  rw [TauCeti.isCalibration_const_iff, hu.norm_alternatingFormEquiv_ιMulti]

end Orthonormal
