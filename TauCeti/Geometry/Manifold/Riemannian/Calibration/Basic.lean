/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CalibratedFrame
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# Smooth calibrations on Riemannian manifolds

Let `(M, g)` be a smooth Riemannian manifold. A smooth real `k`-form `φ` on `M` is a *calibration*
for `g` (`TauCeti.IsCalibration`) when it is closed (`mextDeriv φ = 0`) and has pointwise comass
at most one, meaning `|φ x v| ≤ 1` for every `g_x`-orthonormal `k`-frame `v` in `T_x M`.

By the operator-norm characterization of comass on orthonormal frames
(`ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal`), this pointwise frame bound is equivalent
to `‖φ x‖ ≤ 1` for the inner-product-space operator norm induced by `g` on `T_x M`
(`TauCeti.isCalibration_iff_norm_le_one`), and in positive degree `1 ≤ k` to the one-sided bound
`φ x v ≤ 1` (`TauCeti.isCalibration_iff_apply_le_one`).

This file develops the foundational API for smooth calibrations:

* **Comass and linear calibration bounds**: `TauCeti.isCalibration_iff_norm_le_one`,
  `TauCeti.IsCalibration.norm_le_one`, `TauCeti.isCalibration_iff_apply_le_one`, and the pointwise
  calibration inequality `|φ x v| ≤ ‖v₁ ∧ ⋯ ∧ vₖ‖`
  (`TauCeti.IsCalibration.abs_apply_le_norm_ιMulti`).
* **Symmetry and convexity**: the calibrations of degree `k` on `(M, g)` contain `0`, are closed
  under negation and scalar multiplication by `c` with `|c| ≤ 1`, and are convex
  (`TauCeti.IsCalibration.convex_combo`).
* **Degree zero and top degree**: in degree `0`, calibrations are locally constant functions taking
  values in `[-1, 1]` (`TauCeti.isCalibration_ofFunction_iff`,
  `TauCeti.isCalibration_zero_degree_iff`); in top degree, the Riemannian volume form of any
  orientation is a calibration in every dimension, including `0` and on manifolds with boundary or
  corners (`TauCeti.isCalibration_riemannianVolumeForm`).
* **Functoriality and constant calibrations**: calibrations pull back along metric-preserving smooth
  maps (`TauCeti.IsCalibration.mpullback_of_inner_eq`), smooth immersions with the pullback metric
  (`TauCeti.IsCalibration.mpullback`), and open inclusions
  (`TauCeti.IsCalibration.restrictOpenTangentSpace`). On a flat real inner product space `V`, the
  constant form `SmoothForm.const A` is a calibration if and only if `‖A‖ ≤ 1`
  (`TauCeti.isCalibration_const_iff`); in particular, every orthonormal `k`-frame `u` induces a
  simple constant calibration `SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k u))`
  (`Orthonormal.isCalibration_const_alternatingFormEquiv_ιMulti`).

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1, p. 59.
* D. Joyce, *Lectures on Special Lagrangian Geometry*, arXiv:math/0111111 (2001), §2.1.
-/

public section

noncomputable section

open Bundle exteriorPower
open scoped Manifold ContDiff Topology

namespace TauCeti

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ}

/-- A smooth calibration for the smooth Riemannian metric `g` on `M`: a smooth closed real `k`-form
`φ` of comass at most one at every point, that is `|φ x v| ≤ 1` for every `g_x`-orthonormal frame
`v` of `T_x M` (Harvey–Lawson 1982, Definition II.4.1). In degree zero this is a locally constant
function with values in `[-1, 1]`. -/
def IsCalibration (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {k : ℕ}
    (φ : RoughForm I M ℝ k) : Prop :=
  IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
    ∀ x (v : Fin k → TangentSpace I x),
      (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → |φ x v| ≤ 1

/-- Unfolding `IsCalibration` into smoothness, closedness, and the orthonormal-frame bound. -/
theorem isCalibration_def (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) :
    IsCalibration g φ ↔
      IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
        ∀ x (v : Fin k → TangentSpace I x),
          (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → |φ x v| ≤ 1 :=
  Iff.rfl

section Projections

variable {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {φ ψ : RoughForm I M ℝ k}

/-- A calibration is a smooth differential form. -/
theorem IsCalibration.isSmoothForm (hφ : IsCalibration g φ) : IsSmoothForm I ∞ φ := hφ.1

/-- A calibration is closed (`mextDeriv φ = 0`). -/
theorem IsCalibration.mextDeriv_eq_zero (hφ : IsCalibration g φ) : mextDeriv φ = 0 := hφ.2.1

/-- Evaluating a calibration on any `g_x`-orthonormal frame gives a number of absolute value at
most `1`. -/
theorem IsCalibration.abs_apply_le_one (hφ : IsCalibration g φ) (x : M)
    {v : Fin k → TangentSpace I x}
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) : |φ x v| ≤ 1 :=
  hφ.2.2 x v hv

/-- Evaluating a calibration on any `g_x`-orthonormal frame gives at most `1`. -/
theorem IsCalibration.apply_le_one (hφ : IsCalibration g φ) (x : M)
    {v : Fin k → TangentSpace I x}
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) : φ x v ≤ 1 :=
  (le_abs_self _).trans (hφ.abs_apply_le_one x hv)

/-- Bundle a calibration as a `SmoothForm`. -/
def IsCalibration.toSmoothForm (hφ : IsCalibration g φ) : SmoothForm I M ℝ k :=
  ⟨φ, hφ.isSmoothForm.mem_smoothBundleForms⟩

/-- Coercing `hφ.toSmoothForm` back to a rough form recovers `φ`. -/
@[simp]
theorem IsCalibration.coe_toSmoothForm (hφ : IsCalibration g φ) :
    (hφ.toSmoothForm : RoughForm I M ℝ k) = φ := (rfl)

/-- Bundled as a `SmoothForm`, a calibration is closed. -/
theorem IsCalibration.isClosed_toSmoothForm (hφ : IsCalibration g φ) :
    hφ.toSmoothForm.IsClosed :=
  (SmoothForm.isClosed_def hφ.toSmoothForm).2 hφ.mextDeriv_eq_zero

/-- **Operator-norm characterization of calibrations**: `φ` is a calibration for `g` if and only if
`φ` is smooth, closed, and has pointwise operator norm (comass) at most `1` with respect to `g`. -/
theorem isCalibration_iff_norm_le_one :
    IsCalibration g φ ↔
      IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
        ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          ‖φ x‖) ≤ 1 := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [isCalibration_def]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  rw [(φ x).opNorm_le_iff_le_orthonormal zero_le_one]
  exact forall_congr' fun v ↦ by
    simp_rw [orthonormal_iff_ite, Real.norm_eq_abs,
      ContMDiffRiemannianMetric.inner_riemannianBundle]

/-- At every point `x`, a calibration has comass `‖φ x‖ ≤ 1` for the inner product `g_x`. -/
theorem IsCalibration.norm_le_one (hφ : IsCalibration g φ) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ‖φ x‖) ≤ 1 :=
  (isCalibration_iff_norm_le_one.1 hφ).2.2 x

/-- In positive degree `1 ≤ k`, the two-sided bound `|φ x v| ≤ 1` in `IsCalibration` is equivalent
to the one-sided bound `φ x v ≤ 1` on `g_x`-orthonormal frames. -/
theorem isCalibration_iff_apply_le_one (hk : 1 ≤ k) :
    IsCalibration g φ ↔
      IsSmoothForm I ∞ φ ∧ mextDeriv φ = 0 ∧
        ∀ x (v : Fin k → TangentSpace I x),
          (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) → φ x v ≤ 1 := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [isCalibration_iff_norm_le_one]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  rw [(φ x).opNorm_le_iff_apply_le_orthonormal hk zero_le_one]
  exact forall_congr' fun v ↦ by
    simp_rw [orthonormal_iff_ite, ContMDiffRiemannianMetric.inner_riemannianBundle]

/-- The zero `k`-form is a calibration on every smooth Riemannian manifold. -/
@[simp]
theorem isCalibration_zero (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    IsCalibration g (0 : RoughForm I M ℝ k) :=
  ⟨IsSmoothForm.zero ∞, mextDeriv_zero, fun _ _ _ ↦ by simp⟩

/-- Negating a calibration yields a calibration. -/
theorem IsCalibration.neg (hφ : IsCalibration g φ) : IsCalibration g (-φ) :=
  ⟨hφ.isSmoothForm.neg, by rw [mextDeriv_neg, hφ.mextDeriv_eq_zero, neg_zero],
    fun x v hv ↦ by simpa using hφ.abs_apply_le_one x hv⟩

/-- `-φ` is a calibration if and only if `φ` is a calibration. -/
@[simp]
theorem isCalibration_neg_iff : IsCalibration g (-φ) ↔ IsCalibration g φ :=
  ⟨fun h ↦ by simpa using h.neg, IsCalibration.neg⟩

/-- Scaling a calibration by a real constant `c` with `|c| ≤ 1` yields a calibration. -/
theorem IsCalibration.smul_of_abs_le_one (hφ : IsCalibration g φ) {c : ℝ} (hc : |c| ≤ 1) :
    IsCalibration g (c • φ) := by
  refine ⟨hφ.isSmoothForm.smul c, by rw [mextDeriv_smul, hφ.mextDeriv_eq_zero, smul_zero],
    fun x v hv ↦ ?_⟩
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hφ.abs_apply_le_one x hv) (abs_nonneg c)).trans
    (by rwa [mul_one])

/-- **Convexity of calibrations**: if `0 ≤ a`, `0 ≤ b`, and `a + b ≤ 1` (in particular for convex
combinations `a + b = 1`), then `a • φ + b • ψ` is a calibration whenever `φ` and `ψ` are. -/
theorem IsCalibration.convex_combo (hφ : IsCalibration g φ) (hψ : IsCalibration g ψ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) : IsCalibration g (a • φ + b • ψ) := by
  refine ⟨(hφ.isSmoothForm.smul a).add (hψ.isSmoothForm.smul b), (SmoothForm.isClosed_def _).1
    ((hφ.isClosed_toSmoothForm.smul a).add (hψ.isClosed_toSmoothForm.smul b)), fun x v hv ↦ ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  linarith [mul_le_mul_of_nonneg_left (hφ.abs_apply_le_one x hv) ha,
    mul_le_mul_of_nonneg_left (hψ.abs_apply_le_one x hv) hb]

end Projections

section DegreeZero

/-- **Degree-zero calibrations from functions**: `RoughForm.ofFunction I f` is a calibration on
`(M, g)` if and only if `f` is locally constant and takes values in `[-1, 1]`. The manifold may
have boundary or corners. -/
theorem isCalibration_ofFunction_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (f : M → ℝ) :
    IsCalibration g (RoughForm.ofFunction I f) ↔ IsLocallyConstant f ∧ ∀ x, |f x| ≤ 1 := by
  refine ⟨fun h ↦ ⟨?_, fun x ↦ by simpa using h.abs_apply_le_one x (v := ![]) (fun i ↦ i.elim0)⟩,
    fun ⟨hlc, hb⟩ ↦ ?_⟩
  · have hf : ContMDiff I 𝓘(ℝ) ∞ f := isSmoothForm_ofFunction_iff.1 h.isSmoothForm
    exact (mextDeriv_ofFunction_eq_zero_iff (hf.mdifferentiable (by simp))).1 h.mextDeriv_eq_zero
  · have hf : ContMDiff I 𝓘(ℝ) ∞ f := fun x ↦
      contMDiffAt_const.congr_of_eventuallyEq ((IsLocallyConstant.iff_eventually_eq f).1 hlc x)
    exact ⟨isSmoothForm_ofFunction_iff.2 hf,
      (mextDeriv_ofFunction_eq_zero_iff (hf.mdifferentiable (by simp))).2 hlc,
      fun x _ _ ↦ by simpa using hb x⟩

/-- **Characterization of degree-zero calibrations**: a rough `0`-form `φ` is a calibration if and
only if `x ↦ φ x ![]` is locally constant with values in `[-1, 1]`. -/
theorem isCalibration_zero_degree_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ 0) :
    IsCalibration g φ ↔ IsLocallyConstant (fun x ↦ φ x ![]) ∧ ∀ x, |φ x ![]| ≤ 1 := by
  have hφ : φ = RoughForm.ofFunction I (fun x ↦ φ x ![]) :=
    (RoughForm.eq_ofFunction φ).trans
      (by congr with x; exact congrArg (φ x) (Subsingleton.elim 0 ![]))
  conv_lhs => rw [hφ]
  exact isCalibration_ofFunction_iff g (fun x ↦ φ x ![])

end DegreeZero

section Pullback

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}

/-- Pulling a calibration `φ` on `(M, g)` back along a smooth map `f : N → M` that intertwines `g'`
and `g` (`g'_{y}(v, w) = g_{f y}(df_y v, df_y w)`) gives a calibration on `(N, g')`. -/
theorem IsCalibration.mpullback_of_inner_eq (hφ : IsCalibration g φ)
    (g' : ContMDiffRiemannianMetric I' ∞ E' (fun y : N ↦ TangentSpace I' y))
    {f : N → M} (hf : ContMDiff I' I ∞ f)
    (hg : ∀ y v w, g'.inner y v w = g.inner (f y) (mfderiv I' I f y v) (mfderiv I' I f y w)) :
    IsCalibration g' (TauCeti.mpullback I' I f φ) := by
  have hcoe : ((SmoothForm.mpullback f hf hφ.toSmoothForm : SmoothForm I' N ℝ k) :
      RoughForm I' N ℝ k) = TauCeti.mpullback I' I f φ := by
    rw [SmoothForm.coe_mpullback, hφ.coe_toSmoothForm]
  refine ⟨hcoe ▸ (SmoothForm.mpullback f hf hφ.toSmoothForm).isSmoothForm,
    hcoe ▸ (SmoothForm.isClosed_def _).1 (hφ.isClosed_toSmoothForm.mpullback f hf), fun y v hv ↦ ?_⟩
  rw [mpullback_apply]
  exact hφ.abs_apply_le_one (f y) fun i j ↦ by rw [← hg y (v i) (v j), hv i j]

/-- Pulling a calibration `φ` on `(M, g)` back along a smooth immersion `f : N → M` gives a
calibration for the pullback metric `f*g` on `N`. -/
theorem IsCalibration.mpullback [FiniteDimensional ℝ E'] (hφ : IsCalibration g φ) (f : N → M)
    (hf : ContMDiff I' I ∞ f) (hinj : ∀ y, Function.Injective (mfderiv I' I f y)) :
    IsCalibration (g.pullback f (by simpa using hf) hinj) (TauCeti.mpullback I' I f φ) :=
  hφ.mpullback_of_inner_eq _ hf fun y v w ↦
    ContMDiffRiemannianMetric.pullback_inner g f (by simpa using hf) hinj y v w

/-- Restricting a calibration `φ` on `(M, g)` to an open subset `U : Opens M` gives a calibration
for the restricted metric `g.restrictOpenTangentSpace U`. -/
theorem IsCalibration.restrictOpenTangentSpace (hφ : IsCalibration g φ)
    (U : TopologicalSpace.Opens M) :
    IsCalibration (g.restrictOpenTangentSpace U)
      (TauCeti.mpullback I I (Subtype.val : U → M) φ) :=
  hφ.mpullback_of_inner_eq (g.restrictOpenTangentSpace U) contMDiff_subtype_val fun y v w ↦ by
    rw [ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
      Manifold.mfderiv_subtype_val (I := I) y, ContinuousLinearEquiv.coe_coe]

end Pullback

section FiniteDimensional

variable [FiniteDimensional ℝ E]
  {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {φ : RoughForm I M ℝ k}

/-- **Pointwise linear calibration inequality**: for a calibration `φ` on `(M, g)` and any `k`-tuple
`v` of tangent vectors at `x`, `|φ x v| ≤ ‖v₁ ∧ ⋯ ∧ vₖ‖` in the metric induced by `g_x` on the
exterior power `⋀[ℝ]^k (T_x M)`. -/
theorem IsCalibration.abs_apply_le_norm_ιMulti (hφ : IsCalibration g φ) (x : M)
    (v : Fin k → TangentSpace I x) :
    |φ x v| ≤
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ‖ιMulti ℝ k v‖) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  refine (Real.norm_eq_abs _).symm.trans_le (((φ x).le_opNorm_mul_norm_ιMulti v).trans ?_)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hφ.norm_le_one x) (norm_nonneg _)

/-- **The Riemannian volume form is a calibration** in every dimension `m`, including `m = 0` and on
manifolds with boundary or corners. -/
theorem isCalibration_riemannianVolumeForm {m : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibration g (riemannianVolumeForm o) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  refine isCalibration_iff_norm_le_one.2 ⟨isSmoothForm_riemannianVolumeForm o,
    mextDeriv_eq_zero_of_finrank_le (by simpa using o.card_eq.ge) _, fun x ↦ ?_⟩
  let := o.fact_finrank_tangentSpace x
  rw [riemannianVolumeForm_def, (o.orientationAt x).norm_volumeFormL]

end FiniteDimensional

section VectorSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}

/-- On a real inner product space `V` equipped with its standard flat metric
`(riemannianMetricVectorSpace V).ofLE le_top`, the constant smooth `k`-form `SmoothForm.const A` is
a calibration if and only if `A` has comass `‖A‖ ≤ 1`. -/
@[simp]
theorem isCalibration_const_iff (A : V [⋀^Fin k]→L[ℝ] ℝ) :
    IsCalibration ((riemannianMetricVectorSpace V).ofLE le_top) (SmoothForm.const A).1 ↔
      ‖A‖ ≤ 1 := by
  rw [isCalibration_def, and_iff_right (SmoothForm.const A).isSmoothForm,
    and_iff_right ((SmoothForm.isClosed_def _).1 (SmoothForm.isClosed_const A)),
    A.opNorm_le_iff_le_orthonormal zero_le_one]
  have hinner (x : V) (u w : TangentSpace 𝓘(ℝ, V) x) :
      (riemannianMetricVectorSpace V).inner x u w =
        inner ℝ (NormedSpace.fromTangentSpace x u) (NormedSpace.fromTangentSpace x w) := by
    rw [← ContMDiffRiemannianMetric.inner_riemannianBundle (riemannianMetricVectorSpace V) x u w,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      ← map_add, norm_tangentSpace_vectorSpace, norm_tangentSpace_vectorSpace,
      norm_tangentSpace_vectorSpace]
  refine ⟨fun h u hu ↦ ?_, fun h x v hv ↦ ?_⟩
  · rw [Real.norm_eq_abs]
    simpa using h 0 (fun i ↦ (NormedSpace.fromTangentSpace 0).symm (u i)) fun i j ↦ by
      simpa [hinner] using orthonormal_iff_ite.1 hu i j
  · rw [SmoothForm.const_apply, ← Real.norm_eq_abs]
    refine h (fun i ↦ NormedSpace.fromTangentSpace x (v i)) (orthonormal_iff_ite.2 fun i j ↦ ?_)
    rw [← hinner x (v i) (v j), ← hv i j, ContMDiffRiemannianMetric.ofLE_inner]

/-- For any orthonormal frame `u : Fin k → V` in a finite-dimensional real inner product space `V`,
the constant smooth `k`-form `SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k u))` is a
calibration on `(V, (riemannianMetricVectorSpace V).ofLE le_top)`. -/
theorem _root_.Orthonormal.isCalibration_const_alternatingFormEquiv_ιMulti [FiniteDimensional ℝ V]
    {u : Fin k → V} (hu : Orthonormal ℝ u) :
    IsCalibration ((riemannianMetricVectorSpace V).ofLE le_top)
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k u))).1 := by
  rw [isCalibration_const_iff, hu.norm_alternatingFormEquiv_ιMulti]

end VectorSpace

end General

end TauCeti
