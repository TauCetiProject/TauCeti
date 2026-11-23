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
* `TauCeti.isCalibration_iff_isLocallyConstant_and_abs_apply_le_one`: degree-zero calibrations are
  locally constant functions into `[-1, 1]`.
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
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let v' : Fin k → TangentSpace I x := Function.update v 0 (-v 0)
  have hv' : ∀ i j, g.inner x (v' i) (v' j) = if i = j then 1 else 0 := by
    have hvo' : Orthonormal ℝ v' :=
      (orthonormal_iff_ite.2 hv : Orthonormal ℝ v).orthonormal_of_forall_eq_or_eq_neg fun i ↦ by
        rcases eq_or_ne i 0 with rfl | hi
        · exact Or.inr (Function.update_self 0 (-v 0) v)
        · exact Or.inl (Function.update_of_ne hi (-v 0) v)
    exact orthonormal_iff_ite.1 hvo'
  have hval : φ x v' = -φ x v := by
    have hsmul := (φ x).map_update_smul v 0 (-1 : ℝ) (v 0)
    simpa [v', Function.update_eq_self] using hsmul
  have hbound := hle x v' hv'
  linarith

/-- In degree zero, a calibration is a locally constant function with values in `[-1, 1]`. -/
theorem isCalibration_iff_isLocallyConstant_and_abs_apply_le_one
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ 0) :
    IsCalibration g φ ↔ IsLocallyConstant (fun x ↦ φ x ![]) ∧ ∀ x, |φ x ![]| ≤ 1 := by
  rw [isCalibration_iff]
  have hfn : φ = RoughForm.ofFunction I (fun x ↦ φ x ![]) := by
    simpa only [Subsingleton.elim (0 : Fin 0 → _) ![]] using RoughForm.eq_ofFunction φ
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
    · rw [Subsingleton.elim v ![]]
      exact hbd x

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

end Calibrations

end TauCeti
