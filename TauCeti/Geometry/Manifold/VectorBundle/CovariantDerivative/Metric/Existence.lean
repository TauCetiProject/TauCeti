/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Affine
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Basic
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Metric-compatible connections on real vector bundles

For a finite-rank real vector bundle with a `C¹` metric over a real charted space, the metric
defect of a connection determines a correction: raise one metric slot and divide by two. Adding
this correction gives a metric-compatible connection on the same native bundle. A connection
that is already metric is unchanged on every section, including nondifferentiable sections.

For every `n : ℕ∞`, correction preserves `C^n` regularity when the bundle and metric are
`C^(n+1)`, on a finite-dimensional Hausdorff smooth base. On a σ-compact such base, native bare
connection existence therefore gives actual metric-compatible connections. Rank zero, model
dimension zero and empty bases are included.

## Main results

* `CovariantDerivative.metricCorrected`: correction of an arbitrary native connection.
* `CovariantDerivative.isMetricCompatible_metricCorrected`: metric compatibility.
* `CovariantDerivative.derivMetricTensor_eq_inner_metricCorrection_add`: the metric defect is the
  symmetric part of the correction.
* `CovariantDerivative.IsMetricCompatible.metricCorrected_eq`: exact fixedness.
* `CovariantDerivative.ContMDiffCovariantDerivative.metricCorrected`: preservation of
  `C^n` regularity for every `n : ℕ∞`, including smoothness.
* `CovariantDerivative.exists_contMDiffCovariantDerivative_isMetricCompatible`: existence.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
/-- The metric defect evaluated on a `C^(n+1)` section is `C^n` in its two remaining slots
when the connection is `C^n` and the metric is `C^(n+1)`. This includes `n = 0` and rank zero. -/
theorem contMDiff_derivMetricTensor_apply [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] {n : ℕ∞}
    [ContMDiffVectorBundle (n + 1) F V I] [IsContMDiffRiemannianBundle I (n + 1) F V]
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov n]
    {σ : Π x, V x} (hσ : CMDiff (n + 1) (T% σ)) :
    let _ : ContMDiffVectorBundle 1 F V I :=
      .of_le (show (1 : ℕ∞ω) ≤ n + 1 from le_add_self)
    let _ : IsContMDiffRiemannianBundle I 1 F V :=
      .of_le (show (1 : ℕ∞ω) ≤ n + 1 from le_add_self)
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (cov.derivMetricTensor x (σ x))) := by
  intro bundleOne metricOne
  have : ContMDiffVectorBundle n F V I :=
    .of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)
  have : IsContMDiffRiemannianBundle I n F V :=
    .of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)
  apply contMDiffOn_univ.1
  apply TauCeti.Manifold.contMDiffOn_hom_of_forall_contMDiff
    (m := (n : ℕ∞ω) + 1) le_self_add (by simp)
  intro τ hτ
  have hcovσ := contMDiffOn_univ.1 (ContMDiffCovariantDerivative.contMDiff.contMDiff
    (cov := cov) hσ.contMDiffOn)
  have hcovτ := contMDiffOn_univ.1 (ContMDiffCovariantDerivative.contMDiff.contMDiff
    (cov := cov) hτ.contMDiffOn)
  have hσdual : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ) x (innerSL ℝ (σ x))) := fun x ↦ by
    simpa only [contMDiffWithinAt_univ] using ((hσ.of_le le_self_add) x).innerSL_bundle
  have hτdual : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ) x (innerSL ℝ (τ x))) := fun x ↦ by
    simpa only [contMDiffWithinAt_univ] using ((hτ.of_le le_self_add) x).innerSL_bundle
  have h := (hσ.inner_bundle hτ).contMDiff_totalSpaceMk_mvfderiv
    |>.sub_section (hτdual.clm_bundle_comp hcovσ)
    |>.sub_section (hσdual.clm_bundle_comp hcovτ)
  refine h.contMDiffOn.congr fun x _ ↦ ?_
  congr 1
  ext X
  -- The explicit constant tangent field fixes the unbundled direction in the native formula.
  erw [cov.derivMetricTensor_apply (X := fun _ ↦ X) x (hσ.mdifferentiableAt (by simp))
    (hτ.mdifferentiableAt (by simp))]
  simp only [Pi.sub_apply, sub_apply, ContinuousLinearMap.comp_apply]
  -- Align the metric-induced scalar/module projections in the two Riesz evaluations.
  erw [innerSL_apply_apply, innerSL_apply_apply]
  rw [real_inner_comm (cov σ x X) (τ x)]

/-- Half the metric defect with one fibre slot raised by the metric. The section vector
precedes the tangent direction, as in `CovariantDerivative.addOneForm`. -/
def metricCorrection (cov : CovariantDerivative I F V) (x : M) :
    V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  letI := VectorBundle.finiteDimensional ℝ F V x
  letI : IsNormableSpace ℝ (TangentSpace I x) := inferInstanceAs (IsNormableSpace ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun u := (2 : ℝ)⁻¹ • ((innerSL ℝ (E := V x)).inverse.comp
        (cov.derivMetricTensor x u).flip)
      map_add' u v := by
        ext X
        simp only [map_add, ContinuousLinearMap.flip_add, add_apply,
          ContinuousLinearMap.comp_apply, smul_apply, smul_add]
      map_smul' c u := by
        ext X
        simp only [map_smul, ContinuousLinearMap.flip_smul, ContinuousLinearMap.comp_apply,
          smul_apply, RingHom.id_apply, smul_smul]
        rw [mul_comm] }

/-- Evaluate the raised metric defect on a fibre vector, leaving the tangent direction free. -/
theorem metricCorrection_apply (cov : CovariantDerivative I F V) (x : M) (u : V x) :
    let _ : IsNormableSpace ℝ (TangentSpace I x) :=
      inferInstanceAs (IsNormableSpace ℝ E)
    cov.metricCorrection x u = (2 : ℝ)⁻¹ •
      ((innerSL ℝ (E := V x)).inverse.comp (cov.derivMetricTensor x u).flip) := by
  intro _tangentNormable
  rfl

/-- The metric correction represents half of the metric defect. -/
@[simp]
theorem inner_metricCorrection (cov : CovariantDerivative I F V) (x : M)
    (u v : V x) (X : TangentSpace I x) :
    inner ℝ (cov.metricCorrection x u X) v = (2 : ℝ)⁻¹ * cov.derivMetricTensor x u v X := by
  let := VectorBundle.finiteDimensional ℝ F V x
  let : IsNormableSpace ℝ (TangentSpace I x) := inferInstanceAs (IsNormableSpace ℝ E)
  have hinv := InnerProductSpace.isInvertible_innerSL (E := V x)
  rw [metricCorrection_apply]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_left]
  congr 1
  exact congrArg (fun φ ↦ φ v) (hinv.self_apply_inverse ((cov.derivMetricTensor x u).flip X))


/-- Correct a connection by adding half its metric defect, with one fibre slot raised by the
metric (`metricCorrection`). -/
def metricCorrected (cov : CovariantDerivative I F V) : CovariantDerivative I F V :=
  cov.addOneForm cov.metricCorrection

/-- Evaluation of the corrected connection on any section, including sections that are not
differentiable. -/
@[simp]
theorem metricCorrected_apply (cov : CovariantDerivative I F V) (σ : Π x, V x)
    (x : M) : cov.metricCorrected σ x = cov σ x + cov.metricCorrection x (σ x) :=
  cov.addOneForm_apply _ _ _

/-- The metric correction makes every connection metric-compatible. -/
theorem isMetricCompatible_metricCorrected (cov : CovariantDerivative I F V) :
    cov.metricCorrected.IsMetricCompatible := by
  rw [isMetricCompatible_iff_derivMetricTensor_eq_zero]
  ext x u v X
  have hsymm := cov.derivBilinearTensor_apply_comm
    (b := fun y ↦ innerSL ℝ (E := V y))
    (fun y a b ↦ by
      -- The metric-induced module projections are definitionally equal to the ambient ones;
      -- `erw` unfolds those projections so the generic Riesz evaluation lemma matches.
      erw [innerSL_apply_apply, innerSL_apply_apply]
      exact (real_inner_comm a b).symm) u v
  rw [cov.derivBilinearTensor_eq_derivMetricTensor (fun _ _ _ ↦ rfl)] at hsymm
  simp only [metricCorrected, derivMetricTensor_addOneForm, zero_apply,
    inner_metricCorrection, real_inner_comm (cov.metricCorrection x v X) u,
    hsymm]
  ring

/-- The metric defect of a connection is the symmetric part of its correction `C`:
`X ⟪u, v⟫ - ⟪∇_X u, v⟫ - ⟪u, ∇_X v⟫ = ⟪C(u, X), v⟫ + ⟪u, C(v, X)⟫`. So a connection is metric
exactly when its correction is skew-adjoint in every tangent direction. -/
theorem derivMetricTensor_eq_inner_metricCorrection_add (cov : CovariantDerivative I F V)
    (x : M) (u v : V x) (X : TangentSpace I x) :
    cov.derivMetricTensor x u v X =
      inner ℝ (cov.metricCorrection x u X) v + inner ℝ u (cov.metricCorrection x v X) := by
  have h := congrArg (fun T ↦ T x u v X)
    (isMetricCompatible_iff_derivMetricTensor_eq_zero.1 cov.isMetricCompatible_metricCorrected)
  simp only [metricCorrected, derivMetricTensor_addOneForm, zero_apply] at h
  linarith

/-- An already metric-compatible connection is unchanged as a native connection, on every
input section rather than just differentiable sections. -/
@[simp]
theorem IsMetricCompatible.metricCorrected_eq {cov : CovariantDerivative I F V}
    (hcov : cov.IsMetricCompatible) : cov.metricCorrected = cov := by
  have hzero := isMetricCompatible_iff_derivMetricTensor_eq_zero.mp hcov
  ext σ x X
  rw [metricCorrected_apply]
  have hz : cov.metricCorrection x (σ x) X = 0 := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_metricCorrection]
    simp [hzero]
  simp [hz]

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
/-- The metric correction of a `C^n` connection is `C^n` when the metric and bundle are
`C^(n+1)`. No positive rank or dimension assumption is needed. -/
theorem contMDiff_metricCorrection [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] {n : ℕ∞}
    [ContMDiffVectorBundle (n + 1) F V I] [IsContMDiffRiemannianBundle I (n + 1) F V]
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov n] :
    let _ : ContMDiffVectorBundle 1 F V I :=
      .of_le (show (1 : ℕ∞ω) ≤ n + 1 from le_add_self)
    let _ : IsContMDiffRiemannianBundle I 1 F V :=
      .of_le (show (1 : ℕ∞ω) ≤ n + 1 from le_add_self)
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ V x →L[ℝ] TangentSpace I x →L[ℝ] V x) x
        (cov.metricCorrection x)) := by
  intro bundleOne metricOne
  have : ContMDiffVectorBundle n F V I :=
    .of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)
  have : IsContMDiffRiemannianBundle I n F V :=
    .of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)
  let : ∀ x : M, IsNormableSpace ℝ (TangentSpace I x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) x).isNormableSpace
  apply contMDiffOn_univ.1
  apply TauCeti.Manifold.contMDiffOn_hom_of_forall_contMDiff
    (m := (n : ℕ∞ω) + 1) le_self_add (by simp)
  intro σ hσ
  have hB := cov.contMDiff_derivMetricTensor_apply (n := n) hσ
  have hflip := fun x ↦ (hB x).clm_bundle_flip
  have hinv := IsContMDiffRiemannianBundle.contMDiff_innerSL_inverse
    (I := I) (F := F) (V := V) (n := n)
  have h := (hinv.clm_bundle_comp hflip).const_smul_section (a := (2 : ℝ)⁻¹)
  exact h.contMDiffOn.congr fun x _ ↦
    congrArg (TotalSpace.mk' (E →L[ℝ] F) x) (cov.metricCorrection_apply x (σ x)).symm

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
/-- Correcting a `C^n` connection using a `C^(n+1)` metric preserves its order of regularity,
including continuity and smoothness. -/
instance ContMDiffCovariantDerivative.metricCorrected [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I ∞ M] {n : ℕ∞ω} [ENat.LEInfty n]
    [ContMDiffVectorBundle (n + 1) F V I] [IsContMDiffRiemannianBundle I (n + 1) F V]
    {cov : CovariantDerivative I F V} [hcov : ContMDiffCovariantDerivative cov n] :
    let _ : ContMDiffVectorBundle 1 F V I :=
      .of_le (show (1 : ℕ∞ω) ≤ n + 1 from le_add_self)
    let _ : IsContMDiffRiemannianBundle I 1 F V :=
      .of_le (show (1 : ℕ∞ω) ≤ n + 1 from le_add_self)
    ContMDiffCovariantDerivative cov.metricCorrected n := by
  intro bundleOne metricOne
  lift n to ℕ∞ using ENat.LEInfty.ne_top n
  exact hcov.addOneForm cov.contMDiff_metricCorrection

omit [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V] in
/-- Every finite-rank real `C^k` vector bundle with a `C^k` metric over a finite-dimensional,
σ-compact Hausdorff smooth manifold admits a `C^n` metric-compatible connection if `n+1≤k`.
This includes continuous and smooth connections, and rank zero. -/
theorem exists_contMDiffCovariantDerivative_isMetricCompatible
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    {n : ℕ∞} {k : ℕ∞ω} [ContMDiffVectorBundle k F V I]
    [IsContMDiffRiemannianBundle I k F V] (hk : n + 1 ≤ k) :
    let _ : ContMDiffVectorBundle 1 F V I := .of_le (le_add_self.trans hk)
    let _ : IsContMDiffRiemannianBundle I 1 F V := .of_le (le_add_self.trans hk)
    ∃ cov : CovariantDerivative I F V,
      ContMDiffCovariantDerivative cov n ∧ cov.IsMetricCompatible := by
  intro bundleOne metricOne
  have : ContMDiffVectorBundle (n + 1) F V I := .of_le hk
  have : IsContMDiffRiemannianBundle I (n + 1) F V := .of_le hk
  obtain ⟨cov, hcov⟩ := exists_contMDiffCovariantDerivative (I := I) (F := F) (V := V) hk
  exact ⟨cov.metricCorrected, inferInstance, cov.isMetricCompatible_metricCorrected⟩

end CovariantDerivative
