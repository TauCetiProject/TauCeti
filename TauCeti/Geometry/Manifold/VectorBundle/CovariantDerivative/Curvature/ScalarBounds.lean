/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Trace
public import Mathlib.Analysis.InnerProductSpace.Positive
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Scalar control of nonnegative curvature operators

For a metric connection whose curvature operator is nonnegative, the scalar curvature
controls the entire curvature operator and every four-vector curvature pairing. The
constant is `1 / 2`, since the scalar curvature is twice the trace of the bivector operator.
The conclusions include zero-dimensional tangent spaces and do not require completeness.

These estimates supply the scalar-to-curvature control used in ancient-solution arguments.
The curvature operator acts on the second exterior power. For a family of metrics with a
uniform scalar upper bound, these estimates give a uniform curvature bound in each metric's
own norm. Scalar curvature vanishes exactly at flat points under operator positivity.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapter 4.
* B. Kleiner and J. Lott, *Notes on Perelman's papers*, Section 41.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- Nonnegative curvature operator implies nonnegative scalar curvature. -/
theorem scalarCurvature_nonneg_of_curvatureEndomorphism_nonneg
    (x : M)
    (hpos : ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      0 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫) :
    0 ≤ cov.scalarCurvature x := by
  rw [cov.scalarCurvature_eq_two_mul_trace_curvatureEndomorphism hcov x]
  refine mul_nonneg (by norm_num) ?_
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x)))]
  exact Finset.sum_nonneg fun i _ ↦ by simpa only [real_inner_comm] using hpos _

/-- Quadratic nonnegativity bounds the curvature quadratic form by half the scalar curvature. -/
theorem inner_curvatureEndomorphism_le_scalarCurvature
    (x : M)
    (hpos : ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      0 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫)
    (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    ⟪cov.curvatureEndomorphism hcov x z, z⟫ ≤ cov.scalarCurvature x / 2 * ‖z‖ ^ 2 := by
  classical
  by_cases hz : z = 0
  · simp [hz]
  let A := cov.curvatureEndomorphism hcov x
  let e : ⋀[ℝ]^2 (TangentSpace I x) := ‖z‖⁻¹ • z
  have he : ‖e‖ = 1 := by
    simp [e, norm_smul, norm_ne_zero_iff.mpr hz]
  have hon : Orthonormal ℝ
      (Subtype.val : ({e} : Set (⋀[ℝ]^2 (TangentSpace I x))) →
        ⋀[ℝ]^2 (TangentSpace I x)) :=
    orthonormal_subsingleton_iff.mpr fun i ↦ by
      simpa only [Set.mem_singleton_iff.mp i.property] using he
  obtain ⟨u, b, heu, hb⟩ := hon.exists_orthonormalBasis_extension
  have hi : e ∈ u := heu (by simp)
  have hsum : ⟪A e, e⟫ ≤ LinearMap.trace ℝ _ A := by
    rw [LinearMap.trace_eq_sum_inner A b, hb]
    have h := Finset.single_le_sum
      (f := fun i : u ↦ ⟪(i : ⋀[ℝ]^2 (TangentSpace I x)), A i⟫)
      (fun i _ ↦ by simpa only [real_inner_comm] using hpos (i : ⋀[ℝ]^2 (TangentSpace I x)))
      (Finset.mem_univ (⟨e, hi⟩ : u))
    simpa only [real_inner_comm] using h
  have hvec : z = ‖z‖ • e := by
    simp [e, smul_smul, norm_ne_zero_iff.mpr hz]
  have hinner : ⟪A z, z⟫ = ‖z‖ ^ 2 * ⟪A e, e⟫ := by
    conv_lhs => rw [hvec, map_smul, real_inner_smul_left (A e) (‖z‖ • e) ‖z‖,
      real_inner_smul_right (A e) e ‖z‖]
    ring
  rw [cov.scalarCurvature_eq_two_mul_trace_curvatureEndomorphism hcov x]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  dsimp only [A] at hinner hsum
  rw [hinner]
  nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg ‖z‖)]

/-- The operator norm of a nonnegative curvature operator is at most half the scalar curvature. -/
theorem norm_curvatureEndomorphism_le_scalarCurvature
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive) :
    ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ ≤
      cov.scalarCurvature x / 2 := by
  let A := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  have hA : A.IsSymmetric := hpos.isSymmetric
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  refine ciSup_le fun z ↦ ?_
  have hz := cov.inner_curvatureEndomorphism_le_scalarCurvature hcov x hpos.inner_nonneg_left z
  by_cases hzero : z = 0
  · simp only [hzero, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    exact div_nonneg
      (cov.scalarCurvature_nonneg_of_curvatureEndomorphism_nonneg hcov x hpos.inner_nonneg_left)
      (by norm_num)
  · have hn : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzero)
    have hquot : A.rayleighQuotient z =
        ⟪cov.curvatureEndomorphism hcov x z, z⟫ / ‖z‖ ^ 2 := rfl
    have hzpos : 0 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫ := hpos.inner_nonneg_left z
    rw [hquot, abs_of_nonneg (div_nonneg hzpos hn.le)]
    exact (div_le_iff₀ hn).mpr hz

/-- For nonnegative curvature operator, every curvature pairing is controlled by scalar
curvature and the four vector norms. -/
theorem abs_inner_curvatureTensor_le_scalarCurvature
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive)
    (u v w z : TangentSpace I x) :
    |⟪cov.curvatureTensor x u v w, z⟫| ≤
      cov.scalarCurvature x / 2 * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
  let A := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  let a := exteriorPower.ιMulti ℝ 2 ![u, v]
  let b := exteriorPower.ιMulti ℝ 2 ![z, w]
  have hA := cov.norm_curvatureEndomorphism_le_scalarCurvature hcov x hpos
  have hC : 0 ≤ cov.scalarCurvature x / 2 :=
    div_nonneg
      (cov.scalarCurvature_nonneg_of_curvatureEndomorphism_nonneg hcov x hpos.inner_nonneg_left)
      (by norm_num)
  have hab : |⟪A a, b⟫| ≤ cov.scalarCurvature x / 2 * ‖a‖ * ‖b‖ := by
    exact (abs_real_inner_le_norm _ _).trans <|
      mul_le_mul_of_nonneg_right ((A.le_opNorm a).trans <|
        mul_le_mul_of_nonneg_right hA (norm_nonneg a)) (norm_nonneg b)
  have hwedge : ‖a‖ * ‖b‖ ≤ (‖u‖ * ‖v‖) * (‖z‖ * ‖w‖) :=
    mul_le_mul (exteriorPower.norm_ιMulti_two_le u v)
      (exteriorPower.norm_ιMulti_two_le z w) (norm_nonneg b)
      (mul_nonneg (norm_nonneg u) (norm_nonneg v))
  calc
    |⟪cov.curvatureTensor x u v w, z⟫| = |⟪A a, b⟫| := by
      simp only [A, a, b, LinearMap.coe_toContinuousLinearMap',
        inner_curvatureEndomorphism_ιMulti, Matrix.cons_val_zero, Matrix.cons_val_one]
    _ ≤ cov.scalarCurvature x / 2 * (‖a‖ * ‖b‖) := by simpa only [mul_assoc] using hab
    _ ≤ cov.scalarCurvature x / 2 * ((‖u‖ * ‖v‖) * (‖z‖ * ‖w‖)) :=
      mul_le_mul_of_nonneg_left hwedge hC
    _ = cov.scalarCurvature x / 2 * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by ring

/-- Scalar curvature bounds the actual tangent vector `R(u,v)w` when the curvature operator
is nonnegative. -/
theorem norm_curvatureTensor_le_scalarCurvature
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive)
    (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤ cov.scalarCurvature x / 2 * ‖u‖ * ‖v‖ * ‖w‖ := by
  by_cases hzero : cov.curvatureTensor x u v w = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (div_nonneg
        (cov.scalarCurvature_nonneg_of_curvatureEndomorphism_nonneg hcov x hpos.inner_nonneg_left)
        (by norm_num)) (norm_nonneg u)) (norm_nonneg v)) (norm_nonneg w)
  · have h := cov.abs_inner_curvatureTensor_le_scalarCurvature hcov x hpos u v w
      (cov.curvatureTensor x u v w)
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _), pow_two] at h
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hzero)).mp h

/-- Under nonnegative curvature operator, scalar curvature vanishes exactly at flat points. -/
theorem scalarCurvature_eq_zero_iff_curvatureTensor_eq_zero
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive) :
    cov.scalarCurvature x = 0 ↔ cov.curvatureTensor x = 0 := by
  refine ⟨fun hscalar ↦ ?_, cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x⟩
  ext u v w
  have hnorm : ‖cov.curvatureTensor x u v w‖ ≤ 0 := by
    simpa only [hscalar, zero_div, zero_mul] using
      cov.norm_curvatureTensor_le_scalarCurvature hcov x hpos u v w
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

end CovariantDerivative

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A uniform scalar upper bound for a family of metrics with nonnegative curvature operator
gives a positive uniform bound for their curvature tensors, in each metric's own norm.

No regularity of the parameter family is needed. In particular, this applies to a time slab
of an ancient Ricci flow without requiring compactness or a common background metric. -/
theorem exists_pos_norm_curvatureTensor_le_of_scalarCurvature_le
    {T : Type*} (g : T → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (s : Set T) (C : ℝ)
    (hpos : ∀ t ∈ s,
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
      ∀ (x : M) (z : ⋀[ℝ]^2 (TangentSpace I x)),
        0 ≤ ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫)
    (hscalar : ∀ t ∈ s, ∀ x, (g t).scalarCurvature x ≤ C) :
    ∃ K > 0, ∀ t ∈ s,
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
      ∀ (x : M) (u v w : TangentSpace I x),
        ‖(CovariantDerivative.leviCivitaConnection I M).curvatureTensor x u v w‖ ≤
          K * ‖u‖ * ‖v‖ * ‖w‖ := by
  refine ⟨max (C / 2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
  intro x u v w
  have hbound :=
    (CovariantDerivative.leviCivitaConnection I M).norm_curvatureTensor_le_scalarCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)
      x ⟨(CovariantDerivative.leviCivitaConnection I M).isSymmetric_curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)
        (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) x, hpos t ht x⟩ u v w
  have hscalar' : (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x ≤ C := by
    simpa only [(g t).scalarCurvature_eq_scalarCurvature_leviCivitaConnection rfl] using
      hscalar t ht x
  exact hbound.trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((div_le_div_of_nonneg_right hscalar' (by norm_num : (0 : ℝ) ≤ 2)).trans
        (le_max_left _ _)) (norm_nonneg u)) (norm_nonneg v)) (norm_nonneg w)

end TauCeti
