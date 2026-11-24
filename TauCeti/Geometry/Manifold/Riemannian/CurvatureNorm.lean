/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Norm
public import TauCeti.Geometry.Manifold.Riemannian.Scaling

/-!
# Scaling the full Riemann curvature norm

The full Riemann curvature norm of a smooth metric satisfies `|Rm(c g)| = c⁻¹ |Rm(g)|` for
positive constants `c`. Consequently, any compact set admits arbitrarily large constant metric
rescalings whose full curvature norm is below a prescribed positive threshold. On a compact
manifold this gives a global curvature normalization.

The norm and rescaling arguments are adapted from the formalizations in
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle
open scoped ContDiff Manifold
noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The full Riemann curvature norm of a smooth metric, computed using its Levi-Civita
connection. -/
def riemannCurvatureNorm (x : M) : ℝ :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).riemannCurvatureNorm x

/-- The curvature norm of a metric is the full norm of its Levi-Civita curvature tensor. -/
theorem riemannCurvatureNorm_def (x : M) :
    g.riemannCurvatureNorm x =
      letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).riemannCurvatureNorm x := by
  rfl

/-- The full Riemann curvature norm of a smooth metric is nonnegative. -/
theorem riemannCurvatureNorm_nonneg (x : M) : 0 ≤ g.riemannCurvatureNorm x := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact CovariantDerivative.riemannCurvatureNorm_nonneg _ x

/-- The squared curvature norm of a metric is the sum of the squared Riemann coefficients in
any orthonormal basis for that metric. -/
theorem riemannCurvatureNorm_sq_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I x)) :
    g.riemannCurvatureNorm x ^ 2 =
      letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
      ∑ i, ∑ j, ∑ k, ∑ l,
        ((CovariantDerivative.leviCivitaConnection I M).riemannCurvatureTensor x
          (b i) (b j) (b k) (b l)) ^ 2 := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact CovariantDerivative.riemannCurvatureNorm_sq_eq_sum _ x b

/-- Under constant metric scaling, each orthonormal coefficient is divided by the scale, so
the squared curvature norm is divided by its square. -/
private theorem riemannCurvatureNorm_sq_rescale_const {c : ℝ} (hc : 0 < c) (x : M) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).riemannCurvatureNorm x ^ 2 =
      c⁻¹ ^ 2 * g.riemannCurvatureNorm x ^ 2 := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  obtain ⟨b', hb'⟩ := g.exists_orthonormalBasis_rescale contMDiff_const (fun _ ↦ hc) b
  let g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  let R (u v w z : TangentSpace I x) :=
    (CovariantDerivative.leviCivitaConnection I M).riemannCurvatureTensor x u v w z
  let R' (u v w z : TangentSpace I x) :=
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g'.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).riemannCurvatureTensor x u v w z
  have hR (u v w z : TangentSpace I x) : R' u v w z = c * R u v w z :=
    g.riemannCurvatureTensor_leviCivitaConnection_rescale_const hc x u v w z
  have hscale : c * (Real.sqrt c)⁻¹ ^ 4 = c⁻¹ := by
    have hs : Real.sqrt c ^ 4 = c ^ 2 := by
      calc
        _ = (Real.sqrt c ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hc.le]
    rw [inv_pow, hs]
    field_simp
  have hcoeff i j k l : R' (b' i) (b' j) (b' k) (b' l) =
      c⁻¹ * R (b i) (b j) (b k) (b l) := by
    rw [hR]
    calc
      _ = (c * (Real.sqrt c)⁻¹ ^ 4) * R (b i) (b j) (b k) (b l) := by
        simp only [hb', R, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [hscale]
  have hsum : g'.riemannCurvatureNorm x ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (R' (b' i) (b' j) (b' k) (b' l)) ^ 2 :=
    g'.riemannCurvatureNorm_sq_eq_sum x b'
  simp_rw [hcoeff, mul_pow, ← Finset.mul_sum] at hsum
  rw [hsum, g.riemannCurvatureNorm_sq_eq_sum x b]

/-- Multiplying a metric by `c > 0` divides its full Riemann curvature norm by `c`. -/
theorem riemannCurvatureNorm_rescale_const {c : ℝ} (hc : 0 < c) (x : M) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).riemannCurvatureNorm x =
      c⁻¹ * g.riemannCurvatureNorm x := by
  apply (sq_eq_sq₀
    ((g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).riemannCurvatureNorm_nonneg x)
    (mul_nonneg (inv_nonneg.mpr hc.le) (g.riemannCurvatureNorm_nonneg x))).mp
  rw [g.riemannCurvatureNorm_sq_rescale_const hc, mul_pow]

/-- The full Riemann curvature norm of a smooth metric has a uniform positive bound on every
compact set. -/
theorem exists_riemannCurvatureNorm_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, g.riemannCurvatureNorm x ≤ C := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  exact CovariantDerivative.exists_riemannCurvatureNorm_le_of_isCompact
    (CovariantDerivative.leviCivitaConnection I M) hK

/-- On a compact set, arbitrarily large constant metric rescalings make the full Riemann
curvature norm at most any prescribed positive threshold. -/
theorem exists_rescale_riemannCurvatureNorm_le_of_isCompact {K : Set M}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ (c : ℝ) (hc : 0 < c), A < c ∧
      ∀ x ∈ K,
        (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).riemannCurvatureNorm x ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := g.exists_riemannCurvatureNorm_le_of_isCompact hK
  obtain ⟨c, hCc⟩ := exists_gt (max A (C / ε))
  have hpos : 0 < c := (div_pos hC hε).trans ((le_max_right A (C / ε)).trans_lt hCc)
  refine ⟨c, hpos, (le_max_left A (C / ε)).trans_lt hCc, ?_⟩
  intro x hx
  rw [g.riemannCurvatureNorm_rescale_const hpos]
  calc
    c⁻¹ * g.riemannCurvatureNorm x ≤ c⁻¹ * C :=
      mul_le_mul_of_nonneg_left (hbound x hx) (inv_nonneg.mpr hpos.le)
    _ ≤ ε := by
      rw [← div_eq_inv_mul, div_le_iff₀ hpos]
      exact (by simpa only [mul_comm] using
        ((div_lt_iff₀ hε).mp ((le_max_right A (C / ε)).trans_lt hCc)).le)

/-- On a compact manifold, arbitrarily large constant metric rescalings give any prescribed
positive global bound on the full Riemann curvature norm. -/
theorem exists_rescale_riemannCurvatureNorm_le [CompactSpace M] {ε : ℝ}
    (hε : 0 < ε) (A : ℝ) :
    ∃ (c : ℝ) (hc : 0 < c), A < c ∧
      ∀ x, (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).riemannCurvatureNorm x ≤ ε := by
  obtain ⟨c, hc, hAc, hbound⟩ :=
    g.exists_rescale_riemannCurvatureNorm_le_of_isCompact isCompact_univ hε A
  exact ⟨c, hc, hAc, fun x ↦ hbound x (Set.mem_univ x)⟩

end Bundle.ContMDiffRiemannianMetric
