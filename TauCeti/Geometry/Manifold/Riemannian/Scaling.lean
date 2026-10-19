/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Curvature under constant rescaling of a metric

Let `g` be a Riemannian metric on `M` and `c` a positive constant, and let `c g` be the rescaled
metric `Bundle.ContMDiffRiemannianMetric.rescale` by the constant function `c`. The Koszul formula
is homogeneous of degree one in the metric when `c` is constant, so `g` and `c g` have the same
Levi-Civita connection, and hence the same `(1,3)` curvature tensor and the same Ricci tensor.
Scalar curvature is the metric trace of the Ricci tensor, and the trace for `c g` is `c⁻¹` times
the trace for `g`, so

`Scal(c g) = c⁻¹ Scal(g)`.

Both metrics are installed in turn as the `RiemannianBundle` instance of the tangent bundle of
`M`. Connections and curvature tensors do not depend on the metric, so they are compared directly
on `M`. Mathlib's `CovariantDerivative.leviCivitaConnection` is unconstrained on vector fields which
are not differentiable at the point, so the two Levi-Civita connections are compared on
differentiable fields; this determines the curvature tensor.

## Main results

* `Bundle.ContMDiffRiemannianMetric.isLeviCivitaConnection_rescale_const_iff`: a connection is
  Levi-Civita for `c g` exactly when it is Levi-Civita for `g`.
* `Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_const_apply`: the Levi-Civita
  connections of `c g` and `g` agree on differentiable vector fields.
* `Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_rescale_const`: the curvature
  and Ricci tensors of `c g` and `g` coincide.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_leviCivitaConnection_rescale_const`:
  `Scal(c g) = c⁻¹ Scal(g)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5 (the Koszul formula) and Chapter 7 (curvature conventions).
* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section LeviCivita

variable [IsManifold I 2 M] {n : ℕ∞ω}

/-- Metric compatibility with a `C¹` metric `g`, written with the inner products of `g`. -/
private theorem isMetricCompatible_iff_inner
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) ↔
      ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
        MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
        mvfderiv I (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
          g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x)) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  rw [CovariantDerivative.isMetricCompatible_iff]
  -- The inner product of the installed `RiemannianBundle` is `g.inner` by definition.
  exact ⟨fun h x X Y Z hX hY hZ ↦ h hX hY hZ, fun h x X Y Z hX hY hZ ↦ h hX hY hZ⟩

/-- Multiplying a `C¹` metric by a positive constant does not change which connections are
Levi-Civita connections. -/
theorem isLeviCivitaConnection_rescale_const_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      cov.IsLeviCivitaConnection) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      cov.IsLeviCivitaConnection) := by
  -- Both metric-compatibility conditions are read through the inner products of `g`.
  have key : ∀ ⦃x : M⦄ ⦃Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      mvfderiv I (fun y ↦ c * g.inner y (Y y) (Z y)) x =
        c • mvfderiv I (fun y ↦ g.inner y (Y y) (Z y)) x := by
    intro x Y Z hY hZ
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    -- As above, `g.inner` is by definition the inner product of the installed metric.
    have hg : MDiffAt (fun y ↦ g.inner y (Y y) (Z y)) x :=
      TauCeti.Manifold.mdifferentiableAt_inner hY hZ
    rw [mvfderiv_fun_mul mdifferentiableAt_const hg, mvfderiv_const, smul_zero, add_zero]
  have hm := (isMetricCompatible_iff_inner (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
    hn cov).trans <| (Iff.intro (fun h x X Y Z hX hY hZ ↦ ?_) fun h x X Y Z hX hY hZ ↦ ?_).trans
      (isMetricCompatible_iff_inner g hn cov).symm
  · -- Torsion does not involve the metric.
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨h₁, h₂⟩ := h
    · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn
      exact ⟨hm.1 h₁, h₂⟩
    · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn
      exact ⟨hm.2 h₁, h₂⟩
  · have h := h hX hY hZ
    simp only [rescale_inner, key hY hZ, smul_apply, smul_eq_mul] at h
    exact mul_left_cancel₀ hc.ne' (by linear_combination h)
  · simp only [rescale_inner, key hY hZ, smul_apply, smul_eq_mul, h hX hY hZ]
    ring

/-- The Levi-Civita connections of a `C¹` metric and of a positive constant multiple of it agree
on every vector field differentiable at the point. -/
theorem leviCivitaConnection_rescale_const_apply
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M Y x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M Y x) := by
  have h := (isLeviCivitaConnection_rescale_const_iff g hn hc
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M)).2 (by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact ContinuousLinearMap.ext fun X₀ ↦
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).uniqueness I h hY X₀

end LeviCivita

section Curvature

variable [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)

/-- Multiplying a smooth metric by a positive constant does not change the `(1,3)` curvature
tensor of its Levi-Civita connection. -/
theorem curvatureTensor_leviCivitaConnection_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) :=
  CovariantDerivative.curvatureTensor_congr _
    (fun _ _ hY ↦ leviCivitaConnection_rescale_const_apply g (by simp) hc hY) x

/-- Multiplying a smooth metric by a positive constant does not change the Ricci tensor of its
Levi-Civita connection. -/
theorem ricciTensor_leviCivitaConnection_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) := by
  ext u v
  simp only [CovariantDerivative.ricciTensor_apply,
    curvatureTensor_leviCivitaConnection_rescale_const g hc x]

/-- **Scaling of scalar curvature.** Multiplying a smooth metric by a positive constant `c`
multiplies its scalar curvature by `c⁻¹`. -/
theorem scalarCurvature_leviCivitaConnection_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) =
    c⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) := by
  -- A `g`-orthonormal basis, recorded through the inner products of `g` itself.
  obtain ⟨d, b, hb, hs⟩ : ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (TangentSpace I x)),
      (∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) ∧
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x) =
      ∑ j, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) (b j) (b j) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let b := stdOrthonormalBasis ℝ (TangentSpace I x)
    refine ⟨_, b.toBasis, fun i j ↦ ?_, ?_⟩
    · -- The inner product of the installed metric is `g.inner` by definition.
      rw [b.coe_toBasis]
      exact orthonormal_iff_ite.1 b.orthonormal i j
    · rw [b.coe_toBasis]
      exact CovariantDerivative.scalarCurvature_eq_sum _ x b
  set s := Real.sqrt c
  have hs0 : 0 < s := Real.sqrt_pos.2 hc
  have hss : s⁻¹ * s⁻¹ = c⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hc.le]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
  -- Dividing it by `√c` gives a basis orthonormal for the rescaled metric.
  have hon : Orthonormal ℝ (b.unitsSMul fun _ ↦ Units.mk0 s⁻¹ (inv_ne_zero hs0.ne')) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
    -- The inner product of the installed metric is, by definition, the `inner` field of the
    -- rescaled metric; Mathlib states no unfolding lemma for `RiemannianBundle` inner products.
    change (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).inner x (s⁻¹ • b i)
      (s⁻¹ • b j) = _
    rw [rescale_inner, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul, hb]
    calc c * (s⁻¹ * (s⁻¹ * if i = j then (1 : ℝ) else 0))
        = c * (s⁻¹ * s⁻¹) * if i = j then (1 : ℝ) else 0 := by ring
      _ = if i = j then 1 else 0 := by rw [hss, mul_inv_cancel₀ hc.ne', one_mul]
  rw [CovariantDerivative.scalarCurvature_eq_sum _ x ((b.unitsSMul _).toOrthonormalBasis hon),
    ricciTensor_leviCivitaConnection_rescale_const g hc x, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Module.Basis.coe_toOrthonormalBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Units.val_mk0]
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, hss]

end Curvature

end Bundle.ContMDiffRiemannianMetric
