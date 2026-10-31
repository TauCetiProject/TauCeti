/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Bootstrap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smoothness of Jacobi fields

On a smooth Riemannian manifold, every `C²` Jacobi field is smooth, as is its
covariant derivative. These statements concern the actual tangent-bundle lifts of
sections along the geodesic. They hold within the parameter set, including the
endpoints of nondegenerate closed intervals, and imply ordinary smoothness at
interior parameters.

The geodesic and its velocity are smooth. The Jacobi equation therefore makes the
second covariant derivative as regular as the field itself. Solving the fixed-chart
covariant derivative formula for the ordinary derivative upgrades the field and its
first covariant derivative together. No completeness or extension beyond the
parameter interval is needed.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 10.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ}

/-- The simultaneous finite-order bootstrap for a Jacobi field and its first derivative. -/
private theorem IsJacobiFieldOn.contMDiffOn_nat_pair (h : IsJacobiFieldOn I γ J s) (n : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
        (fun r ↦ TotalSpace.mk' E (γ r) (J r)) s ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
        (fun r ↦ TotalSpace.mk' E (γ r)
          (alongCurveWithin (leviCivitaConnection I M) γ J s r)) s := by
  induction n with
  | zero => exact ⟨h.contMDiffOn.of_le (by norm_num), h.contMDiffOn_alongCurveWithin⟩
  | succ n ih =>
    let cov := leviCivitaConnection I M
    have hn_le_infty : (n + 1 : ℕ) ≤ (∞ : ℕ∞ω) := by simp
    have hγ := h.isGeodesicCurveOn.contMDiffOn_infty
    have hvel := h.isGeodesicCurveOn.contMDiffOn_curveVelocityLiftWithin_infty
    -- Cache the iterated hom-fibre instances to keep typeclass search within its budget.
    let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
    let _ : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ inferInstance
    let _ : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ inferInstance
    let _ : ∀ x : M, NormedAddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ inferInstance
    let _ : ∀ x : M, NormedSpace ℝ
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ inferInstance
    let _ : ∀ x : M, AddCommMonoid
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ (inferInstance : NormedAddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)).toAddCommMonoid
    have hR : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] E))
        (n + 1 : ℕ) (fun r ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
          (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
            TangentSpace I x →L[ℝ] TangentSpace I x) (γ r)
          (cov.curvatureTensorCLM (V := fun x : M ↦ TangentSpace I x)
            (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x)))
            (γ r))) s :=
      ((contMDiff_curvatureTensorCLM (F := E)
        (V := fun x : M ↦ TangentSpace I x)
        (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x)))
        cov).comp_contMDiffOn hγ).of_le hn_le_infty
    -- Evaluate the smooth curvature tensor on the three section lifts.
    have hvel' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
        (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ s r)) s := by
      simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ s)] using
        hvel.of_le hn_le_infty
    have hcurv := ((hR.clm_bundle_apply ih.1).clm_bundle_apply hvel').clm_bundle_apply hvel'
    have hDDJ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
        (fun r ↦ TotalSpace.mk' E (γ r)
          (alongCurveWithin cov γ (alongCurveWithin cov γ J s) s r)) s := by
      refine (contMDiffOn_const (c := (-1 : ℝ))).smul_totalSpace hcurv |>.congr ?_
      intro r hr
      simp only [curvatureTensorCLM_apply, neg_one_smul]
      exact congrArg (TotalSpace.mk' E (γ r)) (h.alongCurveWithin_alongCurveWithin_eq hr)
    -- Both first-order equations now have right-hand sides of class C^(n + 1).
    have hcov (t : ℝ) (_ht : t ∈ s) :
        ContMDiffCovariantDerivativeOn E (n + 1 : ℕ) cov.toFun
          (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
      contMDiffCovariantDerivativeOn_leviCivitaConnection
        (m := ∞) (k := ∞) (trivializationAt E (TangentSpace I) (γ t)).open_baseSet
        (by simp) (by simp)
    have hγ' : ContMDiffOn 𝓘(ℝ, ℝ) I (n + 1 + 1 : ℕ) γ s := hγ.of_le (by simp)
    exact ⟨contMDiffOn_succ_of_alongCurveWithin cov γ J (by omega) hcov h.uniqueDiffOn
        hγ' ih.1 ih.2,
      contMDiffOn_succ_of_alongCurveWithin cov γ (alongCurveWithin cov γ J s)
        (by omega) hcov h.uniqueDiffOn hγ' ih.2 hDDJ⟩

/-- A `C²` Jacobi field along a geodesic of a smooth metric is smooth within its
parameter set, including at closed interval endpoints. -/
theorem IsJacobiFieldOn.contMDiffOn_infty (h : IsJacobiFieldOn I γ J s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r ↦ TotalSpace.mk' E (γ r) (J r)) s :=
  _root_.contMDiffOn_infty.2 fun n ↦
    (h.contMDiffOn_nat_pair n).1.of_le (by exact_mod_cast Nat.le_succ n)

/-- The covariant derivative of a Jacobi field for a smooth metric has a smooth
lift to the tangent bundle within the parameter set. -/
theorem IsJacobiFieldOn.contMDiffOn_alongCurveWithin_infty (h : IsJacobiFieldOn I γ J s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ J s r)) s :=
  _root_.contMDiffOn_infty.2 fun n ↦
    (h.contMDiffOn_nat_pair n).2.of_le (by exact_mod_cast Nat.le_succ n)

/-- A Jacobi field for a smooth metric is smooth at each interior parameter. -/
theorem IsJacobiFieldOn.contMDiffAt_infty (h : IsJacobiFieldOn I γ J s) {t : ℝ}
    (ht : s ∈ 𝓝 t) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun r ↦ TotalSpace.mk' E (γ r) (J r)) t :=
  h.contMDiffOn_infty.contMDiffAt ht

end TauCeti.Manifold
