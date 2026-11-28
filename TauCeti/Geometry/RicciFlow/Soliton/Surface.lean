/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Soliton.Conservation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.Exp
import TauCeti.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Conservation laws and a Ricci bound for surface gradient solitons

For a smooth potential satisfying `Ric + Hess f = ρg` on a Riemannian surface, we prove
`dR = R df` and show that the weighted scalar curvature `R exp(-f)` is constant on each
connected component. The Hamilton conservation law comes from
`SatisfiesGradientRicciSolitonEquation.hamilton_eq` in `Soliton/Conservation.lean`. If
`ρ > 0` and the scalar curvature is positive at one point of a preconnected surface, these
laws give a uniform positive Ricci lower bound.

This supplies the curvature bound used in the compactness argument for two-dimensional
shrinking models. Compactness and classification require further arguments. All statements
here concern smooth potentials.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 9.50.
  This file supplies the curvature-bound step of that result.
* Public formalizations:
  [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "∇" => leviCivitaConnection I M

/-- The soliton equation on a surface makes the Hessian pure trace. -/
theorem hessian_eq_of_surface_soliton (hn : Module.finrank ℝ E = 2) {f : M → ℝ} {ρ : ℝ}
    {x : M} (hsol : ∀ u v : TangentSpace I x,
      ∇.ricciTensor x u v + hessian I f x u v = ρ * inner ℝ u v)
    (u v : TangentSpace I x) :
    hessian I f x u v = (ρ - ∇.scalarCurvature x / 2) * inner ℝ u v := by
  have h := hsol u v
  rw [∇.ricciTensor_eq_scalarCurvature_div_two_smul (x := x)
    (isMetricCompatible_leviCivitaConnection I) (by rw [TauCeti.finrank_tangentSpace, hn])] at h
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul] at h
  linarith

/-- The scalar curvature of a smooth surface gradient soliton satisfies `dR = R df`. -/
theorem mvfderiv_scalarCurvature_of_surface_soliton (hn : Module.finrank ℝ E = 2)
    {f : M → ℝ} {ρ : ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f ρ)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I ∇.scalarCurvature x v = ∇.scalarCurvature x * mvfderiv I f x v := by
  rw [hsol.mvfderiv_scalarCurvature hf,
    ∇.ricciTensor_eq_scalarCurvature_div_two_smul (x := x)
      (isMetricCompatible_leviCivitaConnection I) (by rw [TauCeti.finrank_tangentSpace, hn])]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, inner_mgradient_right]
  ring

/-- The weighted scalar curvature `R exp(-f)` has zero differential on a surface soliton. -/
theorem mvfderiv_weighted_scalar_of_surface_soliton (hn : Module.finrank ℝ E = 2)
    {f : M → ℝ} {ρ : ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f ρ)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ∇.scalarCurvature y * Real.exp (-f y)) x v = 0 := by
  have hdexp : mvfderiv I (fun y ↦ Real.exp (-f y)) x =
      -(Real.exp (-f x)) • mvfderiv I f x := by
    rw [TauCeti.mvfderiv_exp (g := fun y ↦ -f y) (hf.neg.mdifferentiableAt (by simp)),
      mvfderiv_fun_neg, smul_neg, neg_smul]
  have hRdiff : MDiffAt ∇.scalarCurvature x :=
    (∇.contMDiff_scalarCurvature (n := ⊤)).mdifferentiableAt (by simp)
  have hexdiff : MDiffAt (fun y ↦ Real.exp (-f y)) x :=
    (Real.contDiff_exp.contMDiff.comp hf.neg).mdifferentiableAt (by simp)
  rw [mvfderiv_fun_mul (f := ∇.scalarCurvature) (g := fun y ↦ Real.exp (-f y))
    hRdiff hexdiff, hdexp]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [mvfderiv_scalarCurvature_of_surface_soliton hn hf hsol]
  ring

/-- On a preconnected surface soliton, `R exp(-f)` has the same value at any two points. -/
theorem weighted_scalar_eq_of_surface_soliton [PreconnectedSpace M]
    (hn : Module.finrank ℝ E = 2) {f : M → ℝ} {ρ : ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f ρ)
    (x p : M) :
    ∇.scalarCurvature x * Real.exp (-f x) =
      ∇.scalarCurvature p * Real.exp (-f p) := by
  apply MDifferentiable.apply_eq_of_mfderiv_eq_zero
    ((∇.contMDiff_scalarCurvature.mul (Real.contDiff_exp.contMDiff.comp hf.neg)).mdifferentiable
      (by simp))
  intro y
  apply TauCeti.mvfderiv_eq_zero_iff.mp
  ext v
  exact mvfderiv_weighted_scalar_of_surface_soliton hn hf hsol y v

/-- A shrinking surface gradient soliton with positive scalar curvature at one point has a
uniform positive Ricci lower bound. Completeness and a global curvature-sign assumption are
not required. -/
theorem exists_pos_ricci_lower_bound_of_surface_soliton [PreconnectedSpace M]
    (hn : Module.finrank ℝ E = 2) {f : M → ℝ} {ρ : ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f ρ)
    (hρ : 0 < ρ) (p : M) (hp : 0 < ∇.scalarCurvature p) :
    ∃ c > 0, ∀ x (v : TangentSpace I x), c * ‖v‖ ^ 2 ≤ ∇.ricciTensor x v v := by
  let A := ∇.scalarCurvature p * Real.exp (-f p)
  let C := ∇.scalarCurvature p + ‖mgradient I f p‖ ^ 2 - 2 * ρ * f p
  have hA : 0 < A := mul_pos hp (Real.exp_pos _)
  have hweighted (x : M) : ∇.scalarCurvature x * Real.exp (-f x) = A :=
    weighted_scalar_eq_of_surface_soliton hn hf hsol x p
  have hhamilton (x : M) :
      ∇.scalarCurvature x + ‖mgradient I f x‖ ^ 2 - 2 * ρ * f x = C :=
    hsol.hamilton_eq hf x p
  have hRpos (x : M) : 0 < ∇.scalarCurvature x := by
    have hexp := Real.exp_pos (-f x)
    have heq := hweighted x
    nlinarith
  have hf_lower (x : M) : -C / (2 * ρ) ≤ f x := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ρ)).mpr
    have h := hhamilton x
    nlinarith [hRpos x, sq_nonneg ‖mgradient I f x‖]
  have hR (x : M) : ∇.scalarCurvature x = A * Real.exp (f x) := by
    rw [← hweighted x]
    simp only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hR_lower (x : M) : A * Real.exp (-C / (2 * ρ)) ≤ ∇.scalarCurvature x := by
    rw [hR x]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hf_lower x)) hA.le
  refine ⟨A * Real.exp (-C / (2 * ρ)) / 2, by positivity, ?_⟩
  intro x v
  rw [∇.ricciTensor_eq_scalarCurvature_div_two_smul (x := x)
    (isMetricCompatible_leviCivitaConnection I) (by rw [TauCeti.finrank_tangentSpace, hn])]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
  exact mul_le_mul_of_nonneg_right (by linarith [hR_lower x]) (sq_nonneg _)

end TauCeti.Manifold
