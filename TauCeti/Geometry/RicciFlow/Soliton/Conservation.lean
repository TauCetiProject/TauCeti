/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Soliton.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Bochner.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormSq
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Conservation and normalization for gradient Ricci solitons

The equation `Ric + Hess f = c g` implies `dR = 2 Ric(·, grad f)`. Consequently Hamilton's
quantity `R + |grad f|² - 2 c f` is constant on each connected component. On a preconnected
carrier, a smooth potential with nonzero `c` admits one global constant shift giving the
normalization `R + |grad f|² = 2 c f`.

The identities hold in every finite dimension, with no completeness or curvature-sign premise.

## References

* P. Topping, *Lectures on the Ricci Flow*, §1.2.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "∇" => leviCivitaConnection I M

namespace SatisfiesGradientRicciSolitonEquation

variable {f : M → ℝ} {c : ℝ} (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f c)

include hsol

/-- Differentiating a soliton equation identifies the third derivative of the potential with
minus the covariant derivative of Ricci curvature. -/
theorem inner_secondCovariantDerivative_mgradient (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M) (u v w : TangentSpace I x) :
    ⟪∇.secondCovariantDerivative ∇ (mgradient I f) x u v, w⟫_ℝ =
      -∇.derivRicciTensor x v w u := by
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ w
  have hVd : MDiffAt (T% V) x := hV.mdifferentiable (by simp) x
  have hWd : MDiffAt (T% W) x := hW.mdifferentiable (by simp) x
  have hs := satisfiesGradientRicciSolitonEquation_iff.mp hsol
  have hfun : (fun y ↦ hessian I f y (V y) (W y)) =
      fun y ↦ c * inner ℝ (V y) (W y) - ∇.ricciTensor y (V y) (W y) := by
    funext y
    linarith [hs y (V y) (W y)]
  have hscale : mvfderiv I (fun y ↦ c * inner ℝ (V y) (W y)) x =
      c • mvfderiv I (fun y ↦ inner ℝ (V y) (W y)) x :=
    TauCeti.mvfderiv_const_smul_field _ x c
  rw [inner_secondCovariantDerivative_mgradient_eq_mvfderiv_hessian hf hV hWd,
    ∇.derivRicciTensor_apply hVd hWd, hfun,
    mvfderiv_fun_sub (g := fun y ↦ c * inner ℝ (V y) (W y))
      (g' := fun y ↦ ∇.ricciTensor y (V y) (W y))
      (mdifferentiableAt_const.mul (mdifferentiableAt_inner hVd hWd))
      (∇.mdifferentiableAt_ricciTensor_apply hVd hWd), hscale]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  have hm := (isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
    (FiberBundle.extend E u) hVd hWd
  simp only [FiberBundle.extend_apply_self] at hm
  rw [hm]
  linarith [hs x (∇ V x u) (W x), hs x (V x) (∇ W x u)]

/-- The scalar curvature differential of a smooth gradient Ricci soliton is
`dR(v) = 2 Ric(v, grad f)`. -/
theorem mvfderiv_scalarCurvature (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v : TangentSpace I x) :
    mvfderiv I ∇.scalarCurvature x v = 2 * ∇.ricciTensor x v (mgradient I f x) := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hmetric := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hB := hmetric.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature
    (torsion_leviCivitaConnection_eq_zero I) x b v
  have hG := sum_inner_secondCovariantDerivative_mgradient_self hf x b v
  simp_rw [hsol.inner_secondCovariantDerivative_mgradient hf, Finset.sum_neg_distrib] at hG
  have hfun : laplaceBeltrami I f =
      fun y ↦ (Module.finrank ℝ E : ℝ) * c - ∇.scalarCurvature y := by
    funext y
    linarith [hsol.scalarCurvature_add_laplaceBeltrami y]
  rw [hfun, mvfderiv_fun_sub mdifferentiableAt_const
    ((∇.contMDiff_scalarCurvature (n := ⊤)).mdifferentiableAt (by simp))] at hG
  simp only [mvfderiv_const, zero_sub, neg_apply] at hG
  linarith

/-- Hamilton's scalar quantity `R + |grad f|² - 2cf` has zero differential. -/
theorem mvfderiv_hamilton (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ ∇.scalarCurvature y + ‖mgradient I f y‖ ^ 2 - 2 * c * f y)
      x v = 0 := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hdnorm : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ‖mgradient I f y‖ ^ 2) x :=
    (contMDiff_norm_sq_mgradient (n := ∞) (by simpa using hf)).mdifferentiableAt (by simp)
  have hdscale : mvfderiv I (fun y ↦ 2 * c * f y) x =
      (2 * c) • mvfderiv I f x := by
    exact TauCeti.mvfderiv_const_smul_field f x (2 * c)
  have hRdiff : MDiffAt ∇.scalarCurvature x :=
    (∇.contMDiff_scalarCurvature (n := ⊤)).mdifferentiableAt (by simp)
  have hsum : MDiffAt (fun y ↦ ∇.scalarCurvature y + ‖mgradient I f y‖ ^ 2) x :=
    hRdiff.add hdnorm
  have hscale : MDiffAt (fun y ↦ 2 * c * f y) x :=
    mdifferentiableAt_const.mul (hf.mdifferentiableAt (by simp))
  rw [mvfderiv_fun_sub (g := fun y ↦ ∇.scalarCurvature y + ‖mgradient I f y‖ ^ 2)
    (g' := fun y ↦ 2 * c * f y) hsum hscale,
    mvfderiv_fun_add (g := ∇.scalarCurvature) (g' := fun y ↦ ‖mgradient I f y‖ ^ 2)
      hRdiff hdnorm, hdscale]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul]
  have hh := satisfiesGradientRicciSolitonEquation_iff.mp hsol x v (mgradient I f x)
  simp only [I.hessian_eq_inner_leviCivitaConnection_mgradient, inner_mgradient_right] at hh
  rw [hsol.mvfderiv_scalarCurvature hf,
    mvfderiv_norm_sq_mgradient ((hf x).of_le (by simp)) v]
  simp only [inner_mgradient_right]
  nlinarith [hh]

/-- Hamilton's scalar quantity is constant on a preconnected gradient Ricci soliton. -/
theorem hamilton_eq [PreconnectedSpace M]
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x p : M) :
    ∇.scalarCurvature x + ‖mgradient I f x‖ ^ 2 - 2 * c * f x =
      ∇.scalarCurvature p + ‖mgradient I f p‖ ^ 2 - 2 * c * f p := by
  have : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  apply MDifferentiable.apply_eq_of_mfderiv_eq_zero
    (((∇.contMDiff_scalarCurvature.add
      (contMDiff_norm_sq_mgradient (n := ∞) (by simpa using hf))).sub
        (contMDiff_const.mul hf)).mdifferentiable (by simp))
  intro y
  apply TauCeti.mvfderiv_eq_zero_iff.mp
  ext v
  exact hsol.mvfderiv_hamilton hf y v

/-- A smooth soliton potential on a preconnected carrier with nonzero soliton constant admits
a global constant shift with `R + |grad f|² = 2 c f`. The equation and gradient are preserved. -/
theorem exists_add_const_normalized [PreconnectedSpace M]
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : c ≠ 0) :
    ∃ a : ℝ, SatisfiesGradientRicciSolitonEquation (I := I) (fun x ↦ f x + a) c ∧
      ∀ x, ∇.scalarCurvature x + ‖mgradient I (fun y ↦ f y + a) x‖ ^ 2 =
        2 * c * (f x + a) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl h =>
    exact ⟨0, (satisfiesGradientRicciSolitonEquation_add_const_iff f 0 c).mpr hsol,
      fun x ↦ (h.false x).elim⟩
  | inr h =>
    let p : M := Classical.choice h
    let a := (∇.scalarCurvature p + ‖mgradient I f p‖ ^ 2 - 2 * c * f p) / (2 * c)
    refine ⟨a, (satisfiesGradientRicciSolitonEquation_add_const_iff f a c).mpr hsol, ?_⟩
    intro x
    rw [mgradient_add_const]
    have hham := hsol.hamilton_eq hf x p
    have ha : 2 * c * a =
        ∇.scalarCurvature p + ‖mgradient I f p‖ ^ 2 - 2 * c * f p := by
      dsimp only [a]
      exact mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hc)
    linarith

end SatisfiesGradientRicciSolitonEquation

end TauCeti.Manifold
