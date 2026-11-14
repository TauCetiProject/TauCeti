/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Exponential decay of the derivatives at a nondegenerate end

Let `(V, ω)` be a symplectic vector space, `H` a `1`-periodic Hamiltonian, and `u` a finite-energy
solution of the Floer equation `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0` on a half-cylinder `s > a` whose
loops converge uniformly to a nondegenerate `1`-periodic orbit `x`. By
`TauCeti.Geometry.Symplectic.Floer.ExponentialDecay` the energy of `[s, ∞) × [0, 1]` decays
exponentially and the loops converge to `x` exponentially in `C⁰`. This file proves exponential
convergence in `C¹`
(`TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp`):
eventually `‖du(s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C e^{-κ s}`. This is the form in which the
pre-gluing error estimate `TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`
takes the asymptotics of the two broken cylinders.

**The derivative solves a linear equation.** For the cylindrical perturbation `H_t dt` the
equation does not depend on `s`, so differentiating it in `s` shows that `v = ∂ₛu` solves the
linear Cauchy–Riemann equation `∂ₜv = J ∂ₛv + B v`, with `B = ∂ₛJ + dX_{H_t}(u)`
(`TauCeti.SymplecticForm.fderiv_fderiv_apply_snd_eq_of_floer`). Here `J` is the almost complex
structure along `u`, as a function of the domain point.

**Mean-value inequality.** For a linear equation the squared norm satisfies
`Δ ‖v‖² ≥ -K ‖v‖²`, with `K` depending only on bounds for `J`, `B` and their first derivatives
(`TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`). Near the orbit these coefficients are
bounded, so on discs of a fixed small radius `r` the value `‖v‖²` at the centre is at most
`5 / (π r²)` times its integral over the disc
(`TauCeti.pi_mul_sq_mul_norm_sq_le_five_mul_setIntegral_ball_of_fderiv_I_eq`). Unlike the
mean-value inequality for the nonlinear equation, this needs no smallness of the energy.

**From energy to pointwise decay.** A disc of radius at most `1 / 2` centred in `[s, ∞) × [0, 1]`
lies over `[s - 1 / 2, ∞)`, and by periodicity in `t` the integral of `‖v‖²` over it is at most
twice its integral over `[s - 1 / 2, ∞) × [0, 1]`
(`Function.Periodic.setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioo`), which the energy
controls. So `‖v(s, t)‖² ≤ D e^{-κ s}`. Finally
`∂ₜu - X_{H_t}(x) = J ∂ₛu + X_{H_t}(u) - X_{H_t}(x)`, and the last difference is at most a
Lipschitz constant times `‖u - x‖`.

The almost complex structures enter through their values along `u`, as in
`TauCeti.Geometry.Symplectic.Floer.ExponentialDecay`; bounds on their first two derivatives as
functions of the domain point are hypotheses. No Sobolev completion or optimal rate is asserted.

## Main results

* `TauCeti.SymplecticForm.fderiv_fderiv_apply_snd_eq_of_floer`: `∂ₛu` solves the linear equation
  `∂ₜv = J ∂ₛv + B v`.
* `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp`:
  exponential convergence in `C¹` to a nondegenerate orbit.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the exponential decay of Floer trajectories at nondegenerate
  orbits.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the mean-value inequality).
-/

public section

open Set Filter Topology MeasureTheory Function Metric Real
open scoped ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {a c M : ℝ}

/-- The Floer equation `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0`, solved for `∂ₜu`. -/
private theorem fderiv_apply_snd_eq_of_floer {z : ℝ × ℝ}
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ u z (0, 1) = J z (fderiv ℝ u z (1, 0)) + ω.hamiltonianVectorField (H z.2) (u z) := by
  have h := (ω.isComplexLinearMap_perturbedFDeriv_iff (J z) _ _ u z).1 hfloer
  simp only [stdComplexLineReal_eq, stdComplexLineImag_eq, hamiltonianVectorField_const,
    Pi.zero_apply, sub_zero] at h
  have h' := congrArg (J z) h
  rw [map_add, AlmostComplexStructure.apply_apply, map_zero, add_neg_eq_zero] at h'
  rw [h']
  abel

/-- **The `s`-derivative of a Floer solution solves a linear Cauchy–Riemann equation.** On an open
set where `u` is a `C²` solution of `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0` and `J` is a `C¹` family, the
derivative `v = ∂ₛu` satisfies `∂ₜv = J ∂ₛv + B v` with
`B z = ∂ₛJ z + dX_{H_t}(u z)`, the second term being the derivative in the target of the
Hamiltonian vector field `X(t, y) = X_{H_t}(y)`. -/
theorem fderiv_fderiv_apply_snd_eq_of_floer (hH : ContDiff ℝ 2 (uncurry H))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hJ : ContDiffOn ℝ 1 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) U)
    (hfloer : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {z : ℝ × ℝ} (hz : z ∈ U) :
    fderiv ℝ (fun w ↦ fderiv ℝ u w (1, 0)) z (0, 1) =
      J z (fderiv ℝ (fun w ↦ fderiv ℝ u w (1, 0)) z (1, 0)) +
        (fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z (1, 0) +
          (fderiv ℝ (fun p : ℝ × V ↦ ω.hamiltonianVectorField (H p.1) p.2) (z.2, u z)).comp
            (ContinuousLinearMap.inr ℝ ℝ V)) (fderiv ℝ u z (1, 0)) := by
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap with hJc_def
  set X : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2 with hX_def
  have hX : ContDiff ℝ 1 X := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have huz : ContDiffAt ℝ 2 u z := hu.contDiffAt (hU.mem_nhds hz)
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (huz.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hud : DifferentiableAt ℝ u z := huz.differentiableAt (by norm_num)
  have hJz : DifferentiableAt ℝ Jc z :=
    (hJ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ (w.2, u w)) z :=
    differentiableAt_snd.prodMk hud
  have hXg : DifferentiableAt ℝ X (z.2, u z) := (hX.differentiable (by norm_num)).differentiableAt
  -- Near `z` the Floer equation reads `∂ₜu = J ∂ₛu + X(t, u)`.
  have heq : (fun w ↦ fderiv ℝ u w (0, 1)) =ᶠ[𝓝 z]
      fun w ↦ Jc w (fderiv ℝ u w (1, 0)) + X (w.2, u w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa [hJc_def, hX_def] using fderiv_apply_snd_eq_of_floer (hfloer w hw)
  -- Differentiate in the direction `(1, 0)`, using the symmetry of the second derivative of `u`.
  have hvs : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w (1, 0)) z :=
    hDu.clm_apply (differentiableAt_const _)
  have hsymm : fderiv ℝ (fderiv ℝ u) z (0, 1) (1, 0) = fderiv ℝ (fderiv ℝ u) z (1, 0) (0, 1) :=
    huz.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) _ _
  have hcomp : fderiv ℝ (fun w : ℝ × ℝ ↦ X (w.2, u w)) z (1, 0) =
      fderiv ℝ X (z.2, u z) (0, fderiv ℝ u z (1, 0)) := by
    rw [show (fun w : ℝ × ℝ ↦ X (w.2, u w)) = X ∘ fun w ↦ (w.2, u w) from rfl,
      fderiv_comp z hXg hg, ContinuousLinearMap.comp_apply,
      DifferentiableAt.fderiv_prodMk differentiableAt_snd hud]
    simp [fderiv_snd]
  have h := congrArg (fun L : ℝ × ℝ →L[ℝ] V ↦ L (1, 0)) heq.fderiv_eq
  have hXg' : DifferentiableAt ℝ (X ∘ fun w : ℝ × ℝ ↦ (w.2, u w)) z := hXg.comp z hg
  rw [fderiv_clm_apply_const_apply hDu, fderiv_fun_add (f := fun w ↦ Jc w (fderiv ℝ u w (1, 0)))
    (g := fun w ↦ X (w.2, u w)) (hJz.clm_apply hvs) hXg',
    fderiv_clm_apply hJz hvs] at h
  rw [fderiv_clm_apply_const_apply hDu, hsymm, h, add_apply, hcomp]
  simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_clm_apply_const_apply hDu,
    LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply, Jc]
  abel

/-- The coefficient `B z = ∂ₛJ z + dX_{H_t}(u z)` of the linear equation `∂ₜv = J ∂ₛv + B v`
solved by `v = ∂ₛu` (`TauCeti.SymplecticForm.fderiv_fderiv_apply_snd_eq_of_floer`). -/
private noncomputable def floerCoeff (ω : SymplecticForm V) (H : ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (J : ℝ × ℝ → AlmostComplexStructure V) (z : ℝ × ℝ) : V →L[ℝ] V :=
  fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z (1, 0) +
    (fderiv ℝ (fun p : ℝ × V ↦ ω.hamiltonianVectorField (H p.1) p.2) (z.2, u z)).comp
      (ContinuousLinearMap.inr ℝ ℝ V)

private theorem floerCoeff_eq : floerCoeff ω H u J = fun z ↦
    fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z (1, 0) +
      (fderiv ℝ (fun p : ℝ × V ↦ ω.hamiltonianVectorField (H p.1) p.2) (z.2, u z)).comp
        (ContinuousLinearMap.inr ℝ ℝ V) :=
  rfl

/-- **The mean-value inequality for `∂ₛu`.** On an open set `U` where `u` is a `C³` Floer solution
for `H_t dt`, with a `C²` family `J`, let `a`, `b`, `β`, `γ` bound `J`, its derivative, the
coefficient `B` of `TauCeti.SymplecticForm.fderiv_fderiv_apply_snd_eq_of_floer` and its
derivative. Then for every disc `ball y r` of the complex coordinate whose closure lies in `U`,
with `K r² ≤ 1` for the constant `K` of
`TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`, `π r² ‖∂ₛu‖²` at the centre is at most
five times the integral of `‖∂ₛu‖²` over the disc. -/
private theorem pi_mul_sq_mul_norm_sq_le_of_floer (hH : ContDiff ℝ 3 (uncurry H))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) U)
    (hfloer : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {r a' b β γ : ℝ}
    (ha : ∀ z ∈ U, ‖(J z).toLinearMap.toContinuousLinearMap‖ ≤ a')
    (hb : ∀ z ∈ U, ‖fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hβ : ∀ z ∈ U, ‖floerCoeff ω H u J z‖ ≤ β)
    (hγ : ∀ z ∈ U, ‖fderiv ℝ (floerCoeff ω H u J) z‖ ≤ γ)
    (hKr : (((b + a' * b + a' * β) ^ 2 + β ^ 2) / 2 + 2 * (a' * γ + γ)) * r ^ 2 ≤ 1)
    (hr : 0 ≤ r) {y : ℂ} (hy : closedBall y r ⊆ Complex.equivRealProdCLM ⁻¹' U) :
    π * r ^ 2 * ‖fderiv ℝ u (Complex.equivRealProdCLM y) (1, 0)‖ ^ 2 ≤
      5 * ∫ w in ball y r, ‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2 := by
  set e : ℂ →L[ℝ] ℝ × ℝ := (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap
  set X : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  set B : ℝ × ℝ → V →L[ℝ] V := floerCoeff ω H u J
  have hX : ContDiff ℝ 2 X := ω.contDiff_hamiltonianVectorField_uncurry (n := 2) hH
  have he : ‖e‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ by
    simpa [e] using Complex.equivRealProd_apply_le' w
  have hball : ball y r ⊆ e ⁻¹' U := ball_subset_closedBall.trans hy
  -- `∂ₛu` is `C²` on `U`, and `B` is `C¹` there.
  have hv : ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ u z (1, 0)) U :=
    (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hBc : ContDiffOn ℝ 1 B U := by
    rw [show B = _ from floerCoeff_eq]
    refine ((hJ.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).add ?_
    exact ((hX.fderiv_right (m := 1) (by norm_num)).comp_contDiffOn
      (contDiffOn_snd.prodMk (hu.of_le (by norm_num)))).clm_comp contDiffOn_const
  have hv' : ContDiffOn ℝ 2 (fun w ↦ fderiv ℝ u (e w) (1, 0)) (e ⁻¹' U) :=
    hv.comp e.contDiff.contDiffOn fun _ h ↦ h
  refine pi_mul_sq_mul_norm_sq_le_five_mul_setIntegral_ball_of_fderiv_I_eq
    (J := Jc ∘ e) (B := B ∘ e) hr (hv'.mono hball) (hv'.continuousOn.mono hy)
    (fun w hw ↦ ((hJ.contDiffAt (hU.mem_nhds (hball hw))).differentiableAt
      (by norm_num)).comp w e.differentiableAt)
    (fun w hw ↦ ((hBc.contDiffAt (hU.mem_nhds (hball hw))).differentiableAt
      (by norm_num)).comp w e.differentiableAt)
    (fun w hw ↦ ?_) (fun w _ v ↦ ?_) (fun w hw ↦ ha _ (hball hw)) (fun w hw ↦ ?_)
    (fun w hw ↦ hβ _ (hball hw)) (fun w hw ↦ ?_) hKr
  · -- The linear equation, read in the complex coordinate.
    have h := fderiv_fderiv_apply_snd_eq_of_floer (hH.of_le (by norm_num)) hU
      (hu.of_le (by norm_num)) (hJ.of_le (by norm_num)) hfloer (hball hw)
    have hcomp : fderiv ℝ (fun w ↦ fderiv ℝ u (e w) (1, 0)) w =
        (fderiv ℝ (fun z ↦ fderiv ℝ u z (1, 0)) (e w)).comp e :=
      Complex.equivRealProdCLM.comp_right_fderiv (f := fun z ↦ fderiv ℝ u z (1, 0))
    have he1 : e 1 = (1, 0) := by simp [e]
    have heI : e Complex.I = (0, 1) := by simp [e]
    rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, he1, heI]
    exact h
  · simp [Jc, AlmostComplexStructure.apply_apply]
  · have hcomp : fderiv ℝ (Jc ∘ e) w = (fderiv ℝ Jc (e w)).comp e :=
      Complex.equivRealProdCLM.comp_right_fderiv (f := Jc)
    rw [hcomp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [hb _ (hball hw), norm_nonneg (fderiv ℝ Jc (e w))])
  · have hcomp : fderiv ℝ (B ∘ e) w = (fderiv ℝ B (e w)).comp e :=
      Complex.equivRealProdCLM.comp_right_fderiv (f := B)
    rw [hcomp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [hγ _ (hball hw), norm_nonneg (fderiv ℝ B (e w))])

omit [FiniteDimensional ℝ V] in
/-- On the half-cylinder `s > a`, where `u` is `1`-periodic in `t`, so is its derivative. -/
private theorem fderiv_mk_add_one (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    {z : ℝ × ℝ} (hz : a < z.1) : fderiv ℝ u (z.1, z.2 + 1) = fderiv ℝ u z := by
  have hev : (fun w : ℝ × ℝ ↦ u (w + (0, 1))) =ᶠ[𝓝 z] u := by
    filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds (show z ∈ Prod.fst ⁻¹' Ioi a
      from hz)] with w hw
    rw [show w + ((0 : ℝ), (1 : ℝ)) = (w.1, w.2 + 1) by ext <;> simp]
    exact hper w.1 hw w.2
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((0 : ℝ), (1 : ℝ))
  rw [hev.fderiv_eq] at h
  rw [show ((z.1, z.2 + 1) : ℝ × ℝ) = z + (0, 1) by ext <;> simp]
  exact h.symm

/-- For uniformly tame `J`, the energy density of a Floer solution dominates `‖∂ₛu‖²`. -/
private theorem norm_sq_fderiv_apply_le_mul_floerEnergyDensity {z : ℝ × ℝ} (hc : 0 < c)
    (hJc : ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v)) (hJM : ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ‖fderiv ℝ u z (1, 0)‖ ^ 2 ≤
      (1 + M ^ 2) / c * ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z := by
  have h := ω.mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity hc.le hJc hJM
    hfloer
  rw [perturbedFDeriv_apply_stdComplexLineReal, hamiltonianVectorField_const, Pi.zero_apply,
    sub_zero, stdComplexLineReal_eq] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [sq_nonneg ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag‖]

/-- **The integral of `‖∂ₛu‖²` over a disc is controlled by the energy of a half-cylinder.** If a
disc of the complex coordinate of radius `r ≤ 1 / 2` lies over `[s, ∞)`, with `s > a`, then the
integral of `‖∂ₛu‖²` over it is at most `2 (1 + M²) / c` times the energy over
`[s, ∞) × [0, 1]`. -/
private theorem ofReal_setIntegral_ball_le_mul_setLIntegral
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {s r : ℝ} {y : ℂ} (hs : a < s) (hr : r ≤ 1 / 2) (hsy : s ≤ y.re - r)
    (hcont : ContinuousOn (fun w ↦ fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0))
      (closedBall y r)) :
    ENNReal.ofReal (∫ w in ball y r, ‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2) ≤
      ENNReal.ofReal (2 * ((1 + M ^ 2) / c)) * ∫⁻ z in Ici s ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  set F : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖fderiv ℝ u z (1, 0)‖ ^ 2)
  -- Cut `F` off at `s = a`, so that it is periodic in `t` on the whole plane.
  set S : Set ℂ := {w | a < w.re}
  set g : ℂ → ℝ≥0∞ := S.indicator fun w ↦ F (Complex.measurableEquivRealProd w)
  have hg : Periodic g Complex.I := fun w ↦ by
    by_cases hw : w ∈ S
    · have hw' : w + Complex.I ∈ S := by simpa [S] using hw
      simp only [g, indicator_of_mem hw', indicator_of_mem hw, F,
        Complex.measurableEquivRealProd_apply, Complex.add_re, Complex.add_im, Complex.I_re,
        Complex.I_im, add_zero]
      rw [fderiv_mk_add_one hper (z := (w.re, w.im)) hw]
    · have hw' : w + Complex.I ∉ S := by simpa [S] using hw
      simp only [g, indicator_of_notMem hw', indicator_of_notMem hw]
  have hint : IntegrableOn (fun w ↦ ‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2)
      (ball y r) :=
    ((hcont.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ by positivity)]
  calc ∫⁻ w in ball y r, F (Complex.measurableEquivRealProd w)
      = ∫⁻ w in ball y r, g w := by
        refine setLIntegral_congr_fun measurableSet_ball fun w hw ↦ ?_
        have h := Complex.abs_re_le_norm (w - y)
        rw [← dist_eq_norm, Complex.sub_re] at h
        have h' := abs_le.1 (h.trans (mem_ball.1 hw).le)
        exact (indicator_of_mem (show w ∈ S from by simp only [S, mem_ofPred_eq]; linarith)
          fun w ↦ F (Complex.measurableEquivRealProd w)).symm
    _ ≤ 2 * ∫⁻ w in Ioo (y.re - r) (y.re + r) ×ℂ Icc 0 1, g w :=
        hg.setLIntegral_ball_le_two_mul_setLIntegral_reProdIm_Ioo y hr
    _ ≤ 2 * ∫⁻ w in Ici s ×ℂ Icc 0 1, g w := by
        gcongr
        exact Complex.reProdIm_subset_iff.2 (prod_mono (fun t ht ↦ hsy.trans ht.1.le) le_rfl)
    _ = 2 * ∫⁻ w in Ici s ×ℂ Icc 0 1, F (Complex.measurableEquivRealProd w) := by
        congr 1
        exact setLIntegral_congr_fun (measurableSet_Ici.reProdIm measurableSet_Icc)
          fun w hw ↦ indicator_of_mem (show w ∈ S from hs.trans_le hw.1)
            fun w ↦ F (Complex.measurableEquivRealProd w)
    -- The rectangle `[s, ∞) ×ℂ [0, 1]` is the preimage of `[s, ∞) × [0, 1]` under `ℂ ≃ ℝ × ℝ`.
    _ = 2 * ∫⁻ z in Ici s ×ˢ Icc 0 1, F z := by
        rw [← Complex.preimage_equivRealProd_prod]
        exact congrArg _ (Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
          Complex.measurableEquivRealProd.measurableEmbedding _ _)
    _ ≤ 2 * ∫⁻ z in Ici s ×ˢ Icc 0 1, ENNReal.ofReal ((1 + M ^ 2) / c) *
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_Ici.prod measurableSet_Icc)
          fun z hz ↦ ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        have hz' : z ∈ Ioi a ×ˢ univ := ⟨hs.trans_le hz.1, mem_univ _⟩
        exact ENNReal.ofReal_le_ofReal (norm_sq_fderiv_apply_le_mul_floerEnergyDensity hc
          (hJc z hz') (hJM z hz') (hfloer z hz'))
    _ = ENNReal.ofReal (2 * ((1 + M ^ 2) / c)) * ∫⁻ z in Ici s ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- **The coefficients near the orbit.** Once the loops stay within `1` of the orbit, for
`s ≥ s₁`, the coefficients `J` and `B = ∂ₛJ + dX_{H_t}(u)` of the linear equation of `∂ₛu`, and
their derivatives, are bounded on `(max a s₁, ∞) × (-1, 2)`. -/
private theorem exists_bounds_of_floer {L b : ℝ} (hH : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ)) (hJM : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (Ioi a ×ˢ univ))
    (hJ₁ : ∀ z ∈ Ioi a ×ˢ univ,
      ‖fderiv ℝ (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hJ₂ : ∀ z ∈ Ioi a ×ˢ univ,
      ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z (1, 0)‖ ≤ L) (hxc : Continuous x) {s₁ : ℝ}
    (hs₁ : ∀ s ≥ s₁, ∀ t, ‖u (s, t) - x t‖ ≤ 1) :
    ∃ a' b' β γ : ℝ, 0 ≤ a' ∧ 0 ≤ γ ∧ ∀ z ∈ Ioi (max a s₁) ×ˢ Ioo (-1) 2,
      ‖(J z).toLinearMap.toContinuousLinearMap‖ ≤ a' ∧
      ‖fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z‖ ≤ b' ∧
      ‖floerCoeff ω H u J z‖ ≤ β ∧ ‖fderiv ℝ (floerCoeff ω H u J) z‖ ≤ γ := by
  rw [floerCoeff_eq]
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap
  set X : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  set Y : ℝ × V → V →L[ℝ] V := fun p ↦ (fderiv ℝ X p).comp (ContinuousLinearMap.inr ℝ ℝ V)
  have hX : ContDiff ℝ 2 X := ω.contDiff_hamiltonianVectorField_uncurry (n := 2) hH
  have hY : ContDiff ℝ 1 Y := (hX.fderiv_right (m := 1) (by norm_num)).clm_comp contDiff_const
  have hopen : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  -- Bounds for `Y` and its derivative on a compact neighbourhood of the orbit.
  set Kc : Set (ℝ × V) := (fun q : ℝ × V ↦ (q.1, x q.1 + q.2)) '' (Icc (-1) 2 ×ˢ closedBall 0 1)
  have hKc : IsCompact Kc := (isCompact_Icc.prod (isCompact_closedBall _ _)).image
    (continuous_fst.prodMk ((hxc.comp continuous_fst).add continuous_snd))
  obtain ⟨G₀, hG₀⟩ := hKc.exists_bound_of_continuousOn hX.continuous.continuousOn
  obtain ⟨G₁, hG₁⟩ := hKc.exists_bound_of_continuousOn hY.continuous.continuousOn
  obtain ⟨G₂, hG₂⟩ := hKc.exists_bound_of_continuousOn
    (hY.continuous_fderiv (by norm_num)).continuousOn
  set U : Set (ℝ × ℝ) := Ioi (max a s₁) ×ˢ Ioo (-1) 2
  have hUa : U ⊆ Ioi a ×ˢ univ := fun z hz ↦ ⟨(le_max_left _ _).trans_lt hz.1, mem_univ _⟩
  have hUK : ∀ z ∈ U, (z.2, u z) ∈ Kc := fun z hz ↦
    ⟨(z.2, u z - x z.2), ⟨Ioo_subset_Icc_self hz.2, by
      simpa [dist_eq_norm] using hs₁ z.1 ((le_max_right _ _).trans hz.1.le) z.2⟩, by simp⟩
  have hb₀ : 0 ≤ max b 0 := le_max_right _ _
  have hL₀ : 0 ≤ max L 0 := le_max_right _ _
  have hM₀ : 0 ≤ max M 0 := le_max_right _ _
  have hG₀' : 0 ≤ max G₀ 0 := le_max_right _ _
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  -- The full derivative of `u` is bounded on `U`, since `∂ₜu = J ∂ₛu + X_{H_t}(u)` there.
  set L₂ := 1 + max L 0 + max M 0 * max L 0 + max G₀ 0
  have hJu : ∀ z ∈ U, ‖Jc z‖ ≤ max M 0 := fun z hz ↦
    ContinuousLinearMap.opNorm_le_bound _ hM₀ fun v ↦
      (hJM z (hUa hz) v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))
  have hDu : ∀ z ∈ U, ‖fderiv ℝ u z‖ ≤ L₂ - 1 := fun z hz ↦ by
    have hs := (hL z (hUa hz)).trans (le_max_left L 0)
    have h := (fderiv ℝ u z).opNorm_le_norm_apply_add_norm_apply
    rw [fderiv_apply_snd_eq_of_floer (hfloer z (hUa hz))] at h
    have ht : ‖J z (fderiv ℝ u z (1, 0))‖ ≤ max M 0 * max L 0 :=
      ((Jc z).le_of_opNorm_le (hJu z hz) _).trans (mul_le_mul_of_nonneg_left hs hM₀)
    have hX₀ : ‖ω.hamiltonianVectorField (H z.2) (u z)‖ ≤ max G₀ 0 :=
      (hG₀ _ (hUK z hz)).trans (le_max_left _ _)
    linarith [norm_add_le (J z (fderiv ℝ u z (1, 0))) (ω.hamiltonianVectorField (H z.2) (u z))]
  refine ⟨max M 0, max b 0, max b 0 + max G₁ 0, max b 0 + max G₂ 0 * L₂,
    hM₀, add_nonneg hb₀ (mul_nonneg (le_max_right _ _) (by positivity)),
    fun z hz ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact hJu z hz
  · exact (hJ₁ z (hUa hz)).trans (le_max_left _ _)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ((hG₁ _ (hUK z hz)).trans (le_max_left _ _)))
    exact ((fderiv ℝ Jc z).le_of_opNorm_le_of_le ((hJ₁ z (hUa hz)).trans (le_max_left _ _))
      h10).trans_eq (mul_one _)
  have hza := hUa hz
  have hDJ : DifferentiableAt ℝ (fderiv ℝ Jc) z :=
    ((hJ.fderiv_of_isOpen (m := 1) hopen (by norm_num)).contDiffAt
      (hopen.mem_nhds hza)).differentiableAt (by norm_num)
  have hud : DifferentiableAt ℝ u z :=
    ((hu.contDiffAt (hopen.mem_nhds hza)).differentiableAt (by norm_num))
  have hg : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ (w.2, u w)) z :=
    differentiableAt_snd.prodMk hud
  have hYg : DifferentiableAt ℝ (Y ∘ fun w : ℝ × ℝ ↦ (w.2, u w)) z :=
    (hY.differentiable (by norm_num)).differentiableAt.comp z hg
  rw [fderiv_fun_add (f := fun w ↦ fderiv ℝ Jc w (1, 0)) (g := fun w ↦ Y (w.2, u w))
    (hDJ.clm_apply (differentiableAt_const _)) hYg]
  refine (norm_add_le (fderiv ℝ (fun w ↦ fderiv ℝ Jc w (1, 0)) z)
    (fderiv ℝ (fun w ↦ Y (w.2, u w)) z)).trans (add_le_add ?_ ?_)
  · -- The derivative of `∂ₛJ` is bounded by the second derivative of `J`.
    have h2 := hJ₂ z hza
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h2
    refine ContinuousLinearMap.opNorm_le_bound _ hb₀ fun w ↦ ?_
    rw [fderiv_clm_apply_const_apply hDJ]
    exact ((fderiv ℝ (fderiv ℝ Jc) z).le_of_opNorm₂_le_of_le (h2.trans (le_max_left _ _)) le_rfl
      h10).trans_eq (mul_one _)
  · -- The derivative of `Y(t, u)` is bounded by the chain rule.
    have hnorm_g : ‖fderiv ℝ (fun w : ℝ × ℝ ↦ (w.2, u w)) z‖ ≤ L₂ := by
      have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ by simpa using norm_snd_le w
      rw [DifferentiableAt.fderiv_prodMk differentiableAt_snd hud, fderiv_snd,
        ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      have hL₂ : 1 ≤ L₂ := by
        have := mul_nonneg hM₀ hL₀
        simp only [L₂]
        linarith
      exact max_le (hsnd.trans hL₂) ((hDu z hz).trans (by linarith))
    rw [show (fun w : ℝ × ℝ ↦ Y (w.2, u w)) = Y ∘ fun w ↦ (w.2, u w) from rfl,
      fderiv_comp z ((hY.differentiable (by norm_num)).differentiableAt) hg]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    exact (hG₂ _ (hUK z hz)).trans (le_max_left _ _)

/-- **Pointwise exponential decay of `∂ₛu`.** If the energy of `[s, ∞) × [0, 1]` is at most
`C₁ e^{-κ s}` eventually, then `‖∂ₛu(s, t)‖² ≤ D e^{-κ s}` eventually, for `t ∈ [0, 1]`. -/
private theorem exists_eventually_norm_sq_fderiv_le_exp {L b κ C₁ : ℝ}
    (hH : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (Ioi a ×ˢ univ))
    (hJ₁ : ∀ z ∈ Ioi a ×ˢ univ,
      ‖fderiv ℝ (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hJ₂ : ∀ z ∈ Ioi a ×ˢ univ,
      ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z (1, 0)‖ ≤ L) (hxc : Continuous x)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hC₁ : ∀ᶠ s in atTop, ∫⁻ z in Ici s ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal (C₁ * Real.exp (-(κ * s)))) :
    ∃ D, 0 ≤ D ∧ ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ u (s, t) (1, 0)‖ ^ 2 ≤ D * Real.exp (-(κ * s)) := by
  have hopen : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, ∀ s ≥ s₁, ∀ t, ‖u (s, t) - x t‖ ≤ 1 := by
    obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hux 1 one_pos)
    exact ⟨s₁, fun s hs t ↦ by rw [← dist_eq_norm, dist_comm]; exact (hs₁ s hs t).le⟩
  obtain ⟨a', b', β, γ, ha'₀, hγ₀, hbd⟩ :=
    exists_bounds_of_floer hH hu hJM hJ hJ₁ hJ₂ hfloer hL hxc hs₁
  set s₀ := max a s₁
  set U : Set (ℝ × ℝ) := Ioi s₀ ×ˢ Ioo (-1) 2
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_Ioo
  have hUa : U ⊆ Ioi a ×ˢ univ := fun z hz ↦ ⟨(le_max_left _ _).trans_lt hz.1, mem_univ _⟩
  -- The constant of the mean-value inequality, and a radius `r ≤ 1 / 2` with `K r² ≤ 1`.
  set K := ((b' + a' * b' + a' * β) ^ 2 + β ^ 2) / 2 + 2 * (a' * γ + γ)
  have hK₀ : 0 ≤ K := add_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) two_pos.le)
    (mul_nonneg two_pos.le (add_nonneg (mul_nonneg ha'₀ hγ₀) hγ₀))
  set r := 1 / (2 * (K + 1))
  have hr₀ : 0 < r := div_pos one_pos (by linarith)
  have hr2 : r ≤ 1 / 2 := one_div_le_one_div_of_le two_pos (by linarith)
  have hKr : K * r ^ 2 ≤ 1 := by
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith
  have hvc : ContinuousOn (fun z ↦ fderiv ℝ u z (1, 0)) (Ioi a ×ˢ univ) :=
    (hu.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.1 hC₁
  set C₁' := max C₁ 0
  set D := 5 / (π * r ^ 2) * (2 * ((1 + M ^ 2) / c)) * (C₁' * Real.exp (κ / 2))
  refine ⟨D, by positivity, eventually_atTop.2 ⟨max (s₀ + 1) (S₁ + 1 / 2), fun s hs t ht ↦ ?_⟩⟩
  have hs₀ : s₀ + 1 ≤ s := (le_max_left _ _).trans hs
  have hS : S₁ ≤ s - 1 / 2 := by linarith [le_max_right (s₀ + 1) (S₁ + 1 / 2)]
  have has : a < s - 1 / 2 := by linarith [le_max_left a s₁]
  set y : ℂ := Complex.equivRealProdCLM.symm (s, t)
  have hey : Complex.equivRealProdCLM y = (s, t) := Complex.equivRealProdCLM.apply_symm_apply _
  have hy : y.re = s ∧ y.im = t := by simp [y]
  -- The closed disc of radius `r` about `y` lies over `[s - 1/2, ∞) × [t - 1/2, t + 1/2]`.
  have hdisc : ∀ w ∈ closedBall y r, s - 1 / 2 ≤ w.re ∧ t - 1 / 2 ≤ w.im ∧ w.im ≤ t + 1 / 2 := by
    intro w hw
    have h1 := Complex.abs_re_le_norm (w - y)
    have h2 := Complex.abs_im_le_norm (w - y)
    rw [← dist_eq_norm] at h1 h2
    have hd := mem_closedBall.1 hw
    simp only [Complex.sub_re, Complex.sub_im, hy.1, hy.2] at h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith [abs_le.1 (h1.trans (hd.trans hr2)),
      abs_le.1 (h2.trans (hd.trans hr2))]
  have hU' : closedBall y r ⊆ Complex.equivRealProdCLM ⁻¹' U := fun w hw ↦ by
    obtain ⟨h1, h2, h3⟩ := hdisc w hw
    simp only [mem_preimage, Complex.equivRealProdCLM_apply, U, mem_prod, mem_Ioi, mem_Ioo]
    exact ⟨by linarith, by linarith [ht.1], by linarith [ht.2]⟩
  have hmv := pi_mul_sq_mul_norm_sq_le_of_floer hH hU (hu.mono hUa) (hJ.mono hUa)
    (fun z hz ↦ hfloer z (hUa hz)) (fun z hz ↦ (hbd z hz).1) (fun z hz ↦ (hbd z hz).2.1)
    (fun z hz ↦ (hbd z hz).2.2.1) (fun z hz ↦ (hbd z hz).2.2.2) hKr hr₀.le hU'
  rw [hey] at hmv
  have hint := ofReal_setIntegral_ball_le_mul_setLIntegral hper hc hJc hJM hfloer has hr2
    (by linarith [hy.1])
    (hvc.comp Complex.equivRealProdCLM.continuous.continuousOn fun w hw ↦ hUa (hU' hw))
  have hE' := (hint.trans (mul_le_mul' le_rfl (hS₁ _ hS))).trans (mul_le_mul' le_rfl
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C₁ 0)
      (Real.exp_pos _).le)))
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE'
  have hexp : Real.exp (-(κ * (s - 1 / 2))) = Real.exp (κ / 2) * Real.exp (-(κ * s)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at hE'
  have hpr : 0 < π * r ^ 2 := by positivity
  rw [show D * Real.exp (-(κ * s)) = 5 * (2 * ((1 + M ^ 2) / c) *
    (C₁' * (Real.exp (κ / 2) * Real.exp (-(κ * s))))) / (π * r ^ 2) by simp only [D]; ring,
    le_div_iff₀ hpr]
  linarith [hmv, hE', mul_comm (‖fderiv ℝ u (s, t) (1, 0)‖ ^ 2) (π * r ^ 2)]

/-- **Exponential convergence in `C¹` at a nondegenerate end.** Let `u` be a `C³` finite-energy
solution of the Floer equation `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0` on the half-cylinder `s > a`, for
a `C³` Hamiltonian `H` and a `C²` family `J` of uniformly tame almost complex structures whose first
and second derivatives are bounded, with bounded `∂ₛu` and `1`-periodic loops converging uniformly
to a nondegenerate `1`-periodic orbit `x`. Then `u` converges to `x` exponentially fast
in `C¹`: for some `κ > 0` and `C`, eventually in `s` and for `t ∈ [0, 1]`,

`‖u(s, t) - x(t)‖ ≤ C e^{-κ s}` and `‖du(s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C e^{-κ s}`.

The derivative of the stationary cylinder over `x` is `dt ⊗ x'(t) = dt ⊗ X_{H_t}(x(t))`, so this is
the hypothesis of the pre-gluing estimate
`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`.

The derivative `v = ∂ₛu` solves the linear equation `∂ₜv = J ∂ₛv + B v` of
`TauCeti.SymplecticForm.fderiv_fderiv_apply_snd_eq_of_floer`, whose coefficients are bounded near
the orbit, so `‖v‖²` satisfies the mean-value inequality on discs of a fixed radius
(`TauCeti.pi_mul_sq_mul_norm_sq_le_five_mul_setIntegral_ball_of_fderiv_I_eq`). The energy over
`[s, ∞) × [0, 1]` decays exponentially
(`TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp`) and
dominates the integral of `‖v‖²` over such discs, so `v` decays exponentially pointwise. Finally
`∂ₜu - X_{H_t}(x) = J ∂ₛu + X_{H_t}(u) - X_{H_t}(x)`, and the last difference is controlled by
the exponential convergence of the loops
(`TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp`). -/
theorem exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_le_exp {L b : ℝ}
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ univ, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (Ioi a ×ˢ univ))
    (hJ₁ : ∀ z ∈ Ioi a ×ˢ univ,
      ‖fderiv ℝ (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hJ₂ : ∀ z ∈ Ioi a ×ˢ univ,
      ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hfloer : ∀ z ∈ Ioi a ×ˢ univ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hL : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z (1, 0)‖ ≤ L)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)) ∧
      ‖fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (H t) (x t))‖ ≤ C * Real.exp (-(κ * s)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hH2 : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  have hsub : Ioi a ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ univ := prod_mono le_rfl (subset_univ _)
  -- The loops converge exponentially, and the energy of `[s, ∞) × [0, 1]` decays exponentially.
  obtain ⟨κ₀, hκ₀, C₀, hC₀⟩ := exists_pos_eventually_norm_sub_le_exp hH2 hHper
    (hu.of_le (by norm_num)) hper hc (fun z hz ↦ hJc z (hsub hz)) (fun z hz ↦ hJM z (hsub hz))
    (fun z hz ↦ hfloer z (hsub hz)) hE (fun z hz ↦ hL z (hsub hz)) hxper hx hnd hux
  obtain ⟨κ, hκ, C₁, hC₁⟩ := exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp hH2
    hHper (hu.of_le (by norm_num)) hper hc (fun z hz ↦ hJc z (hsub hz))
    (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz)) hE hxper hx hnd hux
  obtain ⟨D, hD₀, hv⟩ := exists_eventually_norm_sq_fderiv_le_exp hH hu hper hc hJc hJM hJ hJ₁ hJ₂
    hfloer hL hxc hux hC₁
  -- `X_{H_t}` is uniformly Lipschitz near the orbit, for `t ∈ [0, 1]`.
  obtain ⟨δ₁, hδ₁, Lx, hLx⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le_mul
      (F := fun t y ↦ ω.hamiltonianVectorField (H t) y)
      ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH2)) hxc.continuousOn
  -- Assemble the `C¹` estimate at the common rate `κ' = min (κ / 2) κ₀`.
  set κ' := min (κ / 2) κ₀
  have hκ'₀ : κ' ≤ κ₀ := min_le_right _ _
  have hκ'κ : κ' ≤ κ / 2 := min_le_left _ _
  set C₀' := max C₀ 0
  set Lx' := max Lx 0
  set a' := max M 0
  have hC₀' : 0 ≤ C₀' := le_max_right _ _
  have hLx' : 0 ≤ Lx' := le_max_right _ _
  have ha' : 0 ≤ a' := le_max_right _ _
  have hsD : 0 ≤ √D := Real.sqrt_nonneg _
  refine ⟨κ', lt_min (half_pos hκ) hκ₀, C₀' + (1 + a') * √D + Lx' * C₀', ?_⟩
  filter_upwards [hC₀, hv, eventually_ge_atTop 0, eventually_gt_atTop a,
    (Metric.tendstoUniformly_iff.1 hux δ₁ hδ₁)] with s hs0 hvs hspos hsa hδs t ht
  have hz : (s, t) ∈ Ioi a ×ˢ univ := ⟨hsa, mem_univ _⟩
  have he' : 0 < Real.exp (-(κ' * s)) := Real.exp_pos _
  -- The `C⁰` part.
  have hux0 : ‖u (s, t) - x t‖ ≤ C₀' * Real.exp (-(κ' * s)) :=
    (hs0 t).trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hC₀')
  -- The `∂ₛ` part.
  have hvs' : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ √D * Real.exp (-(κ' * s)) := by
    have hrhs : (√D * Real.exp (-(κ' * s))) ^ 2 = D * Real.exp (-(2 * κ' * s)) := by
      rw [mul_pow, Real.sq_sqrt hD₀, ← Real.exp_nat_mul]; ring_nf
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hrhs]
    exact (hvs t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hD₀)
  -- The `∂ₜ` part: `∂ₜu - X_{H_t}(x) = J ∂ₛu + X_{H_t}(u) - X_{H_t}(x)`.
  have hdt : ‖fderiv ℝ u (s, t) (0, 1) - ω.hamiltonianVectorField (H t) (x t)‖ ≤
      a' * ‖fderiv ℝ u (s, t) (1, 0)‖ + Lx' * ‖u (s, t) - x t‖ := by
    rw [fderiv_apply_snd_eq_of_floer (hfloer _ hz), add_sub_assoc]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (hJM _ hz _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · refine (hLx t ht _ ?_).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      rw [← dist_eq_norm, dist_comm]
      exact (hδs t).le
  refine ⟨hux0.trans (mul_le_mul_of_nonneg_right (by nlinarith) he'.le), ?_⟩
  refine ((fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
    (ω.hamiltonianVectorField (H t) (x t))).opNorm_le_norm_apply_add_norm_apply.trans ?_)
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', zero_smul, sub_zero, one_smul]
  nlinarith [mul_le_mul_of_nonneg_left hvs' ha', mul_le_mul_of_nonneg_left hux0 hLx']

end TauCeti.SymplecticForm
