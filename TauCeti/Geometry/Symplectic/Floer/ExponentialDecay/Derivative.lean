/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm

/-!
# Exponential decay of the derivatives at a nondegenerate end

Let `(V, ω)` be a symplectic vector space, `H` a `1`-periodic Hamiltonian, and `u` a finite-energy
solution of the Floer equation `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0` on a half-cylinder `s > a` whose
loops converge uniformly to a nondegenerate `1`-periodic orbit `x`. By
`TauCeti.Geometry.Symplectic.Floer.ExponentialDecay` the energy of `[s, ∞) × [0, 1]` decays
exponentially and the loops converge to `x` exponentially in `C⁰`. This file proves exponential
convergence in `C¹`
(`SymplecticForm.exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_smulRight_le_exp`):
eventually `‖du(s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C e^{-κ s}`. This is the form in which the
pre-gluing error estimate `TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`
takes the asymptotics of the two broken cylinders.

**The derivative solves a linear equation.** For the cylindrical perturbation `H_t dt` the
Hamiltonian term does not depend on `s`, so differentiating the equation in `s` shows that
`v = ∂ₛu` solves the linear Cauchy–Riemann equation `∂ₜv = J ∂ₛv + B v`, with
`B = ∂ₛJ + dX_{H_t}(u)`; the term `∂ₛJ` comes from differentiating `J`, which may depend on `s`
(`TauCeti.SymplecticForm.fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer`). Here `J` is the
almost complex structure along `u`, as a function of the domain point.

**Mean-value inequality.** For a linear equation the squared norm satisfies
`Δ ‖v‖² ≥ -K ‖v‖²`, with `K` depending only on bounds for `J`, `B` and their first derivatives
(`TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`). Near the orbit these coefficients are
bounded, so on discs of a fixed small radius `r` the value `‖v‖²` at the centre is at most
`15 / (π r²)` times its integral over the disc
(`TauCeti.pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq`). Unlike the
mean-value inequality for the nonlinear equation, this needs no smallness of the energy.

**From energy to pointwise decay.** A disc of radius at most `1 / 2` centred in `[s, ∞) × [0, 1]`
lies over `[s - 1 / 2, ∞)`, and by periodicity in `t` the integral of `‖v‖²` over it is at most
twice its integral over `[s - 1 / 2, ∞) × [0, 1]`
(`TauCeti.setLIntegral_ball_le_two_mul_setLIntegral_prod_Ioo`), which the energy
controls. So `‖v(s, t)‖² ≤ D e^{-κ s}`. Finally
`∂ₜu - X_{H_t}(x) = J ∂ₛu + X_{H_t}(u) - X_{H_t}(x)`, and the last difference is at most a
Lipschitz constant times `‖u - x‖`.

The almost complex structures enter through their values along `u`, as in
`TauCeti.Geometry.Symplectic.Floer.ExponentialDecay`. Their regularity, bounds on them and their
first two derivatives as functions of the domain point, the `C³` regularity of `u` and the Floer
equation are assumed over a strip `t ∈ (-ε, 1 + ε)` around one period only. No Sobolev completion or
optimal rate is asserted.

## Main results

* `TauCeti.SymplecticForm.fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer`: `∂ₛu` solves
  the linear equation `∂ₜv = J ∂ₛv + B v`.
* `SymplecticForm.exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_smulRight_le_exp`:
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

variable {V : Type*} [NormedAddCommGroup V]

section NormedSpace

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {a c M ε : ℝ}

/-- **The `s`-derivative of a Floer solution solves a linear Cauchy–Riemann equation.** On an open
set where `u` is a `C²` solution of `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0` and `J` is a `C¹` family, at a
point `z` such that the Hamiltonian is `C²` near `(t, u z)`, the derivative `v = ∂ₛu` satisfies
`∂ₜv = J ∂ₛv + B v` with `B z = ∂ₛJ z + dX_{H_t}(u z)`, the second term being the spatial Jacobian
`spatialFDeriv` of the Hamiltonian vector field `X(t, y) = X_{H_t}(y)`. -/
theorem fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hJ : ContDiffOn ℝ 1 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) U)
    (hfloer : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {z : ℝ × ℝ} (hz : z ∈ U) (hH : ContDiffAt ℝ 2 (uncurry H) (z.2, u z)) :
    fderiv ℝ (fun w ↦ fderiv ℝ u w (1, 0)) z (0, 1) =
      J z (fderiv ℝ (fun w ↦ fderiv ℝ u w (1, 0)) z (1, 0)) +
        (fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z (1, 0) +
          spatialFDeriv (𝕜 := ℝ) (fun p : ℝ × V ↦ ω.hamiltonianVectorField (H p.1) p.2) (u z) z.2)
          (fderiv ℝ u z (1, 0)) := by
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap with hJc_def
  set X : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  have huz : ContDiffAt ℝ 2 u z := hu.contDiffAt (hU.mem_nhds hz)
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (huz.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hud : DifferentiableAt ℝ u z := huz.differentiableAt (by norm_num)
  have hJz : DifferentiableAt ℝ Jc z :=
    (hJ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hXg : DifferentiableAt ℝ X (z.2, u z) :=
    (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hH).differentiableAt (by norm_num)
  -- Near `z` the Floer equation reads `∂ₜu = J ∂ₛu + X_{H_t}(u)`.
  have heq : (fun w ↦ fderiv ℝ u w (0, 1)) =ᶠ[𝓝 z]
      fun w ↦ Jc w (fderiv ℝ u w (1, 0)) + ω.hamiltonianVectorField (H w.2) (u w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa [hJc_def] using ω.fderiv_apply_zero_one_eq_of_floer (hfloer w hw)
  -- Differentiate in the direction `(1, 0)`, using the symmetry of the second derivative of `u`.
  have hvs : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w (1, 0)) z :=
    hDu.clm_apply (differentiableAt_const _)
  have hsymm : fderiv ℝ (fderiv ℝ u) z (0, 1) (1, 0) = fderiv ℝ (fderiv ℝ u) z (1, 0) (0, 1) :=
    huz.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) _ _
  -- The Hamiltonian term does not depend on `s`, so its `s`-derivative is spatial.
  have hcomp : fderiv ℝ (fun w ↦ ω.hamiltonianVectorField (H w.2) (u w)) z (1, 0) =
      spatialFDeriv (𝕜 := ℝ) X (u z) z.2 (fderiv ℝ u z (1, 0)) := by
    have h0 : (fun y ↦ fderiv ℝ (fun q : ℝ × ℝ ↦ H q.2 y) z (1, 0)) = fun _ ↦ 0 :=
      funext fun y ↦ fderiv_comp_snd_apply_mk_zero (fun t ↦ H t y) z 1
    rw [ω.fderiv_hamiltonianVectorField_comp_apply (K := fun q : ℝ × ℝ ↦ H q.2)
      (hH.comp (z, u z) (contDiffAt_fst.snd.prodMk contDiffAt_snd)) hud, fderiv_timeSlice hXg,
      h0, hamiltonianVectorField_const, Pi.zero_apply, add_zero]
  have h := congrArg (fun L : ℝ × ℝ →L[ℝ] V ↦ L (1, 0)) heq.fderiv_eq
  have hXg' : DifferentiableAt ℝ (fun w ↦ ω.hamiltonianVectorField (H w.2) (u w)) z :=
    hXg.comp z (differentiableAt_snd.prodMk hud)
  rw [fderiv_clm_apply_const_apply hDu, fderiv_fun_add (f := fun w ↦ Jc w (fderiv ℝ u w (1, 0)))
    (hJz.clm_apply hvs) hXg', fderiv_clm_apply hJz hvs] at h
  rw [fderiv_clm_apply_const_apply hDu, hsymm, h, add_apply, hcomp]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_clm_apply_const_apply hDu, LinearMap.coe_toContinuousLinearMap',
    ContinuousLinearMap.flip_apply, Jc]
  abel

/-- The coefficient `B z = ∂ₛJ z + dX_{H_t}(u z)` of the linear equation `∂ₜv = J ∂ₛv + B v`
solved by `v = ∂ₛu`
(`TauCeti.SymplecticForm.fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer`). -/
private noncomputable def floerCoeff (ω : SymplecticForm V) (H : ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (J : ℝ × ℝ → AlmostComplexStructure V) : ℝ × ℝ → V →L[ℝ] V :=
  fun z ↦ fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z (1, 0) +
    spatialFDeriv (𝕜 := ℝ) (fun p : ℝ × V ↦ ω.hamiltonianVectorField (H p.1) p.2) (u z) z.2

/-- **The integral of `‖∂ₛu‖²` over a disc is controlled by the energy of a half-cylinder.** If a
disc of the complex coordinate of radius `r ≤ 1 / 2` lies over `[s, ∞)`, with `s > a`, then the
integral of `‖∂ₛu‖²` over it is at most `4 / c` times the energy over `[s, ∞) × [0, 1]`. -/
private theorem ofReal_setIntegral_ball_le_mul_setLIntegral
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {s r : ℝ} {y : ℂ} (hs : a < s) (hr : r ≤ 1 / 2) (hsy : s ≤ y.re - r)
    (hcont : ContinuousOn (fun w ↦ fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0))
      (closedBall y r)) :
    ENNReal.ofReal (∫ w in ball y r, ‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2) ≤
      ENNReal.ofReal (2 * (2 / c)) * ∫⁻ z in Ici s ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
  have hint : IntegrableOn (fun w ↦ ‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2)
      (ball y r) :=
    ((hcont.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ by positivity)]
  calc ∫⁻ w in ball y r, ENNReal.ofReal (‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2)
      = ∫⁻ w in ball y r, ‖fderiv ℝ u (w.re, w.im) stdComplexLineReal‖ₑ ^ 2 := by
        simp only [Complex.equivRealProdCLM_apply, stdComplexLineReal_eq,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    -- Over `s > a`, the derivative of `u` is `1`-periodic in `t`.
    _ ≤ 2 * ∫⁻ z in Ioo (y.re - r) (y.re + r) ×ˢ Icc 0 1,
          ‖fderiv ℝ u z stdComplexLineReal‖ₑ ^ 2 :=
        setLIntegral_ball_le_two_mul_setLIntegral_prod_Ioo
          (g := fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ₑ ^ 2)
          (fun s hs t ↦ congrArg (fun L : ℝ × ℝ →L[ℝ] V ↦ ‖L stdComplexLineReal‖ₑ ^ 2)
            (periodic_fderiv_mk_of_isOpen isOpen_Ioi hper hs t)) y hr (hs.le.trans hsy)
    _ ≤ 2 * ∫⁻ z in Ici s ×ˢ Icc 0 1, ‖fderiv ℝ u z stdComplexLineReal‖ₑ ^ 2 := by
        gcongr
        exact fun t ht ↦ hsy.trans ht.1.le
    -- `‖∂ₛu‖² ≤ (2 / c) e` on `[s, ∞) × [0, 1]`.
    _ ≤ 2 * (ENNReal.ofReal (2 / c) * ∫⁻ z in Ici s ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)) := by
        gcongr
        exact ω.setLIntegral_enorm_fderiv_stdComplexLineReal_sq_le hc
          (measurableSet_Ici.prod measurableSet_Icc) (fun z hz ↦ hJc z ⟨hs.trans_le hz.1, hz.2⟩)
          fun z hz ↦ hfloer z ⟨hs.trans_le hz.1, hz.2⟩
    _ = ENNReal.ofReal (2 * (2 / c)) * ∫⁻ z in Ici s ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) := by
        rw [← mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- **The derivative of the coefficient `B`.** At a point of an open set where `u` is `C¹` and `J`
is `C²`, the derivative of `B = ∂ₛJ + dX_{H_t}(u)` is at most `b + G L`, for bounds `b` on the
second derivative of `J`, `G` on the derivative of `dX_{H_t}` at `(t, u)`, and `L ≥ 1` on `du`. -/
private theorem norm_fderiv_floerCoeff_le (hH : ContDiff ℝ 3 (uncurry H)) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) U) {z : ℝ × ℝ}
    (hz : z ∈ U) {b G L : ℝ} (hb : 0 ≤ b) (hG : 0 ≤ G)
    (hJ₂ : ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hX : ‖fderiv ℝ (fun p : ℝ × V ↦ spatialFDeriv (𝕜 := ℝ)
      (fun q : ℝ × V ↦ ω.hamiltonianVectorField (H q.1) q.2) p.2 p.1) (z.2, u z)‖ ≤ G)
    (hL : 1 ≤ L) (hDu : ‖fderiv ℝ u z‖ ≤ L) :
    ‖fderiv ℝ (floerCoeff ω H u J) z‖ ≤ b + G * L := by
  unfold floerCoeff
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap
  set Y : ℝ × V → V →L[ℝ] V := fun p ↦ spatialFDeriv (𝕜 := ℝ)
    (fun q : ℝ × V ↦ ω.hamiltonianVectorField (H q.1) q.2) p.2 p.1
  have hY : ContDiff ℝ 1 Y := contDiff_iff_contDiffAt.2 fun _ ↦
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 2) hH).contDiffAt.spatialFDeriv (by norm_num)
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hDJ : DifferentiableAt ℝ (fderiv ℝ Jc) z :=
    ((hJ.fderiv_of_isOpen (m := 1) hU (by norm_num)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hud : DifferentiableAt ℝ u z :=
    (hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ (w.2, u w)) z :=
    differentiableAt_snd.prodMk hud
  have hYd : DifferentiableAt ℝ Y (z.2, u z) := (hY.differentiable (by norm_num)).differentiableAt
  rw [fderiv_fun_add (f := fun w ↦ fderiv ℝ Jc w (1, 0)) (g := fun w ↦ Y (w.2, u w))
    (hDJ.clm_apply (differentiableAt_const _)) (hYd.fun_comp' z hg)]
  refine (norm_add_le (fderiv ℝ (fun w ↦ fderiv ℝ Jc w (1, 0)) z)
    (fderiv ℝ (fun w ↦ Y (w.2, u w)) z)).trans (add_le_add ?_ ?_)
  · -- The derivative of `∂ₛJ` is bounded by the second derivative of `J`.
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at hJ₂
    refine ContinuousLinearMap.opNorm_le_bound _ hb fun w ↦ ?_
    rw [fderiv_clm_apply_const_apply hDJ]
    exact ((fderiv ℝ (fderiv ℝ Jc) z).le_of_opNorm₂_le_of_le hJ₂ le_rfl h10).trans_eq (mul_one _)
  · -- The derivative of `Y(t, u)` is bounded by the chain rule.
    have hnorm_g : ‖fderiv ℝ (fun w : ℝ × ℝ ↦ (w.2, u w)) z‖ ≤ L := by
      rw [DifferentiableAt.fderiv_prodMk differentiableAt_snd hud, fderiv_snd,
        ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      exact max_le ((ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ).trans hL) hDu
    rw [fderiv_fun_comp z hYd hg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hX hnorm_g (norm_nonneg _) hG)

/-- **The coefficients near the orbit.** Once the loops stay within `1` of the orbit, for
`s ≥ s₁`, the coefficients `J` and `B = ∂ₛJ + dX_{H_t}(u)` of the linear equation of `∂ₛu`, and
their derivatives, are bounded on `(max a s₁, ∞) × (-ε, 1 + ε)`. -/
private theorem exists_bounds_of_floer {L b : ℝ} (hH : ContDiff ℝ 3 (uncurry H))
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ Ioo (-ε) (1 + ε)))
    (hJM : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε), ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
      (Ioi a ×ˢ Ioo (-ε) (1 + ε)))
    (hJ₁ : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε),
      ‖fderiv ℝ (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hJ₂ : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε),
      ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε), IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z (1, 0)‖ ≤ L) (hxc : Continuous x) {s₁ : ℝ}
    (hs₁ : ∀ s ≥ s₁, ∀ t, ‖u (s, t) - x t‖ ≤ 1) :
    ∃ a' b' β γ : ℝ, 0 ≤ a' ∧ 0 ≤ γ ∧ ∀ z ∈ Ioi (max a s₁) ×ˢ Ioo (-ε) (1 + ε),
      ‖(J z).toLinearMap.toContinuousLinearMap‖ ≤ a' ∧
      ‖fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z‖ ≤ b' ∧
      ‖floerCoeff ω H u J z‖ ≤ β ∧ ‖fderiv ℝ (floerCoeff ω H u J) z‖ ≤ γ := by
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap
  set X : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  set Y : ℝ × V → V →L[ℝ] V := fun p ↦ spatialFDeriv (𝕜 := ℝ) X p.2 p.1
  have hX : ContDiff ℝ 2 X := ω.contDiff_hamiltonianVectorField_uncurry (n := 2) hH
  have hY : ContDiff ℝ 1 Y :=
    contDiff_iff_contDiffAt.2 fun _ ↦ hX.contDiffAt.spatialFDeriv (by norm_num)
  -- Bounds for `X`, `Y` and the derivative of `Y` on a compact neighbourhood of the orbit.
  set Kc : Set (ℝ × V) :=
    (fun q : ℝ × V ↦ (q.1, x q.1 + q.2)) '' (Icc (-ε) (1 + ε) ×ˢ closedBall 0 1)
  have hKc : IsCompact Kc := (isCompact_Icc.prod (isCompact_closedBall _ _)).image
    (continuous_fst.prodMk ((hxc.comp continuous_fst).add continuous_snd))
  obtain ⟨G₀, hG₀⟩ := hKc.exists_bound_of_continuousOn hX.continuous.continuousOn
  obtain ⟨G₁, hG₁⟩ := hKc.exists_bound_of_continuousOn hY.continuous.continuousOn
  obtain ⟨G₂, hG₂⟩ := hKc.exists_bound_of_continuousOn
    (hY.continuous_fderiv (by norm_num)).continuousOn
  set U : Set (ℝ × ℝ) := Ioi (max a s₁) ×ˢ Ioo (-ε) (1 + ε)
  have hUa : U ⊆ Ioi a ×ˢ univ := fun z hz ↦ ⟨(le_max_left _ _).trans_lt hz.1, mem_univ _⟩
  have hUb : U ⊆ Ioi a ×ˢ Ioo (-ε) (1 + ε) := fun z hz ↦ ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩
  have hUK : ∀ z ∈ U, (z.2, u z) ∈ Kc := fun z hz ↦
    ⟨(z.2, u z - x z.2), ⟨Ioo_subset_Icc_self hz.2, by
      simpa [dist_eq_norm] using hs₁ z.1 ((le_max_right _ _).trans hz.1.le) z.2⟩, by simp⟩
  have hb₀ : 0 ≤ max b 0 := le_max_right _ _
  have hL₀ : 0 ≤ max L 0 := le_max_right _ _
  have hM₀ : 0 ≤ max M 0 := le_max_right _ _
  have hG₀' : 0 ≤ max G₀ 0 := le_max_right _ _
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  set L₂ := 1 + max L 0 + max M 0 * max L 0 + max G₀ 0
  have hJM' : ∀ z ∈ U, ∀ v, ‖J z v‖ ≤ max M 0 * ‖v‖ := fun z hz v ↦
    (hJM z (hUb hz) v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))
  refine ⟨max M 0, max b 0, max b 0 + max G₁ 0, max b 0 + max G₂ 0 * L₂,
    hM₀, add_nonneg hb₀ (mul_nonneg (le_max_right _ _) (by positivity)),
    fun z hz ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ hM₀ (hJM' z hz)
  · exact (hJ₁ z (hUb hz)).trans (le_max_left _ _)
  · simp only [floerCoeff]
    refine (norm_add_le _ _).trans (add_le_add ?_ ((hG₁ _ (hUK z hz)).trans (le_max_left _ _)))
    exact ((fderiv ℝ Jc z).le_of_opNorm_le_of_le ((hJ₁ z (hUb hz)).trans (le_max_left _ _))
      h10).trans_eq (mul_one _)
  -- The full derivative of `u` is bounded on `U`, since `∂ₜu = J ∂ₛu + X_{H_t}(u)` there.
  have hDu : ‖fderiv ℝ u z‖ ≤ (1 + max M 0) * max L 0 + max G₀ 0 := by
    have h := ω.norm_fderiv_sub_smulRight_le_of_floer 0 (hJM' z hz) (hfloer z (hUb hz))
    rw [ContinuousLinearMap.smulRight_zero, sub_zero, sub_zero] at h
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left
      ((hL z (hUa hz)).trans (le_max_left L 0)) (by positivity))
      ((hG₀ _ (hUK z hz)).trans (le_max_left G₀ 0)))
  have hML := mul_nonneg hM₀ hL₀
  exact norm_fderiv_floerCoeff_le hH (isOpen_Ioi.prod isOpen_Ioo) hu hJ
    (hUb hz) hb₀ (le_max_right _ _) ((hJ₂ z (hUb hz)).trans (le_max_left _ _))
    ((hG₂ _ (hUK z hz)).trans (le_max_left _ _)) (by simp only [L₂]; linarith)
    (by simp only [L₂]; linarith)

/-- **Reduction to one period.** Since `u`, its derivative, `x` and `H` are `1`-periodic in `t`,
bounds on `‖u(s, t) - x(t)‖` and `‖du(s, t) - dt ⊗ X_{H_t}(x(t))‖` for `t ∈ [0, 1]` hold for every
`t`. -/
private theorem norm_sub_le_and_norm_fderiv_sub_smulRight_le_of_forall_mem_Icc
    (hHper : Periodic H 1) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hxper : Periodic x 1) {s A B : ℝ}
    (hs : a < s) (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t) - x t‖ ≤ A ∧
      ‖fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (H t) (x t))‖ ≤ B) (t : ℝ) :
    ‖u (s, t) - x t‖ ≤ A ∧ ‖fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (ω.hamiltonianVectorField (H t) (x t))‖ ≤ B := by
  -- The data at `t` are those at some `t' ∈ [0, 1)`.
  have hP : Periodic (fun t ↦ (u (s, t), x t, H t, fderiv ℝ u (s, t))) 1 := fun t ↦ by
    simp only [Prod.mk.injEq]
    exact ⟨hper s hs t, hxper t, hHper t, periodic_fderiv_mk_of_isOpen isOpen_Ioi hper hs t⟩
  obtain ⟨t', ht', heq⟩ := hP.exists_mem_Ico₀ one_pos t
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hut, hxt, hHt, hdut⟩ := heq
  rw [hut, hxt, hHt, hdut]
  exact h t' (Ico_subset_Icc_self ht')

end NormedSpace

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V} {u : ℝ × ℝ → V}
  {J : ℝ × ℝ → AlmostComplexStructure V} {a c M ε : ℝ}

/-- **The mean-value inequality for `∂ₛu`.** On an open set `U` where `u` is a `C³` Floer solution
for `H_t dt`, with a `C²` family `J`, let `a`, `b`, `β`, `γ` bound `J`, its derivative, the
coefficient `B` of
`TauCeti.SymplecticForm.fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer` and its
derivative. Then for every disc `ball y r` of the complex coordinate whose closure lies in `U`,
with `16 K r² ≤ 1` for the constant `K` of
`TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`, `π r² ‖∂ₛu‖²` at the centre is at most
fifteen times the integral of `‖∂ₛu‖²` over the disc. -/
private theorem pi_mul_sq_mul_norm_fderiv_apply_one_zero_sq_le_of_floer
    (hH : ContDiff ℝ 3 (uncurry H))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) U)
    (hfloer : ∀ z ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    {r a' b β γ : ℝ}
    (ha : ∀ z ∈ U, ‖(J z).toLinearMap.toContinuousLinearMap‖ ≤ a')
    (hb : ∀ z ∈ U, ‖fderiv ℝ (fun w ↦ (J w).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hβ : ∀ z ∈ U, ‖floerCoeff ω H u J z‖ ≤ β)
    (hγ : ∀ z ∈ U, ‖fderiv ℝ (floerCoeff ω H u J) z‖ ≤ γ)
    (hKr : 16 * (((b + a' * b + a' * β) ^ 2 + β ^ 2) / 2 + 2 * (a' * γ + γ)) * r ^ 2 ≤ 1)
    (hr : 0 ≤ r) {y : ℂ} (hy : closedBall y r ⊆ Complex.equivRealProdCLM ⁻¹' U) :
    π * r ^ 2 * ‖fderiv ℝ u (Complex.equivRealProdCLM y) (1, 0)‖ ^ 2 ≤
      15 * ∫ w in ball y r, ‖fderiv ℝ u (Complex.equivRealProdCLM w) (1, 0)‖ ^ 2 := by
  set e : ℂ →L[ℝ] ℝ × ℝ := (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  set Jc : ℝ × ℝ → V →L[ℝ] V := fun w ↦ (J w).toLinearMap.toContinuousLinearMap
  set B : ℝ × ℝ → V →L[ℝ] V := floerCoeff ω H u J with hB
  have he : ‖e‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ by
    simpa [e] using Complex.equivRealProd_apply_le' w
  have hball : ball y r ⊆ e ⁻¹' U := ball_subset_closedBall.trans hy
  -- Precomposition with the coordinate `e`, of norm at most `1`, keeps derivative bounds.
  have hpull (F : ℝ × ℝ → V →L[ℝ] V) {w : ℂ} {k : ℝ} (hk : ‖fderiv ℝ F (e w)‖ ≤ k) :
      ‖fderiv ℝ (F ∘ e) w‖ ≤ k := by
    have h : fderiv ℝ (F ∘ e) w = (fderiv ℝ F (e w)).comp e :=
      Complex.equivRealProdCLM.comp_right_fderiv (f := F)
    rw [h]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) he).trans hk)
  -- `∂ₛu` is `C²` on `U`, and `B` is `C¹` there.
  have hv : ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ u z (1, 0)) U :=
    (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  have hBc : ContDiffOn ℝ 1 B U := by
    rw [hB]
    unfold floerCoeff
    exact ((hJ.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).add
      ((contDiff_iff_contDiffAt.2 fun _ ↦
        (ω.contDiff_hamiltonianVectorField_uncurry (n := 2) hH).contDiffAt.spatialFDeriv
          (by norm_num)).comp_contDiffOn (contDiffOn_snd.prodMk (hu.of_le (by norm_num))))
  have hv' : ContDiffOn ℝ 2 (fun w ↦ fderiv ℝ u (e w) (1, 0)) (e ⁻¹' U) :=
    hv.comp e.contDiff.contDiffOn fun _ h ↦ h
  refine pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq
    (J := Jc ∘ e) (B := B ∘ e) hr (hv'.mono hball) (hv'.continuousOn.mono hy)
    (fun w hw ↦ ((hJ.contDiffAt (hU.mem_nhds (hball hw))).differentiableAt
      (by norm_num)).comp w e.differentiableAt)
    (fun w hw ↦ ((hBc.contDiffAt (hU.mem_nhds (hball hw))).differentiableAt
      (by norm_num)).comp w e.differentiableAt)
    (fun w hw ↦ ?_) (fun w _ v ↦ ?_) (fun w hw ↦ ha _ (hball hw)) (fun w hw ↦ ?_)
    (fun w hw ↦ hβ _ (hball hw)) (fun w hw ↦ ?_) hKr
  · -- The linear equation, read in the complex coordinate.
    have h := fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer hU
      (hu.of_le (by norm_num)) (hJ.of_le (by norm_num)) hfloer (hball hw)
      (hH.of_le (by norm_num)).contDiffAt
    rw [show (fun w ↦ fderiv ℝ u (e w) (1, 0)) =
        (fun z ↦ fderiv ℝ u z (1, 0)) ∘ Complex.equivRealProdCLM from rfl,
      fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I, stdComplexLineReal_eq,
      stdComplexLineImag_eq]
    simpa only [B, Jc, e, floerCoeff, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap'] using h
  · simp [Jc, AlmostComplexStructure.apply_apply]
  · exact hpull Jc (hb _ (hball hw))
  · exact hpull B (hγ _ (hball hw))

/-- **Pointwise exponential decay of `∂ₛu`.** If the energy of `[s, ∞) × [0, 1]` is at most
`C₁ e^{-κ s}` eventually, then `‖∂ₛu(s, t)‖² ≤ D e^{-κ s}` eventually, for `t ∈ [0, 1]`. -/
private theorem exists_eventually_norm_fderiv_apply_one_zero_sq_le_exp {L b κ C₁ : ℝ}
    (hε : 0 < ε) (hH : ContDiff ℝ 3 (uncurry H)) (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ Ioo (-ε) (1 + ε)))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε), ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
      (Ioi a ×ˢ Ioo (-ε) (1 + ε)))
    (hJ₁ : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε),
      ‖fderiv ℝ (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hJ₂ : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε),
      ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε), IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hL : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z (1, 0)‖ ≤ L) (hxc : Continuous x)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop)
    (hC₁ : ∀ᶠ s in atTop, ∫⁻ z in Ici s ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal (C₁ * Real.exp (-(κ * s)))) :
    ∃ D, 0 ≤ D ∧ ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ u (s, t) (1, 0)‖ ^ 2 ≤ D * Real.exp (-(κ * s)) := by
  have hopen : IsOpen (Ioi a ×ˢ Ioo (-ε) (1 + ε)) := isOpen_Ioi.prod isOpen_Ioo
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, ∀ s ≥ s₁, ∀ t, ‖u (s, t) - x t‖ ≤ 1 := by
    obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hux 1 one_pos)
    exact ⟨s₁, fun s hs t ↦ by rw [← dist_eq_norm, dist_comm]; exact (hs₁ s hs t).le⟩
  obtain ⟨a', b', β, γ, ha'₀, hγ₀, hbd⟩ :=
    exists_bounds_of_floer hH (hu.of_le (by norm_num)) hJM hJ hJ₁ hJ₂ hfloer hL hxc hs₁
  set s₀ := max a s₁
  set U : Set (ℝ × ℝ) := Ioi s₀ ×ˢ Ioo (-ε) (1 + ε)
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_Ioo
  have hUa : U ⊆ Ioi a ×ˢ Ioo (-ε) (1 + ε) := fun z hz ↦ ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩
  -- The constant of the mean-value inequality, and a radius `r ≤ 1 / 2` with `16 K r² ≤ 1`.
  set K := ((b' + a' * b' + a' * β) ^ 2 + β ^ 2) / 2 + 2 * (a' * γ + γ)
  have hK₀ : 0 ≤ K := add_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) two_pos.le)
    (mul_nonneg two_pos.le (add_nonneg (mul_nonneg ha'₀ hγ₀) hγ₀))
  set r := min (1 / (8 * (K + 1))) (ε / 2)
  have hr₀ : 0 < r := lt_min (div_pos one_pos (by linarith)) (half_pos hε)
  have hr2 : r ≤ 1 / 2 :=
    (min_le_left _ _).trans (one_div_le_one_div_of_le two_pos (by linarith))
  have hKr : 16 * K * r ^ 2 ≤ 1 := by
    have hr8 : r ^ 2 ≤ (1 / (8 * (K + 1))) ^ 2 := pow_le_pow_left₀ hr₀.le (min_le_left _ _) 2
    have h8 : 16 * K * (1 / (8 * (K + 1))) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
      nlinarith
    nlinarith
  have hvc : ContinuousOn (fun z ↦ fderiv ℝ u z (1, 0)) (Ioi a ×ˢ Ioo (-ε) (1 + ε)) :=
    (hu.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.1 hC₁
  set C₁' := max C₁ 0
  set D := 15 / (π * r ^ 2) * (2 * (2 / c)) * (C₁' * Real.exp (κ / 2))
  refine ⟨D, by positivity, eventually_atTop.2 ⟨max (s₀ + 1) (S₁ + 1 / 2), fun s hs t ht ↦ ?_⟩⟩
  have hs₀ : s₀ + 1 ≤ s := (le_max_left _ _).trans hs
  have hS : S₁ ≤ s - 1 / 2 := by linarith [le_max_right (s₀ + 1) (S₁ + 1 / 2)]
  have has : a < s - 1 / 2 := by linarith [le_max_left a s₁]
  set y : ℂ := Complex.equivRealProdCLM.symm (s, t)
  have hey : Complex.equivRealProdCLM y = (s, t) := Complex.equivRealProdCLM.apply_symm_apply _
  have hy : y.re = s := by simp [y]
  -- The closed disc of radius `r` about `y` lies over the square `[s - r, s + r] × [t - r, t + r]`.
  have hU' : closedBall y r ⊆ Complex.equivRealProdCLM ⁻¹' U := fun w hw ↦ by
    have hsq : Complex.equivRealProdCLM w ∈ Icc (s - r) (s + r) ×ˢ Icc (t - r) (t + r) := by
      rw [← Real.closedBall_eq_Icc, ← Real.closedBall_eq_Icc, closedBall_prod_same]
      exact (Complex.dist_equivRealProdCLM_le w (s, t)).trans hw
    obtain ⟨⟨h1, -⟩, h2, h3⟩ := hsq
    have hrε : r ≤ ε / 2 := min_le_right _ _
    simp only [mem_preimage, U, mem_prod, mem_Ioi, mem_Ioo]
    exact ⟨by linarith, by linarith [ht.1], by linarith [ht.2]⟩
  have hmv := pi_mul_sq_mul_norm_fderiv_apply_one_zero_sq_le_of_floer hH hU (hu.mono hUa)
    (hJ.mono hUa) (fun z hz ↦ hfloer z (hUa hz)) (fun z hz ↦ (hbd z hz).1)
    (fun z hz ↦ (hbd z hz).2.1) (fun z hz ↦ (hbd z hz).2.2.1) (fun z hz ↦ (hbd z hz).2.2.2) hKr
    hr₀.le hU'
  rw [hey] at hmv
  have hint := ofReal_setIntegral_ball_le_mul_setLIntegral hper hc hJc
    (fun z hz ↦ hfloer z ⟨hz.1, Icc_subset_Ioo (by linarith) (by linarith) hz.2⟩) has hr2
    (by linarith [hy])
    (hvc.comp Complex.equivRealProdCLM.continuous.continuousOn fun w hw ↦ hUa (hU' hw))
  have hE' := (hint.trans (mul_le_mul' le_rfl (hS₁ _ hS))).trans (mul_le_mul' le_rfl
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C₁ 0)
      (Real.exp_pos _).le)))
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE'
  have hexp : Real.exp (-(κ * (s - 1 / 2))) = Real.exp (κ / 2) * Real.exp (-(κ * s)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at hE'
  have hpr : 0 < π * r ^ 2 := by positivity
  -- Write the bound `D e^{-κ s}` with the factor `1 / (π r²)` of the mean-value inequality last.
  have hD : D * Real.exp (-(κ * s)) = 15 * (2 * (2 / c) *
      (C₁' * (Real.exp (κ / 2) * Real.exp (-(κ * s))))) / (π * r ^ 2) := by
    simp only [D]; ring
  rw [hD, le_div_iff₀ hpr]
  linarith [hmv, hE', mul_comm (‖fderiv ℝ u (s, t) (1, 0)‖ ^ 2) (π * r ^ 2)]

/-- **Exponential convergence in `C¹` at a nondegenerate end.** Let `u` be a finite-energy solution
of the Floer equation `∂ₛu + J (∂ₜu - X_{H_t}(u)) = 0` for a `C³` Hamiltonian `H`, on the
half-cylinder `s > a`, with `1`-periodic loops converging uniformly to a nondegenerate
`1`-periodic orbit `x`, and with `∂ₛu` bounded over `t ∈ [0, 1]`. Suppose that the family `J` of
almost complex structures is uniformly tame over `t ∈ [0, 1]`, and that over a strip
`t ∈ (-ε, 1 + ε)` around one period `u` is `C³`, solves the Floer equation, and `J` is `C²` and
bounded together with its first and second derivatives. By periodicity `u` is then `C³` on the
whole half-cylinder. Then `u` converges to `x` exponentially fast in
`C¹`: for some `κ > 0` and `C`, eventually in `s` and for all `t`,

`‖u(s, t) - x(t)‖ ≤ C e^{-κ s}` and `‖du(s, t) - dt ⊗ X_{H_t}(x(t))‖ ≤ C e^{-κ s}`.

The derivative of the stationary cylinder over `x` is `dt ⊗ x'(t) = dt ⊗ X_{H_t}(x(t))`, so this
gives the hypothesis of the pre-gluing estimate
`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le`.

The derivative `v = ∂ₛu` solves the linear equation `∂ₜv = J ∂ₛv + B v` of
`TauCeti.SymplecticForm.fderiv_fderiv_apply_one_zero_apply_zero_one_eq_of_floer`, whose coefficients
are bounded near the orbit, so `‖v‖²` satisfies the mean-value inequality on discs of a fixed radius
(`TauCeti.pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq`). The energy over
`[s, ∞) × [0, 1]` decays exponentially
(`TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp`) and
dominates the integral of `‖v‖²` over such discs, so `v` decays exponentially pointwise. The same
energy decay gives the exponential convergence of the loops
(`TauCeti.SymplecticForm.exists_eventually_norm_sub_le_exp_of_setLIntegral_le_exp`). Finally
`∂ₜu - X_{H_t}(x) = J ∂ₛu + X_{H_t}(u) - X_{H_t}(x)`, and the last difference is at most a
Lipschitz constant times `‖u - x‖`. -/
theorem exists_pos_eventually_norm_sub_le_exp_and_norm_fderiv_sub_smulRight_le_exp {L b : ℝ}
    (hε : 0 < ε) (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    (hu : ContDiffOn ℝ 3 u (Ioi a ×ˢ Ioo (-ε) (1 + ε)))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε), ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hJ : ContDiffOn ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
      (Ioi a ×ˢ Ioo (-ε) (1 + ε)))
    (hJ₁ : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε),
      ‖fderiv ℝ (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hJ₂ : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε),
      ‖iteratedFDeriv ℝ 2 (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) z‖ ≤ b)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Ioo (-ε) (1 + ε), IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hL : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ u z (1, 0)‖ ≤ L)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t,
      ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)) ∧
      ‖fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (H t) (x t))‖ ≤ C * Real.exp (-(κ * s)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hH2 : ContDiff ℝ 2 (uncurry H) := hH.of_le (by norm_num)
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := Icc_subset_Ioo (by linarith) (by linarith)
  -- By periodicity, `u` is `C²` on the whole half-cylinder.
  have hu₂ : ContDiffOn ℝ 2 u (Ioi a ×ˢ univ) :=
    (contDiffOn_prod_univ_of_periodic_snd isOpen_Ioi isOpen_Ioo one_pos
      (Ico_subset_Icc_self.trans hIcc) hper hu).of_le (by norm_num)
  have hJM' : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖ := fun z hz ↦ hJM z ⟨hz.1, hIcc hz.2⟩
  have hfloer' : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z) (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V) :=
    fun z hz ↦ hfloer z ⟨hz.1, hIcc hz.2⟩
  -- `∂ₛu` is `1`-periodic in `t`, so the bound `L` holds on the whole half-cylinder.
  have hL' : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z (1, 0)‖ ≤ L := by
    rintro ⟨s, t⟩ hz
    obtain ⟨t', ht', heq⟩ :=
      (periodic_fderiv_mk_of_isOpen (𝕜 := ℝ) (x := s) isOpen_Ioi hper hz.1).exists_mem_Ico₀
        one_pos t
    rw [heq]
    exact hL (s, t') ⟨hz.1, Ico_subset_Icc_self ht'⟩
  -- The energy of `[s, ∞) × [0, 1]` decays exponentially; this gives the decay of the loops and of
  -- `∂ₛu`.
  obtain ⟨κ, hκ, C₁, hC₁⟩ := exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp hH2
    hHper hu₂ hper hc hJc hJM' hfloer' hE hxper hx hnd hux
  obtain ⟨C₀, hC₀⟩ := exists_eventually_norm_sub_le_exp_of_setLIntegral_le_exp hH2
    (hu₂.of_le (by norm_num)) hper hc hJc hJM' hfloer' hL hxper hx hnd hux hC₁
  obtain ⟨D, hD₀, hv⟩ := exists_eventually_norm_fderiv_apply_one_zero_sq_le_exp hε hH hu hper hc
    hJc hJM hJ hJ₁ hJ₂ hfloer hL' hxc hux hC₁
  -- `X_{H_t}` is uniformly Lipschitz near the orbit, for `t ∈ [0, 1]`.
  obtain ⟨δ₁, hδ₁, Lx, hLx⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_pos_forall_norm_sub_le_mul
      (F := fun t y ↦ ω.hamiltonianVectorField (H t) y)
      (fun _ _ ↦ (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH2).contDiffAt)
      hxc.continuousOn
  -- Assemble the `C¹` estimate at the rate `κ / 3` of the loops.
  set C₀' := max C₀ 0
  set Lx' := max Lx 0
  set a' := max M 0
  have hC₀' : 0 ≤ C₀' := le_max_right _ _
  have hLx' : 0 ≤ Lx' := le_max_right _ _
  have ha' : 0 ≤ a' := le_max_right _ _
  have hsD : 0 ≤ √D := Real.sqrt_nonneg _
  refine ⟨κ / 3, by positivity, C₀' + (1 + a') * √D + Lx' * C₀', ?_⟩
  filter_upwards [hC₀, hv, eventually_ge_atTop 0, eventually_gt_atTop a,
    (Metric.tendstoUniformly_iff.1 hux δ₁ hδ₁)] with s hs0 hvs hspos hsa hδs
  -- By periodicity in `t`, it suffices to treat `t ∈ [0, 1]`.
  refine norm_sub_le_and_norm_fderiv_sub_smulRight_le_of_forall_mem_Icc hHper hper hxper hsa
    fun t ht ↦ ?_
  have he' : 0 < Real.exp (-(κ / 3 * s)) := Real.exp_pos _
  -- The `C⁰` part.
  have hux0 : ‖u (s, t) - x t‖ ≤ C₀' * Real.exp (-(κ / 3 * s)) :=
    (hs0 t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he'.le)
  -- The `∂ₛ` part.
  have hvs' : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ √D * Real.exp (-(κ / 3 * s)) := by
    have hrhs : (√D * Real.exp (-(κ / 3 * s))) ^ 2 = D * Real.exp (-(2 * (κ / 3) * s)) := by
      rw [mul_pow, Real.sq_sqrt hD₀, ← Real.exp_natCast_mul]; ring_nf
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hrhs]
    exact (hvs t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hD₀)
  -- The `∂ₜ` part: `∂ₜu - X_{H_t}(x) = J ∂ₛu + X_{H_t}(u) - X_{H_t}(x)`.
  have hd : ‖fderiv ℝ u (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (ω.hamiltonianVectorField (H t) (x t))‖ ≤
      (1 + a') * ‖fderiv ℝ u (s, t) (1, 0)‖ + Lx' * ‖u (s, t) - x t‖ :=
    (ω.norm_fderiv_sub_smulRight_le_of_floer (ω.hamiltonianVectorField (H t) (x t))
      (fun v ↦ (hJM (s, t) ⟨hsa, hIcc ht⟩ v).trans
        (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg _)))
      (hfloer _ ⟨hsa, hIcc ht⟩)).trans (add_le_add le_rfl
      ((hLx t ht _ (by rw [← dist_eq_norm, dist_comm]; exact (hδs t).le)).trans
        (mul_le_mul_of_nonneg_right (le_max_left Lx 0) (norm_nonneg _))))
  refine ⟨hux0.trans (mul_le_mul_of_nonneg_right (by nlinarith) he'.le), hd.trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hvs' (by positivity : (0 : ℝ) ≤ 1 + a'),
    mul_le_mul_of_nonneg_left hux0 hLx']

end TauCeti.SymplecticForm
