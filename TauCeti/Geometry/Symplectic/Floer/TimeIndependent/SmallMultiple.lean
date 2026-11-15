/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallHamiltonian
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.ReProdIm
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Floer cylinders of small multiples of a Hamiltonian are gradient lines

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `g = ω(·, J ·)` of a
constant compatible almost complex structure `J`, let `H : V → ℝ` be a `C³` autonomous Hamiltonian
and `K ⊆ V` compact. For `δ ∈ ℝ` consider the Floer equation `∂s u + J (∂t u - δ X_H(u)) = 0` of the
perturbation `K = δ H dt`, for maps `u` of period one in `t` with image in `K`. Its energy density
is `‖∂s u‖²` (`TauCeti.SymplecticForm.floerEnergyDensity_eq_norm_fderiv_stdComplexLineReal_sq`).

`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv` shows that such a
solution does not depend on `t` once `‖du‖ ≤ M` with `c M < 2 (2π - a)²`, where `a` and `c` bound
the first two derivatives of the Hamiltonian vector field. For the Hamiltonian `δ H` both `a` and
`c` are proportional to `|δ|`, so the condition holds for all small `δ` as soon as `M` does not
depend on `δ`. This file supplies that bound.

* **A priori bound.** There are an energy `ε > 0` and a bound `M` such that every solution with
  `|δ| ≤ R` and energy at most `ε` over `ℝ × [0, 1]` has `‖du‖ ≤ M` everywhere
  (`TauCeti.SymplecticForm.exists_pos_forall_norm_fderiv_le_of_small_energy`). Read in the complex
  coordinate `z = s + i t`, the solutions solve the coordinate equation of
  `TauCeti.Geometry.Symplectic.Floer.Compactness.Basic` with data depending on the parameter `δ`,
  so the mean-value inequality has a threshold uniform over `|δ| ≤ R`
  (`Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric`).
  The data do not depend on the domain point, so it applies on a disc of a fixed small radius about
  every point. Since `u` is periodic in `t`, the energy over such a disc is at most twice the energy
  over `ℝ × [0, 1]` (`Function.Periodic.setIntegral_ball_le_two_mul`). This bounds `∂s u`, and the
  equation `∂t u = δ X_H(u) + J ∂s u` bounds `∂t u`.
* **Small multiples.** There are `ε > 0` and `δ₀ > 0` such that for `|δ| ≤ δ₀` every such solution
  of energy at most `ε` is independent of `t`, and `γ(s) = u(s, 0)` is a gradient line,
  `γ' = δ ∇H(γ)`
  (`SymplecticForm.exists_pos_forall_eq_comp_fst_and_hasDerivAt_of_small_energy`).
  The time-independence theorem needs bounds on the derivatives of `X_H` over all of `V`; these
  hold after replacing `H` by `χ H` for a bump function `χ` equal to `1` near `K`, which does not
  change the equation along `u`.

The energy condition holds for the Floer trajectories of `δ H` that the comparison with Morse
theory counts. A finite-energy solution with loops in `K` has energy equal to the difference of the
actions of its asymptotic orbits
(`TauCeti.SymplecticForm.exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_eq`). Between
constant orbits at critical points of `H` this is `δ` times a difference of values of `H` on `K`,
hence at most `ε` once `|δ|` is small. So for small `δ` the Floer trajectories of `δ H` between
critical points, with image in `K`, are gradient lines of `δ H`. This is the analytic step in the
identification of the Floer trajectories of a small Hamiltonian with its gradient trajectories.
Domain- or target-dependent `J` are not treated here.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, Section 7.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.3
  (the mean-value inequality).
-/

public section

open Complex Filter Function Metric MeasureTheory Set Topology
open scoped Gradient RealInnerProductSpace Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {K : Set V}
  {u : ℝ × ℝ → V}

/-- For the metric `g = ω(·, J ·)`, the Floer energy density of a solution of the Floer equation of
a perturbation `K_t dt` is `‖∂s u‖²`. -/
theorem floerEnergyDensity_eq_norm_fderiv_stdComplexLineReal_sq
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {Kt : ℝ × ℝ → V → ℝ} {z : ℝ × ℝ}
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) Kt u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) Kt u z = ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 := by
  rw [ω.floerEnergyDensity_eq_of_isComplexLinearMap hfl, hg, real_inner_self_eq_norm_sq]
  simp [hamiltonianVectorField_const]

/-- The coefficient `X_δ(z, x) = X_K(e z, x) ∘ e` of the Floer equation of `K = δ H dt`, read in the
complex coordinate `e = equivRealProdCLM`. -/
private noncomputable def coordinateCoefficient (ω : SymplecticForm V) (H : V → ℝ) (δ : ℝ)
    (q : ℂ × V) : ℂ →L[ℝ] V :=
  (ω.hamiltonianOneForm (fun _ _ ↦ 0) (fun _ y ↦ δ * H y) (equivRealProdCLM q.1) q.2).comp
    (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)

private theorem coordinateCoefficient_apply (δ : ℝ) (q : ℂ × V) (ξ : ℂ) :
    coordinateCoefficient ω H δ q ξ = (ξ.im * δ) • ω.hamiltonianVectorField H q.2 := by
  simp [coordinateCoefficient, hamiltonianVectorField_const, hamiltonianVectorField_const_mul,
    smul_smul]

private theorem contDiff_coordinateCoefficient (hH : ContDiff ℝ 3 H) :
    ContDiff ℝ 2 (uncurry (coordinateCoefficient ω H)) := by
  have h := ω.contDiffOn_hamiltonianOneForm (P := ℝ) (Ks := fun _ _ _ ↦ 0)
    (Kt := fun p _ y ↦ p * H y) (n := 2) isOpen_univ contDiffOn_const
    (contDiff_fst.mul (hH.comp (contDiff_snd.comp contDiff_snd))).contDiffOn
  rw [contDiffOn_univ] at h
  exact (h.comp (contDiff_fst.prodMk ((equivRealProdCLM.contDiff.comp
    (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd)))).clm_comp
    contDiff_const

/-- In the complex coordinate, small energy over one period of the plane bounds `∂s`, uniformly
over `|δ| ≤ R`: the mean-value inequality with a threshold uniform in `δ`, on a disc of a fixed
radius about each point. -/
private theorem exists_pos_forall_norm_fderiv_one_le (hH : ContDiff ℝ 3 H) (hK : IsCompact K)
    (R : ℝ) :
    ∃ ε > 0, ∃ Ms, ∀ ⦃δ : ℝ⦄ ⦃v : ℂ → V⦄, |δ| ≤ R → ContDiff ℝ 3 v → Periodic v I →
      (∀ y, fderiv ℝ v y I - coordinateCoefficient ω H δ (y, v y) I =
        J.toLinearMap.toContinuousLinearMap
          (fderiv ℝ v y 1 - coordinateCoefficient ω H δ (y, v y) 1)) →
      (∀ y, v y ∈ K) →
      ∫⁻ y in (univ : Set ℝ) ×ℂ Icc 0 1, ENNReal.ofReal (‖fderiv ℝ v y 1‖ ^ 2) ≤
        ENNReal.ofReal ε →
      ∀ y₀, ‖fderiv ℝ v y₀ 1‖ ≤ Ms := by
  obtain ⟨δmv, hδmv, hmean⟩ :=
    Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy_parametric
      (J := fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (X := coordinateCoefficient ω H)
      (C := Icc (-R) R) (D := closedBall 0 1) isOpen_univ contDiffOn_const
      (contDiff_coordinateCoefficient hH).contDiffOn isCompact_Icc (isCompact_closedBall 0 1) hK
      (subset_univ _) fun _ _ _ _ _ _ v ↦ by simp
  -- Fix a radius `r ≤ 1/2` whose disc area `π r²` is below `δmv / 2`.
  set r : ℝ := min (1 / 2) (δmv / 8)
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hr2 : r ≤ 1 / 2 := min_le_left _ _
  have hπr : π * r ^ 2 < δmv / 2 := by
    nlinarith [Real.pi_le_four, Real.pi_pos, min_le_right (1 / 2 : ℝ) (δmv / 8)]
  have hπr0 : 0 < π * r ^ 2 := by positivity
  refine ⟨δmv / 4, by positivity, 8 + 4 * δmv / (π * r ^ 2),
    fun δ v hδ hv hvper hCR hvK hEv y₀ ↦ ?_⟩
  -- The data do not depend on the domain point, so translate the disc about `y₀` to `0`.
  set w : ℂ → V := fun y ↦ v (y + y₀)
  have hdw (y : ℂ) : fderiv ℝ w y = fderiv ℝ v (y + y₀) := fderiv_comp_add_right y₀
  have hw : ContDiff ℝ 3 w := hv.comp (contDiff_id.add contDiff_const)
  have henergy :
      ∫ y in ball 0 r, ‖fderiv ℝ w y 1‖ ^ 2 = ∫ y in ball y₀ r, ‖fderiv ℝ v y 1‖ ^ 2 := by
    have hpre : (· + y₀) ⁻¹' ball y₀ r = ball 0 r := by simp
    simp_rw [hdw, ← hpre]
    exact (measurePreserving_add_right volume y₀).setIntegral_preimage_emb
      (measurableEmbedding_addRight y₀) (fun y ↦ ‖fderiv ℝ v y 1‖ ^ 2) _
  -- The energy over the disc is at most twice the energy over one period.
  have hball : ∫ y in ball y₀ r, ‖fderiv ℝ v y 1‖ ^ 2 ≤ 2 * (δmv / 4) :=
    (show Periodic (fun y ↦ ‖fderiv ℝ v y 1‖ ^ 2) I from fun y ↦ by
        simp only [hvper.fderiv y]).setIntegral_ball_le_two_mul (fun _ ↦ sq_nonneg _) hr2
      (subset_univ _) (by positivity)
      (((hv.continuous_fderiv (by norm_num)).clm_apply continuous_const).norm.pow 2
        |>.aestronglyMeasurable) hEv
  have hmv := hmean (p := δ) (u := w) (z₀ := 0) (abs_le.1 hδ) hr.le
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    hw.contDiffOn (((hw.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)
    (fun y _ ↦ by simpa only [hdw, coordinateCoefficient_apply] using hCR (y + y₀))
    (fun y _ ↦ hvK _) (by rw [henergy]; linarith)
  rw [henergy, hdw, zero_add] at hmv
  have hsq : ‖fderiv ℝ v y₀ 1‖ ^ 2 ≤ 7 + 4 * δmv / (π * r ^ 2) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hπr0]
    nlinarith
  nlinarith [sq_nonneg (‖fderiv ℝ v y₀ 1‖ - 1)]

/-- **A priori bound for Floer cylinders of small energy.** Let the inner product of `V` be the
metric `ω(·, J ·)` of a constant `J`, let `H` be `C³` and `K ⊆ V` compact, and let `R ∈ ℝ`. There
are an energy `ε > 0` and a bound `M` with the following property. Let `|δ| ≤ R`, and let `u` be a
`C³` solution of the Floer equation `∂s u + J (∂t u - δ X_H(u)) = 0`, of period one in `t`, with
image in `K` and energy at most `ε` over `ℝ × [0, 1]`. Then `‖du‖ ≤ M` everywhere. -/
theorem exists_pos_forall_norm_fderiv_le_of_small_energy (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hK : IsCompact K) (R : ℝ) :
    ∃ ε > 0, ∃ M, ∀ ⦃δ : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, |δ| ≤ R → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ δ * H y) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ δ * H y) u z) ≤
        ENNReal.ofReal ε →
      ∀ z, ‖fderiv ℝ u z‖ ≤ M := by
  obtain ⟨ε, hε, Ms, hMs⟩ := exists_pos_forall_norm_fderiv_one_le (ω := ω) (J := J) hH hK R
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (ω.contDiff_hamiltonianVectorField (n := 0) (hH.of_le (by norm_num))).continuous.continuousOn
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  have heapp (y : ℂ) : e y = (y.re, y.im) := by simp [he]
  refine ⟨ε, hε, (2 * Ms + R * max B 0) * ‖(e.symm : ℝ × ℝ →L[ℝ] ℂ)‖,
    fun δ u hδ hu hper hfl huK hE z₀ ↦ ?_⟩
  -- The solution `v = u ∘ e` in the complex coordinate, and its energy.
  set v : ℂ → V := u ∘ e with hv_def
  have hCR (y : ℂ) : fderiv ℝ v y I - coordinateCoefficient ω H δ (y, v y) I =
      J.toLinearMap.toContinuousLinearMap
        (fderiv ℝ v y 1 - coordinateCoefficient ω H δ (y, v y) 1) :=
    ω.fderiv_comp_equivRealProdCLM_I_sub (J := fun _ _ ↦ J) (hfl (e y))
  have hEv : ∫⁻ y in (univ : Set ℝ) ×ℂ Icc 0 1, ENNReal.ofReal (‖fderiv ℝ v y 1‖ ^ 2) ≤
      ENNReal.ofReal ε := by
    refine le_of_eq_of_le ?_ hE
    rw [← Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      measurableEquivRealProd.measurableEmbedding]
    refine setLIntegral_congr_fun (MeasurableSet.univ.reProdIm measurableSet_Icc) fun y _ ↦ ?_
    rw [floerEnergyDensity_eq_norm_fderiv_stdComplexLineReal_sq hg (hfl _), hv_def,
      fderiv_comp_equivRealProdCLM_one, measurableEquivRealProd_apply, ← heapp]
  set y₀ : ℂ := e.symm z₀
  have hs : ‖fderiv ℝ v y₀ 1‖ ≤ Ms := hMs hδ (hu.comp e.contDiff)
    (fun y ↦ by simp only [comp_apply, heapp, add_re, I_re, add_zero, add_im, I_im, hper])
    hCR (fun _ ↦ huK _) hEv y₀
  -- `∂t v(y₀) = δ X_H(v(y₀)) + J ∂s v(y₀)` is bounded by the equation.
  have ht : ‖fderiv ℝ v y₀ I‖ ≤ Ms + R * max B 0 := by
    have hXH : ‖ω.hamiltonianVectorField H (v y₀)‖ ≤ max B 0 :=
      (hB _ (huK _)).trans (le_max_left _ _)
    rw [← sub_add_cancel (fderiv ℝ v y₀ I) (coordinateCoefficient ω H δ (y₀, v y₀) I), hCR]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [LinearMap.coe_toContinuousLinearMap', ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner
        (fun v ↦ hg v v), coordinateCoefficient_apply, one_im, zero_mul, zero_smul, sub_zero]
      exact hs
    · rw [coordinateCoefficient_apply, I_im, one_mul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hδ hXH (norm_nonneg _) ((abs_nonneg δ).trans hδ)
  -- Finally `du(z₀) = dv(y₀) ∘ e⁻¹`.
  have hdu : fderiv ℝ u z₀ = (fderiv ℝ v y₀).comp (e.symm : ℝ × ℝ →L[ℝ] ℂ) := by
    have h := e.symm.comp_right_fderiv (f := v) (x := z₀)
    rwa [show v ∘ e.symm = u from funext fun p ↦ by simp [hv_def]] at h
  rw [hdu]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  calc ‖fderiv ℝ v y₀‖ ≤ ‖fderiv ℝ v y₀ 1‖ + ‖fderiv ℝ v y₀ I‖ := by
        have h := (fderiv ℝ v y₀).opNorm_le_bound (by positivity)
          (fderiv ℝ v y₀).norm_apply_le_norm_one_add_norm_I
        rwa [RCLike.I_to_complex] at h
    _ ≤ 2 * Ms + R * max B 0 := by linarith

/-- A `C³` Hamiltonian agrees near a compact set with a `C³` Hamiltonian `H' = χ H`, for a bump
function `χ`, whose Hamiltonian vector field has globally bounded first and second derivatives. -/
private theorem exists_eventuallyEq_forall_norm_fderiv_le (hH : ContDiff ℝ 3 H) (hK : IsCompact K) :
    ∃ H' : V → ℝ, ContDiff ℝ 3 H' ∧ (∀ x ∈ K, H' =ᶠ[𝓝 x] H) ∧ ∃ a c, ∀ x,
      ‖fderiv ℝ (ω.hamiltonianVectorField H') x‖ ≤ a ∧
        ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H')) x‖ ≤ c := by
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  let χ : ContDiffBump (0 : V) := ⟨max ρ 0 + 1, max ρ 0 + 2, by positivity, by linarith⟩
  have hH' : ContDiff ℝ 3 fun x ↦ χ x * H x := χ.contDiff.mul hH
  have hX' := ω.contDiff_hamiltonianVectorField (n := 2) hH'
  have hX'c : HasCompactSupport (ω.hamiltonianVectorField fun x ↦ χ x * H x) := by
    have h : ω.hamiltonianVectorField (fun x ↦ χ x * H x) =
        ω.toBilinForm.toContinuousBilinearMap.inverse ∘ fderiv ℝ fun x ↦ χ x * H x :=
      funext (ω.hamiltonianVectorField_def _)
    exact h ▸ (χ.hasCompactSupport.mul_right.fderiv ℝ).comp_left (map_zero _)
  have hdX' := hX'.fderiv_right (m := 1) (by norm_num)
  obtain ⟨a, ha⟩ := hdX'.continuous.bounded_above_of_compact_support (hX'c.fderiv ℝ)
  obtain ⟨c, hc⟩ := (hdX'.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((hX'c.fderiv ℝ).fderiv ℝ)
  refine ⟨_, hH', fun x hx ↦ ?_, a, c, fun x ↦ ⟨ha x, hc x⟩⟩
  -- `χ = 1` on a ball containing `K`.
  have hx : x ∈ ball (0 : V) (max ρ 0 + 1) :=
    mem_ball.2 ((mem_closedBall.1 (hρ hx)).trans_lt (by linarith [le_max_left ρ 0]))
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]

/-- The derivative bounds of `X_H` scale with `δ` for the Hamiltonian `δ H`. -/
private theorem norm_fderiv_hamiltonianVectorField_const_mul_le (hH : ContDiff ℝ 3 H) {a c : ℝ}
    (hac : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a ∧
      ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) (δ : ℝ) (x : V) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun y ↦ δ * H y) x‖ ≤ |δ| * a ∧
      ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField fun y ↦ δ * H y)) x‖ ≤ |δ| * c := by
  have hX := ω.contDiff_hamiltonianVectorField (n := 2) hH
  have hXδ : ω.hamiltonianVectorField (fun y ↦ δ * H y) = δ • ω.hamiltonianVectorField H :=
    funext fun x ↦ ω.hamiltonianVectorField_const_mul δ H x
  have hd1 :
      fderiv ℝ (δ • ω.hamiltonianVectorField H) = δ • fderiv ℝ (ω.hamiltonianVectorField H) :=
    funext fun x ↦ fderiv_const_smul ((hX.differentiable (by norm_num)) x) δ
  have hd2 : fderiv ℝ (δ • fderiv ℝ (ω.hamiltonianVectorField H)) =
      δ • fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) :=
    funext fun x ↦ fderiv_const_smul
      (((hX.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x) δ
  rw [hXδ, hd1, hd2, Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  refine ⟨mul_le_mul_of_nonneg_left (hac x).1 (abs_nonneg δ),
    (ContinuousLinearMap.opNorm_smul_le δ _).trans ?_⟩
  rw [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hac x).2 (abs_nonneg δ)

/-- **Floer cylinders of small multiples of a Hamiltonian are gradient lines.** Let the inner
product of `V` be the metric `ω(·, J ·)` of a constant `J`, let `H` be `C³` and `K ⊆ V` compact.
There are an energy `ε > 0` and a threshold `δ₀ > 0` with the following property. Let `|δ| ≤ δ₀`,
and let `u` be a `C³` solution of the Floer equation `∂s u + J (∂t u - δ X_H(u)) = 0`, of period
one in `t`, with image in `K` and energy at most `ε` over `ℝ × [0, 1]`. Then `u` does not depend on
`t`, and `γ(s) = u(s, 0)` is a gradient line of `δ H`: `γ' = δ ∇H(γ)`. -/
theorem exists_pos_forall_eq_comp_fst_and_hasDerivAt_of_small_energy
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 3 H) (hK : IsCompact K) :
    ∃ ε > 0, ∃ δ₀ > 0, ∀ ⦃δ : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, |δ| ≤ δ₀ → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ δ * H y) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ δ * H y) u z) ≤
        ENNReal.ofReal ε →
      (u = fun z ↦ u (z.1, 0)) ∧ ∀ s, HasDerivAt (fun s ↦ u (s, 0)) (δ • ∇ H (u (s, 0))) s := by
  -- Replace `H` by `H'` equal to `H` near `K`, with global bounds `a`, `c` on `dX_{H'}` and
  -- `d²X_{H'}`.
  obtain ⟨H', hH', hHK, a, c, hac⟩ := exists_eventuallyEq_forall_norm_fderiv_le (ω := ω) hH hK
  obtain ⟨ε, hε, M, hM⟩ := exists_pos_forall_norm_fderiv_le_of_small_energy hg hH hK 1
  set a' := max a 0
  set c' := max c 0
  set M' := max M 0
  set δ₀ := min 1 (min (π / (a' + 1)) (π ^ 2 / (c' * M' + 1)))
  refine ⟨ε, hε, δ₀, by positivity, fun δ u hδ hu hper hfl huK hE ↦ ?_⟩
  have hδ0 : 0 ≤ |δ| := abs_nonneg δ
  have hδa : |δ| * a' ≤ π := by
    have h : |δ| * (a' + 1) ≤ π :=
      (le_div_iff₀ (by positivity)).1 (hδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hδc : |δ| * c' * M' ≤ π ^ 2 := by
    have h : |δ| * (c' * M' + 1) ≤ π ^ 2 :=
      (le_div_iff₀ (by positivity)).1 (hδ.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  have ha2π : |δ| * a' < 2 * π := by linarith [Real.pi_pos]
  have hcM : |δ| * c' * M' < 2 * (2 * π - |δ| * a') ^ 2 := by
    nlinarith [Real.pi_pos, mul_nonneg hδ0 (le_max_right a 0 : 0 ≤ a')]
  have hac' (x : V) := norm_fderiv_hamiltonianVectorField_const_mul_le hH'
    (fun x ↦ ⟨(hac x).1.trans (le_max_left a 0), (hac x).2.trans (le_max_left c 0)⟩) δ x
  have hdu (z : ℝ × ℝ) : ‖fderiv ℝ u z‖ ≤ M' :=
    (hM (hδ.trans (min_le_left _ _)) hu hper hfl huK hE z).trans (le_max_left _ _)
  -- `u` also solves the Floer equation of `δ H'`.
  have hloc (x : V) (hx : x ∈ K) : (fun y ↦ δ * H' y) =ᶠ[𝓝 x] fun y ↦ δ * H y :=
    (hHK x hx).mono fun y hy ↦ congrArg (δ * ·) hy
  have hfl' (z : ℝ × ℝ) : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ δ * H' y) u z : ℝ × ℝ →ₗ[ℝ] V) := by
    have h : ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ δ * H' y) u z =
        ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ δ * H y) u z := by
      refine ContinuousLinearMap.ext fun v ↦ ?_
      simp only [perturbedFDeriv_apply,
        ω.hamiltonianVectorField_congr_of_eventuallyEq (hloc _ (huK z))]
    rw [h]
    exact hfl z
  refine ⟨eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv hg (contDiff_const.mul hH')
    (fun x ↦ (hac' x).1) (fun x ↦ (hac' x).2) ha2π hcM hu hper hfl' hdu, fun s ↦ ?_⟩
  -- The gradient of `δ H'` is `δ ∇H` near `K`.
  have h := hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv hg (contDiff_const.mul hH')
    (fun x ↦ (hac' x).1) (fun x ↦ (hac' x).2) ha2π hcM hu hper hfl' hdu s
  have hgrad : HasGradientAt (fun y ↦ δ * H y) (δ • ∇ H (u (s, 0))) (u (s, 0)) := by
    have hHx := ((hH.differentiable (by norm_num)) (u (s, 0))).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt] at hHx ⊢
    rw [map_smulₛₗ, conj_trivial]
    exact hHx.const_mul δ
  rwa [(hloc _ (huK _)).gradient_eq, hgrad.gradient] at h

end TauCeti.SymplecticForm
