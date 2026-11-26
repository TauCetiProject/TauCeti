/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cutoffs of small Dirichlet energy in dimension two

In a real normed space `E` of dimension two, with an additive Haar measure `μ`, there are smooth
compactly supported cutoffs `χ_k : E → [0, 1]`, equal to `1` on the closed ball of radius `k`,
whose Dirichlet energies `∫ ‖Dχ_k‖² dμ` tend to zero
(`TauCeti.exists_seq_contDiff_cutoff_tendsto_integral_norm_fderiv_sq`). Equivalently, the point
at infinity of the plane, and hence every point of a surface, has capacity zero. On the Riemann
sphere this is why the sections with compact support in the plane `ℂ` are dense in `W^{1,2}` of
the sphere: multiplying a section of finite energy by `χ_k` costs at most `sup ‖ξ‖² ∫ ‖Dχ_k‖²`.

The proof uses that the Dirichlet energy is invariant under dilations in dimension two
(`TauCeti.integral_norm_fderiv_comp_inv_smul_sq`): the derivative of `x ↦ f (R⁻¹ x)` is `R⁻¹`
times that of `f`, and the change of variables `x = R y` multiplies the measure by `R²`. Let `φ`
be a smooth bump equal to `1` on the unit ball and to `0` off the ball of radius `2`, and let
`φ_j (x) = φ (4⁻ʲ x)`, so that every `φ_j` has the energy `e` of `φ`. The derivative of `φ_j`
vanishes off the annulus `4ʲ ≤ ‖x‖ ≤ 2 · 4ʲ`, and these annuli are disjoint, so at each point at
most one `Dφ_j` is nonzero and `‖∑_j Dφ_j‖² = ∑_j ‖Dφ_j‖²`
(`TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_eq_zero_or_eq_zero`). The average
`χ_k = (k + 1)⁻¹ ∑_{j = k}^{2k} φ_j` therefore has energy at most `e / (k + 1)`, while it equals
`1` on the ball of radius `4ᵏ ≥ k`.

In dimension `d` the dilation multiplies the energy by `4^(j(d - 2))`, so the same average has
energy bounded below when `d ≥ 3`; points have positive capacity there.

## References

* L. C. Evans and R. F. Gariepy, *Measure theory and fine properties of functions*, revised ed.,
  CRC Press (2015), Section 4.7, on capacity.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces on closed Riemann surfaces.
-/

public section

open MeasureTheory Filter Topology Module Metric
open scoped ContDiff

namespace TauCeti

/-- If of any two distinct terms of a finite sum one vanishes, the squared norm of the sum is the
sum of the squared norms: at most one term is nonzero. -/
theorem norm_sum_sq_eq_sum_norm_sq_of_pairwise_eq_zero_or_eq_zero {ι F : Type*}
    [SeminormedAddCommGroup F] {s : Finset ι} {v : ι → F}
    (h : (s : Set ι).Pairwise fun i j ↦ v i = 0 ∨ v j = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  by_cases hex : ∃ j ∈ s, v j ≠ 0
  · obtain ⟨j, hj, hne⟩ := hex
    have h0 (i : ι) (hi : i ∈ s) (hij : i ≠ j) : v i = 0 := (h hi hj hij).resolve_right hne
    rw [Finset.sum_eq_single_of_mem j hj fun i hi hij ↦ h0 i hi hij,
      Finset.sum_eq_single_of_mem j hj fun i hi hij ↦ by simp [h0 i hi hij]]
  · simp only [not_exists, not_and, not_not] at hex
    rw [Finset.sum_eq_zero hex, Finset.sum_eq_zero fun i hi ↦ by simp [hex i hi]]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Dirichlet energy is invariant under dilations in dimension two.** For an additive Haar
measure `μ` on a real normed space of dimension two and `R > 0`, the map `x ↦ f (R⁻¹ x)` has the
same Dirichlet energy `∫ ‖Df‖² dμ` as `f`: its derivative is `R⁻¹` times that of `f`, and the
change of variables multiplies the measure by `R²`. -/
theorem integral_norm_fderiv_comp_inv_smul_sq [MeasurableSpace E] [BorelSpace E]
    (hE : finrank ℝ E = 2) (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) {R : ℝ} (hR : 0 < R) :
    ∫ x, ‖fderiv ℝ (fun y ↦ f (R⁻¹ • y)) x‖ ^ 2 ∂μ = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  simp_rw [fderiv_comp_smul (f := f), norm_smul, mul_pow,
    Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg μ (fun y ↦ ‖fderiv ℝ f y‖ ^ 2) hR.le, hE,
    smul_eq_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, one_mul]

/-- The derivative of a bump function centred at `0` vanishes off the closed annulus
`rIn ≤ ‖y‖ ≤ rOut`: the bump is `1` on the open ball of radius `rIn` and `0` outside the closed
ball of radius `rOut`. -/
private theorem rIn_le_norm_and_norm_le_rOut_of_fderiv_ne_zero (φ : ContDiffBump (0 : E)) {y : E}
    (hy : fderiv ℝ φ y ≠ 0) : φ.rIn ≤ ‖y‖ ∧ ‖y‖ ≤ φ.rOut := by
  refine ⟨not_lt.1 fun h ↦ hy ?_, not_lt.1 fun h ↦ hy ?_⟩
  · have : (φ : E → ℝ) =ᶠ[𝓝 y] fun _ ↦ 1 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 h)] with x hx
      exact φ.one_of_mem_closedBall (ball_subset_closedBall hx)
    rw [this.fderiv_eq, fderiv_const_apply]
  · have : (φ : E → ℝ) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with x hx
      exact φ.zero_of_le_dist (by rw [dist_zero_right]; exact hx.le)
    rw [this.fderiv_eq, fderiv_const_apply]

/-- The derivative of the bump `x ↦ φ (R⁻¹ x)` vanishes off the annulus
`R rIn ≤ ‖x‖ ≤ R rOut`. -/
private theorem mul_rIn_le_norm_and_norm_le_mul_rOut (φ : ContDiffBump (0 : E)) {R : ℝ}
    (hR : 0 < R) {x : E} (hx : fderiv ℝ (fun y ↦ φ (R⁻¹ • y)) x ≠ 0) :
    R * φ.rIn ≤ ‖x‖ ∧ ‖x‖ ≤ R * φ.rOut := by
  rw [fderiv_comp_smul (f := (φ : E → ℝ))] at hx
  obtain ⟨h₁, h₂⟩ := rIn_le_norm_and_norm_le_rOut_of_fderiv_ne_zero φ (right_ne_zero_of_smul hx)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)] at h₁ h₂
  exact ⟨(le_inv_mul_iff₀ hR).1 h₁, (inv_mul_le_iff₀ hR).1 h₂⟩

/-- The average `(k + 1)⁻¹ ∑_{j = k}^{2k} φ (4⁻ʲ x)` of the dilations of a bump with radii `1`
and `2` has Dirichlet energy at most `(k + 1)⁻¹` times that of the bump. Every dilation has the
energy of the bump, and their derivatives live on the disjoint annuli `4ʲ ≤ ‖x‖ ≤ 2 · 4ʲ`. -/
private theorem integral_norm_fderiv_average_sq_le [MeasurableSpace E] [BorelSpace E]
    (hE : finrank ℝ E = 2) (μ : Measure E) [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))
    (hφ₁ : φ.rIn = 1) (hφ₂ : φ.rOut = 2) (k : ℕ) :
    ∫ x, ‖fderiv ℝ (fun x ↦ ((k : ℝ) + 1)⁻¹ *
        ∑ j ∈ Finset.range (k + 1), φ (((4 : ℝ) ^ (j + k))⁻¹ • x)) x‖ ^ 2 ∂μ ≤
      ((k : ℝ) + 1)⁻¹ * ∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂μ := by
  set ψ : ℕ → E → ℝ := fun j x ↦ φ (((4 : ℝ) ^ j)⁻¹ • x)
  have h4 (j : ℕ) : (0 : ℝ) < 4 ^ j := by positivity
  have hψs (j : ℕ) : ContDiff ℝ ∞ (ψ j) := φ.contDiff.comp (contDiff_id.const_smul _)
  have hψd (j : ℕ) (x : E) : DifferentiableAt ℝ (ψ j) x :=
    ((hψs j).differentiable (by simp)) x
  have hψi (j : ℕ) : Integrable (fun x ↦ ‖fderiv ℝ (ψ j) x‖ ^ 2) μ := by
    have hc : Continuous fun x ↦ ‖fderiv ℝ (ψ j) x‖ ^ 2 :=
      ((hψs j).continuous_fderiv (by simp)).norm.pow 2
    exact hc.integrable_of_hasCompactSupport
      (((φ.hasCompactSupport.comp_smul (inv_ne_zero (h4 j).ne')).fderiv (𝕜 := ℝ)).comp_left
        (g := fun L ↦ ‖L‖ ^ 2) (by simp))
  -- At each point at most one `Dψ_j` is nonzero, since the annuli are disjoint.
  have hpair (x : E) : ((Finset.range (k + 1) : Finset ℕ) : Set ℕ).Pairwise
      fun a b ↦ fderiv ℝ (ψ (a + k)) x = 0 ∨ fderiv ℝ (ψ (b + k)) x = 0 := by
    have key (a b : ℕ) (hab : a < b) : fderiv ℝ (ψ a) x = 0 ∨ fderiv ℝ (ψ b) x = 0 := by
      by_contra! h
      have ha := (mul_rIn_le_norm_and_norm_le_mul_rOut φ (h4 a) h.1).2
      have hb := (mul_rIn_le_norm_and_norm_le_mul_rOut φ (h4 b) h.2).1
      have h₁ : (4 : ℝ) ^ (a + 1) ≤ 4 ^ b := pow_le_pow_right₀ (by norm_num) hab
      rw [hφ₁, hφ₂] at *
      rw [pow_succ] at h₁
      linarith [h4 a]
    intro a _ b _ hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact key _ _ (by omega)
    · exact (key _ _ (by omega)).symm
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hfd (x : E) : fderiv ℝ (fun x ↦ ((k : ℝ) + 1)⁻¹ *
      ∑ j ∈ Finset.range (k + 1), ψ (j + k) x) x =
      ((k : ℝ) + 1)⁻¹ • ∑ j ∈ Finset.range (k + 1), fderiv ℝ (ψ (j + k)) x := by
    rw [fderiv_const_mul (DifferentiableAt.fun_sum fun j _ ↦ hψd (j + k) x),
      fderiv_fun_sum fun j _ ↦ hψd (j + k) x]
  calc ∫ x, ‖fderiv ℝ (fun x ↦ ((k : ℝ) + 1)⁻¹ *
          ∑ j ∈ Finset.range (k + 1), ψ (j + k) x) x‖ ^ 2 ∂μ
      = ∫ x, ((k : ℝ) + 1)⁻¹ ^ 2 *
          ∑ j ∈ Finset.range (k + 1), ‖fderiv ℝ (ψ (j + k)) x‖ ^ 2 ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [hfd, norm_smul, mul_pow, Real.norm_of_nonneg (inv_nonneg.2 hk.le),
          norm_sum_sq_eq_sum_norm_sq_of_pairwise_eq_zero_or_eq_zero (hpair x)]
    _ = ((k : ℝ) + 1)⁻¹ * ∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hψi (j + k),
          Finset.sum_congr rfl fun j _ ↦ integral_norm_fderiv_comp_inv_smul_sq hE μ φ (h4 _),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, sq,
          mul_assoc, inv_mul_cancel_left₀ hk.ne']
    _ ≤ _ := le_rfl

/-- **Cutoffs of small energy in dimension two.** In a real normed space of dimension two with an
additive Haar measure `μ`, there are smooth compactly supported functions `χ_k` with values in
`[0, 1]`, equal to `1` on the closed ball of radius `k`, whose Dirichlet energies
`∫ ‖Dχ_k‖² dμ` tend to zero. The point at infinity has capacity zero. -/
theorem exists_seq_contDiff_cutoff_tendsto_integral_norm_fderiv_sq [MeasurableSpace E]
    [BorelSpace E] (hE : finrank ℝ E = 2) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ χ : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ (k : ℕ) x, ‖x‖ ≤ k → χ k x = 1) ∧
      Tendsto (fun k ↦ ∫ x, ‖fderiv ℝ (χ k) x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have h4 (j : ℕ) : (0 : ℝ) < 4 ^ j := by positivity
  have hnorm (j : ℕ) (x : E) : ‖((4 : ℝ) ^ j)⁻¹ • x‖ = ((4 : ℝ) ^ j)⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (h4 j).le)]
  refine ⟨fun k x ↦ ((k : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (k + 1), φ (((4 : ℝ) ^ (j + k))⁻¹ • x),
    fun k ↦ contDiff_const.mul (ContDiff.sum fun j _ ↦
      φ.contDiff.comp (contDiff_id.const_smul _)), fun k ↦ ?_, fun k x ↦ ?_, fun k x hx ↦ ?_, ?_⟩
  · -- The cutoff vanishes outside the closed ball of radius `2 · 4^(2k)`.
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * 4 ^ (2 * k))) fun x hx ↦ ?_
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j hj ↦ φ.zero_of_le_dist ?_)
    have hx' : 2 * 4 ^ (2 * k) < ‖x‖ := by simpa using hx
    have : (4 : ℝ) ^ (j + k) ≤ 4 ^ (2 * k) :=
      pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.1 hj; omega)
    rw [dist_zero_right, hnorm]
    exact (le_inv_mul_iff₀ (h4 _)).2 (by simp only [φ]; nlinarith)
  · have hk : (0 : ℝ) < k + 1 := by positivity
    have hle : ∑ j ∈ Finset.range (k + 1), φ (((4 : ℝ) ^ (j + k))⁻¹ • x) ≤ k + 1 :=
      (Finset.sum_le_sum fun j _ ↦ φ.le_one).trans_eq (by simp)
    exact ⟨mul_nonneg (inv_nonneg.2 hk.le) (Finset.sum_nonneg fun j _ ↦ φ.nonneg),
      (inv_mul_le_one₀ hk).2 hle⟩
  · -- On the ball of radius `k ≤ 4ᵏ` every dilated bump is `1`.
    have hk4 : (k : ℝ) ≤ 4 ^ k := by
      exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 4)).le
    have h1 (j : ℕ) : φ (((4 : ℝ) ^ (j + k))⁻¹ • x) = 1 := by
      refine φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 ?_)
      rw [hnorm]
      exact (inv_mul_le_one₀ (h4 _)).2
        (hx.trans (hk4.trans (pow_le_pow_right₀ (by norm_num) (by omega))))
    dsimp only
    rw [Finset.sum_congr rfl fun j _ ↦ h1 j, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ (by positivity)]
  · -- The energy of the `k`-th cutoff is at most `(k + 1)⁻¹` times that of `φ`.
    have hlim : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹ * ∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂μ) atTop
        (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
        (∫ x, ‖fderiv ℝ φ x‖ ^ 2 ∂μ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k ↦ integral_nonneg fun _ ↦ sq_nonneg _)
      (integral_norm_fderiv_average_sq_le hE μ φ rfl rfl)

end TauCeti
