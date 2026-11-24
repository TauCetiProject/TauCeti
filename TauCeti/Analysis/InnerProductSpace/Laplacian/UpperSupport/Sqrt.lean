/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.UpperSupport.Basic
import TauCeti.Analysis.Normed.Module.SqrtExpansion
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Smooth touching upper supports from square-root inequalities

One-sided quadratic expansions for scalar functions `F j`, together with `f ≤ √(F j)` near a
point, give a smooth local upper support touching `f` there. The scales only need to tend to
the positive contact value; they are eventually positive without a separate lower-bound
hypothesis. Scaled linear bounds control the derivative norm at the contact point, and a
convergent bound on the normalized bilinear trace controls the Laplacian there. The full
negative rank-one contribution to that trace is retained. The family may use any nontrivial
filter, and no differentiability of `f` or `F j` is assumed.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorems 3.27–3.29:
  the Euclidean analytic step for distance support barriers used in localization.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Filter Topology InnerProductSpace Laplacian
open scoped ContDiff

namespace TauCeti

section OperatorBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical operator norm used for bilinear coefficient estimates. -/
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical scalar action on linear coefficients. -/
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private theorem sqrt_jet_norm_bounds
    (L : E →L[ℝ] ℝ) (Q : E →L[ℝ] E →L[ℝ] ℝ) {d c M L₀ B : ℝ}
    (hd : 0 < d) (hdc : d ≤ c) (hL : ‖L‖ ≤ 2 * M * c) (hL₀ : ‖L‖ ≤ L₀)
    (hQ : ‖Q‖ ≤ B) :
    ‖(2 * c)⁻¹ • L‖ ≤ M ∧
      ‖(2 * c)⁻¹ • Q - (4 * c ^ 3)⁻¹ • L.smulRight L‖ ≤
        B / (2 * d) + L₀ ^ 2 / (4 * d ^ 3) := by
  have hc : 0 < c := hd.trans_le hdc
  have hT : ‖L.smulRight L‖ ≤ L₀ ^ 2 := by
    rw [L.norm_smulRight_apply, ← sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hL₀ 2
  constructor
  · erw [norm_inv_smul_of_nonneg (by positivity)]
    calc
      ‖L‖ / (2 * c) ≤ (2 * M * c) / (2 * c) :=
        div_le_div_of_nonneg_right hL (by positivity)
      _ = M := by field_simp [hc.ne']
  · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · have heq : ‖(2 * c)⁻¹ • Q‖ = ‖Q‖ / (2 * c) := by
        simpa +instances only using
          norm_inv_smul_of_nonneg (z := Q) (by positivity : 0 ≤ 2 * c)
      rw [heq]
      exact div_le_div₀ ((norm_nonneg _).trans hQ) hQ (by positivity) (by gcongr)
    · have heq : ‖(4 * c ^ 3)⁻¹ • L.smulRight L‖ = ‖L.smulRight L‖ / (4 * c ^ 3) := by
        simpa +instances only using
          norm_inv_smul_of_nonneg (z := L.smulRight L) (by positivity : 0 ≤ 4 * c ^ 3)
      rw [heq]
      exact div_le_div₀ (sq_nonneg _) hT (by positivity) (by gcongr)

private theorem eventually_le_sqrt_jet
    {κ : Type*} {l : Filter κ} (f : E → ℝ) (x₀ : E) (F : κ → E → ℝ)
    (c : κ → ℝ) (L : κ → E →L[ℝ] ℝ) (Q : κ → E →L[ℝ] E →L[ℝ] ℝ)
    (d L₀ B ρ₀ C₀ : ℝ) (hd : 0 < d) (hρ₀ : 0 < ρ₀)
    (hc : ∀ᶠ j in l, d ≤ c j) (hL : ∀ᶠ j in l, ‖L j‖ ≤ L₀)
    (hQ : ∀ᶠ j in l, ‖Q j‖ ≤ B)
    (herror : ∀ᶠ j in l, ∀ x, dist x x₀ < ρ₀ → F j x ≤ c j ^ 2 + L j (x - x₀) +
      Q j (x - x₀) (x - x₀) / 2 + C₀ * ‖x - x₀‖ ^ 3)
    (hmajor : ∀ᶠ j in l, ∀ x, dist x x₀ < ρ₀ → f x ≤ Real.sqrt (F j x)) :
    ∀ μ > 0, ∀ᶠ x in 𝓝 x₀, ∀ᶠ j in l, f x ≤ c j + ((2 * c j)⁻¹ • L j) (x - x₀) +
      (1 / 2 : ℝ) * ((2 * c j)⁻¹ • Q j -
        (4 * c j ^ 3)⁻¹ • (L j).smulRight (L j)) (x - x₀) (x - x₀) +
      μ * ‖x - x₀‖ ^ 2 := by
  obtain ⟨C, hC, hsqrt⟩ := exists_forall_sqrt_le_quadratic_add_cubic d L₀ B C₀ hd
  intro μ hμ
  let r := min ρ₀ (min 1 (μ / (C + 1)))
  have hr : 0 < r := lt_min hρ₀ (lt_min zero_lt_one (by positivity))
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with x hx
  have hn : ‖x - x₀‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hxρ : dist x x₀ < ρ₀ := (dist_eq_norm x x₀).symm ▸ hn.trans_le (min_le_left _ _)
  have hn1 : ‖x - x₀‖ ≤ 1 :=
    hn.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hCμ : C * ‖x - x₀‖ ≤ μ := by
    have h := (le_div_iff₀ (by positivity : 0 < C + 1)).mp
      (hn.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith [norm_nonneg (x - x₀)]
  have hsmall : C * ‖x - x₀‖ ^ 3 ≤ μ * ‖x - x₀‖ ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hCμ (sq_nonneg ‖x - x₀‖)]
  filter_upwards [hc, hL, hQ, herror, hmajor] with j hjc hjL hjQ hjerror hjmajor
  have hs := (hjmajor x hxρ).trans
    (hsqrt (x - x₀) (c j) (F j x) (L j) (Q j) hjc hjL hjQ hn1 (hjerror x hxρ))
  have heq : c j + ((2 * c j)⁻¹ • L j) (x - x₀) +
      (1 / 2 : ℝ) * ((2 * c j)⁻¹ • Q j -
        (4 * c j ^ 3)⁻¹ • (L j).smulRight (L j)) (x - x₀) (x - x₀) =
      c j + L j (x - x₀) / (2 * c j) + Q j (x - x₀) (x - x₀) / (4 * c j) -
        (L j (x - x₀)) ^ 2 / (8 * c j ^ 3) := by
    simp only [sub_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply]
    field_simp [(hd.trans_le hjc).ne']
    ring
  rw [← heq] at hs
  exact hs.trans (add_le_add le_rfl hsmall)

end OperatorBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- One-sided square-root upper expansions yield a smooth touching local upper support.
At `x₀` its derivative norm is at most `M` and its Laplacian is at most `Λ + ε`; the normalized
trace bound retains the full rank-one subtraction. -/
theorem exists_contDiff_apply_eq_ge_norm_fderiv_le_laplacian_le_of_le_sqrt
    {κ : Type*} {l : Filter κ} [l.NeBot] (f : E → ℝ) (x₀ : E)
    (F : κ → E → ℝ) (c b : κ → ℝ) (L : κ → E →L[ℝ] ℝ)
    (Q : κ → E →L[ℝ] E →L[ℝ] ℝ) (M B ρ₀ C₀ Λ : ℝ)
    (hf : 0 < f x₀) (hρ₀ : 0 < ρ₀) (hc : Tendsto c l (𝓝 (f x₀)))
    (hb : Tendsto b l (𝓝 Λ)) (hL : ∀ᶠ j in l, ‖L j‖ ≤ 2 * M * c j)
    (hQ : ∀ᶠ j in l, ‖Q j‖ ≤ B)
    (htrace : ∀ᶠ j in l,
      traceL ((2 * c j)⁻¹ • Q j - (4 * c j ^ 3)⁻¹ • (L j).smulRight (L j)) ≤ b j)
    (herror : ∀ᶠ j in l, ∀ x, dist x x₀ < ρ₀ → F j x ≤ c j ^ 2 + L j (x - x₀) +
      Q j (x - x₀) (x - x₀) / 2 + C₀ * ‖x - x₀‖ ^ 3)
    (hmajor : ∀ᶠ j in l, ∀ x, dist x x₀ < ρ₀ → f x ≤ Real.sqrt (F j x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x₀ = f x₀ ∧ (∀ᶠ x in 𝓝 x₀, f x ≤ P x) ∧
      ‖fderiv ℝ P x₀‖ ≤ M ∧ Δ P x₀ ≤ Λ + ε := by
  have hd : 0 < f x₀ / 2 := half_pos hf
  have hcb : ∀ᶠ j in l, f x₀ / 2 ≤ c j ∧ c j ≤ 2 * f x₀ :=
    hc.eventually (Icc_mem_nhds (by linarith) (by linarith))
  let L₀ := 4 * max M 0 * f x₀
  have hLb : ∀ᶠ j in l, ‖L j‖ ≤ L₀ := by
    filter_upwards [hL, hcb] with j hj hjc
    have hcj : 0 < c j := hd.trans_le hjc.1
    calc
      ‖L j‖ ≤ 2 * M * c j := hj
      _ ≤ 2 * max M 0 * c j := by gcongr; exact le_max_left _ _
      _ ≤ 2 * max M 0 * (2 * f x₀) := by gcongr; exact hjc.2
      _ = L₀ := by dsimp [L₀]; ring
  let A := fun j ↦ (2 * c j)⁻¹ • L j
  let H := fun j ↦ (2 * c j)⁻¹ • Q j - (4 * c j ^ 3)⁻¹ • (L j).smulRight (L j)
  have hnorm : ∀ᶠ j in l, ‖A j‖ ≤ M ∧
      ‖H j‖ ≤ B / (2 * (f x₀ / 2)) + L₀ ^ 2 / (4 * (f x₀ / 2) ^ 3) := by
    filter_upwards [hL, hLb, hQ, hcb] with j hjL hjLb hjQ hjc
    exact sqrt_jet_norm_bounds (L j) (Q j) hd hjc.1 hjL hjLb hjQ
  exact exists_contDiff_apply_eq_ge_norm_fderiv_le_laplacian_le f x₀ c b A H M
    (B / (2 * (f x₀ / 2)) + L₀ ^ 2 / (4 * (f x₀ / 2) ^ 3)) Λ hc hb
    (hnorm.mono fun _ h ↦ h.1) (hnorm.mono fun _ h ↦ h.2) htrace
    (eventually_le_sqrt_jet f x₀ F c L Q (f x₀ / 2) L₀ B ρ₀ C₀ hd hρ₀
      (hcb.mono fun _ h ↦ h.1) hLb hQ herror hmajor) hε

end TauCeti
