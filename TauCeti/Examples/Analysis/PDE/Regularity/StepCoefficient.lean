/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Interval
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

/-!
# A step coefficient on the unit interval

On `(0, 1)` let `σ = 1 + 1_{(1/2, ∞)}`, equal to `1` on `(0, 1/2]` and to `2` on `(1/2, 1)`. It
is bounded, measurable and uniformly elliptic with constants `λ = 1` and `Λ = 2`, but it jumps at
`1/2`, so it does not have vanishing mean oscillation: on every interval centred at the jump its
mean oscillation is `1/2`.

The `W^{2,2}` theory of the Dirichlet problem

`-σ u'' = 1` on `(0, 1)`, `u ∈ W^{2,2}(0, 1) ∩ W^{1,2}_0(0, 1)`,

does not need that hypothesis in one dimension. The problem has exactly one strong solution, by
the one-dimensional theory
`TauCeti.PDE.existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo`,
which integrates `u'' = -1/σ` twice. The equation alone fixes the second derivative, `u'' = -1` on
`(0, 1/2)` and `u'' = -1/2` on `(1/2, 1)`, so every strong solution, whatever its boundary values,
has

`‖u''‖²_{L²(0, 1)} = 1/2 + 1/8 = 5/8`.

The datum `1` has norm `1` in `L²(0, 1)`, so the estimate `‖u''‖ ≤ C ‖f‖` holds for it with
`C = √(5/8)`, below the constant `1/λ = 1` given by the pointwise bound
`|u''| = |f| / σ ≤ |f| / λ` that the equation implies. (The one-dimensional estimate
`TauCeti.PDE.norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo` bounds the full `W^{2,2}` norm,
with constant `(1 + 2 (b - a) + 2 (b - a)²) / λ = 5` here.) In dimension at least two a
coefficient without vanishing mean oscillation can destroy `W^{2,p}` regularity
(`TauCeti.PDE.not_memVMO_radialCoefficient_apply_self` and the counterexample beside it); on an
interval it cannot.

## Main declarations

In the namespace `TauCeti.Examples.StepCoefficientInterval`:

* `stepCoefficient`: the coefficient `σ = 1 + 1_{(1/2, ∞)}`.
* `not_memVMO_stepCoefficient`: `σ` does not have vanishing mean oscillation.
* `existsUnique_firstOrder_mem_w1p0Submodule_and_neg_stepCoefficient_mul_iteratedGradient_eq_one`:
  the Dirichlet problem
  `-σ u'' = 1` has exactly one strong solution in `W^{2,2}(0, 1) ∩ W^{1,2}_0(0, 1)`.
* `norm_iteratedGradient_eq_of_neg_stepCoefficient_mul_eq_one`: every strong solution of
  `-σ u'' = 1` on `(0, 1)` has `‖u''‖_{L²(0, 1)} = √(5/8)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 9, for the `W^{2,p}` theory of strong solutions.
* F. Chiarenza, M. Frasca, P. Longo, *Interior `W^{2,p}` estimates for non divergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. 40 (1991), 149–168, for the theory
  with coefficients of vanishing mean oscillation.
-/

public section

noncomputable section

namespace TauCeti.Examples.StepCoefficientInterval

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- The step coefficient `σ = 1 + 1_{(1/2, ∞)}` on the line: `1` up to `1/2` and `2` after. -/
def stepCoefficient (x : ℝ) : ℝ :=
  1 + (Ioi (1 / 2 : ℝ)).indicator 1 x

/-- The step coefficient is `1` at and before `1/2`. -/
theorem stepCoefficient_of_le {x : ℝ} (hx : x ≤ 1 / 2) : stepCoefficient x = 1 := by
  rw [stepCoefficient, indicator_of_notMem (notMem_Ioi.2 hx), add_zero]

/-- The step coefficient is `2` after `1/2`. -/
theorem stepCoefficient_of_lt {x : ℝ} (hx : 1 / 2 < x) : stepCoefficient x = 2 := by
  rw [stepCoefficient, indicator_of_mem (mem_Ioi.2 hx), Pi.one_apply]
  norm_num

/-- The step coefficient takes only the values `1` and `2`. -/
theorem stepCoefficient_eq_one_or_eq_two (x : ℝ) :
    stepCoefficient x = 1 ∨ stepCoefficient x = 2 := by
  rcases le_or_gt x (1 / 2) with hx | hx
  · exact Or.inl (stepCoefficient_of_le hx)
  · exact Or.inr (stepCoefficient_of_lt hx)

/-- The lower ellipticity bound `λ = 1`. -/
theorem one_le_stepCoefficient (x : ℝ) : 1 ≤ stepCoefficient x := by
  rcases stepCoefficient_eq_one_or_eq_two x with h | h <;> norm_num [h]

/-- The upper bound `Λ = 2`. -/
theorem stepCoefficient_le_two (x : ℝ) : stepCoefficient x ≤ 2 := by
  rcases stepCoefficient_eq_one_or_eq_two x with h | h <;> norm_num [h]

/-- The step coefficient is measurable. -/
theorem measurable_stepCoefficient : Measurable stepCoefficient :=
  measurable_const.add (measurable_const.indicator measurableSet_Ioi)

/-! ### The step coefficient is not of vanishing mean oscillation -/

/-- An integral of `F ∘ σ` over an interval `(a, b]` containing the jump: `σ` is `1` on `(a, 1/2]`
and `2` on `(1/2, b]`. -/
private theorem setIntegral_Ioc_comp_stepCoefficient (F : ℝ → ℝ) {a b : ℝ} (ha : a ≤ 1 / 2)
    (hb : 1 / 2 ≤ b) :
    ∫ x in Ioc a b, F (stepCoefficient x) = (1 / 2 - a) * F 1 + (b - 1 / 2) * F 2 := by
  have h1 : EqOn (fun x => F (stepCoefficient x)) (fun _ => F 1) (Ioc a (1 / 2)) :=
    fun x hx => by simp only [stepCoefficient_of_le hx.2]
  have h2 : EqOn (fun x => F (stepCoefficient x)) (fun _ => F 2) (Ioc (1 / 2) b) :=
    fun x hx => by simp only [stepCoefficient_of_lt hx.1]
  rw [← Ioc_union_Ioc_eq_Ioc ha hb, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc
      (IntegrableOn.congr_fun (integrableOn_const measure_Ioc_lt_top.ne) h1.symm measurableSet_Ioc)
      (IntegrableOn.congr_fun (integrableOn_const measure_Ioc_lt_top.ne) h2.symm measurableSet_Ioc),
    setIntegral_congr_fun measurableSet_Ioc h1, setIntegral_congr_fun measurableSet_Ioc h2]
  simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, max_eq_left (sub_nonneg.2 ha),
    max_eq_left (sub_nonneg.2 hb)]

/-- On the interval `(1/2 - r, 1/2 + r)` centred at the jump, the step coefficient has
average `3/2`. -/
private theorem setAverage_ball_stepCoefficient {r : ℝ} (hr : 0 < r) :
    ⨍ z in ball (1 / 2 : ℝ) r, stepCoefficient z = 3 / 2 := by
  have h := setIntegral_Ioc_comp_stepCoefficient (fun s => s) (a := 1 / 2 - r) (b := 1 / 2 + r)
    (by linarith) (by linarith)
  rw [Real.ball_eq_Ioo, setAverage_eq, setIntegral_congr_set Ioo_ae_eq_Ioc, h, Real.volume_real_Ioo,
    max_eq_left (by linarith), smul_eq_mul]
  field_simp
  ring

/-- The mean oscillation of the step coefficient on the interval `(1/2 - r, 1/2 + r)` centred at
the jump is `1/2`, however small `r > 0` is. -/
theorem setLAverage_enorm_sub_setAverage_ball_stepCoefficient {r : ℝ} (hr : 0 < r) :
    ⨍⁻ y in ball (1 / 2 : ℝ) r,
        ‖stepCoefficient y - ⨍ z in ball (1 / 2 : ℝ) r, stepCoefficient z‖ₑ = 2⁻¹ := by
  rw [setAverage_ball_stepCoefficient hr]
  have h (y : ℝ) : ‖stepCoefficient y - 3 / 2‖ₑ = 2⁻¹ := by
    have habs : |stepCoefficient y - 3 / 2| = 2⁻¹ := by
      rcases stepCoefficient_eq_one_or_eq_two y with h | h <;> norm_num [h]
    rw [← ofReal_norm, Real.norm_eq_abs, habs, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  simp_rw [h]
  refine setLAverage_const ?_ ?_ _
  · rw [Real.volume_ball]
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  · rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top

/-- **The step coefficient does not have vanishing mean oscillation**: its VMO modulus is at least
`1/2` at every scale, because of the jump at `1/2`. -/
theorem not_memVMO_stepCoefficient : ¬ MemVMO stepCoefficient volume := by
  intro h
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), (2⁻¹ : ℝ≥0∞) ≤ vmoModulus stepCoefficient volume r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← setLAverage_enorm_sub_setAverage_ball_stepCoefficient hr]
    exact setLAverage_enorm_sub_setAverage_le_vmoModulus _ _ _ le_rfl
  have := ge_of_tendsto h.tendsto_vmoModulus hle
  simp at this

/-! ### The Dirichlet problem `-σ u'' = 1` -/

/-- **The Dirichlet problem for the step coefficient.** There is exactly one `u ∈ W^{2,2}(0, 1)`
with first-order part in `W^{1,2}_0(0, 1)` solving `-σ u'' = 1` almost everywhere on `(0, 1)`,
although `σ` does not have vanishing mean oscillation. -/
theorem
    existsUnique_firstOrder_mem_w1p0Submodule_and_neg_stepCoefficient_mul_iteratedGradient_eq_one :
    ∃! u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2,
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 ∧
        ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
          -(stepCoefficient x * Wkp.iteratedGradient 1 u x 1) = 1 := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := memLp_const 1
  obtain ⟨u, hu, huniq⟩ :=
    PDE.existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo
      ENNReal.ofNat_ne_top zero_lt_one measurable_stepCoefficient.aestronglyMeasurable one_pos
      (ae_of_all _ one_le_stepCoefficient) (MemLp.toLp _ h1)
  have hiff (v : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2) :
      (∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
          -(stepCoefficient x * Wkp.iteratedGradient 1 v x 1) = MemLp.toLp _ h1 x) ↔
        ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
          -(stepCoefficient x * Wkp.iteratedGradient 1 v x 1) = 1 := by
    refine ⟨fun hv => ?_, fun hv => ?_⟩ <;>
    · filter_upwards [hv, h1.coeFn_toLp] with x hx hx1
      rw [hx, hx1]
  refine ⟨u, ⟨hu.1, (hiff u).1 hu.2⟩, fun v hv => huniq v ⟨hv.1, (hiff v).2 hv.2⟩⟩

/-- **The second derivative for the step coefficient.** Every `u ∈ W^{2,2}(0, 1)` solving
`-σ u'' = 1` almost everywhere on `(0, 1)` has `‖u''‖_{L²(0, 1)} = √(5/8)`: the equation forces
`u'' = -1` on `(0, 1/2)` and `u'' = -1/2` on `(1/2, 1)`. Since the datum `1` has norm `1` in
`L²(0, 1)`, this is below the constant `1/λ = 1` of the bound `‖u''‖ ≤ ‖f‖ / λ`, which follows
from the pointwise bound `|u''| = |f| / σ ≤ |f| / λ` implied by the equation. No boundary condition
is needed. -/
theorem norm_iteratedGradient_eq_of_neg_stepCoefficient_mul_eq_one
    {u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      -(stepCoefficient x * Wkp.iteratedGradient 1 u x 1) = 1) :
    ‖Wkp.iteratedGradient 1 u‖ = √(5 / 8) := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  set g : ℝ → ℝ := fun x => (stepCoefficient x)⁻¹
  -- Pointwise `‖u''‖ = 1 / σ`.
  have hD : ∀ᵐ x ∂μ, ‖Wkp.iteratedGradient 1 u x‖ = ‖g x‖ := by
    filter_upwards [hu] with x hx
    have hσ : stepCoefficient x ≠ 0 := (one_pos.trans_le (one_le_stepCoefficient x)).ne'
    rw [← (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).symm.norm_map,
      ContinuousLinearMap.toSpanSingletonLIE_symm_apply]
    have : Wkp.iteratedGradient 1 u x 1 = -g x := by
      simp only [g]
      field_simp
      linear_combination -hx
    rw [this, norm_neg]
  have hg : MemLp g 2 μ := by
    refine MemLp.of_bound (measurable_stepCoefficient.inv.aestronglyMeasurable) 1
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans (one_le_stepCoefficient x)))]
    exact inv_le_one_of_one_le₀ (one_le_stepCoefficient x)
  -- `∫ (1 / σ)² = 1/2 + 1/8` over `(0, 1/2] ∪ (1/2, 1)`.
  have hint : ∫ x, g x ^ 2 ∂μ = 5 / 8 := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
      setIntegral_Ioc_comp_stepCoefficient (fun s => s⁻¹ ^ 2) (by norm_num) (by norm_num)]
    norm_num
  have hE : eLpNorm (Wkp.iteratedGradient 1 u) 2 μ = ENNReal.ofReal √(5 / 8) := by
    rw [eLpNorm_congr_norm_ae (μ := μ) (Lp.aestronglyMeasurable _) hg.aestronglyMeasurable hD,
      hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp [hint, Real.sqrt_eq_rpow]
  rw [Lp.norm_def]
  exact (congrArg ENNReal.toReal hE).trans (ENNReal.toReal_ofReal (Real.sqrt_nonneg _))

end TauCeti.Examples.StepCoefficientInterval
