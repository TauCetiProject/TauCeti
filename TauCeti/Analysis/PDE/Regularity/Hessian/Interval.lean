/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Sobolev.Wkp.Interval

/-!
# The `W^{2,p}` Dirichlet problem on an interval

Let `a < b`, `1 ≤ p < ∞`, and let `σ` be a measurable coefficient on `(a, b)` with `λ ≤ σ` almost
everywhere for some `λ > 0`. This file proves that for every `f ∈ Lᵖ(a, b)` the Dirichlet problem

`-σ u'' = f` on `(a, b)`, `u ∈ W^{2,p}(a, b) ∩ W^{1,p}_0(a, b)`,

has exactly one strong solution
(`TauCeti.PDE.existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo`),
and that every strong solution satisfies the global estimate

`‖u‖_{W^{2,p}(a, b)} ≤ (1 + 2 (b - a) + 2 (b - a)²) / λ · ‖f‖_{Lᵖ(a, b)}`

(`TauCeti.PDE.norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo`), which holds for `p = ∞` as well.
Here `u''` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` evaluated in the direction `1`.

This is the one-dimensional case of the global `W^{2,p}` theory of non-divergence-form equations
`-aⁱʲ ∂ᵢ∂ⱼ u = f` on bounded domains. In higher dimensions that theory needs a regularity
hypothesis on the coefficients, such as continuity or vanishing mean oscillation, and a
Calderón–Zygmund estimate. On an interval it needs neither: the coefficient need only be bounded
below, not bounded above or continuous, and the constant depends on `σ` only through `λ`. The
reason is that the equation is the ordinary differential equation `u'' = -f / σ`, and
`|f / σ| ≤ |f| / λ`.

A step coefficient shows that no continuity or vanishing mean oscillation is needed. Let `σ = 1`
on `(0, 1/2]` and `σ = 2` on `(1/2, 1)`; it does not have vanishing mean oscillation
(`TauCeti.not_memVMO_ite_lt`). Every strong solution of `-σ u'' = 1` on `(0, 1)` has
`u'' = -1/σ`, so `‖u''‖_{Lᵖ(0, 1)} = ((1 + (1/2)ᵖ) / 2)^{1/p}` for `1 ≤ p < ∞`
(`TauCeti.PDE.norm_iteratedGradient_eq_of_neg_ite_mul_iteratedGradient_eq_one`), and in particular
`‖u''‖²_{L²(0, 1)} = 5/8`
(`TauCeti.PDE.norm_iteratedGradient_sq_eq_of_neg_ite_mul_iteratedGradient_eq_one`), within the
bound `‖u''‖ ≤ ‖f‖ / λ = 1`.

## The argument

The solution is written down by integrating twice: with `g = -f / σ ∈ Lᵖ(a, b)`, the function
`w t = ∫ s in a..t, g s - k` has weak derivative `g`, where the constant `k` makes the integral
of `w` over `(a, b)` vanish, and `u t = ∫ s in a..t, w s` then vanishes at both endpoints. So it
lies in `W^{1,p}_0(a, b)`, and uniqueness of weak derivatives identifies `u'' = g`
(`TauCeti.Wkp.exists_firstOrder_mem_w1p0Submodule_and_iteratedGradient_ae_eq`).

For the estimate, a solution `u` has `|u''| ≤ |f| / λ`. Its weak derivative `u'` is a constant
`k` plus the primitive of `u''`, and has integral zero because `u ∈ W^{1,p}_0(a, b)`, which bounds
`|k|` and hence `|u'| ≤ 2 ‖u''‖_{L¹}`. Since `u` is the primitive of `u'` from `a`,
`|u| ≤ 2 (b - a) ‖u''‖_{L¹}`. Hölder's inequality `‖u''‖_{L¹} ≤ (b - a)^{1 - 1/p} ‖u''‖_{Lᵖ}`
turns these pointwise bounds into the `Lᵖ` bounds `‖u'‖ ≤ 2 (b - a) ‖u''‖` and
`‖u‖ ≤ 2 (b - a)² ‖u''‖` (`TauCeti.Wkp.norm_lowerOrder_le_of_mem_w1p0Submodule`). Uniqueness
follows from the estimate applied to the difference of two solutions.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 9, for the `W^{2,p}` theory of strong solutions in higher dimensions.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4, for the one-dimensional boundary value problem.
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral

namespace TauCeti

namespace PDE

variable {a b : ℝ} {p : ENNReal} [Fact (1 ≤ p)]

/-- **The global `W^{2,p}` estimate for the Dirichlet problem on an interval.** Let `a < b`,
`1 ≤ p ≤ ∞` and `λ > 0`, and let `σ ≥ λ` almost everywhere on `(a, b)`. If
`u ∈ W^{2,p}(a, b)` has first-order part in `W^{1,p}_0(a, b)` and solves `-σ u'' = f` almost
everywhere, with `f ∈ Lᵖ(a, b)` and `u''` the weak Hessian in the direction `1`, then

`‖u‖_{W^{2,p}(a, b)} ≤ (1 + 2 (b - a) + 2 (b - a)²) / λ · ‖f‖_{Lᵖ(a, b)}`.

No upper bound, continuity or measurability of `σ` is needed. -/
theorem norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo (hab : a < b) {σ : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x)
    {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2} {f : Lp ℝ p (volume.restrict (Ioo a b))}
    (hu0 : Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p)
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), -(σ x * Wkp.iteratedGradient 1 u x 1) = f x) :
    ‖u‖ ≤ (1 + 2 * (b - a) + 2 * (b - a) ^ 2) / lam * ‖f‖ := by
  rw [Wkp.firstOrder_succ, Wkp.firstOrder_zero] at hu0
  set D := Wkp.iteratedGradient 1 u
  -- Pointwise `|u''| = |f| / σ ≤ |f| / λ`, hence `‖u''‖ ≤ ‖f‖ / λ` in `Lᵖ`.
  have hD : ‖D‖ ≤ lam⁻¹ * ‖f‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hσ, hu] with x hσx hx
    rw [← (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).symm.norm_map,
      ContinuousLinearMap.toSpanSingletonLIE_symm_apply, ← hx, norm_neg, norm_mul,
      Real.norm_of_nonneg (hlam.trans_le hσx).le, ← mul_assoc]
    exact le_mul_of_one_le_left (norm_nonneg _) ((one_le_inv_mul₀ hlam).2 hσx)
  have hlow := Wkp.norm_lowerOrder_le_of_mem_w1p0Submodule hab u hu0
  -- `‖u‖² = ‖u‖_{W^{1,p}}² + ‖u''‖²`, so `‖u‖ ≤ ‖u‖_{W^{1,p}} + ‖u''‖`.
  have hu2 := Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 0 u
  have hu1 : ‖u‖ ≤ ‖Wkp.lowerOrder 1 u‖ + ‖D‖ := by
    nlinarith [norm_nonneg u, norm_nonneg (Wkp.lowerOrder 1 u), norm_nonneg D]
  calc ‖u‖ ≤ (1 + 2 * (b - a) + 2 * (b - a) ^ 2) * ‖D‖ := by linarith
    _ ≤ (1 + 2 * (b - a) + 2 * (b - a) ^ 2) * (lam⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left hD (by nlinarith)
    _ = (1 + 2 * (b - a) + 2 * (b - a) ^ 2) / lam * ‖f‖ := by ring

/-- **The Dirichlet problem on an interval.** Let `a < b`, `1 ≤ p < ∞` and `λ > 0`, and let `σ`
be measurable on `(a, b)` with `σ ≥ λ` almost everywhere. For every `f ∈ Lᵖ(a, b)` there is
exactly one `u ∈ W^{2,p}(a, b)` whose first-order part lies in `W^{1,p}_0(a, b)` and which solves
`-σ u'' = f` almost everywhere on `(a, b)`, where `u''` is the weak Hessian in the direction `1`.
It satisfies the bound of `TauCeti.PDE.norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo`. -/
theorem existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo
    (hp : p ≠ ⊤) (hab : a < b) {σ : ℝ → ℝ}
    (hσm : AEStronglyMeasurable σ (volume.restrict (Ioo a b))) {lam : ℝ} (hlam : 0 < lam)
    (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x) (f : Lp ℝ p (volume.restrict (Ioo a b))) :
    ∃! u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2,
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ∧
        ∀ᵐ x ∂volume.restrict (Ioo a b), -(σ x * Wkp.iteratedGradient 1 u x 1) = f x := by
  -- Existence: `u'' = -f / σ` lies in `Lᵖ(a, b)`, since `|f / σ| ≤ |f| / λ`.
  have hgm : MemLp (fun x => -(f x / σ x)) p (volume.restrict (Ioo a b)) := by
    refine ((Lp.memLp f).const_mul lam⁻¹).of_le ((Lp.aestronglyMeasurable f).div₀ hσm).neg ?_
    filter_upwards [hσ] with x hx
    rw [norm_neg, norm_div, norm_mul, Real.norm_of_nonneg (hlam.trans_le hx).le, norm_inv,
      Real.norm_of_nonneg hlam.le, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hlam hx) (norm_nonneg _)
  obtain ⟨u, hu0, hug⟩ :=
    Wkp.exists_firstOrder_mem_w1p0Submodule_and_iteratedGradient_ae_eq hp hab hgm
  have hu : ∀ᵐ x ∂volume.restrict (Ioo a b), -(σ x * Wkp.iteratedGradient 1 u x 1) = f x := by
    filter_upwards [hug, hσ] with x hx hσx
    rw [hx]
    field_simp [(hlam.trans_le hσx).ne']
  refine ⟨u, ⟨hu0, hu⟩, fun v ⟨hv0, hv⟩ => ?_⟩
  -- Uniqueness: the difference of two solutions solves the problem with `f = 0`.
  have hd0 : Wkp.firstOrder 1 (v - u) ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p := by
    rw [Wkp.firstOrder_sub]
    exact (w1p0Submodule _ _ p).toSubmodule.sub_mem hv0 hu0
  have hd : ∀ᵐ x ∂volume.restrict (Ioo a b),
      -(σ x * Wkp.iteratedGradient 1 (v - u) x 1) = (0 : Lp ℝ p (volume.restrict (Ioo a b))) x := by
    rw [Wkp.iteratedGradient_sub]
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 v) (Wkp.iteratedGradient 1 u),
      Lp.coeFn_zero ℝ p (volume.restrict (Ioo a b)), hv, hu] with x hx hx0 hvx hux
    rw [hx, hx0, Pi.sub_apply, sub_apply, Pi.zero_apply]
    linear_combination hvx - hux
  have h0 := norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo hab hlam hσ hd0 hd
  rw [norm_zero, mul_zero] at h0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-! ### A coefficient with a jump -/

/-- The integral of `σ^{-q}` over `(0, 1)` for the step coefficient `σ = 1` on `(0, 1/2]` and
`σ = 2` on `(1/2, 1)`: it is `(1 + (1/2)^q) / 2`. -/
private theorem setLIntegral_ofReal_inv_ite_rpow {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (if 1 / 2 < x then 2 else 1 : ℝ)⁻¹ ^ q =
      ENNReal.ofReal ((1 + (1 / 2) ^ q) / 2) := by
  -- On `(0, 1/2]` the coefficient is `1`, so the integrand is `1`.
  have h₁ : ∫⁻ x in Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (if 1 / 2 < x then 2 else 1 : ℝ)⁻¹ ^ q =
      ENNReal.ofReal (1 / 2) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 1) fun x hx => by
      rw [ite_eq_right (not_lt.2 hx.2), inv_one, ENNReal.ofReal_one, ENNReal.one_rpow]]
    simp
  -- On `(1/2, 1)` the coefficient is `2`, so the integrand is `(1/2)^q`.
  have h₂ : ∫⁻ x in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal (if 1 / 2 < x then 2 else 1 : ℝ)⁻¹ ^ q =
      ENNReal.ofReal ((1 / 2) ^ q / 2) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => ENNReal.ofReal ((1 / 2) ^ q))
      fun x hx => by rw [ite_eq_left hx.1, ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq, one_div]]
    rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
    norm_num [div_eq_mul_inv, mul_comm]
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 / 2)) (Ioo (1 / 2) 1) :=
    disjoint_left.2 fun x hx hx' => (hx'.1.trans_le hx.2).false
  rw [← Ioc_union_Ioo_eq_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1),
    lintegral_union measurableSet_Ioo hdisj, h₁, h₂,
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  ring

/-- **The second derivative for a coefficient with a jump.** Let `1 ≤ p < ∞` and let `σ = 1` on
`(0, 1/2]` and `σ = 2` on `(1/2, 1)`. Every strong solution `u ∈ W^{2,p}(0, 1)` of `-σ u'' = 1`
has `u'' = -1/σ`, so

`‖u''‖_{Lᵖ(0, 1)} = ((1 + (1/2)ᵖ) / 2)^{1/p}`.

The coefficient `σ` is not of vanishing mean oscillation (`TauCeti.not_memVMO_ite_lt`), and a
solution with zero boundary values exists by
`TauCeti.PDE.existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo`.
Since `‖1‖_{Lᵖ(0, 1)} = 1` and `σ ≥ 1`, the value is below the bound `‖u''‖ ≤ ‖f‖ / λ = 1`. -/
theorem norm_iteratedGradient_eq_of_neg_ite_mul_iteratedGradient_eq_one (hp : p ≠ ⊤)
    {u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      -((if 1 / 2 < x then 2 else 1) * Wkp.iteratedGradient 1 u x 1) = 1) :
    ‖Wkp.iteratedGradient 1 u‖ = ((1 + (1 / 2) ^ p.toReal) / 2) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set σ : ℝ → ℝ := fun x => if 1 / 2 < x then 2 else 1
  have hσ (x : ℝ) : 0 < σ x := by simp only [σ]; split_ifs <;> norm_num
  -- Almost everywhere `|u''| = 1 / σ`.
  have hD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖Wkp.iteratedGradient 1 u x‖ₑ ^ p.toReal = ENNReal.ofReal (σ x)⁻¹ ^ p.toReal := by
    filter_upwards [hu] with x hx
    have hx' : Wkp.iteratedGradient 1 u x 1 = -(σ x)⁻¹ := by
      field_simp [(hσ x).ne']
      linarith
    rw [← ofReal_norm, ← (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).symm.norm_map,
      ContinuousLinearMap.toSpanSingletonLIE_symm_apply, hx', norm_neg,
      Real.norm_of_nonneg (inv_nonneg.2 (hσ x).le)]
  have hlint : ∫⁻ x in ((⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ),
      ‖Wkp.iteratedGradient 1 u x‖ₑ ^ p.toReal =
        ENNReal.ofReal ((1 + (1 / 2) ^ p.toReal) / 2) := by
    simp only [Opens.coe_mk]
    exact (lintegral_congr_ae hD).trans (setLIntegral_ofReal_inv_ite_rpow hq.le)
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (Lp.aestronglyMeasurable _),
    hlint, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ENNReal.toReal_ofReal (by positivity)]

/-- **The `L²` norm of the second derivative for a coefficient with a jump.** For `σ = 1` on
`(0, 1/2]` and `σ = 2` on `(1/2, 1)`, every strong solution `u ∈ W^{2,2}(0, 1)` of `-σ u'' = 1` has
`‖u''‖²_{L²(0, 1)} = 1/2 + 1/8 = 5/8`. -/
theorem norm_iteratedGradient_sq_eq_of_neg_ite_mul_iteratedGradient_eq_one
    {u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      -((if 1 / 2 < x then 2 else 1) * Wkp.iteratedGradient 1 u x 1) = 1) :
    ‖Wkp.iteratedGradient 1 u‖ ^ 2 = 5 / 8 := by
  rw [norm_iteratedGradient_eq_of_neg_ite_mul_iteratedGradient_eq_one ENNReal.ofNat_ne_top hu,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

end PDE

end TauCeti
