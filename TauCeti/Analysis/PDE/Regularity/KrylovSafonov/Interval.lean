/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Interval
import TauCeti.Analysis.PDE.Regularity.Hessian.Interval
import TauCeti.Analysis.Sobolev.Wkp.InteriorMorrey
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Krylov–Safonov estimate in dimension one

The interior Hölder estimate of Krylov and Safonov
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_abs_sum_mul_iteratedGradient_le`)
bounds the `α`-Hölder seminorm of a `W^{2,n}` strong solution of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`, with
uniformly elliptic coefficients, by `C r^(-α) (sup |u| + r ‖f‖_{Lⁿ} / λ)` on balls of
radius `r`, for some exponent `0 < α ≤ 1` depending on the dimension and the ellipticity ratio.
This file treats dimension one, where the estimate holds with the optimal exponent `α = 1`, no
upper bound on the coefficient, and explicit constants.

On an interval `(a, b)` let `σ ≥ λ > 0` almost everywhere, with no measurability or upper bound,
and let `u ∈ W^{2,p}(a, b)`, `1 ≤ p ≤ ∞`, satisfy `|σ u''| ≤ f` almost everywhere, with
`f ∈ L¹(a, b)` and `u''` the weak second derivative. A strong solution of `σ u'' = f` satisfies
this with `|f|` in place of `f`. Then `|u''| ≤ f / λ`, and the precise representative `ū` of `u`,
which is `C¹` on `(a, b)` (`TauCeti.Wkp.contDiffOn_preciseRepresentative_Ioo`), satisfies:

* the oscillation of the derivative is controlled by the datum,
  `|ū'(y) - ū'(x)| ≤ (∫_x^y f) / λ` for `a < x ≤ y < b`
  (`TauCeti.PDE.abs_deriv_preciseRepresentative_sub_le_of_abs_mul_iteratedGradient_le`);
* if `|u| ≤ M` almost everywhere, then `|ū'| ≤ 2 M / (b - a) + (∫_a^b f) / λ` on `(a, b)`
  (`TauCeti.PDE.abs_deriv_preciseRepresentative_le_of_abs_mul_iteratedGradient_le`), so `ū` is
  Lipschitz on `(a, b)` with that constant
  (`TauCeti.PDE.lipschitzOnWith_preciseRepresentative_of_abs_mul_iteratedGradient_le`).

On the ball `(x₀ - 2 r, x₀ + 2 r)` the Lipschitz constant is
`M / (2 r) + ‖f‖_{L¹} / λ ≤ r⁻¹ (M + r ‖f‖_{L¹} / λ)`, which is the Krylov–Safonov bound with
`n = 1`, `α = 1` and `C = 1`, valid on the whole ball rather than on the ball of half the radius.
The derivative bound comes from the mean value theorem, which produces a point of `(a, b)` where
`|ū'| ≤ 2 M / (b - a)` up to an arbitrarily small loss, and the oscillation bound, which is the
fundamental theorem of calculus `ū'(y) - ū'(x) = ∫_x^y u''`.

The regularity stops at `C^{1,1}`. For the jump coefficient `σ = 2` on `(0, 1)`, `σ = 1` on
`(-1, 0]`, the equation `-σ u'' = 1` has strong solutions in `W^{2,p}(-1, 1)` for every `p < ∞`
(`TauCeti.PDE.exists_neg_ite_mul_iteratedGradient_eq_one`), and the derivative of each of them is
`1`-Lipschitz on `(-1, 1)` by the oscillation bound, but is not differentiable at `0`
(`not_differentiableAt_deriv_preciseRepresentative_of_neg_ite_mul_iteratedGradient_eq_one`, in
the `TauCeti.PDE` namespace): its one-sided derivatives there are `u'' = -1` from the left and
`u'' = -1/2` from the right. So no `C²` conclusion holds for measurable coefficients, even in
dimension one.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Corollary 9.24 (the interior Hölder estimate of Krylov and Safonov).
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral TauCeti.MeasureTheory
open scoped Topology

namespace TauCeti

namespace PDE

variable {a b : ℝ} {p : ENNReal} [Fact (1 ≤ p)]

/-- From `|σ u''| ≤ f` and `σ ≥ λ > 0`, the weak second derivative is bounded by `f / λ`. -/
private theorem ae_abs_iteratedGradient_le_div {σ f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x)
    {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), |σ x * Wkp.iteratedGradient 1 u x 1| ≤ f x) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), |Wkp.iteratedGradient 1 u x 1| ≤ f x / lam := by
  filter_upwards [hσ, hu] with x hσx hx
  rw [le_div_iff₀ hlam]
  calc |Wkp.iteratedGradient 1 u x 1| * lam ≤ |Wkp.iteratedGradient 1 u x 1| * σ x :=
        mul_le_mul_of_nonneg_left hσx (abs_nonneg _)
    _ = |σ x * Wkp.iteratedGradient 1 u x 1| := by
        rw [abs_mul, abs_of_pos (hlam.trans_le hσx), mul_comm]
    _ ≤ f x := hx

/-- **The oscillation of the derivative in the one-dimensional Krylov–Safonov estimate.** Let
`σ ≥ λ > 0` almost everywhere on `(a, b)` and let `u ∈ W^{2,p}(a, b)` satisfy `|σ u''| ≤ f`
almost everywhere. Then the derivative of the precise representative `ū` of `u` satisfies
`|ū'(y) - ū'(x)| ≤ (∫_x^y f) / λ` for `a < x ≤ y < b` with `f` integrable on `(x, y)`.

No measurability or upper bound of `σ` is needed. -/
theorem abs_deriv_preciseRepresentative_sub_le_of_abs_mul_iteratedGradient_le
    {σ f : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam) (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x)
    {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), |σ x * Wkp.iteratedGradient 1 u x 1| ≤ f x)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hxy : x ≤ y)
    (hf : IntervalIntegrable f volume x y) :
    |deriv (preciseRepresentative volume (Wkp.value 2 u)) y -
        deriv (preciseRepresentative volume (Wkp.value 2 u)) x| ≤
      (∫ t in x..y, f t) / lam := by
  have hDint : IntervalIntegrable (fun t => Wkp.iteratedGradient 1 u t 1) volume x y :=
    (Wkp.integrableOn_iteratedGradient_one_Ioo u).intervalIntegrable_of_mem_Icc
      (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
  rw [Wkp.deriv_preciseRepresentative_sub_deriv_eq_integral u hx hy,
    ← intervalIntegral.integral_div]
  exact (abs_integral_le_integral_abs hxy).trans
    (integral_mono_ae_restrict hxy hDint.abs (hf.div_const lam)
      (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Ioo hx.1 hy.2)
        (ae_abs_iteratedGradient_le_div hlam hσ hu)))

/-- On all of `(a, b)`, the derivative of the precise representative oscillates by at most
`(∫_a^b f) / λ`, since `f ≥ |σ u''| ≥ 0`. -/
private theorem abs_deriv_preciseRepresentative_sub_le_integral_div {σ f : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x)
    {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), |σ x * Wkp.iteratedGradient 1 u x 1| ≤ f x)
    (hf : IntegrableOn f (Ioo a b)) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    |deriv (preciseRepresentative volume (Wkp.value 2 u)) x -
        deriv (preciseRepresentative volume (Wkp.value 2 u)) y| ≤ (∫ t in a..b, f t) / lam := by
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioc a b)] f := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hu.mono fun _ h => (abs_nonneg _).trans h
  have hfi : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hx.1.trans hx.2).le).2 hf
  have hfs {y z : ℝ} (hy : y ∈ Ioo a b) (hz : z ∈ Ioo a b) : IntervalIntegrable f volume y z :=
    hf.intervalIntegrable_of_mem_Icc (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hz)
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    exact (abs_deriv_preciseRepresentative_sub_le_of_abs_mul_iteratedGradient_le hlam hσ hu
      hx hy hxy (hfs hx hy)).trans
      (div_le_div_of_nonneg_right (integral_mono_interval hx.1.le hxy hy.2.le hf0 hfi) hlam.le)
  · exact (abs_deriv_preciseRepresentative_sub_le_of_abs_mul_iteratedGradient_le hlam hσ hu
      hy hx hyx (hfs hy hx)).trans
      (div_le_div_of_nonneg_right (integral_mono_interval hy.1.le hyx hx.2.le hf0 hfi) hlam.le)

/-- **The derivative bound in the one-dimensional Krylov–Safonov estimate.** Let `σ ≥ λ > 0`
almost everywhere on `(a, b)` and let `u ∈ W^{2,p}(a, b)` satisfy `|u| ≤ M` and `|σ u''| ≤ f`
almost everywhere, with `f` integrable. Then the derivative of the precise representative `ū` of
`u` satisfies `|ū'| ≤ 2 M / (b - a) + (∫_a^b f) / λ` at every point of `(a, b)`.

No measurability or upper bound of `σ` is needed. -/
theorem abs_deriv_preciseRepresentative_le_of_abs_mul_iteratedGradient_le
    {σ f : ℝ → ℝ} {lam M : ℝ} (hlam : 0 < lam)
    (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x) {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2}
    (hM : ∀ᵐ x ∂volume.restrict (Ioo a b), |Wkp.value 2 u x| ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), |σ x * Wkp.iteratedGradient 1 u x 1| ≤ f x)
    (hf : IntegrableOn f (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    |deriv (preciseRepresentative volume (Wkp.value 2 u)) x| ≤
      2 * M / (b - a) + (∫ t in a..b, f t) / lam := by
  set ū := preciseRepresentative volume (Wkp.value 2 u)
  set I := ∫ t in a..b, f t
  have hab : a < b := hx.1.trans hx.2
  have hd := Wkp.differentiableOn_preciseRepresentative_Ioo u
  have hMū (z : ℝ) (hz : z ∈ Ioo a b) : |ū z| ≤ M :=
    Wkp.abs_preciseRepresentative_le (by
      rw [Module.finrank_self, Nat.cast_one]
      exact ENNReal.one_lt_two.trans_le
        (le_mul_of_one_le_right (by positivity) (Fact.out : 1 ≤ p))) u isOpen_Ioo subset_rfl hM hz
  have hosc (y : ℝ) (hy : y ∈ Ioo a b) : |deriv ū x - deriv ū y| ≤ I / lam :=
    abs_deriv_preciseRepresentative_sub_le_integral_div hlam hσ hu hf hx hy
  -- On `[a + ε, b - ε]` the mean value theorem gives a point where `|ū'| ≤ 2 M / (b - a - 2 ε)`.
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |deriv ū x| ≤ 2 * M / (b - a - 2 * ε) + I / lam := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (b - a) / 2 by linarith)] with ε hε
    have hs : a + ε < b - ε := by linarith [hε.2]
    have hsI : Icc (a + ε) (b - ε) ⊆ Ioo a b :=
      Icc_subset_Ioo (by linarith [hε.1]) (by linarith [hε.1])
    obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope ū hs (hd.continuousOn.mono hsI)
      (hd.mono (Ioo_subset_Icc_self.trans hsI))
    have hdiff : |ū (b - ε) - ū (a + ε)| ≤ 2 * M := by
      have h1 := abs_le.1 (hMū _ (hsI (right_mem_Icc.2 hs.le)))
      have h2 := abs_le.1 (hMū _ (hsI (left_mem_Icc.2 hs.le)))
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hξ1 : |deriv ū ξ| ≤ 2 * M / (b - a - 2 * ε) := by
      rw [hξd, abs_div, abs_of_pos (sub_pos.2 hs), show b - ε - (a + ε) = b - a - 2 * ε by ring]
      exact div_le_div_of_nonneg_right hdiff (by linarith [hε.2])
    linarith [abs_sub_abs_le_abs_sub (deriv ū x) (deriv ū ξ),
      hosc ξ (hsI (Ioo_subset_Icc_self hξ))]
  -- Letting `ε → 0` gives the bound.
  have hcont : ContinuousAt (fun ε : ℝ => 2 * M / (b - a - 2 * ε) + I / lam) 0 :=
    (continuousAt_const.div (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
      (by simpa using (sub_pos.2 hab).ne')).add continuousAt_const
  have hlim := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) hcont.tendsto
  simp only [mul_zero, sub_zero] at hlim
  exact ge_of_tendsto hlim hev

/-- **The Krylov–Safonov estimate in dimension one.** Let `σ ≥ λ > 0` almost everywhere on
`(a, b)` and let `u ∈ W^{2,p}(a, b)` satisfy `|u| ≤ M` and `|σ u''| ≤ f` almost everywhere, with
`f` integrable. Then the precise representative of `u` is Lipschitz on `(a, b)` with constant
`2 M / (b - a) + (∫_a^b f) / λ`.

This is the interior Hölder estimate of Krylov and Safonov in dimension one, with the exponent
`α = 1`; no measurability or upper bound of `σ` is needed. -/
theorem lipschitzOnWith_preciseRepresentative_of_abs_mul_iteratedGradient_le
    {σ f : ℝ → ℝ} {lam M : ℝ} (hlam : 0 < lam)
    (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x) {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2}
    (hM : ∀ᵐ x ∂volume.restrict (Ioo a b), |Wkp.value 2 u x| ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), |σ x * Wkp.iteratedGradient 1 u x 1| ≤ f x)
    (hf : IntegrableOn f (Ioo a b)) :
    LipschitzOnWith (2 * M / (b - a) + (∫ t in a..b, f t) / lam).toNNReal
      (preciseRepresentative volume (Wkp.value 2 u)) (Ioo a b) := by
  have hd := Wkp.differentiableOn_preciseRepresentative_Ioo u
  refine (convex_Ioo a b).lipschitzOnWith_of_nnNorm_deriv_le
    (fun x hx => hd.differentiableAt (isOpen_Ioo.mem_nhds hx)) fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs]
  exact (abs_deriv_preciseRepresentative_le_of_abs_mul_iteratedGradient_le hlam hσ hM hu hf
    hx).trans (Real.le_coe_toNNReal _)

/-! ### A coefficient with a jump -/

/-- **Strong solutions with a jump coefficient exist.** For every `1 ≤ p < ∞` the equation
`-σ u'' = 1` on `(-1, 1)`, with `σ = 2` on `(0, 1)` and `σ = 1` on `(-1, 0]`, has a strong
solution `u ∈ W^{2,p}(-1, 1)`. -/
theorem exists_neg_ite_mul_iteratedGradient_eq_one (hp : p ≠ ⊤) :
    ∃ u : Wkp volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 2, ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
      -((if 0 < x then 2 else 1) * Wkp.iteratedGradient 1 u x 1) = 1 := by
  have : IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    Real.isFiniteMeasure_restrict_Ioo _ _
  obtain ⟨u, ⟨-, hu⟩, -⟩ :=
    existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo hp
      (by norm_num : (-1 : ℝ) < 1) (σ := fun x => if 0 < x then 2 else 1)
      ((Measurable.ite measurableSet_Ioi measurable_const measurable_const).aestronglyMeasurable)
      one_pos (ae_of_all _ fun x => by split_ifs <;> norm_num)
      (Lp.const p (volume.restrict (Ioo (-1 : ℝ) 1)) 1)
  refine ⟨u, ?_⟩
  filter_upwards [hu, Lp.coeFn_const p (volume.restrict (Ioo (-1 : ℝ) 1)) (1 : ℝ)] with x hx hc
  rw [hx, hc, Function.const_apply]

/-- **The one-dimensional Krylov–Safonov estimate does not give `C²`.** Let `σ = 2` on `(0, 1)`
and `σ = 1` on `(-1, 0]`, and let `u ∈ W^{2,p}(-1, 1)` be a strong solution of `-σ u'' = 1`.
The derivative of the precise representative `ū` of `u` is `1`-Lipschitz on `(-1, 1)`
(`TauCeti.PDE.abs_deriv_preciseRepresentative_sub_le_of_abs_mul_iteratedGradient_le`), but it is
not differentiable at `0`: its one-sided derivatives there are `-1` and `-1/2`. -/
theorem not_differentiableAt_deriv_preciseRepresentative_of_neg_ite_mul_iteratedGradient_eq_one
    {u : Wkp volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ p 2}
    (hu : ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
      -((if 0 < x then 2 else 1) * Wkp.iteratedGradient 1 u x 1) = 1) :
    ¬ DifferentiableAt ℝ (deriv (preciseRepresentative volume (Wkp.value 2 u))) 0 := by
  set d := deriv (preciseRepresentative volume (Wkp.value 2 u))
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hu' := (ae_restrict_iff' measurableSet_Ioo).1 hu
  -- On `(-1, 0]` the weak second derivative is `-1`, on `(0, 1)` it is `-1/2`, so `d` is affine
  -- on each side of `0`.
  have hconst (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) (c : ℝ)
      (hc : ∀ t ∈ uIoc 0 y, (if 0 < t then 2 else 1) * c = -1) : d y = d 0 + c * (y - 0) := by
    refine Wkp.deriv_preciseRepresentative_eq_add_mul_of_iteratedGradient_eq u h0 hy ?_
    filter_upwards [hu'] with t ht htI
    have hs : (if 0 < t then 2 else 1 : ℝ) ≠ 0 := by split_ifs <;> norm_num
    refine mul_left_cancel₀ hs ((neg_eq_iff_eq_neg.1 (ht ?_)).trans (hc t htI).symm)
    exact ordConnected_Ioo.uIcc_subset h0 hy (uIoc_subset_uIcc htI)
  have hl (y : ℝ) (hy : y ∈ Ioc (-1 : ℝ) 0) : d y = d 0 - y := by
    have := hconst y ⟨hy.1, by linarith [hy.2]⟩ (-1) fun t ht => by
      simp [not_lt.2 (uIoc_of_ge hy.2 ▸ ht).2]
    linarith
  have hr (y : ℝ) (hy : y ∈ Ico 0 1) : d y = d 0 - y / 2 := by
    have := hconst y ⟨by linarith [hy.1], hy.2⟩ (-1 / 2) fun t ht => by
      norm_num [(uIoc_of_le hy.1 ▸ ht).1]
    linarith
  -- A derivative at `0` would equal both one-sided derivatives.
  intro hd
  have hL : HasDerivWithinAt d (-1) (Iic 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_sub (d 0)).hasDerivWithinAt.congr_of_eventuallyEq
      (by filter_upwards [Ioc_mem_nhdsLE (show (-1 : ℝ) < 0 by norm_num)] with y hy
          using hl y hy)
      (by simp)
  have hR : HasDerivWithinAt d (-(1 / 2)) (Ici 0) 0 :=
    (((hasDerivAt_id (0 : ℝ)).div_const 2).const_sub (d 0)).hasDerivWithinAt.congr_of_eventuallyEq
      (by filter_upwards [Ico_mem_nhdsGE (show (0 : ℝ) < 1 by norm_num)] with y hy
          using hr y hy)
      (by simp)
  have h1 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Iic 0)
    hd.hasDerivAt.hasDerivWithinAt hL
  have h2 := UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici 0)
    hd.hasDerivAt.hasDerivWithinAt hR
  linarith

end PDE

end TauCeti
