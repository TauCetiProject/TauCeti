/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.PDE.Regularity.Oscillation
public import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# De Giorgi's oscillation decay at the boundary

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, let `f ∈ L²(Ω)`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u ≤ 0` on `∂Ω`, in the sense that
`u⁺ ∈ H¹₀(Ω)`. Nothing is assumed about the regularity of `∂Ω`. This file proves De Giorgi's
estimate at boundary points: if the complement of `Ω` fills a fixed proportion `θ > 0` of the
ball `B(x₀, R)` and `f ∈ Lʳ(Ω ∩ B(x₀, 2R))` with `r > 1` and `r > n/2`, then the supremum of
`u⁺` drops by a fixed factor from `Ω ∩ B(x₀, 2R)` to `Ω ∩ B(x₀, R/2)`, up to an error
`K R^(2 - n/r) ‖f⁺‖_{Lʳ} / λ`. If the complement fills that proportion of every ball `B(x₀, r)`,
`r ≤ R`, the supremum decays geometrically along the balls `B(x₀, R / 4ʲ)`, up to the same kind of
error. For `f = 0` the error vanishes.

The proof reduces the boundary estimate to the interior one.

* **Testing against functions without boundary values.** For a subsolution with `u⁺ ∈ H¹₀(Ω)`,
  the inequality `a(u⁺, v) ≤ ∫_{u > 0} f v` holds for every nonnegative `v ∈ H¹(Ω)`, not only for
  `v ∈ H¹₀(Ω)` (`TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`). The test function is
  `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺`, which lies in `H¹₀(Ω)` because `u⁺` does
  (`TauCeti.W1p.posPart_sub_mem_w1p0Submodule`). On `{u⁺ ≤ ε v}` its gradient is `∇u⁺` and
  contributes the nonnegative energy `⟨a ∇u⁺, ∇u⁺⟩`; on `{u⁺ > ε v}` it is `ε ∇v`. Dividing by
  `ε` and letting `ε → 0`, dominated convergence turns the indicator of `{u⁺ > ε v}` into that of
  `{u > 0}`, and `ε⁻¹ min(u⁺, ε v)` into `1_{u > 0} v`.
* **The zero extension is a subsolution.** Hence the zero extension `ū` of `u⁺` to a larger open
  set `Ω'` satisfies `a'(ū, v) ≤ ∫_{u > 0} f v` for every nonnegative `v ∈ H¹(Ω')`, for every
  coefficient field `a'` agreeing with `a` on `Ω`
  (`TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`).
* **Reduction of the supremum.** Extending `a` by `λ I` off `Ω`, the zero extension is a weak
  subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ g = 1_Ω f⁺` on the whole space, and it vanishes on
  `B(x₀, R) \ Ω`. Let `z ∈ H¹₀(B)` solve `-∂ᵢ(a'ⁱʲ ∂ⱼz) = g` in `B = B(x₀, 2R)`. Stampacchia's
  bound (`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow`) gives `|z| ≤ S` with `S` a multiple
  of `R^(2 - n/r) ‖g‖_{Lʳ(B)} / λ`. So `ū - z` is a weak subsolution of the homogeneous equation on
  `B`, at most `M + S` there and at most `S` on `B(x₀, R) \ Ω`. De Giorgi's interior reduction of
  the supremum (`TauCeti.PDE.exists_ae_value_le_sub_mul_sub`) at the level `S` gives
  `ū - z ≤ (1 - δ) M + S` on `B(x₀, R/2)`, hence `u ≤ (1 - δ) M + 2 S` on `Ω ∩ B(x₀, R/2)`
  (`TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).

The exterior density hypothesis `θ |B(x₀, r)| ≤ |B(x₀, r) \ Ω|` for all small `r` is an
exterior measure density condition at `x₀`. An exterior cone with vertex `x₀` gives it, with `θ`
depending only on the aperture of the cone, for every `r` up to the height of the cone. Iterating
the reduction along the balls `B(x₀, R / 4ʲ)` contracts the bound by `1 - δ` at each step, while
the error shrinks by `4^(-(2 - n/r))`, which gives the geometric decay
`u ≤ τʲ (M + K R^(2 - n/r) ‖f⁺‖_{Lʳ} / λ)` with a rate `τ < 1`
(`TauCeti.PDE.exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`). For
a weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` both `u` and `-u` are such subsolutions, with
data `f` and `-f`, so `|u|` decays geometrically towards boundary points
(`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).
This is the boundary step of the global Hölder estimate for the Dirichlet problem.

## Main declarations

* `TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`: `a(u⁺, v) ≤ ∫_{u > 0} f v` for every
  nonnegative `v ∈ H¹(Ω)`, and its case `f = 0`, `TauCeti.PDE.energyFormH1_posPart_left_nonpos`.
* `TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`: the zero extension of `u⁺` is
  a weak subsolution on every larger open set, and its case `f = 0`,
  `TauCeti.PDE.energyFormH1_extendByZeroL_posPart_nonpos`.
* `TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`: the
  reduction of the supremum at the boundary, and its case `f = 0`,
  `TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`.
* `TauCeti.PDE.exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`: its
  iteration, geometric decay of the supremum; for `f = 0` with the rate `1 - δ`,
  `TauCeti.PDE.exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`.
* `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`:
  geometric decay of `|u|` for weak solutions in `H¹₀(Ω)`, and its case `f = 0`,
  `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.16, 8.25, 8.27 and 8.29.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ} {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- The density `⟨a ∇u, ∇w⟩` of the principal energy form is integrable on `Ω` for a measurable
uniformly elliptic `a` and `u, w ∈ H¹(Ω)`. -/
private theorem integrable_matrixBilinearForm_gradient
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (u w : W1p mu Omega 2) :
    Integrable (fun x => matrixBilinearForm (a x) (W1p.gradient w x) (W1p.gradient u x))
      (mu.restrict Omega) := by
  simpa using h.integrable_energyIntegrand_jetField ha (b := 0) (c := 0) (beta := 0)
    (gamma := 0) aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u w

/-- The pointwise step of the test-function argument: for `ε > 0`, the energy density of `u`
against `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` dominates `ε` times the density of `u` against `v` cut
off to `{u⁺ > ε v}`. -/
private theorem mul_indicator_le_matrixBilinearForm_gradient
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (u v : W1p mu Omega 2) {ε : ℝ} :
    ∀ᵐ x ∂mu.restrict Omega,
      ε * {x | ε * W1p.value v x < max (W1p.value u x) 0}.indicator
          (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ≤
        matrixBilinearForm (a x) (W1p.gradient (W1p.posPart (by norm_num) u -
          W1p.posPart (by norm_num) (W1p.posPart (by norm_num) u - ε • v)) x)
          (W1p.gradient u x) := by
  set up := W1p.posPart (p := 2) (mu := mu) (Omega := Omega) (by norm_num) u
  have hsmul : ⇑(W1p.gradient (ε • v)) =ᵐ[mu.restrict Omega] ε • ⇑(W1p.gradient v) := by
    rw [← W1p.gradientL_apply, map_smul, W1p.gradientL_apply]
    exact Lp.coeFn_smul _ _
  have hgsub (w₁ w₂ : W1p mu Omega 2) :
      ⇑(W1p.gradient (w₁ - w₂)) =ᵐ[mu.restrict Omega]
        ⇑(W1p.gradient w₁) - ⇑(W1p.gradient w₂) := by
    rw [W1p.gradient_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hgsub up (W1p.posPart (by norm_num) (up - ε • v)),
    hgsub up (ε • v), hsmul, W1p.gradient_posPart_ae (by norm_num) u,
    W1p.gradient_posPart_ae (by norm_num) (up - ε • v), Lp.coeFn_posPart (W1p.value u),
    W1p.value_sub_ae up (ε • v), W1p.value_smul_ae ε v, self_mem_ae_restrict
      Omega.isOpen.measurableSet] with x h1 h2 h3 h4 h5 h6 h7 h8 hxO
  have hup : W1p.value up x = max (W1p.value u x) 0 := by
    rw [W1p.value_posPart]
    exact h6
  have hval : W1p.value (up - ε • v) x = max (W1p.value u x) 0 - ε * W1p.value v x := by
    rw [h7, Pi.sub_apply, hup, h8, Pi.smul_apply, smul_eq_mul]
  rw [h1, Pi.sub_apply, h5]
  by_cases hx : ε * W1p.value v x < max (W1p.value u x) 0
  · -- On `{u⁺ > ε v}` the test function is `ε v`, with gradient `ε ∇v`.
    rw [indicator_of_mem (s := {x | ε * W1p.value v x < max (W1p.value u x) 0}) hx,
      indicator_of_mem (s := {y | 0 < W1p.value (up - ε • v) y}) (by
        rw [mem_ofPred_eq, hval]
        exact sub_pos.2 hx),
      h2, Pi.sub_apply, h3, Pi.smul_apply, sub_sub_cancel, map_smul,
      smul_apply, smul_eq_mul]
  · -- On `{u⁺ ≤ ε v}` the test function is `u⁺`, whose energy against `u` is nonnegative.
    rw [indicator_of_notMem (s := {x | ε * W1p.value v x < max (W1p.value u x) 0}) hx,
      indicator_of_notMem (s := {y | 0 < W1p.value (up - ε • v) y}) (by
        rw [mem_ofPred_eq, hval]
        exact fun hlt => hx (sub_pos.1 hlt)),
      sub_zero, mul_zero, h4]
    by_cases hu : 0 < W1p.value u x
    · rw [indicator_of_mem (s := {y | 0 < W1p.value u y}) hu, matrixBilinearForm_self]
      exact h.quadraticForm_nonneg hxO _
    · rw [indicator_of_notMem (s := {y | 0 < W1p.value u y}) hu, map_zero, zero_apply]

omit [DecidableEq ι] in
/-- The values of the test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` of the test-function
argument. -/
private theorem value_posPart_sub_posPart_sub_smul_ae (u v : W1p mu Omega 2) (ε : ℝ) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (W1p.posPart (by norm_num) u -
          W1p.posPart (by norm_num) (W1p.posPart (by norm_num) u - ε • v)) x =
        min (max (W1p.value u x) 0) (ε * W1p.value v x) := by
  set up := W1p.posPart (p := 2) (mu := mu) (Omega := Omega) (by norm_num) u
  filter_upwards [W1p.value_sub_ae up (W1p.posPart (by norm_num) (up - ε • v)),
    Lp.coeFn_posPart (W1p.value (up - ε • v)), W1p.value_sub_ae up (ε • v),
    Lp.coeFn_posPart (W1p.value u), W1p.value_smul_ae ε v] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, W1p.value_posPart (u := up - ε • v), h2, h3, Pi.sub_apply,
    W1p.value_posPart, h4, h5, Pi.smul_apply, smul_eq_mul]
  rcases le_total (max (W1p.value u x) 0) (ε * W1p.value v x) with hle | hle
  · rw [min_eq_left hle, max_eq_right (sub_nonpos.2 hle), sub_zero]
  · rw [min_eq_right hle, max_eq_left (sub_nonneg.2 hle), sub_sub_cancel]

/-- The cut-off step of the test-function argument: for `ε > 0`, the density `⟨a ∇u, ∇v⟩` of
a subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)` against a nonnegative `v ∈ H¹(Ω)`, cut off
to `{u⁺ > ε v}` and multiplied by `ε`, has integral at most `∫_Ω f min(u⁺, ε v)`. The left side
is a lower bound for the energy of `u` against the test function
`min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺ ∈ H¹₀(Ω)`. -/
private theorem mul_setIntegral_indicator_matrixBilinearForm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu Omega 2} (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) {ε : ℝ}
    (hε : 0 < ε) (hFm : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0}) :
    ε * ∫ x in Omega, {x | ε * W1p.value v x < max (W1p.value u x) 0}.indicator
      (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu ≤
      ∫ x in Omega, f x * min (max (W1p.value u x) 0) (ε * W1p.value v x) ∂mu := by
  set up := W1p.posPart (p := 2) (mu := mu) (Omega := Omega) (by norm_num) u
  have hεv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (ε • v) x := by
    filter_upwards [W1p.value_smul_ae ε v, hv] with x hx hvx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hε.le hvx
  -- The test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` lies in `H¹₀(Ω)` and is nonnegative.
  have hmem : up - W1p.posPart (by norm_num) (up - ε • v) ∈ w1p0Submodule mu Omega 2 :=
    (w1p0Submodule mu Omega 2).toSubmodule.sub_mem hboundary
      (W1p.posPart_sub_mem_w1p0Submodule (by norm_num) hboundary hεv)
  have hval := value_posPart_sub_posPart_sub_smul_ae u v ε
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega,
      0 ≤ W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x := by
    filter_upwards [hval, hv] with x hx hvx
    rw [hx]
    exact le_min (le_max_right _ _) (mul_nonneg hε.le hvx)
  have htest := hu ⟨_, hmem⟩ hnonneg
  rw [energyFormH1_zero_zero_eq_setIntegral] at htest
  rw [← integral_const_mul]
  refine (integral_mono_ae
    (((integrable_matrixBilinearForm_gradient h ha u v).indicator hFm).const_mul ε)
    (integrable_matrixBilinearForm_gradient h ha u _)
    (mul_indicator_le_matrixBilinearForm_gradient h u v)).trans
    (htest.trans_eq (integral_congr_ae ?_))
  filter_upwards [hval] with x hx
  rw [← hx]

/-- The left side of the test-function argument in the limit `ε = 1 / (n + 1) → 0`: the cut-off
densities `1_{u⁺ > ε v} ⟨a ∇u, ∇v⟩` converge in `L¹(Ω)` to `1_{u > 0} ⟨a ∇u, ∇v⟩`. -/
private theorem tendsto_setIntegral_indicator_matrixBilinearForm
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (u : W1p mu Omega 2)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    Tendsto (fun n : ℕ => ∫ x in Omega,
      {x | 1 / ((n : ℝ) + 1) * W1p.value v x < max (W1p.value u x) 0}.indicator
        (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu) atTop
      (𝓝 (∫ x in Omega, {x | 0 < W1p.value u x}.indicator
        (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu)) := by
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
  have hg : Integrable g (mu.restrict Omega) := integrable_matrixBilinearForm_gradient h ha u v
  have hFm (ε : ℝ) : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0} :=
    measurableSet_lt ((Lp.stronglyMeasurable (W1p.value v)).measurable.const_mul ε)
      ((Lp.stronglyMeasurable (W1p.value u)).measurable.max measurable_const)
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (hg.indicator (hFm _)).aestronglyMeasurable) hg.norm
    (fun n => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _) ?_
  filter_upwards [hv] with x hvx
  by_cases hux : 0 < W1p.value u x
  · rw [indicator_of_mem (s := {x | 0 < W1p.value u x}) hux]
    have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * W1p.value v x) atTop
        (𝓝 (0 * W1p.value v x)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
    rw [zero_mul] at hsmall
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsmall.eventually (gt_mem_nhds (lt_max_of_lt_left hux))] with n hn
    exact (indicator_of_mem (s := {x | 1 / ((n : ℝ) + 1) * W1p.value v x <
      max (W1p.value u x) 0}) hn g).symm
  · rw [indicator_of_notMem (s := {x | 0 < W1p.value u x}) hux]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    refine (indicator_of_notMem (s := {x | 1 / ((n : ℝ) + 1) * W1p.value v x <
      max (W1p.value u x) 0}) ?_ g).symm
    rw [mem_ofPred_eq, max_eq_right (le_of_not_gt hux), not_lt]
    positivity

omit [DecidableEq ι] in
/-- The right side of the test-function argument in the limit `ε = 1 / (n + 1) → 0`: for
`f ∈ L²(Ω)`, `∫_Ω f ε⁻¹ min(u⁺, ε v)` converges to `∫_{u > 0} f v`. -/
private theorem tendsto_setIntegral_mul_mul_min {f : EuclideanSpace ℝ ι → ℝ}
    (hf : MemLp f 2 (mu.restrict Omega)) (u : W1p mu Omega 2) {v : W1p mu Omega 2}
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    Tendsto (fun n : ℕ => ∫ x in Omega, f x *
      (((n : ℝ) + 1) * min (max (W1p.value u x) 0) (1 / ((n : ℝ) + 1) * W1p.value v x)) ∂mu)
      atTop (𝓝 (∫ x in Omega, {x | 0 < W1p.value u x}.indicator f x * W1p.value v x ∂mu)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * ‖W1p.value v x‖)
    (fun n => hf.aestronglyMeasurable.mul ((((Lp.stronglyMeasurable (W1p.value u)).measurable.max
      measurable_const).min ((Lp.stronglyMeasurable (W1p.value v)).measurable.const_mul
        _)).const_mul _).aestronglyMeasurable)
    (hf.norm.integrable_mul (Lp.memLp (W1p.value v)).norm) (fun n => ?_) ?_
  · filter_upwards [hv] with x hvx
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h0 : 0 ≤ ((n : ℝ) + 1) *
        min (max (W1p.value u x) 0) (1 / ((n : ℝ) + 1) * W1p.value v x) :=
      mul_nonneg hn.le (le_min (le_max_right _ _) (by positivity))
    have h1 : ((n : ℝ) + 1) *
        min (max (W1p.value u x) 0) (1 / ((n : ℝ) + 1) * W1p.value v x) ≤ W1p.value v x :=
      calc _ ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1) * W1p.value v x) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hn.le
        _ = W1p.value v x := by field_simp
    rw [norm_mul, Real.norm_of_nonneg h0, Real.norm_of_nonneg hvx]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  · filter_upwards [hv] with x hvx
    by_cases hux : 0 < W1p.value u x
    · rw [indicator_of_mem (s := {x | 0 < W1p.value u x}) hux]
      have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * W1p.value v x) atTop
          (𝓝 (0 * W1p.value v x)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
      rw [zero_mul] at hsmall
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hsmall.eventually (gt_mem_nhds (lt_max_of_lt_left hux))] with n hn
      rw [min_eq_right hn.le]
      field_simp
    · rw [indicator_of_notMem (s := {x | 0 < W1p.value u x}) hux, zero_mul]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      dsimp only
      rw [max_eq_right (le_of_not_gt hux), min_eq_left (by positivity), mul_zero, mul_zero]

/-- **Subsolutions vanishing on the boundary may be tested against any nonnegative function.**
Let `a` be measurable and uniformly elliptic on `Ω`, let `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`, that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative
`v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the sense that `u⁺ ∈ H¹₀(Ω)`. Then
`a(u⁺, v) ≤ ∫_{u > 0} f v` for every nonnegative `v ∈ H¹(Ω)`, with no boundary condition on
`v`. -/
theorem energyFormH1_posPart_left_le_setIntegral
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : MemLp f 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    energyFormH1 a 0 0 (W1p.posPart (by norm_num) u) v ≤
      ∫ x in Omega, {x | 0 < W1p.value u x}.indicator f x * W1p.value v x ∂mu := by
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
  have hFm (ε : ℝ) : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0} :=
    measurableSet_lt ((Lp.stronglyMeasurable (W1p.value v)).measurable.const_mul ε)
      ((Lp.stronglyMeasurable (W1p.value u)).measurable.max measurable_const)
  -- Pass to the limit `ε = 1 / (n + 1) → 0` on both sides of the cut-off inequality.
  have hlim := tendsto_setIntegral_indicator_matrixBilinearForm h ha u hv
  have hrhs := tendsto_setIntegral_mul_mul_min hf u hv
  -- Each cut-off integral is bounded by the corresponding integral of the datum.
  have hstep (n : ℕ) : ∫ x in Omega,
      {x | 1 / ((n : ℝ) + 1) * W1p.value v x < max (W1p.value u x) 0}.indicator g x ∂mu ≤
      ∫ x in Omega, f x *
        (((n : ℝ) + 1) * min (max (W1p.value u x) 0) (1 / ((n : ℝ) + 1) * W1p.value v x)) ∂mu := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle := mul_setIntegral_indicator_matrixBilinearForm_le h ha hboundary hu hv
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) (hFm _)
    calc _ = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1) * ∫ x in Omega,
          {x | 1 / ((n : ℝ) + 1) * W1p.value v x < max (W1p.value u x) 0}.indicator g x ∂mu) := by
          field_simp
      _ ≤ ((n : ℝ) + 1) * ∫ x in Omega,
          f x * min (max (W1p.value u x) 0) (1 / ((n : ℝ) + 1) * W1p.value v x) ∂mu :=
          mul_le_mul_of_nonneg_left hle hn.le
      _ = _ := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hint := le_of_tendsto_of_tendsto' hlim hrhs hstep
  -- The limit on the left is `a(u⁺, v)`, because `∇u⁺ = 1_{u > 0} ∇u`.
  rw [energyFormH1_zero_zero_eq_setIntegral]
  refine le_of_eq_of_le (integral_congr_ae ?_) hint
  filter_upwards [W1p.gradient_posPart_ae (by norm_num) u] with x hx
  rw [hx]
  by_cases hux : 0 < W1p.value u x
  · rw [indicator_of_mem (s := {y | 0 < W1p.value u y}) hux,
      indicator_of_mem (s := {y | 0 < W1p.value u y}) hux]
  · rw [indicator_of_notMem (s := {y | 0 < W1p.value u y}) hux,
      indicator_of_notMem (s := {y | 0 < W1p.value u y}) hux, map_zero]

/-- **Subsolutions vanishing on the boundary may be tested against any nonnegative function.**
Let `a` be measurable and uniformly elliptic on `Ω`, and let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≤ 0` on
`∂Ω` in the sense that `u⁺ ∈ H¹₀(Ω)`. Then `a(u⁺, v) ≤ 0` for every nonnegative `v ∈ H¹(Ω)`, with
no boundary condition on `v`. -/
theorem energyFormH1_posPart_left_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    energyFormH1 a 0 0 (W1p.posPart (by norm_num) u) v ≤ 0 := by
  simpa using energyFormH1_posPart_left_le_setIntegral h ha (f := 0) MemLp.zero hboundary
    (fun w hw => by simpa using hu w hw) hv

/-- **The zero extension of the positive part of a subsolution is a subsolution.** Let `a` be
measurable and uniformly elliptic on `Ω`, let `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)`. For every larger open set `Ω' ⊇ Ω` and
every coefficient field `a'` agreeing with `a` on `Ω`, the zero extension `ū ∈ H¹₀(Ω')` of `u⁺`
satisfies `a'(ū, v) ≤ ∫_{u > 0} f v` for every nonnegative `v ∈ H¹(Ω')`. In particular `ū` is a
weak subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_{u > 0} f` on `Ω'`. -/
theorem energyFormH1_extendByZeroL_posPart_le_setIntegral {Omega' : Opens (EuclideanSpace ℝ ι)}
    (hsub : Omega ≤ Omega') {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)))
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : MemLp f 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega' 2} (hv : ∀ᵐ x ∂mu.restrict Omega', 0 ≤ W1p.value v x) :
    energyFormH1 a' 0 0 (W1p0.extendByZeroL hsub ⟨_, hboundary⟩ : W1p mu Omega' 2) v ≤
      ∫ x in Omega, {x | 0 < W1p.value u x}.indicator f x * W1p.value v x ∂mu := by
  rw [energyFormH1_extendByZeroL_left]
  have hres := W1p.value_restrictL_ae hsub v
  have hres' : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL hsub v) x := by
    filter_upwards [hres,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hsub) hv] with x h1 h2
    rw [h1]
    exact h2
  refine le_of_eq_of_le ?_
    ((energyFormH1_posPart_left_le_setIntegral h ha hf hboundary hu hres').trans_eq
      (integral_congr_ae ?_))
  · rw [energyFormH1_def, energyFormH1_def]
    exact setIntegral_congr_fun Omega.isOpen.measurableSet fun x hx => by rw [haa' hx]
  · filter_upwards [hres] with x hx
    rw [hx]

/-- **The zero extension of the positive part of a subsolution is a subsolution.** Let `a` be
measurable and uniformly elliptic on `Ω`, and let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u⁺ ∈ H¹₀(Ω)`. For every larger open set `Ω' ⊇ Ω` and every coefficient
field `a'` agreeing with `a` on `Ω`, the zero extension `ū ∈ H¹₀(Ω')` of `u⁺` satisfies
`a'(ū, v) ≤ 0` for every nonnegative `v ∈ H¹(Ω')`. In particular `ū` is a weak subsolution of
`-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 0` on `Ω'`. -/
theorem energyFormH1_extendByZeroL_posPart_nonpos {Omega' : Opens (EuclideanSpace ℝ ι)}
    (hsub : Omega ≤ Omega') {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)))
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {v : W1p mu Omega' 2} (hv : ∀ᵐ x ∂mu.restrict Omega', 0 ≤ W1p.value v x) :
    energyFormH1 a' 0 0 (W1p0.extendByZeroL hsub ⟨_, hboundary⟩ : W1p mu Omega' 2) v ≤ 0 := by
  simpa using energyFormH1_extendByZeroL_posPart_le_setIntegral hsub haa' h ha (f := 0)
    MemLp.zero hboundary (fun w hw => by simpa using hu w hw) hv

/-- The zero extension of the positive part of a subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with
`u⁺ ∈ H¹₀(Ω)` is a weak subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺` on every larger open set: against a
nonnegative `v`, the datum `1_{u > 0} f` of
`TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral` is at most `f⁺`. -/
private theorem energyFormH1_extendByZeroL_posPart_le_setIntegral_posPart
    {Omega' : Opens (EuclideanSpace ℝ ι)} (hsub : Omega ≤ Omega')
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)))
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : MemLp f 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega' 2} (hv : ∀ᵐ x ∂mu.restrict Omega', 0 ≤ W1p.value v x) :
    energyFormH1 a' 0 0 (W1p0.extendByZeroL hsub ⟨_, hboundary⟩ : W1p mu Omega' 2) v ≤
      ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
  have hΩ : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ Omega' := SetLike.coe_subset_coe.mpr hsub
  have hvΩ : MemLp (W1p.value v) 2 (mu.restrict Omega) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hΩ le_rfl)
  refine (energyFormH1_extendByZeroL_posPart_le_setIntegral hsub haa' h ha hf hboundary hu
    hv).trans (integral_mono_ae ?_ (hf.pos_part.integrable_mul hvΩ) ?_)
  · exact (hf.indicator (measurableSet_lt measurable_const
      (Lp.stronglyMeasurable (W1p.value u)).measurable).nullMeasurableSet).integrable_mul hvΩ
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩ hv] with x hvx
    refine mul_le_mul_of_nonneg_right ?_ hvx
    by_cases hux : x ∈ {x | 0 < W1p.value u x}
    · rw [indicator_of_mem hux]
      exact le_max_left _ _
    · rw [indicator_of_notMem hux]
      exact le_max_right _ _

/-- The whole-space problem behind the boundary estimate: extending `a` by `λ I` off `Ω` gives a
uniformly elliptic field on the whole space, for which the zero extension `ū` of `u⁺` is a weak
subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺`; `ū` equals `u⁺` on `Ω` and vanishes off `Ω`. -/
private theorem exists_uniformlyEllipticOn_top_extendByZeroL_posPart
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : MemLp f 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) a'
        lam Lam ∧
      AEStronglyMeasurable a' (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))) ∧
      ∃ ub : W1p mu ⊤ 2, (∀ v : W1p0 mu ⊤ 2,
        (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
        energyFormH1 a' 0 0 ub (v : W1p mu ⊤ 2) ≤
          ∫ x in Omega, max (f x) 0 * W1p.value (v : W1p mu ⊤ 2) x ∂mu) ∧
      ∀ᵐ x ∂mu, W1p.value ub x =
        (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x := by
  classical
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  set a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ :=
    (Omega : Set (EuclideanSpace ℝ ι)).piecewise a fun _ => lam • (1 : Matrix ι ι ℝ)
  have hI := uniformlyEllipticOn_const_smul_one (n := ι) (univ : Set (EuclideanSpace ℝ ι))
    h.pos le_rfl h.le
  have h' : UniformlyEllipticOn (((⊤ : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι))) a' lam Lam := by
    refine UniformlyEllipticOn.of_bounds h.pos h.le (fun x _ ξ => ?_) (fun x _ η ξ => ?_)
    · by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
      · rw [show a' x = a x from piecewise_eq_of_mem _ _ _ hx]
        exact h.lower_bound hx ξ
      · rw [show a' x = lam • 1 from piecewise_eq_of_notMem _ _ _ hx]
        exact hI.lower_bound (mem_univ x) ξ
    · by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
      · rw [show a' x = a x from piecewise_eq_of_mem _ _ _ hx]
        exact h.upper_bound hx η ξ
      · rw [show a' x = lam • 1 from piecewise_eq_of_notMem _ _ _ hx]
        exact hI.upper_bound (mem_univ x) η ξ
  have ha' : AEStronglyMeasurable a' (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι))) := by
    rw [Opens.coe_top, Measure.restrict_univ]
    exact ha.piecewise hOm.nullMeasurableSet aestronglyMeasurable_const
  set ub : W1p mu ⊤ 2 :=
    ((W1p0.extendByZeroL le_top ⟨_, hboundary⟩ : W1p0 mu ⊤ 2) : W1p mu ⊤ 2)
  have hsubsol : ∀ v : W1p0 mu ⊤ 2,
      (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
      energyFormH1 a' 0 0 ub (v : W1p mu ⊤ 2) ≤
        ∫ x in Omega, max (f x) 0 * W1p.value (v : W1p mu ⊤ 2) x ∂mu := fun v hv =>
    energyFormH1_extendByZeroL_posPart_le_setIntegral_posPart le_top (piecewise_eqOn _ _ _) h ha
      hf hboundary hu hv
  -- The values of the extension: `u⁺` on `Ω` and `0` off `Ω`.
  have hval : ∀ᵐ x ∂mu, W1p.value ub x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x := by
    have hext := coeFn_extendByZeroLpₗᵢ ℝ hOm
      (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.value (W1p.posPart (p := 2)
        (mu := mu) (Omega := Omega) (by norm_num) u))
    simp only [Opens.coe_top, Measure.restrict_univ] at hext
    filter_upwards [hext, (ae_restrict_iff' hOm).1 (Lp.coeFn_posPart (W1p.value u))]
      with x hx hx'
    rw [W1p0.value_extendByZeroL]
    by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxO, ← hx' hxO, ← W1p.value_posPart (by norm_num), hx,
        indicator_of_mem hxO]
    · rw [indicator_of_notMem hxO, hx, indicator_of_notMem hxO]
  exact ⟨a', h', ha', ub, hsubsol, hval⟩

omit [DecidableEq ι] in
/-- The comparison step of the boundary estimate: if `ū ∈ H¹(ℝⁿ)` is a weak subsolution of
`-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺` on the whole space and `z ∈ H¹₀(B)` solves `-∂ᵢ(a'ⁱʲ ∂ⱼz) = 1_Ω f⁺` in an
open set `B`, then `ū|_B - z` is a weak subsolution of the homogeneous equation on `B`. -/
private theorem energyFormH1_restrictL_sub_nonpos {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {f : EuclideanSpace ℝ ι → ℝ} (hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)))
    {B : Opens (EuclideanSpace ℝ ι)} (hBtop : B ≤ ⊤)
    (hcoeff : MemLp (fun x => energyIntegrand (a' x) ((0 : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict B))
    {ub : W1p mu ⊤ 2}
    (hsubsol : ∀ v : W1p0 mu ⊤ 2,
      (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
      energyFormH1 a' 0 0 ub (v : W1p mu ⊤ 2) ≤
        ∫ x in Omega, max (f x) 0 * W1p.value (v : W1p mu ⊤ 2) x ∂mu)
    {z : W1p0 mu B 2}
    (hz : ∀ v : W1p0 mu B 2, energyFormH1 a' 0 0 (z : W1p mu B 2) (v : W1p mu B 2) =
      ∫ x in B, (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
        W1p.value (v : W1p mu B 2) x ∂mu)
    (v : W1p0 mu B 2) (hv : ∀ᵐ x ∂mu.restrict B, 0 ≤ W1p.value (v : W1p mu B 2) x) :
    energyFormH1 a' 0 0 (W1p.restrictL hBtop ub - (z : W1p mu B 2)) (v : W1p mu B 2) ≤ 0 := by
  have hBm : MeasurableSet (B : Set (EuclideanSpace ℝ ι)) := B.isOpen.measurableSet
  obtain ⟨vb, hvb⟩ : ∃ vb : W1p0 mu ⊤ 2, vb = W1p0.extendByZeroL hBtop v := ⟨_, rfl⟩
  have hext : ∀ᵐ x ∂mu, W1p.value (vb : W1p mu ⊤ 2) x =
      (B : Set (EuclideanSpace ℝ ι)).indicator (W1p.value (v : W1p mu B 2)) x := by
    have hext' := coeFn_extendByZeroLpₗᵢ ℝ hBm (SetLike.coe_subset_coe.mpr hBtop)
      (W1p.value (v : W1p mu B 2))
    simp only [Opens.coe_top, Measure.restrict_univ] at hext'
    filter_upwards [hext'] with x hx
    rw [hvb, W1p0.value_extendByZeroL, hx]
  have hextnonneg : ∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
      Set (EuclideanSpace ℝ ι)), 0 ≤ W1p.value (vb : W1p mu ⊤ 2) x := by
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hext, (ae_restrict_iff' hBm).1 hv] with x hx hvx
    rw [hx]
    by_cases hxB : x ∈ (B : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxB]
      exact hvx hxB
    · rw [indicator_of_notMem hxB]
  rw [energyFormH1_sub_left hcoeff, energyFormH1_restrictL, hz v, sub_nonpos, ← hvb]
  refine (hsubsol vb hextnonneg).trans_eq ?_
  rw [← integral_indicator hOm, ← integral_indicator hBm]
  refine integral_congr_ae ?_
  filter_upwards [hext] with x hx
  by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) <;>
    by_cases hxB : x ∈ (B : Set (EuclideanSpace ℝ ι)) <;> simp [hx, hxO, hxB]

/-- Stampacchia's bound for the datum `1_Ω f⁺` on a ball. Let `n ≥ 1` be the dimension and let
`r > 1` with `r > n/2`. There is `C > 0`, depending only on `n`, `r` and the normalization of
`mu`, such that the following holds. Let `a'` be measurable and uniformly elliptic on
`B = B(x₀, 2R)` with constants `λ, Λ`, and let `f ∈ Lʳ(Ω ∩ B(x₀, 2R))`. Then the weak solution
`z ∈ H¹₀(B)` of `-∂ᵢ(a'ⁱʲ ∂ⱼz) = 1_Ω f⁺` in `B` satisfies

`|z| ≤ C R^(2 - n/r) ‖f⁺‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ` almost everywhere on `B`. -/
private theorem exists_forall_energyFormH1_eq_ae_abs_le [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {B : Opens (EuclideanSpace ℝ ι)} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a' lam Lam →
      AEStronglyMeasurable a' (mu.restrict B) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R))) →
      0 < R → (B : Set (EuclideanSpace ℝ ι)) = ball x₀ (2 * R) →
      ∃ z : W1p0 mu B 2, (∀ v : W1p0 mu B 2,
        energyFormH1 a' 0 0 (z : W1p mu B 2) (v : W1p mu B 2) =
          ∫ x in B, (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
            W1p.value (v : W1p mu B 2) x ∂mu) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), |W1p.value (z : W1p mu B 2) x| ≤
          C * R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm (fun x => max (f x) 0) r
            (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrn' : (Fintype.card ι : ℝ) * (2 - r) < 2 * r := by
    nlinarith [mul_pos hn (sub_pos.2 hr1)]
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow (mu := mu) hr hrn
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 2 - (Fintype.card ι : ℝ) / r := ⟨_, rfl⟩
  have hγe : (Fintype.card ι : ℝ) * e = γ := by rw [he, hγ]; field_simp
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = mu.real (ball (0 : EuclideanSpace ℝ ι) 1) := ⟨_, rfl⟩
  have hω0 : 0 < ω := hω ▸ Metric.measureReal_ball_pos mu 0 one_pos
  refine ⟨C * 2 ^ γ * ω ^ e, by positivity, ?_⟩
  intro Omega a' f B x₀ R hBell hBmeas hfr hR hB
  rw [← hγ]
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hBfin : mu B ≠ ∞ := by
    rw [hB]
    exact measure_ball_lt_top.ne
  have hgB : MemLp ((Omega : Set (EuclideanSpace ℝ ι)).indicator fun y => max (f y) 0) r
      (mu.restrict B) := by
    refine (memLp_indicator_iff_restrict hOm.nullMeasurableSet).2 ?_
    rw [Measure.restrict_restrict hOm, hB]
    exact hfr.pos_part
  obtain ⟨z, hz, -⟩ :=
    hBell.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp (c := 0) (gamma := 0) hBmeas
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hBfin hr hrn' hgB
  refine ⟨z, hz, ?_⟩
  have hzb := hstamp (Omega := B) (c := 0) (gamma := 0) hBfin hBell hBmeas
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hgB hz
  -- `‖1_Ω f⁺‖_{Lʳ(B)} = ‖f⁺‖_{Lʳ(Ω ∩ B)}` and `μ(B)^e = (2R)^γ ω^e`.
  have hconst : C * (eLpNorm ((Omega : Set (EuclideanSpace ℝ ι)).indicator fun y => max (f y) 0)
      r (mu.restrict B)).toReal / lam *
        mu.real (B : Set (EuclideanSpace ℝ ι)) ^ (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹) =
      C * 2 ^ γ * ω ^ e * R ^ γ * (eLpNorm (fun x => max (f x) 0) r
        (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hOm.nullMeasurableSet,
      Measure.restrict_restrict hOm, ← he, hB,
      Measure.addHaar_real_ball_rpow mu x₀ (by positivity) e, finrank_euclideanSpace, hγe,
      Real.mul_rpow (by norm_num) hR.le, ← hω]
    ring
  have hBball : ∀ {P : EuclideanSpace ℝ ι → Prop}, (∀ᵐ x ∂mu.restrict B, P x) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), P x := fun hP => hB ▸ hP
  filter_upwards [hBball hzb] with x hx
  exact hx.trans_eq hconst

/-- The comparison step of the boundary estimate. Let `n ≥ 1` be the dimension and let `r > 1`
with `r > n/2`. There is `C > 0`, depending only on `n`, `r` and the normalization of `mu`, such
that the following holds. Let `a'` be measurable and uniformly elliptic on the whole space with
constants `λ, Λ`, let `f ∈ Lʳ(Ω ∩ B(x₀, 2R))`, and let `ū ∈ H¹(ℝⁿ)` be a weak subsolution of
`-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺`. Then on `B = B(x₀, 2R)` there is a weak subsolution `w ∈ H¹(B)` of the
homogeneous equation with

`|ū - w| ≤ C R^(2 - n/r) ‖f⁺‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ` almost everywhere on `B`,

namely `w = ū|_B - z` for the solution `z ∈ H¹₀(B)` of `-∂ᵢ(a'ⁱʲ ∂ⱼz) = 1_Ω f⁺`. -/
private theorem exists_forall_energyFormH1_nonpos_ae_abs_sub_le [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {ub : W1p mu ⊤ 2}
      {B : Opens (EuclideanSpace ℝ ι)} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) a'
        lam Lam →
      AEStronglyMeasurable a' (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R))) →
      (∀ v : W1p0 mu ⊤ 2,
        (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
        energyFormH1 a' 0 0 ub (v : W1p mu ⊤ 2) ≤
          ∫ x in Omega, max (f x) 0 * W1p.value (v : W1p mu ⊤ 2) x ∂mu) →
      0 < R → (B : Set (EuclideanSpace ℝ ι)) = ball x₀ (2 * R) →
      ∃ w : W1p mu B 2, (∀ v : W1p0 mu B 2,
        (∀ᵐ x ∂mu.restrict B, 0 ≤ W1p.value (v : W1p mu B 2) x) →
          energyFormH1 a' 0 0 w (v : W1p mu B 2) ≤ 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), |W1p.value ub x - W1p.value w x| ≤
          C * R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm (fun x => max (f x) 0) r
            (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam := by
  obtain ⟨C, hC, hsplit⟩ := exists_forall_energyFormH1_eq_ae_abs_le (mu := mu) (lam := lam)
    (Lam := Lam) hr hrn
  refine ⟨C, hC, fun {Omega a' f ub B x₀ R} h' ha' hfr hsubsol hR hB => ?_⟩
  have hBtop : B ≤ ⊤ := le_top
  have hBell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a' lam Lam :=
    h'.mono_set (subset_univ _)
  have hBmeas : AEStronglyMeasurable a' (mu.restrict B) :=
    ha'.mono_measure (Measure.restrict_mono (subset_univ _) le_rfl)
  obtain ⟨z, hz, hzb⟩ := hsplit hBell hBmeas hfr hR hB
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hBell.upper_nonneg hBmeas aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hBell.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨W1p.restrictL hBtop ub - (z : W1p mu B 2),
    energyFormH1_restrictL_sub_nonpos Omega.isOpen.measurableSet hBtop hcoeff hsubsol hz, ?_⟩
  have hval : ∀ᵐ x ∂mu.restrict B, W1p.value (W1p.restrictL hBtop ub - (z : W1p mu B 2)) x =
      W1p.value ub x - W1p.value (z : W1p mu B 2) x := by
    filter_upwards [W1p.value_sub_ae (W1p.restrictL hBtop ub) (z : W1p mu B 2),
      W1p.value_restrictL_ae hBtop ub] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hBball : ∀ {P : EuclideanSpace ℝ ι → Prop}, (∀ᵐ x ∂mu.restrict B, P x) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), P x := fun hP => hB ▸ hP
  filter_upwards [hBball hval, hzb] with x h1 h2
  rwa [h1, sub_sub_cancel]

/-- The reduction step of the boundary estimate. Let `n ≥ 1` be the dimension and fix a
proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension and the
normalization of `mu`, such that the following holds. Let `ū ∈ H¹(ℝⁿ)` equal `u⁺` on `Ω` and vanish
off `Ω`, where `u ≤ M` on `Ω ∩ B(x₀, 2R)` with `M ≥ 0`, and let `ū` lie within `S` of a weak
subsolution `w` of the homogeneous equation on `B = B(x₀, 2R)`, for a measurable uniformly
elliptic `a'`. If the complement of `Ω` fills the proportion `θ` of `B(x₀, R)`, then
`u ≤ (1 - δ) M + 2 S` almost everywhere on `Ω ∩ B(x₀, R/2)`. -/
private theorem exists_ae_value_le_mul_add_of_ae_abs_sub_le [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega B : Opens (EuclideanSpace ℝ ι)}
      {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {ub : W1p mu ⊤ 2}
      {w : W1p mu B 2} {x₀ : EuclideanSpace ℝ ι} {R M S : ℝ},
      UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a' lam Lam →
      AEStronglyMeasurable a' (mu.restrict B) →
      (∀ v : W1p0 mu B 2,
        (∀ᵐ x ∂mu.restrict B, 0 ≤ W1p.value (v : W1p mu B 2) x) →
          energyFormH1 a' 0 0 w (v : W1p mu B 2) ≤ 0) →
      0 < R → (B : Set (EuclideanSpace ℝ ι)) = ball x₀ (2 * R) → 0 ≤ M →
      (∀ᵐ x ∂mu, W1p.value ub x =
        (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x) →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), |W1p.value ub x - W1p.value w x| ≤ S) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M + 2 * S := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hθ
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro Omega B a' u ub w x₀ R M S hBell hBmeas hwsub hR hB hM hval hle hwub hθR
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  -- On `B`, `w ≤ ū + S ≤ M + S`; off `Ω`, `ū = 0` and so `w ≤ S`.
  have hle' := (ae_restrict_iff' (hOm.inter measurableSet_ball)).1 hle
  have hwM : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value w x ≤ M + S := by
    filter_upwards [hwub, ae_restrict_of_ae hval, ae_restrict_of_ae hle',
      self_mem_ae_restrict measurableSet_ball] with x hxw hxv hxl hxB
    have hub : W1p.value ub x ≤ M := by
      rw [hxv]
      by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
      · rw [indicator_of_mem hxO]
        exact max_le (hxl ⟨hxO, hxB⟩) hM
      · rw [indicator_of_notMem hxO]
        exact hM
    linarith [neg_abs_le (W1p.value ub x - W1p.value w x)]
  have hRB : ball x₀ R ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  have hSM : S ≤ M + S := by linarith
  -- The complement of `Ω` fills the proportion `θ` of `B(x₀, R)`, so the interior reduction of
  -- the supremum at the level `S` applies to `w`.
  have hred' : ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value w x ≤ M + S - δ * (M + S - S) := by
    refine hred (Omega := B) (a := a') (u := w) (x₀ := x₀) (R := R) (k := S) (M := M + S)
      hBell hBmeas hwsub hR hB.ge hSM hwM (hθR.trans ?_)
    rw [sdiff_eq, inter_comm, ← measureReal_restrict_apply hOm.compl]
    refine ENNReal.toReal_mono ((measure_mono (subset_univ _)).trans_lt ?_).ne
      (measure_mono_ae ?_)
    · rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top
    · filter_upwards [ae_restrict_of_ae hval, ae_restrict_of_ae_restrict_of_subset hRB hwub]
        with x hx hxw hxc
      rw [hx, indicator_of_notMem hxc] at hxw
      linarith [neg_abs_le (0 - W1p.value w x)]
  -- Hence `u ≤ u⁺ = ū ≤ w + S ≤ (1 - δ) M + 2 S` on `Ω ∩ B(x₀, R/2)`.
  rw [ae_restrict_iff' (hOm.inter measurableSet_ball)]
  filter_upwards [hval, (ae_restrict_iff' measurableSet_ball).1 hred',
    (ae_restrict_iff' measurableSet_ball).1 hwub] with x hxv hxr hxw hx
  obtain ⟨hxO, hxB⟩ := hx
  have h1 := hxr hxB
  have h2 := (abs_le.1 (hxw (hR2 hxB))).2
  rw [hxv, indicator_of_mem hxO] at h2
  have h3 := le_max_left (W1p.value u x) 0
  linarith [show δ * (M + S - S) = δ * M by ring, show (1 - δ) * M = M - δ * M by ring]

/-- **Reduction of the supremum at the boundary, with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and let `r > 1` with `r > n/2`. There are
`δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension and the normalization of the additive
Haar measure `mu`, and `K > 0`, depending only on `n`, `r` and `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ L²(Ω)` with
`f ∈ Lʳ(Ω ∩ B(x₀, 2R))`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`, that is
`a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the sense that
`u⁺ ∈ H¹₀(Ω)`. If `u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of `Ω` fills
the proportion `θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then almost everywhere
on `Ω ∩ B(x₀, R/2)`

`u ≤ (1 - δ) M + K R^(2 - n/r) ‖f⁺‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. -/
theorem exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff [Nonempty ι]
    {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f 2 (mu.restrict Omega) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R))) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm (fun x => max (f x) 0) r
            (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ := exists_ae_value_le_mul_add_of_ae_abs_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) hθ
  obtain ⟨C, hC, hcomp⟩ := exists_forall_energyFormH1_nonpos_ae_abs_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) hr hrn
  refine ⟨δ, 2 * C, hδ0, hδ1, by positivity, ?_⟩
  intro Omega a f u x₀ R M h ha hf2 hfr hboundary hu hR hle hθR
  have hlam := h.pos
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = C * R ^ (2 - (Fintype.card ι : ℝ) / r) *
      (eLpNorm (fun x => max (f x) 0) r
        (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam :=
    ⟨_, rfl⟩
  have hS : 0 ≤ S := by rw [hSdef]; positivity
  have h2S : 2 * C * R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm (fun x => max (f x) 0) r
      (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam =
      2 * S := by
    rw [hSdef]
    ring
  rw [h2S]
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball (by linarith))) hle] with x hx
    nlinarith
  -- The zero extension `ū` of `u⁺` is a weak subsolution on the whole space with datum `1_Ω f⁺`,
  -- and on `B = B(x₀, 2R)` it lies within `S` of a weak subsolution `w` of the homogeneous
  -- equation, to which the interior reduction of the supremum applies.
  obtain ⟨a', h', ha', ub, hsubsol, hval⟩ :=
    exists_uniformlyEllipticOn_top_extendByZeroL_posPart h ha hf2 hboundary hu
  obtain ⟨B, hB⟩ : ∃ B : Opens (EuclideanSpace ℝ ι), (B : Set (EuclideanSpace ℝ ι)) =
      ball x₀ (2 * R) := ⟨⟨ball x₀ (2 * R), isOpen_ball⟩, rfl⟩
  obtain ⟨w, hwsub, hwub⟩ := hcomp h' ha' hfr hsubsol hR hB
  rw [← hSdef] at hwub
  exact hred (h'.mono_set (subset_univ _))
    (ha'.mono_measure (Measure.restrict_mono (subset_univ _) le_rfl)) hwsub hR hB hM hval hle
    hwub hθR

/-- **Reduction of the supremum at the boundary (De Giorgi).** Let `n ≥ 1` be the dimension and
fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension
and the normalization of the additive Haar measure `mu`, such that the following holds. Let `a`
be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u ≤ 0` on `∂Ω`, in the sense that `u⁺ ∈ H¹₀(Ω)`. If
`u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of `Ω` fills the proportion
`θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then

`u ≤ (1 - δ) M` almost everywhere on `Ω ∩ B(x₀, R/2)`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. -/
theorem exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff [Nonempty ι] {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M := by
  obtain ⟨δ, K, hδ0, hδ1, -, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ (r := Fintype.card ι + 1)
      (by simpa using Fintype.card_pos (α := ι)) (by push_cast; linarith)
  refine ⟨δ, hδ0, hδ1, fun h ha hboundary hu hR hle hθR => ?_⟩
  simpa using hred (f := 0) h ha MemLp.zero MemLp.zero hboundary
    (fun v hv => by simpa using hu v hv) hR hle hθR

/-- **Geometric decay of the supremum at the boundary (De Giorgi).** Let `n ≥ 1` be the dimension
and fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the
dimension and the normalization of the additive Haar measure `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be
a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u⁺ ∈ H¹₀(Ω)`. If `u ≤ M` almost everywhere on
`Ω ∩ B(x₀, R)` and the complement of `Ω` fills the proportion `θ` of every ball `B(x₀, r)`,
`0 < r ≤ R`, then for every `j`

`u ≤ (1 - δ)ʲ M` almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`. -/
theorem exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff [Nonempty ι]
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        W1p.value u x ≤ (1 - δ) ^ j * M := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff (mu := mu) (lam := lam)
      (Lam := Lam) hθ
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro Omega a u x₀ R M h ha hboundary hu hR hle hext j
  induction j with
  | zero => simpa using hle
  | succ j ih =>
    -- One reduction step from `B(x₀, 2r)` to `B(x₀, r / 2)`, with `2r = R / 4ʲ`.
    set r := R / 4 ^ j / 2 with hr_def
    have h2r : R / 4 ^ j = 2 * r := by rw [hr_def]; ring
    have hr2 : R / 4 ^ (j + 1) = r / 2 := by rw [hr_def, pow_succ]; ring
    have hr : 0 < r := by positivity
    have hrR : r ≤ R := by
      have : R / 4 ^ j ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
      linarith
    rw [h2r] at ih
    rw [hr2, pow_succ, mul_comm ((1 - δ) ^ j) (1 - δ), mul_assoc]
    exact hred h ha hboundary hu hr ih (hext r hr hrR)

/-- **Geometric decay of weak solutions at the boundary (De Giorgi).** Let `n ≥ 1` be the
dimension and fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`,
the dimension and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`. If `|u| ≤ M` almost everywhere on
`Ω ∩ B(x₀, R)` and the complement of `Ω` fills the proportion `θ` of every ball `B(x₀, r)`,
`0 < r ≤ R`, then for every `j`

`|u| ≤ (1 - δ)ʲ M` almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`. -/
theorem exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        |W1p.value u x| ≤ (1 - δ) ^ j * M := by
  obtain ⟨δ, hδ0, hδ1, hdecay⟩ :=
    exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro Omega a u x₀ R M h ha hu0 hu hR hle hext j
  have hneg : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
      W1p.value (-u) x = -W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left (W1p.value_neg_ae u)
  -- Both `u` and `-u` are subsolutions vanishing on the boundary.
  have hpos := hdecay h ha (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) hR (by filter_upwards [hle] with x hx using (abs_le.1 hx).2) hext j
  have hneg' := hdecay h ha
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by rw [energyFormH1_neg_left, hu v, neg_zero]) hR
    (by
      filter_upwards [hle, ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (W1p.value_neg_ae u)] with x hx hx'
      rw [hx', Pi.neg_apply]
      exact neg_le.1 (abs_le.1 hx).1) hext j
  filter_upwards [hpos, hneg', hneg] with x h1 h2 h3
  rw [h3] at h2
  exact abs_le.2 ⟨neg_le.1 h2, h1⟩

/-- The rate of the iterated boundary estimate: for `δ > 0` and `γ > 0` there are `m` and
`τ ∈ (m, 1)` with `τ > 0`, `1 - δ ≤ m` and `4^(-γ) ≤ m`. -/
private theorem exists_le_and_le_and_lt_and_lt {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ m τ : ℝ, 1 - δ ≤ m ∧ (4 : ℝ) ^ (-γ) ≤ m ∧ m < τ ∧ 0 < τ ∧ τ < 1 := by
  have hq0 : 0 < (4 : ℝ) ^ (-γ) := by positivity
  have hq1 : (4 : ℝ) ^ (-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hm0 : (4 : ℝ) ^ (-γ) ≤ max (1 - δ) ((4 : ℝ) ^ (-γ)) := le_max_right _ _
  have hm1 : max (1 - δ) ((4 : ℝ) ^ (-γ)) < 1 := max_lt (by linarith) hq1
  exact ⟨max (1 - δ) ((4 : ℝ) ^ (-γ)), (1 + max (1 - δ) ((4 : ℝ) ^ (-γ))) / 2, le_max_left _ _,
    hm0, by linarith, by linarith, by linarith⟩

/-- The radius factor of the iterated boundary estimate: for `R > 0`, `γ ≥ 0` and a rate `τ`
with `4^(-γ) ≤ τ`, the radii `R / 4ʲ / 2` satisfy `(R / 4ʲ / 2)^γ ≤ R^γ τʲ`. -/
private theorem rpow_div_pow_div_two_le_mul_pow {R γ τ : ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (hτ : (4 : ℝ) ^ (-γ) ≤ τ) (j : ℕ) : (R / 4 ^ j / 2) ^ γ ≤ R ^ γ * τ ^ j := by
  have hpow : (R / 4 ^ j) ^ γ = R ^ γ * ((4 : ℝ) ^ (-γ)) ^ j := by
    rw [Real.div_rpow hR.le (by positivity), ← Real.rpow_natCast_mul (by norm_num),
      mul_comm (j : ℝ), Real.rpow_mul_natCast (by norm_num), Real.rpow_neg (by norm_num),
      inv_pow, div_eq_mul_inv]
  calc (R / 4 ^ j / 2) ^ γ ≤ (R / 4 ^ j) ^ γ :=
        Real.rpow_le_rpow (by positivity) (half_le_self (by positivity)) hγ
    _ = R ^ γ * ((4 : ℝ) ^ (-γ)) ^ j := hpow
    _ ≤ R ^ γ * τ ^ j := by gcongr

/-- The arithmetic of one step of the iterated boundary estimate: if the reduction contracts by
`1 - δ ≤ m` and the error is at most `τʲ (τ - m) D`, with `m ≤ τ`, then the bound `τʲ (M + D)`
improves to `τʲ⁺¹ (M + D)`. -/
private theorem mul_add_le_pow_succ_mul {δ m τ M D E : ℝ} (j : ℕ) (hδm : 1 - δ ≤ m) (hτ : 0 ≤ τ)
    (hmτ : m ≤ τ) (hM : 0 ≤ M) (hD : 0 ≤ D) (hE : E ≤ τ ^ j * ((τ - m) * D)) :
    (1 - δ) * (τ ^ j * (M + D)) + E ≤ τ ^ (j + 1) * (M + D) := by
  have hMD : 0 ≤ τ ^ j * (M + D) := by positivity
  have hcontr : (1 - δ) * (τ ^ j * (M + D)) ≤ m * (τ ^ j * (M + D)) :=
    mul_le_mul_of_nonneg_right hδm hMD
  have hgap : τ ^ j * ((τ - m) * D) ≤ τ ^ j * ((τ - m) * (M + D)) := by
    have : 0 ≤ τ - m := by linarith
    gcongr
    linarith
  have hid : m * (τ ^ j * (M + D)) + τ ^ j * ((τ - m) * (M + D)) = τ ^ (j + 1) * (M + D) := by
    ring
  linarith

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- The iteration behind the geometric decay at the boundary. If a bound `g ≤ M'` on
`s ∩ B(x₀, 2ρ)` always improves to `g ≤ (1 - δ) M' + A ρ^γ` on `s ∩ B(x₀, ρ/2)`, and `g ≤ M` on
`s ∩ B(x₀, R)` with `M ≥ 0`, then `g ≤ τʲ (M + A R^γ / (τ - m))` on `s ∩ B(x₀, R / 4ʲ)` for every
rate `τ > m` with `1 - δ ≤ m` and `4^(-γ) ≤ m`. -/
private theorem ae_le_pow_mul_add_of_forall_ae_le_mul_add {s : Set (EuclideanSpace ℝ ι)}
    {g : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {R M A γ δ m τ : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hγ : 0 ≤ γ) (hδm : 1 - δ ≤ m) (hqm : (4 : ℝ) ^ (-γ) ≤ m)
    (hτ0 : 0 ≤ τ) (hmτ : m < τ) (hle : ∀ᵐ x ∂mu.restrict (s ∩ ball x₀ R), g x ≤ M)
    (hstep : ∀ ρ M', 0 < ρ → 2 * ρ ≤ R → (∀ᵐ x ∂mu.restrict (s ∩ ball x₀ (2 * ρ)), g x ≤ M') →
      ∀ᵐ x ∂mu.restrict (s ∩ ball x₀ (ρ / 2)), g x ≤ (1 - δ) * M' + A * ρ ^ γ) (j : ℕ) :
    ∀ᵐ x ∂mu.restrict (s ∩ ball x₀ (R / 4 ^ j)), g x ≤ τ ^ j * (M + A * R ^ γ / (τ - m)) := by
  have hτm : 0 < τ - m := by linarith
  have hD0 : 0 ≤ A * R ^ γ / (τ - m) := by positivity
  induction j with
  | zero => simpa using hle.mono fun x hx => hx.trans (le_add_of_nonneg_right hD0)
  | succ j ih =>
    -- One step from `B(x₀, 2ρ)` to `B(x₀, ρ / 2)`, with `2ρ = R / 4ʲ`.
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R / 4 ^ j / 2 := ⟨_, rfl⟩
    have h2ρ : R / 4 ^ j = 2 * ρ := by rw [hρdef]; ring
    have hρR : 2 * ρ ≤ R := h2ρ ▸ div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hρ2 : R / 4 ^ (j + 1) = ρ / 2 := by rw [hρdef, pow_succ]; ring
    have hρ : 0 < ρ := by rw [hρdef]; positivity
    have hργ : ρ ^ γ ≤ R ^ γ * τ ^ j :=
      hρdef ▸ rpow_div_pow_div_two_le_mul_pow hR hγ (hqm.trans hmτ.le) j
    have herr : A * ρ ^ γ ≤ τ ^ j * ((τ - m) * (A * R ^ γ / (τ - m))) := by
      rw [mul_div_cancel₀ _ hτm.ne']
      calc _ ≤ A * (R ^ γ * τ ^ j) := by gcongr
        _ = _ := by ring
    have hnext := mul_add_le_pow_succ_mul j hδm hτ0 hmτ.le hM hD0 herr
    rw [hρ2]
    filter_upwards [hstep ρ _ hρ hρR (by rw [← h2ρ]; exact ih)] with x hx
    linarith

/-- **Geometric decay of the supremum at the boundary, with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and let `r > 1` with `r > n/2`. There are
`τ ∈ (0, 1)` and `K > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `r` and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, let `f ∈ L²(Ω)` with `f ∈ Lʳ(Ω ∩ B(x₀, R))`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)`. If `u ≤ M` almost
everywhere on `Ω ∩ B(x₀, R)` and the complement of `Ω` fills the proportion `θ` of every ball
`B(x₀, ρ)`, `0 < ρ ≤ R`, then for every `j`, almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`,

`u ≤ τʲ (M + K R^(2 - n/r) ‖f⁺‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)`. -/
theorem exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ τ K : ℝ, 0 < τ ∧ τ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f 2 (mu.restrict Omega) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ ρ, 0 < ρ → ρ ≤ R →
        θ * mu.real (ball x₀ ρ) ≤ mu.real (ball x₀ ρ \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        W1p.value u x ≤ τ ^ j * (M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm (fun x => max (f x) 0) r
            (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam) := by
  obtain ⟨δ, K₀, hδ0, hδ1, hK₀, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ hr hrn
  have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 2 - (Fintype.card ι : ℝ) / r := ⟨_, rfl⟩
  have hγ0 : 0 < γ := hγ ▸ sub_pos.2 ((div_lt_iff₀ hr0).2 (by linarith only [hrn]))
  -- One step contracts by `m < 1` up to an error shrinking by `4^(-γ) ≤ m`; the rate is `τ`.
  obtain ⟨m, τ, hδm, hqm, hτm', hτpos, hτ1⟩ := exists_le_and_le_and_lt_and_lt hδ0 hγ0
  have hτm : 0 < τ - m := by linarith
  refine ⟨τ, K₀ / (τ - m), hτpos, hτ1, div_pos hK₀ hτm, ?_⟩
  intro Omega a f u x₀ R M h ha hf2 hfr hboundary hu hR hle hext j
  rw [← hγ]
  have hlam := h.pos
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (eLpNorm (fun x => max (f x) 0) r
      (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal := ⟨_, rfl⟩
  rw [← hF]
  have hF0 : 0 ≤ F := hF ▸ ENNReal.toReal_nonneg
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    have hK : 0 ≤ τ ^ j * (K₀ / (τ - m) * R ^ γ * F / lam) := by positivity
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _
      (ball_subset_ball (div_le_self hR.le (one_le_pow₀ (by norm_num))))) hle] with x hx
    nlinarith [pow_le_one₀ (n := j) hτpos.le hτ1.le]
  -- One reduction step from `B(x₀, 2ρ)` to `B(x₀, ρ / 2)` loses at most `K₀ ρ^γ F / λ`.
  have hstep : ∀ ρ M', 0 < ρ → 2 * ρ ≤ R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * ρ)),
        W1p.value u x ≤ M') →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (ρ / 2)),
        W1p.value u x ≤ (1 - δ) * M' + K₀ * F / lam * ρ ^ γ := by
    intro ρ M' hρ hρR hM'
    have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * ρ) ⊆
        (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
      inter_subset_inter_right _ (ball_subset_ball hρR)
    have hFρ : (eLpNorm (fun x => max (f x) 0) r
        (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * ρ)))).toReal ≤ F := by
      rw [hF]
      exact ENNReal.toReal_mono hfr.pos_part.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
    have hred' := hred h ha hf2 (hfr.mono_measure (Measure.restrict_mono hsub le_rfl)) hboundary
      hu hρ hM' (hext ρ hρ (by linarith))
    rw [← hγ] at hred'
    filter_upwards [hred'] with x hx
    refine hx.trans (add_le_add_right ?_ _)
    calc _ ≤ K₀ * ρ ^ γ * F / lam := by gcongr
      _ = _ := by ring
  have hDeq : K₀ / (τ - m) * R ^ γ * F / lam = K₀ * F / lam * R ^ γ / (τ - m) := by
    field_simp
  rw [hDeq]
  exact ae_le_pow_mul_add_of_forall_ae_le_mul_add hR hM (by positivity) hγ0.le hδm hqm hτpos.le hτm'
    hle hstep j

/-- **Geometric decay of weak solutions at the boundary, with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0` and let `r > 1` with `r > n/2`. There are
`τ ∈ (0, 1)` and `K > 0`, depending only on `λ`, `Λ`, `θ`, `n`, `r` and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, let `f ∈ L²(Ω)` with `f ∈ Lʳ(Ω ∩ B(x₀, R))`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`. If `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the complement of `Ω` fills the
proportion `θ` of every ball `B(x₀, ρ)`, `0 < ρ ≤ R`, then for every `j`, almost everywhere on
`Ω ∩ B(x₀, R / 4ʲ)`,

`|u| ≤ τʲ (M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)`.

This is the boundary step of the global Hölder estimate for the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, `u = 0` on `∂Ω`. -/
theorem exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ τ K : ℝ, 0 < τ ∧ τ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f 2 (mu.restrict Omega) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ ρ, 0 < ρ → ρ ≤ R →
        θ * mu.real (ball x₀ ρ) ≤ mu.real (ball x₀ ρ \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        |W1p.value u x| ≤ τ ^ j * (M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
            lam) := by
  obtain ⟨τ, K, hτ0, hτ1, hK, hdecay⟩ :=
    exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ hr hrn
  refine ⟨τ, K, hτ0, hτ1, hK, ?_⟩
  intro Omega a f u x₀ R M h ha hf2 hfr hu0 hu hR hle hext j
  have hlam := h.pos
  -- The datum enters through `f⁺` for `u` and through `(-f)⁺` for `-u`, both bounded by `|f|`.
  have hnorm (g : EuclideanSpace ℝ ι → ℝ)
      (hgm : AEStronglyMeasurable g (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
        ball x₀ R))) (hg : ∀ x, |g x| ≤ |f x|) :
      τ ^ j * (M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm g r
        (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam) ≤
      τ ^ j * (M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r
        (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal / lam) := by
    have hgf := ENNReal.toReal_mono hfr.eLpNorm_ne_top
      (eLpNorm_mono hgm fun x => by simpa only [Real.norm_eq_abs] using hg x)
    gcongr
  have hpos := hdecay h ha hf2 hfr (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) hR (hle.mono fun x hx => (abs_le.1 hx).2) hext j
  have hneg := hdecay (f := fun x => -f x) (u := -u) h ha hf2.neg hfr.neg
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by simp [energyFormH1_neg_left, hu v, integral_neg]) hR
    (by
      filter_upwards [hle, ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (W1p.value_neg_ae u)] with x hx hx'
      rw [hx', Pi.neg_apply]
      exact neg_le.1 (abs_le.1 hx).1) hext j
  have hb₁ := hnorm (fun x => max (f x) 0) hfr.pos_part.aestronglyMeasurable fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hb₂ := hnorm (fun x => max (-f x) 0) hfr.neg.pos_part.aestronglyMeasurable fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  filter_upwards [hpos, hneg, ae_restrict_of_ae_restrict_of_subset inter_subset_left
    (W1p.value_neg_ae u)] with x h1 h2 h3
  rw [h3, Pi.neg_apply] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

end PDE

end TauCeti
