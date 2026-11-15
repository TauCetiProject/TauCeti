/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.PDE.Regularity.Oscillation
public import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous

/-!
# De Giorgi's oscillation decay at the boundary

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, let `f ∈ L²(Ω)`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u ≤ 0` on `∂Ω`, in the sense that
`u⁺ ∈ H¹₀(Ω)`. Nothing is assumed about the regularity of `∂Ω`. This file proves De Giorgi's
estimate at boundary points: if the complement of `Ω` fills a fixed proportion `θ > 0` of the
ball `B(x₀, R)` and `f ∈ Lʳ` with `r > 1` and `r > n/2`, then the supremum of `u⁺` drops by a
fixed factor from `Ω ∩ B(x₀, 2R)` to `Ω ∩ B(x₀, R/2)`, up to an error
`K R^(2 - n/r) ‖f‖_{Lʳ} / λ`; and if the complement fills that proportion of every ball
`B(x₀, ρ)`, `ρ ≤ R`, the supremum decays geometrically along the balls `B(x₀, R / 4ʲ)`. For
`f = 0` there is no error term.

The proof reduces the boundary estimate to the interior one.

* **Testing against functions without boundary values.** For a subsolution with `u⁺ ∈ H¹₀(Ω)`,
  the inequality `a(u⁺, v) ≤ ∫_Ω f⁺ v` holds for every nonnegative `v ∈ H¹(Ω)`, not only for
  `v ∈ H¹₀(Ω)` (`TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`). The test function is
  `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺`, which lies in `H¹₀(Ω)` because `u⁺` does
  (`TauCeti.W1p.posPart_sub_mem_w1p0Submodule`), and which lies between `0` and `ε v`. On
  `{u⁺ ≤ ε v}` its gradient is `∇u⁺` and contributes the nonnegative energy `⟨a ∇u⁺, ∇u⁺⟩`; on
  `{u⁺ > ε v}` it is `ε ∇v`. Dividing by `ε` and letting `ε → 0`, dominated convergence turns the
  indicator of `{u⁺ > ε v}` into that of `{u > 0}`, which is `a(u⁺, v)`.
* **The zero extension is a subsolution.** Hence the zero extension of `u⁺` to a larger open set
  `Ω'` satisfies `a'(ū, v) ≤ ∫_{Ω'} 1_Ω f⁺ v` for every nonnegative `v ∈ H¹(Ω')`, for every
  coefficient field `a'` agreeing with `a` on `Ω`
  (`TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`).
* **Reduction of the supremum.** Extending `a` by `λ I` off `Ω`, the zero extension is a weak
  subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺` on the whole space, and it vanishes on `B(x₀, R) \ Ω`.
  De Giorgi's interior reduction of the supremum with a right-hand side
  (`TauCeti.PDE.exists_ae_value_le_sub_mul_sub_add_of_memLp`) at the level `0` therefore applies
  with the proportion `θ`
  (`TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).
* **Geometric decay.** Iterating the reduction along `B(x₀, R / 4ʲ)`, the supremum shrinks by
  `1 - δ` and the error term by `4^(-(2 - n/r))` from one ball to the next, so both decay like
  `σʲ` for `σ = max (1 - δ/2) 4^(-(2 - n/r)) < 1`.

The exterior density hypothesis `θ |B(x₀, r)| ≤ |B(x₀, r) \ Ω|` for all small `r` is an
exterior measure density condition at `x₀`. An exterior cone with vertex `x₀` gives it, with `θ`
depending only on the aperture of the cone, for every `r` up to the height of the cone. For a
weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` both `u` and `-u` are such subsolutions, with
data `f` and `-f`, so `|u|` decays geometrically towards boundary points
(`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).
This is the boundary step of the global Hölder estimate for the Dirichlet problem.

## Main declarations

* `TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`: `a(u⁺, v) ≤ ∫_Ω f⁺ v` for every
  nonnegative `v ∈ H¹(Ω)`; `TauCeti.PDE.energyFormH1_posPart_left_nonpos` is the case `f = 0`.
* `TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`: the zero extension of `u⁺` is
  a weak subsolution on every larger open set;
  `TauCeti.PDE.energyFormH1_extendByZeroL_posPart_nonpos` is the case `f = 0`.
* `TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`:
  the reduction of the supremum at the boundary; for `f = 0`,
  `TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`.
* `TauCeti.PDE.exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`:
  its iteration, geometric decay of the supremum; for `f = 0`,
  `TauCeti.PDE.exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`.
* `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`:
  geometric decay of `|u|` for weak solutions in `H¹₀(Ω)`; for `f = 0`,
  `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.25, 8.27 and 8.29.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped NNReal Topology

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

/-- The cut-off step of the test-function argument: for `ε > 0`, the density `⟨a ∇u, ∇v⟩` of
a subsolution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)` and `f ∈ L²(Ω)` against a nonnegative
`v ∈ H¹(Ω)`, cut off to `{u⁺ > ε v}`, has integral at most `∫_Ω f⁺ v`. It is `ε⁻¹` times a lower
bound for the energy of `u` against the test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺ ∈ H¹₀(Ω)`,
which lies between `0` and `ε v`. -/
private theorem setIntegral_indicator_matrixBilinearForm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) {ε : ℝ}
    (hε : 0 < ε) (hFm : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0}) :
    ∫ x in Omega, {x | ε * W1p.value v x < max (W1p.value u x) 0}.indicator
      (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu ≤
      ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
  set up := W1p.posPart (p := 2) (mu := mu) (Omega := Omega) (by norm_num) u
  have hεv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (ε • v) x := by
    filter_upwards [W1p.value_smul_ae ε v, hv] with x hx hvx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hε.le hvx
  -- The test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` lies in `H¹₀(Ω)`, between `0` and `ε v`.
  have hmem : up - W1p.posPart (by norm_num) (up - ε • v) ∈ w1p0Submodule mu Omega 2 :=
    (w1p0Submodule mu Omega 2).toSubmodule.sub_mem hboundary
      (W1p.posPart_sub_mem_w1p0Submodule (by norm_num) hboundary hεv)
  have hbounds : ∀ᵐ x ∂mu.restrict Omega,
      0 ≤ W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x ∧
        W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x ≤ ε * W1p.value v x := by
    filter_upwards [W1p.value_sub_ae up (W1p.posPart (by norm_num) (up - ε • v)),
      Lp.coeFn_posPart (W1p.value (up - ε • v)), W1p.value_sub_ae up (ε • v),
      Lp.coeFn_posPart (W1p.value u), hεv, W1p.value_smul_ae ε v] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.sub_apply, W1p.value_posPart (u := up - ε • v), h2, h3, Pi.sub_apply,
      W1p.value_posPart, h4]
    rw [h6, Pi.smul_apply, smul_eq_mul] at h5 ⊢
    refine ⟨?_, by linarith [le_max_left (max (W1p.value u x) 0 - ε * W1p.value v x) 0]⟩
    rcases le_total (max (W1p.value u x) 0 - ε * W1p.value v x) 0 with hle | hle
    · rw [max_eq_right hle, sub_zero]
      exact le_max_right _ _
    · rw [max_eq_left hle]
      linarith
  have htest := hu ⟨_, hmem⟩ (hbounds.mono fun _ hx => hx.1)
  rw [energyFormH1_zero_zero_eq_setIntegral] at htest
  -- The pairing with `f` is at most `ε ∫_Ω f⁺ v`, since the test function lies in `[0, ε v]`.
  have hrhs : ∫ x in Omega, f x *
      W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x ∂mu ≤
      ε * ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hf.integrable_mul (Lp.memLp _))
      ((hf.pos_part.integrable_mul (Lp.memLp _)).const_mul ε) ?_
    filter_upwards [hbounds] with x hx
    calc f x * W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x
        ≤ max (f x) 0 * W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx.1
      _ ≤ max (f x) 0 * (ε * W1p.value v x) := mul_le_mul_of_nonneg_left hx.2 (le_max_right _ _)
      _ = ε * (max (f x) 0 * W1p.value v x) := by ring
  have hle := (integral_mono_ae
    (((integrable_matrixBilinearForm_gradient h ha u v).indicator hFm).const_mul ε)
    (integrable_matrixBilinearForm_gradient h ha u _)
    (mul_indicator_le_matrixBilinearForm_gradient h u v)).trans (htest.trans hrhs)
  rw [integral_const_mul] at hle
  exact le_of_mul_le_mul_left hle hε

/-- **Subsolutions vanishing on the boundary may be tested against any nonnegative function.**
Let `a` be measurable and uniformly elliptic on `Ω`, let `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`, that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative
`v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the sense that `u⁺ ∈ H¹₀(Ω)`. Then `a(u⁺, v) ≤ ∫_Ω f⁺ v`
for every nonnegative `v ∈ H¹(Ω)`, with no boundary condition on `v`. -/
theorem energyFormH1_posPart_left_le_setIntegral
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) :
    energyFormH1 a 0 0 (W1p.posPart (by norm_num) u) v ≤
      ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
  have hg : Integrable g (mu.restrict Omega) := integrable_matrixBilinearForm_gradient h ha u v
  have hFm (ε : ℝ) : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0} :=
    measurableSet_lt ((Lp.stronglyMeasurable (W1p.value v)).measurable.const_mul ε)
      ((Lp.stronglyMeasurable (W1p.value u)).measurable.max measurable_const)
  -- Dominated convergence along `ε = 1 / (n + 1)`: the cut-offs `1_{u⁺ > ε v}` converge to
  -- `1_{u > 0}`, and each cut-off integral is at most `∫_Ω f⁺ v`.
  have hlim : Tendsto (fun n : ℕ => ∫ x in Omega,
      {x | 1 / ((n : ℝ) + 1) * W1p.value v x < max (W1p.value u x) 0}.indicator g x ∂mu) atTop
      (𝓝 (∫ x in Omega, {x | 0 < W1p.value u x}.indicator g x ∂mu)) := by
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
  have hint : ∫ x in Omega, {x | 0 < W1p.value u x}.indicator g x ∂mu ≤
      ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu :=
    le_of_tendsto' hlim fun n => setIntegral_indicator_matrixBilinearForm_le h ha hf hboundary
      hu hv (by positivity) (hFm _)
  -- The limit is `a(u⁺, v)`, because `∇u⁺ = 1_{u > 0} ∇u`.
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
no boundary condition on `v`. This is the case `f = 0` of
`TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`. -/
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
    (fun v hv => by simpa using hu v hv) hv

/-- **The zero extension of the positive part of a subsolution is a subsolution.** Let `a` be
measurable and uniformly elliptic on `Ω`, let `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)`. For every larger open set `Ω' ⊇ Ω` and
every coefficient field `a'` agreeing with `a` on `Ω`, the zero extension `ū ∈ H¹₀(Ω')` of `u⁺`
satisfies `a'(ū, v) ≤ ∫_{Ω'} 1_Ω f⁺ v` for every nonnegative `v ∈ H¹(Ω')`. In particular `ū` is a
weak subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺` on `Ω'`. -/
theorem energyFormH1_extendByZeroL_posPart_le_setIntegral {Omega' : Opens (EuclideanSpace ℝ ι)}
    (hsub : Omega ≤ Omega') {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)))
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega' 2} (hv : ∀ᵐ x ∂mu.restrict Omega', 0 ≤ W1p.value v x) :
    energyFormH1 a' 0 0 (W1p0.extendByZeroL hsub ⟨_, hboundary⟩ : W1p mu Omega' 2) v ≤
      ∫ x in Omega', (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
        W1p.value v x ∂mu := by
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hsub' : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ Omega' := SetLike.coe_subset_coe.mpr hsub
  rw [energyFormH1_extendByZeroL_left]
  have hres : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL hsub v) x := by
    filter_upwards [W1p.value_restrictL_ae hsub v, ae_restrict_of_ae_restrict_of_subset hsub' hv]
      with x h1 h2
    rw [h1]
    exact h2
  refine le_of_eq_of_le ?_
    ((energyFormH1_posPart_left_le_setIntegral h ha hf hboundary hu hres).trans_eq ?_)
  · rw [energyFormH1_def, energyFormH1_def]
    exact setIntegral_congr_fun Omega.isOpen.measurableSet fun x hx => by rw [haa' hx]
  · -- `∫_Ω f⁺ v|_Ω = ∫_{Ω'} 1_Ω f⁺ v`.
    calc ∫ x in Omega, max (f x) 0 * W1p.value (W1p.restrictL hsub v) x ∂mu
        = ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [W1p.value_restrictL_ae hsub v] with x hx
          rw [hx]
      _ = ∫ x in Omega', (Omega : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => max (f y) 0 * W1p.value v y) x ∂mu := by
          rw [integral_indicator hOm, Measure.restrict_restrict hOm, inter_eq_left.2 hsub']
      _ = _ := by simp only [indicator_mul_left]

/-- **The zero extension of the positive part of a subsolution is a subsolution.** Let `a` be
measurable and uniformly elliptic on `Ω`, and let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u⁺ ∈ H¹₀(Ω)`. For every larger open set `Ω' ⊇ Ω` and every coefficient
field `a'` agreeing with `a` on `Ω`, the zero extension `ū ∈ H¹₀(Ω')` of `u⁺` satisfies
`a'(ū, v) ≤ 0` for every nonnegative `v ∈ H¹(Ω')`. In particular `ū` is a weak subsolution of
`-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 0` on `Ω'`. This is the case `f = 0` of
`TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`. -/
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
  simpa using energyFormH1_extendByZeroL_posPart_le_setIntegral hsub haa' h ha (f := 0) MemLp.zero
    hboundary (fun v hv => by simpa using hu v hv) hv

/-- The whole-space problem behind the boundary estimate: extending `a` by `λ I` off `Ω` gives a
uniformly elliptic field on the whole space, for which the zero extension `ū` of `u⁺` is a weak
subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ 1_Ω f⁺`; `ū` equals `u⁺` on `Ω` and vanishes off `Ω`. -/
private theorem exists_uniformlyEllipticOn_top_extendByZeroL_posPart
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega))
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
          ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
            (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
              W1p.value (v : W1p mu ⊤ 2) x ∂mu) ∧
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
        ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
            W1p.value (v : W1p mu ⊤ 2) x ∂mu := fun v hv =>
    energyFormH1_extendByZeroL_posPart_le_setIntegral le_top (piecewise_eqOn _ _ _) h ha hf
      hboundary hu hv
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
/-- An exponent `r > 1` with `r > n/2`, to instantiate the estimates with a right-hand side at
`f = 0`. -/
private theorem exists_one_lt_card_lt_two_mul [Nonempty ι] :
    ∃ r : ℝ≥0, 1 < r ∧ (Fintype.card ι : ℝ) < 2 * r :=
  ⟨Fintype.card ι + 1, lt_add_of_pos_left 1 (Nat.cast_pos.2 Fintype.card_pos), by
    push_cast
    linarith [(Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)]⟩

omit [DecidableEq ι] in
/-- The hypotheses of the interior reduction for the zero extension `ū` of `u⁺`: if `u ≤ M`
on `Ω ∩ B(x₀, 2R)` with `M ≥ 0`, then `ū ≤ M` on `B(x₀, 2R)`; and `ū` vanishes on
`B(x₀, R) \ Ω`, so `{ū ≤ 0}` fills at least the proportion of `B(x₀, R)` that the complement of
`Ω` fills. -/
private theorem ae_value_le_and_mul_measureReal_le_of_ae_eq_indicator {u : W1p mu Omega 2}
    {ub : W1p mu ⊤ 2}
    (hval : ∀ᵐ x ∂mu, W1p.value ub x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x)
    {x₀ : EuclideanSpace ℝ ι} {R M θ : ℝ} (hM : 0 ≤ M)
    (hle : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
      W1p.value u x ≤ M)
    (hθR : θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι)))) :
    (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value ub x ≤ M) ∧
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value ub x ≤ 0} := by
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  constructor
  · rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hval, (ae_restrict_iff' (hOm.inter measurableSet_ball)).1 hle]
      with x hx hx' hxb
    rw [hx]
    by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxO]
      exact max_le (hx' ⟨hxO, hxb⟩) hM
    · rw [indicator_of_notMem hxO]
      exact hM
  · refine hθR.trans ?_
    rw [Set.sdiff_eq, inter_comm, ← measureReal_restrict_apply hOm.compl]
    refine ENNReal.toReal_mono ((measure_mono (subset_univ _)).trans_lt ?_).ne
      (measure_mono_ae ?_)
    · rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top
    · filter_upwards [ae_restrict_of_ae hval] with x hx hxc
      rw [hx, indicator_of_notMem hxc]

/-- **Reduction of the supremum at the boundary with a right-hand side (De Giorgi).** Let `n ≥ 1`
be the dimension, fix a proportion `θ > 0`, and let `r > 1` with `r > n/2`. There are
`δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension and the normalization of the additive
Haar measure `mu`, and `K > 0`, depending only on `n`, `r` and `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ L²(Ω)`, and
let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`, that is `a(u, v) ≤ ∫_Ω f v` for every
nonnegative `v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the sense that `u⁺ ∈ H¹₀(Ω)`. If
`f ∈ Lʳ(Ω ∩ B(x₀, 2R))`, `u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of `Ω`
fills the proportion `θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then

`u ≤ (1 - δ) M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ` almost everywhere on
`Ω ∩ B(x₀, R/2)`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. -/
theorem exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
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
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r
            (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal / lam := by
  obtain ⟨δ, K, hδ0, hδ1, hK, hred⟩ := exists_ae_value_le_sub_mul_sub_add_of_memLp (mu := mu)
    (lam := lam) (Lam := Lam) hθ hr hrn
  refine ⟨δ, K, hδ0, hδ1, hK, ?_⟩
  intro Omega a f u x₀ R M h ha hf2 hfr hboundary hu hle hθR
  rcases le_or_gt R 0 with hR | hR
  · -- For `R ≤ 0` the ball `B(x₀, R/2)` is empty.
    simp [ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have hlam := h.pos
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  set γ : ℝ := 2 - (Fintype.card ι : ℝ) / r
  set F := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)))).toReal
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    have hE : 0 ≤ K * R ^ γ * F / lam := by positivity
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ hR2) hle]
      with x hx
    nlinarith
  -- Extend `a` by `λ I` off `Ω` and `u⁺` by zero: a weak subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ g` on
  -- the whole space, with `g = 1_Ω f⁺`, and `‖g‖_{Lʳ(B(x₀, 2R))} ≤ ‖f‖_{Lʳ(Ω ∩ B(x₀, 2R))}`.
  obtain ⟨a', h', ha', ub, hsubsol, hval⟩ :=
    exists_uniformlyEllipticOn_top_extendByZeroL_posPart h ha hf2 hboundary hu
  set g := (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0)
  have hg : MemLp g r (mu.restrict (ball x₀ (2 * R))) := by
    rw [memLp_indicator_iff_restrict hOm.nullMeasurableSet, Measure.restrict_restrict hOm]
    exact hfr.pos_part
  have hgF : (eLpNorm g r (mu.restrict (ball x₀ (2 * R)))).toReal ≤ F := by
    refine ENNReal.toReal_mono hfr.eLpNorm_lt_top.ne ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hOm.nullMeasurableSet, Measure.restrict_restrict hOm]
    refine eLpNorm_mono hfr.pos_part.aestronglyMeasurable fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_max_le_max_abs_abs.trans (by rw [abs_zero, max_eq_left (abs_nonneg _)])
  obtain ⟨hM', hθ'⟩ := ae_value_le_and_mul_measureReal_le_of_ae_eq_indicator hval hM hle hθR
  have hred' := hred h' ha' hg hsubsol (by simp) hM' hθ'
  have hE : K * R ^ γ * (eLpNorm g r (mu.restrict (ball x₀ (2 * R)))).toReal / lam ≤
      K * R ^ γ * F / lam := by gcongr
  rw [ae_restrict_iff' (hOm.inter measurableSet_ball)]
  filter_upwards [hval, (ae_restrict_iff' measurableSet_ball).1 hred'] with x hx hx' hxO
  have hle' := hx' hxO.2
  rw [hx, indicator_of_mem hxO.1] at hle'
  linarith [le_max_left (W1p.value u x) 0]

/-- **Reduction of the supremum at the boundary (De Giorgi).** Let `n ≥ 1` be the dimension and
fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension
and the normalization of the additive Haar measure `mu`, such that the following holds. Let `a`
be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u ≤ 0` on `∂Ω`, in the sense that `u⁺ ∈ H¹₀(Ω)`. If
`u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of `Ω` fills the proportion
`θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then

`u ≤ (1 - δ) M` almost everywhere on `Ω ∩ B(x₀, R/2)`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. This is the case
`f = 0` of
`TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`. -/
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
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
        W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
        W1p.value u x ≤ (1 - δ) * M := by
  obtain ⟨r, hr, hrn⟩ := exists_one_lt_card_lt_two_mul (ι := ι)
  obtain ⟨δ, _K, hδ0, hδ1, -, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ hr hrn
  exact ⟨δ, hδ0, hδ1, fun h ha hboundary hu hle hθR => by
    simpa using hred h ha (f := 0) MemLp.zero MemLp.zero hboundary
      (fun v hv => by simpa using hu v hv) hle hθR⟩

omit [DecidableEq ι] in
/-- The arithmetic of one step of geometric decay: for `σ ≥ 1 - δ/2`, a bound `σʲ Q` with
`Q = M + 2A/δ`, `M, A ≥ 0`, reduced by the factor `1 - δ` and increased by at most `A σʲ`, is at
most `σʲ⁺¹ Q`. -/
private theorem mul_pow_mul_add_le_pow_succ_mul {δ σ M A E : ℝ} (j : ℕ) (hδ : 0 < δ)
    (hσ0 : 0 ≤ σ) (hσ : 1 - δ / 2 ≤ σ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hE : E ≤ A * σ ^ j) :
    (1 - δ) * (σ ^ j * (M + 2 / δ * A)) + E ≤ σ ^ (j + 1) * (M + 2 / δ * A) := by
  set Q := M + 2 / δ * A with hQ_def
  have hQ : 0 ≤ Q := by positivity
  -- `A ≤ δ/2 · Q` and `σ - 1 + δ ≥ δ/2`.
  have hAQ : A ≤ δ / 2 * Q := by
    have hQ' : δ / 2 * Q = δ / 2 * M + A := by
      rw [hQ_def]
      field_simp
    have : 0 ≤ δ / 2 * M := by positivity
    linarith
  have hkey : 0 ≤ σ ^ j * ((σ - 1 + δ) * Q - A) := by
    refine mul_nonneg (pow_nonneg hσ0 j) ?_
    have : δ / 2 * Q ≤ (σ - 1 + δ) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ
    linarith
  have hexpand : σ ^ (j + 1) * Q - ((1 - δ) * (σ ^ j * Q) + A * σ ^ j) =
      σ ^ j * ((σ - 1 + δ) * Q - A) := by
    ring
  linarith

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- The iteration behind geometric decay: if a bound `g ≤ M'` on `S ∩ B(x₀, 2ρ)` always improves
to `g ≤ (1 - δ) M' + A (ρ/R)^γ` on `S ∩ B(x₀, ρ/2)` when `2ρ ≤ R`, then from `g ≤ M`, `M ≥ 0`, on
`S ∩ B(x₀, R)` follows `g ≤ σʲ (M + 2A/δ)` on `S ∩ B(x₀, R / 4ʲ)`, with
`σ = max (1 - δ/2) 4^(-γ)`. -/
private theorem ae_le_pow_mul_add_of_forall_ae_le_mul_add {S : Set (EuclideanSpace ℝ ι)}
    {g : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {R M A δ γ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) (hγ : 0 < γ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hle : ∀ᵐ x ∂mu.restrict (S ∩ ball x₀ R), g x ≤ M)
    (hstep : ∀ ρ M', 0 < ρ → 2 * ρ ≤ R →
      (∀ᵐ x ∂mu.restrict (S ∩ ball x₀ (2 * ρ)), g x ≤ M') →
        ∀ᵐ x ∂mu.restrict (S ∩ ball x₀ (ρ / 2)), g x ≤ (1 - δ) * M' + A * (ρ / R) ^ γ)
    (j : ℕ) :
    ∀ᵐ x ∂mu.restrict (S ∩ ball x₀ (R / 4 ^ j)),
      g x ≤ max (1 - δ / 2) ((4 : ℝ) ^ γ)⁻¹ ^ j * (M + 2 / δ * A) := by
  set τ : ℝ := ((4 : ℝ) ^ γ)⁻¹ with hτ_def
  have hτ0 : 0 ≤ τ := by positivity
  have hσ0 : 0 ≤ max (1 - δ / 2) τ := hτ0.trans (le_max_right _ _)
  induction j with
  | zero =>
    have : 0 ≤ 2 / δ * A := by positivity
    simpa using hle.mono fun x hx => hx.trans (by linarith)
  | succ j ih =>
    -- One step from `B(x₀, 2ρ)` to `B(x₀, ρ / 2)`, with `2ρ = R / 4ʲ`.
    set ρ := R / 4 ^ j / 2 with hρ_def
    have h2ρ : R / 4 ^ j = 2 * ρ := by rw [hρ_def]; ring
    have hρ2 : R / 4 ^ (j + 1) = ρ / 2 := by rw [hρ_def, pow_succ]; ring
    have hρ : 0 < ρ := by positivity
    have hρR : 2 * ρ ≤ R := by
      rw [← h2ρ]
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    rw [h2ρ] at ih
    rw [hρ2]
    refine (hstep ρ _ hρ hρR ih).mono fun x hx => hx.trans
      (mul_pow_mul_add_le_pow_succ_mul j hδ hσ0 (le_max_left _ _) hM hA ?_)
    -- `(ρ / R)^γ ≤ (4ʲ)^(-γ) = τʲ ≤ σʲ`.
    have h4j : ((4 : ℝ) ^ j) ^ γ = ((4 : ℝ) ^ γ) ^ j := by
      rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num), mul_comm]
    have hργ : (ρ / R) ^ γ ≤ τ ^ j := by
      calc (ρ / R) ^ γ ≤ ((4 : ℝ) ^ j)⁻¹ ^ γ := by
            refine Real.rpow_le_rpow (by positivity) ?_ hγ.le
            rw [div_le_iff₀ hR, ← div_eq_inv_mul]
            linarith
        _ = τ ^ j := by rw [Real.inv_rpow (by positivity), h4j, hτ_def, inv_pow]
    exact mul_le_mul_of_nonneg_left (hργ.trans (pow_le_pow_left₀ hτ0 (le_max_right _ _) j)) hA

/-- **Geometric decay of the supremum at the boundary with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0`, and let `r > 1` with `r > n/2`. There are
`σ ∈ (0, 1)` and `K > 0`, depending only on `λ`, `Λ`, `θ`, the dimension, `r` and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ L²(Ω)`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)`. If
`f ∈ Lʳ(Ω ∩ B(x₀, R))`, `u ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the complement of `Ω`
fills the proportion `θ` of every ball `B(x₀, ρ)`, `0 < ρ ≤ R`, then for every `j`

`u ≤ σʲ (M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)` almost everywhere on
`Ω ∩ B(x₀, R / 4ʲ)`.

Since `σʲ` is a power `(4⁻ʲ)^β` with `β > 0`, this is a Hölder modulus at the boundary point
`x₀`. -/
theorem exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ σ K : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
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
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ ρ, 0 < ρ → ρ ≤ R →
        θ * mu.real (ball x₀ ρ) ≤ mu.real (ball x₀ ρ \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        W1p.value u x ≤ σ ^ j * (M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
            lam) := by
  obtain ⟨δ, K₁, hδ0, hδ1, hK₁, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hθ hr hrn
  set γ : ℝ := 2 - (Fintype.card ι : ℝ) / r with hγ_def
  have hγ : 0 < γ := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
    rw [hγ_def, sub_pos, div_lt_iff₀ hr0]
    linarith
  have h4 : 1 < (4 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  refine ⟨max (1 - δ / 2) ((4 : ℝ) ^ γ)⁻¹, 2 * K₁ / δ,
    lt_max_of_lt_right (inv_pos.2 (by linarith)),
    max_lt (by linarith) (inv_lt_one_of_one_lt₀ h4), by positivity, ?_⟩
  intro Omega a f u x₀ R M h ha hf2 hfr hboundary hu hle hext j
  rcases le_or_gt R 0 with hR | hR
  · -- For `R ≤ 0` the balls are empty.
    simp [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg hR (by positivity) : R / 4 ^ j ≤ 0)]
  have hlam := h.pos
  set F := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal
  set A := K₁ * R ^ γ * F / lam with hA_def
  have hgoal : M + 2 * K₁ / δ * R ^ γ * F / lam = M + 2 / δ * A := by
    rw [hA_def]
    ring
  rw [hgoal]
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    have hRj : R / 4 ^ j ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hσ0 : 0 ≤ max (1 - δ / 2) ((4 : ℝ) ^ γ)⁻¹ := (le_max_right _ _).trans' (by positivity)
    have hσj1 : max (1 - δ / 2) ((4 : ℝ) ^ γ)⁻¹ ^ j ≤ 1 :=
      pow_le_one₀ hσ0 (max_le (by linarith) (inv_lt_one_of_one_lt₀ h4).le)
    have hpos : 0 ≤ max (1 - δ / 2) ((4 : ℝ) ^ γ)⁻¹ ^ j * (2 / δ * A) := by positivity
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball hRj)) hle] with x hx
    nlinarith
  -- Each reduction step from `B(x₀, 2ρ)` to `B(x₀, ρ/2)` has error at most `A (ρ/R)^γ`.
  refine ae_le_pow_mul_add_of_forall_ae_le_mul_add hR hδ0 hγ hM (by positivity) hle
    (fun ρ M' hρ hρR hle' => ?_) j
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * ρ) ⊆
      (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
    inter_subset_inter_right _ (ball_subset_ball hρR)
  refine (hred h ha hf2 (hfr.mono_measure (Measure.restrict_mono hsub le_rfl)) hboundary hu
    hle' (hext ρ hρ (by linarith))).mono fun x hx => hx.trans ?_
  have hFρ : (eLpNorm f r
      (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * ρ)))).toReal ≤ F :=
    ENNReal.toReal_mono hfr.eLpNorm_lt_top.ne
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
  have hAρ : A * (ρ / R) ^ γ = K₁ * ρ ^ γ * F / lam := by
    rw [hA_def, Real.div_rpow hρ.le hR.le]
    field_simp
  rw [hAρ]
  gcongr

/-- **Geometric decay of the supremum at the boundary (De Giorgi).** Let `n ≥ 1` be the dimension
and fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the
dimension and the normalization of the additive Haar measure `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be
a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u⁺ ∈ H¹₀(Ω)`. If `u ≤ M` almost everywhere on
`Ω ∩ B(x₀, R)` and the complement of `Ω` fills the proportion `θ` of every ball `B(x₀, r)`,
`0 < r ≤ R`, then for every `j`

`u ≤ (1 - δ)ʲ M` almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`.

This is the case `f = 0` of
`TauCeti.PDE.exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`. -/
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
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        W1p.value u x ≤ (1 - δ) ^ j * M := by
  obtain ⟨r, hr, hrn⟩ := exists_one_lt_card_lt_two_mul (ι := ι)
  obtain ⟨σ, _K, hσ0, hσ1, -, hdecay⟩ :=
    exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
      (mu := mu) (lam := lam) (Lam := Lam) hθ hr hrn
  exact ⟨1 - σ, by linarith, by linarith, fun h ha hboundary hu hle hext j => by
    simpa using hdecay h ha (f := 0) MemLp.zero MemLp.zero hboundary
      (fun v hv => by simpa using hu v hv) hle hext j⟩

/-- **Geometric decay of weak solutions at the boundary with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, fix a proportion `θ > 0`, and let `r > 1` with `r > n/2`. There are
`σ ∈ (0, 1)` and `K > 0`, depending only on `λ`, `Λ`, `θ`, the dimension, `r` and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ L²(Ω)`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`. If `f ∈ Lʳ(Ω ∩ B(x₀, R))`, `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the
complement of `Ω` fills the proportion `θ` of every ball `B(x₀, ρ)`, `0 < ρ ≤ R`, then for every
`j`

`|u| ≤ σʲ (M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)` almost everywhere on
`Ω ∩ B(x₀, R / 4ʲ)`. -/
theorem exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ σ K : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f 2 (mu.restrict Omega) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), |W1p.value u x| ≤ M) →
      (∀ ρ, 0 < ρ → ρ ≤ R →
        θ * mu.real (ball x₀ ρ) ≤ mu.real (ball x₀ ρ \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        |W1p.value u x| ≤ σ ^ j * (M + K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R))).toReal /
            lam) := by
  obtain ⟨σ, K, hσ0, hσ1, hK, hdecay⟩ :=
    exists_ae_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
      (mu := mu) (lam := lam) (Lam := Lam) hθ hr hrn
  refine ⟨σ, K, hσ0, hσ1, hK, ?_⟩
  intro Omega a f u x₀ R M h ha hf2 hfr hu0 hu hle hext j
  have hneg : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
      W1p.value (-u) x = -W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left (W1p.value_neg_ae u)
  -- Both `u` and `-u` are subsolutions vanishing on the boundary, with data `f` and `-f`.
  have hpos := hdecay h ha hf2 hfr (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) (by filter_upwards [hle] with x hx using (abs_le.1 hx).2) hext j
  have hneg' := hdecay (f := -f) h ha hf2.neg hfr.neg
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by
      rw [energyFormH1_neg_left, hu v]
      simp only [Pi.neg_apply, neg_mul, integral_neg, le_refl])
    (by
      filter_upwards [hle, ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (W1p.value_neg_ae u)] with x hx hx'
      rw [hx', Pi.neg_apply]
      exact neg_le.1 (abs_le.1 hx).1) hext j
  rw [eLpNorm_neg] at hneg'
  filter_upwards [hpos, hneg', hneg] with x h1 h2 h3
  rw [h3] at h2
  exact abs_le.2 ⟨neg_le.1 h2, h1⟩

/-- **Geometric decay of weak solutions at the boundary (De Giorgi).** Let `n ≥ 1` be the
dimension and fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`,
the dimension and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`. If `|u| ≤ M` almost everywhere on
`Ω ∩ B(x₀, R)` and the complement of `Ω` fills the proportion `θ` of every ball `B(x₀, r)`,
`0 < r ≤ R`, then for every `j`

`|u| ≤ (1 - δ)ʲ M` almost everywhere on `Ω ∩ B(x₀, R / 4ʲ)`.

This is the case `f = 0` of
`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`. -/
theorem exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), |W1p.value u x| ≤ M) →
      (∀ r, 0 < r → r ≤ R →
        θ * mu.real (ball x₀ r) ≤ mu.real (ball x₀ r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ j : ℕ, ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
        |W1p.value u x| ≤ (1 - δ) ^ j * M := by
  obtain ⟨r, hr, hrn⟩ := exists_one_lt_card_lt_two_mul (ι := ι)
  obtain ⟨σ, _K, hσ0, hσ1, -, hdecay⟩ :=
    exists_ae_abs_value_le_pow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
      (mu := mu) (lam := lam) (Lam := Lam) hθ hr hrn
  exact ⟨1 - σ, by linarith, by linarith, fun h ha hu0 hu hle hext j => by
    simpa using hdecay h ha (f := 0) MemLp.zero MemLp.zero hu0 (fun v => by simpa using hu v)
      hle hext j⟩

end PDE

end TauCeti
