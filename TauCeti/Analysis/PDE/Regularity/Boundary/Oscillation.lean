/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.PDE.Regularity.Oscillation
public import TauCeti.Analysis.Sobolev.W1p.Truncation

/-!
# De Giorgi's oscillation decay at the boundary

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, and let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u ≤ 0` on `∂Ω`, in the sense that
`u⁺ ∈ H¹₀(Ω)`. Nothing is assumed about the regularity of `∂Ω`. This file proves De Giorgi's
estimate at boundary points: if the complement of `Ω` fills a fixed proportion `θ > 0` of the
ball `B(x₀, R)`, then the supremum of `u⁺` drops by a fixed factor from `Ω ∩ B(x₀, 2R)` to
`Ω ∩ B(x₀, R/2)`, and if the complement fills that proportion of every ball `B(x₀, r)`, `r ≤ R`,
the supremum decays geometrically along the balls `B(x₀, R / 4ʲ)`.

The proof reduces the boundary estimate to the interior one.

* **Testing against functions without boundary values.** For a subsolution with `u⁺ ∈ H¹₀(Ω)`,
  the inequality `a(u⁺, v) ≤ 0` holds for every nonnegative `v ∈ H¹(Ω)`, not only for
  `v ∈ H¹₀(Ω)` (`TauCeti.PDE.energyFormH1_posPart_left_nonpos`). The test function is
  `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺`, which lies in `H¹₀(Ω)` because `u⁺` does
  (`TauCeti.W1p.posPart_sub_mem_w1p0Submodule`). On `{u⁺ ≤ ε v}` its gradient is `∇u⁺` and
  contributes the nonnegative energy `⟨a ∇u⁺, ∇u⁺⟩`; on `{u⁺ > ε v}` it is `ε ∇v`. Dividing by
  `ε` and letting `ε → 0`, dominated convergence turns the indicator of `{u⁺ > ε v}` into that of
  `{u > 0}`, which is `a(u⁺, v)`.
* **The zero extension is a subsolution.** Hence the zero extension of `u⁺` to a larger open set
  `Ω'` satisfies `a'(ū, v) ≤ 0` for every nonnegative `v ∈ H¹(Ω')`, for every coefficient field
  `a'` agreeing with `a` on `Ω` (`TauCeti.PDE.energyFormH1_extendByZeroL_posPart_nonpos`).
* **Reduction of the supremum.** Extending `a` by `λ I` off `Ω`, the zero extension is a weak
  subsolution on the whole space, and it vanishes on `B(x₀, R) \ Ω`. De Giorgi's interior
  reduction of the supremum (`TauCeti.PDE.exists_ae_value_le_sub_mul_sub`) at the level `0`
  therefore applies with the proportion `θ`
  (`TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`).

The exterior density hypothesis `θ |B(x₀, r)| ≤ |B(x₀, r) \ Ω|` for all small `r` is an
exterior measure density condition at `x₀`. An exterior cone with vertex `x₀` gives it, with `θ`
depending only on the aperture of the cone, for every `r` up to the height of the cone. For a
weak solution `u ∈ H¹₀(Ω)` both `u` and `-u` are such subsolutions, so `|u|` decays
geometrically towards boundary points
(`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`). This
is the boundary step of the global Hölder estimate for the Dirichlet problem.

## Main declarations

* `TauCeti.PDE.energyFormH1_posPart_left_nonpos`: `a(u⁺, v) ≤ 0` for every nonnegative
  `v ∈ H¹(Ω)`.
* `TauCeti.PDE.energyFormH1_extendByZeroL_posPart_nonpos`: the zero extension of `u⁺` is a weak
  subsolution on every larger open set.
* `TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`: the
  reduction of the supremum at the boundary.
* `TauCeti.PDE.exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`: its
  iteration, geometric decay of the supremum.
* `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`:
  geometric decay of `|u|` for weak solutions in `H¹₀(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.25, 8.27 and 8.29.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped Topology

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
a subsolution `u` with `u⁺ ∈ H¹₀(Ω)` against a nonnegative `v ∈ H¹(Ω)`, cut off to `{u⁺ > ε v}`,
has nonpositive integral. It is `ε⁻¹` times a lower bound for the energy of `u` against the test
function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺ ∈ H¹₀(Ω)`. -/
private theorem setIntegral_indicator_matrixBilinearForm_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x) {ε : ℝ}
    (hε : 0 < ε) (hFm : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0}) :
    ∫ x in Omega, {x | ε * W1p.value v x < max (W1p.value u x) 0}.indicator
      (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu ≤ 0 := by
  set up := W1p.posPart (p := 2) (mu := mu) (Omega := Omega) (by norm_num) u
  have hεv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (ε • v) x := by
    filter_upwards [W1p.value_smul_ae ε v, hv] with x hx hvx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hε.le hvx
  -- The test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` lies in `H¹₀(Ω)` and is nonnegative.
  have hmem : up - W1p.posPart (by norm_num) (up - ε • v) ∈ w1p0Submodule mu Omega 2 :=
    (w1p0Submodule mu Omega 2).toSubmodule.sub_mem hboundary
      (W1p.posPart_sub_mem_w1p0Submodule (by norm_num) hboundary hεv)
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega,
      0 ≤ W1p.value (up - W1p.posPart (by norm_num) (up - ε • v)) x := by
    filter_upwards [W1p.value_sub_ae up (W1p.posPart (by norm_num) (up - ε • v)),
      Lp.coeFn_posPart (W1p.value (up - ε • v)), W1p.value_sub_ae up (ε • v),
      Lp.coeFn_posPart (W1p.value u), hεv] with x h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, W1p.value_posPart (u := up - ε • v), h2, h3, Pi.sub_apply,
      W1p.value_posPart, h4]
    rcases le_total (max (W1p.value u x) 0 - W1p.value (ε • v) x) 0 with hle | hle
    · rw [max_eq_right hle, sub_zero]
      exact le_max_right _ _
    · rw [max_eq_left hle]
      linarith
  have htest := hu ⟨_, hmem⟩ hnonneg
  rw [energyFormH1_zero_zero_eq_setIntegral] at htest
  have hle := (integral_mono_ae
    (((integrable_matrixBilinearForm_gradient h ha u v).indicator hFm).const_mul ε)
    (integrable_matrixBilinearForm_gradient h ha u _)
    (mul_indicator_le_matrixBilinearForm_gradient h u v)).trans htest
  rw [integral_const_mul] at hle
  exact nonpos_of_mul_nonpos_right hle hε

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
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
  have hg : Integrable g (mu.restrict Omega) := integrable_matrixBilinearForm_gradient h ha u v
  have hFm (ε : ℝ) : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0} :=
    measurableSet_lt ((Lp.stronglyMeasurable (W1p.value v)).measurable.const_mul ε)
      ((Lp.stronglyMeasurable (W1p.value u)).measurable.max measurable_const)
  -- Dominated convergence along `ε = 1 / (n + 1)`: the cut-offs `1_{u⁺ > ε v}` converge to
  -- `1_{u > 0}`, and each cut-off integral is nonpositive.
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
  have hint : ∫ x in Omega, {x | 0 < W1p.value u x}.indicator g x ∂mu ≤ 0 :=
    le_of_tendsto' hlim fun n => setIntegral_indicator_matrixBilinearForm_nonpos h ha hboundary
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
  rw [energyFormH1_extendByZeroL_left]
  have hres : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL hsub v) x := by
    filter_upwards [W1p.value_restrictL_ae hsub v,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hsub) hv] with x h1 h2
    rw [h1]
    exact h2
  refine le_of_eq_of_le ?_ (energyFormH1_posPart_left_nonpos h ha hboundary hu hres)
  rw [energyFormH1_def, energyFormH1_def]
  exact setIntegral_congr_fun Omega.isOpen.measurableSet fun x hx => by rw [haa' hx]

/-- The whole-space problem behind the boundary estimate: extending `a` by `λ I` off `Ω` gives a
uniformly elliptic field on the whole space, for which the zero extension `ū` of `u⁺` is a weak
subsolution; `ū` equals `u⁺` on `Ω` and vanishes off `Ω`. -/
private theorem exists_uniformlyEllipticOn_top_extendByZeroL_posPart
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) a'
        lam Lam ∧
      AEStronglyMeasurable a' (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))) ∧
      ∃ ub : W1p mu ⊤ 2, (∀ v : W1p0 mu ⊤ 2,
        (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          0 ≤ W1p.value (v : W1p mu ⊤ 2) x) →
        energyFormH1 a' 0 0 ub (v : W1p mu ⊤ 2) ≤ 0) ∧
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
      energyFormH1 a' 0 0 ub (v : W1p mu ⊤ 2) ≤ 0 := fun v hv =>
    energyFormH1_extendByZeroL_posPart_nonpos le_top (piecewise_eqOn _ _ _) h ha hboundary hu hv
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
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hθ
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro Omega a u x₀ R M h ha hboundary hu hR hle hθR
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ hR2) hle]
      with x hx
    nlinarith
  -- Extend `a` by `λ I` off `Ω` and `u⁺` by zero: a weak subsolution on the whole space.
  obtain ⟨a', h', ha', ub, hsubsol, hval⟩ :=
    exists_uniformlyEllipticOn_top_extendByZeroL_posPart h ha hboundary hu
  have hM' : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value ub x ≤ M := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hval, (ae_restrict_iff' (hOm.inter measurableSet_ball)).1 hle]
      with x hx hx' hxb
    rw [hx]
    by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxO]
      exact max_le (hx' ⟨hxO, hxb⟩) hM
    · rw [indicator_of_notMem hxO]
      exact hM
  -- The extension vanishes on `B(x₀, R) \ Ω`, which fills the proportion `θ` of the ball.
  have hθ' : θ * mu.real (ball x₀ R) ≤
      (mu.restrict (ball x₀ R)).real {x | W1p.value ub x ≤ 0} := by
    refine hθR.trans ?_
    rw [sdiff_eq, inter_comm, ← measureReal_restrict_apply hOm.compl]
    refine ENNReal.toReal_mono ((measure_mono (subset_univ _)).trans_lt ?_).ne
      (measure_mono_ae ?_)
    · rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top
    · filter_upwards [ae_restrict_of_ae hval] with x hx hxc
      rw [hx, indicator_of_notMem hxc]
  have hred' := hred h' ha' hsubsol hR (by simp) hM hM' hθ'
  rw [ae_restrict_iff' (hOm.inter measurableSet_ball)]
  filter_upwards [hval, (ae_restrict_iff' measurableSet_ball).1 hred'] with x hx hx' hxO
  have hle' := hx' hxO.2
  rw [hx, indicator_of_mem hxO.1] at hle'
  nlinarith [le_max_left (W1p.value u x) 0]

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

end PDE

end TauCeti
