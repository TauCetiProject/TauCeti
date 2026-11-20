/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.PDE.Regularity.Oscillation
public import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# De Giorgi's oscillation decay at the boundary

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, and let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u ≤ 0` on `∂Ω`, in the sense that `u⁺ ∈ H¹₀(Ω)`,
and with `f ∈ Lʳ`, `r > 1`, `r > n/2`. Nothing is assumed about the regularity of `∂Ω`. This file
proves De Giorgi's estimate at boundary points: if the complement of `Ω` fills a fixed proportion
`θ > 0` of the ball `B(x₀, R)`, then the supremum of `u⁺` drops by a fixed factor from
`Ω ∩ B(x₀, 2R)` to `Ω ∩ B(x₀, R/2)`, up to the datum term `R^(2 - n/r) ‖f‖_{Lʳ} / λ`. If the
complement fills that proportion of every ball `B(x₀, s)`, `s ≤ R`, the supremum on
`Ω ∩ B(x₀, ρ)` decays like a power `(ρ / R)^α`, and for `f = 0` geometrically along the balls
`B(x₀, R / 4ʲ)`.

The proof reduces the boundary estimate to the interior one.

* **Testing against functions without boundary values.** For a subsolution with `u⁺ ∈ H¹₀(Ω)`,
  the inequality `a(u⁺, v) ≤ ∫_Ω f⁺ v` holds for every nonnegative `v ∈ H¹(Ω)` with `f⁺ v`
  integrable, not only for `v ∈ H¹₀(Ω)` (`TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`).
  The test function is `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺`, which lies in `H¹₀(Ω)` because `u⁺`
  does (`TauCeti.W1p.posPart_sub_mem_w1p0Submodule`), and `f min(u⁺, ε v) ≤ ε f⁺ v`. On
  `{u⁺ ≤ ε v}` its gradient is `∇u⁺` and contributes the nonnegative energy `⟨a ∇u⁺, ∇u⁺⟩`; on
  `{u⁺ > ε v}` it is `ε ∇v`. Dividing by `ε` and letting `ε → 0`, dominated convergence turns
  the indicator of `{u⁺ > ε v}` into that of `{u > 0}`, which is `a(u⁺, v)`.
* **The zero extension is a subsolution.** Hence the zero extension `ū` of `u⁺` to a larger open
  set `Ω'` satisfies `a'(ū, v) ≤ ∫_{Ω'} f₀ v` for every nonnegative `v ∈ H¹(Ω')`, for every
  coefficient field `a'` agreeing with `a` on `Ω`, where `f₀` is the zero extension of `f⁺`
  (`TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`).
* **Splitting off the datum.** Extending `a` by `λ I` off `Ω`, `ū` is a weak subsolution on the
  whole space. On `U = B(x₀, 2R)` let `w ∈ H¹₀(U)` solve `-∂ᵢ(aⁱʲ ∂ⱼw) = f₀`; Stampacchia's
  estimate on a ball (`TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_ae_abs_le`) gives
  `|w| ≤ E = C R^(2 - n/r) ‖f‖_{Lʳ} / λ`, and `ū - w` is a weak subsolution of the homogeneous
  equation on `U`. The test functions `v ∈ H¹₀(U)` make `f₀ v` integrable
  (`TauCeti.W1p0.integrable_mul_value_of_memLp`).
* **Reduction of the supremum.** `ū - w ≤ M + E` on `U`, and `ū - w ≤ E` on `B(x₀, R) \ Ω`,
  where `ū` vanishes. De Giorgi's interior reduction of the supremum
  (`TauCeti.PDE.exists_ae_value_le_sub_mul_sub`) at the level `E` therefore applies with the
  proportion `θ`, and gives `u ≤ (1 - δ) M + 2 E` on `Ω ∩ B(x₀, R/2)`
  (`TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).
* **Iteration.** Along the radii `R / 4ʲ`, the datum term shrinks by the factor `4^(-(2 - n/r))`
  at each step, so the bound decays like `qʲ` for a `q < 1` depending only on `δ` and `2 - n/r`,
  which is a power `(ρ / R)^α`
  (`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`).

The exterior density hypothesis `θ |B(x₀, r)| ≤ |B(x₀, r) \ Ω|` for all small `r` is an
exterior measure density condition at `x₀`. An exterior cone with vertex `x₀` gives it, with `θ`
depending only on the aperture of the cone, for every `r` up to the height of the cone. For a
weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, both `u` and `-u` are such subsolutions, so
`|u|` decays like `(ρ / R)^α` towards boundary points
(`TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`;
for `f = 0` geometrically,
`TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`). This
is the boundary step of the global Hölder estimate for the Dirichlet problem.

## Main declarations

* `TauCeti.PDE.energyFormH1_posPart_left_nonpos_of_forall_pos`: `a(u⁺, v) ≤ 0` as soon as the
  energy of `u` against every truncation `min(u⁺, ε v)`, `ε > 0`, is nonpositive.
* `TauCeti.PDE.energyFormH1_posPart_left_le_setIntegral`: `a(u⁺, v) ≤ ∫_Ω f⁺ v` for every
  nonnegative `v ∈ H¹(Ω)` with `f⁺ v` integrable.
* `TauCeti.PDE.energyFormH1_extendByZeroL_posPart_le_setIntegral`: the zero extension of `u⁺` is
  a weak subsolution on every larger open set.
* `TauCeti.PDE.mul_measureReal_ball_le_measureReal_setOf_le_zero`: the exterior density at `x₀`
  passes to the sublevel set `{g ≤ 0}` of a function that is nonpositive off `Ω`.
* `TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`: the
  reduction of the supremum at the boundary with a right-hand side; the case `f = 0` is
  `TauCeti.PDE.exists_ae_value_le_mul_of_mul_measureReal_le_measureReal_ball_diff`.
* `TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`:
  its iteration, power decay of the supremum with a right-hand side.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`:
  power decay of `|u|` for weak solutions in `H¹₀(Ω)` with a right-hand side.
* `TauCeti.PDE.exists_ae_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff` and
  `TauCeti.PDE.exists_ae_abs_value_le_pow_mul_of_mul_measureReal_le_measureReal_ball_diff`:
  geometric decay for `f = 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.25, 8.27 and 8.29.
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

/-- The cut-off step of the test-function argument: for `ε > 0`, the density `⟨a ∇u, ∇v⟩` of a
subsolution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)` against a nonnegative `v ∈ H¹(Ω)`, cut
off to `{u⁺ > ε v}`, has integral at most `∫_Ω f⁺ v`. It is `ε⁻¹` times a lower bound for the
energy of `u` against the test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺ ∈ H¹₀(Ω)`, and
`f min(u⁺, ε v) ≤ ε f⁺ v`. -/
private theorem setIntegral_indicator_matrixBilinearForm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x)
    (hfv : Integrable (fun x => max (f x) 0 * W1p.value v x) (mu.restrict Omega)) {ε : ℝ}
    (hε : 0 < ε) (hFm : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0}) :
    ∫ x in Omega, {x | ε * W1p.value v x < max (W1p.value u x) 0}.indicator
      (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu ≤
      ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
  set up := W1p.posPart (p := 2) (mu := mu) (Omega := Omega) (by norm_num) u
  set m := up - W1p.posPart (by norm_num) (up - ε • v)
  have hεv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (ε • v) x := by
    filter_upwards [W1p.value_smul_ae ε v, hv] with x hx hvx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hε.le hvx
  -- The test function `m = min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` lies in `H¹₀(Ω)`.
  have hmem : m ∈ w1p0Submodule mu Omega 2 :=
    (w1p0Submodule mu Omega 2).toSubmodule.sub_mem hboundary
      (W1p.posPart_sub_mem_w1p0Submodule (by norm_num) hboundary hεv)
  have hval : ∀ᵐ x ∂mu.restrict Omega,
      W1p.value m x = min (max (W1p.value u x) 0) (ε * W1p.value v x) := by
    filter_upwards [W1p.value_sub_ae up (W1p.posPart (by norm_num) (up - ε • v)),
      Lp.coeFn_posPart (W1p.value (up - ε • v)), W1p.value_sub_ae up (ε • v),
      Lp.coeFn_posPart (W1p.value u), W1p.value_smul_ae ε v] with x h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, W1p.value_posPart (u := up - ε • v), h2, h3, Pi.sub_apply,
      W1p.value_posPart, h4, h5, Pi.smul_apply, smul_eq_mul]
    rcases le_total (max (W1p.value u x) 0) (ε * W1p.value v x) with hle | hle
    · rw [max_eq_right (sub_nonpos.2 hle), sub_zero, min_eq_left hle]
    · rw [max_eq_left (sub_nonneg.2 hle), min_eq_right hle]
      ring
  have hm0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value m x := by
    filter_upwards [hval, hv] with x hx hvx
    rw [hx]
    exact le_min (le_max_right _ _) (mul_nonneg hε.le hvx)
  -- `f m ≤ f⁺ m ≤ ε f⁺ v`, so `∫_Ω f m ≤ ε ∫_Ω f⁺ v`, also when `f m` is not integrable.
  have hfm : ∫ x in Omega, f x * W1p.value m x ∂mu ≤
      ε * ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
    rw [← integral_const_mul]
    refine MeasureTheory.integral_mono_of_integral_nonneg ?_ (hfv.const_mul ε)
      (integral_nonneg_of_ae ?_)
    · filter_upwards [hval, hm0] with x hx hx0
      calc f x * W1p.value m x ≤ max (f x) 0 * W1p.value m x :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hx0
        _ ≤ max (f x) 0 * (ε * W1p.value v x) :=
            mul_le_mul_of_nonneg_left (hx ▸ min_le_right _ _) (le_max_right _ _)
        _ = ε * (max (f x) 0 * W1p.value v x) := by ring
    · filter_upwards [hv] with x hvx
      exact mul_nonneg hε.le (mul_nonneg (le_max_right _ _) hvx)
  have htest := hu ⟨_, hmem⟩ hm0
  rw [energyFormH1_zero_zero_eq_setIntegral] at htest
  have hle := (integral_mono_ae
    (((h.integrable_matrixBilinearForm_gradient ha u v).indicator hFm).const_mul ε)
    (h.integrable_matrixBilinearForm_gradient ha u _)
    (mul_indicator_le_matrixBilinearForm_gradient h u v)).trans (htest.trans hfm)
  rw [integral_const_mul] at hle
  exact le_of_mul_le_mul_left hle hε

/-- The cut-off step of the test-function argument: for `ε > 0`, if the energy of `u` against
the test function `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` is nonpositive, then so is the integral of
the density `⟨a ∇u, ∇v⟩` cut off to `{u⁺ > ε v}`, which is `ε⁻¹` times a lower bound for that
energy. -/
private theorem setIntegral_indicator_matrixBilinearForm_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u v : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hFm : MeasurableSet {x | ε * W1p.value v x < max (W1p.value u x) 0})
    (htest : energyFormH1 a 0 0 u (W1p.posPart (by norm_num) u -
      W1p.posPart (by norm_num) (W1p.posPart (by norm_num) u - ε • v)) ≤ 0) :
    ∫ x in Omega, {x | ε * W1p.value v x < max (W1p.value u x) 0}.indicator
      (fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)) x ∂mu ≤ 0 := by
  rw [energyFormH1_zero_zero_eq_setIntegral] at htest
  have hle := (integral_mono_ae
    (((h.integrable_matrixBilinearForm_gradient ha u v).indicator hFm).const_mul ε)
    (h.integrable_matrixBilinearForm_gradient ha u _)
    (mul_indicator_le_matrixBilinearForm_gradient h u v)).trans htest
  rw [integral_const_mul] at hle
  exact nonpos_of_mul_nonpos_right hle hε

/-- **Testing against truncations suffices.** Let `a` be measurable and uniformly elliptic on
`Ω`, let `u, v ∈ H¹(Ω)` with `v ≥ 0`, and suppose that for every `ε > 0` the energy of `u` against
the truncation `min(u⁺, ε v) = u⁺ - (u⁺ - ε v)⁺` is nonpositive. Then `a(u⁺, v) ≤ 0`.

The truncations carry the boundary values of `u⁺` and of `v` at once: `min(u⁺, ε v)` lies in
`H¹₀` of a set as soon as one of `u⁺` and `ε v` does, which is how this lemma is used to test a
subsolution against functions that do not vanish on the boundary. -/
theorem energyFormH1_posPart_left_nonpos_of_forall_pos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u v : W1p mu Omega 2}
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x)
    (htest : ∀ ε : ℝ, 0 < ε → energyFormH1 a 0 0 u (W1p.posPart (by norm_num) u -
      W1p.posPart (by norm_num) (W1p.posPart (by norm_num) u - ε • v)) ≤ 0) :
    energyFormH1 a 0 0 (W1p.posPart (by norm_num) u) v ≤ 0 := by
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
  have hg : Integrable g (mu.restrict Omega) := h.integrable_matrixBilinearForm_gradient ha u v
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
    le_of_tendsto' hlim fun n => setIntegral_indicator_matrixBilinearForm_nonpos h ha
      (by positivity) (hFm _) (htest _ (by positivity))
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
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`, that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, with
`u ≤ 0` on `∂Ω` in the sense that `u⁺ ∈ H¹₀(Ω)`. Then `a(u⁺, v) ≤ ∫_Ω f⁺ v` for every nonnegative
`v ∈ H¹(Ω)` with `f⁺ v` integrable, with no boundary condition on `v`. -/
theorem energyFormH1_posPart_left_le_setIntegral
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega 2} (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x)
    (hfv : Integrable (fun x => max (f x) 0 * W1p.value v x) (mu.restrict Omega)) :
    energyFormH1 a 0 0 (W1p.posPart (by norm_num) u) v ≤
      ∫ x in Omega, max (f x) 0 * W1p.value v x ∂mu := by
  set g : EuclideanSpace ℝ ι → ℝ :=
    fun x => matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x)
  have hg : Integrable g (mu.restrict Omega) := h.integrable_matrixBilinearForm_gradient ha u v
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
    le_of_tendsto' hlim fun n => setIntegral_indicator_matrixBilinearForm_le h ha hboundary
      hu hv hfv (by positivity) (hFm _)
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
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with `u⁺ ∈ H¹₀(Ω)`. For every larger open set `Ω' ⊇ Ω` and every coefficient
field `a'` agreeing with `a` on `Ω`, the zero extension `ū ∈ H¹₀(Ω')` of `u⁺` satisfies
`a'(ū, v) ≤ ∫_{Ω'} f₀ v` for every nonnegative `v ∈ H¹(Ω')` with `f₀ v` integrable, where `f₀` is
the zero extension of `f⁺`. In particular, when `f₀ v` is integrable for every `v ∈ H¹₀(Ω')`
(for instance when `Ω'` has finite measure and `f ∈ Lʳ` with `r > max 1 (2n/(n+2))`,
`TauCeti.W1p0.integrable_mul_value_of_memLp`), `ū` is a weak subsolution of
`-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ f₀` on `Ω'`. -/
theorem energyFormH1_extendByZeroL_posPart_le_setIntegral {Omega' : Opens (EuclideanSpace ℝ ι)}
    (hsub : Omega ≤ Omega') {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (haa' : EqOn a' a (Omega : Set (EuclideanSpace ℝ ι)))
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {v : W1p mu Omega' 2} (hv : ∀ᵐ x ∂mu.restrict Omega', 0 ≤ W1p.value v x)
    (hfv : Integrable (fun x => (Omega : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => max (f y) 0) x * W1p.value v x) (mu.restrict Omega')) :
    energyFormH1 a' 0 0 (W1p0.extendByZeroL hsub ⟨_, hboundary⟩ : W1p mu Omega' 2) v ≤
      ∫ x in Omega', (Omega : Set (EuclideanSpace ℝ ι)).indicator
        (fun y => max (f y) 0) x * W1p.value v x ∂mu := by
  have hOm := Omega.isOpen.measurableSet
  have hOO' : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ Omega' := SetLike.coe_subset_coe.mpr hsub
  -- The right-hand side is `∫_Ω f⁺ v|_Ω`.
  have hind : (fun x => (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
      W1p.value v x) = (Omega : Set (EuclideanSpace ℝ ι)).indicator
        (fun x => max (f x) 0 * W1p.value v x) := by
    funext x
    exact (indicator_mul_left _ _ _).symm
  have hrestr : ∀ᵐ x ∂mu.restrict Omega,
      max (f x) 0 * W1p.value v x = max (f x) 0 * W1p.value (W1p.restrictL hsub v) x := by
    filter_upwards [W1p.value_restrictL_ae hsub v] with x hx
    rw [hx]
  have hint : Integrable (fun x => max (f x) 0 * W1p.value (W1p.restrictL hsub v) x)
      (mu.restrict Omega) := by
    rw [hind, integrable_indicator_iff hOm, IntegrableOn, Measure.restrict_restrict hOm,
      inter_eq_left.2 hOO'] at hfv
    exact hfv.congr hrestr
  have hres : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (W1p.restrictL hsub v) x := by
    filter_upwards [W1p.value_restrictL_ae hsub v,
      ae_restrict_of_ae_restrict_of_subset hOO' hv] with x h1 h2
    rw [h1]
    exact h2
  rw [energyFormH1_extendByZeroL_left, hind, integral_indicator hOm, Measure.restrict_restrict hOm,
    inter_eq_left.2 hOO', integral_congr_ae hrestr]
  refine le_of_eq_of_le ?_ (energyFormH1_posPart_left_le_setIntegral h ha hboundary hu hres hint)
  rw [energyFormH1_def, energyFormH1_def]
  exact setIntegral_congr_fun hOm fun x hx => by rw [haa' hx]

/-- The whole-space problem behind the boundary estimate: extending `a` by `λ I` off `Ω` gives a
uniformly elliptic field on the whole space, for which the zero extension `ū` of `u⁺` is a weak
subsolution of `-∂ᵢ(a'ⁱʲ ∂ⱼū) ≤ f₀`, with `f₀` the zero extension of `f⁺`; `ū` equals `u⁺` on `Ω`
and vanishes off `Ω`. -/
private theorem exists_uniformlyEllipticOn_top_extendByZeroL_posPart
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ,
      UniformlyEllipticOn (((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) a'
        lam Lam ∧
      AEStronglyMeasurable a' (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))) ∧
      ∃ ub : W1p mu ⊤ 2, (∀ v : W1p mu ⊤ 2,
        (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          0 ≤ W1p.value v x) →
        Integrable (fun x => (Omega : Set (EuclideanSpace ℝ ι)).indicator
          (fun y => max (f y) 0) x * W1p.value v x)
          (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) →
        energyFormH1 a' 0 0 ub v ≤ ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)),
          (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (f y) 0) x *
            W1p.value v x ∂mu) ∧
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
  -- The values of the extension: `u⁺` on `Ω` and `0` off `Ω`.
  have hval : ∀ᵐ x ∂mu, W1p.value ub x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x := by
    have hext := coeFn_extendByZeroLpₗᵢ ℝ hOm.nullMeasurableSet
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
  exact ⟨a', h', ha', ub, fun v hv hfv => energyFormH1_extendByZeroL_posPart_le_setIntegral le_top
    (piecewise_eqOn _ _ _) h ha hboundary hu hv hfv, hval⟩

/-- Splitting off the right-hand side of a whole-space subsolution on an open set `U` of finite
measure. If `ū ∈ H¹(ℝⁿ)` satisfies `a'(ū, v) ≤ ∫ g v` for every nonnegative `v ∈ H¹(ℝⁿ)` with
`g v` integrable, and `w ∈ H¹₀(U)` solves `-∂ᵢ(a'ⁱʲ ∂ⱼw) = g` in `U` with `g ∈ Lʳ(U)`, then
`ū|_U - w` is a weak subsolution of the homogeneous equation `-∂ᵢ(a'ⁱʲ ∂ⱼh) ≤ 0` in `U`. -/
private theorem energyFormH1_restrictL_sub_nonpos [Nonempty ι] {U : Opens (EuclideanSpace ℝ ι)}
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (h' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) a' lam Lam)
    (ha' : AEStronglyMeasurable a' (mu.restrict U)) {g : EuclideanSpace ℝ ι → ℝ}
    {ub : W1p mu ⊤ 2} (hsubsol : ∀ v : W1p mu ⊤ 2,
      (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        0 ≤ W1p.value v x) →
      Integrable (fun x => g x * W1p.value v x)
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) →
      energyFormH1 a' 0 0 ub v ≤ ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)), g x * W1p.value v x ∂mu)
    (hUm : MeasurableSet (U : Set (EuclideanSpace ℝ ι))) (hUfin : mu U ≠ ⊤) {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) * (2 - r) < 2 * r)
    (hg : MemLp g r (mu.restrict U)) {w : W1p0 mu U 2}
    (hw : ∀ v : W1p0 mu U 2, energyFormH1 a' 0 0 (w : W1p mu U 2) (v : W1p mu U 2) =
      ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu)
    (v : W1p0 mu U 2) (hv : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) :
    energyFormH1 a' 0 0 (W1p.restrictL le_top ub - (w : W1p mu U 2)) (v : W1p mu U 2) ≤ 0 := by
  have hU : U ≤ ⊤ := le_top
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h'.upper_nonneg ha' aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => h'.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  -- The zero extension `v₀` of `v` is a nonnegative test function on the whole space, and
  -- `g v₀` is integrable.
  have hext := coeFn_extendByZeroLpₗᵢ ℝ hUm.nullMeasurableSet (SetLike.coe_subset_coe.mpr hU)
    (W1p.value (v : W1p mu U 2))
  have hvt : ∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
      0 ≤ W1p.value (W1p0.extendByZeroL hU v : W1p mu ⊤ 2) x := by
    rw [W1p0.value_extendByZeroL]
    filter_upwards [hext, ae_restrict_of_ae ((ae_restrict_iff' hUm).1 hv)] with x hx hxv
    rw [hx]
    exact indicator_apply_nonneg hxv
  have hint : Integrable (fun x => g x * W1p.value (W1p0.extendByZeroL hU v : W1p mu ⊤ 2) x)
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
    have hind : Integrable ((U : Set (EuclideanSpace ℝ ι)).indicator
        fun x => g x * W1p.value (v : W1p mu U 2) x)
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
      (integrable_indicator_iff hUm).2 ((W1p0.integrable_mul_value_of_memLp hUfin hr hrn hg
        v).mono_measure (Measure.restrict_mono subset_rfl Measure.restrict_le_self))
    refine hind.congr ?_
    rw [W1p0.value_extendByZeroL]
    filter_upwards [hext] with x hx
    rw [hx]
    exact indicator_mul_right _ _ _
  have hle : energyFormH1 a' 0 0 (W1p.restrictL hU ub) (v : W1p mu U 2) ≤
      ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu := by
    rw [energyFormH1_restrictL a' 0 0 hU ub v]
    refine (hsubsol _ hvt hint).trans_eq ?_
    rw [W1p0.value_extendByZeroL]
    exact setIntegral_extendByZeroLpₗᵢ ℝ _ _ (fun x y => g x * y) (fun _ => mul_zero _) _
  rw [energyFormH1_sub_left hcoeff, hw v]
  linarith

/-- The last step of the reduction of the supremum at the boundary with a right-hand side. On
`U = B(x₀, 2R)`, let `h₀ = ū|_U - w`, where `ū` is the zero extension of `u⁺` and `|w| ≤ E`, be
a weak subsolution of the homogeneous equation. Since `ū ≤ M` on `B(x₀, 2R)` and `ū` vanishes off
`Ω`, De Giorgi's interior reduction of the supremum of `h₀` at the level `E` gives
`u ≤ (1 - δ) M + 2 E` on `Ω ∩ B(x₀, R/2)`. -/
private theorem ae_value_le_mul_add_of_ae_value_sub_le {θ δ : ℝ}
    (hred : ∀ {V : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {u : W1p mu V 2} {x₀ : EuclideanSpace ℝ ι} {R k M : ℝ},
      UniformlyEllipticOn (V : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict V) →
      (∀ v : W1p0 mu V 2,
        (∀ᵐ x ∂mu.restrict V, 0 ≤ W1p.value (v : W1p mu V 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu V 2) ≤ 0) →
      0 < R → ball x₀ (2 * R) ⊆ (V : Set (EuclideanSpace ℝ ι)) → k ≤ M →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), W1p.value u x ≤ M) →
      θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | W1p.value u x ≤ k} →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), W1p.value u x ≤ M - δ * (M - k))
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M E : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hle : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * R)),
      W1p.value u x ≤ M)
    (hθR : θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))))
    {U : Opens (EuclideanSpace ℝ ι)} (hUdef : (U : Set (EuclideanSpace ℝ ι)) = ball x₀ (2 * R))
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (h' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) a' lam Lam)
    (ha' : AEStronglyMeasurable a' (mu.restrict U)) {ub : W1p mu ⊤ 2}
    (hub : ∀ᵐ x ∂mu, W1p.value ub x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x)
    {w : W1p mu U 2}
    (hsub : ∀ v : W1p0 mu U 2,
      (∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) →
        energyFormH1 a' 0 0 (W1p.restrictL le_top ub - w) (v : W1p mu U 2) ≤ 0)
    (hw : ∀ᵐ x ∂mu.restrict U, |W1p.value w x| ≤ E) :
    ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 2)),
      W1p.value u x ≤ (1 - δ) * M + 2 * E := by
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have hUm : MeasurableSet (U : Set (EuclideanSpace ℝ ι)) := hUdef ▸ measurableSet_ball
  have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  have hval : ∀ᵐ x ∂mu.restrict U, W1p.value (W1p.restrictL le_top ub - w) x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => max (W1p.value u y) 0) x -
        W1p.value w x := by
    filter_upwards [W1p.value_sub_ae (W1p.restrictL le_top ub) w,
      W1p.value_restrictL_ae le_top ub, ae_restrict_of_ae hub] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hM' : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)),
      W1p.value (W1p.restrictL le_top ub - w) x ≤ M + E := by
    have hle' := (ae_restrict_iff' (hOm.inter measurableSet_ball)).1 hle
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [(ae_restrict_iff' hUm).1 hval, (ae_restrict_iff' hUm).1 hw, hle']
      with x h1 h2 h3 hxb
    have hxU : x ∈ (U : Set (EuclideanSpace ℝ ι)) := hUdef ▸ hxb
    rw [h1 hxU]
    have hw' := (abs_le.1 (h2 hxU)).1
    by_cases hxO : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxO]
      have := max_le (h3 ⟨hxO, hxb⟩) hM
      linarith
    · rw [indicator_of_notMem hxO]
      linarith
  have hθ' : θ * mu.real (ball x₀ R) ≤
      (mu.restrict (ball x₀ R)).real {x | W1p.value (W1p.restrictL le_top ub - w) x ≤ E} := by
    refine hθR.trans ?_
    rw [sdiff_eq, inter_comm, ← measureReal_restrict_apply hOm.compl]
    refine ENNReal.toReal_mono ((measure_mono (subset_univ _)).trans_lt ?_).ne
      (measure_mono_ae ?_)
    · rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top
    · have hRU : ball x₀ R ⊆ (U : Set (EuclideanSpace ℝ ι)) :=
        hUdef ▸ ball_subset_ball (by linarith)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hRU hval,
        ae_restrict_of_ae_restrict_of_subset hRU hw] with x h1 h2 hxc
      rw [h1, indicator_of_notMem hxc]
      linarith [(abs_le.1 h2).1]
  have hred' := hred h' ha' hsub hR hUdef.symm.subset (by linarith) hM' hθ'
  rw [ae_restrict_iff' (hOm.inter measurableSet_ball)]
  filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hred',
    (ae_restrict_iff' hUm).1 hval, (ae_restrict_iff' hUm).1 hw] with x h1 h2 h3 hxO
  have hxU : x ∈ (U : Set (EuclideanSpace ℝ ι)) := hUdef ▸ hR2 hxO.2
  have hle1 := h1 hxO.2
  rw [h2 hxU, indicator_of_mem hxO.1] at hle1
  have hw' := (abs_le.1 (h3 hxU)).2
  nlinarith [le_max_left (W1p.value u x) 0]

/-- Splitting off the datum on a ball. Let `n ≥ 1` be the dimension and let `r > 1` with
`r > n/2`. There is `C > 0`, depending only on `n`, `r` and the normalization of `mu`, such that
the following holds. Let `U = B(x₀, 2R)` and let `a'` be measurable and uniformly elliptic on
`U`. If `ū ∈ H¹(ℝⁿ)` satisfies `a'(ū, v) ≤ ∫ g v` for every nonnegative `v ∈ H¹(ℝⁿ)` with `g v`
integrable, and `g ∈ Lʳ(U)`, then there is `w ∈ H¹(U)` with `ū|_U - w` a weak subsolution of the
homogeneous equation on `U` and `|w| ≤ C R^(2 - n/r) ‖g‖_{Lʳ(U)} / λ`: the weak solution
`w ∈ H¹₀(U)` of `-∂ᵢ(a'ⁱʲ ∂ⱼw) = g`, bounded by Stampacchia's estimate. -/
private theorem exists_energyFormH1_restrictL_sub_nonpos_and_ae_abs_le [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Opens (EuclideanSpace ℝ ι)} {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {g : EuclideanSpace ℝ ι → ℝ} {ub : W1p mu ⊤ 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      (U : Set (EuclideanSpace ℝ ι)) = ball x₀ (2 * R) → 0 < R →
      UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) a' lam Lam →
      AEStronglyMeasurable a' (mu.restrict U) →
      (∀ v : W1p mu ⊤ 2,
        (∀ᵐ x ∂mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          0 ≤ W1p.value v x) →
        Integrable (fun x => g x * W1p.value v x)
          (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) →
        energyFormH1 a' 0 0 ub v ≤
          ∫ x in (⊤ : Opens (EuclideanSpace ℝ ι)), g x * W1p.value v x ∂mu) →
      MemLp g r (mu.restrict U) →
      ∃ w : W1p mu U 2,
        (∀ v : W1p0 mu U 2,
          (∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) →
            energyFormH1 a' 0 0 (W1p.restrictL le_top ub - w) (v : W1p mu U 2) ≤ 0) ∧
        ∀ᵐ x ∂mu.restrict U, |W1p.value w x| ≤ C * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm g r (mu.restrict U)).toReal / lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrn' : n * (2 - r) < 2 * r := by nlinarith [mul_pos hn (sub_pos.2 hr1)]
  obtain ⟨K, hK, hsolve⟩ := exists_forall_energyFormH1_eq_setIntegral_ae_abs_le (mu := mu) hr hrn
  refine ⟨K * 2 ^ (2 - n / r), by positivity, ?_⟩
  intro U a' g ub x₀ R hUdef hR h' ha' hsubsol hg
  obtain rfl : U = ⟨ball x₀ (2 * R), isOpen_ball⟩ := Opens.ext hUdef
  obtain ⟨w, hw, hwbound⟩ := hsolve h' ha' hg (by positivity)
  refine ⟨w, fun v hv => energyFormH1_restrictL_sub_nonpos h' ha' hsubsol measurableSet_ball
    measure_ball_lt_top.ne hr (by rwa [finrank_euclideanSpace]) hg hw v hv, ?_⟩
  -- `(2R)^(2 - n/r) = 2^(2 - n/r) R^(2 - n/r)`.
  filter_upwards [hwbound] with x hx
  refine hx.trans_eq ?_
  simp only [n, Opens.coe_mk]
  rw [Real.mul_rpow (by norm_num) hR.le]
  ring

omit [DecidableEq ι] in
/-- The exterior density at `x₀` passes to the sublevel set `{g ≤ 0}` of a function that is
nonpositive off `Ω`: if `g ≤ 0` almost everywhere on `B(x₀, R) \ Ω` and `Ωᶜ` fills the proportion
`θ` of `B(x₀, R)`, so does `{g ≤ 0}`. -/
theorem mul_measureReal_ball_le_measureReal_setOf_le_zero {θ R : ℝ}
    {x₀ : EuclideanSpace ℝ ι} {g : EuclideanSpace ℝ ι → ℝ}
    (hθR : θ * mu.real (ball x₀ R) ≤ mu.real (ball x₀ R \ (Omega : Set (EuclideanSpace ℝ ι))))
    (hg : ∀ᵐ x ∂mu, x ∈ ball x₀ R → x ∉ (Omega : Set (EuclideanSpace ℝ ι)) → g x ≤ 0) :
    θ * mu.real (ball x₀ R) ≤ (mu.restrict (ball x₀ R)).real {x | g x ≤ 0} := by
  refine hθR.trans ?_
  rw [sdiff_eq, inter_comm, ← measureReal_restrict_apply Omega.isOpen.measurableSet.compl]
  refine ENNReal.toReal_mono ((measure_mono (subset_univ _)).trans_lt ?_).ne
    (measure_mono_ae ?_)
  · rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  · filter_upwards [ae_restrict_of_ae hg, self_mem_ae_restrict measurableSet_ball]
      with x h1 hxB hxc
    exact h1 hxB hxc

/-- **Reduction of the supremum at the boundary, with a right-hand side (De Giorgi).** Let `n ≥ 1`
be the dimension, let `r > 1` with `r > n/2`, and fix a proportion `θ > 0`. There are
`δ ∈ (0, 1)` and `K > 0`, depending only on `λ`, `Λ`, `θ`, `r`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f`, that is `a(u, v) ≤ ∫_Ω f v` for every nonnegative
`v ∈ H¹₀(Ω)`, with `u ≤ 0` on `∂Ω` in the sense that `u⁺ ∈ H¹₀(Ω)`, and with
`f ∈ Lʳ(Ω ∩ B(x₀, 2R))`. If `u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of
`Ω` fills the proportion `θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then

`u ≤ (1 - δ) M + K R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, 2R))} / λ` almost everywhere on
`Ω ∩ B(x₀, R/2)`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. -/
theorem exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff [Nonempty ι]
    {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
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
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ (2 * R)))).toReal / lam := by
  obtain ⟨δ, hδ0, hδ1, hred⟩ :=
    exists_ae_value_le_sub_mul_sub (mu := mu) (lam := lam) (Lam := Lam) hθ
  obtain ⟨C, hC, hsplit⟩ := exists_energyFormH1_restrictL_sub_nonpos_and_ae_abs_le (mu := mu)
    (lam := lam) (Lam := Lam) hr hrn
  refine ⟨δ, 2 * C, hδ0, hδ1, by positivity, ?_⟩
  intro Omega a f u x₀ R M h ha hf hboundary hu hR hle hθR
  have hlam := h.pos
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  set F : ℝ := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
    ball x₀ (2 * R)))).toReal
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the claim is weaker than the hypothesis.
    have hR2 : ball x₀ (R / 2) ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right _ hR2) hle]
      with x hx
    have : 0 ≤ 2 * C * R ^ (2 - (Fintype.card ι : ℝ) / r) * F / lam := by positivity
    nlinarith
  -- Extend `a` by `λ I` off `Ω` and `u⁺` by zero: a weak subsolution on the whole space, with
  -- right-hand side the zero extension `g` of `f⁺`, which lies in `Lʳ(B(x₀, 2R))`.
  obtain ⟨a', h', ha', ub, hsubsol, hval⟩ :=
    exists_uniformlyEllipticOn_top_extendByZeroL_posPart h ha hboundary hu
  obtain ⟨U, hUdef⟩ : ∃ U : Opens (EuclideanSpace ℝ ι),
      (U : Set (EuclideanSpace ℝ ι)) = ball x₀ (2 * R) := ⟨⟨_, isOpen_ball⟩, rfl⟩
  have hUell : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) a' lam Lam :=
    h'.mono_set (by simp)
  have hUmeas : AEStronglyMeasurable a' (mu.restrict U) :=
    ha'.mono_measure (Measure.restrict_mono (by simp) le_rfl)
  have hg : MemLp ((Omega : Set (EuclideanSpace ℝ ι)).indicator fun y => max (f y) 0) r
      (mu.restrict U) := by
    rw [memLp_indicator_iff_restrict hOm.nullMeasurableSet, Measure.restrict_restrict hOm, hUdef]
    exact hf.pos_part
  have hgF : (eLpNorm ((Omega : Set (EuclideanSpace ℝ ι)).indicator fun y => max (f y) 0) r
      (mu.restrict U)).toReal ≤ F := by
    refine ENNReal.toReal_mono hf.eLpNorm_ne_top ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hOm.nullMeasurableSet,
      Measure.restrict_restrict hOm, hUdef]
    refine eLpNorm_mono hf.pos_part.aestronglyMeasurable fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  -- Split off the datum on `U = B(x₀, 2R)` and reduce the supremum of the homogeneous part.
  obtain ⟨w, hsub, hwb⟩ := hsplit hUdef hR hUell hUmeas hsubsol hg
  filter_upwards [ae_value_le_mul_add_of_ae_value_sub_le hred hR hM hle hθR hUdef hUell hUmeas
    hval hsub hwb] with x hx
  calc W1p.value u x ≤ (1 - δ) * M + 2 * (C * R ^ (2 - (Fintype.card ι : ℝ) / r) *
        (eLpNorm ((Omega : Set (EuclideanSpace ℝ ι)).indicator fun y => max (f y) 0) r
          (mu.restrict U)).toReal / lam) := hx
    _ ≤ (1 - δ) * M + 2 * (C * R ^ (2 - (Fintype.card ι : ℝ) / r) * F / lam) := by gcongr
    _ = (1 - δ) * M + 2 * C * R ^ (2 - (Fintype.card ι : ℝ) / r) * F / lam := by ring

/-- **Reduction of the supremum at the boundary (De Giorgi).** Let `n ≥ 1` be the dimension and
fix a proportion `θ > 0`. There is `δ ∈ (0, 1)`, depending only on `λ`, `Λ`, `θ`, the dimension
and the normalization of the additive Haar measure `mu`, such that the following holds. Let `a`
be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` with `u ≤ 0` on `∂Ω`, in the sense that `u⁺ ∈ H¹₀(Ω)`. If
`u ≤ M` almost everywhere on `Ω ∩ B(x₀, 2R)` and the complement of `Ω` fills the proportion
`θ` of `B(x₀, R)`, that is `θ |B(x₀, R)| ≤ |B(x₀, R) \ Ω|`, then

`u ≤ (1 - δ) M` almost everywhere on `Ω ∩ B(x₀, R/2)`.

The ball `B(x₀, 2R)` need not lie in `Ω`, and no regularity of `∂Ω` is assumed. This is the case
`f = 0` of `TauCeti.PDE.exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff`. -/
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
  -- Any exponent `r > max 1 (n/2)` will do, for instance `r = n + 1`.
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  obtain ⟨δ, K, hδ0, hδ1, -, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) (r := (Fintype.card ι : ℝ≥0) + 1)
      (by rw [← NNReal.coe_lt_coe]; push_cast; linarith) (by push_cast; linarith) hθ
  refine ⟨δ, hδ0, hδ1, fun h ha hboundary hu hR hle hθR => ?_⟩
  simpa using hred (f := 0) h ha (MemLp.zero' ..) hboundary (fun v hv => by simpa using hu v hv) hR
    hle hθR

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
  rw [W1p.ae_abs_value_le_iff inter_subset_left] at hle ⊢
  -- Both `u` and `-u` are subsolutions vanishing on the boundary.
  exact ⟨hdecay h ha (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) hR hle.1 hext j,
    hdecay h ha (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by rw [energyFormH1_neg_left, hu v, neg_zero]) hR hle.2 hext j⟩

/-- The discrete form of the decay at the boundary with a right-hand side: iterating the
reduction of the supremum `u ≤ (1 - δ) M + K t^γ ‖f‖ / λ` from `B(x₀, 2t)` to `B(x₀, t/2)` along
the radii `2t = R / 4ʲ` gives `u ≤ qʲ (M + D E)` on `Ω ∩ B(x₀, R / 4ʲ)`, where
`E = K R^γ ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ`, `q₁ ≥ max (1 - δ) 4^(-γ)`, `q = (1 + q₁)/2` and
`D = 2 / (1 - q₁)`. -/
private theorem ae_value_le_pow_mul_add_of_forall_ae_value_le {r : ℝ≥0} {θ δ K q₁ : ℝ}
    (hK : 0 < K) (hq₁δ : 1 - δ ≤ q₁) (hq₁ : q₁ < 1)
    (hsq₁ : ((4 : ℝ) ^ (2 - (Fintype.card ι : ℝ) / r))⁻¹ ≤ q₁)
    (hγ : 0 < 2 - (Fintype.card ι : ℝ) / r)
    (hred : ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
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
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ (2 * R)))).toReal / lam)
    {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hf : MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)))
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hle : ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M)
    (hext : ∀ s, 0 < s → s ≤ R →
      θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι))))
    (j : ℕ) :
    ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (R / 4 ^ j)),
      W1p.value u x ≤ ((1 + q₁) / 2) ^ j * (M + 2 / (1 - q₁) *
        (K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam)) := by
  set γ : ℝ := 2 - (Fintype.card ι : ℝ) / r
  set F : ℝ := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
    ball x₀ R))).toReal
  have hlam := h.pos
  have hE : 0 ≤ K * R ^ γ * F / lam := by positivity
  have hq₁0 : 0 < q₁ := (inv_pos.2 (by positivity)).trans_le hsq₁
  induction j with
  | zero =>
    simp only [pow_zero, div_one, one_mul]
    filter_upwards [hle] with x hx
    linarith [mul_nonneg (div_nonneg zero_le_two (sub_nonneg.2 hq₁.le)) hE]
  | succ j ih =>
    -- One reduction step from `B(x₀, 2t)` to `B(x₀, t / 2)`, with `2t = R / 4ʲ`.
    set t := R / 4 ^ j / 2 with ht_def
    have h2t : R / 4 ^ j = 2 * t := by rw [ht_def]; ring
    have ht2 : R / 4 ^ (j + 1) = t / 2 := by rw [ht_def, pow_succ]; ring
    have ht : 0 < t := by positivity
    have h2tR : 2 * t ≤ R := h2t ▸ div_le_self hR.le (one_le_pow₀ (by norm_num))
    rw [h2t] at ih
    have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ (2 * t) ⊆
        (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
      inter_subset_inter_right _ (ball_subset_ball h2tR)
    have hstep := hred h ha (hf.mono_measure (Measure.restrict_mono hsub le_rfl)) hboundary hu
      ht ih (hext t ht (by linarith))
    rw [ht2]
    filter_upwards [hstep] with x hx
    refine hx.trans (one_sub_mul_pow_mul_add_le_pow_succ_mul j hq₁δ hq₁0 hq₁ hM hE ?_)
    -- The datum term on `B(x₀, 2t)` is at most `q₁ʲ E`.
    have hFt : (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
        ball x₀ (2 * t)))).toReal ≤ F :=
      ENNReal.toReal_mono hf.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
    calc K * t ^ γ * (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
          ball x₀ (2 * t)))).toReal / lam
        ≤ K * (R ^ γ * q₁ ^ j) * F / lam := by
          gcongr
          calc t ^ γ ≤ (2 * t) ^ γ := Real.rpow_le_rpow ht.le (by linarith) hγ.le
            _ ≤ R ^ γ * q₁ ^ j := h2t ▸ div_pow_rpow_le_rpow_mul_pow hR.le (by norm_num) hsq₁ j
      _ = q₁ ^ j * (K * R ^ γ * F / lam) := by ring

/-- **Hölder decay at the boundary, with a right-hand side (De Giorgi).** Let `n ≥ 1` be the
dimension, let `r > 1` with `r > n/2`, and fix a proportion `θ > 0`. There are `α > 0` and `C`,
depending only on `λ`, `Λ`, `θ`, `r`, the dimension and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ f` with
`u⁺ ∈ H¹₀(Ω)` and `f ∈ Lʳ(Ω ∩ B(x₀, R))`. If `u ≤ M` almost everywhere on `Ω ∩ B(x₀, R)`, with
`M ≥ 0`, and the complement of `Ω` fills the proportion `θ` of every ball `B(x₀, s)`,
`0 < s ≤ R`, then for `0 < ρ ≤ R`

`u ≤ C (ρ / R)^α (M + R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)` almost everywhere on
`Ω ∩ B(x₀, ρ)`.

The datum enters with the Morrey gain `2 - n/r` of its exponent, and both sides scale in the
same way under dilations about `x₀`. -/
theorem exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
            ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < ρ → ρ ≤ R → 0 ≤ M →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R), W1p.value u x ≤ M) →
      (∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        W1p.value u x ≤ C * (ρ / R) ^ α * (M + R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  set γ : ℝ := 2 - (Fintype.card ι : ℝ) / r
  have hγ : 0 < γ := by
    have hr0 : (0 : ℝ) < r := by positivity
    simp only [γ]
    rw [sub_pos, div_lt_iff₀ hr0]
    linarith
  obtain ⟨δ, K, hδ0, hδ1, hK, hred⟩ :=
    exists_ae_value_le_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hr hrn hθ
  have hs : 1 < (4 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  set q₁ : ℝ := max (1 - δ) ((4 : ℝ) ^ γ)⁻¹
  have hq₁ : q₁ < 1 := max_lt (by linarith) (inv_lt_one_of_one_lt₀ hs)
  set q : ℝ := (1 + q₁) / 2
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by simp only [q]; linarith
  set D : ℝ := 2 / (1 - q₁)
  set α : ℝ := Real.logb 4 q⁻¹
  have hα : 0 < α := Real.logb_pos (by norm_num) ((one_lt_inv₀ hq0).2 hq1)
  refine ⟨α, q⁻¹ * max 1 (D * K), hα, by positivity, ?_⟩
  intro Omega a f u x₀ R M ρ h ha hf hboundary hu hρ hρR hM hle hext
  have hR : 0 < R := hρ.trans_le hρR
  have hlam := h.pos
  set F : ℝ := (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
    ball x₀ R))).toReal
  -- The radius `ρ` lies between `R / 4ʲ⁺¹` and `R / 4ʲ`.
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near ((one_le_div hρ).2 hρR) (by norm_num : (1 : ℝ) < 4)
  have hρj : ρ ≤ R / 4 ^ j := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    rwa [le_div_iff₀ hρ] at hj1
  have hdisc := ae_value_le_pow_mul_add_of_forall_ae_value_le hK (le_max_left _ _) hq₁
    (le_max_right _ _) hγ hred h ha hf hboundary hu hR hM hle hext j
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (inter_subset_inter_right _ (ball_subset_ball hρj)) hdisc] with x hx
  refine hx.trans ?_
  have hpow : q ^ (j + 1) ≤ (ρ / R) ^ α :=
    pow_le_div_rpow_logb (by norm_num) hq0 hq1.le hρ hR hj2.le
  have hB : 0 ≤ R ^ γ * F / lam := by positivity
  have hX : M + D * (K * R ^ γ * F / lam) ≤ max 1 (D * K) * (M + R ^ γ * F / lam) := by
    calc M + D * (K * R ^ γ * F / lam) = M + D * K * (R ^ γ * F / lam) := by ring
      _ ≤ max 1 (D * K) * M + max 1 (D * K) * (R ^ γ * F / lam) :=
        add_le_add (le_mul_of_one_le_left hM (le_max_left _ _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
      _ = max 1 (D * K) * (M + R ^ γ * F / lam) := by ring
  calc q ^ j * (M + D * (K * R ^ γ * F / lam))
      = q⁻¹ * q ^ (j + 1) * (M + D * (K * R ^ γ * F / lam)) := by
        rw [pow_succ]
        field_simp
    _ ≤ q⁻¹ * (ρ / R) ^ α * (max 1 (D * K) * (M + R ^ γ * F / lam)) := by gcongr
    _ = q⁻¹ * max 1 (D * K) * (ρ / R) ^ α * (M + R ^ γ * F / lam) := by ring

/-- **Hölder decay of weak solutions at the boundary, with a right-hand side (De Giorgi).** Let
`n ≥ 1` be the dimension, let `r > 1` with `r > n/2`, and fix a proportion `θ > 0`. There are
`α > 0` and `C`, depending only on `λ`, `Λ`, `θ`, `r`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with
`f ∈ Lʳ(Ω ∩ B(x₀, R))`. If `|u| ≤ M` almost everywhere on `Ω ∩ B(x₀, R)` and the complement of
`Ω` fills the proportion `θ` of every ball `B(x₀, s)`, `0 < s ≤ R`, then for `0 < ρ ≤ R`

`|u| ≤ C (ρ / R)^α (M + R^(2 - n/r) ‖f‖_{Lʳ(Ω ∩ B(x₀, R))} / λ)` almost everywhere on
`Ω ∩ B(x₀, ρ)`.

This is the boundary half of the global Hölder estimate for the Dirichlet problem with zero
boundary values (Gilbarg–Trudinger, Theorem 8.29). -/
theorem exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
    [Nonempty ι] {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R M ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R)) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < ρ → ρ ≤ R →
      (∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R),
        |W1p.value u x| ≤ M) →
      (∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball x₀ s) ≤ mu.real (ball x₀ s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ),
        |W1p.value u x| ≤ C * (ρ / R) ^ α * (M + R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
            ball x₀ R))).toReal / lam) := by
  obtain ⟨α, C, hα, hC, hdecay⟩ :=
    exists_ae_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff (mu := mu)
      (lam := lam) (Lam := Lam) hr hrn hθ
  refine ⟨α, C, hα, hC, ?_⟩
  intro Omega a f u x₀ R M ρ h ha hf hu0 hu hρ hρR hle hext
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ ρ ⊆
      (Omega : Set (EuclideanSpace ℝ ι)) ∩ ball x₀ R :=
    inter_subset_inter_right _ (ball_subset_ball hρR)
  rcases lt_or_ge M 0 with hM | hM
  · -- For `M < 0` the hypothesis says that `Ω ∩ B(x₀, R)` is null.
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hle] with x hx
    exact absurd ((abs_nonneg _).trans hx) (not_le.2 hM)
  rw [W1p.ae_abs_value_le_iff inter_subset_left] at hle ⊢
  -- Both `u` and `-u` are subsolutions vanishing on the boundary, with data `f` and `-f`.
  have hneg := hdecay (u := -u) (f := -f) h ha hf.neg
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem hu0))
    (fun v _ => by
      rw [energyFormH1_neg_left, hu v]
      simp only [Pi.neg_apply, neg_mul, integral_neg, le_refl])
    hρ hρR hM hle.2 hext
  rw [eLpNorm_neg] at hneg
  exact ⟨hdecay h ha hf (W1p.posPart_mem_w1p0Submodule (by norm_num) hu0)
    (fun v _ => (hu v).le) hρ hρR hM hle.1 hext, hneg⟩

end PDE

end TauCeti
