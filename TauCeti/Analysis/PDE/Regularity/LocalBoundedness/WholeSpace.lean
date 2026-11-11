/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.ClassicalSolution
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Upper bounds for weak subsolutions of `-Δu ≤ c` on the whole space

Let `E` be a nonzero finite-dimensional real inner product space with its volume measure, let
`c ≥ 0`, and let `u ∈ H¹(E) = W^{1,2}(E)` be a weak subsolution of `-Δu ≤ c` in the sense that

`∫ ⟪∇u, ∇v⟫ ≤ c ∫ v`

for every `v ∈ H¹(E)` that is nonnegative, bounded, and vanishes outside a set of finite measure.
This file proves that `u` is essentially bounded above, with

`u ≤ D (‖u⁺‖_{L²(E)} + c)` almost everywhere,

where `D` depends only on `E` (`TauCeti.PDE.exists_ae_value_le_mul_sqrt_integral_add`).
The weak inequality is required only against bounded test functions, which is the form in which
it is available for semilinear equations such as `Δu = f(x, u)` with `f` bounded below but with no
growth condition from above: there the nonlinear term is integrable against bounded test functions
of finite-measure support, but not necessarily against all of `H¹`.

## The argument

Truncating a nonnegative test function `v` at the levels `N = 0, 1, 2, …` and letting `N → ∞`
extends the weak inequality to every nonnegative `v ∈ H¹(E)` vanishing outside a set of finite
measure. Fix an orthonormal coordinate system `E ≃ ℝⁿ`, a point `x₀` and the unit ball
`B = B(x₀, 1)`. On `B`, the function

`w = u + c ‖x - x₀‖² / (2n)`

is a weak subsolution of `-Δw ≤ 0`, because `Δ (c ‖x - x₀‖² / (2n)) = c`; its restriction to `B`
therefore satisfies De Giorgi's local bound
(`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`)
`w ≤ D₀ ‖w⁺‖_{L²(B)}` on `B(x₀, 1/2)`. Since `0 ≤ w - u ≤ c` on `B`, this bounds `u` on
`B(x₀, 1/2)` by a constant independent of `x₀`, and countably many such balls cover `E`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.17.
-/

public section

noncomputable section

open Filter InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Gradient RealInnerProductSpace Topology

namespace TauCeti

namespace PDE

/-- An almost-everywhere statement on the whole space, read off its restriction to the open set
`⊤`, without rewriting inside the statement. -/
private theorem ae_of_ae_restrict_top {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} {P : α → Prop}
    (h : ∀ᵐ x ∂μ.restrict ((⊤ : Opens α) : Set α), P x) : ∀ᵐ x ∂μ, P x :=
  ((ae_restrict_iff' (⊤ : Opens α).isOpen.measurableSet).1 h).mono fun _ hx => hx trivial

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]

/-- **Truncation of test functions.** If the weak inequality `∫ ⟪∇u, ∇v⟫ ≤ c ∫ v` holds for every
bounded nonnegative `v ∈ H¹` vanishing outside a set of finite measure, it holds for every
nonnegative `v ∈ H¹` vanishing outside a set of finite measure. The truncations `min v N` are
admissible, and both sides converge as `N → ∞` by dominated convergence. -/
private theorem integral_inner_gradient_le_of_forall_bounded {u v : W1p mu ⊤ 2} {c : ℝ}
    (hu : ∀ (v : W1p mu ⊤ 2) (K : Set E) (M : ℝ), mu K ≠ ∞ → (∀ᵐ x ∂mu, 0 ≤ W1p.value v x) →
      (∀ᵐ x ∂mu, W1p.value v x ≤ M) → (∀ᵐ x ∂mu, x ∉ K → W1p.value v x = 0) →
      ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ∂mu ≤ c * ∫ x, W1p.value v x ∂mu)
    {K : Set E} (hK : mu K ≠ ∞) (hv : ∀ᵐ x ∂mu, 0 ≤ W1p.value v x)
    (hvK : ∀ᵐ x ∂mu, x ∉ K → W1p.value v x = 0) :
    ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ∂mu ≤ c * ∫ x, W1p.value v x ∂mu := by
  have hp : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  have htop : mu.restrict ((⊤ : Opens E) : Set E) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hmeas (f : W1p mu ⊤ 2) : AEStronglyMeasurable (W1p.value f) mu ∧
      AEStronglyMeasurable (W1p.gradient f) mu :=
    ⟨by simpa only [htop] using Lp.aestronglyMeasurable (W1p.value f),
      by simpa only [htop] using Lp.aestronglyMeasurable (W1p.gradient f)⟩
  -- The truncation `w N = v - (v - N)⁺ = min v N`.
  let w : ℕ → W1p mu ⊤ 2 := fun N => v - W1p.posPartAbove hp (Nat.cast_nonneg N) v
  have hval (N : ℕ) : ∀ᵐ x ∂mu,
      W1p.value (w N) x = W1p.value v x - max (W1p.value v x - N) 0 := by
    have h := W1p.value_posPartAbove_ae hp (Nat.cast_nonneg N) v
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    have hsub := W1p.value_sub_ae v (W1p.posPartAbove hp (Nat.cast_nonneg N) v)
    simp only [Opens.coe_top, Measure.restrict_univ] at hsub
    filter_upwards [hsub, h] with x hx hx'
    rw [hx, Pi.sub_apply, hx']
  have hgrad (N : ℕ) : ∀ᵐ x ∂mu, W1p.gradient (w N) x =
      W1p.gradient v x - {y | (N : ℝ) < W1p.value v y}.indicator (W1p.gradient v) x := by
    have h := W1p.gradient_posPartAbove_ae hp (Nat.cast_nonneg N) v
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    have hsub := Lp.coeFn_sub (W1p.gradient v)
      (W1p.gradient (W1p.posPartAbove hp (Nat.cast_nonneg N) v))
    simp only [Opens.coe_top, Measure.restrict_univ] at hsub
    filter_upwards [hsub, h] with x hx hx'
    rw [show W1p.gradient (w N) = _ from W1p.gradient_sub _ _, hx, Pi.sub_apply, hx']
  -- For almost every `x`, both truncated integrands agree with the limit once `N > v x`.
  have hevent : ∀ᵐ x ∂mu, ∀ᶠ N : ℕ in atTop, W1p.value (w N) x = W1p.value v x ∧
      W1p.gradient (w N) x = W1p.gradient v x := by
    filter_upwards [ae_all_iff.2 hval, ae_all_iff.2 hgrad] with x hx hg
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (W1p.value v x)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hlt : W1p.value v x < N := hN₀.trans_le (by exact_mod_cast hN)
    refine ⟨by rw [hx N, max_eq_right (by linarith), sub_zero], ?_⟩
    rw [hg N, indicator_of_notMem (by simpa using hlt.le), sub_zero]
  have hvint : Integrable (W1p.value v) mu := by
    simpa using (integrableOn_Lp_of_measure_ne_top (W1p.value v) one_le_two
      (s := K) (by simpa using hK)).integrable_of_ae_notMem_eq_zero (by simpa using hvK)
  -- The gradient term converges by dominated convergence, with bound `‖∇u‖ ‖∇v‖`.
  have hlim₁ : Tendsto (fun N : ℕ => ∫ x, ⟪W1p.gradient u x, W1p.gradient (w N) x⟫ ∂mu) atTop
      (𝓝 (∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖W1p.gradient u x‖ * ‖W1p.gradient v x‖)
      (fun N => (hmeas u).2.inner (hmeas (w N)).2) ?_ (fun N => ?_) ?_
    · have h1 := (Lp.memLp (W1p.gradient u)).norm
      have h2 := (Lp.memLp (W1p.gradient v)).norm
      simp only [Opens.coe_top, Measure.restrict_univ] at h1 h2
      exact h1.integrable_mul h2
    · filter_upwards [hgrad N] with x hx
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [hx]
      by_cases hxN : (N : ℝ) < W1p.value v x
      · simp [indicator_of_mem (show x ∈ {y | (N : ℝ) < W1p.value v y} from hxN)]
      · simp [indicator_of_notMem (show x ∉ {y | (N : ℝ) < W1p.value v y} from hxN)]
    · filter_upwards [hevent] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun N hN => by simp only [hN.2])
  -- The value term converges by dominated convergence, with bound `|v|`.
  have hlim₂ : Tendsto (fun N : ℕ => ∫ x, W1p.value (w N) x ∂mu) atTop
      (𝓝 (∫ x, W1p.value v x ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖W1p.value v x‖)
      (fun N => (hmeas (w N)).1) hvint.norm (fun N => ?_) ?_
    · filter_upwards [hval N, hv] with x hx hx0
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
      constructor <;> cases max_cases (W1p.value v x - N) 0 <;>
        nlinarith [abs_nonneg (W1p.value v x), le_abs_self (W1p.value v x),
          (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · filter_upwards [hevent] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun N hN => by simp only [hN.1])
  refine le_of_tendsto_of_tendsto' hlim₁ (hlim₂.const_mul c) fun N => hu (w N) K N hK ?_ ?_ ?_
  · filter_upwards [hval N, hv] with x hx hx0
    rw [hx]
    cases max_cases (W1p.value v x - N) 0 <;> linarith
  · filter_upwards [hval N] with x hx
    rw [hx]
    cases max_cases (W1p.value v x - N) 0 <;> linarith
  · filter_upwards [hval N, hvK] with x hx hxK hxn
    rw [hx, hxK hxn]
    simp

end Truncation

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The quadratic `c ‖x - x₀‖² / (2n)` on `ℝⁿ` has Laplacian `c`. -/
private theorem laplacian_div_mul_norm_sub_sq [Nonempty ι] (c : ℝ) (x₀ x : EuclideanSpace ℝ ι) :
    Δ (fun y : EuclideanSpace ℝ ι => (c / (2 * Fintype.card ι) * ‖y - x₀‖ ^ 2 : ℝ)) x = c := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hf : (fun y : EuclideanSpace ℝ ι => c / (2 * Fintype.card ι) * ‖y - x₀‖ ^ 2) =
      (c / (2 * Fintype.card ι)) • fun y => (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (y + -x₀) := by
    ext y
    simp [sub_eq_add_neg]
  rw [hf, InnerProductSpace.laplacian_smul
      (f := fun y : EuclideanSpace ℝ ι => (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (y + -x₀)) _
      ((contDiff_norm_sq ℝ).comp (contDiff_id.add contDiff_const)).contDiffAt,
    congrFun (laplacian_comp_add_right (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) (-x₀)) x,
    laplacian_norm_sq, finrank_euclideanSpace, smul_eq_mul]
  field_simp

/-- **Restriction to an open set of finite measure.** If `-Δu ≤ c` weakly on `ℝⁿ`, tested against
nonnegative `v ∈ H¹` vanishing outside a set of finite measure, then the restriction of `u` to an
open set `U` of finite measure satisfies `∫_U ⟪∇u, ∇v⟫ ≤ c ∫_U v` for nonnegative `v ∈ H¹₀(U)`. -/
private theorem energyFormH1_restrictL_le
    {u : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2} {c : ℝ}
    (hu : ∀ (v : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2) (K : Set (EuclideanSpace ℝ ι)),
      volume K ≠ ∞ → (∀ᵐ x, 0 ≤ W1p.value v x) → (∀ᵐ x, x ∉ K → W1p.value v x = 0) →
      ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x)
    {U : Opens (EuclideanSpace ℝ ι)} (hU : volume (U : Set (EuclideanSpace ℝ ι)) ≠ ∞)
    (v : W1p0 volume U 2) (hv : ∀ᵐ x ∂volume.restrict U, 0 ≤ W1p.value (v : W1p volume U 2) x) :
    energyFormH1 (fun _ => (1 : Matrix ι ι ℝ)) 0 0 (W1p.restrictL le_top u)
      (v : W1p volume U 2) ≤ c * ∫ x in U, W1p.value (v : W1p volume U 2) x := by
  -- The zero extension of `v` is an admissible test function on `ℝⁿ`.
  have hVval : W1p.value (W1p0.extendByZeroL le_top v :
      W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2) =ᵐ[volume]
      (U : Set (EuclideanSpace ℝ ι)).indicator (W1p.value (v : W1p volume U 2)) := by
    rw [W1p0.value_extendByZeroL]
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      coeFn_extendByZeroLpₗᵢ ℝ U.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : U ≤ ⊤)) (W1p.value (v : W1p volume U 2))
  have hV0 : ∀ᵐ x, 0 ≤ W1p.value (W1p0.extendByZeroL le_top v :
      W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2) x := by
    filter_upwards [hVval, (ae_restrict_iff' U.isOpen.measurableSet).1 hv] with x hx hxv
    rw [hx]
    by_cases hxb : x ∈ (U : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxb]
      exact hxv hxb
    · rw [indicator_of_notMem hxb]
  have huV := hu (W1p0.extendByZeroL le_top v) U hU hV0
    (W1p0.value_extendByZeroL_ae_eq_zero_compl v)
  rw [energyFormH1_restrictL _ _ _ le_top, energyFormH1_one_zero_zero_eq_inner, L2.inner_def,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => (hx (by simp)).elim,
    ← integral_indicator U.isOpen.measurableSet, ← integral_congr_ae hVval]
  exact huV

/-- **The quadratic on the unit ball.** On `B = B(x₀, 1)`, the function `c ‖x - x₀‖² / (2n)` lies in
`H¹(B)` and satisfies `∫_B ⟪∇q, ∇v⟫ = -c ∫_B v` for every `v ∈ H¹₀(B)`. -/
private theorem exists_energyFormH1_quadratic [Nonempty ι] (c : ℝ) (x₀ : EuclideanSpace ℝ ι) :
    ∃ Q : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2,
      (∀ᵐ x ∂volume.restrict (ball x₀ 1),
        W1p.value Q x = c / (2 * Fintype.card ι) * ‖x - x₀‖ ^ 2) ∧
      ∀ v : W1p0 volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2,
        energyFormH1 (fun _ => (1 : Matrix ι ι ℝ)) 0 0 Q
          (v : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) =
          -(c * ∫ x in ball x₀ 1, W1p.value
            (v : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) x) := by
  -- The quadratic, kept opaque so that its Laplacian is only computed once.
  obtain ⟨q, hqdef⟩ : ∃ q : EuclideanSpace ℝ ι → ℝ,
      q = fun y => c / (2 * Fintype.card ι) * ‖y - x₀‖ ^ 2 := ⟨_, rfl⟩
  have hq : ContDiff ℝ 2 q := by
    rw [hqdef]
    exact contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hΔq : Δ q = fun _ => c := by
    rw [hqdef]
    exact funext (laplacian_div_mul_norm_sub_sq c x₀)
  have : IsFiniteMeasure (volume.restrict (ball x₀ 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨Q, hQv, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
    (mu := volume) (Omega := ⟨ball x₀ 1, isOpen_ball⟩) (p := 2) isOpen_univ
    (hq.of_le one_le_two).contDiffOn (isCompact_closedBall x₀ 1) ball_subset_closedBall
    (subset_univ _)
  refine ⟨Q, ?_, fun v => ?_⟩
  · filter_upwards [hQv] with x hx
    rw [hx, hqdef]
  rw [energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul hq.contDiffOn hQv
    (by rw [hΔq]; exact memLp_const c) v, hΔq, ← integral_const_mul, ← integral_neg]
  exact integral_congr_ae (ae_of_all _ fun x => neg_mul _ _)

/-- **A subsolution on the unit ball.** If `-Δu ≤ c` weakly on `ℝⁿ`, tested against nonnegative
`v ∈ H¹` vanishing outside a set of finite measure, then on `B = B(x₀, 1)` the function
`w = u + c ‖x - x₀‖² / (2n)` lies in `H¹(B)` and is a weak subsolution of `-Δw ≤ 0`. -/
private theorem exists_subsolution_ball [Nonempty ι]
    {u : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2} {c : ℝ}
    (hu : ∀ (v : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2) (K : Set (EuclideanSpace ℝ ι)),
      volume K ≠ ∞ → (∀ᵐ x, 0 ≤ W1p.value v x) → (∀ᵐ x, x ∉ K → W1p.value v x = 0) →
      ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x)
    (x₀ : EuclideanSpace ℝ ι) :
    ∃ w : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2,
      (∀ᵐ x ∂volume.restrict (ball x₀ 1),
        W1p.value w x = W1p.value u x + c / (2 * Fintype.card ι) * ‖x - x₀‖ ^ 2) ∧
      ∀ v : W1p0 volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2,
        (∀ᵐ x ∂volume.restrict (ball x₀ 1), 0 ≤ W1p.value
          (v : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) x) →
          energyFormH1 (fun _ => (1 : Matrix ι ι ℝ)) 0 0 w
            (v : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) ≤ 0 := by
  obtain ⟨Q, hQv, hQ⟩ := exists_energyFormH1_quadratic (ι := ι) c x₀
  refine ⟨W1p.restrictL le_top u + Q, ?_, fun v hv => ?_⟩
  · filter_upwards [W1p.value_add_ae (W1p.restrictL le_top u) Q,
      W1p.value_restrictL_ae (U := ⟨ball x₀ 1, isOpen_ball⟩) le_top u, hQv] with x h₁ h₂ h₃
    rw [h₁, Pi.add_apply, h₂, h₃]
  have h : energyFormH1 (fun _ => (1 : Matrix ι ι ℝ)) 0 0 (W1p.restrictL le_top u)
      (v : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) ≤
      c * ∫ x in ball x₀ 1, W1p.value
        (v : W1p volume (⟨ball x₀ 1, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) 2) x :=
    energyFormH1_restrictL_le hu measure_ball_lt_top.ne v hv
  rw [energyFormH1_one_zero_zero_eq_inner, W1p.gradient_add, inner_add_left,
    ← energyFormH1_one_zero_zero_eq_inner, ← energyFormH1_one_zero_zero_eq_inner, hQ v]
  linarith

omit [DecidableEq ι] in
/-- If `f ≤ u + c` almost everywhere on `B(x₀, 1)`, then
`∫_{B(x₀, 1)} (f⁺)² ≤ 2 ‖u⁺‖²_{L²(ℝⁿ)} + 2 c² |B(0, 1)|`. -/
private theorem setIntegral_ball_max_sq_le {u : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2}
    {f : EuclideanSpace ℝ ι → ℝ} {c : ℝ} (hc : 0 ≤ c) {x₀ : EuclideanSpace ℝ ι}
    (hf : ∀ᵐ x ∂volume.restrict (ball x₀ 1), f x ≤ W1p.value u x + c) :
    ∫ x in ball x₀ 1, max (f x) 0 ^ 2 ≤
      2 * (∫ x, max (W1p.value u x) 0 ^ 2) +
        2 * c ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ ι) 1) := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (fun x => max (W1p.value u x) 0 ^ 2) := by
    refine (W1p.memLp_value u).integrable_sq.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((W1p.memLp_value u).aestronglyMeasurable.sup aestronglyMeasurable_const).pow 2
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rcases max_cases (W1p.value u x) 0 with h | h
      · rw [h.1]
      · rw [h.1]
        nlinarith [sq_nonneg (W1p.value u x)]
  calc ∫ x in ball x₀ 1, max (f x) 0 ^ 2
      ≤ ∫ x in ball x₀ 1, (2 * max (W1p.value u x) 0 ^ 2 + 2 * c ^ 2) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          ((hint.const_mul 2).integrableOn.add (integrable_const _)) ?_
        filter_upwards [hf] with x hx
        have h₁ : max (f x) 0 ≤ max (W1p.value u x) 0 + c :=
          max_le (hx.trans (by gcongr; exact le_max_left _ _)) (by positivity)
        nlinarith [le_max_right (f x) 0, le_max_right (W1p.value u x) 0,
          sq_nonneg (max (W1p.value u x) 0 - c)]
    _ = 2 * (∫ x in ball x₀ 1, max (W1p.value u x) 0 ^ 2) +
          2 * c ^ 2 * volume.real (ball x₀ 1) := by
        rw [integral_add (hint.const_mul 2).integrableOn (integrable_const _), integral_const_mul,
          setIntegral_const, smul_eq_mul]
        ring
    _ ≤ 2 * (∫ x, max (W1p.value u x) 0 ^ 2) +
          2 * c ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ ι) 1) := by
        rw [measureReal_def, Measure.addHaar_ball_center, ← measureReal_def]
        linarith [setIntegral_le_integral (s := ball x₀ 1) hint
          (ae_of_all _ fun x => sq_nonneg _)]

omit [DecidableEq ι] in
/-- **The bound on half balls.** There is `D₀ > 0` such that if `-Δu ≤ c` weakly on `ℝⁿ`, tested
against nonnegative `v ∈ H¹` vanishing outside a set of finite measure, with `c ≥ 0`, then
`u ≤ D₀ (2 ‖u⁺‖²_{L²} + 2 c² |B(0, 1)|)^{1/2}` almost everywhere on every ball `B(x₀, 1/2)`. -/
private theorem exists_ae_value_le_mul_sqrt_ball_half [Nonempty ι] :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ {u : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2} {c : ℝ}, 0 ≤ c →
      (∀ (v : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2) (K : Set (EuclideanSpace ℝ ι)),
        volume K ≠ ∞ → (∀ᵐ x, 0 ≤ W1p.value v x) → (∀ᵐ x, x ∉ K → W1p.value v x = 0) →
        ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x) →
      ∀ x₀ : EuclideanSpace ℝ ι, ∀ᵐ x ∂volume.restrict (ball x₀ (1 / 2)),
        W1p.value u x ≤ D₀ * √(2 * (∫ x, max (W1p.value u x) 0 ^ 2) +
          2 * c ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) := by
  classical
  obtain ⟨D₀, hD₀, hDG⟩ := exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral
    (mu := (volume : Measure (EuclideanSpace ℝ ι))) (lam := 1) (Lam := 1)
  refine ⟨D₀, hD₀, fun {u c} hc hu x₀ => ?_⟩
  -- De Giorgi's bound for `w = u + q`, `q = c ‖x - x₀‖² / (2n)`, on `B(x₀, 1/2)`.
  obtain ⟨w, hwv, hwsub⟩ := exists_subsolution_ball hu x₀
  have hq (x : EuclideanSpace ℝ ι) (hx : x ∈ ball x₀ 1) :
      0 ≤ c / (2 * Fintype.card ι) * ‖x - x₀‖ ^ 2 ∧
        c / (2 * Fintype.card ι) * ‖x - x₀‖ ^ 2 ≤ c := by
    have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
    have hx' : ‖x - x₀‖ ^ 2 ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hx
      nlinarith [norm_nonneg (x - x₀)]
    refine ⟨by positivity, ?_⟩
    calc c / (2 * Fintype.card ι) * ‖x - x₀‖ ^ 2 ≤ c / (2 * Fintype.card ι) * 1 := by gcongr
      _ ≤ c := by
          rw [mul_one, div_le_iff₀ (by positivity)]
          nlinarith
  have hint := setIntegral_ball_max_sq_le (u := u) (f := fun x => W1p.value w x - 0) hc
    (x₀ := x₀) (by
      filter_upwards [hwv, ae_restrict_mem measurableSet_ball] with x hx hxb
      rw [hx, sub_zero]
      linarith [(hq x hxb).2])
  have hbound := hDG (Omega := ⟨ball x₀ 1, isOpen_ball⟩) (a := fun _ => 1) (u := w) (k := 0)
    (x₀ := x₀) (R := 1) (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const hwsub
    one_pos subset_rfl
  filter_upwards [hbound, ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by norm_num)) hwv, ae_restrict_mem measurableSet_ball] with x hx hwx hxb
  rw [hwx, Real.one_rpow, mul_one, zero_add] at hx
  linarith [(hq x (ball_subset_ball (by norm_num) hxb)).1,
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hint) hD₀.le]

/-- `√(2a + 2c²b) ≤ √2 (1 + √b) (√a + c)` for `a, b, c ≥ 0`. -/
private theorem sqrt_two_mul_add_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    √(2 * a + 2 * c ^ 2 * b) ≤ √2 * (1 + √b) * (√a + c) := by
  have h₁ : 2 * a + 2 * c ^ 2 * b ≤ (√2 * (√a + √b * c)) ^ 2 := by
    have hexp : (√2 * (√a + √b * c)) ^ 2 =
        √2 ^ 2 * (√a ^ 2 + √b ^ 2 * c ^ 2 + 2 * (√a * √b * c)) := by ring
    rw [hexp, Real.sq_sqrt zero_le_two, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)) hc]
  calc √(2 * a + 2 * c ^ 2 * b) ≤ √((√2 * (√a + √b * c)) ^ 2) := Real.sqrt_le_sqrt h₁
    _ = √2 * (√a + √b * c) := Real.sqrt_sq (by positivity)
    _ ≤ √2 * (1 + √b) * (√a + c) := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg 2) hc,
        mul_nonneg (Real.sqrt_nonneg 2) (mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg a))]

omit [DecidableEq ι] in
/-- **Upper bounds for subsolutions of `-Δu ≤ c` on `ℝⁿ`.** This is
`TauCeti.PDE.exists_ae_value_le_mul_sqrt_integral_add` for `E = ℝⁿ`. -/
private theorem exists_ae_value_le_mul_sqrt_integral_add_euclidean [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {u : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2} {c : ℝ}, 0 ≤ c →
      (∀ (v : W1p (volume : Measure (EuclideanSpace ℝ ι)) ⊤ 2) (K : Set (EuclideanSpace ℝ ι))
        (M : ℝ), volume K ≠ ∞ → (∀ᵐ x, 0 ≤ W1p.value v x) → (∀ᵐ x, W1p.value v x ≤ M) →
        (∀ᵐ x, x ∉ K → W1p.value v x = 0) →
        ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x) →
      ∀ᵐ x, W1p.value u x ≤ D * (√(∫ x, max (W1p.value u x) 0 ^ 2) + c) := by
  obtain ⟨D₀, hD₀, hloc⟩ := exists_ae_value_le_mul_sqrt_ball_half (ι := ι)
  set V₁ := volume.real (ball (0 : EuclideanSpace ℝ ι) 1)
  refine ⟨D₀ * (√2 * (1 + √V₁)), by positivity, fun {u c} hc hu => ?_⟩
  have hball (x₀ : EuclideanSpace ℝ ι) : ∀ᵐ x ∂volume.restrict (ball x₀ (1 / 2)),
      W1p.value u x ≤ D₀ * (√2 * (1 + √V₁)) * (√(∫ x, max (W1p.value u x) 0 ^ 2) + c) := by
    filter_upwards [hloc hc
      (fun v K hK hv hvK => integral_inner_gradient_le_of_forall_bounded hu hK hv hvK) x₀]
      with x hx
    rw [mul_assoc]
    exact hx.trans (mul_le_mul_of_nonneg_left (sqrt_two_mul_add_le
      (integral_nonneg fun x => sq_nonneg _) measureReal_nonneg hc) hD₀.le)
  -- Countably many balls `B(s, 1/2)` cover `ℝⁿ`.
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ ι)
  have hcover : (⋃ s ∈ S, ball s (1 / 2)) = univ :=
    eq_univ_of_forall fun x => by
      obtain ⟨s, hs, hxs⟩ := hSd.exists_dist_lt x (by norm_num : (0 : ℝ) < 1 / 2)
      exact mem_biUnion hs (mem_ball.2 hxs)
  have h := (ae_restrict_biUnion_iff (fun s => ball s (1 / 2)) hSc _).2 fun s _ => hball s
  rwa [hcover, Measure.restrict_univ] at h

end Euclidean

section Isometry

variable {F F' : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
  [FiniteDimensional ℝ F'] [MeasurableSpace F'] [BorelSpace F']

/-- **Rigid changes of coordinates preserve weak subsolutions of `-Δu ≤ c`.** If `u ∈ H¹(F')`
satisfies `∫ ⟪∇u, ∇v⟫ ≤ c ∫ v` for all bounded nonnegative `v ∈ H¹(F')` vanishing outside a set
of finite measure, then so does `u ∘ g` on `F`, for every affine isometry `g : F ≃ F'`. Test
functions are transported by `g⁻¹`, which preserves the three conditions on them and both
integrals. -/
private theorem integral_inner_gradient_compAffineIsometryEquivL_le (g : F ≃ᵃⁱ[ℝ] F')
    {u : W1p (volume : Measure F') ⊤ 2} {c : ℝ}
    (hu : ∀ (v : W1p (volume : Measure F') ⊤ 2) (K : Set F') (M : ℝ), volume K ≠ ∞ →
      (∀ᵐ x, 0 ≤ W1p.value v x) → (∀ᵐ x, W1p.value v x ≤ M) →
      (∀ᵐ x, x ∉ K → W1p.value v x = 0) →
      ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x)
    (v : W1p (volume : Measure F) ⊤ 2) (K : Set F) (M : ℝ) (hK : volume K ≠ ∞)
    (hv : ∀ᵐ x, 0 ≤ W1p.value v x) (hvM : ∀ᵐ x, W1p.value v x ≤ M)
    (hvK : ∀ᵐ x, x ∉ K → W1p.value v x = 0) :
    ∫ x, ⟪W1p.gradient (W1p.compAffineIsometryEquivL (U := ⊤) (V := ⊤) g (by simp) u) x,
      W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x := by
  have hg := g.measurePreserving
  have hgs := g.symm.measurePreserving
  have hVU : ((⊤ : Opens F') : Set F') = g.symm ⁻¹' ((⊤ : Opens F) : Set F) := by simp
  -- The transported test function `v ∘ g⁻¹` on `F'`.
  have hv'val : ∀ᵐ y, W1p.value (W1p.compAffineIsometryEquivL g.symm hVU v) y =
      W1p.value v (g.symm y) := by
    exact ae_of_ae_restrict_top (W1p.value_compAffineIsometryEquivL_ae g.symm hVU v)
  have hv'grad : ∀ᵐ y, W1p.gradient (W1p.compAffineIsometryEquivL g.symm hVU v) y =
      g.linearIsometryEquiv (W1p.gradient v (g.symm y)) := by
    filter_upwards [ae_of_ae_restrict_top
      (W1p.gradient_compAffineIsometryEquivL_ae g.symm hVU v)] with y hy
    rw [hy]
    rfl
  have hugrad : ∀ᵐ x, W1p.gradient (W1p.compAffineIsometryEquivL (U := ⊤) (V := ⊤) g
      (by simp) u) x = g.linearIsometryEquiv.symm (W1p.gradient u (g x)) := by
    exact ae_of_ae_restrict_top
      (W1p.gradient_compAffineIsometryEquivL_ae (U := ⊤) (V := ⊤) g (by simp) u)
  -- The admissibility conditions and the integrals transfer along `g⁻¹`.
  have hK' : volume (g.symm ⁻¹' toMeasurable volume K) ≠ ∞ := by
    rw [hgs.measure_preimage (measurableSet_toMeasurable _ _).nullMeasurableSet,
      measure_toMeasurable]
    exact hK
  have h := hu (W1p.compAffineIsometryEquivL g.symm hVU v) (g.symm ⁻¹' toMeasurable volume K) M
    hK'
    (by filter_upwards [hv'val, hgs.quasiMeasurePreserving.ae hv] with y hy h0; rwa [hy])
    (by filter_upwards [hv'val, hgs.quasiMeasurePreserving.ae hvM] with y hy h0; rwa [hy])
    (by
      filter_upwards [hv'val, hgs.quasiMeasurePreserving.ae hvK] with y hy h0 hyK
      rw [hy]
      exact h0 fun hk => hyK (subset_toMeasurable volume K hk))
  have hval : ∫ y, W1p.value (W1p.compAffineIsometryEquivL g.symm hVU v) y =
      ∫ x, W1p.value v x := by
    rw [integral_congr_ae hv'val, hgs.integral_comp g.symm.toHomeomorph.measurableEmbedding]
  have hgrad : ∫ y, ⟪W1p.gradient u y,
      W1p.gradient (W1p.compAffineIsometryEquivL g.symm hVU v) y⟫ =
      ∫ x, ⟪W1p.gradient (W1p.compAffineIsometryEquivL (U := ⊤) (V := ⊤) g (by simp) u) x,
        W1p.gradient v x⟫ := by
    rw [integral_congr_ae (hv'grad.mono fun y hy => by rw [hy]),
      ← hg.integral_comp g.toHomeomorph.measurableEmbedding]
    refine integral_congr_ae (hugrad.mono fun x hx => ?_)
    dsimp only
    rw [hx, g.symm_apply_apply, ← g.linearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.apply_symm_apply]
  rw [← hval, ← hgrad]
  exact h

end Isometry

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Weak subsolutions of `-Δu ≤ c` on the whole space are bounded above.** On a nonzero
finite-dimensional real inner product space `E` there is `D > 0` such that every `u ∈ H¹(E)`
with

`∫ ⟪∇u, ∇v⟫ ≤ c ∫ v`

for all `v ∈ H¹(E)` that are nonnegative, bounded and vanish outside a set of finite measure,
where `c ≥ 0`, satisfies

`u ≤ D (‖u⁺‖_{L²(E)} + c)` almost everywhere.

The constant depends only on `E` (through its dimension). -/
theorem exists_ae_value_le_mul_sqrt_integral_add [Nontrivial E] :
    ∃ D : ℝ, 0 < D ∧ ∀ {u : W1p (volume : Measure E) ⊤ 2} {c : ℝ}, 0 ≤ c →
      (∀ (v : W1p (volume : Measure E) ⊤ 2) (K : Set E) (M : ℝ), volume K ≠ ∞ →
        (∀ᵐ x, 0 ≤ W1p.value v x) → (∀ᵐ x, W1p.value v x ≤ M) →
        (∀ᵐ x, x ∉ K → W1p.value v x = 0) →
        ∫ x, ⟪W1p.gradient u x, W1p.gradient v x⟫ ≤ c * ∫ x, W1p.value v x) →
      ∀ᵐ x, W1p.value u x ≤ D * (√(∫ x, max (W1p.value u x) 0 ^ 2) + c) := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨D, hD, h⟩ :=
    exists_ae_value_le_mul_sqrt_integral_add_euclidean (ι := Fin (Module.finrank ℝ E))
  refine ⟨D, hD, fun {u c} hc hu => ?_⟩
  -- Orthonormal coordinates `g : ℝⁿ ≃ E`, in which `u ∘ g` satisfies the same inequality.
  obtain ⟨g⟩ : Nonempty (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ᵃⁱ[ℝ] E) :=
    ⟨(stdOrthonormalBasis ℝ E).repr.symm.toAffineIsometryEquiv⟩
  have hval : ∀ᵐ x, W1p.value (W1p.compAffineIsometryEquivL (U := ⊤) (V := ⊤) g (by simp) u) x =
      W1p.value u (g x) :=
    ae_of_ae_restrict_top (W1p.value_compAffineIsometryEquivL_ae (U := ⊤) (V := ⊤) g (by simp) u)
  have hb := h hc (integral_inner_gradient_compAffineIsometryEquivL_le g hu)
  have hint : ∫ x, max (W1p.value (W1p.compAffineIsometryEquivL (U := ⊤) (V := ⊤) g
      (by simp) u) x) 0 ^ 2 = ∫ y, max (W1p.value u y) 0 ^ 2 := by
    rw [integral_congr_ae (hval.mono fun x hx => by rw [hx]),
      g.measurePreserving.integral_comp g.toHomeomorph.measurableEmbedding
        (fun y => max (W1p.value u y) 0 ^ 2)]
  rw [hint] at hb
  -- Transport the bound back along `g⁻¹`.
  have hb' : ∀ᵐ x, W1p.value u (g x) ≤ D * (√(∫ y, max (W1p.value u y) 0 ^ 2) + c) := by
    filter_upwards [hb, hval] with x h₁ h₂
    rwa [← h₂]
  filter_upwards [g.symm.measurePreserving.quasiMeasurePreserving.ae hb'] with y hy
  rwa [g.apply_symm_apply] at hy

end General

end PDE

end TauCeti
