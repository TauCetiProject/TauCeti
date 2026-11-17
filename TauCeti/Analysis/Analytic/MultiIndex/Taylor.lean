/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Pi.Interval
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import TauCeti.Algebra.MvPolynomial.Funext
import TauCeti.Analysis.Normed.Module.InfiniteSum

/-!
# Multi-index Taylor coefficients of analytic functions

This file defines `TauCeti.mvTaylorCoeff f x α`, the coefficient of `∏ i, (z i - x i) ^ α i` in
the power series expansion of `f : (ι → 𝕜) → F` about `x`, taking the value `0` when `f` is not
analytic at `x`. Because the multi-index coefficients of a formal power series depend only on the
local germ of the function (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`), `mvTaylorCoeff f x α`
agrees with `p.mvCoeff α` for any power series `p` of `f` at `x`.

The factorial `∏ i, (α i)!` multiplies `mvTaylorCoeff` when comparing with `iteratedFDeriv` and
`iteratedDeriv`; it is never inverted, so all statements hold in arbitrary characteristic.

## Main definitions and results

* `TauCeti.mvTaylorCoeff`: the multi-index Taylor coefficient of `f` at `x`.
* `HasFPowerSeriesAt.mvTaylorCoeff_eq` and `HasFPowerSeriesOnBall.mvTaylorCoeff_eq`: independence
  of the chosen formal power series.
* `AnalyticAt.mvTaylorCoeff_zero`, `TauCeti.mvTaylorCoeff_const`, `TauCeti.mvTaylorCoeff_zero_fun`:
  values at order `0` and on constant functions.
* `AnalyticAt.mvTaylorCoeff_add`, `TauCeti.mvTaylorCoeff_neg`, `AnalyticAt.mvTaylorCoeff_sub`,
  `TauCeti.mvTaylorCoeff_const_smul`, `TauCeti.mvTaylorCoeff_sum`: linearity properties.
* `Filter.EventuallyEq.mvTaylorCoeff_eq` and `TauCeti.mvTaylorCoeff_comp_add_right`: locality and
  translation invariance (without analyticity hypotheses).
* `AnalyticAt.exists_hasSum_mvTaylorCoeff` and `TauCeti.mvTaylorCoeff_eq_of_hasSum`: local normal
  expansion and identification of coefficients from a normally convergent expansion.
* `TauCeti.mvTaylorCoeff_prod_pow_smul` and `TauCeti.mvTaylorCoeff_prod_pow`: Taylor coefficients
  of monomials at `0`.
* `AnalyticAt.mvTaylorCoeff_smul` and `AnalyticAt.mvTaylorCoeff_mul`: the product rule (Cauchy
  product over `Finset.Iic α`).
* `ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`: linear change of variables preserves vanishing
  in each total degree.
* `AnalyticAt.prod_factorial_smul_mvTaylorCoeff` and
  `AnalyticAt.factorial_smul_mvTaylorCoeff_of_unique`: agreement with `iteratedFDeriv` and
  `iteratedDeriv`.

## References

Multi-index Taylor coefficients of analytic functions on `ι → 𝕜` also appear in Michail
Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit
`1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/TaylorCoeff.lean`, Apache 2.0). The
present development generalizes the product rule to bounded module actions without completeness
assumptions and states the iterated-derivative identities without inverting factorials.
-/

public section

open Filter Finset Topology
open scoped ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

open Classical in
/-- The **multi-index Taylor coefficient** of `f : (ι → 𝕜) → F` at `x`: the coefficient of
`∏ i, (z i - x i) ^ α i` in the power series expansion of `f` about `x`, and `0` if `f` is not
analytic at `x`. -/
noncomputable def mvTaylorCoeff (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) : F :=
  if h : AnalyticAt 𝕜 f x then h.choose.mvCoeff α else 0

/-- If `f` is not analytic at `x`, all its multi-index Taylor coefficients at `x` vanish. -/
theorem mvTaylorCoeff_of_not_analyticAt {f : (ι → 𝕜) → F} {x : ι → 𝕜} (h : ¬ AnalyticAt 𝕜 f x)
    (α : ι → ℕ) : mvTaylorCoeff f x α = 0 := by
  simp [mvTaylorCoeff, h]

end TauCeti

namespace HasFPowerSeriesAt

/-- The multi-index Taylor coefficient of `f` at `x` equals the multi-index coefficient of any
formal power series of `f` at `x`. -/
theorem mvTaylorCoeff_eq {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {x : ι → 𝕜} (hp : HasFPowerSeriesAt f p x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff f x α = p.mvCoeff α := by
  have h : AnalyticAt 𝕜 f x := ⟨p, hp⟩
  simp only [TauCeti.mvTaylorCoeff, h, ↓reduceDIte]
  exact h.choose_spec.mvCoeff_eq_of_eventuallyEq hp .rfl α

end HasFPowerSeriesAt

namespace HasFPowerSeriesOnBall

/-- The multi-index Taylor coefficient of `f` at `x` equals the multi-index coefficient of any
formal power series of `f` on a ball around `x`. -/
theorem mvTaylorCoeff_eq {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {x : ι → 𝕜} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p x r) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff f x α = p.mvCoeff α :=
  hp.hasFPowerSeriesAt.mvTaylorCoeff_eq α

end HasFPowerSeriesOnBall

namespace Filter.EventuallyEq

/-- **Locality**: functions that agree in a neighborhood of `x` have the same multi-index Taylor
coefficients at `x` (whether or not they are analytic there). -/
theorem mvTaylorCoeff_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (h : f =ᶠ[𝓝 x] g) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff f x α = TauCeti.mvTaylorCoeff g x α := by
  by_cases hf : AnalyticAt 𝕜 f x
  · obtain ⟨p, hp⟩ := hf
    rw [hp.mvTaylorCoeff_eq, (hp.congr h).mvTaylorCoeff_eq]
  · have hg : ¬ AnalyticAt 𝕜 g x := fun hg ↦ hf (hg.congr h.symm)
    rw [TauCeti.mvTaylorCoeff_of_not_analyticAt hf, TauCeti.mvTaylorCoeff_of_not_analyticAt hg]

end Filter.EventuallyEq

namespace AnalyticAt

/-- For a function analytic at `x`, the order-`0` multi-index Taylor coefficient is `f x`. -/
theorem mvTaylorCoeff_zero {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    TauCeti.mvTaylorCoeff f x 0 = f x := by
  obtain ⟨p, hp⟩ := hf
  rw [hp.mvTaylorCoeff_eq, p.mvCoeff_zero_eq_apply (fun _ ↦ 0), hp.coeff_zero]

/-- **Additivity** of multi-index Taylor coefficients for functions analytic at `x`. -/
theorem mvTaylorCoeff_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (f + g) x α =
      TauCeti.mvTaylorCoeff f x α + TauCeti.mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.add hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_add]

/-- **Subtraction** of multi-index Taylor coefficients for functions analytic at `x`. -/
theorem mvTaylorCoeff_sub {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (f - g) x α =
      TauCeti.mvTaylorCoeff f x α - TauCeti.mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.sub hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_sub]

end AnalyticAt

namespace TauCeti

/-- The multi-index Taylor coefficients of a constant function vanish except at `α = 0`, where the
coefficient is the constant value. -/
@[simp]
theorem mvTaylorCoeff_const (c : F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun _ : ι → 𝕜 ↦ c) x α = if α = 0 then c else 0 := by
  rw [(hasFPowerSeriesAt_const (𝕜 := 𝕜) (c := c) (e := x)).mvTaylorCoeff_eq]
  split_ifs with h
  · subst h
    rw [FormalMultilinearSeries.mvCoeff_zero_eq_apply _ (fun _ ↦ 0)]
    simp [constFormalMultilinearSeries]
  · classical
    have hpos : ∑ i, α i ≠ 0 := by
      intro h0
      apply h
      ext i
      exact (sum_eq_zero_iff.1 h0) i (mem_univ i)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [FormalMultilinearSeries.mvCoeff_eq_sum _ hn]
    simp [constFormalMultilinearSeries]

/-- Every multi-index Taylor coefficient of the zero function vanishes. -/
@[simp]
theorem mvTaylorCoeff_zero_fun (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (0 : (ι → 𝕜) → F) x α = 0 :=
  (mvTaylorCoeff_const (𝕜 := 𝕜) (0 : F) x α).trans (by simp)

/-- Negation commutes with `mvTaylorCoeff` without any analyticity assumption. -/
@[simp]
theorem mvTaylorCoeff_neg (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (-f) x α = -mvTaylorCoeff f x α := by
  by_cases hf : AnalyticAt 𝕜 f x
  · obtain ⟨p, hp⟩ := hf
    rw [hp.neg.mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, FormalMultilinearSeries.mvCoeff_neg]
  · have hnf : ¬ AnalyticAt 𝕜 (-f) x := fun h ↦ hf (by simpa using h.neg)
    rw [mvTaylorCoeff_of_not_analyticAt hnf, mvTaylorCoeff_of_not_analyticAt hf, neg_zero]

/-- Constant scalar multiples commute with `mvTaylorCoeff` without any analyticity assumption. -/
@[simp]
theorem mvTaylorCoeff_const_smul (c : 𝕜) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ c • f z) x α = c • mvTaylorCoeff f x α := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases hf : AnalyticAt 𝕜 f x
    · obtain ⟨p, hp⟩ := hf
      rw [← Pi.smul_def, (hp.const_smul (c := c)).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq,
        FormalMultilinearSeries.mvCoeff_smul]
    · have hcf : ¬ AnalyticAt 𝕜 (fun z ↦ c • f z) x := by
        intro h
        apply hf
        have h' := h.const_smul (c := c⁻¹)
        simpa [Pi.smul_def, inv_smul_smul₀ hc] using h'
      rw [mvTaylorCoeff_of_not_analyticAt hcf, mvTaylorCoeff_of_not_analyticAt hf, smul_zero]

/-- Finite sums of analytic functions have additive multi-index Taylor coefficients. -/
theorem mvTaylorCoeff_sum {κ : Type*} {s : Finset κ} {g : κ → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hg : ∀ j ∈ s, AnalyticAt 𝕜 (g j) x) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ ∑ j ∈ s, g j z) x α = ∑ j ∈ s, mvTaylorCoeff (g j) x α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hga : AnalyticAt 𝕜 (g a) x := hg a (mem_insert_self a s)
    have hgs : AnalyticAt 𝕜 (fun z ↦ ∑ j ∈ s, g j z) x := by
      have h := Finset.analyticAt_sum s fun j hj ↦ hg j (mem_insert_of_mem hj)
      convert h using 1
      ext z
      simp
    simp only [sum_insert ha]
    rw [← Pi.add_def, hga.mvTaylorCoeff_add hgs, ih fun j hj ↦ hg j (mem_insert_of_mem hj)]

/-- **Translation invariance**: translating `f` by `y` shifts the expansion point from `x + y` to
`x`, without any analyticity assumption. -/
theorem mvTaylorCoeff_comp_add_right (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (z + y)) x α = mvTaylorCoeff f (x + y) α := by
  have hiff (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (r : ℝ≥0∞) :
      HasFPowerSeriesOnBall (fun z ↦ f (z + y)) p x r ↔ HasFPowerSeriesOnBall f p (x + y) r := by
    constructor <;> intro h <;> refine ⟨h.r_le, h.r_pos, fun {w} hw ↦ ?_⟩
    · simpa [add_right_comm] using h.hasSum hw
    · simpa [add_right_comm] using h.hasSum hw
  by_cases hf : AnalyticAt 𝕜 f (x + y)
  · obtain ⟨p, r, hp⟩ := hf
    rw [((hiff p r).mpr hp).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq]
  · have hf' : ¬ AnalyticAt 𝕜 (fun z ↦ f (z + y)) x := by
      rintro ⟨p, r, hp'⟩
      exact hf ⟨p, r, (hiff p r).mp hp'⟩
    rw [mvTaylorCoeff_of_not_analyticAt hf', mvTaylorCoeff_of_not_analyticAt hf]

/-- **Coefficients from an expansion**: if `f (x + y)` is given on an open polydisc of positive
radius by a normally convergent multi-index series with coefficients `c`, then the multi-index
Taylor coefficients of `f` at `x` are `c`. -/
theorem mvTaylorCoeff_eq_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i))
    (h : ∀ y : ι → 𝕜, ‖y‖ < ρ →
      HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y)))
    (α : ι → ℕ) : mvTaylorCoeff f x α = c α := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_of_hasSum hρ hsum h
  rw [hp.mvTaylorCoeff_eq, hpc]

/-- At the origin, the monomial `(∏ i, z i ^ τ i) • v` has multi-index Taylor coefficient `v` at
`τ` and `0` at every other multi-index. -/
theorem mvTaylorCoeff_prod_pow_smul (τ : ι → ℕ) (v : F) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ (∏ i, z i ^ τ i) • v) 0 α = if α = τ then v else 0 := by
  refine mvTaylorCoeff_eq_of_hasSum (c := fun β ↦ if β = τ then v else 0) (ρ := 1) zero_lt_one
    ?_ (fun y _ ↦ ?_) α
  · refine summable_of_ne_finset_zero (s := {τ}) fun β hβ ↦ ?_
    simp [mem_singleton.not.mp hβ]
  · convert hasSum_ite_eq τ ((∏ i, y i ^ τ i) • v) using 1
    · ext β
      split_ifs with h <;> simp [h]
    · simp

/-- At the origin, the scalar monomial `∏ i, z i ^ τ i` has multi-index Taylor coefficient `1` at
`τ` and `0` at every other multi-index. -/
theorem mvTaylorCoeff_prod_pow (τ α : ι → ℕ) :
    mvTaylorCoeff (𝕜 := 𝕜) (fun z : ι → 𝕜 ↦ ∏ i, z i ^ τ i) 0 α = if α = τ then 1 else 0 := by
  simpa using mvTaylorCoeff_prod_pow_smul (𝕜 := 𝕜) τ (1 : 𝕜) α

end TauCeti

namespace AnalyticAt

/-- **Local expansion** of an analytic function: near `x`, `f (x + y)` is the sum of its
multi-index Taylor series on a polydisc of positive radius `ρ`, with normal convergence at `ρ`. -/
theorem exists_hasSum_mvTaylorCoeff {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      Summable (fun α : ι → ℕ ↦ ‖TauCeti.mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ i, α i)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ →
        HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • TauCeti.mvTaylorCoeff f x α) (f (x + y)) := by
  obtain ⟨p, r, hp⟩ := hf
  -- Pick a finite positive radius `r₀ < r ≤ p.radius`, then shrink by `card ι + 1` so that
  -- `(card ι) ^ k * ‖p k‖ * ρ ^ k` is dominated by `‖p k‖ * r₀ ^ k`.
  obtain ⟨r₀, hr₀_pos, hr₀_lt⟩ : ∃ r₀ : ℝ≥0, 0 < r₀ ∧ (r₀ : ℝ≥0∞) < r := by
    cases r with
    | top => exact ⟨1, one_pos, ENNReal.coe_lt_top⟩
    | coe r =>
      have hr : 0 < r := ENNReal.coe_pos.mp hp.r_pos
      exact ⟨r / 2, half_pos hr, ENNReal.coe_lt_coe.mpr (half_lt_self hr)⟩
  have hsum_r₀ : Summable fun k ↦ ‖p k‖ * (r₀ : ℝ) ^ k :=
    p.summable_norm_mul_pow (hr₀_lt.trans_le hp.r_le)
  let d : ℝ≥0 := Fintype.card ι + 1
  have hd_pos : 0 < d := by positivity
  let ρ : ℝ≥0 := r₀ / d
  have hρ_pos : 0 < ρ := div_pos hr₀_pos hd_pos
  have hcard_mul_ρ : (Fintype.card ι : ℝ) * (ρ : ℝ) ≤ (r₀ : ℝ) := by
    have hle : (Fintype.card ι : ℝ) ≤ (d : ℝ) := by simp [d]
    have hdR : (0 : ℝ) < (d : ℝ) := hd_pos
    calc (Fintype.card ι : ℝ) * (ρ : ℝ)
        ≤ (d : ℝ) * ((r₀ : ℝ) / (d : ℝ)) := by
          gcongr
          simp [ρ]
      _ = (r₀ : ℝ) := mul_div_cancel₀ _ hdR.ne'
  have hcard_sum : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) hsum_r₀
    calc (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k
        = ‖p k‖ * ((Fintype.card ι : ℝ) * (ρ : ℝ)) ^ k := by rw [mul_pow]; ring
      _ ≤ ‖p k‖ * (r₀ : ℝ) ^ k := by gcongr
  refine ⟨ρ, hρ_pos, ?_, fun y hy ↦ ?_⟩
  · simp_rw [hp.mvTaylorCoeff_eq]
    exact p.summable_norm_mvCoeff_mul_pow ρ.coe_nonneg hcard_sum
  · simp_rw [hp.mvTaylorCoeff_eq]
    have hρ_le : (ρ : ℝ) ≤ (r₀ : ℝ) := by
      have h1 : (1 : ℝ≥0) ≤ d := by simp [d]
      exact_mod_cast div_le_self zero_le h1
    have hy_ball : y ∈ Metric.eball (0 : ι → 𝕜) r := by
      rw [mem_eball_zero_iff, eNorm_eq_nnNorm]
      have hlt : ‖y‖₊ < r₀ := by exact_mod_cast hy.trans_le hρ_le
      exact (ENNReal.coe_lt_coe.mpr hlt).trans hr₀_lt
    have hy_sum : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖y‖ ^ k :=
      Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ by gcongr) hcard_sum
    exact hp.hasSum_mvCoeff hy_ball hy_sum

/-- Equivalence grouping pairs `(β, γ)` of multi-indices by their sum `β + γ`. -/
private def sigmaIicEquiv [DecidableEq ι] :
    (Σ δ : ι → ℕ, Iic δ) ≃ (ι → ℕ) × (ι → ℕ) where
  toFun q := (q.2.1, q.1 - q.2.1)
  invFun p := ⟨p.1 + p.2, ⟨p.1, mem_Iic.2 le_self_add⟩⟩
  left_inv := fun ⟨δ, ⟨β, hβ⟩⟩ ↦ by
    have hsum_eq : β + (δ - β) = δ := by
      ext i
      exact Nat.add_sub_of_le (mem_Iic.1 hβ i)
    refine Sigma.ext hsum_eq ?_
    refine (Subtype.heq_iff_coe_eq fun x ↦ ?_).2 rfl
    simp [hsum_eq]
  right_inv := fun ⟨β, γ⟩ ↦ by
    ext i <;> simp

/-- Normal convergence of the Cauchy-product coefficients of two normally convergent multi-index
families at radius `ρ ≥ 0`. -/
private theorem summable_norm_cauchy_mul_pow [DecidableEq ι] {A : Type*} [NormedRing A]
    [Module A F] [IsBoundedSMul A F] {a : (ι → ℕ) → A} {b : (ι → ℕ) → F} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (ha : Summable fun β : ι → ℕ ↦ ‖a β‖ * ρ ^ (∑ i, β i))
    (hb : Summable fun γ : ι → ℕ ↦ ‖b γ‖ * ρ ^ (∑ i, γ i)) :
    Summable fun δ : ι → ℕ ↦ ‖∑ β ∈ Iic δ, a β • b (δ - β)‖ * ρ ^ (∑ i, δ i) := by
  have hprod : Summable fun p : (ι → ℕ) × (ι → ℕ) ↦
      (‖a p.1‖ * ρ ^ (∑ i, p.1 i)) * (‖b p.2‖ * ρ ^ (∑ i, p.2 i)) :=
    ha.mul_of_nonneg hb (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  have hsigma : Summable fun q : Σ δ : ι → ℕ, Iic δ ↦
      (‖a q.2.1‖ * ρ ^ (∑ i, q.2.1 i)) *
        (‖b (q.1 - q.2.1)‖ * ρ ^ (∑ i, (q.1 - q.2.1) i)) :=
    (sigmaIicEquiv (ι := ι)).summable_iff.mpr hprod
  have hfib : Summable fun δ : ι → ℕ ↦
      ∑ β ∈ Iic δ, (‖a β‖ * ρ ^ (∑ i, β i)) * (‖b (δ - β)‖ * ρ ^ (∑ i, (δ - β) i)) := by
    have h := hsigma.sigma' fun δ ↦ (hasSum_fintype _).summable
    convert h using 1
    ext δ
    rw [tsum_fintype, Finset.univ_eq_attach]
    exact (sum_attach (Iic δ) fun β ↦
      (‖a β‖ * ρ ^ (∑ i, β i)) * (‖b (δ - β)‖ * ρ ^ (∑ i, (δ - β) i))).symm
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun δ ↦ ?_) hfib
  calc ‖∑ β ∈ Iic δ, a β • b (δ - β)‖ * ρ ^ (∑ i, δ i)
      ≤ (∑ β ∈ Iic δ, ‖a β • b (δ - β)‖) * ρ ^ (∑ i, δ i) :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ ≤ (∑ β ∈ Iic δ, ‖a β‖ * ‖b (δ - β)‖) * ρ ^ (∑ i, δ i) := by
        gcongr
        exact norm_smul_le _ _
    _ = ∑ β ∈ Iic δ, (‖a β‖ * ρ ^ (∑ i, β i)) * (‖b (δ - β)‖ * ρ ^ (∑ i, (δ - β) i)) := by
        rw [sum_mul]
        refine sum_congr rfl fun β hβ ↦ ?_
        have hdeg : ∑ i, β i + ∑ i, (δ - β) i = ∑ i, δ i := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun i _ ↦ Nat.add_sub_of_le (mem_Iic.1 hβ i)
        rw [← hdeg, pow_add]
        ring

/-- **The product rule** for multi-index Taylor coefficients under a bounded action of a normed
`𝕜`-algebra `A` on `F` (in particular, scalar-times-vector with `A = 𝕜`). No completeness
assumption on `F` is needed. -/
theorem mvTaylorCoeff_smul [DecidableEq ι] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : (ι → 𝕜) → A} {g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (fun z ↦ f z • g z) x α =
      ∑ β ∈ Iic α, TauCeti.mvTaylorCoeff f x β • TauCeti.mvTaylorCoeff g x (α - β) := by
  obtain ⟨ρ₁, hρ₁, hsum₁, hf_sum⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨ρ₂, hρ₂, hsum₂, hg_sum⟩ := hg.exists_hasSum_mvTaylorCoeff
  let ρ : ℝ≥0 := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  let a : (ι → ℕ) → A := TauCeti.mvTaylorCoeff f x
  let b : (ι → ℕ) → F := TauCeti.mvTaylorCoeff g x
  have ha_norm : Summable fun β : ι → ℕ ↦ ‖a β‖ * (ρ : ℝ) ^ (∑ i, β i) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun β ↦ by
      gcongr; exact_mod_cast min_le_left ρ₁ ρ₂) hsum₁
  have hb_norm : Summable fun γ : ι → ℕ ↦ ‖b γ‖ * (ρ : ℝ) ^ (∑ i, γ i) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun γ ↦ by
      gcongr; exact_mod_cast min_le_right ρ₁ ρ₂) hsum₂
  have hc_norm := summable_norm_cauchy_mul_pow ρ.coe_nonneg ha_norm hb_norm
  refine TauCeti.mvTaylorCoeff_eq_of_hasSum hρ hc_norm (fun y hy ↦ ?_) α
  have hy₁ : ‖y‖ < (ρ₁ : ℝ) := hy.trans_le (by exact_mod_cast min_le_left ρ₁ ρ₂)
  have hy₂ : ‖y‖ < (ρ₂ : ℝ) := hy.trans_le (by exact_mod_cast min_le_right ρ₁ ρ₂)
  have huv := (hf_sum y hy₁).smul_of_summable_norm (hg_sum y hy₂)
    (ha_norm.norm_prod_pow_smul_of_le hy.le) (hb_norm.norm_prod_pow_smul_of_le hy.le)
  have hsigma := (sigmaIicEquiv (ι := ι)).hasSum_iff.mpr huv
  have hgrouped := hsigma.sigma fun δ ↦
    hasSum_fintype (L := .unconditional _) fun β : Iic δ ↦
      ((∏ i, y i ^ β.1 i) • a β.1) • ((∏ i, y i ^ (δ - β.1) i) • b (δ - β.1))
  convert hgrouped using 1
  ext δ
  rw [Finset.univ_eq_attach, smul_sum, sum_attach (Iic δ) fun β ↦
    ((∏ i, y i ^ β i) • a β) • ((∏ i, y i ^ (δ - β) i) • b (δ - β))]
  refine sum_congr rfl fun β hβ ↦ ?_
  have hcomm : ∀ (r : 𝕜) (u : A) (v : F), u • (r • v) = r • (u • v) := fun r u v ↦ by
    rw [← algebraMap_smul A r v, ← algebraMap_smul A r (u • v), smul_smul, smul_smul,
      Algebra.commutes]
  rw [smul_assoc (∏ i, y i ^ β i), hcomm, smul_smul, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun i _ ↦ ?_
  rw [← pow_add, Pi.sub_apply, Nat.add_sub_of_le (mem_Iic.1 hβ i)]

/-- **The product rule** for multi-index Taylor coefficients of two analytic functions taking values
in a normed `𝕜`-algebra. -/
theorem mvTaylorCoeff_mul [DecidableEq ι] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : (ι → 𝕜) → A} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (fun z ↦ f z * g z) x α =
      ∑ β ∈ Iic α, TauCeti.mvTaylorCoeff f x β * TauCeti.mvTaylorCoeff g x (α - β) :=
  hf.mvTaylorCoeff_smul hg α

end AnalyticAt

namespace ContinuousLinearMap

/-- **Linear change of variables**: if the multi-index Taylor coefficients of `G` at `A x` all
vanish in total degree `k`, then so do those of `G ∘ A` at `x`. -/
theorem mvTaylorCoeff_comp_eq_zero {κ : Type*} [Fintype κ] {G : (ι → 𝕜) → F}
    (A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) {x : κ → 𝕜} (hG : AnalyticAt 𝕜 G (A x)) {k : ℕ}
    (h : ∀ α : ι → ℕ, ∑ i, α i = k → TauCeti.mvTaylorCoeff G (A x) α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → TauCeti.mvTaylorCoeff (G ∘ A) x β = 0 := by
  intro β hβ
  classical
  obtain ⟨p, hp⟩ := hG
  have hpA : HasFPowerSeriesAt (G ∘ A) (p.compContinuousLinearMap A) x :=
    hp.compContinuousLinearMap
  rw [hpA.mvTaylorCoeff_eq]
  refine TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero (fun z : κ → 𝕜 ↦ ?_)
    (mem_piAntidiag.2 ⟨hβ, by simp⟩)
  rw [← FormalMultilinearSeries.apply_eq_sum_mvCoeff]
  simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def]
  rw [FormalMultilinearSeries.apply_eq_sum_mvCoeff]
  refine sum_eq_zero fun α hα ↦ ?_
  rw [← hp.mvTaylorCoeff_eq, h α (mem_piAntidiag.1 hα).1, smul_zero]

end ContinuousLinearMap

namespace AnalyticAt

/-- Permutations `σ` with `v ∘ σ = a` correspond bijectively to families of bijections between
the fibers of `a` and `v`, so there are `∏ i, (α i)!` of them whenever `a` and `v` have the same
fiber counts `α`. -/
private theorem card_perm_comp_eq [DecidableEq ι] {k : ℕ} {α : ι → ℕ}
    {a v : Fin k → ι}
    (ha : ∀ i, Fintype.card {j : Fin k // a j = i} = α i)
    (hv : ∀ i, Fintype.card {j : Fin k // v j = i} = α i) :
    (univ.filter fun σ : Equiv.Perm (Fin k) ↦ v ∘ σ = a).card = ∏ i, (α i).factorial := by
  let e : {σ : Equiv.Perm (Fin k) // v ∘ σ = a} ≃
      (∀ i : ι, {j : Fin k // a j = i} ≃ {j : Fin k // v j = i}) :=
    { toFun := fun ⟨σ, hσ⟩ i ↦
        { toFun := fun ⟨j, hj⟩ ↦ ⟨σ j, by simpa [hj] using congrFun hσ j⟩
          invFun := fun ⟨j, hj⟩ ↦ ⟨σ.symm j, by
            have := congrFun hσ (σ.symm j)
            simpa [hj] using this.symm⟩
          left_inv := fun ⟨j, _⟩ ↦ Subtype.ext (σ.symm_apply_apply j)
          right_inv := fun ⟨j, _⟩ ↦ Subtype.ext (σ.apply_symm_apply j) }
      invFun := fun φ ↦
        ⟨(Equiv.sigmaFiberEquiv a).symm.trans
            ((Equiv.sigmaCongrRight φ).trans (Equiv.sigmaFiberEquiv v)), by
          ext j
          exact (φ (a j) ⟨j, rfl⟩).2⟩
      left_inv := fun ⟨σ, hσ⟩ ↦ by
        ext j
        rfl
      right_inv := fun φ ↦ by
        ext i ⟨j, hj⟩
        subst hj
        rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_pi]
  refine prod_congr rfl fun i _ ↦ ?_
  have heq : Fintype.card {j : Fin k // a j = i} = Fintype.card {j : Fin k // v j = i} :=
    (ha i).trans (hv i).symm
  rw [Fintype.card_equiv (Fintype.equivOfCardEq heq), ha i]

/-- **Agreement with iterated Fréchet derivatives**: for any tuple `v` of standard basis directions
with coordinate counts `α`, `(∏ i, (α i)!) • mvTaylorCoeff f x α` equals `iteratedFDeriv` applied
to `v`. No factorial is inverted, so this holds in arbitrary characteristic. -/
theorem prod_factorial_smul_mvTaylorCoeff [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ)
    (v : Fin (∑ i, α i) → ι)
    (hv : ∀ i, (univ.filter fun j ↦ v j = i).card = α i) :
    (∏ i, (α i).factorial) • TauCeti.mvTaylorCoeff f x α =
      iteratedFDeriv 𝕜 (∑ i, α i) f x (fun j ↦ Pi.single (v j) 1) := by
  obtain ⟨p, r, hp⟩ := hf
  have hv' : ∀ i, Fintype.card {j : Fin (∑ i, α i) // v j = i} = α i := fun i ↦ by
    simpa [Fintype.card_subtype] using hv i
  rw [hp.mvTaylorCoeff_eq, FormalMultilinearSeries.mvCoeff_eq_sum _ rfl,
    hp.iteratedFDeriv_eq_sum_of_completeSpace]
  let S : Finset (Fin (∑ i, α i) → ι) :=
    univ.filter fun a ↦ ∀ i, Fintype.card {j // a j = i} = α i
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin (∑ i, α i)))), v ∘ σ ∈ S := fun σ _ ↦ by
    refine mem_filter.2 ⟨mem_univ _, fun i ↦ ?_⟩
    rw [← hv' i]
    exact Fintype.card_congr (Equiv.subtypeEquiv σ fun _ ↦ Iff.rfl)
  rw [← sum_fiberwise_of_maps_to hmaps, smul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  have ha' : ∀ i, Fintype.card {j : Fin (∑ i, α i) // a j = i} = α i := (mem_filter.1 ha).2
  have hcongr : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a),
      p (∑ i, α i) (fun j ↦ Pi.single (v (σ j)) (1 : 𝕜)) =
      ∑ _σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a),
        p (∑ i, α i) (fun j ↦ Pi.single (a j) (1 : 𝕜)) :=
    sum_congr rfl fun σ hσ ↦ by
      congr 1
      ext j
      rw [← congrFun (mem_filter.1 hσ).2 j]
      rfl
  rw [hcongr, sum_const, card_perm_comp_eq ha' hv']

/-- **One-variable specialization**: for a singleton index type, `k! • mvTaylorCoeff` equals
`iteratedDeriv k`. No factorial is inverted, so this holds in arbitrary characteristic. -/
theorem factorial_smul_mvTaylorCoeff_of_unique [Unique ι] [CompleteSpace F]
    {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    (α default).factorial •
        TauCeti.mvTaylorCoeff (fun z : ι → 𝕜 ↦ f (z default)) (fun _ ↦ x) α =
      iteratedDeriv (α default) f x := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  let proj : (ι → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj (R := 𝕜) (default : ι)
  have hp' : HasFPowerSeriesAt (fun z : ι → 𝕜 ↦ f (z default))
      (p.compContinuousLinearMap proj) (fun _ ↦ x) :=
    hp.hasFPowerSeriesAt.compContinuousLinearMap (u := proj) (x := fun _ ↦ x)
  rw [hp'.mvTaylorCoeff_eq, FormalMultilinearSeries.mvCoeff_eq_sum _ (Fintype.sum_unique α)]
  have hfilt : univ.filter (fun a : Fin (α default) → ι ↦
      ∀ i, Fintype.card {j // a j = i} = α i) = {fun _ ↦ default} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _
      ext j
      exact Unique.eq_default _
    · rintro rfl i
      rw [Unique.eq_default i]
      simp
  rw [hfilt, sum_singleton]
  have hterm : (p.compContinuousLinearMap proj) (α default) (fun _ ↦ Pi.single default (1 : 𝕜)) =
      p (α default) (fun _ ↦ 1) := by
    simp [FormalMultilinearSeries.compContinuousLinearMap_apply, proj, Function.comp_def]
  rw [hterm, hp.factorial_smul (1 : 𝕜) (α default), iteratedDeriv_eq_iteratedFDeriv]

end AnalyticAt
