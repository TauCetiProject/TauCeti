/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Pi.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Algebra.MvPolynomial.Funext

/-!
# Multi-index Taylor coefficients of functions at a point

Given a function `f : (ι → 𝕜) → F` on a finite product of copies of a nontrivially normed field
`𝕜` and a point `x : ι → 𝕜`, this file defines the multi-index Taylor coefficient
`TauCeti.mvTaylorCoeff f x α : F` for `α : ι → ℕ` as the multi-index coefficient `p.mvCoeff α`
of a formal multilinear series `p` representing `f` at `x`, and `0` if `f` is not analytic at `x`.

By the identity theorem (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`), `mvTaylorCoeff f x α`
depends only on the germ of `f` at `x` and is independent of the chosen series `p`. Because no
factorial is inverted in the definition, it works over fields of arbitrary characteristic (including
positive characteristic, where `(α i)!` may vanish), and agrees with the iterated Fréchet
derivative after multiplying by `∏ i, (α i)!`.

## Main definitions and results

* `TauCeti.mvTaylorCoeff`: the multi-index Taylor coefficient of `f` at `x`, equal to `0` when
  `f` is not analytic at `x`.
* `HasFPowerSeriesAt.mvTaylorCoeff_eq` and `HasFPowerSeriesOnBall.mvTaylorCoeff_eq`: independence
  of the chosen formal multilinear series.
* `AnalyticAt.mvTaylorCoeff_zero`: the coefficient of order `0` is `f x` when `f` is analytic at
  `x`.
* `Filter.EventuallyEq.mvTaylorCoeff_eq` and `TauCeti.mvTaylorCoeff_comp_add_right`: locality and
  translation invariance (with no analyticity assumption).
* `AnalyticAt.mvTaylorCoeff_add`, `AnalyticAt.mvTaylorCoeff_sub`, `TauCeti.mvTaylorCoeff_sum`,
  `TauCeti.mvTaylorCoeff_neg`, and `TauCeti.mvTaylorCoeff_const_smul`: linearity in the function.
* `AnalyticAt.exists_hasSum_mvTaylorCoeff` and `TauCeti.mvTaylorCoeff_eq_of_hasSum`: an analytic
  function is the sum of its normally convergent Taylor series near `x`, and conversely any
  convergent multi-index expansion near `x` has `mvTaylorCoeff f x` as its coefficients.
* `AnalyticAt.mvTaylorCoeff_smul` and `AnalyticAt.mvTaylorCoeff_mul`: the Cauchy product rule over
  `Finset.Iic α`.
* `AnalyticAt.prod_factorial_smul_mvTaylorCoeff` and
  `AnalyticAt.factorial_smul_mvTaylorCoeff_of_unique`: `(∏ i, (α i)!) • mvTaylorCoeff f x α` equals
  the iterated derivative at `x`.
* `ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`: vanishing of all Taylor coefficients of total
  degree `k` is preserved under precomposition by a continuous linear map.

## References

* Michel Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Chapter 4 (whose normalized differential
  operator `D^σ f(ξ)` is `(∏ i, (σ i)!) • mvTaylorCoeff f ξ σ`).
* Multi-index Taylor coefficients at a point are also formalized in Michail Karatarakis's
  formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
  `Mathlib/NumberTheory/Transcendental/Baker/TaylorCoeff.lean`, Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped ENNReal NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

open Classical in
/-- The **multi-index Taylor coefficient** of `f : (ι → 𝕜) → F` at `x : ι → 𝕜` and `α : ι → ℕ`:
the coefficient of `∏ i, (z i - x i) ^ α i` in the power series expansion of `f` about `x`, and `0`
if `f` is not analytic at `x`. -/
noncomputable irreducible_def mvTaylorCoeff (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) : F :=
  if h : AnalyticAt 𝕜 f x then h.choose.mvCoeff α else 0

/-- Outside the analytic locus of `f`, every multi-index Taylor coefficient is `0`. -/
theorem mvTaylorCoeff_of_not_analyticAt {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : ¬ AnalyticAt 𝕜 f x)
    (α : ι → ℕ) : mvTaylorCoeff f x α = 0 := by
  rw [mvTaylorCoeff_def, dite_eq_right hf]

end TauCeti

open TauCeti

/-- **Independence of the chosen series**: if `f` has the formal multilinear series `p` at `x`,
then `mvTaylorCoeff f x α = p.mvCoeff α`. -/
theorem HasFPowerSeriesAt.mvTaylorCoeff_eq {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} (hp : HasFPowerSeriesAt f p x)
    (α : ι → ℕ) : mvTaylorCoeff f x α = p.mvCoeff α := by
  have h : AnalyticAt 𝕜 f x := ⟨p, hp⟩
  rw [mvTaylorCoeff_def, dite_eq_left h]
  exact h.choose_spec.mvCoeff_eq_of_eventuallyEq hp .rfl α

/-- If `f` has the formal multilinear series `p` on a ball about `x`, then
`mvTaylorCoeff f x α = p.mvCoeff α`. -/
theorem HasFPowerSeriesOnBall.mvTaylorCoeff_eq {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (α : ι → ℕ) : mvTaylorCoeff f x α = p.mvCoeff α :=
  hp.hasFPowerSeriesAt.mvTaylorCoeff_eq α

/-- For `f` analytic at `x`, the Taylor coefficient of order `0` at `x` is `f x`. -/
theorem AnalyticAt.mvTaylorCoeff_zero {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    mvTaylorCoeff f x 0 = f x := by
  rcases hf with ⟨p, hp⟩
  rw [hp.mvTaylorCoeff_eq, p.mvCoeff_zero_eq_apply 0, hp.coeff_zero]

/-- **Locality**: functions that agree on a neighbourhood of `x` have the same Taylor coefficients
at `x`. -/
theorem Filter.EventuallyEq.mvTaylorCoeff_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (h : f =ᶠ[𝓝 x] g)
    (α : ι → ℕ) : mvTaylorCoeff f x α = mvTaylorCoeff g x α := by
  by_cases hf : AnalyticAt 𝕜 f x
  · rcases hf with ⟨p, hp⟩
    rw [hp.mvTaylorCoeff_eq, (hp.congr h).mvTaylorCoeff_eq]
  · have hg : ¬ AnalyticAt 𝕜 g x := fun hg ↦ hf (hg.congr h.symm)
    rw [mvTaylorCoeff_of_not_analyticAt hf, mvTaylorCoeff_of_not_analyticAt hg]

namespace TauCeti

@[simp]
theorem mvTaylorCoeff_const (c : F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun _ : ι → 𝕜 ↦ c) x α = if α = 0 then c else 0 := by
  rw [(hasFPowerSeriesOnBall_const (c := c) (e := x)).hasFPowerSeriesAt.mvTaylorCoeff_eq]
  split_ifs with hα
  · subst hα
    rw [FormalMultilinearSeries.mvCoeff_zero_eq_apply _ 0]
    simp
  · have hk : ∑ i, α i ≠ 0 := by simpa [sum_eq_zero_iff, funext_iff] using hα
    rw [FormalMultilinearSeries.mvCoeff_congr (q := 0)
      (constFormalMultilinearSeries_apply_of_ne_zero hk)]
    simp

@[simp]
theorem mvTaylorCoeff_zero (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (0 : (ι → 𝕜) → F) x α = 0 := by
  simp [Pi.zero_def]

/-- **Scalar multiples**: `mvTaylorCoeff` commutes with scalar multiplication by constants in `𝕜`,
with no analyticity assumption. -/
@[simp]
theorem mvTaylorCoeff_const_smul (c : 𝕜) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (c • f) x α = c • mvTaylorCoeff f x α := by
  by_cases hc : c = 0
  · subst hc
    simp
  · by_cases hf : AnalyticAt 𝕜 f x
    · rcases hf with ⟨p, hp⟩
      rw [hp.mvTaylorCoeff_eq, (hp.const_smul (c := c)).mvTaylorCoeff_eq,
        FormalMultilinearSeries.mvCoeff_smul]
    · have hcf : ¬ AnalyticAt 𝕜 (c • f) x := fun h ↦
        hf <| by simpa [Pi.smul_def, inv_smul_smul₀ hc] using h.const_smul (c := c⁻¹)
      rw [mvTaylorCoeff_of_not_analyticAt hf, mvTaylorCoeff_of_not_analyticAt hcf, smul_zero]

@[simp]
theorem mvTaylorCoeff_fun_const_smul (c : 𝕜) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ c • f z) x α = c • mvTaylorCoeff f x α :=
  mvTaylorCoeff_const_smul c f x α

@[simp]
theorem mvTaylorCoeff_const_mul (c : 𝕜) (f : (ι → 𝕜) → 𝕜) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ c * f z) x α = c * mvTaylorCoeff f x α :=
  mvTaylorCoeff_fun_const_smul c f x α

@[to_fun (attr := simp) mvTaylorCoeff_fun_neg]
theorem mvTaylorCoeff_neg (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (-f) x α = -mvTaylorCoeff f x α := by
  simpa [neg_one_smul] using mvTaylorCoeff_const_smul (-1 : 𝕜) f x α

/-- **Translation**: shifting the argument by `y` shifts the expansion point by `y`. -/
@[simp]
theorem mvTaylorCoeff_comp_add_right (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (z + y)) x α = mvTaylorCoeff f (x + y) α := by
  have hshift {g : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {u v : ι → 𝕜}
      (hp : HasFPowerSeriesAt g p (u + v)) :
      HasFPowerSeriesAt (fun z ↦ g (z + v)) p u := by
    rcases hp with ⟨r, hr⟩
    exact ⟨r, hr.r_le, hr.r_pos, fun {w} hw ↦ by simpa [add_right_comm] using hr.hasSum hw⟩
  by_cases hf : AnalyticAt 𝕜 f (x + y)
  · rcases hf with ⟨p, hp⟩
    rw [hp.mvTaylorCoeff_eq, (hshift hp).mvTaylorCoeff_eq]
  · have hfy : ¬ AnalyticAt 𝕜 (fun z ↦ f (z + y)) x := fun ⟨p, hp⟩ ↦
      hf ⟨p, by
        have hp' := hshift (u := x + y) (v := -y) (by simpa using hp)
        simpa using hp'⟩
    rw [mvTaylorCoeff_of_not_analyticAt hf, mvTaylorCoeff_of_not_analyticAt hfy]

@[simp]
theorem mvTaylorCoeff_comp_add_left (f : (ι → 𝕜) → F) (y x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (y + z)) x α = mvTaylorCoeff f (y + x) α := by
  simp_rw [add_comm y]
  exact mvTaylorCoeff_comp_add_right f x y α

end TauCeti

/-- **Additivity**: for `f` and `g` analytic at `x`, the Taylor coefficients of `f + g` at `x` are
the sums of those of `f` and `g`. -/
@[to_fun AnalyticAt.mvTaylorCoeff_fun_add]
theorem AnalyticAt.mvTaylorCoeff_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f + g) x α = mvTaylorCoeff f x α + mvTaylorCoeff g x α := by
  rcases hf with ⟨p, hp⟩
  rcases hg with ⟨q, hq⟩
  rw [hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq, (hp.add hq).mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_add]

/-- For `f` and `g` analytic at `x`, the Taylor coefficients of `f - g` at `x` are the differences
of those of `f` and `g`. -/
@[to_fun AnalyticAt.mvTaylorCoeff_fun_sub]
theorem AnalyticAt.mvTaylorCoeff_sub {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f - g) x α = mvTaylorCoeff f x α - mvTaylorCoeff g x α := by
  rw [sub_eq_add_neg, hf.mvTaylorCoeff_add hg.neg, mvTaylorCoeff_neg, ← sub_eq_add_neg]

namespace TauCeti

/-- The Taylor coefficient of a finite sum of functions analytic at `x` is the sum of their Taylor
coefficients. -/
@[to_fun mvTaylorCoeff_fun_sum]
theorem mvTaylorCoeff_sum {κ : Type*} {s : Finset κ} {f : κ → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ∀ k ∈ s, AnalyticAt 𝕜 (f k) x) (α : ι → ℕ) :
    mvTaylorCoeff (∑ k ∈ s, f k) x α = ∑ k ∈ s, mvTaylorCoeff (f k) x α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha_an : AnalyticAt 𝕜 (f a) x := hf a (mem_insert_self a s)
    have hs_an : AnalyticAt 𝕜 (∑ k ∈ s, f k) x :=
      Finset.analyticAt_sum s fun k hk ↦ hf k (mem_insert_of_mem hk)
    rw [sum_insert ha, sum_insert ha, ha_an.mvTaylorCoeff_add hs_an,
      ih fun k hk ↦ hf k (mem_insert_of_mem hk)]

end TauCeti

namespace ContinuousLinearMap

/-- Postcomposing an analytic function with a continuous linear map applies the map to each Taylor
coefficient. -/
theorem mvTaylorCoeff_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] (L : F →L[𝕜] G)
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    mvTaylorCoeff (L ∘ f) x α = L (mvTaylorCoeff f x α) := by
  rcases hf with ⟨p, r, hp⟩
  rw [hp.mvTaylorCoeff_eq, (L.comp_hasFPowerSeriesOnBall hp).mvTaylorCoeff_eq,
    L.mvCoeff_compFormalMultilinearSeries]

/-- **A linear change of variables preserves vanishing in each total degree**: if every Taylor
coefficient of `G` at `A x` of total degree `k` vanishes, then so does every Taylor coefficient of
`G ∘ A` at `x` of total degree `k`. -/
theorem mvTaylorCoeff_comp_eq_zero {κ : Type*} [Fintype κ] {G : (ι → 𝕜) → F}
    (A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) {x : κ → 𝕜} (hG : AnalyticAt 𝕜 G (A x)) {k : ℕ}
    (h : ∀ α : ι → ℕ, ∑ i, α i = k → mvTaylorCoeff G (A x) α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → mvTaylorCoeff (G ∘ A) x β = 0 := by
  classical
  rcases hG with ⟨p, hp⟩
  intro β hβ
  have hp0 (α : ι → ℕ) (hα : α ∈ univ.piAntidiag k) : p.mvCoeff α = 0 := by
    rw [← hp.mvTaylorCoeff_eq, h α (mem_piAntidiag.1 hα).1]
  rw [(hp.compContinuousLinearMap (u := A)).mvTaylorCoeff_eq]
  refine TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero (K := 𝕜) (V := F)
    (s := univ.piAntidiag k) (c := (p.compContinuousLinearMap A).mvCoeff)
    (fun w ↦ ?_) (mem_piAntidiag.2 ⟨hβ, by simp⟩)
  rw [← FormalMultilinearSeries.apply_eq_sum_mvCoeff,
    FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def,
    FormalMultilinearSeries.apply_eq_sum_mvCoeff]
  exact sum_eq_zero fun α hα ↦ by rw [hp0 α hα, smul_zero]

end ContinuousLinearMap

/-- **The local multi-index expansion of an analytic function**: if `f` is analytic at `x`, then
there is a positive radius `ρ` on which the Taylor coefficients are normally summable and
`(∏ i, y i ^ α i) • mvTaylorCoeff f x α` sums to `f (x + y)` whenever `‖y‖ < ρ`. -/
theorem AnalyticAt.exists_hasSum_mvTaylorCoeff {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      Summable (fun α : ι → ℕ ↦ ‖mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ i, α i)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ →
        HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • mvTaylorCoeff f x α) (f (x + y)) := by
  rcases hf with ⟨p, r, hp⟩
  obtain ⟨r₀, hr₀_pos, hr₀_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hr₀_pos' : 0 < r₀ := ENNReal.coe_pos.1 hr₀_pos
  let N : ℝ≥0 := max (Fintype.card ι) 1
  have hN_pos : 0 < N := lt_max_of_lt_right zero_lt_one
  have hN_ge_one : (1 : ℝ≥0) ≤ N := le_max_right _ _
  let ρ : ℝ≥0 := r₀ / N
  have hρ_pos : 0 < ρ := div_pos hr₀_pos' hN_pos
  have hρ_le : ρ ≤ r₀ := div_le_self zero_le hN_ge_one
  have hρ_lt_r : (ρ : ℝ≥0∞) < r := (ENNReal.coe_le_coe.2 hρ_le).trans_lt hr₀_lt
  have hr₀_sum : Summable fun k ↦ ‖p k‖ * (r₀ : ℝ) ^ k :=
    p.summable_norm_mul_pow (hr₀_lt.trans_le hp.r_le)
  have hcard_sum : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k := by
    refine hr₀_sum.of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    have hcard_le : (Fintype.card ι : ℝ) * (ρ : ℝ) ≤ (r₀ : ℝ) := by
      have hN : (Fintype.card ι : ℝ≥0) ≤ N := le_max_left _ _
      have hle : (Fintype.card ι : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hρ : (ρ : ℝ) = (r₀ : ℝ) / (N : ℝ) := NNReal.coe_div r₀ N
      calc (Fintype.card ι : ℝ) * (ρ : ℝ)
          ≤ (N : ℝ) * ((r₀ : ℝ) / (N : ℝ)) := by rw [hρ]; gcongr
        _ = (r₀ : ℝ) := mul_div_cancel₀ _ (by positivity)
    calc (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k
        = ‖p k‖ * ((Fintype.card ι : ℝ) * (ρ : ℝ)) ^ k := by ring
      _ ≤ ‖p k‖ * (r₀ : ℝ) ^ k := by gcongr
  simp_rw [hp.mvTaylorCoeff_eq]
  refine ⟨ρ, hρ_pos, p.summable_norm_mvCoeff_mul_pow hcard_sum, fun y hy ↦ ?_⟩
  have hy_eball : y ∈ Metric.eball (0 : ι → 𝕜) r := by
    have hnn : (‖y‖₊ : ℝ≥0∞) < ρ := by exact_mod_cast hy
    simpa [Metric.mem_eball, eNorm_eq_nnNorm] using hnn.trans hρ_lt_r
  refine hp.hasSum_mvCoeff hy_eball <|
    hcard_sum.of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
  have := hy.le
  gcongr

namespace TauCeti

/-- **Coefficients from an expansion**: if `(∏ i, y i ^ α i) • c α` sums to `f (x + y)` for all `y`
in a neighbourhood of `0`, then `mvTaylorCoeff f x α = c α` for every `α`. -/
theorem mvTaylorCoeff_eq_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜} {c : (ι → ℕ) → F}
    (h : ∀ᶠ y in 𝓝 (0 : ι → 𝕜), HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y)))
    (α : ι → ℕ) : mvTaylorCoeff f x α = c α := by
  obtain ⟨p, hp, hcoeff⟩ := exists_hasFPowerSeriesAt_of_eventually_hasSum c h
  rw [hp.mvTaylorCoeff_eq, hcoeff]

/-- At the origin, the monomial `(∏ i, z i ^ τ i) • c` has Taylor coefficient `c` at `τ` and `0`
at every other multi-index. -/
@[simp]
theorem mvTaylorCoeff_prod_pow_smul_zero (τ : ι → ℕ) (c : F) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ (∏ i, z i ^ τ i) • c) 0 α = if α = τ then c else 0 := by
  apply mvTaylorCoeff_eq_of_hasSum
  refine Eventually.of_forall fun y ↦ ?_
  have h0 : (∏ i, y i ^ τ i) • c = (∏ i, y i ^ τ i) • (if τ = τ then c else 0) := by simp
  rw [zero_add, h0]
  exact hasSum_single τ fun β hβ ↦ by simp [hβ]

/-- At the origin, the scalar monomial `∏ i, z i ^ τ i` has Taylor coefficient `1` at `τ` and `0`
at every other multi-index. -/
@[simp]
theorem mvTaylorCoeff_prod_pow_zero (τ : ι → ℕ) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ ∏ i, z i ^ τ i) 0 α = if α = τ then 1 else 0 := by
  simpa using mvTaylorCoeff_prod_pow_smul_zero (𝕜 := 𝕜) τ (1 : 𝕜) α

/-- Equivalence `(Σ α : ι → ℕ, Finset.Iic α) ≃ (ι → ℕ) × (ι → ℕ)` sending `⟨α, β⟩` to
`(β, α - β)`, used to re-index the Cauchy product of two multi-index series. -/
private def sigmaIicEquivProd [DecidableEq ι] :
    (Σ α : ι → ℕ, Finset.Iic α) ≃ (ι → ℕ) × (ι → ℕ) where
  toFun p := (p.2.1, p.1 - p.2.1)
  invFun q := ⟨q.1 + q.2, q.1, mem_Iic.2 le_self_add⟩
  left_inv := fun ⟨α, β, hβ⟩ ↦
    Sigma.subtype_ext (funext fun i ↦ add_tsub_cancel_of_le (mem_Iic.1 hβ i)) rfl
  right_inv := fun ⟨β, γ⟩ ↦ by ext <;> simp

private theorem mvTaylorCoeff_smul_of_completeSpace [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → 𝕜} {g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f • g) x α =
      ∑ β ∈ Finset.Iic α, mvTaylorCoeff f x β • mvTaylorCoeff g x (α - β) := by
  obtain ⟨ρ₁, hρ₁, hsum₁, h₁⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨ρ₂, hρ₂, hsum₂, h₂⟩ := hg.exists_hasSum_mvTaylorCoeff
  apply mvTaylorCoeff_eq_of_hasSum
  refine Metric.eventually_nhds_iff.2 ⟨min (ρ₁ : ℝ) ρ₂, lt_min hρ₁ hρ₂, fun y hy ↦ ?_⟩
  rw [dist_zero_right] at hy
  have hy₁ : ‖y‖ < ρ₁ := hy.trans_le (min_le_left _ _)
  have hy₂ : ‖y‖ < ρ₂ := hy.trans_le (min_le_right _ _)
  have hn₁ : Summable fun β : ι → ℕ ↦ ‖(∏ i, y i ^ β i) * mvTaylorCoeff f x β‖ :=
    summable_norm_prod_pow_smul hsum₁ fun i ↦ (norm_le_pi_norm y i).trans hy₁.le
  have hn₂ : Summable fun γ : ι → ℕ ↦ ‖(∏ i, y i ^ γ i) • mvTaylorCoeff g x γ‖ :=
    summable_norm_prod_pow_smul hsum₂ fun i ↦ (norm_le_pi_norm y i).trans hy₂.le
  have hprod_sum : Summable fun p : (ι → ℕ) × (ι → ℕ) ↦
      ((∏ i, y i ^ p.1 i) * mvTaylorCoeff f x p.1) •
        ((∏ i, y i ^ p.2 i) • mvTaylorCoeff g x p.2) :=
    Summable.of_norm <| (hn₁.mul_of_nonneg hn₂ (fun _ ↦ norm_nonneg _)
      fun _ ↦ norm_nonneg _).congr fun _ ↦ (norm_smul _ _).symm
  have h₁' : HasSum (fun β : ι → ℕ ↦ (∏ i, y i ^ β i) * mvTaylorCoeff f x β) (f (x + y)) := by
    simpa only [smul_eq_mul] using h₁ y hy₁
  have hprod := h₁'.smul (h₂ y hy₂) hprod_sum
  have hsig := (sigmaIicEquivProd (ι := ι)).hasSum_iff.2 hprod
  refine hsig.sigma fun γ ↦ ?_
  have hterm (β : Finset.Iic γ) :
      ((∏ i, y i ^ β.1 i) * mvTaylorCoeff f x β.1) •
        ((∏ i, y i ^ (γ - β.1) i) • mvTaylorCoeff g x (γ - β.1)) =
      (∏ i, y i ^ γ i) • (mvTaylorCoeff f x β.1 • mvTaylorCoeff g x (γ - β.1)) := by
    have hpow : (∏ i, y i ^ β.1 i) * ∏ i, y i ^ (γ - β.1) i = ∏ i, y i ^ γ i := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ ↦ ?_
      rw [← pow_add, Pi.sub_apply, add_tsub_cancel_of_le (mem_Iic.1 β.2 i)]
    rw [smul_smul, smul_smul, ← hpow]
    congr 1
    ring
  simp_rw [sigmaIicEquivProd, Equiv.coe_fn_mk, Function.comp_def, hterm]
  rw [smul_sum, ← sum_attach (Iic γ)
    (fun β ↦ (∏ i, y i ^ γ i) • (mvTaylorCoeff f x β • mvTaylorCoeff g x (γ - β))),
    ← univ_eq_attach]
  exact hasSum_fintype _

end TauCeti

/-- **The product rule** for a scalar-valued analytic function times a vector-valued one: the
Taylor coefficient at `α` is the Cauchy sum over `β ∈ Finset.Iic α`. No completeness assumption on
`F` is required. -/
@[to_fun AnalyticAt.mvTaylorCoeff_fun_smul]
theorem AnalyticAt.mvTaylorCoeff_smul [DecidableEq ι] {f : (ι → 𝕜) → 𝕜} {g : (ι → 𝕜) → F}
    {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f • g) x α =
      ∑ β ∈ Finset.Iic α, mvTaylorCoeff f x β • mvTaylorCoeff g x (α - β) := by
  let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have he_fg : e ∘ (f • g) = f • (e ∘ g) := by
    ext z
    exact map_smul e (f z) (g z)
  have hcomp := e.mvTaylorCoeff_comp (hf.smul hg) α
  rw [he_fg, TauCeti.mvTaylorCoeff_smul_of_completeSpace hf ((e.analyticAt _).comp hg) α] at hcomp
  simp_rw [e.mvTaylorCoeff_comp hg, ← map_smul, ← map_sum] at hcomp
  exact UniformSpace.Completion.coe_inj.1 hcomp.symm

/-- **The product rule** for two scalar-valued analytic functions. -/
@[to_fun AnalyticAt.mvTaylorCoeff_fun_mul]
theorem AnalyticAt.mvTaylorCoeff_mul [DecidableEq ι] {f g : (ι → 𝕜) → 𝕜} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f * g) x α =
      ∑ β ∈ Finset.Iic α, mvTaylorCoeff f x β * mvTaylorCoeff g x (α - β) := by
  simpa only [Pi.mul_def, Pi.smul_def, smul_eq_mul] using hf.mvTaylorCoeff_smul hg α

/-- **Agreement with iterated derivatives**: for `f` analytic at `x` with values in a complete
space, `(∏ i, (α i)!) • mvTaylorCoeff f x α` equals `iteratedFDeriv 𝕜 (∑ i, α i) f x` applied to
any tuple of standard basis vectors with coordinate counts `α`. -/
theorem AnalyticAt.prod_factorial_smul_mvTaylorCoeff [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ)
    (v : Fin (∑ i, α i) → ι) (hv : ∀ i, (Finset.univ.filter fun j ↦ v j = i).card = α i) :
    (∏ i, (α i).factorial) • mvTaylorCoeff f x α =
      iteratedFDeriv 𝕜 (∑ i, α i) f x (fun j ↦ Pi.single (v j) 1) := by
  rcases hf with ⟨p, r, hp⟩
  rw [hp.mvTaylorCoeff_eq, p.prod_factorial_smul_mvCoeff α v hv,
    hp.iteratedFDeriv_eq_sum_of_completeSpace]

/-- **Agreement with one-variable iterated derivatives**: over a singleton index type,
`(α default)! • mvTaylorCoeff` equals `iteratedDeriv (α default) f x`. Because no factorial is
inverted, this holds in every characteristic. -/
theorem AnalyticAt.factorial_smul_mvTaylorCoeff_of_unique [Unique ι] [CompleteSpace F]
    {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    (α default).factorial • mvTaylorCoeff (fun z : ι → 𝕜 ↦ f (z default)) (fun _ ↦ x) α =
      iteratedDeriv (α default) f x := by
  rcases hf with ⟨p, r, hp⟩
  let L : (ι → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj default
  have hL : HasFPowerSeriesAt (fun z : ι → 𝕜 ↦ f (z default)) (p.compContinuousLinearMap L)
      (fun _ ↦ x) :=
    hp.hasFPowerSeriesAt.compContinuousLinearMap (u := L)
  rw [hL.mvTaylorCoeff_eq, FormalMultilinearSeries.mvCoeff_eq_apply_of_unique,
    FormalMultilinearSeries.compContinuousLinearMap_apply, iteratedDeriv_eq_iteratedFDeriv]
  exact hp.factorial_smul (y := 1) (α default)
