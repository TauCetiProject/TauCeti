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
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.GroupTheory.Perm.DomMulAct
import TauCeti.Analysis.Normed.Module.InfiniteSum

/-!
# Multi-index Taylor coefficients at a point

For a function `f : (ι → 𝕜) → F` on a finite product over a nontrivially normed field `𝕜`, the
**multi-index Taylor coefficient** `TauCeti.mvTaylorCoeff f x α` at `x : ι → 𝕜` and `α : ι → ℕ` is
the multi-index coefficient `p.mvCoeff α` of any formal multilinear series `p` representing `f`
near `x`, and `0` when `f` is not analytic at `x`. By the identity theorem in coefficient form
(`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`), this does not depend on the choice of `p`.

No factorial is inverted in the definition, so the calculus of `mvTaylorCoeff` holds in arbitrary
characteristic: the product of factorials `∏ i, (α i)!` multiplies `mvTaylorCoeff f x α` when
comparing with the iterated Fréchet derivative `iteratedFDeriv 𝕜 (∑ i, α i) f x`. Whereas Mathlib's
`ftaylorSeries` records iterated multilinear derivatives and `TauCeti.taylorSeries` constructs the
one-variable formal power series via divided differences, `TauCeti.mvTaylorCoeff` extracts the
individual coefficients indexed by `ι → ℕ` in several variables.

## Main definitions and results

* `TauCeti.mvTaylorCoeff`: the multi-index Taylor coefficient of `f` at `x` of index `α`.
* `HasFPowerSeriesAt.mvTaylorCoeff_eq`: independence of the chosen formal multilinear series.
* `AnalyticAt.mvTaylorCoeff_add`, `TauCeti.mvTaylorCoeff_const_smul`,
  `TauCeti.mvTaylorCoeff_comp_add_right`, `Filter.EventuallyEq.mvTaylorCoeff_eq`: linearity,
  translation invariance, and locality of Taylor coefficients.
* `AnalyticAt.exists_hasSum_mvTaylorCoeff` and `TauCeti.mvTaylorCoeff_eq_of_hasSum`: local
  normally convergent multi-index expansion of an analytic function, and uniqueness of its
  coefficients.
* `AnalyticAt.mvTaylorCoeff_smul` and `AnalyticAt.mvTaylorCoeff_mul`: Cauchy product rule over
  `Finset.Iic α` for functions valued in a normed `𝕜`-algebra and a module over it.
* `ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`: for `G` analytic at `A x`, vanishing of all
  Taylor coefficients of `G` at `A x` in a fixed total degree is preserved under precomposition by
  `A`.
* `AnalyticAt.prod_factorial_smul_mvTaylorCoeff` and
  `AnalyticAt.factorial_smul_mvTaylorCoeff_of_unique`: comparison with `iteratedFDeriv` and, in
  one variable, `iteratedDeriv`.

## References

Multi-index Taylor coefficients at a point are also formalized in Michail Karatarakis's
formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
`Mathlib/NumberTheory/Transcendental/Baker/TaylorCoeff.lean`, Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped NNReal ENNReal Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

open Classical in
/-- The **multi-index Taylor coefficient** of `f : (ι → 𝕜) → F` at `x : ι → 𝕜` of index
`α : ι → ℕ`: the coefficient of `∏ i, (z i - x i) ^ α i` in the power series expansion of `f`
about `x`, and `0` when `f` is not analytic at `x`. -/
noncomputable def mvTaylorCoeff (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) : F :=
  if h : AnalyticAt 𝕜 f x then h.choose.mvCoeff α else 0

theorem mvTaylorCoeff_of_not_analyticAt {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ¬AnalyticAt 𝕜 f x) (α : ι → ℕ) : mvTaylorCoeff f x α = 0 := by
  simp [mvTaylorCoeff, hf]

end TauCeti

/-- **Independence of the chosen power series**: if `f` has the formal multilinear series `p` at
`x`, then its Taylor coefficients at `x` are the multi-index coefficients of `p`. -/
theorem HasFPowerSeriesAt.mvTaylorCoeff_eq {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} (hp : HasFPowerSeriesAt f p x)
    (α : ι → ℕ) : TauCeti.mvTaylorCoeff f x α = p.mvCoeff α := by
  have hf := hp.analyticAt
  simp only [TauCeti.mvTaylorCoeff, hf, ↓reduceDIte]
  exact hf.choose_spec.mvCoeff_eq_of_eventuallyEq hp EventuallyEq.rfl α

/-- **Locality**: functions that agree on a neighborhood of `x` have the same Taylor coefficients
at `x`, whether or not they are analytic at `x`. -/
theorem Filter.EventuallyEq.mvTaylorCoeff_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (h : f =ᶠ[𝓝 x] g) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff f x α = TauCeti.mvTaylorCoeff g x α := by
  by_cases hf : AnalyticAt 𝕜 f x
  · obtain ⟨p, hp⟩ := hf
    rw [hp.mvTaylorCoeff_eq, (hp.congr h).mvTaylorCoeff_eq]
  · have hg : ¬AnalyticAt 𝕜 g x := fun ⟨q, hq⟩ ↦ hf ⟨q, hq.congr h.symm⟩
    rw [TauCeti.mvTaylorCoeff_of_not_analyticAt hf, TauCeti.mvTaylorCoeff_of_not_analyticAt hg]

namespace AnalyticAt

/-- For `f` analytic at `x`, the Taylor coefficient of order `0` is `f x`. -/
theorem mvTaylorCoeff_zero {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    TauCeti.mvTaylorCoeff f x 0 = f x := by
  obtain ⟨p, hp⟩ := hf
  rw [hp.mvTaylorCoeff_eq, p.mvCoeff_zero_eq_apply 0, hp.coeff_zero 0]

@[to_fun mvTaylorCoeff_fun_add]
theorem mvTaylorCoeff_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (f + g) x α =
      TauCeti.mvTaylorCoeff f x α + TauCeti.mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.add hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_add]

@[to_fun mvTaylorCoeff_fun_sub]
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

open scoped Classical in
/-- The Taylor coefficients of a constant function vanish away from `0` and equal the constant at
`0`. -/
theorem mvTaylorCoeff_const (c : F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun _ ↦ c) x α = if α = 0 then c else 0 := by
  rw [(hasFPowerSeriesAt_const (𝕜 := 𝕜) (c := c) (e := x)).mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_constFormalMultilinearSeries]

@[simp]
theorem mvTaylorCoeff_const_zero (c : F) (x : ι → 𝕜) :
    mvTaylorCoeff (fun _ ↦ c) x 0 = c := by
  simp [mvTaylorCoeff_const]

theorem mvTaylorCoeff_const_of_ne_zero (c : F) (x : ι → 𝕜) {α : ι → ℕ} (hα : α ≠ 0) :
    mvTaylorCoeff (fun _ ↦ c) x α = 0 := by
  simp [mvTaylorCoeff_const, hα]

@[to_fun (attr := simp) mvTaylorCoeff_fun_zero]
theorem mvTaylorCoeff_zero (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (0 : (ι → 𝕜) → F) x α = 0 := by
  rw [Pi.zero_def]
  simp [mvTaylorCoeff_const]

/-- **Constant multiples**: multiplying a function by a scalar multiplies every Taylor coefficient
by that scalar, with no analyticity assumption. -/
@[to_fun (attr := simp) mvTaylorCoeff_fun_const_smul]
theorem mvTaylorCoeff_const_smul (c : 𝕜) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (c • f) x α = c • mvTaylorCoeff f x α := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases hf : AnalyticAt 𝕜 f x
    · obtain ⟨p, hp⟩ := hf
      rw [(hp.const_smul (c := c)).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq,
        FormalMultilinearSeries.mvCoeff_smul]
    · have hcf : ¬AnalyticAt 𝕜 (c • f) x := fun ⟨q, hq⟩ ↦
        hf ⟨c⁻¹ • q, by simpa [inv_smul_smul₀ hc] using hq.const_smul (c := c⁻¹)⟩
      rw [mvTaylorCoeff_of_not_analyticAt hcf, mvTaylorCoeff_of_not_analyticAt hf, smul_zero]

@[to_fun (attr := simp) mvTaylorCoeff_fun_neg]
theorem mvTaylorCoeff_neg (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (-f) x α = -mvTaylorCoeff f x α := by
  rw [← neg_one_smul 𝕜 f, mvTaylorCoeff_const_smul, neg_one_smul]

@[to_fun mvTaylorCoeff_fun_sum]
theorem mvTaylorCoeff_sum {κ : Type*} (s : Finset κ) {f : κ → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ∀ j ∈ s, AnalyticAt 𝕜 (f j) x) (α : ι → ℕ) :
    mvTaylorCoeff (∑ j ∈ s, f j) x α = ∑ j ∈ s, mvTaylorCoeff (f j) x α := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    have hsum : AnalyticAt 𝕜 (∑ l ∈ s, f l) x :=
      s.analyticAt_sum fun l hl ↦ hf l (mem_insert_of_mem hl)
    rw [sum_insert hj, sum_insert hj,
      (hf j (mem_insert_self j s)).mvTaylorCoeff_add hsum,
      ih fun l hl ↦ hf l (mem_insert_of_mem hl)]

/-- **Translation invariance**: shifting the argument by `y` shifts the expansion point by `y`,
with no analyticity assumption. -/
@[simp]
theorem mvTaylorCoeff_comp_add_right (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (z + y)) x α = mvTaylorCoeff f (x + y) α := by
  by_cases hf : AnalyticAt 𝕜 f (x + y)
  · obtain ⟨p, hp⟩ := hf
    have hcomp : HasFPowerSeriesAt (fun z ↦ f (z + y)) p x := by
      simpa [sub_neg_eq_add] using hp.comp_sub (-y)
    rw [hcomp.mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq]
  · have hcomp : ¬AnalyticAt 𝕜 (fun z ↦ f (z + y)) x := fun ⟨q, hq⟩ ↦
      hf ⟨q, by simpa [sub_add_cancel] using hq.comp_sub y⟩
    rw [mvTaylorCoeff_of_not_analyticAt hcomp, mvTaylorCoeff_of_not_analyticAt hf]

@[simp]
theorem mvTaylorCoeff_comp_add_left (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (y + z)) x α = mvTaylorCoeff f (y + x) α := by
  simp_rw [add_comm y, mvTaylorCoeff_comp_add_right]

end TauCeti

namespace ContinuousLinearMap

/-- Postcomposing an analytic function with a continuous linear map applies that linear map to each
Taylor coefficient. -/
theorem mvTaylorCoeff_comp_left {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (L : F →L[𝕜] G) {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (L ∘ f) x α = L (TauCeti.mvTaylorCoeff f x α) := by
  obtain ⟨p, r, hp⟩ := hf
  rw [(L.comp_hasFPowerSeriesOnBall hp).hasFPowerSeriesAt.mvTaylorCoeff_eq,
    hp.hasFPowerSeriesAt.mvTaylorCoeff_eq, L.mvCoeff_compFormalMultilinearSeries]

/-- **Linear change of variables**: for `G` analytic at `A x`, if all Taylor coefficients of `G` at
`A x` of total degree `k` vanish, then so do all Taylor coefficients of `G ∘ A` at `x` of total
degree `k`. -/
theorem mvTaylorCoeff_comp_eq_zero {κ : Type*} [Fintype κ] {G : (ι → 𝕜) → F}
    (A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) {x : κ → 𝕜} (hG : AnalyticAt 𝕜 G (A x)) {k : ℕ}
    (h : ∀ α : ι → ℕ, ∑ i, α i = k → TauCeti.mvTaylorCoeff G (A x) α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → TauCeti.mvTaylorCoeff (G ∘ A) x β = 0 := by
  obtain ⟨p, hp⟩ := hG
  intro β hβ
  rw [hp.compContinuousLinearMap.mvTaylorCoeff_eq]
  exact p.mvCoeff_compContinuousLinearMap_eq_zero A
    (fun α hα ↦ by rw [← hp.mvTaylorCoeff_eq]; exact h α hα) β hβ

end ContinuousLinearMap

namespace AnalyticAt

/-- **Local multi-index expansion**: a function analytic at `x` expands in a normally convergent
multi-index power series `∑' α, (∏ i, y i ^ α i) • mvTaylorCoeff f x α` on some open polydisc of
positive radius `ρ` about `0`. -/
theorem exists_hasSum_mvTaylorCoeff {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      Summable (fun α : ι → ℕ ↦ ‖TauCeti.mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ i, α i)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ →
        HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • TauCeti.mvTaylorCoeff f x α) (f (x + y)) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨s, hs0, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hs_pos : 0 < s := ENNReal.coe_pos.1 hs0
  have hs_sum : Summable fun k ↦ ‖p k‖ * (s : ℝ) ^ k :=
    p.summable_norm_mul_pow (hsr.trans_le hp.r_le)
  let M : ℝ≥0 := Fintype.card ι + 1
  have hM_pos : 0 < M := by positivity
  let ρ : ℝ≥0 := s / M
  have hρ_pos : 0 < ρ := div_pos hs_pos hM_pos
  have hcM : (Fintype.card ι : ℝ) ≤ M := by simp [M]
  have hcρ : (Fintype.card ι : ℝ) * (ρ : ℝ) ≤ s := by
    calc (Fintype.card ι : ℝ) * (s / M : ℝ)
        ≤ (M : ℝ) * ((s : ℝ) / (M : ℝ)) := by gcongr
      _ = s := mul_div_cancel₀ _ (by positivity)
  have hρ_sum : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k := by
    refine hs_sum.of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    calc (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k
        = ‖p k‖ * ((Fintype.card ι : ℝ) * (ρ : ℝ)) ^ k := by rw [mul_pow]; ring
      _ ≤ ‖p k‖ * (s : ℝ) ^ k := by gcongr
  have hcoeff (α : ι → ℕ) : TauCeti.mvTaylorCoeff f x α = p.mvCoeff α :=
    hp.hasFPowerSeriesAt.mvTaylorCoeff_eq α
  refine ⟨ρ, hρ_pos, ?_, fun y hy ↦ ?_⟩
  · simp_rw [hcoeff]
    exact p.summable_norm_mvCoeff_mul_pow ρ.coe_nonneg hρ_sum
  · simp_rw [hcoeff]
    have h1M : (1 : ℝ) ≤ M := by simp [M]
    have hys : ‖y‖ < (s : ℝ) := hy.trans_le (div_le_self s.coe_nonneg h1M)
    have hy_mem : y ∈ Metric.eball (0 : ι → 𝕜) r := by
      have hnn : (‖y‖₊ : ℝ≥0∞) < s := ENNReal.coe_lt_coe.2 (by exact_mod_cast hys)
      simpa [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm] using hnn.trans hsr
    refine hp.hasSum_mvCoeff hy_mem ?_
    refine hρ_sum.of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    gcongr

end AnalyticAt

namespace TauCeti

/-- **Coefficients from an expansion**: any multi-index series that converges normally on a
polydisc of radius `ρ > 0` and sums to `f (x + y)` there has `mvTaylorCoeff f x` as its
coefficients. -/
theorem mvTaylorCoeff_eq_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i))
    (h : ∀ y : ι → 𝕜, ‖y‖ < ρ →
      HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y)))
    (α : ι → ℕ) : mvTaylorCoeff f x α = c α := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_of_hasSum c hρ hsum h
  rw [hp.hasFPowerSeriesAt.mvTaylorCoeff_eq, hpc]

open scoped Classical in
/-- At the origin, the vector-valued monomial `z ↦ (∏ i, z i ^ τ i) • v` has Taylor coefficient
`v` at `τ` and `0` at every other multi-index. -/
theorem mvTaylorCoeff_prod_pow_smul_zero (τ : ι → ℕ) (v : F) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ (∏ i, z i ^ τ i) • v) 0 α = if α = τ then v else 0 := by
  refine mvTaylorCoeff_eq_of_hasSum (𝕜 := 𝕜) (c := fun β ↦ if β = τ then v else 0)
    (ρ := 1) one_pos ?_ (fun y _ ↦ ?_) α
  · refine summable_of_ne_finset_zero (s := {τ}) fun β hβ ↦ ?_
    have hne : β ≠ τ := by simpa using hβ
    simp [hne]
  · rw [zero_add]
    convert hasSum_ite_eq τ ((∏ i, y i ^ τ i) • v) using 1
    ext β
    split_ifs with h
    · subst h; rfl
    · simp

open scoped Classical in
/-- At the origin, the scalar monomial `z ↦ ∏ i, z i ^ τ i` has Taylor coefficient `1` at `τ` and
`0` at every other multi-index. -/
theorem mvTaylorCoeff_prod_pow_zero (τ α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ ∏ i, z i ^ τ i) 0 α = if α = τ then 1 else 0 := by
  simpa using mvTaylorCoeff_prod_pow_smul_zero (𝕜 := 𝕜) τ (1 : 𝕜) α

end TauCeti

namespace AnalyticAt

/-- **Product rule for Taylor coefficients**: for an algebra-valued function `f` and a
module-valued function `g` both analytic at `x`, the Taylor coefficients of `f • g` are given by the
Cauchy convolution over `Finset.Iic α`. -/
@[to_fun mvTaylorCoeff_fun_smul]
theorem mvTaylorCoeff_smul {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    [DecidableEq ι] {f : (ι → 𝕜) → A} {g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (f • g) x α =
      ∑ β ∈ Finset.Iic α, TauCeti.mvTaylorCoeff f x β • TauCeti.mvTaylorCoeff g x (α - β) := by
  -- Intersect the polydiscs of normal convergence of `f` and `g` at `x`.
  obtain ⟨ρ₁, hρ₁, hsum₁, hf_sum⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨ρ₂, hρ₂, hsum₂, hg_sum⟩ := hg.exists_hasSum_mvTaylorCoeff
  let ρ : ℝ≥0 := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hsum₁' : Summable fun β : ι → ℕ ↦ ‖TauCeti.mvTaylorCoeff f x β‖ * (ρ : ℝ) ^ (∑ i, β i) :=
    hsum₁.of_nonneg_of_le (fun _ ↦ by positivity) fun β ↦ by gcongr; exact min_le_left ρ₁ ρ₂
  have hsum₂' : Summable fun γ : ι → ℕ ↦ ‖TauCeti.mvTaylorCoeff g x γ‖ * (ρ : ℝ) ^ (∑ i, γ i) :=
    hsum₂.of_nonneg_of_le (fun _ ↦ by positivity) fun γ ↦ by gcongr; exact min_le_right ρ₁ ρ₂
  -- Apply Cauchy-product normal convergence and `HasSum` on the common polydisc.
  let c : (ι → ℕ) → F :=
    fun μ ↦ ∑ β ∈ Finset.Iic μ, TauCeti.mvTaylorCoeff f x β • TauCeti.mvTaylorCoeff g x (μ - β)
  have hc_sum : Summable fun μ : ι → ℕ ↦ ‖c μ‖ * (ρ : ℝ) ^ (∑ i, μ i) :=
    TauCeti.summable_norm_sum_smul_Iic_mul hsum₁' hsum₂' (fun _ ↦ by positivity)
      (fun β γ ↦ by simp_rw [Pi.add_apply, sum_add_distrib, pow_add]; exact le_rfl)
  refine TauCeti.mvTaylorCoeff_eq_of_hasSum (c := c) hρ hc_sum (fun y hy ↦ ?_) α
  have hy₁ : ‖y‖ < (ρ₁ : ℝ) := hy.trans_le (min_le_left ρ₁ ρ₂)
  have hy₂ : ‖y‖ < (ρ₂ : ℝ) := hy.trans_le (min_le_right ρ₁ ρ₂)
  have hterm : (fun μ : ι → ℕ ↦ (∏ i, y i ^ μ i) • c μ) =
      fun μ ↦ ∑ β ∈ Finset.Iic μ,
        ((∏ i, y i ^ β i) • TauCeti.mvTaylorCoeff f x β) •
          ((∏ i, y i ^ (μ - β) i) • TauCeti.mvTaylorCoeff g x (μ - β)) := by
    ext μ
    rw [smul_sum]
    refine sum_congr rfl fun β hβ ↦ ?_
    have hpow : (∏ i, y i ^ β i) * (∏ i, y i ^ (μ - β) i) = ∏ i, y i ^ μ i := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ ↦ by
        rw [← pow_add, Pi.sub_apply, Nat.add_sub_of_le (mem_Iic.1 hβ i)]
    rw [← algebraMap_smul A (∏ i, y i ^ (μ - β) i), Algebra.smul_def, smul_smul, mul_assoc,
      ← Algebra.commutes, ← mul_assoc, ← map_mul, hpow, ← Algebra.smul_def, smul_assoc]
  rw [hterm]
  exact HasSum.sum_smul_Iic_of_summable_norm
    (f := fun β ↦ (∏ i, y i ^ β i) • TauCeti.mvTaylorCoeff f x β)
    (g := fun γ ↦ (∏ i, y i ^ γ i) • TauCeti.mvTaylorCoeff g x γ)
    (hf_sum y hy₁) (hg_sum y hy₂)
    (TauCeti.summable_norm_prod_pow_smul hy.le hsum₁')
    (TauCeti.summable_norm_prod_pow_smul hy.le hsum₂')

/-- **Product rule for algebra-valued analytic functions**: for `f` and `g` both analytic at `x`,
the Taylor coefficients of `f * g` are the Cauchy products over `Finset.Iic α`. -/
@[to_fun mvTaylorCoeff_fun_mul]
theorem mvTaylorCoeff_mul {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [DecidableEq ι] {f g : (ι → 𝕜) → A} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (f * g) x α =
      ∑ β ∈ Finset.Iic α, TauCeti.mvTaylorCoeff f x β * TauCeti.mvTaylorCoeff g x (α - β) :=
  hf.mvTaylorCoeff_smul hg α

/-- **Agreement with iterated Fréchet derivatives**: for `f` analytic at `x` and any coordinate
tuple `v : Fin (∑ i, α i) → ι` whose coordinate counts are `α`,
`(∏ i, (α i)!) • mvTaylorCoeff f x α` equals `iteratedFDeriv 𝕜 (∑ i, α i) f x` evaluated at
`fun j ↦ Pi.single (v j) 1`. No factorial is inverted, so this holds in every characteristic. -/
theorem prod_factorial_smul_mvTaylorCoeff [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ)
    (v : Fin (∑ i, α i) → ι)
    (hv : ∀ i, Fintype.card {j // v j = i} = α i) :
    (∏ i, (α i)!) • TauCeti.mvTaylorCoeff f x α =
      iteratedFDeriv 𝕜 (∑ i, α i) f x (fun j ↦ Pi.single (v j) 1) := by
  obtain ⟨p, r, hp⟩ := hf
  rw [hp.hasFPowerSeriesAt.mvTaylorCoeff_eq]
  revert v hv
  generalize hk : ∑ i, α i = k
  intro v hv
  rw [p.mvCoeff_eq_sum hk, hp.iteratedFDeriv_eq_sum_of_completeSpace]
  let S : Finset (Fin k → ι) :=
    univ.filter fun a : Fin k → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i
  have hmaps (σ : Equiv.Perm (Fin k)) : v ∘ σ ∈ S := by
    simp only [S, mem_filter, mem_univ, true_and]
    intro i
    rw [← hv i]
    exact Fintype.card_congr (Equiv.subtypeEquiv σ fun _ ↦ Iff.rfl)
  rw [← sum_fiberwise_of_maps_to (fun σ _ ↦ hmaps σ), smul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  have ha' : ∀ i, Fintype.card {j // a j = i} = α i := (mem_filter.1 ha).2
  have hterm : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin k) ↦ v ∘ σ = a),
        p k (fun j ↦ Pi.single (v (σ j)) 1) =
      (#(univ.filter fun σ : Equiv.Perm (Fin k) ↦ v ∘ σ = a)) •
        p k (fun j ↦ Pi.single (a j) 1) := by
    rw [← sum_const]
    refine sum_congr rfl fun σ hσ ↦ ?_
    have hσ' : v ∘ σ = a := (mem_filter.1 hσ).2
    simp_rw [← Function.comp_apply (f := v) (g := σ), hσ']
  rw [hterm]
  congr 1
  -- Right-multiplying by a permutation sending `a` to `v` bijects the fiber with the stabilizer.
  let σ₀ : Equiv.Perm (Fin k) :=
    Equiv.ofFiberEquiv fun i ↦ Fintype.equivOfCardEq ((ha' i).trans (hv i).symm)
  have hσ₀ : v ∘ σ₀ = a := funext fun j ↦ Equiv.ofFiberEquiv_map _ j
  have hbij : {σ : Equiv.Perm (Fin k) // v ∘ σ = a} ≃ {τ : Equiv.Perm (Fin k) // v ∘ τ = v} :=
    Equiv.subtypeEquiv (Equiv.mulRight σ₀⁻¹) fun σ ↦ by
      constructor <;> intro h <;> ext j
      · simpa [Equiv.Perm.coe_mul, ← hσ₀] using congrFun h (σ₀⁻¹ j)
      · have hj := congrFun h (σ₀ j)
        simpa [Equiv.Perm.coe_mul, ← congrFun hσ₀ j] using hj
  rw [← Fintype.card_subtype, Fintype.card_congr hbij, DomMulAct.stabilizer_card v]
  exact prod_congr rfl fun i _ ↦ by rw [hv i]

/-- **One-variable specialization**: for `f` analytic at `x` and a singleton index type `ι`,
`(α default)! • mvTaylorCoeff` of `z ↦ f (z default)` at `fun _ ↦ x` equals
`iteratedDeriv (α default) f x`. -/
theorem factorial_smul_mvTaylorCoeff_of_unique [Unique ι] [CompleteSpace F]
    {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    (α default)! • TauCeti.mvTaylorCoeff (fun z : ι → 𝕜 ↦ f (z default)) (fun _ ↦ x) α =
      iteratedDeriv (α default) f x := by
  obtain ⟨p, r, hp⟩ := hf
  let L : (ι → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj default
  have hpL : HasFPowerSeriesAt (fun z : ι → 𝕜 ↦ f (z default))
      (p.compContinuousLinearMap L) (fun _ ↦ x) :=
    hp.hasFPowerSeriesAt.compContinuousLinearMap (u := L) (x := fun _ ↦ x)
  rw [hpL.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_eq_sum _ (k := α default) (Fintype.sum_unique α)]
  have huniv : (univ.filter fun a : Fin (α default) → ι ↦
      ∀ i, Fintype.card {j // a j = i} = α i) = {fun _ ↦ default} := by
    ext a
    simp [Subsingleton.elim a (fun _ ↦ default), Unique.forall_iff]
  rw [huniv, sum_singleton, FormalMultilinearSeries.compContinuousLinearMap_apply]
  have harg : (⇑L ∘ fun _ : Fin (α default) ↦ Pi.single default (1 : 𝕜)) = fun _ ↦ 1 := by
    ext; simp [L]
  rw [harg]
  exact hp.factorial_smul 1 (α default)

end AnalyticAt
