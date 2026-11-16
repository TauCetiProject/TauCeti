/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Pi.Interval
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.GroupTheory.Perm.DomMulAct
import TauCeti.Algebra.MvPolynomial.Funext

/-!
# Multi-index Taylor coefficients of analytic functions

For a function `f : (ι → 𝕜) → F` on a finite-dimensional coordinate space over a nontrivially
normed field `𝕜`, the multi-index Taylor coefficient `TauCeti.mvTaylorCoeff f x α : F` is the
coefficient of `∏ i, (z i - x i) ^ α i` in any formal power series of `f` about `x`, and `0` when
`f` is not analytic at `x`.

By the identity theorem in coefficient form (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`), this
does not depend on the choice of formal power series (`HasFPowerSeriesAt.mvTaylorCoeff_eq`).
Because the definition avoids dividing by `α!`, it works in every characteristic and agrees with
iterated Fréchet derivatives via `(∏ i, (α i)!) • mvTaylorCoeff f x α = D^α f(x)`
(`AnalyticAt.prod_factorial_smul_mvTaylorCoeff`).

## Main definitions and results

* `TauCeti.mvTaylorCoeff`: the multi-index Taylor coefficient of `f` at `x` of order `α`.
* `HasFPowerSeriesAt.mvTaylorCoeff_eq` and `TauCeti.mvTaylorCoeff_of_not_analyticAt`:
  characterization in terms of any formal power series at `x`, and vanishing where `f` is not
  analytic.
* `AnalyticAt.mvTaylorCoeff_zero`, `TauCeti.mvTaylorCoeff_const`,
  `TauCeti.mvTaylorCoeff_const_smul`, `TauCeti.mvTaylorCoeff_neg`, `AnalyticAt.mvTaylorCoeff_add`,
  `AnalyticAt.mvTaylorCoeff_sub`, `TauCeti.mvTaylorCoeff_sum`: algebraic operations on Taylor
  coefficients.
* `Filter.EventuallyEq.mvTaylorCoeff_eq` and `TauCeti.mvTaylorCoeff_comp_add_right`: locality and
  translation invariance.
* `AnalyticAt.prod_factorial_smul_mvTaylorCoeff` and
  `AnalyticAt.factorial_smul_mvTaylorCoeff_of_unique`: agreement with iterated Fréchet derivatives
  and one-variable iterated derivatives.
* `AnalyticAt.exists_hasSum_mvTaylorCoeff` and `TauCeti.mvTaylorCoeff_eq_of_hasSum`: local
  normally convergent expansion of an analytic function, and extraction of Taylor coefficients from
  any normally convergent expansion.
* `TauCeti.mvTaylorCoeff_prod_pow_smul` and `TauCeti.mvTaylorCoeff_prod_pow`: Taylor coefficients
  of monomials at the origin.
* `AnalyticAt.mvTaylorCoeff_smul` and `AnalyticAt.mvTaylorCoeff_mul`: the product rule.
* `AnalyticAt.mvTaylorCoeff_comp_update`: freezing one coordinate kills coefficients with positive
  exponent in that coordinate and preserves the rest.
* `ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`: linear changes of variables preserve vanishing
  in each total degree.

## References

Multi-index Taylor coefficients of analytic functions are also developed in Michail Karatarakis's
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
/-- The **multi-index Taylor coefficient** of `f : (ι → 𝕜) → F` at `x` of order `α : ι → ℕ`: the
coefficient of `∏ i, (z i - x i) ^ α i` in any formal power series of `f` about `x`, and `0` when
`f` is not analytic at `x`. -/
noncomputable def mvTaylorCoeff (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) : F :=
  if h : AnalyticAt 𝕜 f x then h.choose.mvCoeff α else 0

/-- Where `f` is not analytic at `x`, every multi-index Taylor coefficient is `0`. -/
theorem mvTaylorCoeff_of_not_analyticAt {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ¬ AnalyticAt 𝕜 f x) (α : ι → ℕ) : mvTaylorCoeff f x α = 0 := by
  simp [mvTaylorCoeff, hf]

end TauCeti

open TauCeti

namespace HasFPowerSeriesAt

/-- The multi-index Taylor coefficient of `f` at `x` equals the multi-index coefficient of any
formal power series of `f` at `x`. -/
theorem mvTaylorCoeff_eq {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {x : ι → 𝕜} (hp : HasFPowerSeriesAt f p x) (α : ι → ℕ) :
    mvTaylorCoeff f x α = p.mvCoeff α := by
  have hf : AnalyticAt 𝕜 f x := ⟨p, hp⟩
  rw [mvTaylorCoeff, dite_eq_left hf]
  exact hf.choose_spec.mvCoeff_eq_of_eventuallyEq hp EventuallyEq.rfl α

end HasFPowerSeriesAt

namespace HasFPowerSeriesOnBall

/-- The multi-index Taylor coefficient of `f` at `x` equals the multi-index coefficient of any
formal power series of `f` on a ball about `x`. -/
theorem mvTaylorCoeff_eq {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {x : ι → 𝕜} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p x r) (α : ι → ℕ) :
    mvTaylorCoeff f x α = p.mvCoeff α :=
  hp.hasFPowerSeriesAt.mvTaylorCoeff_eq α

end HasFPowerSeriesOnBall

namespace AnalyticAt

/-- For a function analytic at `x`, the multi-index Taylor coefficient of order `0` is `f x`. -/
theorem mvTaylorCoeff_zero {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    mvTaylorCoeff f x 0 = f x := by
  obtain ⟨p, hp⟩ := hf
  rw [hp.mvTaylorCoeff_eq, p.mvCoeff_zero_eq_apply (fun _ ↦ 0), hp.coeff_zero]

/-- Additivity of multi-index Taylor coefficients for functions analytic at `x`. -/
theorem mvTaylorCoeff_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f + g) x α = mvTaylorCoeff f x α + mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.add hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_add]

/-- Subtraction of multi-index Taylor coefficients for functions analytic at `x`. -/
theorem mvTaylorCoeff_sub {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f - g) x α = mvTaylorCoeff f x α - mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.sub hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_sub]

end AnalyticAt

namespace TauCeti

/-- A constant function has Taylor coefficient `c` at `0` and `0` at every nonzero multi-index. -/
@[simp]
theorem mvTaylorCoeff_const (c : F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun _ : ι → 𝕜 ↦ c) x α = if α = 0 then c else 0 := by
  have hp := hasFPowerSeriesAt_const (𝕜 := 𝕜) (c := c) (e := x)
  split_ifs with hα
  · subst hα
    exact analyticAt_const.mvTaylorCoeff_zero
  · rw [hp.mvTaylorCoeff_eq]
    have hsum : ∑ i, α i ≠ 0 := fun h0 ↦
      hα (funext fun i ↦ (Finset.sum_eq_zero_iff.1 h0) i (mem_univ i))
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hsum
    classical
    rw [FormalMultilinearSeries.mvCoeff_eq_sum _ hk]
    simp [constFormalMultilinearSeries]

/-- The zero function has all multi-index Taylor coefficients equal to `0`. -/
@[simp]
theorem mvTaylorCoeff_zero_fun (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (0 : (ι → 𝕜) → F) x α = 0 := by
  simp [Pi.zero_def]

/-- Scalar multiplication by a constant commutes with `mvTaylorCoeff`, with no analyticity
hypothesis. -/
@[simp]
theorem mvTaylorCoeff_const_smul (c : 𝕜) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ c • f z) x α = c • mvTaylorCoeff f x α := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · by_cases hf : AnalyticAt 𝕜 f x
    · obtain ⟨p, hp⟩ := hf
      have hcf : HasFPowerSeriesAt (fun z ↦ c • f z) (c • p) x := hp.const_smul (c := c)
      rw [hcf.mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, FormalMultilinearSeries.mvCoeff_smul]
    · have hcf : ¬ AnalyticAt 𝕜 (fun z ↦ c • f z) x := by
        intro h
        have h' : AnalyticAt 𝕜 (fun z ↦ c⁻¹ • (c • f z)) x := h.const_smul (c := c⁻¹)
        exact hf (by simpa [hc] using h')
      rw [mvTaylorCoeff_of_not_analyticAt hcf, mvTaylorCoeff_of_not_analyticAt hf, smul_zero]

/-- Negation commutes with `mvTaylorCoeff`, with no analyticity hypothesis. -/
@[simp]
theorem mvTaylorCoeff_neg (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (-f) x α = -mvTaylorCoeff f x α := by
  simpa [Pi.neg_def] using mvTaylorCoeff_const_smul (-1 : 𝕜) f x α

/-- Finite additivity of multi-index Taylor coefficients for functions analytic at `x`. -/
theorem mvTaylorCoeff_sum {κ : Type*} (s : Finset κ) {f : κ → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ∀ i ∈ s, AnalyticAt 𝕜 (f i) x) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ ∑ i ∈ s, f i z) x α = ∑ i ∈ s, mvTaylorCoeff (f i) x α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha : AnalyticAt 𝕜 (f a) x := hf a (mem_insert_self a s)
    have hs : ∀ i ∈ s, AnalyticAt 𝕜 (f i) x := fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hsum : AnalyticAt 𝕜 (fun z ↦ ∑ i ∈ s, f i z) x := Finset.analyticAt_fun_sum s hs
    simp only [sum_insert has]
    rw [← ih hs, ← ha.mvTaylorCoeff_add hsum]
    rfl

/-- Translation invariance of multi-index Taylor coefficients, with no analyticity hypothesis. -/
theorem mvTaylorCoeff_comp_add_right (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (z + y)) x α = mvTaylorCoeff f (x + y) α := by
  have shift : ∀ {g : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {a b : ι → 𝕜},
      HasFPowerSeriesAt g p (a + b) → HasFPowerSeriesAt (fun z ↦ g (z + b)) p a := by
    intro g p a b ⟨r, hr⟩
    exact ⟨r, hr.r_le, hr.r_pos, fun {w} hw ↦ by
      simpa [add_assoc, add_comm w b] using hr.hasSum hw⟩
  by_cases hf : AnalyticAt 𝕜 f (x + y)
  · obtain ⟨p, hp⟩ := hf
    rw [(shift hp).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq]
  · have hfy : ¬ AnalyticAt 𝕜 (fun z ↦ f (z + y)) x := by
      intro ⟨p, hp⟩
      have hp' : HasFPowerSeriesAt (fun z ↦ f (z + y)) p ((x + y) + (-y)) := by simpa using hp
      exact hf ⟨p, by simpa using shift hp'⟩
    rw [mvTaylorCoeff_of_not_analyticAt hfy, mvTaylorCoeff_of_not_analyticAt hf]

end TauCeti

namespace Filter.EventuallyEq

/-- **Locality of multi-index Taylor coefficients**: functions agreeing near `x` have the same
Taylor coefficients at `x`, with no analyticity hypothesis. -/
theorem mvTaylorCoeff_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (h : f =ᶠ[𝓝 x] g) (α : ι → ℕ) :
    mvTaylorCoeff f x α = mvTaylorCoeff g x α := by
  by_cases hf : AnalyticAt 𝕜 f x
  · obtain ⟨p, hp⟩ := hf
    rw [hp.mvTaylorCoeff_eq, (hp.congr h).mvTaylorCoeff_eq]
  · have hg : ¬ AnalyticAt 𝕜 g x := fun hg ↦ hf (hg.congr h.symm)
    rw [mvTaylorCoeff_of_not_analyticAt hf, mvTaylorCoeff_of_not_analyticAt hg]

end Filter.EventuallyEq

namespace AnalyticAt

/-- **Agreement with iterated Fréchet derivatives**: for any tuple of basis vectors with coordinate
counts `α`, `(∏ i, (α i)!) • mvTaylorCoeff f x α` equals `iteratedFDeriv 𝕜 (∑ i, α i) f x` on that
tuple. No factorial is inverted, so this holds in every characteristic. -/
theorem prod_factorial_smul_mvTaylorCoeff [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ)
    (v : Fin (∑ i, α i) → ι) (hv : ∀ i, (univ.filter fun j ↦ v j = i).card = α i) :
    (∏ i, (α i).factorial) • mvTaylorCoeff f x α =
      iteratedFDeriv 𝕜 (∑ i, α i) f x (fun j ↦ Pi.single (v j) 1) := by
  obtain ⟨p, r, hp⟩ := hf
  let S : Finset (Fin (∑ i, α i) → ι) :=
    univ.filter fun a : Fin (∑ i, α i) → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i
  have hv_card (i : ι) : Fintype.card {j // v j = i} = α i := by
    simpa [Fintype.card_subtype] using hv i
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin (∑ i, α i)))), v ∘ σ ∈ S := fun σ _ ↦ by
    refine mem_filter.2 ⟨mem_univ _, fun i ↦ ?_⟩
    rw [← hv_card i]
    exact Fintype.card_congr (Equiv.subtypeEquiv σ fun j ↦ Iff.rfl)
  -- Each tuple `a ∈ S` arises from `v ∘ σ` for exactly `∏ i, (α i)!` permutations `σ`.
  have hfiber (a : Fin (∑ i, α i) → ι) (ha : a ∈ S) :
      (univ.filter fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a).card =
        ∏ i, (α i).factorial := by
    have ha_card : ∀ i, Fintype.card {j // a j = i} = α i := (mem_filter.1 ha).2
    let e_fib : ∀ i, {j // a j = i} ≃ {j // v j = i} :=
      fun i ↦ Fintype.equivOfCardEq ((ha_card i).trans (hv_card i).symm)
    let τ : Equiv.Perm (Fin (∑ i, α i)) :=
      (Equiv.sigmaFiberEquiv a).symm.trans
        ((Equiv.sigmaCongrRight e_fib).trans (Equiv.sigmaFiberEquiv v))
    have hτ : v ∘ τ = a := funext fun j ↦ by
      simpa [τ, Equiv.sigmaFiberEquiv, Equiv.sigmaCongrRight] using (e_fib (a j) ⟨j, rfl⟩).2
    let e_perm : {g : Equiv.Perm (Fin (∑ i, α i)) // a ∘ g = a} ≃
        {σ : Equiv.Perm (Fin (∑ i, α i)) // v ∘ σ = a} :=
      Equiv.subtypeEquiv (Equiv.mulLeft τ) fun g ↦ by
        simp [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ]
    rw [← Fintype.card_subtype, ← Fintype.card_congr e_perm, DomMulAct.stabilizer_card]
    exact prod_congr rfl fun i _ ↦ by rw [ha_card i]
  rw [hp.iteratedFDeriv_eq_sum_of_completeSpace, hp.mvTaylorCoeff_eq,
    p.mvCoeff_eq_sum (k := ∑ i, α i) rfl, smul_sum,
    ← sum_fiberwise_of_maps_to (g := fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ) hmaps]
  refine sum_congr rfl fun a ha ↦ ?_
  calc (∏ i, (α i).factorial) • p (∑ i, α i) (fun j ↦ Pi.single (a j) 1)
      = (univ.filter fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a).card •
          p (∑ i, α i) (fun j ↦ Pi.single (a j) 1) := by rw [hfiber a ha]
    _ = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a),
          p (∑ i, α i) (fun j ↦ Pi.single (v (σ j)) 1) := by
        rw [← sum_const]
        refine sum_congr rfl fun σ hσ ↦ ?_
        have hσ' : v ∘ σ = a := (mem_filter.1 hσ).2
        refine congrArg (p (∑ i, α i)) (funext fun j ↦ ?_)
        exact congrArg (fun i ↦ Pi.single i (1 : 𝕜)) (congrFun hσ'.symm j)

/-- **One-variable specialization**: for a singleton index type `ι`, `(α default)! • mvTaylorCoeff`
agrees with `iteratedDeriv (α default)`. No factorial is inverted, so this holds in every
characteristic. -/
theorem factorial_smul_mvTaylorCoeff_of_unique [Unique ι] [CompleteSpace F]
    {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    (α default).factorial • mvTaylorCoeff (fun z : ι → 𝕜 ↦ f (z default)) (fun _ ↦ x) α =
      iteratedDeriv (α default) f x := by
  obtain ⟨p, r, hp⟩ := hf
  let eval : (ι → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) default
  have hp_comp : HasFPowerSeriesAt (f ∘ eval) (p.compContinuousLinearMap eval) (fun _ ↦ x) :=
    (hp.hasFPowerSeriesAt : HasFPowerSeriesAt f p (eval fun _ ↦ x)).compContinuousLinearMap
  have hcoeff : mvTaylorCoeff (fun z : ι → 𝕜 ↦ f (z default)) (fun _ ↦ x) α =
      (p.compContinuousLinearMap eval).mvCoeff α := by
    simpa [Function.comp_def, eval] using hp_comp.mvTaylorCoeff_eq α
  rw [hcoeff, iteratedDeriv_eq_iteratedFDeriv, ← hp.factorial_smul 1]
  congr 1
  rw [FormalMultilinearSeries.mvCoeff_eq_sum _ (k := α default) (by simp)]
  have hfilt : (univ.filter fun a : Fin (α default) → ι ↦
      ∀ i, Fintype.card {j // a j = i} = α i) = {fun _ ↦ default} := by
    ext a
    simp [Subsingleton.elim a (fun _ ↦ default), Unique.forall_iff]
  rw [hfilt, sum_singleton]
  simp [eval, FormalMultilinearSeries.compContinuousLinearMap_apply]

/-- **The local expansion of an analytic function**: `f (x + y)` is the sum of its multi-index
Taylor series, normally convergent on some polydisc of positive radius `ρ`. -/
theorem exists_hasSum_mvTaylorCoeff {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      Summable (fun α : ι → ℕ ↦ ‖mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ i, α i)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ →
        HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • mvTaylorCoeff f x α) (f (x + y)) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨r₀, hr₀_pos, hr₀_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hr₀_pos' : (0 : ℝ≥0) < r₀ := ENNReal.coe_pos.1 hr₀_pos
  have hs : Summable fun k ↦ ‖p k‖ * (r₀ : ℝ) ^ k :=
    p.summable_norm_mul_pow (hr₀_lt.trans_le hp.r_le)
  let c : ℝ≥0 := max (Fintype.card ι : ℝ≥0) 1
  have hc_pos : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  let ρ : ℝ≥0 := r₀ / c
  have hρ_pos : 0 < ρ := div_pos hr₀_pos' hc_pos
  have hcard_mul (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ ρ) :
      Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * t ^ k := by
    refine hs.of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
    have hct : (Fintype.card ι : ℝ) * t ≤ r₀ := by
      calc (Fintype.card ι : ℝ) * t
          ≤ (c : ℝ) * (ρ : ℝ) := by
            gcongr
            exact NNReal.coe_le_coe.2 (le_max_left (Fintype.card ι : ℝ≥0) 1)
        _ = r₀ := by simp [ρ, mul_div_cancel₀ _ (NNReal.coe_ne_zero.2 hc_pos.ne')]
    calc (Fintype.card ι : ℝ) ^ k * ‖p k‖ * t ^ k
        = ‖p k‖ * ((Fintype.card ι : ℝ) * t) ^ k := by rw [mul_pow]; ring
      _ ≤ ‖p k‖ * (r₀ : ℝ) ^ k := by gcongr
  refine ⟨ρ, hρ_pos, ?_, fun y hy ↦ ?_⟩
  · simp_rw [hp.mvTaylorCoeff_eq]
    exact p.summable_norm_mvCoeff_mul_pow ρ.coe_nonneg (hcard_mul ρ ρ.coe_nonneg le_rfl)
  · simp_rw [hp.mvTaylorCoeff_eq]
    have hρ_le : ρ ≤ r₀ := div_le_self zero_le (le_max_right _ _)
    have hy_r₀ : ‖y‖ₑ < r := by
      rw [← ofReal_norm]
      exact ((ENNReal.ofReal_lt_coe_iff (norm_nonneg y)).2 (hy.trans_le hρ_le)).trans hr₀_lt
    have hy_mem : y ∈ Metric.eball (0 : ι → 𝕜) r := by
      simpa [Metric.mem_eball, edist_zero_right] using hy_r₀
    exact hp.hasSum_mvCoeff hy_mem (hcard_mul ‖y‖ (norm_nonneg y) hy.le)

end AnalyticAt

namespace TauCeti

/-- **Coefficients from a normally convergent expansion**: any normally convergent multi-index
expansion of `f (x + ·)` on a polydisc has the multi-index Taylor coefficients of `f` at `x` as its
coefficients. -/
theorem mvTaylorCoeff_eq_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i))
    (h : ∀ y : ι → 𝕜, ‖y‖ < ρ →
      HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y)))
    (α : ι → ℕ) : mvTaylorCoeff f x α = c α := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_of_hasSum hρ hsum h
  rw [hp.mvTaylorCoeff_eq, hpc]

/-- A scaled monomial `z ↦ (∏ i, z i ^ τ i) • v` has Taylor coefficient `v` at `τ` and `0` at
every other multi-index, at the origin. -/
@[simp]
theorem mvTaylorCoeff_prod_pow_smul (τ : ι → ℕ) (v : F) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ (∏ i, z i ^ τ i) • v) 0 α = if α = τ then v else 0 := by
  let c : (ι → ℕ) → F := fun β ↦ if β = τ then v else 0
  refine mvTaylorCoeff_eq_of_hasSum (c := c) (ρ := 1) one_pos ?_ (fun y _ ↦ ?_) α
  · refine summable_of_ne_finset_zero (s := {τ}) fun β hβ ↦ ?_
    simp [c, Finset.mem_singleton.not.1 hβ]
  · rw [zero_add]
    convert hasSum_ite_eq τ ((∏ i, y i ^ τ i) • v) with β
    dsimp only [c]
    split_ifs with h <;> simp [h]

/-- A monomial `z ↦ ∏ i, z i ^ τ i` has Taylor coefficient `1` at `τ` and `0` at every other
multi-index, at the origin. -/
@[simp]
theorem mvTaylorCoeff_prod_pow (τ : ι → ℕ) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ ∏ i, z i ^ τ i) 0 α = if α = τ then (1 : 𝕜) else 0 := by
  simpa using mvTaylorCoeff_prod_pow_smul (𝕜 := 𝕜) τ (1 : 𝕜) α

end TauCeti

namespace AnalyticAt

/-- **The product rule for multi-index Taylor coefficients** of a scalar-valued function times a
vector-valued one. -/
theorem mvTaylorCoeff_smul [DecidableEq ι] {f : (ι → 𝕜) → 𝕜} {g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f z • g z) x α =
      ∑ β ∈ Iic α, mvTaylorCoeff f x β • mvTaylorCoeff g x (α - β) := by
  obtain ⟨ρ₁, hρ₁, hsum₁, hhas₁⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨ρ₂, hρ₂, hsum₂, hhas₂⟩ := hg.exists_hasSum_mvTaylorCoeff
  let ρ : ℝ≥0 := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  let a : (ι → ℕ) → 𝕜 := mvTaylorCoeff f x
  let b : (ι → ℕ) → F := mvTaylorCoeff g x
  let c : (ι → ℕ) → F := fun α ↦ ∑ β ∈ Iic α, a β • b (α - β)
  have hsum₁' : Summable fun β : ι → ℕ ↦ ‖a β‖ * (ρ : ℝ) ^ (∑ i, β i) :=
    hsum₁.of_nonneg_of_le (fun _ ↦ by positivity) fun β ↦ by
      gcongr; exact_mod_cast min_le_left ρ₁ ρ₂
  have hsum₂' : Summable fun γ : ι → ℕ ↦ ‖b γ‖ * (ρ : ℝ) ^ (∑ i, γ i) :=
    hsum₂.of_nonneg_of_le (fun _ ↦ by positivity) fun γ ↦ by
      gcongr; exact_mod_cast min_le_right ρ₁ ρ₂
  -- Reindex `(β, γ) : (ι → ℕ) × (ι → ℕ)` by total multi-index `α = β + γ` and `β ∈ Iic α`.
  let e : (Σ α : ι → ℕ, Iic α) ≃ (ι → ℕ) × (ι → ℕ) :=
    { toFun := fun ⟨α, β, _⟩ ↦ (β, α - β)
      invFun := fun p ↦ ⟨p.1 + p.2, p.1, mem_Iic.2 le_self_add⟩
      left_inv := fun ⟨_, _, hβ⟩ ↦
        Sigma.subtype_ext (funext fun i ↦ Nat.add_sub_of_le (mem_Iic.1 hβ i)) rfl
      right_inv := fun ⟨_, _⟩ ↦ Prod.ext rfl (funext fun i ↦ Nat.add_sub_cancel_left _ _) }
  -- Normal summability of the Cauchy convolution `c` on the polydisc of radius `ρ`.
  have hprod := hsum₁'.mul_of_nonneg hsum₂' (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  have hsum_c : Summable fun α : ι → ℕ ↦ ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i) := by
    have hsigma := (e.summable_iff.2 hprod).sigma' fun _ ↦ (hasSum_fintype _).summable
    refine hsigma.of_nonneg_of_le (fun _ ↦ by positivity) fun α ↦ ?_
    rw [tsum_fintype]
    simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
    rw [sum_coe_sort (Iic α)
      (fun β ↦ (‖a β‖ * (ρ : ℝ) ^ (∑ i, β i)) * (‖b (α - β)‖ * (ρ : ℝ) ^ (∑ i, (α - β) i)))]
    calc ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i)
        ≤ (∑ β ∈ Iic α, ‖a β‖ * ‖b (α - β)‖) * (ρ : ℝ) ^ (∑ i, α i) := by
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun β _ ↦ by rw [norm_smul])
      _ = ∑ β ∈ Iic α,
            (‖a β‖ * (ρ : ℝ) ^ (∑ i, β i)) * (‖b (α - β)‖ * (ρ : ℝ) ^ (∑ i, (α - β) i)) := by
          rw [sum_mul]
          refine sum_congr rfl fun β hβ ↦ ?_
          have hdeg : ∑ i, α i = (∑ i, β i) + ∑ i, (α - β) i := by
            rw [← sum_add_distrib]
            exact sum_congr rfl fun i _ ↦ (Nat.add_sub_of_le (mem_Iic.1 hβ i)).symm
          rw [hdeg, pow_add]; ring
  -- Identify the series of `c` with `f (x + y) • g (x + y)` on `‖y‖ < ρ`, then extract coeffs.
  refine mvTaylorCoeff_eq_of_hasSum hρ hsum_c (fun y hy ↦ ?_) α
  let u : (ι → ℕ) → 𝕜 := fun β ↦ (∏ i, y i ^ β i) • a β
  let v : (ι → ℕ) → F := fun γ ↦ (∏ i, y i ^ γ i) • b γ
  have hu : HasSum u (f (x + y)) := hhas₁ y (hy.trans_le (min_le_left ρ₁ ρ₂))
  have hv : HasSum v (g (x + y)) := hhas₂ y (hy.trans_le (min_le_right ρ₁ ρ₂))
  have hun : Summable fun β ↦ ‖u β‖ := summable_norm_prod_pow_smul hsum₁' hy.le
  have hvn : Summable fun γ ↦ ‖v γ‖ := summable_norm_prod_pow_smul hsum₂' hy.le
  have huv_norm : Summable fun p : (ι → ℕ) × (ι → ℕ) ↦ ‖u p.1 • v p.2‖ := by
    simpa only [norm_smul] using
      hun.mul_of_nonneg hvn (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have huv : HasSum (fun p : (ι → ℕ) × (ι → ℕ) ↦ u p.1 • v p.2) (f (x + y) • g (x + y)) := by
    refine hasSum_of_subseq_of_summable huv_norm
      (s := fun p : Finset (ι → ℕ) × Finset (ι → ℕ) ↦ p.1 ×ˢ p.2) tendsto_finsetProd_atTop ?_
    rw [← prod_atTop_atTop_eq]
    have hpair : Tendsto (Prod.map (fun s ↦ ∑ β ∈ s, u β) (fun s ↦ ∑ γ ∈ s, v γ))
        (atTop ×ˢ atTop) (𝓝 (f (x + y), g (x + y))) := by
      simpa only [HasSum, SummationFilter.unconditional_filter, nhds_prod_eq] using hu.prodMap hv
    convert (continuous_smul.continuousAt (x := (f (x + y), g (x + y)))).tendsto.comp hpair with p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, sum_product, sum_smul, smul_sum]
    rw [sum_comm]
  refine (e.hasSum_iff.2 huv).sigma fun α ↦ ?_
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
  convert hasSum_fintype (fun β : Iic α ↦ u β • v (α - β)) using 1
  rw [sum_coe_sort (Iic α) (fun β ↦ u β • v (α - β)), smul_sum]
  refine sum_congr rfl fun β hβ ↦ ?_
  dsimp only [u, v]
  rw [smul_eq_mul, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (a β), ← mul_assoc, ← prod_mul_distrib]
  congr 1
  exact prod_congr rfl fun i _ ↦ by
    rw [← pow_add, Pi.sub_apply, Nat.add_sub_of_le (mem_Iic.1 hβ i)]

/-- **The product rule for scalar-valued analytic functions**. -/
theorem mvTaylorCoeff_mul [DecidableEq ι] {f g : (ι → 𝕜) → 𝕜} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f z * g z) x α =
      ∑ β ∈ Iic α, mvTaylorCoeff f x β * mvTaylorCoeff g x (α - β) :=
  hf.mvTaylorCoeff_smul hg α

/-- Freezing the `i`-th coordinate to `x i` kills every multi-index Taylor coefficient at `x`
with `α i ≠ 0` and preserves those with `α i = 0`. -/
theorem mvTaylorCoeff_comp_update [DecidableEq ι] {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (i : ι) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (Function.update z i (x i))) x α =
      if α i = 0 then mvTaylorCoeff f x α else 0 := by
  obtain ⟨p, r, hp⟩ := hf
  let L : (ι → 𝕜) →L[𝕜] (ι → 𝕜) :=
    ContinuousLinearMap.pi fun j ↦
      if j = i then 0 else ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) j
  have hupd (y : ι → 𝕜) : Function.update (y + x) i (x i) = L y + x := by
    ext j; by_cases hji : j = i <;> simp [L, hji]
  have hp0 : HasFPowerSeriesAt (fun w ↦ f (w + x)) p (L 0) := by
    rw [map_zero]
    exact ⟨r, hp.r_le, hp.r_pos, fun {y} hy ↦ by simpa [add_comm y x] using hp.hasSum hy⟩
  have hpL : HasFPowerSeriesAt (fun y ↦ f (Function.update (y + x) i (x i)))
      (p.compContinuousLinearMap L) 0 := by
    simpa only [Function.comp_def, ← hupd] using hp0.compContinuousLinearMap
  have htrans : mvTaylorCoeff (fun z ↦ f (Function.update z i (x i))) x α =
      mvTaylorCoeff (fun y ↦ f (Function.update (y + x) i (x i))) 0 α := by
    simpa using (mvTaylorCoeff_comp_add_right (fun z ↦ f (Function.update z i (x i))) 0 x α).symm
  rw [htrans, hpL.mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq,
    FormalMultilinearSeries.mvCoeff_eq_sum _ (k := ∑ j, α j) rfl,
    FormalMultilinearSeries.mvCoeff_eq_sum _ (k := ∑ j, α j) rfl]
  split_ifs with hα
  · refine sum_congr rfl fun a ha ↦ ?_
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def]
    refine congrArg (p (∑ j, α j)) (funext fun t ↦ ?_)
    have hne : a t ≠ i := fun h ↦ by
      have hpos : 0 < Fintype.card {j // a j = i} := Fintype.card_pos_iff.2 ⟨⟨t, h⟩⟩
      rw [(mem_filter.1 ha).2 i, hα] at hpos
      exact lt_irrefl 0 hpos
    ext j
    by_cases hji : j = i <;> simp [L, hji, hne]
  · refine sum_eq_zero fun a ha ↦ ?_
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def]
    have hpos : 0 < Fintype.card {j // a j = i} := by
      rw [(mem_filter.1 ha).2 i]; exact Nat.pos_of_ne_zero hα
    obtain ⟨t, ht⟩ := Fintype.card_pos_iff.1 hpos
    refine (p (∑ j, α j)).map_coord_zero t ?_
    ext j
    by_cases hji : j = i <;> simp [L, hji, ht]

end AnalyticAt

namespace ContinuousLinearMap

/-- **Linear change of variables**: if all multi-index Taylor coefficients of `G` at `A x` of total
degree `k` vanish, then all multi-index Taylor coefficients of `G ∘ A` at `x` of total degree `k`
also vanish. -/
theorem mvTaylorCoeff_comp_eq_zero {κ : Type*} [Fintype κ] {G : (ι → 𝕜) → F}
    (A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) {x : κ → 𝕜} (hG : AnalyticAt 𝕜 G (A x)) {k : ℕ}
    (h : ∀ α : ι → ℕ, ∑ i, α i = k → mvTaylorCoeff G (A x) α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → mvTaylorCoeff (G ∘ A) x β = 0 := by
  classical
  obtain ⟨p, hp⟩ := hG
  have hpA : HasFPowerSeriesAt (G ∘ A) (p.compContinuousLinearMap A) x :=
    hp.compContinuousLinearMap
  have hzero (z : κ → 𝕜) :
      ∑ β ∈ univ.piAntidiag k,
        (∏ j, z j ^ β j) • (p.compContinuousLinearMap A).mvCoeff β = 0 := by
    rw [← FormalMultilinearSeries.apply_eq_sum_mvCoeff,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp only [Function.comp_def]
    rw [p.apply_eq_sum_mvCoeff]
    refine sum_eq_zero fun α hα ↦ ?_
    rw [← hp.mvTaylorCoeff_eq, h α (mem_piAntidiag.1 hα).1, smul_zero]
  intro β hβ
  rw [hpA.mvTaylorCoeff_eq]
  exact eq_zero_of_forall_sum_prod_pow_smul_eq_zero hzero (mem_piAntidiag.2 ⟨hβ, by simp⟩)

end ContinuousLinearMap
