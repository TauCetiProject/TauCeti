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
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.GroupTheory.Perm.DomMulAct
import TauCeti.Algebra.MvPolynomial.Funext
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Normed.Module.InfiniteSum
import TauCeti.GroupTheory.Perm.FiberSubgroup

/-!
# Multi-index Taylor coefficients of analytic functions

For a function `f : (ι → 𝕜) → F` on a finite product over a nontrivially normed field `𝕜`,
`TauCeti.mvTaylorCoeff f x α` is the multi-index Taylor coefficient of `f` at `x` of index
`α : ι → ℕ`: the coefficient `p.mvCoeff α` of `(z - x) ^ α` in any formal multilinear power series
`p` representing `f` around `x`, and `0` when `f` is not analytic at `x`. By the identity theorem
in multi-index form (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`), this value does not depend
on the choice of formal power series `p`.

Relating Taylor coefficients to iterated derivatives multiplies by the multi-index factorial
`∏ i, (α i)!` rather than dividing by it (`AnalyticAt.prod_factorial_smul_mvTaylorCoeff`), so the
formula holds in arbitrary characteristic. Under a continuous linear change of variables `A`,
vanishing of all Taylor coefficients of a fixed total degree `k` at `A x` transfers to `G ∘ A` at
`x` (`ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`), whereas coordinatewise bounds `α i < m` do
not.

## Main definitions and results

* `TauCeti.mvTaylorCoeff`: the multi-index Taylor coefficient of `f` at `x`, equal to `0` if `f`
  is not analytic at `x`.
* `HasFPowerSeriesAt.mvTaylorCoeff_eq` and `HasFPowerSeriesOnBall.mvTaylorCoeff_eq`: agreement
  with `FormalMultilinearSeries.mvCoeff` for any power series of `f` at `x`.
* `Filter.EventuallyEq.mvTaylorCoeff_eq`,
  `AnalyticAt.eventuallyEq_zero_iff_forall_mvTaylorCoeff_eq_zero`, and
  `AnalyticAt.eventuallyEq_iff_forall_mvTaylorCoeff_eq`: locality and analytic-germ extensionality.
* `TauCeti.mvTaylorCoeff_const`, `TauCeti.mvTaylorCoeff_zero`, `TauCeti.mvTaylorCoeff_one`,
  `TauCeti.mvTaylorCoeff_const_smul`, `TauCeti.mvTaylorCoeff_neg`,
  `AnalyticAt.mvTaylorCoeff_add`, `AnalyticAt.mvTaylorCoeff_sub`, `TauCeti.mvTaylorCoeff_sum`,
  `TauCeti.mvTaylorCoeff_comp_add_right`, `TauCeti.mvTaylorCoeff_comp_sub`: algebraic and
  translation properties.
* `AnalyticAt.exists_hasSum_mvTaylorCoeff` and `TauCeti.mvTaylorCoeff_eq_of_hasSum`: local
  normally convergent multi-index expansion on a polydisc and characterization of Taylor
  coefficients by such an expansion.
* `TauCeti.mvTaylorCoeff_prod_pow_smul`, `TauCeti.mvTaylorCoeff_prod_pow`,
  `TauCeti.mvTaylorCoeff_prod_sub_pow_smul`, `TauCeti.mvTaylorCoeff_prod_sub_pow`, and
  `TauCeti.mvTaylorCoeff_apply`: Taylor coefficients of monomials and coordinate projections.
* `AnalyticAt.mvTaylorCoeff_smul` and `AnalyticAt.mvTaylorCoeff_mul`: the Cauchy product rule
  over `Finset.Iic α` for normed-algebra actions and products.
* `AnalyticAt.prod_factorial_smul_mvTaylorCoeff`,
  `AnalyticAt.norm_prod_factorial_smul_mvTaylorCoeff_le`, and
  `AnalyticAt.factorial_smul_mvTaylorCoeff_of_unique`: agreement and norm bound with
  `iteratedFDeriv` and, in one variable, `iteratedDeriv`.
* `ContinuousLinearMap.mvTaylorCoeff_comp_left`,
  `ContinuousLinearEquiv.mvTaylorCoeff_comp_left`, and
  `ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero`: postcomposition with continuous linear maps and
  equivalences, and preservation of vanishing in a given total degree under precomposition.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Chapter 4.
* Multi-index Taylor coefficients are also formalized in Michail Karatarakis's development of
  Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
  `Mathlib/NumberTheory/Transcendental/Baker/TaylorCoeff.lean`, Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped NNReal ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

open Classical in
/-- The **multi-index Taylor coefficient** of `f : (ι → 𝕜) → F` at `x` of index `α : ι → ℕ`: the
coefficient of `∏ i, (z i - x i) ^ α i` in the power series expansion of `f` about `x`, and `0` if
`f` is not analytic at `x`. -/
noncomputable def mvTaylorCoeff (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) : F :=
  if h : AnalyticAt 𝕜 f x then h.choose.mvCoeff α else 0

/-- Outside the analytic locus of `f`, every Taylor coefficient is `0` by convention. -/
theorem mvTaylorCoeff_of_not_analyticAt {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (h : ¬ AnalyticAt 𝕜 f x) (α : ι → ℕ) : mvTaylorCoeff f x α = 0 := by
  simp [mvTaylorCoeff, h]

end TauCeti

/-- **Independence of the chosen power series**: if `f` has the formal multilinear series `p` at
`x`, then `TauCeti.mvTaylorCoeff f x α = p.mvCoeff α`. -/
theorem HasFPowerSeriesAt.mvTaylorCoeff_eq {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} (hp : HasFPowerSeriesAt f p x)
    (α : ι → ℕ) : TauCeti.mvTaylorCoeff f x α = p.mvCoeff α := by
  have hf : AnalyticAt 𝕜 f x := ⟨p, hp⟩
  simp only [TauCeti.mvTaylorCoeff, hf, ↓reduceDIte]
  exact hf.choose_spec.mvCoeff_eq_of_eventuallyEq hp EventuallyEq.rfl α

/-- If `f` has the formal multilinear series `p` on a ball around `x`, its Taylor coefficients at
`x` are the multi-index coefficients of `p`. -/
theorem HasFPowerSeriesOnBall.mvTaylorCoeff_eq {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff f x α = p.mvCoeff α :=
  hp.hasFPowerSeriesAt.mvTaylorCoeff_eq α

/-- **Locality**: functions that agree on a neighborhood of `x` have the same Taylor coefficients
at `x`, whether or not they are analytic there. -/
theorem Filter.EventuallyEq.mvTaylorCoeff_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (h : f =ᶠ[𝓝 x] g) (α : ι → ℕ) : TauCeti.mvTaylorCoeff f x α = TauCeti.mvTaylorCoeff g x α := by
  by_cases hf : AnalyticAt 𝕜 f x
  · have hg : AnalyticAt 𝕜 g x := (analyticAt_congr h).1 hf
    rw [hf.choose_spec.mvTaylorCoeff_eq, hg.choose_spec.mvTaylorCoeff_eq]
    exact hf.choose_spec.mvCoeff_eq_of_eventuallyEq hg.choose_spec h α
  · have hg : ¬ AnalyticAt 𝕜 g x := fun hg ↦ hf ((analyticAt_congr h).2 hg)
    rw [TauCeti.mvTaylorCoeff_of_not_analyticAt hf, TauCeti.mvTaylorCoeff_of_not_analyticAt hg]

namespace AnalyticAt

open TauCeti

/-- For `f` analytic at `x`, the Taylor coefficient of order `0` is `f x`. -/
theorem mvTaylorCoeff_zero {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    mvTaylorCoeff f x 0 = f x := by
  obtain ⟨p, hp⟩ := hf
  rw [hp.mvTaylorCoeff_eq, p.mvCoeff_zero_eq_apply 0, hp.coeff_zero 0]

/-- **Additivity** of Taylor coefficients for functions analytic at `x`. -/
@[to_fun mvTaylorCoeff_fun_add]
theorem mvTaylorCoeff_add {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f + g) x α = mvTaylorCoeff f x α + mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.add hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq, p.mvCoeff_add]

/-- Taylor coefficients commute with subtraction for functions analytic at `x`. -/
@[to_fun mvTaylorCoeff_fun_sub]
theorem mvTaylorCoeff_sub {f g : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f - g) x α = mvTaylorCoeff f x α - mvTaylorCoeff g x α := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  rw [(hp.sub hq).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, hq.mvTaylorCoeff_eq, p.mvCoeff_sub]

/-- **Local multi-index expansion of an analytic function**: if `f` is analytic at `x`, then on
some polydisc of positive radius `ρ` its Taylor coefficients are normally summable and `f (x + y)`
is the sum of `(∏ i, y i ^ α i) • mvTaylorCoeff f x α`. -/
theorem exists_hasSum_mvTaylorCoeff {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧
      Summable (fun α : ι → ℕ ↦ ‖mvTaylorCoeff f x α‖ * (ρ : ℝ) ^ (∑ i, α i)) ∧
      ∀ y : ι → 𝕜, ‖y‖ < ρ →
        HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • mvTaylorCoeff f x α) (f (x + y)) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨r₀, hr₀_pos, hr₀_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hr₀ : (0 : ℝ≥0) < r₀ := ENNReal.coe_pos.1 hr₀_pos
  let N : ℝ≥0 := max (Fintype.card ι) 1
  have hN1 : (1 : ℝ≥0) ≤ N := le_max_right _ _
  have hN_pos : (0 : ℝ≥0) < N := zero_lt_one.trans_le hN1
  let ρ : ℝ≥0 := r₀ / (2 * N)
  have hρ_pos : 0 < ρ := div_pos hr₀ (mul_pos two_pos hN_pos)
  -- Scale by `2 * max (card ι) 1` so `(card ι) * ρ < r₀ < r ≤ p.radius` even when `ι` is empty.
  have hcard_ρ_lt : (((Fintype.card ι : ℝ≥0) * ρ : ℝ≥0) : ℝ≥0∞) < p.radius := by
    have hle : (Fintype.card ι : ℝ≥0) * ρ ≤ r₀ / 2 := by
      calc (Fintype.card ι : ℝ≥0) * (r₀ / (2 * N))
          ≤ N * (r₀ / (2 * N)) := by gcongr; exact le_max_left _ _
        _ = r₀ / 2 := by
            rw [mul_div_assoc', mul_comm (2 : ℝ≥0) N, mul_div_mul_left _ _ hN_pos.ne']
    have hlt : r₀ / 2 < r₀ := NNReal.half_lt_self hr₀.ne'
    exact (ENNReal.coe_lt_coe.2 (hle.trans_lt hlt)).trans (hr₀_lt.trans_le hp.r_le)
  have hop : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * (ρ : ℝ) ^ k := by
    refine (p.summable_norm_mul_pow hcard_ρ_lt).congr fun k ↦ ?_
    push_cast
    ring
  have hρ_lt_r : (ρ : ℝ≥0∞) < r := by
    have hle : ρ ≤ r₀ / 2 := by
      rw [div_le_div_iff_of_pos_left hr₀ (mul_pos two_pos hN_pos) two_pos]
      simpa using mul_le_mul_of_nonneg_left hN1 zero_le_two
    exact (ENNReal.coe_lt_coe.2 (hle.trans_lt (NNReal.half_lt_self hr₀.ne'))).trans hr₀_lt
  refine ⟨ρ, hρ_pos, ?_, fun y hy ↦ ?_⟩
  · simp_rw [hp.mvTaylorCoeff_eq]
    exact p.summable_norm_mvCoeff_mul_pow ρ.coe_nonneg hop
  · simp_rw [hp.mvTaylorCoeff_eq]
    have hy_ball : y ∈ Metric.eball (0 : ι → 𝕜) r := by
      have h1 : (‖y‖₊ : ℝ≥0∞) < ρ := ENNReal.coe_lt_coe.2 (by exact_mod_cast hy)
      simpa only [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm] using h1.trans hρ_lt_r
    refine hp.hasSum_mvCoeff hy_ball ?_
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) hop
    gcongr

/-- **Analytic-germ vanishing criterion**: an analytic function at `x` vanishes on a neighborhood of
`x` if and only if all of its multi-index Taylor coefficients at `x` vanish. No completeness
assumption on `F` is needed. -/
theorem eventuallyEq_zero_iff_forall_mvTaylorCoeff_eq_zero {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) :
    f =ᶠ[𝓝 x] 0 ↔ ∀ α, mvTaylorCoeff f x α = 0 := by
  refine ⟨fun h α ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨p, hp⟩ := hf
    rw [hp.mvTaylorCoeff_eq]
    exact hp.mvCoeff_eq_zero_of_eventuallyEq_zero h α
  · obtain ⟨ρ, hρ, -, hexp⟩ := hf.exists_hasSum_mvTaylorCoeff
    filter_upwards [Metric.ball_mem_nhds x (NNReal.coe_pos.2 hρ)] with z hz
    have hy : ‖z - x‖ < ρ := by simpa [dist_eq_norm] using hz
    have hsum := hexp (z - x) hy
    simp_rw [h, smul_zero, add_sub_cancel] at hsum
    exact hsum.unique hasSum_zero

/-- **Analytic-germ extensionality**: two functions analytic at `x` agree on a neighborhood of `x`
if and only if they have the same multi-index Taylor coefficients at `x`. No completeness
assumption on `F` is needed. -/
theorem eventuallyEq_iff_forall_mvTaylorCoeff_eq {f g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    f =ᶠ[𝓝 x] g ↔ ∀ α, mvTaylorCoeff f x α = mvTaylorCoeff g x α := by
  refine ⟨fun h ↦ h.mvTaylorCoeff_eq, fun h ↦ ?_⟩
  have hsub : f - g =ᶠ[𝓝 x] 0 :=
    (hf.sub hg).eventuallyEq_zero_iff_forall_mvTaylorCoeff_eq_zero.2 fun α ↦ by
      rw [hf.mvTaylorCoeff_sub hg α, h α, sub_self]
  exact hsub.mono fun y hy ↦ sub_eq_zero.1 hy

/-- **Agreement with iterated Fréchet derivatives**: for `f` analytic at `x` and any tuple `v` of
basis coordinates in which each `i` appears `α i` times (such as the one provided by
`TauCeti.exists_forall_card_filter_eq`), `(∏ i, (α i)!) • mvTaylorCoeff f x α` equals
`iteratedFDeriv 𝕜 (∑ i, α i) f x` applied to `j ↦ Pi.single (v j) 1`. No factorial is inverted, so
this holds in arbitrary characteristic. -/
theorem prod_factorial_smul_mvTaylorCoeff [DecidableEq ι] [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) (v : Fin (∑ i, α i) → ι)
    (hv : ∀ i, (Finset.univ.filter fun j ↦ v j = i).card = α i) :
    (∏ i, (α i).factorial) • mvTaylorCoeff f x α =
      iteratedFDeriv 𝕜 (∑ i, α i) f x (fun j ↦ Pi.single (v j) 1) := by
  obtain ⟨p, r, hp⟩ := hf
  let S := univ.filter fun a : Fin (∑ i, α i) → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i
  rw [hp.mvTaylorCoeff_eq, p.mvCoeff_eq_sum rfl, hp.iteratedFDeriv_eq_sum_of_completeSpace]
  -- Group permutations `σ` by the rearranged coordinate tuple `v ∘ σ ∈ S`.
  have hmaps (σ : Equiv.Perm (Fin (∑ i, α i))) : v ∘ σ ∈ S := by
    rw [mem_filter]
    refine ⟨mem_univ _, fun i ↦ ?_⟩
    rw [← hv i, ← Fintype.card_subtype]
    exact Fintype.card_congr (σ.subtypeEquiv fun _ ↦ Iff.rfl)
  rw [← sum_fiberwise_of_maps_to (fun σ _ ↦ hmaps σ), smul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  have hconst : ∀ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a),
      p (∑ i, α i) (fun j ↦ Pi.single (v (σ j)) 1) =
        p (∑ i, α i) (fun j ↦ Pi.single (a j) 1) :=
    fun σ hσ ↦ congrArg (p (∑ i, α i)) (funext fun j ↦ by simp [← congrFun (mem_filter.1 hσ).2 j])
  rw [sum_congr rfl hconst, sum_const]
  congr 1
  -- Every fiber `v ∘ σ = a` is a coset of the stabilizer `{τ | v ∘ τ = v}`, of size `∏ i, (α i)!`.
  have ha_card : ∀ i, Fintype.card {j // a j = i} = Fintype.card {j // v j = i} := fun i ↦ by
    rw [(mem_filter.1 ha).2 i, Fintype.card_subtype, hv i]
  let σ₀ : Equiv.Perm (Fin (∑ i, α i)) :=
    Equiv.ofFiberEquiv fun i ↦ Fintype.equivOfCardEq (ha_card i)
  have hσ₀ : v ∘ σ₀ = a := funext (Equiv.ofFiberEquiv_map _)
  have hcoset : Fintype.card {σ : Equiv.Perm (Fin (∑ i, α i)) // v ∘ σ = a} =
      Fintype.card {τ : Equiv.Perm (Fin (∑ i, α i)) // v ∘ τ = v} := by
    refine Fintype.card_congr ((Equiv.mulRight σ₀⁻¹).subtypeEquiv fun σ ↦ ?_)
    rw [← hσ₀, funext_iff, funext_iff]
    refine ⟨fun h j ↦ ?_, fun h j ↦ ?_⟩
    · simpa [Equiv.Perm.mul_apply] using h (σ₀⁻¹ j)
    · simpa [Equiv.Perm.mul_apply] using h (σ₀ j)
  rw [← Fintype.card_subtype, hcoset, DomMulAct.stabilizer_card]
  exact prod_congr rfl fun i _ ↦ by rw [Fintype.card_subtype, hv i]

/-- **Norm bound in terms of `iteratedFDeriv`**: for `f` analytic at `x`,
`‖(∏ i, (α i)!) • mvTaylorCoeff f x α‖` is at most the operator norm of the `(∑ i, α i)`-th
iterated Fréchet derivative of `f` at `x`. -/
theorem norm_prod_factorial_smul_mvTaylorCoeff_le [CompleteSpace F]
    {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    ‖(∏ i, (α i).factorial) • mvTaylorCoeff f x α‖ ≤ ‖iteratedFDeriv 𝕜 (∑ i, α i) f x‖ := by
  classical
  obtain ⟨v, hv⟩ :=
    TauCeti.exists_forall_card_filter_eq (α := Fin (∑ i, α i)) (Fintype.card_fin _).symm
  rw [hf.prod_factorial_smul_mvTaylorCoeff α v hv]
  simpa [Pi.norm_single] using
    (iteratedFDeriv 𝕜 (∑ i, α i) f x).le_opNorm fun j ↦ Pi.single (v j) (1 : 𝕜)

/-- **One-variable iterated derivative formula**: when `ι` has a unique element, `(α default)!`
times the multi-index Taylor coefficient of `z ↦ f (z default)` is `iteratedDeriv (α default) f x`.
No factorial is inverted, so this holds in every characteristic. -/
theorem factorial_smul_mvTaylorCoeff_of_unique [Unique ι] [CompleteSpace F]
    {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    (α default).factorial • mvTaylorCoeff (fun z : ι → 𝕜 ↦ f (z default)) (fun _ ↦ x) α =
      iteratedDeriv (α default) f x := by
  let L : (ι → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj default
  let s : 𝕜 →L[𝕜] (ι → 𝕜) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id 𝕜 𝕜
  have hfL : AnalyticAt 𝕜 (f ∘ L) (fun _ ↦ x) := hf.compContinuousLinearMap
  have hv : ∀ i : ι, (univ.filter fun _ : Fin (∑ j, α j) ↦ default = i).card = α i := fun i ↦ by
    rw [Subsingleton.elim i default]
    simp
  have hmain := hfL.prod_factorial_smul_mvTaylorCoeff α (fun _ ↦ default) hv
  rw [Fintype.prod_unique] at hmain
  have hcomp : (fun z : ι → 𝕜 ↦ f (z default)) = f ∘ L := by
    ext
    simp [L]
  have hLs : Function.RightInverse s L := fun y ↦ by
    simp [L, s]
  rw [hcomp, hmain,
    L.iteratedFDeriv_comp_right_of_rightInverse s hLs f (fun _ ↦ x),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have harg : (fun _ : Fin (∑ i, α i) ↦ L (Pi.single default (1 : 𝕜))) = fun _ ↦ 1 := by
    ext
    simp [L]
  rw [harg, ContinuousLinearMap.proj_apply, ← iteratedDeriv_eq_iteratedFDeriv,
    Fintype.sum_unique]

end AnalyticAt

namespace TauCeti

/-- **Constant functions**: at any point `x`, the Taylor coefficient of a constant function `c` is
`c` at `0` and `0` at every nonzero multi-index. -/
@[simp]
theorem mvTaylorCoeff_const (c : F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun _ ↦ c) x α = if α = 0 then c else 0 := by
  simp [(hasFPowerSeriesAt_const (c := c) (e := x)).mvTaylorCoeff_eq]

/-- Every Taylor coefficient of the zero function is `0`. -/
@[simp]
theorem mvTaylorCoeff_zero (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (0 : (ι → 𝕜) → F) x α = 0 := by
  rw [Pi.zero_def, mvTaylorCoeff_const, ite_self]

/-- The Taylor coefficient of the constant function `1` is `1` at `0` and `0` elsewhere. -/
@[simp]
theorem mvTaylorCoeff_one [One F] (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (1 : (ι → 𝕜) → F) x α = if α = 0 then 1 else 0 := by
  rw [Pi.one_def, mvTaylorCoeff_const]

/-- **Constant scalar multiples** commute with `mvTaylorCoeff` unconditionally (whether or not `f`
is analytic at `x`). -/
@[to_fun (attr := simp) mvTaylorCoeff_fun_const_smul, simp]
theorem mvTaylorCoeff_const_smul (c : 𝕜) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (c • f) x α = c • mvTaylorCoeff f x α := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [zero_smul]
  · by_cases hf : AnalyticAt 𝕜 f x
    · obtain ⟨p, hp⟩ := hf
      rw [(hp.const_smul (c := c)).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq, p.mvCoeff_smul]
    · have hcf : ¬ AnalyticAt 𝕜 (c • f) x := fun h ↦ by
        have h' := h.const_smul (c := c⁻¹)
        exact hf (by simpa [inv_smul_smul₀ hc] using h')
      rw [mvTaylorCoeff_of_not_analyticAt hcf, mvTaylorCoeff_of_not_analyticAt hf, smul_zero]

/-- Negation commutes with `mvTaylorCoeff` unconditionally. -/
@[to_fun (attr := simp) mvTaylorCoeff_fun_neg, simp]
theorem mvTaylorCoeff_neg (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (-f) x α = -mvTaylorCoeff f x α := by
  simpa using mvTaylorCoeff_const_smul (-1 : 𝕜) f x α

/-- Taylor coefficients commute with finite sums of functions analytic at `x`. -/
@[to_fun mvTaylorCoeff_fun_sum]
theorem mvTaylorCoeff_sum {κ : Type*} (s : Finset κ) {f : κ → (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : ∀ j ∈ s, AnalyticAt 𝕜 (f j) x) (α : ι → ℕ) :
    mvTaylorCoeff (∑ j ∈ s, f j) x α = ∑ j ∈ s, mvTaylorCoeff (f j) x α := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have ha_an : AnalyticAt 𝕜 (f a) x := hf a (mem_insert_self a s)
    have hs_an : ∀ j ∈ s, AnalyticAt 𝕜 (f j) x := fun j hj ↦ hf j (mem_insert_of_mem hj)
    have hsum_an : AnalyticAt 𝕜 (∑ j ∈ s, f j) x := Finset.analyticAt_sum s hs_an
    rw [sum_insert ha, sum_insert ha, ha_an.mvTaylorCoeff_add hsum_an, ih hs_an]

/-- **Translation invariance** on the right: expanding `z ↦ f (z + y)` around `x` gives the Taylor
coefficients of `f` around `x + y`, whether or not `f` is analytic at `x + y`. -/
@[simp]
theorem mvTaylorCoeff_comp_add_right (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (z + y)) x α = mvTaylorCoeff f (x + y) α := by
  by_cases hf : AnalyticAt 𝕜 f (x + y)
  · obtain ⟨p, hp⟩ := hf
    have hp' : HasFPowerSeriesAt (fun z ↦ f (z + y)) p x := by
      simpa using hp.comp_sub (-y)
    rw [hp'.mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq]
  · have hg : ¬ AnalyticAt 𝕜 (fun z ↦ f (z + y)) x := fun hg ↦
      hf (by simpa using hg.comp_sub y)
    rw [mvTaylorCoeff_of_not_analyticAt hg, mvTaylorCoeff_of_not_analyticAt hf]

/-- **Translation invariance** on the left: expanding `z ↦ f (y + z)` around `x` gives the Taylor
coefficients of `f` around `y + x`. -/
@[simp]
theorem mvTaylorCoeff_comp_add_left (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (y + z)) x α = mvTaylorCoeff f (y + x) α := by
  simpa [add_comm] using mvTaylorCoeff_comp_add_right f x y α

/-- **Translation invariance** under subtraction: expanding `z ↦ f (z - y)` around `x` gives the
Taylor coefficients of `f` around `x - y`, whether or not `f` is analytic at `x - y`. -/
@[simp]
theorem mvTaylorCoeff_comp_sub (f : (ι → 𝕜) → F) (x y : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z ↦ f (z - y)) x α = mvTaylorCoeff f (x - y) α := by
  simpa only [sub_eq_add_neg] using mvTaylorCoeff_comp_add_right f x (-y) α

/-- **Coefficients from an expansion**: if `c` is normally summable on a polydisc of positive
radius `ρ` and `(∏ i, y i ^ α i) • c α` has sum `f (x + y)` for `‖y‖ < ρ`, then `c` is the family
of Taylor coefficients of `f` at `x`. No completeness assumption on `F` is needed. -/
theorem mvTaylorCoeff_eq_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (ρ : ℝ) ^ (∑ i, α i))
    (h : ∀ y : ι → 𝕜, ‖y‖ < ρ →
      HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y)))
    (α : ι → ℕ) : mvTaylorCoeff f x α = c α := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_of_hasSum hρ hsum h
  rw [hp.mvTaylorCoeff_eq, hpc]

/-- **Monomial with a vector coefficient**: at the origin, `z ↦ (∏ i, z i ^ τ i) • v` has Taylor
coefficient `v` at `τ` and `0` at every other multi-index. -/
@[simp]
theorem mvTaylorCoeff_prod_pow_smul (τ : ι → ℕ) (v : F) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ (∏ i, z i ^ τ i) • v) 0 α = if α = τ then v else 0 := by
  let c : (ι → ℕ) → F := fun β ↦ if β = τ then v else 0
  refine mvTaylorCoeff_eq_of_hasSum (c := c) zero_lt_one ?_ (fun y _ ↦ ?_) α
  · refine summable_of_ne_finset_zero (s := {τ}) fun β hβ ↦ ?_
    simp [c, mem_singleton.not.1 hβ]
  · simpa [c] using hasSum_single τ (f := fun β ↦ (∏ i, y i ^ β i) • c β) fun β hβ ↦ by simp [c, hβ]

/-- **Scalar monomial**: at the origin, `z ↦ ∏ i, z i ^ τ i` has Taylor coefficient `1` at `τ`
and `0` at every other multi-index. -/
@[simp]
theorem mvTaylorCoeff_prod_pow (τ α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ ∏ i, z i ^ τ i) 0 α = if α = τ then 1 else 0 := by
  simpa using mvTaylorCoeff_prod_pow_smul (𝕜 := 𝕜) τ (1 : 𝕜) α

/-- **Centered monomial with a vector coefficient**: around `x`,
`z ↦ (∏ i, (z i - x i) ^ τ i) • v` has Taylor coefficient `v` at `τ` and `0` at every other
multi-index. -/
@[simp]
theorem mvTaylorCoeff_prod_sub_pow_smul (τ : ι → ℕ) (x : ι → 𝕜) (v : F) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ (∏ i, (z i - x i) ^ τ i) • v) x α =
      if α = τ then v else 0 := by
  let g : (ι → 𝕜) → F := fun w ↦ (∏ i, w i ^ τ i) • v
  have h : (fun z : ι → 𝕜 ↦ (∏ i, (z i - x i) ^ τ i) • v) = fun z ↦ g (z - x) := by
    ext z
    simp [g]
  rw [h, mvTaylorCoeff_comp_sub, sub_self]
  exact mvTaylorCoeff_prod_pow_smul τ v α

/-- **Centered scalar monomial**: around `x`, `z ↦ ∏ i, (z i - x i) ^ τ i` has Taylor coefficient
`1` at `τ` and `0` at every other multi-index. -/
@[simp]
theorem mvTaylorCoeff_prod_sub_pow (τ : ι → ℕ) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ ∏ i, (z i - x i) ^ τ i) x α = if α = τ then 1 else 0 := by
  simpa using mvTaylorCoeff_prod_sub_pow_smul (𝕜 := 𝕜) τ x (1 : 𝕜) α

/-- **Coordinate projections**: the Taylor coefficient of `z ↦ z i` at `x` is `1` at
`Pi.single i 1`, `x i` at `0`, and `0` at every other multi-index. -/
@[simp]
theorem mvTaylorCoeff_apply [DecidableEq ι] (i : ι) (x : ι → 𝕜) (α : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → 𝕜 ↦ z i) x α =
      if α = Pi.single i 1 then 1 else if α = 0 then x i else 0 := by
  rw [← zero_add x, ← mvTaylorCoeff_comp_add_right]
  have hproj_eq : ∀ z : ι → 𝕜, ∏ j, z j ^ (Pi.single i 1 : ι → ℕ) j = z i := fun z ↦ by
    rw [Fintype.prod_eq_single i fun j hj ↦ by simp [Pi.single_eq_of_ne hj]]
    simp
  have hfn : (fun z : ι → 𝕜 ↦ (z + x) i) =
      (fun _ : ι → 𝕜 ↦ x i) + fun z : ι → 𝕜 ↦ ∏ j, z j ^ (Pi.single i 1 : ι → ℕ) j := by
    ext z
    simp [hproj_eq, add_comm]
  have hproj : AnalyticAt 𝕜 (fun z : ι → 𝕜 ↦ ∏ j, z j ^ (Pi.single i 1 : ι → ℕ) j) 0 :=
    ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt 0).congr
      (Eventually.of_forall fun z ↦ by simp [hproj_eq])
  rw [hfn, analyticAt_const.mvTaylorCoeff_add hproj, mvTaylorCoeff_const, mvTaylorCoeff_prod_pow]
  split_ifs <;> simp_all

end TauCeti

section ProductRule

omit [Fintype ι] in
/-- Bijection grouping pairs `(β, γ)` of multi-indices by their sum `α = β + γ` and `β ∈ Iic α`. -/
private def sigmaIicEquiv [DecidableEq ι] :
    (Σ α : ι → ℕ, {β // β ∈ Iic α}) ≃ (ι → ℕ) × (ι → ℕ) where
  toFun x := (x.2.1, x.1 - x.2.1)
  invFun p := ⟨p.1 + p.2, ⟨p.1, mem_Iic.2 le_self_add⟩⟩
  left_inv := by
    rintro ⟨α, β, hβ⟩
    exact Sigma.subtype_ext (funext fun i ↦ add_tsub_cancel_of_le (mem_Iic.1 hβ i)) rfl
  right_inv p := by
    ext <;> simp

/-- Normal summability at radius `ρ` is preserved under Cauchy convolution over `Finset.Iic`. -/
private theorem summable_norm_cauchy_mul_pow {A G : Type*} [NormedRing A] [NormedAddCommGroup G]
    [Module A G] [IsBoundedSMul A G] [DecidableEq ι] {a : (ι → ℕ) → A} {b : (ι → ℕ) → G} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (ha : Summable fun β : ι → ℕ ↦ ‖a β‖ * ρ ^ (∑ i, β i))
    (hb : Summable fun γ : ι → ℕ ↦ ‖b γ‖ * ρ ^ (∑ i, γ i)) :
    Summable fun ν : ι → ℕ ↦ ‖∑ β ∈ Iic ν, a β • b (ν - β)‖ * ρ ^ (∑ i, ν i) := by
  have hprod := ha.mul_of_nonneg hb (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  have hsig := ((sigmaIicEquiv (ι := ι)).summable_iff.2 hprod).sigma
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun ν ↦ ?_) hsig
  calc ‖∑ β ∈ Iic ν, a β • b (ν - β)‖ * ρ ^ (∑ i, ν i)
      ≤ (∑ β ∈ Iic ν, ‖a β‖ * ‖b (ν - β)‖) * ρ ^ (∑ i, ν i) := by
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_smul_le _ _)
    _ = ∑ β ∈ Iic ν, (‖a β‖ * ρ ^ (∑ i, β i)) * (‖b (ν - β)‖ * ρ ^ (∑ i, (ν - β) i)) := by
        rw [sum_mul]
        refine sum_congr rfl fun β hβ ↦ ?_
        have hdeg : ∑ i, β i + ∑ i, (ν - β) i = ∑ i, ν i := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun i _ ↦ add_tsub_cancel_of_le (mem_Iic.1 hβ i)
        rw [← hdeg, pow_add]
        ring
    _ = ∑ x : {β // β ∈ Iic ν},
          (‖a x.1‖ * ρ ^ (∑ i, x.1 i)) * (‖b (ν - x.1)‖ * ρ ^ (∑ i, (ν - x.1) i)) :=
        (sum_coe_sort (Iic ν) fun β ↦
          (‖a β‖ * ρ ^ (∑ i, β i)) * (‖b (ν - β)‖ * ρ ^ (∑ i, (ν - β) i))).symm
    _ = _ := (tsum_fintype _).symm

/-- Grouping the Cauchy product along `sigmaIicEquiv` evaluates the convolved multi-index series on
`‖y‖ ≤ ρ`. -/
private theorem hasSum_prod_pow_smul_cauchy {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] [DecidableEq ι]
    {a : (ι → ℕ) → A} {b : (ι → ℕ) → F} {ρ : ℝ} {y : ι → 𝕜} {u : A} {v : F}
    (ha : Summable fun β : ι → ℕ ↦ ‖a β‖ * ρ ^ (∑ i, β i))
    (hb : Summable fun γ : ι → ℕ ↦ ‖b γ‖ * ρ ^ (∑ i, γ i)) (hy : ‖y‖ ≤ ρ)
    (hu : HasSum (fun β : ι → ℕ ↦ (∏ i, y i ^ β i) • a β) u)
    (hv : HasSum (fun γ : ι → ℕ ↦ (∏ i, y i ^ γ i) • b γ) v) :
    HasSum (fun ν : ι → ℕ ↦ (∏ i, y i ^ ν i) • ∑ β ∈ Iic ν, a β • b (ν - β)) (u • v) := by
  have hu_norm := TauCeti.summable_norm_prod_pow_smul_of_le ha hy
  have hv_norm := TauCeti.summable_norm_prod_pow_smul_of_le hb hy
  have hprod := hu.smul_of_summable_norm hv hu_norm hv_norm
  refine ((sigmaIicEquiv (ι := ι)).hasSum_iff.2 hprod).sigma fun ν ↦ ?_
  have hfib : (∏ i, y i ^ ν i) • ∑ β ∈ Iic ν, a β • b (ν - β) =
      ∑ β : {β // β ∈ Iic ν},
        ((∏ i, y i ^ β.1 i) • a β.1) • ((∏ i, y i ^ (ν - β.1) i) • b (ν - β.1)) := by
    rw [sum_coe_sort (Iic ν) fun β ↦
      ((∏ i, y i ^ β i) • a β) • ((∏ i, y i ^ (ν - β) i) • b (ν - β)), smul_sum]
    refine sum_congr rfl fun β hβ ↦ ?_
    have hpow : (∏ i, y i ^ β i) * (∏ i, y i ^ (ν - β) i) = ∏ i, y i ^ ν i := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ ↦ by
        rw [← pow_add, Pi.sub_apply, add_tsub_cancel_of_le (mem_Iic.1 hβ i)]
    have hcomm : a β • ((∏ i, y i ^ (ν - β) i) • b (ν - β)) =
        (∏ i, y i ^ (ν - β) i) • (a β • b (ν - β)) := by
      rw [← IsScalarTower.algebraMap_smul A (∏ i, y i ^ (ν - β) i) (b (ν - β)), ← mul_smul,
        ← Algebra.commutes, mul_smul, IsScalarTower.algebraMap_smul]
    rw [smul_assoc (∏ i, y i ^ β i) (a β), hcomm, smul_smul, hpow]
  rw [hfib]
  exact hasSum_fintype _

namespace AnalyticAt

open TauCeti

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- **Product rule for Taylor coefficients**: for an algebra-valued function `f : (ι → 𝕜) → A` and
a module-valued function `g : (ι → 𝕜) → F`, both analytic at `x`, the Taylor coefficient of `f • g`
at `α` is the Cauchy sum `∑ β ∈ Iic α, mvTaylorCoeff f x β • mvTaylorCoeff g x (α - β)`. No
completeness assumption on `F` is needed. -/
@[to_fun mvTaylorCoeff_fun_smul]
theorem mvTaylorCoeff_smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] [DecidableEq ι]
    {f : (ι → 𝕜) → A} {g : (ι → 𝕜) → F} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f • g) x α =
      ∑ β ∈ Iic α, mvTaylorCoeff f x β • mvTaylorCoeff g x (α - β) := by
  obtain ⟨ρ₁, hρ₁, hsum₁, hexp₁⟩ := hf.exists_hasSum_mvTaylorCoeff
  obtain ⟨ρ₂, hρ₂, hsum₂, hexp₂⟩ := hg.exists_hasSum_mvTaylorCoeff
  let ρ : ℝ≥0 := min ρ₁ ρ₂
  have hfρ : Summable fun β : ι → ℕ ↦ ‖mvTaylorCoeff f x β‖ * (ρ : ℝ) ^ (∑ i, β i) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun _ ↦ by gcongr; exact_mod_cast min_le_left ρ₁ ρ₂) hsum₁
  have hgρ : Summable fun γ : ι → ℕ ↦ ‖mvTaylorCoeff g x γ‖ * (ρ : ℝ) ^ (∑ i, γ i) :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun _ ↦ by gcongr; exact_mod_cast min_le_right ρ₁ ρ₂) hsum₂
  refine mvTaylorCoeff_eq_of_hasSum (lt_min hρ₁ hρ₂)
    (summable_norm_cauchy_mul_pow ρ.coe_nonneg hfρ hgρ) (fun y hy ↦ ?_) α
  exact hasSum_prod_pow_smul_cauchy hfρ hgρ hy.le
    (hexp₁ y (hy.trans_le (by exact_mod_cast min_le_left ρ₁ ρ₂)))
    (hexp₂ y (hy.trans_le (by exact_mod_cast min_le_right ρ₁ ρ₂)))

/-- **Product rule for algebra-valued analytic functions**: the Taylor coefficient of `f * g` at
`α` is `∑ β ∈ Iic α, mvTaylorCoeff f x β * mvTaylorCoeff g x (α - β)`. -/
@[to_fun mvTaylorCoeff_fun_mul]
theorem mvTaylorCoeff_mul [DecidableEq ι] {f g : (ι → 𝕜) → A} {x : ι → 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) (α : ι → ℕ) :
    mvTaylorCoeff (f * g) x α =
      ∑ β ∈ Iic α, mvTaylorCoeff f x β * mvTaylorCoeff g x (α - β) :=
  hf.mvTaylorCoeff_smul hg α

end Algebra

end AnalyticAt

end ProductRule

/-- Postcomposition with a continuous linear map commutes with `mvTaylorCoeff` for functions
analytic at `x`. -/
@[to_fun ContinuousLinearMap.mvTaylorCoeff_fun_comp_left]
theorem ContinuousLinearMap.mvTaylorCoeff_comp_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (g : F →L[𝕜] G) {f : (ι → 𝕜) → F} {x : ι → 𝕜} (hf : AnalyticAt 𝕜 f x) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (g ∘ f) x α = g (TauCeti.mvTaylorCoeff f x α) := by
  obtain ⟨p, r, hp⟩ := hf
  rw [(g.comp_hasFPowerSeriesOnBall hp).mvTaylorCoeff_eq, hp.mvTaylorCoeff_eq,
    g.mvCoeff_compFormalMultilinearSeries]

/-- Postcomposition with a continuous linear equivalence commutes with `mvTaylorCoeff`
unconditionally (whether or not `f` is analytic at `x`). -/
@[to_fun (attr := simp) ContinuousLinearEquiv.mvTaylorCoeff_fun_comp_left, simp]
theorem ContinuousLinearEquiv.mvTaylorCoeff_comp_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (g : F ≃L[𝕜] G) (f : (ι → 𝕜) → F) (x : ι → 𝕜) (α : ι → ℕ) :
    TauCeti.mvTaylorCoeff (g ∘ f) x α = g (TauCeti.mvTaylorCoeff f x α) := by
  by_cases hf : AnalyticAt 𝕜 f x
  · exact (g : F →L[𝕜] G).mvTaylorCoeff_comp_left hf α
  · have hgf : ¬ AnalyticAt 𝕜 (g ∘ f) x := fun h ↦ hf <|
      (((g.symm : G →L[𝕜] F).analyticAt _).comp h).congr (Eventually.of_forall fun y ↦ by simp)
    rw [TauCeti.mvTaylorCoeff_of_not_analyticAt hgf, TauCeti.mvTaylorCoeff_of_not_analyticAt hf,
      map_zero]

/-- **Linear change of variables preserves vanishing in each total degree**: if `G` is analytic at
`A x` for a continuous linear map `A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)` and every Taylor coefficient of `G`
at `A x` of total degree `k` vanishes, then every Taylor coefficient of `G ∘ A` at `x` of total
degree `k` vanishes. -/
theorem ContinuousLinearMap.mvTaylorCoeff_comp_eq_zero {κ : Type*} [Fintype κ] {G : (ι → 𝕜) → F}
    (A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) {x : κ → 𝕜} (hG : AnalyticAt 𝕜 G (A x)) {k : ℕ}
    (h : ∀ α : ι → ℕ, ∑ i, α i = k → TauCeti.mvTaylorCoeff G (A x) α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → TauCeti.mvTaylorCoeff (G ∘ A) x β = 0 := by
  classical
  obtain ⟨p, hp⟩ := hG
  have hpA : HasFPowerSeriesAt (G ∘ A) (p.compContinuousLinearMap A) x :=
    hp.compContinuousLinearMap
  intro β hβ
  rw [hpA.mvTaylorCoeff_eq]
  refine TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero (fun w : κ → 𝕜 ↦ ?_)
    (mem_piAntidiag.2 ⟨hβ, by simp⟩)
  rw [← (p.compContinuousLinearMap A).apply_eq_sum_mvCoeff,
    FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def,
    p.apply_eq_sum_mvCoeff]
  refine sum_eq_zero fun α hα ↦ ?_
  have h0 : p.mvCoeff α = 0 := by
    rw [← hp.mvTaylorCoeff_eq]
    exact h α (mem_piAntidiag.1 hα).1
  simp [h0]
