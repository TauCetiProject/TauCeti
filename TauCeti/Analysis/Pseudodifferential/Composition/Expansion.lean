/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.Inversion
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The asymptotic expansion of the composition symbol

Let `a` be a symbol of order `m'` with values in `W →L[ℂ] U` and `b` a symbol of order `m` with
values in `V →L[ℂ] W` that vanishes for positions outside a compact set. Their composition symbol
`a # b` (`TauCeti.Symbol.sharp`), whose quantization is `Op(a) ∘ Op(b)`, has the asymptotic
expansion

`a # b ∼ ∑_α (1 / α!) ∂_ξ^α a · D_x^α b`, with `D_x = -i ∂_x`,

meaning that after removing the terms with `|α| < N` the remainder is a symbol of order
`m' + m - N`. This file proves this, with an actual remainder symbol.

Summing over words `w = [j₁, …, j_k]` of coordinate indices instead of multi-indices absorbs the
multinomial coefficients, so the term of order `m' + m - k` is

`TauCeti.Symbol.sharpTerm a b k = ((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`

(`TauCeti.Symbol.coefficient_sharpTerm`). It is defined for arbitrary symbols `a`, `b` by the
recursion `sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting
from the pointwise composition `sharpTerm a b 0 = a ∘ b`, and it satisfies the Leibniz rules in
the position and the frequency.

## Main results

* `TauCeti.Symbol.sharpTerm`: the terms of the expansion, with their closed form
  `TauCeti.Symbol.coefficient_sharpTerm`, the first correction term
  `TauCeti.Symbol.coefficient_sharpTerm_one` (`-i ∑ⱼ ∂_{ξⱼ} a ∘ ∂_{xⱼ} b`) and the Leibniz rules
  `TauCeti.Symbol.spatialDeriv_sharpTerm` and `TauCeti.Symbol.coefficient_frequencyDeriv_sharpTerm`.
  The coefficients of the terms only depend on the coefficients of the two symbols
  (`TauCeti.Symbol.coefficient_sharpTerm_congr`) and depend linearly on each of them, also for
  linear combinations of symbols of different orders
  (`TauCeti.Symbol.coefficient_sharpTerm_eq_sum_left` and its companions), and near a point
  only on their values near that point
  (`TauCeti.Symbol.coefficient_sharpTerm_of_eq_smul_of_eventuallyEq`). For a constant symbol
  only the pointwise composition survives (`TauCeti.Symbol.const_sharpTerm_succ`,
  `TauCeti.Symbol.sharpTerm_const_succ`), and on the right this holds for every symbol that does
  not depend on the position (`TauCeti.Symbol.sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero`).
* `TauCeti.Symbol.sharpRemainder a b hb N`: the remainder `a # b - ∑_{k < N} sharpTerm a b k`, a
  symbol of order `m' + m - N`.
* `TauCeti.Symbol.sharp_eq_sum_sharpTerm_add_sharpRemainder`: **the composition expansion**
  `a # b = ∑_{k < N} sharpTerm a b k + sharpRemainder a b hb N`, for every `N`.
* `TauCeti.Symbol.IsUniform.exists_norm_coefficient_sharpRemainder_le`: **uniform remainders for a
  family**. For a uniform `a` and symbols `bᵢ` with compact spatial support whose position slices
  have Fourier transforms decaying uniformly in `i`, the remainders after `N` terms are bounded by
  `C ⟨ξ⟩ ^ (m' + m - N)` with `C` independent of `i` and of the position. The remainders satisfy
  the Leibniz rules `TauCeti.Symbol.spatialDeriv_sharpRemainder` and
  `TauCeti.Symbol.coefficient_frequencyDeriv_sharpRemainder`.
* `TauCeti.Symbol.coordSub_smul_coefficient_sharpTerm_succ`,
  `TauCeti.Symbol.coordSub_smul_coefficient_sharpRemainder`: **commutators with a coordinate
  function**. The terms and the remainders of the expansion satisfy the identity
  `(x - z)ⱼ (a # b) = a # ((y - z)ⱼ b) + i (∂_{ξⱼ} a) # b` of `TauCeti.Symbol.sharp` with the index
  of the last term lowered by one; for the remainders `R_N`,
  `(x - z)ⱼ R_N(a, b) = R_N(a, (y - z)ⱼ b) + i R_{N-1}(∂_{ξⱼ} a, b)`.
* `TauCeti.Symbol.sharp_eq_comp_add_sharpRemainder_one`: in particular `a # b` agrees with the
  pointwise composition `a ∘ b` up to a symbol of order `m' + m - 1`.
* `TauCeti.Symbol.IsUniform.sharpTerm`, `TauCeti.Symbol.IsUniform.sharpRemainder`: **the uniform
  expansion**. If the estimates of `a` and `b` hold uniformly in the position, then so do those of
  every term of the expansion. If those of `a` do and `b` has compact spatial support (hence is
  uniform, `TauCeti.Symbol.HasCompactSpatialSupport.isUniform`), then so do those of every
  remainder, so the expansion holds in the uniform symbol classes.
* `TauCeti.Symbol.isSmoothing_sharp_sub_comp`: if `a` vanishes outside `K` and `b` does not depend
  on the position near `K`, then `a # b` and `a ∘ b` differ by a smoothing symbol.
* `TauCeti.Symbol.isAsymptoticSum_sharp`: `a # b ∼ ∑ₖ sharpTerm a b k` as an asymptotic sum
  (`TauCeti.Symbol.IsAsymptoticSum`), so the terms determine `a # b` modulo smoothing symbols.
* `TauCeti.Symbol.exists_coefficient_eq_sharp_sub_sharp`: if `a` and `b` both have compact
  spatial support and their values commute pointwise, for instance for scalar symbols, the
  commutator symbol `a # b - b # a` has order `m' + m - 1`.
* `TauCeti.Symbol.exists_coefficient_eq_sharp_sub_sharp_sub_commutator`: **the commutator
  expansion**. In general `a # b - b # a` is
  `[a, b] - i ∑ⱼ (∂_{ξⱼ} a ∘ ∂_{xⱼ} b - ∂_{ξⱼ} b ∘ ∂_{xⱼ} a)` up to a symbol of order
  `m' + m - 2`, where `[a, b]` is the pointwise commutator.
* `TauCeti.Symbol.exists_coefficient_eq_sharp_sub_sharp_add_poissonBracket`: if every value of `a`
  commutes with every value of `b`, for instance if one of them is scalar, then
  `a # b - b # a = -i {a, b}` up to a symbol of order `m' + m - 2`, where
  `{a, b} = ∑ⱼ (∂_{ξⱼ} a ∘ ∂_{xⱼ} b - ∂_{xⱼ} a ∘ ∂_{ξⱼ} b)` is the Poisson bracket.
* `TauCeti.ClassicalSymbol.exists_sharp_sub_cutoffSymbol_principal_comp`: **the principal symbol
  of a composition**. For classical `a` and `b`, the symbol `a # b` differs from the cut-off
  composition `χ(ξ) (σ(a) ∘ σ(b))` of the principal symbols by a symbol of order `m' + m - 1`.

The spaces `W` and `U` are complete: `U` for the Bochner integral defining `a # b`, which is zero
by convention otherwise, and `W` for the Fourier inversion of `b̂` that identifies the `t = 0`
member of the interpolating family below with `a ∘ b`.

## Proof outline

Interpolate between the pointwise composition and the composition symbol by the family

`(a #_t b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2π t η) ∘ b̂(η, ξ) dη`, `t ∈ [0, 1]`,

so that `a #_1 b = a # b`, and `a #_0 b = a ∘ b` by Fourier inversion. Differentiating under the
integral sign, and using `2π ηⱼ b̂ = -i (∂_{xⱼ} b)^`,
`d/dt (a #_t b) = -i ∑ⱼ (∂_{ξⱼ} a) #_t (∂_{xⱼ} b)`. The recursion defining `sharpTerm` is the
matching identity for the polynomial `∑_{k < N} t^k sharpTerm a b k`. So the derivative of the
remainder `a #_t b - ∑_{k < N + 1} t^k sharpTerm a b k` is `-i` times the sum over `j` of the
remainders with `N` terms of `(∂_{ξⱼ} a, ∂_{xⱼ} b)`, and this remainder vanishes at `t = 0`.
By induction on `N` and the mean value inequality on `[0, 1]`, the remainder is bounded by
`C ⟨ξ⟩ ^ (m' + m - N)`, locally uniformly in the position, and uniformly if the estimates of `a`
are: each step lowers the order of `a` by one. The base case is the bound
`‖a #_t b‖ ≤ C ⟨ξ⟩ ^ (m' + m)`, uniform for `|t| ≤ 2` by Peetre's inequality and the rapid decay
of `b̂` (`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_integral_sharpIntegrand_le`, for the
integrand `TauCeti.Symbol.sharpIntegrand a b (2πt)` of `a #_t b`).

The derivative estimates follow from the Leibniz rules, which hold for `a # b` and for each
`sharpTerm`: a position or frequency derivative of the remainder is the sum of the remainders
with the derivative on `a` or on `b`, and a frequency derivative lowers the order of one factor.
An induction on the number of derivatives then gives every symbol estimate of order
`m' + m - N` (`TauCeti.Symbol.exists_norm_mixedDeriv_le_of_leibniz`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the expansion -/

section Term

/-- The term of order `m' + m - k` in the asymptotic expansion of the composition symbol `a # b`:
`((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, the sum running over the words `w` of coordinate
indices of length `k` (`coefficient_sharpTerm`). It is defined by the recursion
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting from the
pointwise composition `sharpTerm a b 0 = a ∘ b`. -/
def sharpTerm : {m m' : ℝ} → Symbol n W U m' → Symbol n V W m → (k : ℕ) →
    Symbol n V U (m' + m - k)
  | _, _, a, b, 0 => inclusion (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

theorem sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m) :
    a.sharpTerm b 0 = inclusion (by simp) (a.comp b) := by
  rw [sharpTerm]

theorem sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    a.sharpTerm b (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

@[simp]
theorem coefficient_sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b 0).coefficient p = (a.coefficient p).comp (b.coefficient p) := by
  rw [sharpTerm_zero, coefficient_inclusion, coefficient_comp]

theorem coefficient_sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient p := by
  simp [sharpTerm_succ]

/-- The first correction term of the composition expansion is `-i ∑ⱼ ∂_{ξⱼ} a ∘ ∂_{xⱼ} b`. -/
theorem coefficient_sharpTerm_one (a : Symbol n W U m') (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b 1).coefficient p = (-Complex.I) •
      ∑ j, ((frequencyDeriv j a).coefficient p).comp ((spatialDeriv j b).coefficient p) := by
  simp [coefficient_sharpTerm_succ]

/-- **The terms of the composition expansion** are
`((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, the sum running over the words `w` of coordinate
indices of length `k`. Grouping the words by the multi-index they determine gives the familiar
form `∑_{|α| = k} (1 / α!) ∂_ξ^α a · D_x^α b` with `D_x = -i ∂_x`. -/
theorem coefficient_sharpTerm (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (x ξ : CoordinateSpace n) :
    (a.sharpTerm b k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n, (mixedDeriv [] (List.ofFn w) a.coefficient x ξ).comp
        (mixedDeriv (List.ofFn w) [] b.coefficient x ξ) := by
  induction k generalizing m m' with
  | zero => simp
  | succ k ih =>
    rw [coefficient_sharpTerm_succ, ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp,
      Fintype.sum_prod_type]
    simp only [ih, mixedDeriv_frequencyDeriv, mixedDeriv_spatialDeriv, Finset.smul_sum, smul_smul,
      Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The terms of the composition expansion only depend on the coefficients of the two symbols, not
on the orders at which the symbols are considered. -/
theorem coefficient_sharpTerm_congr {μ μ' : ℝ} {a : Symbol n W U m'} {a' : Symbol n W U μ'}
    {b : Symbol n V W m} {b' : Symbol n V W μ} (ha : a.coefficient = a'.coefficient)
    (hb : b.coefficient = b'.coefficient) (k : ℕ) :
    (a.sharpTerm b k).coefficient = (a'.sharpTerm b' k).coefficient := by
  funext ⟨x, ξ⟩
  simp only [coefficient_sharpTerm, ha, hb]

/-- **Locality of the composition expansion.** Let `ψ` be a function of the position, `a'` a
symbol with `a'(x, ξ) = ψ(x) a(x, ξ)`, and `b'` a symbol which agrees with `b` at all positions
near the support of `ψ`. Then every term of the expansion of `a' # b'` is `ψ(x)` times the
corresponding term of `a # b`. -/
theorem coefficient_sharpTerm_of_eq_smul_of_eventuallyEq {μ μ' : ℝ} {ψ : CoordinateSpace n → ℂ}
    {a : Symbol n W U m'} {a' : Symbol n W U μ'} {b : Symbol n V W m} {b' : Symbol n V W μ}
    (ha : ∀ x ξ, a'.coefficient (x, ξ) = ψ x • a.coefficient (x, ξ))
    (hb : ∀ᶠ x in nhdsSet (tsupport ψ), ∀ ξ, b'.coefficient (x, ξ) = b.coefficient (x, ξ))
    (k : ℕ) (x ξ : CoordinateSpace n) :
    (a'.sharpTerm b' k).coefficient (x, ξ) = ψ x • (a.sharpTerm b k).coefficient (x, ξ) := by
  -- The frequency derivatives of `a'` at `x` are `ψ x` times those of `a`.
  have hfreq (w : List (Fin n)) :
      mixedDeriv [] w a'.coefficient x ξ = ψ x • mixedDeriv [] w a.coefficient x ξ := by
    have h : (fun η ↦ a'.coefficient (x, η)) = ψ x • fun η ↦ a.coefficient (x, η) :=
      funext fun η ↦ ha x η
    simp only [mixedDeriv_def, coordinateDeriv_nil, h, coordinateDeriv_const_smul, Pi.smul_apply]
  simp only [coefficient_sharpTerm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [hfreq, ContinuousLinearMap.smul_comp, smul_comm (ψ x)]
  by_cases hx : x ∈ tsupport ψ
  · rw [mixedDeriv_congr_of_eventually (nhds_le_nhdsSet hx hb)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- The terms of the composition expansion are linear in the first symbol: a linear relation
`a₀ = ∑ᵢ cᵢ aᵢ` between the coefficients of symbols `aᵢ` of possibly different orders gives the
same relation `sharpTerm a₀ b k = ∑ᵢ cᵢ sharpTerm aᵢ b k` between the coefficients of the terms. -/
theorem coefficient_sharpTerm_eq_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) {μ : ι → ℝ}
    (a : (i : ι) → Symbol n W U (μ i)) {a₀ : Symbol n W U m'}
    (h : a₀.coefficient = ∑ i ∈ s, c i • (a i).coefficient) (b : Symbol n V W m) (k : ℕ) :
    (a₀.sharpTerm b k).coefficient = ∑ i ∈ s, c i • ((a i).sharpTerm b k).coefficient := by
  funext ⟨x, ξ⟩
  have hd (w : Fin k → Fin n) : mixedDeriv [] (List.ofFn w) a₀.coefficient x ξ =
      ∑ i ∈ s, c i • mixedDeriv [] (List.ofFn w) (a i).coefficient x ξ := by
    rw [h, mixedDeriv_sum (f := fun i ↦ c i • (a i).coefficient)
      fun i _ ↦ (a i).contDiff_coefficient.const_smul (c i)]
    exact Finset.sum_congr rfl fun i _ ↦ mixedDeriv_const_smul _ _ _ _ _
  simp only [Finset.sum_apply, Pi.smul_apply, coefficient_sharpTerm, hd,
    ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.smul_comp, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦ smul_comm _ _ _

/-- The terms of the composition expansion are linear in the second symbol: a linear relation
`b₀ = ∑ᵢ cᵢ bᵢ` between the coefficients of symbols `bᵢ` of possibly different orders gives the
same relation `sharpTerm a b₀ k = ∑ᵢ cᵢ sharpTerm a bᵢ k` between the coefficients of the terms. -/
theorem coefficient_sharpTerm_eq_sum_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) {μ : ι → ℝ}
    (b : (i : ι) → Symbol n V W (μ i)) {b₀ : Symbol n V W m}
    (h : b₀.coefficient = ∑ i ∈ s, c i • (b i).coefficient) (a : Symbol n W U m') (k : ℕ) :
    (a.sharpTerm b₀ k).coefficient = ∑ i ∈ s, c i • (a.sharpTerm (b i) k).coefficient := by
  funext ⟨x, ξ⟩
  have hd (w : Fin k → Fin n) : mixedDeriv (List.ofFn w) [] b₀.coefficient x ξ =
      ∑ i ∈ s, c i • mixedDeriv (List.ofFn w) [] (b i).coefficient x ξ := by
    rw [h, mixedDeriv_sum (f := fun i ↦ c i • (b i).coefficient)
      fun i _ ↦ (b i).contDiff_coefficient.const_smul (c i)]
    exact Finset.sum_congr rfl fun i _ ↦ mixedDeriv_const_smul _ _ _ _ _
  simp only [Finset.sum_apply, Pi.smul_apply, coefficient_sharpTerm, hd,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦ smul_comm _ _ _

/-- The terms of the composition expansion are additive in the first symbol, for symbols of
possibly different orders: if `a₀ = a₁ + a₂` coefficientwise, then
`sharpTerm a₀ b k = sharpTerm a₁ b k + sharpTerm a₂ b k` coefficientwise. -/
theorem coefficient_sharpTerm_eq_add_left {μ₁ μ₂ : ℝ} {a₀ : Symbol n W U m'}
    {a₁ : Symbol n W U μ₁} {a₂ : Symbol n W U μ₂}
    (h : a₀.coefficient = a₁.coefficient + a₂.coefficient) (b : Symbol n V W m) (k : ℕ) :
    (a₀.sharpTerm b k).coefficient =
      (a₁.sharpTerm b k).coefficient + (a₂.sharpTerm b k).coefficient := by
  funext ⟨x, ξ⟩
  simp only [Pi.add_apply, coefficient_sharpTerm, h,
    mixedDeriv_add a₁.contDiff_coefficient a₂.contDiff_coefficient,
    ContinuousLinearMap.add_comp, Finset.sum_add_distrib, smul_add]

/-- The terms of the composition expansion are additive in the second symbol, for symbols of
possibly different orders: if `b₀ = b₁ + b₂` coefficientwise, then
`sharpTerm a b₀ k = sharpTerm a b₁ k + sharpTerm a b₂ k` coefficientwise. -/
theorem coefficient_sharpTerm_eq_add_right {μ₁ μ₂ : ℝ} {b₀ : Symbol n V W m}
    {b₁ : Symbol n V W μ₁} {b₂ : Symbol n V W μ₂}
    (h : b₀.coefficient = b₁.coefficient + b₂.coefficient) (a : Symbol n W U m') (k : ℕ) :
    (a.sharpTerm b₀ k).coefficient =
      (a.sharpTerm b₁ k).coefficient + (a.sharpTerm b₂ k).coefficient := by
  funext ⟨x, ξ⟩
  simp only [Pi.add_apply, coefficient_sharpTerm, h,
    mixedDeriv_add b₁.contDiff_coefficient b₂.contDiff_coefficient,
    ContinuousLinearMap.comp_add, Finset.sum_add_distrib, smul_add]

/-- Only the pointwise composition survives in the composition expansion of a constant symbol on
the left: its later terms vanish. -/
@[simp]
theorem const_sharpTerm_succ (T : W →L[ℂ] U) (b : Symbol n V W m) (k : ℕ) :
    (const T).sharpTerm b (k + 1) = 0 := by
  ext1
  funext ⟨x, ξ⟩
  have hT : (const T : Symbol n W U 0).coefficient = fun p ↦ (fun _ ↦ T) p.1 :=
    funext (coefficient_const T)
  have h (w : Fin (k + 1) → Fin n) :
      mixedDeriv [] (List.ofFn w) (const T : Symbol n W U 0).coefficient x ξ = 0 := by
    rw [hT]
    exact mixedDeriv_comp_fst (fun _ ↦ T) [] (β := List.ofFn w) (by simp) x ξ
  rw [coefficient_sharpTerm]
  simp only [h, ContinuousLinearMap.zero_comp, Finset.sum_const_zero, smul_zero, coefficient_zero,
    Pi.zero_apply]

/-- Only the pointwise composition survives in the composition expansion of a symbol on the right
that does not depend on the position: its later terms vanish. -/
theorem sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero {b : Symbol n V W m}
    (hb : ∀ j, spatialDeriv j b = 0) (a : Symbol n W U m') (k : ℕ) :
    a.sharpTerm b (k + 1) = 0 := by
  ext1
  funext ⟨x, ξ⟩
  simp [coefficient_sharpTerm_succ, coefficient_sharpTerm, hb]

/-- Only the pointwise composition survives in the composition expansion of a constant symbol on
the right: its later terms vanish. -/
@[simp]
theorem sharpTerm_const_succ (a : Symbol n W U m') (T : V →L[ℂ] W) (k : ℕ) :
    a.sharpTerm (const T) (k + 1) = 0 :=
  sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero (fun j ↦ by
    ext1
    funext ⟨x, ξ⟩
    simp [coefficient_const, coordinateDeriv_const _ (List.cons_ne_nil j [])]) a k

/-- **Leibniz rule in the position** for the terms of the composition expansion. -/
theorem spatialDeriv_sharpTerm (l : Fin n) (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    spatialDeriv l (a.sharpTerm b k) =
      (spatialDeriv l a).sharpTerm b k + a.sharpTerm (spatialDeriv l b) k := by
  induction k generalizing m m' with
  | zero => simp [sharpTerm_zero, spatialDeriv_comp]
  | succ k ih =>
    simp only [sharpTerm_succ, spatialDeriv_inclusion, map_smul, map_sum, ← map_add, ← smul_add,
      ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, spatialDeriv_frequencyDeriv_comm, spatialDeriv_comm]

/-- **Leibniz rule in the frequency** for the terms of the composition expansion. The orders of
the three terms differ, so the rule is stated for their coefficients. -/
theorem coefficient_frequencyDeriv_sharpTerm (l : Fin n) (a : Symbol n W U m')
    (b : Symbol n V W m) (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv l (a.sharpTerm b k)).coefficient p =
      ((frequencyDeriv l a).sharpTerm b k).coefficient p +
        (a.sharpTerm (frequencyDeriv l b) k).coefficient p := by
  induction k generalizing m m' with
  | zero => simp [sharpTerm_zero, frequencyDeriv_comp]
  | succ k ih =>
    simp only [sharpTerm_succ, frequencyDeriv_inclusion, map_smul, map_sum, coefficient_inclusion,
      coefficient_smul, coefficient_sum, Pi.smul_apply, Finset.sum_apply, ← smul_add,
      ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, frequencyDeriv_comm, spatialDeriv_frequencyDeriv_comm]

/-- If the estimates of `a` and `b` hold uniformly in the position, then so do those of every term
of the composition expansion. -/
theorem IsUniform.sharpTerm {a : Symbol n W U m'} {b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (k : ℕ) : (a.sharpTerm b k).IsUniform := by
  induction k generalizing m m' with
  | zero => exact (ha.comp hb).inclusion _
  | succ k ih =>
    rw [sharpTerm_succ]
    refine ((IsUniform.sum fun j _ ↦ ?_).smul _).inclusion _
    exact ih (ha.frequencyDeriv j) (hb.spatialDeriv j)

/-- The terms of positive index `k` of the expansion of `a # b` vanish when `a` vanishes at
positions outside `K` and `b` does not depend on the position near each point of `K`: every such
term contains a frequency derivative of `a` and a position derivative of `b`. -/
private theorem coefficient_sharpTerm_eq_zero {a : Symbol n W U m'} {b : Symbol n V W m}
    {K : Set (CoordinateSpace n)} (haK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0)
    (hbK : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∀ ξ, b.coefficient (y, ξ) = b.coefficient (x, ξ))
    {k : ℕ} (hk : k ≠ 0) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b k).coefficient p = 0 := by
  obtain ⟨x, ξ⟩ := p
  rw [coefficient_sharpTerm, Finset.sum_eq_zero fun w _ ↦ ?_, smul_zero]
  by_cases hx : x ∈ K
  · have hw : List.ofFn w ≠ [] := by simpa using hk
    rw [mixedDeriv_congr_of_eventually (b := fun q ↦ b.coefficient (x, q.2))
      ((hbK x hx).mono fun y hy η ↦ hy η),
      mixedDeriv_comp_snd (fun η ↦ b.coefficient (x, η)) hw, ContinuousLinearMap.comp_zero]
  · simp [mixedDeriv_def, haK x hx, ← Pi.zero_def]

/-- **Commutator with a coordinate function, for the leading term.** Multiplying the pointwise
composition `a ∘ b` by `(x - z)ⱼ` is composing `a` with `(y - z)ⱼ b`. -/
theorem coordSub_smul_coefficient_sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m)
    (z : CoordinateSpace n) (j : Fin n) (x ξ : CoordinateSpace n) :
    ((x - z) j : ℂ) • (a.sharpTerm b 0).coefficient (x, ξ) =
      (a.sharpTerm ((coordSubSymbol z j).comp b) 0).coefficient (x, ξ) := by
  simp only [coefficient_sharpTerm_zero, coefficient_comp, coefficient_coordSubSymbol,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, ← Complex.coe_smul,
    ContinuousLinearMap.comp_smul]

/-- The `k`-th term of the expansion with `∂_{xₗ} ((y - z)ⱼ b)` on the right is the term with
`(y - z)ⱼ ∂_{xₗ} b`, plus, for `l = j`, the term with `b`. -/
private theorem coefficient_sharpTerm_spatialDeriv_coordSubSymbol_comp (a : Symbol n W U m')
    (b : Symbol n V W m) (z : CoordinateSpace n) (j l : Fin n) (k : ℕ) :
    (a.sharpTerm (spatialDeriv l ((coordSubSymbol z j).comp b)) k).coefficient =
      (a.sharpTerm ((coordSubSymbol z j).comp (spatialDeriv l b)) k).coefficient +
        if j = l then (a.sharpTerm b k).coefficient else 0 := by
  have h : (spatialDeriv l ((coordSubSymbol z j).comp b)).coefficient =
      ((coordSubSymbol z j).comp (spatialDeriv l b)).coefficient +
        if j = l then b.coefficient else 0 := by
    funext ⟨x, ξ⟩
    rw [spatialDeriv_comp, coefficient_add, Pi.add_apply, coefficient_comp,
      coefficient_spatialDeriv_coordSubSymbol, add_comm, Pi.add_apply]
    split_ifs with hjl
    · subst hjl
      simp
    · simp [hjl]
  split_ifs with hjl
  · exact coefficient_sharpTerm_eq_add_right (by simpa [hjl] using h) a k
  · rw [add_zero]
    exact coefficient_sharpTerm_congr rfl (by simpa [hjl] using h) k

/-- **Commutator with a coordinate function, for the terms of the expansion.**
`(x - z)ⱼ sharpTerm a b (k + 1) = sharpTerm a ((y - z)ⱼ b) (k + 1) + i sharpTerm (∂_{ξⱼ} a) b k`,
the termwise form of `coordSub_smul_coefficient_sharp`. -/
theorem coordSub_smul_coefficient_sharpTerm_succ (k : ℕ) :
    ∀ {m m' : ℝ} (a : Symbol n W U m') (b : Symbol n V W m) (z : CoordinateSpace n) (j : Fin n)
      (x ξ : CoordinateSpace n),
      ((x - z) j : ℂ) • (a.sharpTerm b (k + 1)).coefficient (x, ξ) =
        (a.sharpTerm ((coordSubSymbol z j).comp b) (k + 1)).coefficient (x, ξ) +
          Complex.I • ((frequencyDeriv j a).sharpTerm b k).coefficient (x, ξ) := by
  -- The term of `a # ((y - z)ⱼ b)` of index `k + 1`, through the recursion.
  have hY (k : ℕ) {m m' : ℝ} (a : Symbol n W U m') (b : Symbol n V W m) (z : CoordinateSpace n)
      (j : Fin n) (x ξ : CoordinateSpace n) :
      (a.sharpTerm ((coordSubSymbol z j).comp b) (k + 1)).coefficient (x, ξ) =
        (-Complex.I / (k + 1)) • (∑ l, ((frequencyDeriv l a).sharpTerm
          ((coordSubSymbol z j).comp (spatialDeriv l b)) k).coefficient (x, ξ) +
            ((frequencyDeriv j a).sharpTerm b k).coefficient (x, ξ)) := by
    rw [coefficient_sharpTerm_succ]
    simp only [coefficient_sharpTerm_spatialDeriv_coordSubSymbol_comp, Pi.add_apply,
      Finset.sum_add_distrib]
    congr 2
    simp [apply_ite (fun f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] U ↦ f (x, ξ))]
  induction k with
  | zero =>
    intro m m' a b z j x ξ
    rw [hY, coefficient_sharpTerm_succ, smul_comm, Finset.smul_sum]
    simp only [coordSub_smul_coefficient_sharpTerm_zero]
    push_cast
    module
  | succ k ih =>
    intro m m' a b z j x ξ
    rw [hY, coefficient_sharpTerm_succ, smul_comm, Finset.smul_sum]
    simp only [ih, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [coefficient_sharpTerm_succ (frequencyDeriv j a)]
    simp only [frequencyDeriv_comm j]
    set S₁ := ∑ l, ((frequencyDeriv l a).sharpTerm
      ((coordSubSymbol z j).comp (spatialDeriv l b)) (k + 1)).coefficient (x, ξ)
    set S₂ := ∑ l, ((frequencyDeriv l (frequencyDeriv j a)).sharpTerm (spatialDeriv l b)
      k).coefficient (x, ξ)
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk' : ((k + 1 : ℕ) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, add_assoc, ← add_smul]
    congr 2
    push_cast at hk' ⊢
    field_simp
    ring

end Term

/-! ### The interpolating family `a #_t b` -/

section Scaled

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The family `(a #_t b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2π t η) ∘ b̂(η, ξ) dη` interpolating
between the pointwise composition (`t = 0`) and the composition symbol (`t = 1`). -/
private def scaledSharp (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, sharpIntegrand a b (t * (2 * π)) (x, ξ) η

/-- The frequency shifts `2π t η` of the family with `|t| ≤ 2` are at most `4π ‖η‖`. -/
private theorem abs_mul_two_pi_le {t : ℝ} (ht : |t| ≤ 2) : |t * (2 * π)| ≤ 4 * π := by
  rw [abs_mul, abs_of_pos Real.two_pi_pos]
  nlinarith [Real.pi_pos]

/-- `‖(a #_t bᵢ)(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)`, uniformly in `i` for a family `bᵢ` whose position
slices have Fourier transforms decaying faster than every power uniformly in `i`, uniformly for
`|t| ≤ 2` and positions in a set on which `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m'`. -/
private theorem exists_norm_scaledSharp_le {ι : Type*} {c : ι → Symbol n V W m}
    (hc : ∀ r : ℝ, ∃ C, 0 ≤ C ∧ ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2))
    {K : Set (CoordinateSpace n)}
    (ha : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ t : ℝ, |t| ≤ 2 → ∀ x ∈ K, ∀ ξ,
      ‖scaledSharp a (c i) t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_integral_sharpIntegrand_le_of_forall_norm_fourier_le hc ha
    (R := 4 * π) (by linarith [Real.two_le_pi])
  exact ⟨C, hC0, fun i t ht ↦ hC i _ (abs_mul_two_pi_le ht)⟩

/-- The Fourier transforms of the position slices of the position derivatives `∂_{xⱼ} bᵢ` decay
faster than every power uniformly in `i` when those of the `bᵢ` do, since
`(∂_{xⱼ} bᵢ)^(η, ξ) = 2πi ηⱼ b̂ᵢ(η, ξ)`. -/
private theorem forall_norm_fourier_spatialDeriv_le {ι : Type*} {c : ι → Symbol n V W m}
    (hcK : ∀ i, (c i).HasCompactSpatialSupport)
    (hc : ∀ r : ℝ, ∃ C, 0 ≤ C ∧ ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2)) (j : Fin n) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ i η ξ, ‖𝓕 (fun y ↦ (spatialDeriv j (c i)).coefficient (y, ξ)) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := hc (r + 1)
  refine ⟨2 * π * C, by positivity, fun i η ξ ↦ ?_⟩
  have hη : ‖η‖ ≤ (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hj : |⟪η, EuclideanSpace.single j (1 : ℝ)⟫| ≤ ‖η‖ :=
    (abs_real_inner_le_norm _ _).trans_eq (by simp)
  have hw : (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + 1) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  rw [(hcK i).fourier_spatialDeriv_slice, norm_smul, norm_mul, norm_mul, norm_mul,
    Complex.norm_I, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
  calc 2 * π * |⟪η, EuclideanSpace.single j (1 : ℝ)⟫| * ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖
      ≤ 2 * π * (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2) *
          (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + 1) / 2)) := by
        gcongr
        · exact hj.trans hη
        · exact hC i η ξ
    _ = 2 * π * C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + 1) / 2)) := by ring
    _ = _ := by rw [hw]

/-- At `t = 1` the family is the composition symbol. -/
private theorem scaledSharp_one (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    scaledSharp a b 1 x ξ = (a.sharp b hb).coefficient (x, ξ) := by
  simp only [scaledSharp, sharpIntegrand_apply, one_mul, coefficient_sharp]

/-- At `t = 0` the family is the pointwise composition, by Fourier inversion. -/
private theorem scaledSharp_zero [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    scaledSharp a b 0 x ξ = (a.coefficient (x, ξ)).comp (b.coefficient (x, ξ)) := by
  set f : CoordinateSpace n → V →L[ℂ] W := fun y ↦ b.coefficient (y, ξ)
  set φ : 𝓢(CoordinateSpace n, V →L[ℂ] W) := hb.sliceSchwartz ξ
  have hfS : ⇑φ = f := hb.coe_sliceSchwartz ξ
  have hFS : 𝓕 f = ⇑(𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)) := by
    rw [SchwartzMap.fourier_coe, hfS]
  have hint : Integrable (𝓕 f) := hb.integrable_fourier_slice ξ
  have hinv : 𝓕⁻ (𝓕 f) = f := hb.fourierInv_fourier_slice ξ
  have hint' : Integrable fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 f η :=
    hint.norm.mono' ((by fun_prop : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ)).smul
      (hFS ▸ (𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)).continuous)).aestronglyMeasurable
      (.of_forall fun η ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  calc scaledSharp a b 0 x ξ
      = ∫ η, ContinuousLinearMap.compL ℂ V W U (a.coefficient (x, ξ))
          ((𝐞 ⟪η, x⟫ : ℂ) • 𝓕 f η) := by
        simp only [scaledSharp, sharpIntegrand_apply, zero_mul, zero_smul, add_zero, map_smul,
          ContinuousLinearMap.compL_apply, f]
    _ = (a.coefficient (x, ξ)).comp (𝓕⁻ (𝓕 f) x) := by
        rw [ContinuousLinearMap.integral_comp_comm _ hint', Real.fourierInv_eq,
          ContinuousLinearMap.compL_apply]
        simp only [Circle.smul_def]
    _ = _ := by rw [hinv]

/-- **Differentiation in the parameter** of the integrand: since `2π ηⱼ b̂ = -i (∂_{xⱼ} b)^`,
`d/dt` of the integrand of `a #_t b` is `-i ∑ⱼ` the integrand of `(∂_{ξⱼ} a) #_t (∂_{xⱼ} b)`. -/
private theorem hasDerivAt_sharpIntegrand (hb : b.HasCompactSpatialSupport) (t : ℝ)
    (x ξ η : CoordinateSpace n) :
    HasDerivAt (fun t ↦ sharpIntegrand a b (t * (2 * π)) (x, ξ) η)
      (∑ j, (-Complex.I) •
        sharpIntegrand (frequencyDeriv j a) (spatialDeriv j b) (t * (2 * π)) (x, ξ) η) t := by
  set c : CoordinateSpace n := (2 * π) • η
  set B := 𝓕 (fun y ↦ b.coefficient (y, ξ)) η
  set Φ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] U) :=
    (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  set g : CoordinateSpace n → W →L[ℂ] U := fun ζ ↦ a.coefficient (x, ζ)
  have hg : HasFDerivAt g (fderiv ℝ g (ξ + (t * (2 * π)) • η)) (ξ + (t * (2 * π)) • η) :=
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable (by simp)
      _).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ ↦ ξ + (t * (2 * π)) • η) c t := by
    simpa using (((hasDerivAt_id t).mul_const (2 * π)).smul_const η).const_add ξ
  have h := ((Φ.flip B).hasFDerivAt.comp_hasDerivAt t (hg.comp_hasDerivAt t hl)).const_smul
    (𝐞 ⟪η, x⟫ : ℂ)
  have hgj (j : Fin n) (ζ : CoordinateSpace n) : fderiv ℝ g ζ (EuclideanSpace.single j 1) =
      (frequencyDeriv j a).coefficient (x, ζ) := by
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
  refine (h.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)).congr_deriv ?_
  · simp only [sharpIntegrand_apply, Pi.smul_apply, Function.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      ContinuousLinearMap.compL_apply, Φ, g, B]
  rw [ContinuousLinearMap.apply_eq_sum_single (fderiv ℝ g (ξ + (t * (2 * π)) • η)) c, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [sharpIntegrand_apply, hb.fourier_spatialDeriv_slice, hgj, map_smul, Φ, c, B,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.comp_smul, PiLp.smul_apply, smul_smul, EuclideanSpace.inner_single_right,
    ← Complex.coe_smul]
  rw [smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  simp only [smul_eq_mul, starRingEnd_apply, star_trivial, one_mul]
  push_cast
  linear_combination (↑(𝐞 ⟪η, x⟫) * 2 * ↑π * ↑(η.ofLp j) : ℂ) * Complex.I_sq

/-- **Differentiation in the parameter** under the integral sign:
`d/dt (a #_t b) = -i ∑ⱼ (∂_{ξⱼ} a) #_t (∂_{xⱼ} b)`. -/
private theorem hasDerivAt_scaledSharp (hb : b.HasCompactSpatialSupport) {t₀ : ℝ} (ht₀ : |t₀| ≤ 1)
    (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledSharp a b t x ξ)
      (∑ j, (-Complex.I) • scaledSharp (frequencyDeriv j a) (spatialDeriv j b) t₀ x ξ) t₀ := by
  choose C _ hC using fun j ↦ (hb.spatialDeriv j).exists_norm_sharpIntegrand_le
    ((frequencyDeriv j a).exists_bound_coefficient {x} isCompact_singleton) ((n : ℝ) + 1)
    (R := 4 * π) (by linarith [Real.two_le_pi])
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t * (2 * π)| ≤ 4 * π := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    exact abs_mul_two_pi_le (by linarith)
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] U := fun t η ↦
    ∑ j, (-Complex.I) •
      sharpIntegrand (frequencyDeriv j a) (spatialDeriv j b) (t * (2 * π)) (x, ξ) η
  set bound : CoordinateSpace n → ℝ := fun η ↦
    (∑ j, C j * (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + m) / 2)) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hint (j : Fin n) : Integrable fun η ↦ (-Complex.I) •
      sharpIntegrand (frequencyDeriv j a) (spatialDeriv j b) (t₀ * (2 * π)) (x, ξ) η :=
    ((hb.spatialDeriv j).integrable_sharpIntegrand _ _).fun_smul _
  have hcont {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂}
      (hb' : b'.HasCompactSpatialSupport) (s : ℝ) :
      Continuous (sharpIntegrand a' b' s (x, ξ)) :=
    Continuous.comp (g := fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      sharpIntegrand a' b' s q.1 q.2) (f := fun η ↦ ((x, ξ), η))
      (hb'.continuous_sharpIntegrand s) (continuous_const.prodMk continuous_id)
  have hmeas : ∀ᶠ t in nhds t₀, AEStronglyMeasurable (sharpIntegrand a b (t * (2 * π)) (x, ξ))
      (volume : Measure (CoordinateSpace n)) :=
    .of_forall fun t ↦ (hcont a hb _).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' t₀) (volume : Measure (CoordinateSpace n)) :=
    (continuous_finsetSum _ fun j _ ↦
      (hcont _ (hb.spatialDeriv j) _).const_smul (-Complex.I)).aestronglyMeasurable
  have hbound : ∀ᵐ η ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t η‖ ≤ bound η := .of_forall fun η t ht ↦ by
    simp only [F', bound, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact hC j _ (hball t ht) x rfl ξ η
  have hdiff : ∀ᵐ η ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      HasDerivAt (fun t ↦ sharpIntegrand a b (t * (2 * π)) (x, ξ) η) (F' t η) t :=
    .of_forall fun η t _ ↦ hasDerivAt_sharpIntegrand hb t x ξ η
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ one_pos) hmeas (hb.integrable_sharpIntegrand _ _) hF'meas
    hbound (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _) hdiff
  refine h.congr_deriv ?_
  simp only [F']
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  simp only [integral_smul, scaledSharp]

end Scaled

/-! ### The remainder of the expansion along the family -/

section Remainder

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The remainder `a #_t b - ∑_{k < N} t^k sharpTerm a b k` of the expansion along the
interpolating family. -/
private def remainderAt (N : ℕ) (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] U :=
  scaledSharp a b t x ξ - ∑ k ∈ range N, t ^ k • (a.sharpTerm b k).coefficient (x, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k sharpTerm a b k` is given by the
recursion defining `sharpTerm`. -/
private theorem hasDerivAt_sum_pow_smul_sharpTerm (N : ℕ) (a : Symbol n W U m')
    (b : Symbol n V W m) (x ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.sharpTerm b k).coefficient (x, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient (x, ξ))) t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.sharpTerm b k).coefficient (x, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_sharpTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `(∂_{ξⱼ} a, ∂_{xⱼ} b)`. -/
private theorem hasDerivAt_remainderAt (hb : b.HasCompactSpatialSupport) (N : ℕ) {t : ℝ}
    (ht : |t| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a b (N + 1) t x ξ)
      ((-Complex.I) • ∑ j, remainderAt (frequencyDeriv j a) (spatialDeriv j b) N t x ξ) t := by
  refine ((hasDerivAt_scaledSharp (a := a) hb ht x ξ).fun_sub
    (hasDerivAt_sum_pow_smul_sharpTerm N a b x ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

/-- The remainder vanishes at `t = 0`. -/
private theorem remainderAt_zero [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (N : ℕ) (x ξ : CoordinateSpace n) :
    remainderAt a b (N + 1) 0 x ξ = 0 := by
  rw [remainderAt, scaledSharp_zero hb, Finset.sum_range_succ']
  simp

/-- **The remainder estimate.**
`‖a #_t bᵢ - ∑_{k < N} t^k sharpTerm a bᵢ k‖ ≤ C ⟨ξ⟩ ^ (m' + m - N)`, uniformly in `i` for a
family `bᵢ` with compact spatial support whose position slices have Fourier transforms decaying
faster than every power uniformly in `i`, uniformly for `t ∈ [0, 1]` and positions in a set `K`
on which every symbol `a` satisfying a predicate `P`, stable under frequency derivatives, is
bounded by `C ⟨ξ⟩ ^ m'`. -/
private theorem exists_norm_remainderAt_le [CompleteSpace W] [CompleteSpace U]
    (P : ∀ {m' : ℝ}, Symbol n W U m' → Prop)
    (hPfrequency : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (frequencyDeriv j a))
    {K : Set (CoordinateSpace n)}
    (hP : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a →
      ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    {ι : Type*} (N : ℕ) :
    ∀ {m m' : ℝ} {a : Symbol n W U m'}, P a → ∀ {c : ι → Symbol n V W m},
      (∀ i, (c i).HasCompactSpatialSupport) →
      (∀ r : ℝ, ∃ C, 0 ≤ C ∧ ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2)) →
      ∃ C, 0 ≤ C ∧ ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ ξ,
        ‖remainderAt a (c i) N t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  induction N with
  | zero =>
    intro m m' a ha c _ hcF
    obtain ⟨C, hC0, hC⟩ := exists_norm_scaledSharp_le hcF (hP ha)
    refine ⟨C, hC0, fun i t ht x hx ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [remainderAt] using hC i t ht2 x hx ξ
  | succ N ih =>
    intro m m' a ha c hcK hcF
    choose C hC0 hC using fun j ↦ ih (hPfrequency ha j) (fun i ↦ (hcK i).spatialDeriv j)
      (forall_norm_fourier_spatialDeriv_le hcK hcF j)
    refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ ↦ hC0 j, fun i t ht x hx ξ ↦ ?_⟩
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + m - N) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      congr 1
      push_cast
      ring
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (frequencyDeriv j a) (spatialDeriv j (c i)) N s x ξ‖ ≤
          (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      intro s hs
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← hw]
      exact hC j i s (Set.Ico_subset_Icc_self hs) x hx ξ
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hasDerivAt_remainderAt (hcK i) N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) x
        ξ).hasDerivWithinAt) hbound t ht
    rw [remainderAt_zero (hcK i), sub_zero, sub_zero] at hmv
    have hB : 0 ≤ (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) :=
      mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section Symbol

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a) in
/-- The remainder `a # b - ∑_{k < N} sharpTerm a b k`, as a symbol of order `m' + m`. -/
private def remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m) :=
  a.sharp b hb - ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k)

private theorem coefficient_remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    (remainderSymbol a hb N).coefficient (x, ξ) = remainderAt a b N 1 x ξ := by
  simp [remainderSymbol, remainderAt, scaledSharp_one hb]

private theorem spatialDeriv_remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    spatialDeriv j (remainderSymbol a hb N) =
      remainderSymbol (spatialDeriv j a) hb N + remainderSymbol a (hb.spatialDeriv j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_sharp, spatialDeriv_inclusion,
    spatialDeriv_sharpTerm, map_add, Finset.sum_add_distrib]
  abel

private theorem coefficient_frequencyDeriv_remainderSymbol (hb : b.HasCompactSpatialSupport)
    (N : ℕ) (j : Fin n) :
    (frequencyDeriv j (remainderSymbol a hb N)).coefficient =
      (remainderSymbol (frequencyDeriv j a) hb N).coefficient +
        (remainderSymbol a (hb.frequencyDeriv j) N).coefficient := by
  funext ⟨x, ξ⟩
  simp only [remainderSymbol, map_sub, map_sum, coefficient_sub, coefficient_sum,
    frequencyDeriv_inclusion, coefficient_inclusion, Pi.sub_apply, Pi.add_apply,
    Finset.sum_apply, coefficient_frequencyDeriv_sharp, coefficient_frequencyDeriv_sharpTerm,
    Finset.sum_add_distrib]
  abel

section Bounds

variable (P : ∀ {m' : ℝ}, Symbol n W U m' → Prop)
  (hPspatial : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (spatialDeriv j a))
  (hPfrequency : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (frequencyDeriv j a))
  {K : Set (CoordinateSpace n)}
  (hP : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a →
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))

include hPfrequency hP in
/-- The remainder is bounded by `C ⟨ξ⟩ ^ (m' + m - N)` for positions in a set `K` on which every
symbol `a` satisfying a predicate `P`, stable under frequency derivatives, is bounded by
`C ⟨ξ⟩ ^ m'`. -/
private theorem exists_norm_coefficient_remainderSymbol_le [CompleteSpace W] [CompleteSpace U]
    (ha : P a) (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖(remainderSymbol a hb N).coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le P hPfrequency hP (ι := Unit) N ha
    (c := fun _ ↦ b) (fun _ ↦ hb)
    (fun r ↦ (hb.exists_norm_fourier_slice_le r).imp fun _ hC ↦ ⟨hC.1, fun _ ↦ hC.2⟩)
  refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
  simpa [coefficient_remainderSymbol] using hC () 1 ⟨zero_le_one, le_rfl⟩ x hx ξ

include hPspatial hPfrequency hP in
/-- The symbol estimates of order `m' + m - N` for the remainder, from the Leibniz rules: each
derivative falls on one of the two symbols, and a frequency derivative lowers the order of that
symbol by one. -/
private theorem exists_bound_remainderSymbol [CompleteSpace W] [CompleteSpace U]
    (ha : P a) (hb : b.HasCompactSpatialSupport) (N : ℕ) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (remainderSymbol a hb N).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) :=
  exists_norm_mixedDeriv_le_of_leibniz N P hPspatial hPfrequency
    (fun a _ hb ↦ (remainderSymbol a hb N).coefficient)
    (fun a _ hb ↦ (remainderSymbol a hb N).contDiff_coefficient)
    (fun a _ hb j x ξ ↦ by
      rw [← coefficient_spatialDeriv, spatialDeriv_remainderSymbol, coefficient_add, Pi.add_apply])
    (fun a _ hb j x ξ ↦ by
      rw [← coefficient_frequencyDeriv, coefficient_frequencyDeriv_remainderSymbol, Pi.add_apply])
    (fun _ ha _ hb ↦ exists_norm_coefficient_remainderSymbol_le P hPfrequency hP ha hb N)
    a ha hb α β

end Bounds

variable [CompleteSpace W] [CompleteSpace U]

variable (a b) in
/-- The remainder `a # b - ∑_{k < N} sharpTerm a b k` of the composition expansion after `N`
terms, a symbol of order `m' + m - N` (`sharp_eq_sum_sharpTerm_add_sharpRemainder`). -/
def sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m - N) where
  coefficient := (remainderSymbol a hb N).coefficient
  contDiff_coefficient := (remainderSymbol a hb N).contDiff_coefficient
  exists_bound K hK α β := exists_bound_remainderSymbol (fun _ ↦ True) (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial) (fun {_} a _ ↦ a.exists_bound_coefficient K hK) trivial hb N α β

/-- The coefficient of `sharpRemainder`, which is `remainderSymbol` considered at the lower order
`m' + m - N`. -/
private theorem coefficient_sharpRemainder_eq (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a.sharpRemainder b hb N).coefficient = (remainderSymbol a hb N).coefficient :=
  rfl

@[simp]
theorem coefficient_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a.sharpRemainder b hb N).coefficient =
      (a.sharp b hb).coefficient - ∑ k ∈ range N, (a.sharpTerm b k).coefficient := by
  simp [sharpRemainder, remainderSymbol]

/-- **The asymptotic expansion of the composition symbol.** For every `N`,
`a # b = ∑_{k < N} sharpTerm a b k + sharpRemainder a b hb N`, where `sharpTerm a b k` is the
term `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of order `m' + m - k` and the remainder is a
symbol of order `m' + m - N`. -/
theorem sharp_eq_sum_sharpTerm_add_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    a.sharp b hb = ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k) +
      inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.sharpRemainder b hb N) := by
  ext1
  simp

/-- **Uniform remainders.** If the estimates of `a` hold uniformly in the position, then so do
those of every remainder `a # b - ∑_{k < N} sharpTerm a b k` of the composition expansion. -/
theorem IsUniform.sharpRemainder (ha : a.IsUniform) (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a.sharpRemainder b hb N).IsUniform := isUniform_iff.2 fun α β ↦ by
  obtain ⟨C, hC0, hC⟩ := exists_bound_remainderSymbol IsUniform (fun ha j ↦ ha.spatialDeriv j)
    (fun ha j ↦ ha.frequencyDeriv j) (K := Set.univ)
    (fun ha ↦ ha.exists_bound_coefficient.imp fun _ hC ↦ ⟨hC.1, fun x _ ξ ↦ hC.2 x ξ⟩) ha hb N
    α β
  exact ⟨C, hC0, fun x ξ ↦ hC x (Set.mem_univ x) ξ⟩

/-- The Leibniz rule for a position derivative of the remainder of the composition expansion. -/
theorem spatialDeriv_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) (j : Fin n) :
    spatialDeriv j (a.sharpRemainder b hb N) =
      (spatialDeriv j a).sharpRemainder b hb N + a.sharpRemainder (spatialDeriv j b)
        (hb.spatialDeriv j) N := by
  ext1
  funext ⟨x, ξ⟩
  have h := congrArg (fun s ↦ s.coefficient (x, ξ)) (spatialDeriv_remainderSymbol (a := a) hb N j)
  simpa only [coefficient_spatialDeriv, coefficient_add, Pi.add_apply,
    coefficient_sharpRemainder_eq] using h

/-- The Leibniz rule for a frequency derivative of the remainder of the composition expansion. The
three remainders have the same order `m' + m - N - 1`, written differently, so the rule is stated
for their coefficients. -/
theorem coefficient_frequencyDeriv_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    (frequencyDeriv j (a.sharpRemainder b hb N)).coefficient =
      ((frequencyDeriv j a).sharpRemainder b hb N).coefficient +
        (a.sharpRemainder (frequencyDeriv j b) (hb.frequencyDeriv j) N).coefficient := by
  funext ⟨x, ξ⟩
  have h := congrFun (coefficient_frequencyDeriv_remainderSymbol (a := a) hb N j) (x, ξ)
  simpa only [coefficient_frequencyDeriv, Pi.add_apply, coefficient_sharpRemainder_eq] using h

/-- **Uniform remainders for a family.** Let `a` be a symbol whose estimates hold uniformly in the
position, and `bᵢ` symbols with compact spatial support whose position slices have Fourier
transforms `b̂ᵢ(η, ξ)` decaying faster than every power in `η`, with the weight `⟨ξ⟩ ^ m` and
constants independent of `i`. Then the remainders `a # bᵢ - ∑_{k < N} sharpTerm a bᵢ k` are
bounded by `C ⟨ξ⟩ ^ (m' + m - N)` with `C` independent of `i` and of the position. -/
theorem IsUniform.exists_norm_coefficient_sharpRemainder_le (ha : a.IsUniform) {ι : Type*}
    {c : ι → Symbol n V W m} (hc : ∀ i, (c i).HasCompactSpatialSupport)
    (hcF : ∀ r : ℝ, ∃ C, 0 ≤ C ∧ ∀ i η ξ, ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ)) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2)) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ, ‖(a.sharpRemainder (c i) (hc i) N).coefficient (x, ξ)‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le IsUniform (fun ha j ↦ ha.frequencyDeriv j)
    (K := Set.univ)
    (fun ha ↦ ha.exists_bound_coefficient.imp fun _ hC ↦ ⟨hC.1, fun x _ ξ ↦ hC.2 x ξ⟩) N ha hc
    hcF
  refine ⟨C, hC0, fun i x ξ ↦ ?_⟩
  have h := hC i 1 ⟨zero_le_one, le_rfl⟩ x (Set.mem_univ x) ξ
  rwa [← coefficient_remainderSymbol] at h

/-- The composition symbol `a # b` is the pointwise composition `a ∘ b` up to a symbol of order
`m' + m - 1`. -/
theorem sharp_eq_comp_add_sharpRemainder_one (hb : b.HasCompactSpatialSupport) :
    a.sharp b hb = a.comp b + inclusion (by simp) (a.sharpRemainder b hb 1) := by
  ext1
  funext p
  simp

/-- **Locality of the composition symbol.** Let `b` have compact spatial support. If `a` vanishes
at positions outside `K` and `b` does not depend on the position near each point of `K`, for
instance if `b` is the symbol of multiplication by a compactly supported smooth function equal to
`1` on a neighbourhood of `K`, then `a # b` agrees with the pointwise composition `a ∘ b` up to a
smoothing symbol. -/
theorem isSmoothing_sharp_sub_comp (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (haK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0)
    (hbK : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∀ ξ, b.coefficient (y, ξ) = b.coefficient (x, ξ)) :
    (a.sharp b hb - a.comp b).IsSmoothing := by
  rw [isSmoothing_iff]
  intro m''
  obtain ⟨N, hN⟩ := exists_nat_ge (m' + m - m'')
  refine ⟨inclusion (by push_cast; linarith) (a.sharpRemainder b hb (N + 1)), ?_⟩
  rw [coefficient_inclusion, coefficient_sharpRemainder, Finset.sum_range_succ', coefficient_sub]
  funext p
  simp [coefficient_sharpTerm_eq_zero haK hbK]

/-- The composition symbol is an asymptotic sum `a # b ∼ ∑ₖ sharpTerm a b k` of the terms of the
expansion, of orders `m' + m - k`. In particular it is determined by the terms modulo smoothing
symbols (`TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`). -/
theorem isAsymptoticSum_sharp (hb : b.HasCompactSpatialSupport) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m' + m - k) (inclusion (by simp) (a.sharp b hb))
      (a.sharpTerm b) :=
  isAsymptoticSum_iff.2 fun N ↦ ⟨a.sharpRemainder b hb N, by simp⟩

end Symbol

/-! ### Commutators -/

section Commutator

variable [CompleteSpace V]

/-- **Commutators lower the order.** If two symbols `a` of order `m'` and `b` of order `m` with
compact spatial support take commuting values `a(x, ξ)` and `b(x, ξ)` at every point, for instance
scalar symbols, the composition symbol `a # b - b # a` of the commutator `[Op(a), Op(b)]` is a
symbol of order `m' + m - 1`. -/
theorem exists_coefficient_eq_sharp_sub_sharp {a : Symbol n V V m'} {b : Symbol n V V m}
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport)
    (hab : ∀ p, Commute (a.coefficient p) (b.coefficient p)) :
    ∃ r : Symbol n V V (m' + m - 1),
      r.coefficient = (a.sharp b hb).coefficient - (b.sharp a ha).coefficient := by
  refine ⟨(inclusion (by simp) (a.sharpRemainder b hb 1) : Symbol n V V (m' + m - 1)) -
    inclusion (by push_cast; linarith) (b.sharpRemainder a ha 1), ?_⟩
  funext p
  have h := (hab p).eq
  simp only [ContinuousLinearMap.mul_def] at h
  simp only [coefficient_sub, coefficient_inclusion, Pi.sub_apply, coefficient_sharpRemainder,
    Finset.sum_range_one, coefficient_sharpTerm_zero, h]
  abel

/-- **The commutator expansion to second order.** For symbols `a` of order `m'` and `b` of order
`m` with compact spatial support, the composition symbol `a # b - b # a` of the commutator
`[Op(a), Op(b)]` is

`[a, b] - i ∑ⱼ (∂_{ξⱼ} a ∘ ∂_{xⱼ} b - ∂_{ξⱼ} b ∘ ∂_{xⱼ} a)`

up to a symbol `r` of order `m' + m - 2`, where `[a, b] = a ∘ b - b ∘ a` is the pointwise
commutator. -/
theorem exists_coefficient_eq_sharp_sub_sharp_sub_commutator {a : Symbol n V V m'}
    {b : Symbol n V V m} (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport) :
    ∃ r : Symbol n V V (m' + m - 2), ∀ p, r.coefficient p =
      (a.sharp b hb).coefficient p - (b.sharp a ha).coefficient p -
        ((a.coefficient p).comp (b.coefficient p) - (b.coefficient p).comp (a.coefficient p)) +
        Complex.I • ∑ j, (((frequencyDeriv j a).coefficient p).comp
            ((spatialDeriv j b).coefficient p) -
          ((frequencyDeriv j b).coefficient p).comp ((spatialDeriv j a).coefficient p)) := by
  refine ⟨(inclusion (by simp) (a.sharpRemainder b hb 2) : Symbol n V V (m' + m - 2)) -
    inclusion (by push_cast; linarith) (b.sharpRemainder a ha 2), fun p ↦ ?_⟩
  simp only [coefficient_sub, coefficient_inclusion, Pi.sub_apply, coefficient_sharpRemainder,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Pi.add_apply,
    coefficient_sharpTerm_zero, coefficient_sharpTerm_one, Finset.sum_sub_distrib, smul_sub,
    neg_smul]
  abel

/-- **The Poisson bracket formula for commutators.** If every value of `a` commutes with every
value of `b`, for instance if one of them is a scalar symbol times the identity, the composition
symbol `a # b - b # a` of `[Op(a), Op(b)]` is `-i {a, b}` up to a symbol `r` of order
`m' + m - 2`, where `{a, b} = ∑ⱼ (∂_{ξⱼ} a ∘ ∂_{xⱼ} b - ∂_{xⱼ} a ∘ ∂_{ξⱼ} b)` is the Poisson
bracket. -/
theorem exists_coefficient_eq_sharp_sub_sharp_add_poissonBracket {a : Symbol n V V m'}
    {b : Symbol n V V m} (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport)
    (hab : ∀ p q, Commute (a.coefficient p) (b.coefficient q)) :
    ∃ r : Symbol n V V (m' + m - 2), r.coefficient =
      (a.sharp b hb).coefficient - (b.sharp a ha).coefficient +
        Complex.I • (a.poissonBracket b).coefficient := by
  obtain ⟨r, hr⟩ := exists_coefficient_eq_sharp_sub_sharp_sub_commutator ha hb
  refine ⟨r, funext fun p ↦ ?_⟩
  have h0 : (a.coefficient p).comp (b.coefficient p) =
      (b.coefficient p).comp (a.coefficient p) := by
    simpa only [ContinuousLinearMap.mul_def] using (hab p p).eq
  -- The derivatives of `a` and `b` inherit the commutation of their values.
  have hder : ∀ j, ((frequencyDeriv j b).coefficient p).comp ((spatialDeriv j a).coefficient p) =
      ((spatialDeriv j a).coefficient p).comp ((frequencyDeriv j b).coefficient p) := fun j ↦ by
    simpa only [ContinuousLinearMap.mul_def] using (commute_coefficient_frequencyDeriv (fun q ↦
      (commute_coefficient_spatialDeriv (fun p' ↦ hab p' q) j p).symm) j p).eq
  simp only [hr p, h0, hder, sub_self, sub_zero, coefficient_poissonBracket,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/-- **Commutator with a coordinate function, for the remainders of the expansion.**
`(x - z)ⱼ R_N(a, b) = R_N(a, (y - z)ⱼ b) + i R_{N - 1}(∂_{ξⱼ} a, b)`, where
`R_N(a, b) = a # b - ∑_{k < N} sharpTerm a b k` and `N - 1` is truncated at `0`. For `N = 0` this
is `coordSub_smul_coefficient_sharp`. -/
theorem coordSub_smul_coefficient_sharpRemainder [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) (z : CoordinateSpace n) (j : Fin n) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    ((x - z) j : ℂ) • (a.sharpRemainder b hb N).coefficient (x, ξ) =
      (a.sharpRemainder ((coordSubSymbol z j).comp b) (hb.comp_left _) N).coefficient (x, ξ) +
        Complex.I • ((frequencyDeriv j a).sharpRemainder b hb (N - 1)).coefficient (x, ξ) := by
  cases N with
  | zero =>
    simpa using coordSub_smul_coefficient_sharp a hb z j x ξ
  | succ N =>
    simp only [coefficient_sharpRemainder, Pi.sub_apply, Finset.sum_apply, Nat.add_sub_cancel]
    rw [smul_sub, coordSub_smul_coefficient_sharp a hb z j x ξ, Finset.sum_range_succ',
      Finset.sum_range_succ', smul_add, Finset.smul_sum, coordSub_smul_coefficient_sharpTerm_zero]
    have h : ∀ k ∈ Finset.range N, ((x - z) j : ℂ) • (a.sharpTerm b (k + 1)).coefficient (x, ξ) =
        (a.sharpTerm ((coordSubSymbol z j).comp b) (k + 1)).coefficient (x, ξ) +
          Complex.I • ((frequencyDeriv j a).sharpTerm b k).coefficient (x, ξ) :=
      fun k _ ↦ coordSub_smul_coefficient_sharpTerm_succ k a b z j x ξ
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.smul_sum, smul_sub]
    abel

end Commutator

end Symbol

/-! ### The principal symbol of a composition -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup U]
  [NormedSpace ℂ U] [CompleteSpace U]

/-- **The principal symbol of a composition.** For classical symbols `a` of order `m'` and `b` of
order `m`, with `b` of compact spatial support, the composition symbol `a # b` differs by a symbol
of order `m' + m - 1` from the cut-off term `χ(ξ) (σ(a) ∘ σ(b))(x, ξ)` of the composition of their
principal symbols. -/
theorem exists_sharp_sub_cutoffSymbol_principal_comp (a : ClassicalSymbol n W U m')
    (b : ClassicalSymbol n V W m) (hb : b.toSymbol.HasCompactSpatialSupport)
    (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : Symbol n V U (m' + m - 1), r.coefficient =
      (a.toSymbol.sharp b.toSymbol hb -
        cutoffSymbol χ (a.principal.comp b.principal)).coefficient := by
  obtain ⟨ra, hra⟩ := a.exists_sub_cutoffSymbol_principal χ
  obtain ⟨rb, hrb⟩ := b.exists_sub_cutoffSymbol_principal χ
  -- `χ(ξ)² (σ(a) ∘ σ(b))` and `χ(ξ) (σ(a) ∘ σ(b))` agree at frequencies of norm at least `2`.
  set d := (cutoffSymbol χ a.principal).comp (cutoffSymbol χ b.principal) -
    cutoffSymbol χ (a.principal.comp b.principal)
  have hd : ∀ x ξ, 2 ≤ ‖ξ‖ → d.coefficient (x, ξ) = 0 := fun x ξ hξ ↦ by
    simp [d, χ.apply_eq_one_of_two_le_norm hξ]
  refine ⟨Symbol.inclusion (by simp) (a.toSymbol.sharpRemainder b.toSymbol hb 1) +
    Symbol.inclusion (by linarith) ((cutoffSymbol χ a.principal).comp rb) +
    Symbol.inclusion (by linarith) (ra.comp b.toSymbol) +
    Symbol.ofBoundedFrequencySupport d.coefficient d.contDiff_coefficient 2 hd, ?_⟩
  funext ⟨x, ξ⟩
  have hra' := congrFun hra (x, ξ)
  have hrb' := congrFun hrb (x, ξ)
  simp only [Symbol.coefficient_sub, Pi.sub_apply] at hra' hrb'
  simp only [d, Symbol.coefficient_add, Symbol.coefficient_sub, Symbol.coefficient_inclusion,
    Symbol.coefficient_ofBoundedFrequencySupport, Symbol.coefficient_sharpRemainder,
    Finset.sum_range_one, Symbol.coefficient_sharpTerm_zero, Symbol.coefficient_comp,
    Pi.add_apply, Pi.sub_apply, hra', hrb',
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

end ClassicalSymbol

end TauCeti
