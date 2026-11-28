/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import TauCeti.MeasureTheory.Function.Lp.Operator.Local

/-!
# Operators that preserve supports are multiplication operators

Let `μ` be a sigma-finite measure, let `1 ≤ p < ∞`, and let `S` be a bounded operator on the scalar
space `Lᵖ(μ)`. This file proves that `S` is multiplication by an essentially bounded function
`a ∈ L∞(μ)` (`MeasureTheory.Lp.multiplicationOperator`) exactly when it is local, that is, does not
enlarge supports: whenever `f` vanishes almost everywhere off a measurable set `s`, so does `S f`
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_iff`). Equivalently, `S` commutes with every
multiplication operator (`MeasureTheory.Lp.forall_commute_multiplicationOperator_iff`):
the commutant of `L∞(μ)` acting on `Lᵖ(μ)` is `L∞(μ)` itself. The operator norm of
multiplication by `a` is `‖a‖` (`MeasureTheory.Lp.norm_multiplicationOperator`), so the multiplier
has `L∞` norm `‖S‖`.

On a topological space whose measure is inner regular for compact sets, compact sets suffice
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_isCompact`): if `S f` vanishes almost
everywhere off every compact set off which `f` vanishes, then `S` is a multiplication operator.
This is the form that applies to singular integral operators, which are only known through their
action away from the support of their argument.

These are the scalar cases of the theorem that a local operator from `Lᵖ(α, E)` to `Lᵖ(α, F)` is
multiplication by an operator-valued symbol `m : α → E →L[𝕜] F`
(`ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero`): for `E = F = 𝕜` the symbol
is multiplication by `m x 1`. That theorem asks `𝕜` to be complete and separable, as `ℝ` and `ℂ`
are. The scalar field matters: on `Lᵖ(μ; E)` with `E` of dimension at least two, applying a fixed
linear map of `E` at every point is local, and it is not multiplication by a scalar function unless
that map is a multiple of the identity.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Section IX.6 (the multiplication
  algebra `L∞(μ)` on `L²(μ)` is maximal abelian).
-/

public section

open Set Filter Topology
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [TopologicalSpace.SeparableSpace 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}

/-- **Local operators on scalar `Lᵖ` are multiplication operators.** On a sigma-finite measure
space and for `p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f` vanishes
almost everywhere off every measurable set off which `f` vanishes is multiplication by some
`a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_forall_ae_eq_zero [SigmaFinite μ] (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  obtain ⟨m, hm, hbound, hSm⟩ := S.exists_forall_ae_eq_apply_of_forall_ae_eq_zero hp hS
  -- the operator `m x` on `𝕜` is multiplication by `m x 1`
  have ha : MemLp (fun x ↦ m x 1) ∞ μ :=
    memLp_top_of_bound ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).continuous.comp_stronglyMeasurable
      hm).aestronglyMeasurable ‖S‖ (hbound.mono fun x hx ↦ by
        simpa using ((m x).le_opNorm 1).trans (by simpa using hx))
  refine ⟨ha.toLp _, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  filter_upwards [hSm f, multiplicationOperator_ae (ha.toLp _) f, ha.coeFn_toLp] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- **Multiplication operators are the local operators.** On a sigma-finite measure space and for
`p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` is multiplication by some
`a ∈ L∞(μ)` if and only if `S f` vanishes almost everywhere off every measurable set off which `f`
vanishes. -/
theorem exists_eq_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a) ↔
      ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
        ∀ᵐ x ∂μ, x ∉ s → S f x = 0 := by
  refine ⟨?_, exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp⟩
  rintro ⟨a, rfl⟩ f s - hf
  filter_upwards [multiplicationOperator_ae a f, hf] with x h₁ h₂ hx
  rw [h₁, h₂ hx, smul_zero]

/-- **The commutant of `L∞`.** On a sigma-finite measure space and for `p < ∞`, a bounded operator
on the scalar space `Lᵖ(μ)` commutes with every multiplication operator if and only if it is
itself a multiplication operator: the multiplication operators form a maximal commutative family
of operators on `Lᵖ(μ)`. -/
theorem forall_commute_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∀ b : Lp 𝕜 ∞ μ, Commute S (multiplicationOperator b)) ↔
      ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  refine ⟨fun h ↦ (exists_eq_multiplicationOperator_iff hp).2 fun f s hs hf ↦ ?_,
    fun ⟨a, ha⟩ b ↦ ha ▸ commute_multiplicationOperator a b⟩
  -- `f` is fixed by multiplication by `1_s`, which commutes with `S`
  have hb : MemLp (s.indicator fun _ ↦ (1 : 𝕜)) ∞ μ :=
    (memLp_top_const 1).indicator hs.nullMeasurableSet
  have hfix : multiplicationOperator (hb.toLp _) f = f := by
    refine Lp.ext ?_
    filter_upwards [multiplicationOperator_ae (hb.toLp _) f, hb.coeFn_toLp, hf] with x h₁ h₂ h₃
    rw [h₁, h₂]
    by_cases hx : x ∈ s <;> simp [hx, h₃]
  have hcomm : S f = multiplicationOperator (hb.toLp _) (S f) := by
    conv_lhs => rw [← hfix]
    exact congrArg (· f) (h (hb.toLp _)).eq
  filter_upwards [multiplicationOperator_ae (hb.toLp _) (S f), hb.coeFn_toLp] with x h₁ h₂ hx
  rw [hcomm, h₁, h₂, indicator_of_notMem hx, zero_smul]

/-- **Operators that preserve compact supports are multiplication operators.** Let `μ` be a
sigma-finite measure on a Hausdorff space, inner regular for compact sets on sets of finite
measure, and let `p < ∞`. A bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f`
vanishes almost everywhere off every compact set off which `f` vanishes almost everywhere is
multiplication by some `a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_isCompact [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [SigmaFinite μ] [μ.InnerRegularCompactLTTop]
    (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a :=
  exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp fun f _ hs hf ↦
    S.ae_apply_eq_zero_of_forall_isCompact hp hS f hs hf

end MeasureTheory.Lp
