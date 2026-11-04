/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# The divisor of a meromorphic `1`-form

Let `ω` be a `1`-form on a Riemann surface `X` which is meromorphic at every point. Near each point
its coefficient in a chart is a meromorphic function of one variable, whose zeros and poles are
isolated; so `ω` has order `0` or `⊤` away from a closed discrete set
(`TauCeti.RiemannSurface.OneForm.setOf_order_eq_zero_or_top_mem_codiscrete`). When `X` is compact
that set is finite, and the orders assemble into the **divisor**
`div ω = Σ_x ord_x(ω) · [x]` (`TauCeti.RiemannSurface.OneForm.divisor`), a finite formal sum of
points (`TauCeti.AlgebraicGeometry.WeilDivisor`). The divisor of a holomorphic `1`-form is
effective.

On a compact connected Riemann surface, multiplying a `1`-form `ω` which is meromorphic and of
finite order at every point by a nonzero meromorphic function `f` adds the divisor of `f`:
`div (f ω) = div f + div ω` (`TauCeti.RiemannSurface.OneForm.divisor_smul`), where `div f` is the
principal divisor of the order system of meromorphic functions
(`TauCeti.RiemannSurface.MeromorphicFunction.orderSystem`). Consequently two meromorphic `1`-forms
which differ by a nonzero meromorphic function have linearly equivalent divisors; this is the
invariance underlying the canonical divisor class.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (divisors) and §17 (the divisor of a meromorphic `1`-form and canonical divisors).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter V §1 (divisors of meromorphic `1`-forms and
  canonical divisors).
* Mathlib's `MeromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top` in
  `Mathlib/Analysis/Meromorphic/Order.lean` supplies the discreteness, read in charts.
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

open AlgebraicGeometry WeilDivisor

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {ω : OneForm X} {x : X}

/-- Near a point where it is meromorphic, a `1`-form has order `0` or `⊤` at every other point:
its zeros and poles are isolated. -/
theorem MeromorphicAt.eventually_order_eq_zero_or_top (hω : ω.MeromorphicAt x) :
    ∀ᶠ y in 𝓝[≠] x, ω.order y = 0 ∨ ω.order y = ⊤ := by
  set c := chartAt ℂ x
  have hcx := mem_chart_source ℂ x
  obtain ⟨U, hU, hpU, hUo⟩ : ∃ U : Set ℂ, MeromorphicOn (ω.coeff c) U ∧ c x ∈ U ∧ IsOpen U := by
    obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.1
      (eventually_nhdsWithin_iff.1 ((meromorphicAt_def ω x).1 hω).eventually_analyticAt)
    refine ⟨V, fun z hz ↦ ?_, hpV, hVo⟩
    rcases eq_or_ne z (c x) with rfl | hne
    · exact (meromorphicAt_def ω x).1 hω
    · exact (hV hz hne).meromorphicAt
  have hS := mem_codiscreteWithin.1
    hU.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top (c x) hpU
  rw [disjoint_principal_right] at hS
  have hev : ∀ᶠ z in 𝓝[≠] c x, _root_.meromorphicOrderAt (ω.coeff c) z = 0 ∨
      _root_.meromorphicOrderAt (ω.coeff c) z = ⊤ := by
    filter_upwards [hS, nhdsWithin_le_nhds (hUo.mem_nhds hpU)] with z hz hzU
    simpa [hzU, or_iff_not_imp_left] using hz
  filter_upwards [(tendsto_chartAt_nhdsNE x).eventually hev,
    nhdsWithin_le_nhds (c.open_source.mem_nhds hcx)] with y hy hys
  rwa [order_eq_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hys]

/-- A `1`-form which is meromorphic everywhere has order `0` or `⊤` away from a closed discrete
set. -/
theorem setOf_order_eq_zero_or_top_mem_codiscrete (hω : ∀ x, ω.MeromorphicAt x) :
    {y | ω.order y = 0 ∨ ω.order y = ⊤} ∈ codiscrete X :=
  mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦ (hω x).eventually_order_eq_zero_or_top

section Compact

variable [CompactSpace X]

/-- On a compact Riemann surface, a `1`-form meromorphic everywhere has nonzero finite order at
only finitely many points. -/
theorem finite_support_untop₀_order (hω : ∀ x, ω.MeromorphicAt x) :
    (support fun x ↦ (ω.order x).untop₀).Finite := by
  refine (mem_cofinite.1 (cofinite_le_codiscrete
    (setOf_order_eq_zero_or_top_mem_codiscrete hω))).subset fun y hy ↦ ?_
  simpa [WithTop.untop₀_eq_zero] using hy

open Classical in
/-- The **divisor** `Σ_x ord_x(ω) · [x]` of a `1`-form on a compact Riemann surface which is
meromorphic everywhere. Points where `ω` vanishes on a punctured neighbourhood contribute `0`, as
does the junk value `0` of the divisor of a `1`-form which is not meromorphic everywhere. -/
def divisor (ω : OneForm X) : WeilDivisor X :=
  if hω : ∀ x, ω.MeromorphicAt x then
    Finsupp.ofSupportFinite (fun x ↦ (ω.order x).untop₀) (finite_support_untop₀_order hω)
  else 0

/-- The coefficient of the divisor of a `1`-form meromorphic everywhere at `x` is its order at
`x`, read in `ℤ`. -/
theorem coeff_divisor (hω : ∀ x, ω.MeromorphicAt x) (x : X) :
    WeilDivisor.coeff ω.divisor x = (ω.order x).untop₀ := by
  rw [divisor, dite_eq_left hω]
  rfl

/-- At a point of finite order, the coefficient of the divisor is the order. -/
theorem coe_coeff_divisor (hω : ∀ x, ω.MeromorphicAt x) (hx : ω.order x ≠ ⊤) :
    (WeilDivisor.coeff ω.divisor x : WithTop ℤ) = ω.order x := by
  rw [coeff_divisor hω, WithTop.coe_untop₀_of_ne_top hx]

/-- The divisor of a `1`-form which is not meromorphic everywhere is the junk value `0`. -/
theorem divisor_of_not_forall_meromorphicAt (hω : ¬ ∀ x, ω.MeromorphicAt x) : ω.divisor = 0 := by
  simp [divisor, hω]

/-- The divisor of a holomorphic `1`-form is effective. -/
theorem isEffective_divisor (hω : ∀ x, ω.HolomorphicAt x) : IsEffective ω.divisor := by
  rw [isEffective_iff]
  intro x
  rw [coeff_divisor fun y ↦ (hω y).meromorphicAt]
  rcases eq_or_ne (ω.order x) ⊤ with h | h
  · simp [h]
  · exact WithTop.coe_nonneg.1 ((WithTop.coe_untop₀_of_ne_top h).symm ▸ (hω x).order_nonneg)

variable [ConnectedSpace X]

/-- **`div(f ω) = div f + div ω`.** Multiplying a `1`-form, meromorphic and of finite order
everywhere, by a nonzero meromorphic function adds the divisor of the function to the divisor of
the form. -/
theorem divisor_smul (f : MeromorphicFunction X) (hf : f ≠ 0) (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) :
    (f.finitePart • ω).divisor = (MeromorphicFunction.orderSystem X).principalDivisor
      (Additive.ofMul (Units.mk0 f hf)) + ω.divisor := by
  have hfω (x : X) : (f.finitePart • ω).MeromorphicAt x :=
    (hω x).smul (f.meromorphicAt_finitePart x)
  have hord (x : X) : (f.finitePart • ω).order x = MeromorphicFunction.order x f + ω.order x := by
    rw [order_smul (f.meromorphicAt_finitePart x) (hω x), MeromorphicFunction.order_apply]
  have hf₀ (x : X) : MeromorphicFunction.order x f ≠ ⊤ :=
    (MeromorphicFunction.order x).ne_top_iff.2 hf
  refine WeilDivisor.ext fun x ↦ ?_
  have := MeromorphicFunction.coe_coeff_principalDivisor_orderSystem
    (Additive.ofMul (Units.mk0 f hf)) x
  simp only [toMul_ofMul, Units.val_mk0] at this
  rw [WeilDivisor.coeff_add, coeff_divisor hfω, hord, WithTop.untop₀_add (hf₀ x) (hω₀ x),
    coeff_divisor hω, ← this, WithTop.untop₀_coe]

end Compact

end TauCeti.RiemannSurface.OneForm
