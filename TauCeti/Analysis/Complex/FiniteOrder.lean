/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

/-!
# Functions of finite order

`TauCeti.IsFiniteOrder f` means that `f` satisfies `OrderLE f A` for some real exponent.
As with `OrderLE`, holomorphy is not part of the predicate. This separates the growth
condition from the analytic hypotheses in applications to entire functions.

Finite order is preserved by sums, products, and affine substitution. Multiplication by
a nonzero polynomial and invertible affine substitution preserve it in both directions.
These equivalences allow pole-clearing polynomials and changes of variable to be removed
from growth hypotheses. For continuous functions, finite order is equivalent to a global
bound by `C * exp (‖z‖ ^ A)` with positive constants. The exponential has finite order,
whereas its self-composition does not.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11.
-/

public section

open Complex Filter Asymptotics Bornology

namespace TauCeti

/-- A function has finite order if it has order at most some real exponent.
Entirety is a separate hypothesis. -/
def IsFiniteOrder (f : ℂ → ℂ) : Prop := ∃ A : ℝ, OrderLE f A

variable {f g : ℂ → ℂ} {A : ℝ}

/-- The existential characterization of finite order. -/
theorem isFiniteOrder_def : IsFiniteOrder f ↔ ∃ A : ℝ, OrderLE f A := Iff.rfl

/-- Any upper bound on the order gives finite order. -/
theorem OrderLE.isFiniteOrder (h : OrderLE f A) : IsFiniteOrder f := ⟨A, h⟩

namespace IsFiniteOrder

/-- A finite-order function has a nonnegative upper bound on its order. -/
theorem exists_nonneg (h : IsFiniteOrder f) : ∃ A : ℝ, 0 ≤ A ∧ OrderLE f A := by
  obtain ⟨A, hA⟩ := h
  exact ⟨max A 0, le_max_right _ _, hA.mono (le_max_left _ _)⟩

/-- Finite order passes to functions dominated at infinity. -/
theorem of_isBigO (hg : IsFiniteOrder g) (hfg : f =O[cobounded ℂ] g) :
    IsFiniteOrder f := by
  obtain ⟨A, hA⟩ := hg
  exact (hfg.orderLE hA).isFiniteOrder

/-- The sum of two finite-order functions has finite order. -/
theorem add (hf : IsFiniteOrder f) (hg : IsFiniteOrder g) :
    IsFiniteOrder (fun z ↦ f z + g z) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ((hA.mono (le_max_left A B)).add (hB.mono (le_max_right A B))).isFiniteOrder

/-- The product of two finite-order functions has finite order. -/
theorem mul (hf : IsFiniteOrder f) (hg : IsFiniteOrder g) :
    IsFiniteOrder (fun z ↦ f z * g z) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ((hA.mono (le_max_left A B)).mul (hB.mono (le_max_right A B))).isFiniteOrder

/-- An affine pullback of a finite-order function has finite order, even for a constant map. -/
theorem comp_mul_add (hf : IsFiniteOrder f) (a b : ℂ) :
    IsFiniteOrder (fun z ↦ f (a * z + b)) := by
  obtain ⟨A, hA⟩ := hf
  exact (hA.comp_mul_add a b).isFiniteOrder

end IsFiniteOrder

/-- Constants have finite order. -/
@[simp]
theorem isFiniteOrder_const (c : ℂ) : IsFiniteOrder (fun _ ↦ c) :=
  (orderLE_const c 0).isFiniteOrder

/-- Every polynomial has finite order. -/
theorem _root_.Polynomial.isFiniteOrder_eval (p : Polynomial ℂ) : IsFiniteOrder p.eval :=
  p.orderLE_eval.isFiniteOrder

/-- Multiplication by a nonzero polynomial preserves finite order in both directions. -/
@[simp]
theorem isFiniteOrder_polynomial_mul_iff {p : Polynomial ℂ} (hp : p ≠ 0) :
    IsFiniteOrder (fun z ↦ p.eval z * f z) ↔ IsFiniteOrder f := by
  refine ⟨fun h ↦ h.of_isBigO ?_, fun h ↦ p.isFiniteOrder_eval.mul h⟩
  have hpoly := Polynomial.isBigO_cobounded_of_degree_le
    (P := (1 : Polynomial ℂ)) (Q := p) (by simpa using Polynomial.zero_le_degree_iff.mpr hp)
  simpa using hpoly.mul (isBigO_refl f (cobounded ℂ))

/-- A nonconstant affine change of variable preserves finite order in both directions. -/
@[simp]
theorem isFiniteOrder_comp_mul_add_iff {a b : ℂ} (ha : a ≠ 0) :
    IsFiniteOrder (fun z ↦ f (a * z + b)) ↔ IsFiniteOrder f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_mul_add a b⟩
  have hi := h.comp_mul_add a⁻¹ (-a⁻¹ * b)
  convert hi using 1
  ext z
  congr 1
  field_simp
  ring

/-- For a continuous function, finite order is equivalent to a global exponential-of-power
bound. Continuity fills in the compact region omitted by the asymptotic definition. -/
theorem isFiniteOrder_iff_exists_bound (hf : Continuous f) :
    IsFiniteOrder f ↔ ∃ A : ℝ, 0 < A ∧ ∃ C > 0, ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ A) := by
  constructor
  · intro h
    obtain ⟨A, hA0, hA⟩ := h.exists_nonneg
    let B := A + 1
    have hB : A < B := by dsimp [B]; linarith
    have hB0 : 0 < B := by dsimp [B]; linarith
    let g : ℂ → ℝ := fun z ↦ Real.exp (‖z‖ ^ B)
    have hg : Continuous g :=
      Real.continuous_exp.comp (continuous_norm.rpow_const fun _ ↦ Or.inr hB0.le)
    have hq : Continuous (fun z ↦ ‖f z‖ / g z) :=
      hf.norm.div hg (fun z ↦ Real.exp_ne_zero _)
    have hO : (fun z ↦ ‖f z‖ / g z) =O[cocompact ℂ] (1 : ℂ → ℝ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact (div_isBoundedUnder_of_isBigO (hA.isBigO hB).norm_left).isBigO_const one_ne_zero
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (hq.isBounded_range_iff_isBigO.mpr hO)
    refine ⟨B, hB0, max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z ↦ ?_⟩
    apply (div_le_iff₀ (Real.exp_pos _)).mp
    exact (le_abs_self _).trans ((hC _ (Set.mem_range_self z)).trans (le_max_left _ _))
  · rintro ⟨A, _, C, _, hC⟩
    refine ⟨A, orderLE_def.mpr fun B hB ↦ ?_⟩
    have hO : f =O[cobounded ℂ] (fun z ↦ Real.exp (‖z‖ ^ A)) := by
      exact IsBigO.of_bound C (Filter.Eventually.of_forall fun z ↦ by simpa using hC z)
    exact hO.trans (by simpa using isBigO_exp_mul_norm_rpow (E := ℂ) 1 hB)

/-- The exponential is a nonconstant example of a finite-order entire function. -/
theorem isFiniteOrder_cexp : IsFiniteOrder cexp :=
  (orderLE_cexp_iff.mpr le_rfl).isFiniteOrder

/-- The double exponential has no finite order: on the positive real axis its logarithm
outgrows every power. -/
theorem not_isFiniteOrder_cexp_cexp : ¬ IsFiniteOrder (fun z ↦ cexp (cexp z)) := by
  rintro ⟨A, hA⟩
  let B := max A 0 + 1
  have hB : A < B := by dsimp [B]; have := le_max_left A 0; linarith
  have ht := RCLike.tendsto_ofReal_atTop_cobounded ℂ
  have hO : (fun x : ℝ ↦ Real.exp (Real.exp x)) =O[atTop]
      fun x : ℝ ↦ Real.exp (‖(x : ℂ)‖ ^ B) := by
    simpa [Function.comp_def, norm_exp, Complex.exp_ofReal_re] using
      ((hA.isBigO hB).comp_tendsto ht).norm_left
  rw [Real.isBigO_exp_comp_exp_comp] at hO
  have hpow : (fun x : ℝ ↦ x ^ B) =o[atTop] Real.exp :=
    isLittleO_rpow_exp_atTop B
  have hl : Tendsto (fun x : ℝ ↦ Real.exp x - ‖(x : ℂ)‖ ^ B) atTop atTop := by
    have he := IsEquivalent.refl.sub_isLittleO hpow
    have hlim := he.symm.tendsto_atTop Real.tendsto_exp_atTop
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [abs_of_nonneg hx]
  exact not_isBoundedUnder_of_tendsto_atTop hl hO

end TauCeti
