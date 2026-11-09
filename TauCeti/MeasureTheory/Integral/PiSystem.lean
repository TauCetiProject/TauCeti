/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# A Dynkin (π-λ) step for Bochner integrals

If a function's integral vanishes on the whole space and on every member of a π-system generating
a sub-σ-algebra, then it vanishes on every set measurable for that sub-σ-algebra; in particular,
for a π-system generating the ambient σ-algebra, it vanishes on every measurable set.

This is the Bochner counterpart of Mathlib's `ℝ≥0∞`-valued
`MeasureTheory.lintegral_eq_lintegral_of_isPiSystem`. Stating it for an arbitrary π-system rather
than for a specific one (rectangles, boxes) lets a single theorem serve every product-measure
arity. A countable cover by members of the π-system gives an almost-everywhere uniqueness
criterion for functions integrable on the covering sets, without global integrability.
-/

public section

namespace TauCeti

open MeasureTheory

/-- **The Dynkin (π-λ) step for Bochner integrals.** A function whose integral vanishes on the
whole space and on every member of a π-system generating a sub-σ-algebra `m` has vanishing
integral on every `m`-measurable set. Taking `m = m0` gives vanishing on every measurable set. -/
theorem setIntegral_eq_zero_of_isPiSystem {X E : Type*} {m m0 : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ρ : Measure X} {S : Set (Set X)} (hm : m ≤ m0)
    (hgen : m = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) {f : X → E}
    (hf : Integrable f ρ) (huniv : ∫ x, f x ∂ρ = 0) (hS : ∀ s ∈ S, ∫ x in s, f x ∂ρ = 0) :
    ∀ u, MeasurableSet[m] u → ∫ x in u, f x ∂ρ = 0 := by
  intro u hu
  induction u, hu using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact hS s hs
  | compl u hu ih => rw [setIntegral_compl (hm u hu) hf, huniv, ih, sub_zero]
  | iUnion u hd hu ih => simp [integral_iUnion (fun i => hm _ (hu i)) hd hf.integrableOn, ih]

/-- A function with zero integral on a generating π-system is zero almost everywhere if
members of that system give a countable cover on which the function is integrable.
No finiteness assumption on the ambient measure or global integrability is required. -/
theorem ae_eq_zero_of_forall_setIntegral_eq_zero_of_isPiSystem
    {X E κ : Type*} {m : MeasurableSpace X} [Countable κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {C : Set (Set X)}
    (hgen : MeasurableSpace.generateFrom C = m) (hpi : IsPiSystem C)
    (s : κ → Set X) (hs : ∀ n, s n ∈ C) (hcover : ⋃ n, s n = Set.univ)
    {f : X → E} (hf : ∀ n, IntegrableOn f (s n) μ)
    (hzero : ∀ R ∈ C, ∫ x in R, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hmeas {R} (hR : R ∈ C) : MeasurableSet R :=
    hgen ▸ MeasurableSpace.measurableSet_generateFrom hR
  suffices h : f =ᵐ[μ.restrict (⋃ n, s n)] 0 by
    simpa only [hcover, Measure.restrict_univ] using h
  apply (ae_eq_restrict_iUnion_iff _ _ _).2
  intro n
  apply (hf n).ae_eq_zero_of_forall_setIntegral_eq_zero
  intro R hR _
  refine setIntegral_eq_zero_of_isPiSystem le_rfl hgen.symm hpi (hf n) ?_ ?_ R hR
  · simpa only [Measure.restrict_univ] using hzero _ (hs n)
  · intro Q hQ
    rw [Measure.restrict_restrict (hmeas hQ)]
    by_cases hne : (Q ∩ s n).Nonempty
    · exact hzero _ (hpi _ hQ _ (hs n) hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp

end TauCeti
