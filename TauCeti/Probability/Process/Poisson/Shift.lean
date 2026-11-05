/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.Process.HasIndepIncrements
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw

/-!
# Deterministic shifts of Poisson counts

A nondecreasing count process starting at zero, with independent rate-`r` Poisson increments,
has the same full path law after any deterministic shift and subtraction of its current count.
The conclusion is equality on the product sigma-algebra of all time coordinates.

Independence of that full shifted process from the natural history is supplied, without any
Poisson-law assumption, by `ProbabilityTheory.HasIndepIncrements.indepFun_shift_nat`.
The rate may be zero, and no continuity or moment assumptions are used.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}

/-- A count process with independent Poisson increments has its original full path law after
any deterministic shift and subtraction of its current count. This includes rate zero and
shifting at time zero. -/
theorem HasIndepIncrements.identDistrib_shift_of_hasLaw_poissonMeasure (hN : HasIndepIncrements N P)
    (hm : ∀ t, Measurable (N t)) (h0 : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω)) (r t : ℝ≥0)
    (hlaw : ∀ s u, s ≤ u → HasLaw (fun ω ↦ N u ω - N s ω)
      (poissonMeasure (r * (u - s))) P) :
    IdentDistrib (fun ω s ↦ N (t + s) ω - N t ω) (fun ω s ↦ N s ω) P P := by
  let Z : ℝ≥0 → Ω → ℤ := fun s ω ↦ (N s ω : ℤ)
  have hmZ (s : ℝ≥0) : Measurable (Z s) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℤ))).comp (hm s)
  have hZ : HasIndepIncrements Z P := hN.natCast hmono
  have h0Z : ∀ᵐ ω ∂P, Z 0 ω = 0 := by
    filter_upwards [h0] with ω hω using by simp [Z, hω]
  have hinclaw : ∀ s u : ℝ≥0, s ≤ u →
      IdentDistrib (fun ω ↦ Z (t + u) ω - Z (t + s) ω)
        (fun ω ↦ Z u ω - Z s ω) P P := by
    intro s u hsu
    have h1 := hlaw (t + s) (t + u) (add_le_add le_rfl hsu)
    have h2 := hlaw s u hsu
    rw [add_tsub_add_eq_tsub_left] at h1
    have hNat : IdentDistrib (fun ω ↦ N (t + u) ω - N (t + s) ω)
        (fun ω ↦ N u ω - N s ω) P P :=
      ⟨h1.aemeasurable, h2.aemeasurable, h1.map_eq.trans h2.map_eq.symm⟩
    have hInt := hNat.comp (measurable_of_countable (fun n : ℕ ↦ (n : ℤ)))
    have hleft : (fun ω ↦ Z (t + u) ω - Z (t + s) ω) =ᵐ[P]
        (fun ω ↦ ((N (t + u) ω - N (t + s) ω : ℕ) : ℤ)) := by
      filter_upwards [hmono] with ω hω
      exact (Int.ofNat_sub (hω (add_le_add le_rfl hsu))).symm
    have hright : (fun ω ↦ Z u ω - Z s ω) =ᵐ[P]
        (fun ω ↦ ((N u ω - N s ω : ℕ) : ℤ)) := by
      filter_upwards [hmono] with ω hω
      exact (Int.ofNat_sub (hω hsu)).symm
    exact (IdentDistrib.of_ae_eq ((hmZ _).sub (hmZ _)).aemeasurable hleft).trans
        (hInt.trans (IdentDistrib.of_ae_eq ((hmZ _).sub (hmZ _)).aemeasurable hright).symm)
  have hdist := hZ.identDistrib_shift hmZ h0Z t hinclaw
  have htoNat : Measurable (fun (z : ℝ≥0 → ℤ) s ↦ (z s).toNat) := by fun_prop
  convert hdist.comp htoNat using 1 <;> ext ω s <;> simp [Z]

end ProbabilityTheory
