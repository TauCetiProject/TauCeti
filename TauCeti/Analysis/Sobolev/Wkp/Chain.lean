/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# Iterated weak gradient chains of `W^{k,p}`

An element of `TauCeti.Wkp mu Ω p (n + 1)` is described by a chain of `Lᵖ` fields
`G 0, …, G n` with `G i : E → TauCeti.IteratedGradient E i`: the value has weak derivative
`innerSL ℝ ∘ G 0`, and each `G (i + 1)` is the weak derivative of `G i`. This file extracts such a
chain from an element of `Wkp` and, conversely, assembles an element of `Wkp` from an `Lᵖ` chain,
by induction on the order through `TauCeti.Wkp.lowerOrder` and `TauCeti.Wkp.mk`.

## Main declarations

* `TauCeti.Wkp.exists_iteratedGradient_chain`: the weak derivative chain of an element of `Wkp`.
* `TauCeti.Wkp.exists_value_iteratedGradient_ae_eq_of_chain`: an `Lᵖ` weak derivative chain is
  represented by an element of `Wkp`.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- **The weak derivative chain of a Sobolev function.** An element `v` of `W^{n+1,p}(Ω)` has
`Lᵖ` iterated weak gradients `G 0, …, G n`: the value of `v` has weak derivative
`innerSL ℝ ∘ G 0`, each `G (i + 1)` is the weak derivative of `G i`, and `G n` is the highest
recorded derivative of `v`. -/
theorem exists_iteratedGradient_chain (n : ℕ) (v : Wkp mu Omega p (n + 1)) :
    ∃ G : (i : ℕ) → E → IteratedGradient E i,
      HasWeakFDerivOn mu Omega (value (n + 1) v) (fun x => innerSL ℝ (G 0 x)) ∧
      (∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1))) ∧
      (∀ i ≤ n, MemLp (G i) p (mu.restrict Omega)) ∧
      G n =ᵐ[mu.restrict Omega] iteratedGradient n v := by
  induction n with
  | zero =>
    refine ⟨Function.update (fun i _ => 0) 0 (iteratedGradient 0 v), ?_, fun i hi => absurd hi
      (Nat.not_lt_zero i), fun i hi => ?_, ?_⟩
    · simpa only [Function.update_self] using hasWeakFDerivOn_value v
    · obtain rfl := Nat.le_zero.1 hi
      simpa only [Function.update_self] using Lp.memLp (iteratedGradient 0 v)
    · simp only [Function.update_self, Filter.EventuallyEq.rfl]
  | succ n ih =>
    obtain ⟨G, h0, hG, hGp, htop⟩ := ih (lowerOrder (n + 1) v)
    refine ⟨Function.update G (n + 1) (iteratedGradient (n + 1) v), ?_, fun i hi => ?_,
      fun i hi => ?_, ?_⟩
    · rw [Function.update_of_ne (Nat.succ_ne_zero n).symm, value_succ]
      exact h0
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hG i hi
      · rw [Function.update_self]
        exact (hasWeakFDerivOn_iteratedGradient i v).congr_ae htop.symm
    · rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hGp i (by omega)
      · rw [Function.update_self]
        exact Lp.memLp _
    · simp only [Function.update_self, Filter.EventuallyEq.rfl]

/-- **An `Lᵖ` weak derivative chain is a Sobolev function.** If `u ∈ Lᵖ(Ω)` has weak derivative
`innerSL ℝ ∘ G 0`, each `G (i + 1)` is the weak derivative of `G i` for `i < n`, and every `G i`
with `i ≤ n` is in `Lᵖ(Ω)`, then `u` is represented by an element of `W^{n+1,p}(Ω)` whose highest
recorded derivative is `G n`. -/
theorem exists_value_iteratedGradient_ae_eq_of_chain (n : ℕ) {u : E → ℝ}
    {G : (i : ℕ) → E → IteratedGradient E i} (hu : MemLp u p (mu.restrict Omega))
    (h0 : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1)))
    (hGp : ∀ i ≤ n, MemLp (G i) p (mu.restrict Omega)) :
    ∃ v : Wkp mu Omega p (n + 1), value (n + 1) v =ᵐ[mu.restrict Omega] u ∧
      iteratedGradient n v =ᵐ[mu.restrict Omega] G n := by
  induction n with
  | zero =>
    have hg : MemLp (G 0 : E → E) p (mu.restrict Omega) := hGp 0 le_rfl
    have hw : HasWeakFDerivOn mu Omega (hu.toLp u) fun x => innerSL ℝ (hg.toLp (G 0) x) := by
      refine (h0.congr_ae hu.coeFn_toLp.symm).congr_ae_deriv ?_
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]
    refine ⟨W1p.mk _ _ hw, ?_, ?_⟩
    · exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ p (mu.restrict Omega) => (f : E → ℝ))
        ((value_one (W1p.mk _ _ hw)).trans (W1p.value_mk _ _ hw)))).trans hu.coeFn_toLp
    · exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp E p (mu.restrict Omega) => (f : E → E))
        ((iteratedGradient_zero (W1p.mk _ _ hw)).trans (W1p.gradient_mk _ _ hw)))).trans
        hg.coeFn_toLp
  | succ n ih =>
    obtain ⟨v, hv, htop⟩ := ih (fun i hi => hG i (by omega)) (fun i hi => hGp i (by omega))
    have hg := hGp (n + 1) le_rfl
    refine ⟨mk n v (hg.toLp (G (n + 1)))
      (((hG n (Nat.lt_succ_self n)).congr_ae htop.symm).congr_ae_deriv hg.coeFn_toLp.symm), ?_, ?_⟩
    · rw [value_mk]
      exact hv
    · rw [iteratedGradient_mk]
      exact hg.coeFn_toLp

end Wkp

end TauCeti
