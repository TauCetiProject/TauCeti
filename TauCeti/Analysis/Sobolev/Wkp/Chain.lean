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
by induction on the order through `TauCeti.Wkp.lowerOrder` and `TauCeti.Wkp.mk`. Any weak
derivative chain of the value of an element of `Wkp` agrees with the recorded derivatives, and its
fields are bounded in `Lᵖ` by the graph norm, so that they converge in `Lᵖ` when the elements
of `Wkp` converge.

## Main declarations

* `TauCeti.Wkp.exists_iteratedGradient_chain`: the weak derivative chain of an element of `Wkp`.
* `TauCeti.Wkp.exists_value_iteratedGradient_ae_eq_of_chain`: an `Lᵖ` weak derivative chain is
  represented by an element of `Wkp`.
* `TauCeti.Wkp.ae_eq_iteratedGradient_and_eLpNorm_le_of_chain`: a weak derivative chain of the
  value of an element of `Wkp` recovers its highest recorded derivative, with `Lᵖ` bounds by the
  graph norm.
* `TauCeti.Wkp.tendsto_eLpNorm_sub_of_tendsto_of_chain`: convergence in `Wkp` gives `Lᵖ`
  convergence of the fields of weak derivative chains of the values.

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

/-- A function almost everywhere equal to the `j`-th recorded derivative of `y ∈ W^{j+1,p}(Ω)`
lies in `Lᵖ(Ω)` with norm at most `‖y‖`. -/
private theorem memLp_and_eLpNorm_le_of_ae_eq_iteratedGradient {j : ℕ}
    {y : Wkp mu Omega p (j + 1)} {G : E → IteratedGradient E j}
    (hG : G =ᵐ[mu.restrict Omega] iteratedGradient j y) :
    MemLp G p (mu.restrict Omega) ∧ eLpNorm G p (mu.restrict Omega) ≤ ENNReal.ofReal ‖y‖ := by
  refine ⟨(Lp.memLp _).ae_eq hG.symm, ?_⟩
  rw [eLpNorm_congr_ae hG, ← Lp.eNorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_iteratedGradient_le j y)

/-- **A weak derivative chain recovers the recorded derivatives.** Let `y ∈ W^{n+1,p}(Ω)` and let
`G 0, …, G n` be a chain of iterated weak gradients on `Ω` of a representative `f` of the value of
`y`. Then `G n` is the highest recorded derivative of `y`, and every `G i` with `i ≤ n` lies in
`Lᵖ(Ω)` with norm at most `‖y‖`. -/
theorem ae_eq_iteratedGradient_and_eLpNorm_le_of_chain :
    ∀ (n : ℕ) (y : Wkp mu Omega p (n + 1)) {f : E → ℝ} {G : (i : ℕ) → E → IteratedGradient E i},
    value (n + 1) y =ᵐ[mu.restrict Omega] f →
    HasWeakFDerivOn mu Omega f (fun x => innerSL ℝ (G 0 x)) →
    (∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1))) →
    G n =ᵐ[mu.restrict Omega] iteratedGradient n y ∧
      ∀ i ≤ n, MemLp (G i) p (mu.restrict Omega) ∧
        eLpNorm (G i) p (mu.restrict Omega) ≤ ENNReal.ofReal ‖y‖
  | 0, y, f, G, hy, h0, _ => by
    have hG0 : G 0 =ᵐ[mu.restrict Omega] iteratedGradient 0 y := by
      filter_upwards [(h0.congr_ae hy.symm).ae_eq (hasWeakFDerivOn_value y)] with x hx
      exact innerSL_inj.1 hx
    refine ⟨hG0, fun i hi => ?_⟩
    obtain rfl := Nat.le_zero.1 hi
    exact memLp_and_eLpNorm_le_of_ae_eq_iteratedGradient hG0
  | n + 1, y, f, G, hy, h0, hG => by
    obtain ⟨hGn, hb⟩ := ae_eq_iteratedGradient_and_eLpNorm_le_of_chain n (lowerOrder (n + 1) y)
      (by rwa [← value_succ]) h0 fun i hi => hG i (by omega)
    have hGn1 : G (n + 1) =ᵐ[mu.restrict Omega] iteratedGradient (n + 1) y :=
      ((hG n (by omega)).congr_ae hGn).ae_eq (hasWeakFDerivOn_iteratedGradient n y)
    refine ⟨hGn1, fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · obtain ⟨hm, hle⟩ := hb i (by omega)
      exact ⟨hm, hle.trans (ENNReal.ofReal_le_ofReal (norm_lowerOrder_le _ y))⟩
    · exact memLp_and_eLpNorm_le_of_ae_eq_iteratedGradient hGn1

/-- **Convergence of weak derivative chains.** Let `y a → w` in `W^{n+1,p}(Ω)` along a filter `l`,
with values representing `f a` and `g` almost everywhere on `Ω`, and let `G a` and `H` be chains of
iterated weak gradients on `Ω` of `f a` and `g`. Then `G a i → H i` in `Lᵖ(Ω)` along `l` for every
`i ≤ n`. -/
theorem tendsto_eLpNorm_sub_of_tendsto_of_chain (n : ℕ) {α : Type*} {l : Filter α}
    {y : α → Wkp mu Omega p (n + 1)} {w : Wkp mu Omega p (n + 1)}
    (hyw : Filter.Tendsto y l (nhds w)) {f : α → E → ℝ} {g : E → ℝ}
    {G : α → (i : ℕ) → E → IteratedGradient E i} {H : (i : ℕ) → E → IteratedGradient E i}
    (hy : ∀ a, value (n + 1) (y a) =ᵐ[mu.restrict Omega] f a)
    (hw : value (n + 1) w =ᵐ[mu.restrict Omega] g)
    (hG0 : ∀ a, HasWeakFDerivOn mu Omega (f a) fun x => innerSL ℝ (G a 0 x))
    (hG : ∀ a, ∀ i < n, HasWeakFDerivOn mu Omega (G a i) (G a (i + 1)))
    (hH0 : HasWeakFDerivOn mu Omega g fun x => innerSL ℝ (H 0 x))
    (hH : ∀ i < n, HasWeakFDerivOn mu Omega (H i) (H (i + 1))) {i : ℕ} (hi : i ≤ n) :
    Filter.Tendsto (fun a => eLpNorm (G a i - H i) p (mu.restrict Omega)) l (nhds 0) := by
  -- The chain `G a - H` of `f a - g` bounds the difference of the fields by `‖y a - w‖`.
  have hle : ∀ a, eLpNorm (G a i - H i) p (mu.restrict Omega) ≤ ENNReal.ofReal ‖y a - w‖ := by
    intro a
    have hval : value (n + 1) (y a - w) =ᵐ[mu.restrict Omega] f a - g := by
      rw [← valueL_apply, map_sub, valueL_apply, valueL_apply]
      filter_upwards [Lp.coeFn_sub (value (n + 1) (y a)) (value (n + 1) w), hy a, hw]
        with z hz hyz hwz
      rw [hz, Pi.sub_apply, Pi.sub_apply, hyz, hwz]
    have h0 : HasWeakFDerivOn mu Omega (f a - g)
        fun x => innerSL ℝ ((fun j => G a j - H j) 0 x) := by
      have heq : (fun x => innerSL ℝ ((fun j => G a j - H j) 0 x)) =
          (fun x => innerSL ℝ (G a 0 x)) - fun x => innerSL ℝ (H 0 x) :=
        funext fun x => by simp only [Pi.sub_apply, map_sub]
      rw [heq]
      exact (hG0 a).sub hH0
    exact ((ae_eq_iteratedGradient_and_eLpNorm_le_of_chain n (y a - w) hval h0
      fun j hj => (hG a j hj).sub (hH j hj)).2 i hi).2
  have h0 : Filter.Tendsto (fun a => ENNReal.ofReal ‖y a - w‖) l (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hyw)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hle

end Wkp

end TauCeti
