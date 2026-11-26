/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weak mixing of actions of `ℝ`

Let `ℝ` act on a measurable space `X` carrying a measure `μ`. The action is *weakly mixing*
(`MeasureTheory.Measure.IsWeaklyMixing`) when for all measurable sets `A` and `B` the time
averages `T⁻¹ ∫₀ᵀ |μ((t +ᵥ ·)⁻¹' A ∩ B) − μ(A)μ(B)| dt` tend to `0` as `T → ∞`, with the measures
read as real numbers. An integrand that is not interval integrable has integral `0` by Lean's
convention, so the condition holds trivially for such a pair `A`, `B`. The definition therefore
expresses weak mixing only for probability measures invariant under a jointly measurable action,
where the integrand is measurable in `t` and bounded by `1`.

A weakly mixing action preserving a finite measure is ergodic
(`MeasureTheory.Measure.IsWeaklyMixing.ergodicVAdd`): a measurable set `A` whose translates are
almost everywhere equal to `A` makes the integrand for `A = B` the constant `|μ(A) − μ(A)²|`,
which must therefore vanish, so `μ(A)` is `0` or `1`
(`MeasureTheory.Measure.IsWeaklyMixing.measureReal_eq_zero_or_one`). The converse fails: the
translation flow on `AddCircle 1` is ergodic and has the nonconstant eigenfunction
`x ↦ exp(2πix)`.

## Main results

* `MeasureTheory.Measure.IsWeaklyMixing`: weak mixing of a measure under an action of `ℝ`;
* `MeasureTheory.Measure.IsWeaklyMixing.measureReal_eq_zero_or_one`: an almost invariant
  measurable set has measure `0` or `1`, read as a real number;
* `MeasureTheory.Measure.IsWeaklyMixing.ergodicVAdd`: weak mixing of a finite invariant measure
  implies ergodicity;
* `MeasureTheory.Measure.IsWeaklyMixing.map`: the pushforward along an equivariant measurable map
  to a space with a measurable translation action is weakly mixing;
* `MeasurableEmbedding.isWeaklyMixing_map_iff`: along an equivariant measurable embedding, the
  pushforward is weakly mixing exactly when the measure is; in particular weak mixing is
  invariant under measure-preserving isomorphism of actions
  (`MeasureTheory.MeasurePreserving.isWeaklyMixing_iff`);
* `MeasureTheory.Measure.isWeaklyMixing_zero`: the zero measure is weakly mixing;
* `MeasureTheory.Measure.isWeaklyMixing_of_subsingleton`: the action on a one-point space is
  weakly mixing for the zero measure and for the probability measure.

## References

* M. Hochman, *Notes on ergodic theory*, 2012, Section 6.1 (for actions of `ℤ`).
-/

public section

open Filter MeasureTheory Set Topology

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] {μ : Measure X}

/-- An action of `ℝ` on `X` is *weakly mixing* for the measure `μ` if for all measurable sets
`A` and `B` the time averages `T⁻¹ ∫₀ᵀ |μ((t +ᵥ ·)⁻¹' A ∩ B) − μ(A)μ(B)| dt` tend to `0` as
`T → ∞`, the measures being read as real numbers.

When the integrand is not interval integrable, the integral is `0` by Lean's convention and the
condition holds trivially for that pair. The definition expresses weak mixing only when the action
is jointly measurable and `μ` is an invariant probability measure: the integrand is then
measurable in `t` and bounded by `1`. -/
def IsWeaklyMixing (μ : Measure X) : Prop :=
  ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B|) atTop (𝓝 0)

/-- Unfolding `IsWeaklyMixing`. -/
theorem isWeaklyMixing_def : IsWeaklyMixing μ ↔ ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B|) atTop (𝓝 0) :=
  Iff.rfl

/-- **The zero-one law of weak mixing.** If the translates of a measurable set `s` are almost
everywhere equal to `s`, then `μ.real s` is `0` or `1`. No finiteness is assumed, so a set of
infinite measure also qualifies, its real measure being `0`. -/
theorem IsWeaklyMixing.measureReal_eq_zero_or_one (h : IsWeaklyMixing μ) {s : Set X}
    (hs : MeasurableSet s) (hinv : ∀ t : ℝ, (fun x => t +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    μ.real s = 0 ∨ μ.real s = 1 := by
  have hconst : ∀ t : ℝ, μ.real ((fun x => t +ᵥ x) ⁻¹' s ∩ s) = μ.real s := fun t => by
    have hs' : s =ᵐ[μ] s := by rfl
    rw [measureReal_congr ((hinv t).inter hs'), inter_self]
  have h0 := h s s hs hs
  simp_rw [hconst] at h0
  have hc := abs_eq_zero.1 (TauCeti.intervalIntegral.eq_zero_of_tendsto_average_const h0)
  exact eq_zero_or_one_of_sq_eq_self (by simpa only [pow_two] using (sub_eq_zero.mp hc).symm)

/-- The total mass of a weakly mixing measure, read as a real number (`μ.real univ`), is `0` or
`1`. An infinite measure also qualifies, since its real total mass is `0`. -/
theorem IsWeaklyMixing.measureReal_univ_eq_zero_or_one (h : IsWeaklyMixing μ) :
    μ.real univ = 0 ∨ μ.real univ = 1 :=
  h.measureReal_eq_zero_or_one .univ fun t => by rw [preimage_univ]

/-- **Weak mixing implies ergodicity.** A weakly mixing action of `ℝ` preserving a finite measure
is ergodic. -/
theorem IsWeaklyMixing.ergodicVAdd [IsFiniteMeasure μ] [VAddInvariantMeasure ℝ X μ]
    (h : IsWeaklyMixing μ) : ErgodicVAdd ℝ X μ where
  aeconst_of_forall_preimage_vadd_ae_eq {s} hs hinv := by
    rcases h.measureReal_univ_eq_zero_or_one with h1 | h1
    · rw [measureReal_eq_zero_iff, Measure.measure_univ_eq_zero] at h1
      subst h1
      simp
    · have : IsProbabilityMeasure μ := ⟨(ENNReal.toReal_eq_one_iff _).1 h1⟩
      rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ, prob_compl_eq_zero_iff hs]
      rcases h.measureReal_eq_zero_or_one hs hinv with h2 | h2
      · exact Or.inl ((measureReal_eq_zero_iff).1 h2)
      · exact Or.inr ((ENNReal.toReal_eq_one_iff _).1 h2)

/-- The zero measure is weakly mixing. -/
@[simp]
theorem isWeaklyMixing_zero : IsWeaklyMixing (0 : Measure X) := by
  intro A B _ _
  simp

/-- The action of `ℝ` on a space with at most one point is weakly mixing for a measure that is
zero or a probability measure. -/
theorem isWeaklyMixing_of_subsingleton [Subsingleton X] [IsZeroOrProbabilityMeasure μ] :
    IsWeaklyMixing μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | _
  · exact isWeaklyMixing_zero
  intro A B _ _
  have hzero : ∀ t : ℝ, |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B| = 0 :=
    fun t => by
      rcases Subsingleton.set_cases (p := fun s => s = ∅ ∨ s = univ) (.inl rfl) (.inr rfl) A
        with rfl | rfl <;> simp
  simp_rw [hzero, intervalIntegral.integral_zero, mul_zero]
  exact tendsto_const_nhds

end MeasureTheory.Measure

/-- **Weak mixing passes to factors**: the pushforward of a weakly mixing measure along an
equivariant measurable map is weakly mixing, as `ErgodicSMul.map` is for ergodicity. -/
theorem MeasureTheory.Measure.IsWeaklyMixing.map {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [AddAction ℝ X] [AddAction ℝ Y] [MeasurableConstVAdd ℝ Y]
    {μ : Measure X} {f : X → Y} (h : μ.IsWeaklyMixing) (hf : Measurable f)
    (hfg : ∀ (t : ℝ) x, f (t +ᵥ x) = t +ᵥ f x) : (μ.map f).IsWeaklyMixing := by
  intro A B hA hB
  have key : ∀ t : ℝ,
      f ⁻¹' ((fun y => t +ᵥ y) ⁻¹' A ∩ B) = (fun x => t +ᵥ x) ⁻¹' (f ⁻¹' A) ∩ f ⁻¹' B :=
    fun t => by ext x; simp [hfg]
  have hm (t : ℝ) : MeasurableSet ((fun y : Y => t +ᵥ y) ⁻¹' A ∩ B) :=
    (measurable_const_vadd t hA).inter hB
  have := h (f ⁻¹' A) (f ⁻¹' B) (hf hA) (hf hB)
  simpa only [measureReal_def, Measure.map_apply hf (hm _), Measure.map_apply hf hA,
    Measure.map_apply hf hB, key] using this

namespace MeasurableEmbedding

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddAction ℝ X] [AddAction ℝ Y]
  {μ : Measure X} {f : X → Y}

/-- **Weak mixing along an equivariant embedding**: the pushforward of a measure along an
equivariant measurable embedding is weakly mixing exactly when the measure is. This is the
weak-mixing analogue of `MeasurableEmbedding.ergodicSMul_map_iff` in
`TauCeti/Dynamics/Ergodic/Action/Map.lean`. -/
theorem isWeaklyMixing_map_iff (hf : MeasurableEmbedding f)
    (hfg : ∀ (t : ℝ) x, f (t +ᵥ x) = t +ᵥ f x) :
    (μ.map f).IsWeaklyMixing ↔ μ.IsWeaklyMixing := by
  have key : ∀ (t : ℝ) (A B : Set Y),
      f ⁻¹' ((fun y => t +ᵥ y) ⁻¹' A ∩ B) = (fun x => t +ᵥ x) ⁻¹' (f ⁻¹' A) ∩ f ⁻¹' B :=
    fun t A B => by ext x; simp [hfg]
  refine ⟨fun h A B hA hB => ?_, fun h A B hA hB => ?_⟩
  · have := h (f '' A) (f '' B) (hf.measurableSet_image' hA) (hf.measurableSet_image' hB)
    simpa only [measureReal_def, hf.map_apply, key, hf.injective.preimage_image] using this
  · have := h (f ⁻¹' A) (f ⁻¹' B) (hf.measurable hA) (hf.measurable hB)
    simpa only [measureReal_def, hf.map_apply, key] using this

end MeasurableEmbedding

/-- **Weak mixing is invariant under isomorphism**: along an equivariant measure-preserving
measurable embedding, the target measure is weakly mixing exactly when the source measure is. -/
theorem MeasureTheory.MeasurePreserving.isWeaklyMixing_iff {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [AddAction ℝ X] [AddAction ℝ Y] {μ : Measure X} {ν : Measure Y}
    {f : X → Y} (hfμ : MeasurePreserving f μ ν) (hf : MeasurableEmbedding f)
    (hfg : ∀ (t : ℝ) x, f (t +ᵥ x) = t +ᵥ f x) :
    ν.IsWeaklyMixing ↔ μ.IsWeaklyMixing := by
  rw [← hfμ.map_eq]
  exact hf.isWeaklyMixing_map_iff hfg
