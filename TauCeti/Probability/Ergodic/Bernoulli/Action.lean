/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.InfinitePi
public import TauCeti.Probability.Process.Tail.ProperAction
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.SymbolicDynamics.Basic
import TauCeti.Probability.ProductMeasure

/-!
# Ergodicity of Bernoulli product measures under group actions

Let a group `Γ` act on a countable set `ι` and on configurations `ω : ι → S` by
`(g • ω) i = ω (g⁻¹ • i)` (Mathlib's `arrowAction`). The Bernoulli product measure `ν^{⊗ι}` of a
probability measure `ν` on `S` is invariant under this action, since each `g` permutes the
coordinates. If every finite set of indices can be moved off every finite set, for instance if
`Γ` is infinite and acts properly, then every almost invariant event is almost surely a tail event
(`TauCeti.Probability.exists_measurableSet_tailEvents_ae_eq`), so by Kolmogorov's zero-one law it
is null or conull: the action is ergodic.

## Main results

* `TauCeti.Probability.measurePreserving_infinitePi_comp_inv_smul`: `ν^{⊗ι}` is invariant.
* `TauCeti.Probability.eventuallyEmptyOrUniv_infinitePi_const`: an almost invariant event is null
  or conull for a Bernoulli product measure.
* `TauCeti.Probability.ergodicSMul_arrowAction_infinitePi_const`: the same statement as
  `ErgodicSMul` for the action `arrowAction`, and
  `TauCeti.Probability.ergodicSMul_arrowAction_infinitePi_const_of_proper` for a proper action of
  an infinite group.
* `TauCeti.Probability.ergodicSMul_arrowAction_self_infinitePi_const`: the Bernoulli action
  `(g • x) h = x (g⁻¹ * h)` of a countable infinite group `Γ` on `Γ → S` is ergodic. This action is
  the shift by `g⁻¹` (`TauCeti.Probability.arrowAction_smul_eq_mulShift`).
* `TauCeti.Probability.ergodicSMul_arrowAction_multiplicative_infinitePi_const`: for a countable
  infinite additive group `Λ`, the Bernoulli action of `Multiplicative Λ` on `Λ → S` is ergodic.
  This action is the shift by `-toAdd g`
  (`TauCeti.Probability.arrowAction_multiplicative_smul_eq_shift`).

For the finitely supported permutations of `ℕ` acting on `ℕ → α`, Hewitt–Savage gives the same
conclusion: `TauCeti.Probability.ergodicSMul_infinitePi_const`.

## References

* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Section 3.2, Lemma 3.2.1.
* H.-O. Georgii, *Gibbs measures and phase transitions* (2nd ed., 2011), Chapter 14.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {ι Γ S : Type*} [Group Γ] [MulAction Γ ι] [MeasurableSpace S] {ν : Measure S}
  [IsProbabilityMeasure ν]

/-- **Bernoulli product measures are invariant**: for a probability measure `ν`, each `g : Γ`
permutes the coordinates, so `ω ↦ (i ↦ ω (g⁻¹ • i))` preserves `ν^{⊗ι}`. -/
theorem measurePreserving_infinitePi_comp_inv_smul (g : Γ) :
    MeasurePreserving (fun (ω : ι → S) i => ω (g⁻¹ • i)) (Measure.infinitePi fun _ => ν)
      (Measure.infinitePi fun _ => ν) :=
  measurePreserving_infinitePi_comp_of_injective (fun _ => ν) (MulAction.injective g⁻¹)

/-- **Bernoulli product measures are ergodic**, stated with almost invariant events. Let a group
`Γ` act on a countable set `ι` so that every finite set can be moved off every finite set, and on
configurations by `(g • ω) i = ω (g⁻¹ • i)`. For a probability measure `ν`, every null-measurable
event that is almost invariant under this action is null or conull for the product measure
`ν^{⊗ι}`. -/
theorem eventuallyEmptyOrUniv_infinitePi_const [Countable ι]
    (hmove : ∀ F Λ : Finset ι, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ) {A : Set (ι → S)}
    (hA : NullMeasurableSet A (Measure.infinitePi fun _ => ν))
    (hAg : ∀ g : Γ, (fun (ω : ι → S) i => ω (g⁻¹ • i)) ⁻¹' A =ᵐ[Measure.infinitePi fun _ => ν] A) :
    EventuallyEmptyOrUniv A (ae (Measure.infinitePi fun _ => ν)) := by
  obtain ⟨T, hT, hTA⟩ := exists_measurableSet_tailEvents_ae_eq hmove
    measurePreserving_infinitePi_comp_inv_smul hA hAg
  refine (eventuallyEmptyOrUniv_iff.2 ?_).congr hTA
  rcases infinitePi_eq_zero_or_one_of_measurableSet_tailEvents (P := fun _ => ν) hT with h | h
  · exact Or.inr (ae_iff.2 (by simpa using h))
  · exact Or.inl ((mem_ae_iff_prob_eq_one (tailEvents_le_pi _ hT)).2 h)

/-- **Bernoulli product measures are ergodic.** Let a group `Γ` act on a countable set `ι` so that
every finite set can be moved off every finite set. For a probability measure `ν` on `S`, the
action `(g • ω) i = ω (g⁻¹ • i)` of `Γ` on `ι → S` (Mathlib's `arrowAction`) is ergodic for the
product measure `ν^{⊗ι}`. -/
theorem ergodicSMul_arrowAction_infinitePi_const [Countable ι]
    (hmove : ∀ F Λ : Finset ι, ∃ g : Γ, ∀ i ∈ F, g • i ∉ Λ) :
    letI := arrowAction (G := Γ) (A := ι) (B := S)
    ErgodicSMul Γ (ι → S) (Measure.infinitePi fun _ => ν) := by
  let := arrowAction (G := Γ) (A := ι) (B := S)
  -- Under `arrowAction`, `(g • ·)` is `fun ω i => ω (g⁻¹ • i)` by the defining equation of the
  -- action; Mathlib's simps lemma `arrowAction_smul` is stated with a bare `SMul.smul`.
  have hsmul (g : Γ) : (g • · : (ι → S) → ι → S) = fun ω i => ω (g⁻¹ • i) := rfl
  exact
    { measure_preimage_smul g s hs := by
        rw [hsmul]
        exact (measurePreserving_infinitePi_comp_inv_smul g).measure_preimage hs.nullMeasurableSet
      aeconst_of_forall_preimage_smul_ae_eq hs hsg :=
        eventuallyEmptyOrUniv_infinitePi_const hmove hs.nullMeasurableSet fun g => by
          simpa only [hsmul] using hsg g }

/-- **Bernoulli product measures are ergodic under proper actions.** If an infinite group `Γ` acts
properly on a countable set `ι` (for finite `F, F' ⊆ ι`, only finitely many `g` move a point of
`F` into `F'`), then the action `arrowAction` is ergodic for `ν^{⊗ι}`. -/
theorem ergodicSMul_arrowAction_infinitePi_const_of_proper [Countable ι] [Infinite Γ]
    (hproper : ∀ F F' : Finset ι, {g : Γ | ∃ i ∈ F, g • i ∈ F'}.Finite) :
    letI := arrowAction (G := Γ) (A := ι) (B := S)
    ErgodicSMul Γ (ι → S) (Measure.infinitePi fun _ => ν) :=
  ergodicSMul_arrowAction_infinitePi_const (exists_forall_smul_notMem_of_proper hproper)

omit [MeasurableSpace S] in
/-- The Bernoulli action `(g • x) h = x (g⁻¹ * h)` of a group on `Γ → S` (Mathlib's
`arrowAction`) is the shift by `g⁻¹`. -/
theorem arrowAction_smul_eq_mulShift (g : Γ) (x : Γ → S) :
    letI := arrowAction (G := Γ) (A := Γ) (B := S)
    g • x = SymbolicDynamics.FullShift.mulShift g⁻¹ x :=
  (rfl)

/-- **The Bernoulli action of a countable infinite group is ergodic.** For a probability measure
`ν` on `S`, the action `(g • x) h = x (g⁻¹ * h)` of a countable infinite group `Γ` on `Γ → S` is
ergodic for the Bernoulli measure `ν^{⊗Γ}`. -/
theorem ergodicSMul_arrowAction_self_infinitePi_const [Countable Γ] [Infinite Γ] :
    letI := arrowAction (G := Γ) (A := Γ) (B := S)
    ErgodicSMul Γ (Γ → S) (Measure.infinitePi fun _ => ν) := by
  refine ergodicSMul_arrowAction_infinitePi_const_of_proper fun F F' ↦ ?_
  refine ((F'.finite_toSet.image2 (fun j i ↦ j * i⁻¹) F.finite_toSet)).subset ?_
  rintro g ⟨i, hi, hg⟩
  exact ⟨g • i, hg, i, hi, by simp⟩

/-- **The Bernoulli action of a countable infinite additive group is ergodic.** For an additive
group `Λ` acting on itself by translation, and a probability measure `ν` on `S`, the action
`(g • x) n = x (-toAdd g + n)` of `Multiplicative Λ` on `Λ → S` is ergodic for `ν^{⊗Λ}`, when `Λ`
is countable and infinite. -/
theorem ergodicSMul_arrowAction_multiplicative_infinitePi_const {Λ : Type*} [AddGroup Λ]
    [Countable Λ] [Infinite Λ] :
    letI := arrowAction (G := Multiplicative Λ) (A := Λ) (B := S)
    ErgodicSMul (Multiplicative Λ) (Λ → S) (Measure.infinitePi fun _ => ν) := by
  have : Infinite (Multiplicative Λ) := inferInstanceAs (Infinite Λ)
  refine ergodicSMul_arrowAction_infinitePi_const_of_proper fun F F' ↦ ?_
  refine ((F'.finite_toSet.image2 (fun j i ↦ Multiplicative.ofAdd (j - i)) F.finite_toSet)).subset
    ?_
  rintro g ⟨i, hi, hg⟩
  obtain ⟨k, rfl⟩ := Multiplicative.ofAdd.surjective g
  rw [ofAdd_smul, vadd_eq_add] at hg
  exact ⟨k + i, hg, i, hi, congrArg Multiplicative.ofAdd (add_sub_cancel_right k i)⟩

omit [MeasurableSpace S] in
/-- The Bernoulli action of `Multiplicative Λ` on `Λ → S` (Mathlib's `arrowAction`, with `Λ` acting
on itself by translation) is the shift by `-toAdd g`: `(g • x) n = x (-toAdd g + n)`. -/
theorem arrowAction_multiplicative_smul_eq_shift {Λ : Type*} [AddGroup Λ] (g : Multiplicative Λ)
    (x : Λ → S) :
    letI := arrowAction (G := Multiplicative Λ) (A := Λ) (B := S)
    g • x = SymbolicDynamics.FullShift.shift (-Multiplicative.toAdd g) x :=
  (rfl)

end Probability

end TauCeti
