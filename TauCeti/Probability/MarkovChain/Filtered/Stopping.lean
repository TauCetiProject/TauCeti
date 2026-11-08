/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Probability.MarkovChain.Filtered.Basic
public import TauCeti.Probability.Process.StoppedValue

/-!
# Conditional transitions after a stopping time

For a chain satisfying `IsMarkovChain ℱ X κ μ`, the conditional distribution of
`X (τ + k)` given the stopped sigma-algebra is `(κ ^ k) (X τ)`. The assertion is
restricted to the event where `τ` is finite. In particular, the arbitrary default
in Mathlib's `stoppedValue` at infinity does not contribute to either side.

These are bounded-test and event forms of the strong Markov transition law on an
arbitrary sample space, relative to the filtration appearing in the Markov hypothesis.
They do not assert that equality of natural-history path laws suffices for a larger
filtration, and impose no topology or countability assumption on the state space.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Theorem 1.4.2.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set

namespace TauCeti.Probability.IsMarkovChain

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S]
  {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}
  [IsFiniteMeasure μ] [IsMarkovKernel κ] {τ : Ω → WithTop ℕ}

private lemma integrable_comp_stoppedValue_add (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) (k : ℕ) {f : S → ℝ} (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun ω => f (stoppedValue (fun n => X (n + k)) τ ω)) μ := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨(hf.comp (measurable_stoppedValue_of_countable
    (fun n => h.adapted.measurable) hτ.measurable')).aestronglyMeasurable,
    .of_bounded (Eventually.of_forall fun ω => hC _)⟩

/-- The conditional transition law at a possibly infinite stopping time, tested against a
bounded measurable real function. Both sides vanish on the event of nontermination. -/
theorem condExp_stoppedValue_add (h : IsMarkovChain ℱ X κ μ) (hτ : IsStoppingTime ℱ τ)
    (k : ℕ) {f : S → ℝ} (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω => f (stoppedValue (fun n => X (n + k)) τ ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => ∫ y, f y ∂(κ ^ k) (stoppedValue X τ ω)) := by
  obtain ⟨C, hC⟩ := hb
  let A := {ω | τ ω ≠ ⊤}
  let Z := fun ω => f (stoppedValue (fun n => X (n + k)) τ ω)
  have hAτ : MeasurableSet[hτ.measurableSpace] A :=
    ((measurableSet_singleton ⊤).preimage hτ.measurable).compl
  have hA : MeasurableSet A := hτ.measurableSpace_le _ hAτ
  have hi : Integrable Z μ := h.integrable_comp_stoppedValue_add hτ k hf ⟨C, hC⟩
  have hiA := hi.indicator hA
  -- Localize the stopped conditional expectation on each finite stopping-time slice.
  have hslice (n : ℕ) :
      μ[A.indicator Z | hτ.measurableSpace] =ᵐ[μ.restrict {ω | τ ω = n}]
        A.indicator (fun ω => ∫ y, f y ∂(κ ^ k) (stoppedValue X τ ω)) := by
    have hs := hτ.measurableSet_eq n
    have hsΩ := ℱ.le n _ hs
    have hin : Integrable (fun ω => f (X (n + k) ω)) μ := by
      simpa only [stoppedValue_const] using
        h.integrable_comp_stoppedValue_add (isStoppingTime_const ℱ n) k hf ⟨C, hC⟩
    have heq : A.indicator Z =ᵐ[μ.restrict {ω | τ ω = n}]
        fun ω => f (X (n + k) ω) := by
      filter_upwards [ae_restrict_mem hsΩ] with ω hω
      simp [A, Z, stoppedValue_of_eq hω, hω]
    have hc := (condExp_restrict_ae_eq_restrict (ℱ.le n) hs hiA).symm.trans
      ((condExp_congr_ae heq).trans
        (condExp_restrict_ae_eq_restrict (ℱ.le n) hs hin))
    filter_upwards [condExp_stopping_time_ae_eq_restrict_eq (f := A.indicator Z) hτ n, hc,
      (h.condExp_add n k hf ⟨C, hC⟩).filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem hsΩ] with ω hstop hcong hstep hω
    simpa [A, stoppedValue_of_eq hω, hω] using
      hstop.trans (hcong.trans hstep)
  -- On the infinite slice the tested random variable vanishes, so does its conditional mean.
  have htop : μ[A.indicator Z | hτ.measurableSpace] =ᵐ[μ.restrict Aᶜ] 0 :=
    condExp_ae_eq_restrict_zero hAτ.compl
      (indicator_ae_eq_restrict_compl hA.nullMeasurableSet)
  have hslices (n : ℕ) := (ae_restrict_iff' (ℱ.le n _ (hτ.measurableSet_eq n))).1
    (hslice n)
  filter_upwards [ae_all_iff.2 hslices, (ae_restrict_iff' hA.compl).1 htop] with ω hω htopω
  by_cases hfin : τ ω = ⊤
  · simpa [A, hfin] using htopω (by simpa [A] using hfin)
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    exact hω n hn.symm

/-- At an almost-surely finite stopping time the conditional transition law needs no
indicator. No bound on the stopping time or its expectation is required. -/
theorem condExp_stoppedValue_add_of_ae_ne_top (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (k : ℕ) {f : S → ℝ} (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    μ[fun ω => f (stoppedValue (fun n => X (n + k)) τ ω) | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∫ y, f y ∂(κ ^ k) (stoppedValue X τ ω) := by
  have hind (g : Ω → ℝ) : {ω | τ ω ≠ ⊤}.indicator g =ᵐ[μ] g := by
    filter_upwards [hfin] with ω hω using indicator_of_mem hω g
  exact (condExp_congr_ae (hind _)).symm.trans
    ((h.condExp_stoppedValue_add hτ k hf hb).trans (hind _))

/-- The event form of the stopped conditional transition law. The finite-time event remains
inside the conditional expectation even when the stopping time can be infinite. -/
theorem condExp_indicator_stoppedValue_add (h : IsMarkovChain ℱ X κ μ)
    (hτ : IsStoppingTime ℱ τ) (k : ℕ) {B : Set S} (hB : MeasurableSet B) :
    μ[({ω | τ ω ≠ ⊤} ∩ stoppedValue (fun n => X (n + k)) τ ⁻¹' B).indicator
        (fun _ => (1 : ℝ)) | hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator
        (fun ω => ((κ ^ k) (stoppedValue X τ ω)).real B) := by
  have hb : ∃ C : ℝ, ∀ x : S, ‖B.indicator (fun _ => (1 : ℝ)) x‖ ≤ C :=
    ⟨1, fun x => by by_cases hx : x ∈ B <;> simp [hx]⟩
  simpa only [← Set.indicator_comp_right, Function.comp_def, Set.indicator_indicator,
    integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one] using
    h.condExp_stoppedValue_add hτ k (measurable_const.indicator hB) hb

/-- Integrate the stopped transition law over any event known at the stopping time. This
identity keeps the full stopped history, rather than conditioning only on the stopped state. -/
theorem setIntegral_stoppedValue_add (h : IsMarkovChain ℱ X κ μ) (hτ : IsStoppingTime ℱ τ)
    (k : ℕ) {f : S → ℝ} (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, f (stoppedValue (fun n => X (n + k)) τ ω) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, ∫ y, f y ∂(κ ^ k) (stoppedValue X τ ω) ∂μ := by
  have hfin : MeasurableSet {ω | τ ω ≠ ⊤} := hτ.measurableSet_eq_top.compl
  have hi := h.integrable_comp_stoppedValue_add hτ k hf hb
  rw [← setIntegral_indicator hfin, ← setIntegral_indicator hfin]
  exact (setIntegral_condExp hτ.measurableSpace_le (hi.indicator hfin) hA).symm.trans
    (integral_congr_ae ((h.condExp_stoppedValue_add hτ k hf hb).filter_mono
      (ae_mono Measure.restrict_le_self)))

end TauCeti.Probability.IsMarkovChain
