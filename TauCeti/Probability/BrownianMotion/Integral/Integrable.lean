/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable
public import TauCeti.MeasureTheory.Function.Lp.Iterated
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Expected and pathwise square-energy domains

`TauCeti.BrownianIntegrable` is the predictable, locally-in-time expected-square-energy
integrand domain. `TauCeti.LocallyBrownianIntegrable` instead requires finite square energy
pathwise, on every finite horizon outside one common null set. These are domains for Brownian
stochastic integration, not assertions that a stochastic integral has already been constructed.

The expected-energy domain embeds into the pathwise-energy domain by Tonelli and a countable
cofinal family of horizons. Both are closed under addition, scaling and product-almost-everywhere
replacement by predictable processes. A finite initial-measurable random variable, held constant
in time, belongs to the pathwise domain without any moment assumption.

Time measure on `(0,T]` is written as the pullback of restricted real Lebesgue measure under
`ℝ≥0 → ℝ`. By the native measurable-embedding restriction identity this is also the restriction
of the pullback Lebesgue measure to `(0,T]`. Pathwise membership uses native `MemLp`, so square
energy means a finite nonnegative lower integral, never the default value of a divergent
Bochner integral.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H K : ℝ≥0 → Ω → ℝ}

/-- Predictable Brownian integrands with finite expected square energy on every finite
horizon. No Brownian motion or usual-filtration assumption is needed to define the domain. -/
structure BrownianIntegrable (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (H : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is literally predictable for the declared filtration. -/
  stronglyPredictable : IsStronglyPredictable ℱ H
  /-- Finite expected square energy on each finite horizon. -/
  memLp : ∀ T : ℝ≥0, MemLp (Function.uncurry H) 2
    (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P)

/-- Predictable Brownian integrands with finite pathwise square energy on every finite
horizon outside one common null set. This does not require finite expected energy. -/
structure LocallyBrownianIntegrable (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (H : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is literally predictable for the declared filtration. -/
  stronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every path is square integrable on every finite horizon. -/
  ae_memLp : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, MemLp (fun t ↦ H t ω) 2
    ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))

/-- To test the pathwise domain, it suffices to test each integer horizon separately.
The exceptional sets are combined before passing to arbitrary horizons. -/
theorem locallyBrownianIntegrable_iff_nat : LocallyBrownianIntegrable ℱ P H ↔
    IsStronglyPredictable ℱ H ∧ ∀ n : ℕ, ∀ᵐ ω ∂P,
      MemLp (fun t ↦ H t ω) 2
        ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) := by
  constructor
  · intro h
    exact ⟨h.stronglyPredictable, fun n ↦ h.ae_memLp.mono fun ω hω ↦ hω n⟩
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    filter_upwards [ae_all_iff.2 hn] with ω hω
    intro T
    obtain ⟨n, hn⟩ := exists_nat_ge (T : ℝ)
    have he := NNReal.isClosedEmbedding_coe.measurableEmbedding
    have hpre (a : ℝ≥0) : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc 0 (a : ℝ) = Ioc 0 a := by
      ext t
      simp
    have hmeasure :
        (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ) ≤
          (volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ) := by
      rw [he.comap_restrict, he.comap_restrict, hpre T]
      have hnpre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc 0 (n : ℝ) = Ioc 0 (n : ℝ≥0) := by
        simpa only [NNReal.coe_natCast] using hpre (n : ℝ≥0)
      rw [hnpre]
      exact Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by exact_mod_cast hn))
    exact (hω n).mono_measure hmeasure

/-- Finite expected energy on every finite horizon gives finite pathwise energy on all
finite horizons simultaneously. -/
theorem BrownianIntegrable.locallyBrownianIntegrable [SFinite P]
    (h : BrownianIntegrable ℱ P H) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨h.stronglyPredictable, fun n ↦ ?_⟩
  exact ((h.memLp n).comp_measurePreserving
    (Measure.measurePreserving_swap (μ := P) (ν := _))).ae_memLp_prod_right

/-- The expected-energy domain is closed under addition. -/
theorem BrownianIntegrable.add (hH : BrownianIntegrable ℱ P H)
    (hK : BrownianIntegrable ℱ P K) :
    BrownianIntegrable ℱ P (fun t ω ↦ H t ω + K t ω) :=
  ⟨StronglyMeasurable.add hH.stronglyPredictable hK.stronglyPredictable,
    fun T ↦ (hH.memLp T).add (hK.memLp T)⟩

/-- The pathwise-energy domain is closed under addition. -/
theorem LocallyBrownianIntegrable.add (hH : LocallyBrownianIntegrable ℱ P H)
    (hK : LocallyBrownianIntegrable ℱ P K) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω + K t ω) := by
  refine ⟨StronglyMeasurable.add hH.stronglyPredictable hK.stronglyPredictable, ?_⟩
  filter_upwards [hH.ae_memLp, hK.ae_memLp] with ω hω kω
  exact fun T ↦ (hω T).add (kω T)

/-- Scaling preserves finite expected square energy. -/
theorem BrownianIntegrable.const_mul (h : BrownianIntegrable ℱ P H) (c : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ c * H t ω) :=
  ⟨StronglyMeasurable.const_mul h.stronglyPredictable c, fun T ↦ (h.memLp T).const_mul c⟩

/-- Scaling preserves finite pathwise square energy. -/
theorem LocallyBrownianIntegrable.const_mul (h : LocallyBrownianIntegrable ℱ P H) (c : ℝ) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ c * H t ω) :=
  ⟨StronglyMeasurable.const_mul h.stronglyPredictable c,
    h.ae_memLp.mono fun _ hω T ↦ (hω T).const_mul c⟩

/-- Product-a.e. replacement preserves the expected-energy domain, provided the new
representative is predictable. -/
theorem BrownianIntegrable.congr (h : BrownianIntegrable ℱ P H)
    (hK : IsStronglyPredictable ℱ K)
    (heq : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[
      ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P]
        Function.uncurry K) : BrownianIntegrable ℱ P K :=
  ⟨hK, fun T ↦ (h.memLp T).ae_eq (heq T)⟩

/-- Product-a.e. replacement preserves the pathwise-energy domain, provided the new
representative is predictable. Equality at each fixed time is not used as a substitute for
product-a.e. equality. -/
theorem LocallyBrownianIntegrable.congr [SFinite P] (h : LocallyBrownianIntegrable ℱ P H)
    (hK : IsStronglyPredictable ℱ K)
    (heq : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[
      ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P]
        Function.uncurry K) : LocallyBrownianIntegrable ℱ P K := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hK, fun n ↦ ?_⟩
  have heq' := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := P) (ν := _)).quasiMeasurePreserving.ae_eq_comp
      (heq n))
  filter_upwards [h.ae_memLp, heq'] with ω hω heqω
  exact (hω n).ae_eq heqω

/-- A time-constant finite random variable belongs to the pathwise domain exactly when it
is initial-measurable. No moment assumption is required. -/
@[simp]
theorem locallyBrownianIntegrable_const_iff {ξ : Ω → ℝ} :
    LocallyBrownianIntegrable ℱ P (fun _ ω ↦ ξ ω) ↔ StronglyMeasurable[ℱ 0] ξ := by
  constructor
  · intro h
    exact h.stronglyPredictable.stronglyAdapted 0
  · intro hξ
    refine ⟨?_, Eventually.of_forall fun ω T ↦ memLp_const (ξ ω)⟩
    have ha : StronglyAdapted ℱ (fun _ ω ↦ ξ ω) :=
      fun t ↦ hξ.mono (ℱ.mono (bot_le : 0 ≤ t))
    exact ha.isStronglyPredictable_of_continuous (fun _ ↦ continuous_const)

/-- A time-constant random variable belongs to the expected-energy domain exactly when it
is initial-measurable and square integrable. Thus the moment requirement is genuinely stronger
than membership in the pathwise domain. -/
@[simp]
theorem brownianIntegrable_const_iff [SFinite P] {ξ : Ω → ℝ} :
    BrownianIntegrable ℱ P (fun _ ω ↦ ξ ω) ↔
      StronglyMeasurable[ℱ 0] ξ ∧ MemLp ξ 2 P := by
  constructor
  · intro h
    refine ⟨h.stronglyPredictable.stronglyAdapted 0, ?_⟩
    -- A unit time interval has positive mass, so an a.e. square-integrable section exists.
    have hmass : (volume.restrict (Ioc 0 (1 : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ) univ = 1 := by
      rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply]
      have hr : ((↑) : ℝ≥0 → ℝ) '' (univ : Set ℝ≥0) = Ici 0 := by
        ext x
        simp
      rw [hr, Measure.restrict_apply measurableSet_Ici]
      have hsub : Ioc (0 : ℝ) 1 ⊆ Ici 0 := fun _ hx ↦ hx.1.le
      rw [inter_eq_right.mpr hsub]
      simp
    have : NeZero ((volume.restrict (Ioc 0 (1 : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) :=
      ⟨fun hz ↦ by simp [hz] at hmass⟩
    have hsec : ∀ᵐ _ ∂(volume.restrict (Ioc 0 (1 : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ), MemLp ξ 2 P := by
      simpa only [NNReal.coe_one, Function.uncurry_apply_pair] using
        (h.memLp 1).ae_memLp_prod_right
    obtain ⟨_, hξ⟩ := hsec.exists
    exact hξ
  · rintro ⟨hξ, hξ₂⟩
    exact ⟨((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).stronglyPredictable,
      fun _ ↦ hξ₂.comp_snd _⟩

end TauCeti
