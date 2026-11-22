/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Measure
public import TauCeti.MeasureTheory.Function.Lp.Iterated
public import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Expected and pathwise square-energy domains

`TauCeti.BrownianIntegrable` is the predictable, locally-in-time expected-square-energy
integrand domain. `TauCeti.LocallyBrownianIntegrable` instead requires finite square energy
pathwise, on every finite horizon outside one common null set. These are domains for Brownian
stochastic integration, not assertions that a stochastic integral has already been constructed.

For s-finite `P`, the expected-energy domain embeds into the pathwise-energy domain by Tonelli
and a countable cofinal family of horizons, and integrating elapsed square energy over an event
known at `s` reduces to the predictable-measure set integral over `(s,t] × A`
(`TauCeti.BrownianIntegrable.setIntegral_sq_timeMeasure_sub`). Both are closed under addition,
scaling and restriction to predictable sets. The expected-energy domain is also closed under
multiplication by predictable processes that are essentially bounded on each finite horizon.
Product-almost-everywhere replacement by predictable processes preserves the expected-energy
domain, and, for s-finite `P`, the pathwise-energy domain. A finite initial-measurable random
variable, held constant in time, belongs to the pathwise domain without any moment assumption.

Time measure on `(0,T]` is written as the pullback of restricted real Lebesgue measure under
`ℝ≥0 → ℝ`. By the native measurable-embedding restriction identity this is also the restriction
of the pullback Lebesgue measure to `(0,T]`, that is `TauCeti.Probability.timeMeasure T`
(`TauCeti.BrownianIntegrable.memLp_timeMeasure`). Pathwise membership uses native `MemLp`, so
square energy means a finite nonnegative lower integral, never the default value of a divergent
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
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Finite expected square energy on each finite horizon. -/
  memLp : ∀ T : ℝ≥0, MemLp (Function.uncurry H) 2
    (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P)

/-- Predictable Brownian integrands with finite pathwise square energy on every finite
horizon outside one common null set. This does not require finite expected energy. -/
structure LocallyBrownianIntegrable (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (H : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is literally predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every path is square integrable on every finite horizon. -/
  ae_memLp : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, MemLp (fun t ↦ H t ω) 2
    ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))

/-- A single a.e. statement for all finite horizons is equivalent to a separate a.e.
statement for each integer horizon, together with predictability. -/
theorem locallyBrownianIntegrable_iff_nat : LocallyBrownianIntegrable ℱ P H ↔
    IsStronglyPredictable ℱ H ∧ ∀ n : ℕ, ∀ᵐ ω ∂P,
      MemLp (fun t ↦ H t ω) 2
        ((volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) := by
  constructor
  · intro h
    exact ⟨h.isStronglyPredictable, fun n ↦ h.ae_memLp.mono fun ω hω ↦ hω n⟩
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    filter_upwards [ae_all_iff.2 hn] with ω hω
    intro T
    obtain ⟨n, hn⟩ := exists_nat_ge (T : ℝ)
    have hmeasure :
        (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ) ≤
          (volume.restrict (Ioc 0 (n : ℝ))).comap ((↑) : ℝ≥0 → ℝ) := by
      rw [NNReal.comap_volume_restrict_Ioc T,
        ← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc]
      exact Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by exact_mod_cast hn))
    exact (hω n).mono_measure hmeasure

/-- The finite expected square energy of a Brownian-integrable integrand, for Lebesgue time
`TauCeti.Probability.timeMeasure T` on `(0,T]` times `P`. -/
theorem BrownianIntegrable.memLp_timeMeasure (h : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using h.memLp T

/-- A Brownian-integrable process belongs to `L²` of the finite-horizon predictable measure. -/
theorem BrownianIntegrable.memLp_predictableMeasure (h : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P h.isStronglyPredictable T 2).mpr (h.memLp_timeMeasure T)

/-- Finite expected energy on every finite horizon gives finite pathwise energy on all
finite horizons simultaneously. -/
theorem BrownianIntegrable.locallyBrownianIntegrable [SFinite P]
    (h : BrownianIntegrable ℱ P H) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨h.isStronglyPredictable, fun n ↦ ?_⟩
  exact ((h.memLp n).comp_measurePreserving
    (Measure.measurePreserving_swap (μ := P) (ν := _))).ae_memLp_prod_right

/-- For a Brownian-integrable integrand, integrating the elapsed square energy over `(s, t]`
and an `ℱ s`-measurable event `A` equals the predictable-measure set integral over `Ioc s t ×ˢ A`
at any horizon `T ≥ t`. -/
theorem BrownianIntegrable.setIntegral_sq_timeMeasure_sub [SFinite P]
    (hH : BrownianIntegrable ℱ P H) {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, ((∫ r, H r ω ^ 2 ∂Probability.timeMeasure t) -
      ∫ r, H r ω ^ 2 ∂Probability.timeMeasure s) ∂P =
      ∫ p in Ioc s t ×ˢ A, H p.fst p.snd ^ 2 ∂ℱ.predictableMeasure P T := by
  have hsT : s ≤ T := hst.trans htT
  have hdiff : Ioc 0 t \ Ioc 0 s = Ioc s t := by
    ext r
    simp only [Set.mem_sdiff, mem_Ioc, not_and, not_le]
    exact ⟨fun ⟨⟨_, hrt⟩, hnot⟩ ↦ ⟨hnot (by positivity), hrt⟩,
      fun ⟨hsr, hrt⟩ ↦ ⟨⟨zero_le.trans_lt hsr, hrt⟩, fun _ ↦ hsr⟩⟩
  have hsec : ∀ᵐ ω ∂P,
      ((∫ r, H r ω ^ 2 ∂Probability.timeMeasure t) -
        ∫ r, H r ω ^ 2 ∂Probability.timeMeasure s) =
        ∫ r in Ioc s t, H r ω ^ 2 ∂Probability.timeMeasure T := by
    filter_upwards [hH.locallyBrownianIntegrable.ae_memLp] with ω hω
    have hHT : IntegrableOn (fun r ↦ H r ω ^ 2) (Ioc 0 t) (Probability.timeMeasure T) := by
      have h : Integrable (fun r ↦ H r ω ^ 2) (Probability.timeMeasure t) := by
        simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using
          (hω t).integrable_sq
      rwa [← Probability.timeMeasure_restrict_of_le htT] at h
    rw [← Probability.timeMeasure_restrict_of_le htT,
      ← Probability.timeMeasure_restrict_of_le hsT,
      ← setIntegral_sdiff measurableSet_Ioc hHT (Ioc_subset_Ioc_right hst), hdiff]
  have hprod_int : IntegrableOn (fun z : Ω × ℝ≥0 ↦ H z.2 z.1 ^ 2)
      (A ×ˢ Ioc s t) (P.prod (Probability.timeMeasure T)) :=
    ((hH.memLp_timeMeasure T).comp_measurePreserving
      (Measure.measurePreserving_swap (μ := P) (ν := Probability.timeMeasure T))).integrable_sq
      |>.integrableOn
  have hmeas_ind : StronglyMeasurable[ℱ.predictable]
      ((Ioc s t ×ˢ A).indicator (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)) :=
    (hH.isStronglyPredictable.pow 2).indicator (measurableSet_predictable_Ioc_prod s t hA)
  calc
    ∫ ω in A, ((∫ r, H r ω ^ 2 ∂Probability.timeMeasure t) -
        ∫ r, H r ω ^ 2 ∂Probability.timeMeasure s) ∂P
      = ∫ ω in A, ∫ r in Ioc s t, H r ω ^ 2 ∂Probability.timeMeasure T ∂P :=
        setIntegral_congr_ae (ℱ.le s A hA) (hsec.mono fun _ hω _ ↦ hω)
    _ = ∫ z in A ×ˢ Ioc s t, H z.snd z.fst ^ 2 ∂P.prod (Probability.timeMeasure T) :=
        (setIntegral_prod (fun z : Ω × ℝ≥0 ↦ H z.2 z.1 ^ 2) hprod_int).symm
    _ = ∫ p in Ioc s t ×ˢ A, H p.fst p.snd ^ 2 ∂(Probability.timeMeasure T).prod P :=
        setIntegral_prod_swap (Ioc s t) A (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
    _ = ∫ p in Ioc s t ×ˢ A, H p.fst p.snd ^ 2 ∂ℱ.predictableMeasure P T := by
        rw [← integral_indicator (measurableSet_Ioc.prod (ℱ.le s A hA)),
          ← ℱ.integral_predictableMeasure P hmeas_ind T,
          integral_indicator (measurableSet_predictable_Ioc_prod s t hA)]

/-- The expected-energy domain is closed under addition. -/
theorem BrownianIntegrable.add (hH : BrownianIntegrable ℱ P H)
    (hK : BrownianIntegrable ℱ P K) :
    BrownianIntegrable ℱ P (fun t ω ↦ H t ω + K t ω) :=
  ⟨hH.isStronglyPredictable.add hK.isStronglyPredictable,
    fun T ↦ (hH.memLp T).add (hK.memLp T)⟩

/-- The pathwise-energy domain is closed under addition. -/
theorem LocallyBrownianIntegrable.add (hH : LocallyBrownianIntegrable ℱ P H)
    (hK : LocallyBrownianIntegrable ℱ P K) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω + K t ω) := by
  refine ⟨hH.isStronglyPredictable.add hK.isStronglyPredictable, ?_⟩
  filter_upwards [hH.ae_memLp, hK.ae_memLp] with ω hω kω
  exact fun T ↦ (hω T).add (kω T)

/-- Scaling preserves finite expected square energy. -/
theorem BrownianIntegrable.const_mul (h : BrownianIntegrable ℱ P H) (c : ℝ) :
    BrownianIntegrable ℱ P (fun t ω ↦ c * H t ω) :=
  ⟨h.isStronglyPredictable.const_mul c, fun T ↦ (h.memLp T).const_mul c⟩

/-- Multiplication by a predictable process that is essentially bounded on every finite
horizon preserves finite expected square energy. -/
theorem BrownianIntegrable.mul (hH : BrownianIntegrable ℱ P H)
    (hK : IsStronglyPredictable ℱ K)
    (hb : ∀ T : ℝ≥0, MemLp (Function.uncurry K) ∞
      (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P)) :
    BrownianIntegrable ℱ P (fun t ω ↦ H t ω * K t ω) :=
  ⟨hH.isStronglyPredictable.mul hK, fun T ↦ (hH.memLp T).mul (hb T)⟩

/-- Multiplication by a uniformly bounded predictable process preserves finite expected
square energy. -/
theorem BrownianIntegrable.mul_of_bound (hH : BrownianIntegrable ℱ P H)
    (hK : IsStronglyPredictable ℱ K) (C : ℝ) (hb : ∀ t ω, ‖K t ω‖ ≤ C) :
    BrownianIntegrable ℱ P (fun t ω ↦ H t ω * K t ω) :=
  hH.mul hK fun _ ↦ memLp_top_of_bound
    (hK.mono ℱ.predictable_le_prod).aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ hb z.1 z.2)

/-- Scaling preserves finite pathwise square energy. -/
theorem LocallyBrownianIntegrable.const_mul (h : LocallyBrownianIntegrable ℱ P H) (c : ℝ) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ c * H t ω) :=
  ⟨h.isStronglyPredictable.const_mul c,
    h.ae_memLp.mono fun _ hω T ↦ (hω T).const_mul c⟩

/-- Restriction to a predictable set preserves finite expected square energy. -/
theorem BrownianIntegrable.indicator (hH : BrownianIntegrable ℱ P H)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A) :
    BrownianIntegrable ℱ P (fun t ω ↦ A.indicator (Function.uncurry H) (t, ω)) := by
  refine ⟨hH.isStronglyPredictable.indicator hA, fun T ↦ ?_⟩
  exact (hH.memLp T).indicator (ℱ.predictable_le_prod A hA).nullMeasurableSet

/-- Restriction to a predictable set preserves finite pathwise square energy. -/
theorem LocallyBrownianIntegrable.indicator (hH : LocallyBrownianIntegrable ℱ P H)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ A.indicator (Function.uncurry H) (t, ω)) := by
  refine ⟨hH.isStronglyPredictable.indicator hA, ?_⟩
  filter_upwards [hH.ae_memLp] with ω hω
  intro T
  exact (hω T).indicator ((ℱ.predictable_le_prod A hA).preimage
    (measurable_id.prodMk measurable_const)).nullMeasurableSet

/-- Product-a.e. replacement preserves the expected-energy domain, provided the new
representative is predictable. -/
theorem BrownianIntegrable.congr (h : BrownianIntegrable ℱ P H)
    (hK : IsStronglyPredictable ℱ K)
    (heq : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[
      ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P]
        Function.uncurry K) : BrownianIntegrable ℱ P K :=
  ⟨hK, fun T ↦ (h.memLp T).ae_eq (heq T)⟩

/-- A.e.-in-time replacement on almost every path preserves the pathwise-energy domain,
provided the new representative is predictable. No s-finiteness assumption is needed. -/
theorem LocallyBrownianIntegrable.congr (h : LocallyBrownianIntegrable ℱ P H)
    (hK : IsStronglyPredictable ℱ K)
    (heq : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (fun t ↦ H t ω) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)] (fun t ↦ K t ω)) :
    LocallyBrownianIntegrable ℱ P K := by
  refine ⟨hK, ?_⟩
  filter_upwards [h.ae_memLp, heq] with ω hω heqω
  exact fun T ↦ (hω T).ae_eq (heqω T)

/-- For s-finite `P`, product-a.e. replacement preserves the pathwise-energy domain,
provided the new representative is predictable. -/
theorem LocallyBrownianIntegrable.congr_prod [SFinite P] (h : LocallyBrownianIntegrable ℱ P H)
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
    exact h.isStronglyPredictable.stronglyAdapted 0
  · intro hξ
    refine ⟨?_, Eventually.of_forall fun ω T ↦ memLp_const (ξ ω)⟩
    have ha : StronglyAdapted ℱ (fun _ ω ↦ ξ ω) :=
      fun t ↦ hξ.mono (ℱ.mono (bot_le : 0 ≤ t))
    exact ha.isStronglyPredictable_of_continuous (fun _ ↦ continuous_const)

/-- A time-constant random variable belongs to the expected-energy domain exactly when it
is initial-measurable and square integrable. Compared with `locallyBrownianIntegrable_const_iff`,
this adds the moment condition `MemLp ξ 2 P`.

Not a `simp` lemma: on the right-hand side, `simp` tries `MeasureTheory.MemLp.of_discrete`, whose
`DiscreteMeasurableSpace Ω` instance search times out for a general `Ω`. -/
theorem brownianIntegrable_const_iff [SFinite P] {ξ : Ω → ℝ} :
    BrownianIntegrable ℱ P (fun _ ω ↦ ξ ω) ↔
      StronglyMeasurable[ℱ 0] ξ ∧ MemLp ξ 2 P := by
  constructor
  · intro h
    refine ⟨h.isStronglyPredictable.stronglyAdapted 0, ?_⟩
    -- A unit time interval has positive mass, so an a.e. square-integrable section exists.
    have hmass : (volume.restrict (Ioc 0 (1 : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ) univ = 1 := by
      simpa using NNReal.comap_volume_restrict_Ioc_univ 1
    have : NeZero ((volume.restrict (Ioc 0 (1 : ℝ))).comap ((↑) : ℝ≥0 → ℝ)) :=
      ⟨fun hz ↦ by simp [hz] at hmass⟩
    have hsec : ∀ᵐ _ ∂(volume.restrict (Ioc 0 (1 : ℝ))).comap
        ((↑) : ℝ≥0 → ℝ), MemLp ξ 2 P := by
      simpa only [NNReal.coe_one, Function.uncurry_apply_pair] using
        (h.memLp 1).ae_memLp_prod_right
    obtain ⟨_, hξ⟩ := hsec.exists
    exact hξ
  · rintro ⟨hξ, hξ₂⟩
    exact ⟨((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable,
      fun _ ↦ hξ₂.comp_snd _⟩

/-- An indicator on `(s, u]` with an `ℱ s`-measurable, square-integrable height belongs to
the expected-energy domain. -/
theorem brownianIntegrable_indicator_Ioc [SFinite P] {s u : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    BrownianIntegrable ℱ P (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t) where
  isStronglyPredictable := ℱ.stronglyMeasurable_indicator_Ioc_predictable s u hξ
  memLp T := by
    rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
    exact (ℱ.memLp_predictableMeasure_iff P
      (ℱ.stronglyMeasurable_indicator_Ioc_predictable s u hξ) T 2).mp
      (ℱ.memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂)

/-- A deterministic measurable function that is square integrable on every finite horizon belongs
to the expected-energy domain. -/
theorem brownianIntegrable_fst [IsFiniteMeasure P] {h : ℝ≥0 → ℝ}
    (hm : Measurable h) (hLp : ∀ T : ℝ≥0, MemLp h 2 (Probability.timeMeasure T)) :
    BrownianIntegrable ℱ P (fun t _ ↦ h t) where
  isStronglyPredictable := hm.stronglyMeasurable.comp_measurable ℱ.measurable_fst_predictable
  memLp T := by
    rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
    exact (hLp T).comp_fst P

end TauCeti
