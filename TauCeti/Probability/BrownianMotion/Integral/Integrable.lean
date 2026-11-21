/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Measure
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.MeasureTheory.Function.Lp.Iterated
public import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import TauCeti.Probability.Finance.SimpleStrategy.Energy

/-!
# Expected and pathwise square-energy domains

`TauCeti.BrownianIntegrable` is the predictable, locally-in-time expected-square-energy
integrand domain. `TauCeti.LocallyBrownianIntegrable` instead requires finite square energy
pathwise, on every finite horizon outside one common null set. These are domains for Brownian
stochastic integration, not assertions that a stochastic integral has already been constructed.

For s-finite `P`, the expected-energy domain embeds into the pathwise-energy domain by Tonelli
and a countable cofinal family of horizons. Both are closed under addition, scaling and
restriction to predictable sets, and finite-grid elementary holdings with square-integrable
left-measurable heights belong to the expected-energy domain
(`TauCeti.BrownianIntegrable.simpleHolding`).
The expected-energy domain is also closed under multiplication by predictable processes that are
essentially bounded on each finite horizon.
Product-almost-everywhere replacement by predictable processes preserves the expected-energy
domain, and, for s-finite `P`, the pathwise-energy domain. A finite initial-measurable random
variable, held constant in time, belongs to the pathwise domain without any moment assumption.

Each `BrownianIntegrable` process embeds into `Lp ℝ 2 (ℱ.predictableMeasure P T)` via
`TauCeti.BrownianIntegrable.toPredictableLp`, compatible with zero, addition, negation,
subtraction, scaling, and product-a.e. equality.

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

/-- Finite expected energy on every finite horizon gives finite pathwise energy on all
finite horizons simultaneously. -/
theorem BrownianIntegrable.locallyBrownianIntegrable [SFinite P]
    (h : BrownianIntegrable ℱ P H) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨h.isStronglyPredictable, fun n ↦ ?_⟩
  exact ((h.memLp n).comp_measurePreserving
    (Measure.measurePreserving_swap (μ := P) (ν := _))).ae_memLp_prod_right

/-- The zero process belongs to the expected-square-energy integrand domain. -/
@[simp]
theorem BrownianIntegrable.zero : BrownianIntegrable ℱ P (0 : ℝ≥0 → Ω → ℝ) :=
  ⟨stronglyMeasurable_const, fun _ ↦ .zero⟩

/-- The zero process belongs to the pathwise square-energy integrand domain. -/
@[simp]
theorem LocallyBrownianIntegrable.zero : LocallyBrownianIntegrable ℱ P (0 : ℝ≥0 → Ω → ℝ) :=
  ⟨stronglyMeasurable_const, .of_forall fun _ _ ↦ .zero⟩

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

/-- Negation preserves finite expected square energy. -/
theorem BrownianIntegrable.neg (h : BrownianIntegrable ℱ P H) :
    BrownianIntegrable ℱ P (fun t ω ↦ -H t ω) := by
  simpa only [neg_one_mul] using h.const_mul (-1)

/-- Subtraction preserves finite expected square energy. -/
theorem BrownianIntegrable.sub (hH : BrownianIntegrable ℱ P H)
    (hK : BrownianIntegrable ℱ P K) :
    BrownianIntegrable ℱ P (fun t ω ↦ H t ω - K t ω) := by
  simpa only [sub_eq_add_neg] using hH.add hK.neg

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

/-- Negation preserves finite pathwise square energy. -/
theorem LocallyBrownianIntegrable.neg (h : LocallyBrownianIntegrable ℱ P H) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ -H t ω) := by
  simpa only [neg_one_mul] using h.const_mul (-1)

/-- Subtraction preserves finite pathwise square energy. -/
theorem LocallyBrownianIntegrable.sub (hH : LocallyBrownianIntegrable ℱ P H)
    (hK : LocallyBrownianIntegrable ℱ P K) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ H t ω - K t ω) := by
  simpa only [sub_eq_add_neg] using hH.add hK.neg

/-- Restriction to a predictable set preserves finite expected square energy. -/
theorem BrownianIntegrable.indicator (hH : BrownianIntegrable ℱ P H)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A) :
    BrownianIntegrable ℱ P (fun t ω ↦ A.indicator (Function.uncurry H) (t, ω)) := by
  refine ⟨hH.isStronglyPredictable.indicator hA, fun T ↦ ?_⟩
  exact (hH.memLp T).indicator (ℱ.predictable_le_prod A hA).nullMeasurableSet

/-- Restricting an expected-square-integrable predictable integrand to a predictable rectangle
`(u, v] × E` preserves `BrownianIntegrable`. -/
theorem BrownianIntegrable.indicator_Ioc_prod (hH : BrownianIntegrable ℱ P H) (u v : ℝ≥0)
    {E : Set Ω} (hE : MeasurableSet[ℱ u] E) :
    BrownianIntegrable ℱ P (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ E.indicator (H t) ω) t) := by
  convert hH.indicator (measurableSet_predictable_Ioc_prod u v hE) using 1
  ext t ω
  by_cases ht : t ∈ Ioc u v <;> by_cases hω : ω ∈ E <;> simp [ht, hω]

/-- Restriction to a predictable set preserves finite pathwise square energy. -/
theorem LocallyBrownianIntegrable.indicator (hH : LocallyBrownianIntegrable ℱ P H)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ A.indicator (Function.uncurry H) (t, ω)) := by
  refine ⟨hH.isStronglyPredictable.indicator hA, ?_⟩
  filter_upwards [hH.ae_memLp] with ω hω
  intro T
  exact (hω T).indicator ((ℱ.predictable_le_prod A hA).preimage
    (measurable_id.prodMk measurable_const)).nullMeasurableSet

private theorem isStronglyPredictable_ite_lt (s : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsStronglyPredictable ℱ (fun t ω ↦ if s < t then ξ ω else 0) := by
  classical
  let : MeasurableSpace Ω := ℱ s
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let S : Set (ℝ≥0 × Ω) := Ioi s ×ˢ univ
  have hS : MeasurableSet S := measurableSet_predictable_Ioi_prod (𝓕 := ℱ) MeasurableSet.univ
  have hproj : Measurable (fun p : S ↦ p.val.2) := by
    intro A hA
    refine ⟨Ioi s ×ˢ A, measurableSet_predictable_Ioi_prod (𝓕 := ℱ) hA, ?_⟩
    ext p
    simp [S, p.property.1]
  change StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ if s < p.1 then ξ p.2 else 0)
  simpa [S] using (hξ.comp_measurable hproj).dite stronglyMeasurable_const hS

/-- Multiplying an expected-square-integrable integrand after a deterministic time `s` by an
essentially bounded `ℱ s`-measurable random variable preserves `BrownianIntegrable`. -/
theorem BrownianIntegrable.ite_lt_mul [SFinite P] (hH : BrownianIntegrable ℱ P H)
    (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ_bd : MemLp ξ ∞ P) :
    BrownianIntegrable ℱ P (fun t ω ↦ if s < t then ξ ω * H t ω else 0) := by
  have hm := hH.mul (isStronglyPredictable_ite_lt s hξ) fun T ↦ by
    have hi := (hξ_bd.comp_snd
      ((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))).indicator
      ((measurableSet_Ioi (a := s)).prod MeasurableSet.univ).nullMeasurableSet
    convert hi using 1
    ext ⟨t, ω⟩
    by_cases ht : s < t <;> simp [ht]
  convert hm using 1
  ext t ω
  by_cases ht : s < t <;> simp [ht, mul_comm]

/-- Multiplying a pathwise-square-integrable integrand after a deterministic time `s` by an
`ℱ s`-measurable random variable preserves `LocallyBrownianIntegrable`. No boundedness or moment
assumption on the multiplier is needed. -/
theorem LocallyBrownianIntegrable.ite_lt_mul (hH : LocallyBrownianIntegrable ℱ P H)
    (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    LocallyBrownianIntegrable ℱ P (fun t ω ↦ if s < t then ξ ω * H t ω else 0) := by
  refine ⟨?_, ?_⟩
  · convert (isStronglyPredictable_ite_lt s hξ).mul hH.isStronglyPredictable using 1
    ext t ω; by_cases ht : s < t <;> simp [ht]
  · filter_upwards [hH.ae_memLp] with ω hω T
    have hi := ((hω T).const_mul (ξ ω)).indicator (measurableSet_Ioi (a := s)).nullMeasurableSet
    convert hi using 1
    ext t
    by_cases ht : s < t <;> simp [ht]

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

namespace BrownianIntegrable

/-- Finite-horizon expected square energy written against `Probability.timeMeasure`. -/
theorem memLp_timeMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T

/-- Finite-horizon membership in the trimmed predictable `L²` space. -/
theorem memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr (hH.memLp_timeMeasure T)

/-- The finite-horizon predictable `L²` class of a `BrownianIntegrable` process. -/
def toPredictableLp (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    Lp ℝ 2 (ℱ.predictableMeasure P T) :=
  (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)

/-- Definitional unfolding of `toPredictableLp` as `MemLp.toLp`. -/
theorem toPredictableLp_def (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    hH.toPredictableLp T = (hH.memLp_predictableMeasure T).toLp (Function.uncurry H) := (rfl)

/-- Almost-everywhere representative of `toPredictableLp` under the predictable measure. -/
theorem coeFn_toPredictableLp (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    hH.toPredictableLp T =ᵐ[ℱ.predictableMeasure P T] Function.uncurry H :=
  (hH.memLp_predictableMeasure T).coeFn_toLp

/-- Almost-everywhere representative of `toPredictableLp` under the ambient product measure. -/
theorem coeFn_toPredictableLp_prod (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    (hH.toPredictableLp T : ℝ≥0 × Ω → ℝ) =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry H := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  exact (ℱ.ae_eq_predictableMeasure_iff P (Lp.stronglyMeasurable _).measurable
    hH.isStronglyPredictable.measurable T).mp (hH.coeFn_toPredictableLp T)

/-- Embedding the zero integrand into `Lp ℝ 2 (ℱ.predictableMeasure P T)` yields `0`. -/
@[simp] theorem toPredictableLp_zero (T : ℝ≥0) :
    (zero : BrownianIntegrable ℱ P 0).toPredictableLp T = 0 := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable; exact MemLp.toLp_zero _

/-- `BrownianIntegrable.toPredictableLp` commutes with pointwise addition of integrands. -/
@[simp] theorem toPredictableLp_add (hH : BrownianIntegrable ℱ P H)
    (hK : BrownianIntegrable ℱ P K) (T : ℝ≥0) :
    (hH.add hK).toPredictableLp T = hH.toPredictableLp T + hK.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable; exact MemLp.toLp_add _ _

/-- `BrownianIntegrable.toPredictableLp` commutes with multiplication by a real constant. -/
@[simp] theorem toPredictableLp_const_mul (hH : BrownianIntegrable ℱ P H) (c : ℝ) (T : ℝ≥0) :
    (hH.const_mul c).toPredictableLp T = c • hH.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable; exact MemLp.toLp_const_smul c _

/-- `BrownianIntegrable.toPredictableLp` commutes with pointwise negation of integrands. -/
@[simp] theorem toPredictableLp_neg (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    hH.neg.toPredictableLp T = -hH.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable; exact MemLp.toLp_neg _

/-- `BrownianIntegrable.toPredictableLp` commutes with pointwise subtraction of integrands. -/
@[simp] theorem toPredictableLp_sub (hH : BrownianIntegrable ℱ P H)
    (hK : BrownianIntegrable ℱ P K) (T : ℝ≥0) :
    (hH.sub hK).toPredictableLp T = hH.toPredictableLp T - hK.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable; exact MemLp.toLp_sub _ _

/-- Two `BrownianIntegrable` integrands have equal predictable `L²` embeddings on `[0, T]` if
and only if they agree almost everywhere under `(timeMeasure T).prod P`. -/
theorem toPredictableLp_eq_iff (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    {T : ℝ≥0} :
    hH.toPredictableLp T = hK.toPredictableLp T ↔
      Function.uncurry H =ᵐ[(Probability.timeMeasure T).prod P] Function.uncurry K := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  refine ⟨fun h ↦ (hH.coeFn_toPredictableLp_prod T).symm.trans
    (h ▸ hK.coeFn_toPredictableLp_prod T), fun hHK ↦ MemLp.toLp_congr _ _ ?_⟩
  exact (ℱ.ae_eq_predictableMeasure_iff P
    hH.isStronglyPredictable.measurable hK.isStronglyPredictable.measurable T).mpr hHK

/-- A finite-grid elementary holding with square-integrable left-measurable heights belongs to
`BrownianIntegrable`. -/
theorem simpleHolding [SFinite P] {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    BrownianIntegrable ℱ P (Finance.simpleHolding τ n a) :=
  ⟨Finance.isStronglyPredictable_simpleHolding ha, fun T ↦ by
    simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using
      (ℱ.memLp_predictableMeasure_iff P (Finance.isStronglyPredictable_simpleHolding ha) T 2).mp
        (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T)⟩

end BrownianIntegrable

end TauCeti
