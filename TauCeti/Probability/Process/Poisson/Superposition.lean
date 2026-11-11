/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Count
public import TauCeti.Probability.PointProcess.Poisson.IntegerValued
public import TauCeti.Probability.PointProcess.Poisson.Superposition

/-!
# Superposition of temporal Poisson count processes

Adding independent homogeneous Poisson random measures adds the rates of their count
processes. The natural-valued counts of the superposition agree with the sum of the
component counts on one event of full probability, simultaneously at every time.
Consequently the summed count process has independent increments and Poisson increment
laws with the summed rate. Counts use `(0,t]`; zero rates and empty families are allowed.

The simultaneous identity matters because natural counts assign zero to infinite masses:
flooring arbitrary extended masses does not commute with addition. Almost-sure local
finiteness and integrality of the component measures justify this passage, without any
pathwise assumptions on the original realizations.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.3 and Chapter 7.

The random-measure superposition theorem and the count-process adapter are those of
`TauCeti.Probability.PointProcess.Poisson.Superposition` and
`TauCeti.Probability.PointProcess.Poisson.Count`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} {M : ι → Ω → Measure ℝ≥0} {Λ : ι → Measure ℝ≥0}

/-- Natural counts commute with finite superposition simultaneously at every time, almost
surely. Independence is unnecessary for this identity. -/
theorem ae_nat_count_sum [∀ i, IsLocallyFiniteMeasure (Λ i)]
    (h : ∀ i, IsPoissonRandomMeasure P (M i) (Λ i)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊((∑ i, M i ω) (Ioc 0 t)).toNNReal⌋₊ =
        ∑ i, ⌊(M i ω (Ioc 0 t)).toNNReal⌋₊ := by
  classical
  filter_upwards [ae_all_iff.2 (fun i => (h i).ae_isIntegerValued),
    ae_all_iff.2 (fun i => (h i).ae_isLocallyFiniteMeasure)] with ω hint hfin
  let (i : ι) : IsLocallyFiniteMeasure (M i ω) := hfin i
  intro t
  have he (i : ι) : M i ω (Ioc 0 t) =
      (⌊(M i ω (Ioc 0 t)).toNNReal⌋₊ : ℝ≥0∞) := by
    obtain ⟨n, hn⟩ := (hint i).exists_eq_natCast (A := Ioc 0 t)
      measurableSet_Ioc measure_Ioc_lt_top
    simp [hn]
  have hsum : (∑ i, M i ω (Ioc 0 t)) =
      ((∑ i, ⌊(M i ω (Ioc 0 t)).toNNReal⌋₊ : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => he i
  rw [sum_apply, hsum, ENNReal.toNNReal_natCast, Nat.floor_natCast]

variable {r : ι → ℝ≥0}

private theorem poisson_sum
    (h : ∀ i, IsPoissonRandomMeasure P (M i) ((r i : ℝ≥0∞) • nnvolume))
    (hind : iIndepFun M P) :
    IsPoissonRandomMeasure P (fun ω => ∑ i, M i ω)
      (((∑ i, r i : ℝ≥0) : ℝ≥0∞) • nnvolume) := by
  classical
  have hs := isPoissonRandomMeasure_finsetSum (s := Finset.univ)
    (fun i _ => h i) (hind.precomp Subtype.val_injective)
  simpa only [← Finset.sum_smul, ENNReal.ofNNReal_finsetSum] using hs

/-- The sum of independent homogeneous Poisson count processes has independent increments.
Independence is imposed on the component random measures, hence on their entire histories,
not merely on the counts at any one time. -/
theorem hasIndepIncrements_sum_nat_count
    (h : ∀ i, IsPoissonRandomMeasure P (M i) ((r i : ℝ≥0∞) • nnvolume))
    (hind : iIndepFun M P) :
    HasIndepIncrements (fun t ω => ∑ i, ⌊(M i ω (Ioc 0 t)).toNNReal⌋₊) P := by
  let (i : ι) : IsLocallyFiniteMeasure ((r i : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  let : IsLocallyFiniteMeasure (((∑ i, r i : ℝ≥0) : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  have he := ae_nat_count_sum h
  intro n t ht
  apply ((poisson_sum h hind).hasIndepIncrements_nat_count n t ht).congr
  intro i
  filter_upwards [he] with ω hω
  rw [hω, hω]

/-- A finite sum of independent homogeneous Poisson count processes has Poisson increments
with rate the sum of the component rates. Equal endpoints, zero rates and the empty family
are included. -/
theorem hasLaw_sum_nat_count_sub_poissonMeasure
    (h : ∀ i, IsPoissonRandomMeasure P (M i) ((r i : ℝ≥0∞) • nnvolume))
    (hind : iIndepFun M P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => (∑ i, ⌊(M i ω (Ioc 0 t)).toNNReal⌋₊) -
      ∑ i, ⌊(M i ω (Ioc 0 s)).toNNReal⌋₊)
      (poissonMeasure ((∑ i, r i) * (t - s))) P := by
  let (i : ι) : IsLocallyFiniteMeasure ((r i : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  apply ((poisson_sum h hind).hasLaw_nat_count_sub_smul_nnvolume hst).congr
  filter_upwards [ae_nat_count_sum h] with ω hω
  rw [hω, hω]

end TauCeti.Probability
