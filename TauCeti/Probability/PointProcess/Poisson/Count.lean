/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.NNReal
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Counts of temporal Poisson random measures

The natural-valued cumulative counts of a Poisson random measure with locally finite intensity
have independent increments. For homogeneous rate `r`, the increment over `(s,t]` has Poisson
law with parameter `r * (t-s)`. Counts use `(0,t]`, so the initial count is zero. The rate may
be zero; an inhomogeneous intensity may have atoms and hence simultaneous occurrences.

The natural-valued representative is obtained by flooring the finite mass. On exceptional
realizations with infinite mass the representative is zero. No pathwise integrality,
simplicity, or local finiteness assumption is required: the finite-window Poisson laws
supply the almost-everywhere identities used here.

These are the count-process implications of the real-line Poisson description in
G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
2018, Chapter 7.
-/

public section

open Function MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {M : Ω → Measure ℝ≥0} {Λ : Measure ℝ≥0} {r : ℝ≥0}

namespace IsPoissonRandomMeasure

/-- The natural-valued count on any right-closed temporal interval has its Poisson law.
This includes empty intervals and rate zero. -/
theorem hasLaw_nat_count_Ioc (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume))
    (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t)).toNNReal⌋₊) (poissonMeasure (r * (t - s))) P := by
  have heval : ((r : ℝ≥0∞) • nnvolume) (Ioc s t) = (r * (t - s) : ℝ≥0) := by
    simp only [smul_apply, nnvolume_Ioc, smul_eq_mul, ENNReal.coe_mul]
  have hc := h.hasLaw (A := Ioc s t) measurableSet_Ioc (by rw [heval]; exact ENNReal.coe_lt_top)
  simp only [heval, ENNReal.toNNReal_coe] at hc
  have hm : Measurable (fun x : ℝ≥0∞ ↦ ⌊x.toNNReal⌋₊) := by fun_prop
  have hp := (hasLaw_map (P := (poissonMeasure (r * (t - s))).map
    (Nat.cast : ℕ → ℝ≥0∞)) hm.aemeasurable).comp hc
  have hmap : ((poissonMeasure (r * (t - s))).map (Nat.cast : ℕ → ℝ≥0∞)).map
      (fun x ↦ ⌊x.toNNReal⌋₊) = poissonMeasure (r * (t - s)) := by
    rw [Measure.map_map hm Measurable.of_discrete]
    simp [Function.comp_def]
  simpa only [hmap, Function.comp_def] using hp

private theorem ae_count_Ioc_natCast [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (s t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, M ω (Ioc s t) = n := by
  have hc := h.hasLaw (A := Ioc s t) measurableSet_Ioc measure_Ioc_lt_top
  have hmem : ∀ᵐ x ∂P.map (fun ω ↦ M ω (Ioc s t)),
      x ∈ range (Nat.cast : ℕ → ℝ≥0∞) := by
    rw [hc.map_eq]
    exact ae_map_mem_range (countable_range _).measurableSet Measurable.of_discrete.aemeasurable
  filter_upwards [ae_of_ae_map hc.aemeasurable hmem] with ω ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

private theorem ae_nat_count_sub_eq [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) {s t : ℝ≥0} (hst : s ≤ t) :
    (fun ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ - ⌊(M ω (Ioc 0 s)).toNNReal⌋₊) =ᵐ[P]
      (fun ω ↦ ⌊(M ω (Ioc s t)).toNNReal⌋₊) := by
  filter_upwards [h.ae_count_Ioc_natCast 0 s, h.ae_count_Ioc_natCast s t] with ω hs ht
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  have hadd := measure_union (μ := M ω) (s₁ := Ioc 0 s) (s₂ := Ioc s t)
    (Ioc_disjoint_Ioc_of_le (le_refl s)) measurableSet_Ioc
  rw [Ioc_union_Ioc_eq_Ioc (a := 0) bot_le hst, ha, hb,
    ← Nat.cast_add] at hadd
  rw [hadd, ha, hb]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast, Nat.add_sub_cancel_left]

/-- A cumulative-count increment has Poisson law with parameter equal to rate times elapsed
time. Counts exclude the origin and include the observation endpoint. -/
theorem hasLaw_nat_count_sub (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume))
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ - ⌊(M ω (Ioc 0 s)).toNNReal⌋₊)
      (poissonMeasure (r * (t - s))) P := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  exact (h.hasLaw_nat_count_Ioc s t).congr (h.ae_nat_count_sub_eq hst)

/-- Natural cumulative counts of a Poisson random measure with locally finite intensity have
independent increments. The intensity may have atoms; no regularity assumptions on the
realizations or sample space are imposed. -/
theorem hasIndepIncrements_nat_count [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) P := by
  intro n t ht
  have hd : Pairwise (Disjoint on (fun i : Fin n ↦ Ioc (t i.castSucc) (t i.succ))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact Ioc_disjoint_Ioc_of_le (ht (by simpa using hij))
    · exact (Ioc_disjoint_Ioc_of_le (ht (by simpa using hij))).symm
  have hi := h.iIndepFun (A := fun i : Fin n ↦ Ioc (t i.castSucc) (t i.succ))
    (fun _ ↦ measurableSet_Ioc) (fun _ ↦ measure_Ioc_lt_top) hd
  have hfloor := hi.comp (fun _ x ↦ ⌊x.toNNReal⌋₊) (fun _ ↦ by fun_prop)
  exact hfloor.congr fun i ↦ (h.ae_nat_count_sub_eq (ht i.castSucc_le_succ)).symm

end IsPoissonRandomMeasure

end TauCeti.Probability
