/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.PointProcess.Poisson.IntegerValued
public import TauCeti.Probability.PointProcess.Poisson.Superposition.Basic
public import TauCeti.MeasureTheory.Measure.NNReal
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Counts of temporal Poisson random measures

The natural-valued cumulative counts of a Poisson random measure with locally finite intensity
are measurable, almost surely monotone, and have independent increments. The increment over
`(s,t]` has Poisson law with parameter `(Λ (Ioc s t)).toNNReal`, equal to `r * (t-s)` for
homogeneous rate `r`. Counts use `(0,t]`, so the initial count is zero. The rate may
be zero; an inhomogeneous intensity may have atoms and hence simultaneous occurrences.

The natural-valued representative is obtained by flooring the finite mass. On exceptional
realizations with infinite mass the representative is zero. No pathwise integrality,
simplicity, or local finiteness assumption is required: the finite-window Poisson laws
supply the almost-everywhere identities used here.

Finite independent superposition adds the interval intensities, and in the homogeneous
case adds the rates. Natural counts commute with superposition on one event of full
probability, simultaneously at every time. Local finiteness and integrality justify this
identity despite the exceptional infinite masses being represented by zero.

These are the count-process implications of the superposition theorem and real-line
Poisson description in G. Last and M. Penrose, *Lectures on the Poisson Process*,
Cambridge University Press, 2018, Theorem 3.3 and Chapter 7.
-/

public section

open Function MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {M : Ω → Measure ℝ≥0} {Λ : Measure ℝ≥0} {r : ℝ≥0}

namespace IsPoissonRandomMeasure

/-- Each natural-valued cumulative count of a Poisson random measure is measurable. -/
theorem measurable_nat_count (h : IsPoissonRandomMeasure P M Λ) (t : ℝ≥0) :
    Measurable (fun ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) :=
  ((Measure.measurable_coe measurableSet_Ioc).comp h.measurable).ennreal_toNNReal.nat_floor

/-- The natural-valued count on any right-closed temporal interval has Poisson law with
parameter equal to the intensity of that interval. This includes empty intervals. -/
theorem hasLaw_nat_count_Ioc [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t)).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t)).toNNReal) P :=
  h.hasLaw_natFloor measurableSet_Ioc measure_Ioc_lt_top

/-- For homogeneous intensity, the interval count has parameter rate times elapsed time.
This includes empty intervals and rate zero. -/
theorem hasLaw_nat_count_Ioc_smul_nnvolume
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t)).toNNReal⌋₊) (poissonMeasure (r * (t - s))) P := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  simpa only [smul_nnvolume_Ioc, ENNReal.toNNReal_coe] using h.hasLaw_nat_count_Ioc s t

/-- Natural cumulative counts are monotone on one event of full probability. Local finiteness
of the intensity rules out infinite counts simultaneously on all bounded time intervals. -/
theorem ae_monotone_nat_count [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) := by
  filter_upwards [ae_all_iff.2 (fun n : ℕ ↦
    h.ae_exists_eq_natCast (A := Ioc 0 (n : ℝ≥0)) measurableSet_Ioc measure_Ioc_lt_top)] with ω hω
  have hfin (t : ℝ≥0) : M ω (Ioc 0 t) ≠ ∞ := by
    obtain ⟨n, hn⟩ := hω ⌈t⌉₊
    exact ne_top_of_le_ne_top (by rw [hn]; exact ENNReal.natCast_ne_top n)
      (measure_mono (Ioc_subset_Ioc_right (Nat.le_ceil t)))
  intro s t hst
  exact Nat.floor_mono (ENNReal.toNNReal_mono (hfin t)
    (measure_mono (Ioc_subset_Ioc_right hst)))

/-- If the intensity gives no mass to the origin, cumulative masses equal the natural-valued
counts simultaneously at every time, on one event of full probability. In particular the
identity is available for comparing full count-process and random-measure laws. -/
theorem ae_forall_measure_Iic_eq_natCast_nat_count [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (hΛ : Λ {0} = 0) :
    ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ≥0∞) := by
  filter_upwards [h.ae_isIntegerValued, h.ae_isLocallyFiniteMeasure,
    h.ae_eq_zero hΛ]
    with ω hint hfin hz t
  let := hfin
  obtain ⟨n, hn⟩ := hint.exists_eq_natCast (A := Ioc 0 t)
    measurableSet_Ioc measure_Ioc_lt_top
  have hinterval : M ω (Iic t) = M ω (Ioc 0 t) := by
    have hu := measure_union (μ := M ω) (s₁ := Iic 0) (s₂ := Ioc 0 t)
      (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
    have hbot : Iic (0 : ℝ≥0) = {0} := by ext x; simp
    rw [Iic_union_Ioc_eq_Iic (zero_le (a := t)), hbot, hz, zero_add] at hu
    exact hu
  simp [hinterval, hn]

private theorem ae_nat_count_sub_eq [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) {s t : ℝ≥0} (hst : s ≤ t) :
    (fun ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ - ⌊(M ω (Ioc 0 s)).toNNReal⌋₊) =ᵐ[P]
      (fun ω ↦ ⌊(M ω (Ioc s t)).toNNReal⌋₊) := by
  filter_upwards [h.ae_natCast_natFloor_eq (A := Ioc 0 s) measurableSet_Ioc measure_Ioc_lt_top,
    h.ae_natCast_natFloor_eq (A := Ioc s t) measurableSet_Ioc measure_Ioc_lt_top] with ω hs ht
  have hadd := measure_union (μ := M ω) (s₁ := Ioc 0 s) (s₂ := Ioc s t)
    (Ioc_disjoint_Ioc_of_le (le_refl s)) measurableSet_Ioc
  rw [Ioc_union_Ioc_eq_Ioc (a := 0) bot_le hst, ← hs, ← ht, ← Nat.cast_add] at hadd
  rw [hadd]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast, Nat.add_sub_cancel_left]

/-- A cumulative-count increment has Poisson law with parameter equal to the interval intensity.
Counts exclude the origin and include the observation endpoint. -/
theorem hasLaw_nat_count_sub [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ - ⌊(M ω (Ioc 0 s)).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t)).toNNReal) P :=
  (h.hasLaw_nat_count_Ioc s t).congr (h.ae_nat_count_sub_eq hst)

/-- For homogeneous intensity, a cumulative-count increment has Poisson law with parameter
rate times elapsed time. This includes rate zero and equal observation times. -/
theorem hasLaw_nat_count_sub_smul_nnvolume
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume))
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ - ⌊(M ω (Ioc 0 s)).toNNReal⌋₊)
      (poissonMeasure (r * (t - s))) P := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  simpa only [smul_nnvolume_Ioc, ENNReal.toNNReal_coe] using h.hasLaw_nat_count_sub hst

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

variable {ι : Type*} {I : Finset ι} {N : ι → Ω → Measure ℝ≥0}
  {Λs : ι → Measure ℝ≥0}

/-- Natural counts commute with finite superposition simultaneously at every time, almost
surely. Only the selected intensities need be locally finite; independence is unnecessary. -/
theorem ae_nat_count_finsetSum [∀ i : I, IsLocallyFiniteMeasure (Λs i)]
    (h : ∀ i ∈ I, IsPoissonRandomMeasure P (N i) (Λs i)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊((∑ i ∈ I, N i ω) (Ioc 0 t)).toNNReal⌋₊ =
        ∑ i ∈ I, ⌊(N i ω (Ioc 0 t)).toNNReal⌋₊ := by
  classical
  filter_upwards [ae_all_iff.2 (fun i : I => (h i i.property).ae_isIntegerValued),
    ae_all_iff.2 (fun i : I => (h i i.property).ae_isLocallyFiniteMeasure)] with ω hint hfin
  let (i : I) : IsLocallyFiniteMeasure (N i ω) := hfin i
  intro t
  have he (i : I) : N i ω (Ioc 0 t) =
      (⌊(N i ω (Ioc 0 t)).toNNReal⌋₊ : ℝ≥0∞) := by
    obtain ⟨n, hn⟩ := (hint i).exists_eq_natCast (A := Ioc 0 t)
      measurableSet_Ioc measure_Ioc_lt_top
    simp [hn]
  have hsum : (∑ i ∈ I, N i ω (Ioc 0 t)) =
      ((∑ i ∈ I, ⌊(N i ω (Ioc 0 t)).toNNReal⌋₊ : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i hi => he ⟨i, hi⟩
  rw [sum_apply, hsum, ENNReal.toNNReal_natCast, Nat.floor_natCast]

/-- A finite sum of independent Poisson count processes with locally finite intensities
has independent increments. Independence concerns the selected random measures, hence their
entire histories, not merely the counts at a single time. -/
theorem hasIndepIncrements_finsetSum_nat_count [∀ i : I, IsLocallyFiniteMeasure (Λs i)]
    (h : ∀ i ∈ I, IsPoissonRandomMeasure P (N i) (Λs i))
    (hind : iIndepFun (fun i : I => N i) P) :
    HasIndepIncrements (fun t ω => ∑ i ∈ I, ⌊(N i ω (Ioc 0 t)).toNNReal⌋₊) P := by
  let : IsFiniteMeasureOnCompacts (∑ i ∈ I, Λs i) := ⟨fun K hK => by
    rw [sum_apply]
    exact ENNReal.sum_lt_top.mpr fun i hi => by
      let : IsLocallyFiniteMeasure (Λs i) := ‹∀ i : I, IsLocallyFiniteMeasure (Λs i)› ⟨i, hi⟩
      exact hK.measure_lt_top⟩
  have he := ae_nat_count_finsetSum h
  intro n t ht
  apply ((isPoissonRandomMeasure_finsetSum h hind).hasIndepIncrements_nat_count n t ht).congr
  intro i
  filter_upwards [he] with ω hω
  rw [hω, hω]

/-- A finite independent superposition has Poisson count increments with parameter the sum
of the selected interval intensities. Locally finite intensities may be inhomogeneous or
atomic. Equal endpoints and the empty family are included. -/
theorem hasLaw_finsetSum_nat_count_sub [∀ i : I, IsLocallyFiniteMeasure (Λs i)]
    (h : ∀ i ∈ I, IsPoissonRandomMeasure P (N i) (Λs i))
    (hind : iIndepFun (fun i : I => N i) P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => (∑ i ∈ I, ⌊(N i ω (Ioc 0 t)).toNNReal⌋₊) -
      ∑ i ∈ I, ⌊(N i ω (Ioc 0 s)).toNNReal⌋₊)
      (poissonMeasure (∑ i ∈ I, (Λs i (Ioc s t)).toNNReal)) P := by
  let : IsFiniteMeasureOnCompacts (∑ i ∈ I, Λs i) := ⟨fun K hK => by
    rw [sum_apply]
    exact ENNReal.sum_lt_top.mpr fun i hi => by
      let : IsLocallyFiniteMeasure (Λs i) := ‹∀ i : I, IsLocallyFiniteMeasure (Λs i)› ⟨i, hi⟩
      exact hK.measure_lt_top⟩
  have hfin (i) (hi : i ∈ I) : Λs i (Ioc s t) ≠ ∞ := by
    let : IsLocallyFiniteMeasure (Λs i) := ‹∀ i : I, IsLocallyFiniteMeasure (Λs i)› ⟨i, hi⟩
    exact measure_Ioc_lt_top.ne
  have hlaw := (isPoissonRandomMeasure_finsetSum h hind).hasLaw_nat_count_sub hst
  rw [sum_apply, ENNReal.toNNReal_sum hfin] at hlaw
  apply hlaw.congr
  filter_upwards [ae_nat_count_finsetSum h] with ω hω
  rw [hω, hω]

/-- A finite sum of independent homogeneous Poisson count processes has Poisson increments
with rate the sum of the selected rates. Zero rates, equal endpoints and the empty family
are included. -/
theorem hasLaw_finsetSum_nat_count_sub_smul_nnvolume {rs : ι → ℝ≥0}
    (h : ∀ i ∈ I, IsPoissonRandomMeasure P (N i) ((rs i : ℝ≥0∞) • nnvolume))
    (hind : iIndepFun (fun i : I => N i) P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => (∑ i ∈ I, ⌊(N i ω (Ioc 0 t)).toNNReal⌋₊) -
      ∑ i ∈ I, ⌊(N i ω (Ioc 0 s)).toNNReal⌋₊)
      (poissonMeasure ((∑ i ∈ I, rs i) * (t - s))) P := by
  let (i : I) : IsLocallyFiniteMeasure ((rs i : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  simpa only [smul_nnvolume_Ioc, ENNReal.toNNReal_coe, Finset.sum_mul] using
    hasLaw_finsetSum_nat_count_sub h hind hst

end TauCeti.Probability
