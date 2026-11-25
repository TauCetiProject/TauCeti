/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Analysis.Subadditive
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Kolmogorov–Sinai entropy

For a map `T : X → X` and a countable label `a : X → ι`, the length-`n` itinerary
`iteratedPartitionLabel T a n` sends `x` to `(a x, a (T x), …, a (T^[n-1] x))`; it labels the join
of the partitions `T^[-k] a`, `k < n`. At `n = 0` it is the unique empty tuple.

* `TauCeti.partitionEntropyRate μ T a` is `⨅ n ≥ 1, H(iteratedPartitionLabel T a n) / n`, in
  `[0, ∞]`.
* `TauCeti.measureEntropy μ T`, the Kolmogorov–Sinai (measure-theoretic) entropy, is the supremum
  of these rates over the measurable labels `a : X → ℕ` of finite entropy. Every countable label
  space embeds in `ℕ` (`TauCeti.countablePartitionEntropy_comp_of_injective`). The value lies in
  `[0, ∞]`, so infinite entropy is retained.

## Main results

* `TauCeti.measurable_iteratedPartitionLabel`: itineraries of a measurable label under a
  measurable map are measurable.
* `TauCeti.countablePartitionEntropy_iteratedPartitionLabel_add_le`: for a measure-preserving map
  under a probability (or zero) measure the itinerary entropies are subadditive,
  `H(join_{m+n} a) ≤ H(join_m a) + H(join_n a)`.
* `TauCeti.tendsto_partitionEntropyRate`: by Fekete's lemma, `H(join_n a) / n` converges to the
  entropy rate for a measure-preserving map under a probability (or zero) measure and a
  measurable countable label.
* `TauCeti.measureEntropy_id`: the identity has entropy zero; its itineraries repeat one label.
* `TauCeti.measureEntropy_eq_zero_of_iterate_eq_id`: under a probability (or zero) measure, a
  measure-preserving map with `T^[p] = id` for some `p ≥ 1` has entropy zero.
* `TauCeti.measureEntropy_eq_zero_of_forall`: if every measurable label has entropy zero, for
  instance under a Dirac probability (`TauCeti.countablePartitionEntropy_dirac`) or the zero
  measure, then every map has entropy zero.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The length-`n` itinerary of the label `a` under `T`: `x ↦ (a x, a (T x), …, a (T^[n-1] x))`.
It labels the join of the partitions given by `a ∘ T^[k]` for `k < n`. -/
def iteratedPartitionLabel (T : X → X) (a : X → ι) (n : ℕ) : X → (Fin n → ι) :=
  fun x k ↦ a (T^[k] x)

@[simp]
theorem iteratedPartitionLabel_apply (T : X → X) (a : X → ι) (n : ℕ) (x : X) (k : Fin n) :
    iteratedPartitionLabel T a n x k = a (T^[k] x) :=
  (rfl)

/-- The length-zero itinerary is the unique empty tuple. -/
@[simp]
theorem iteratedPartitionLabel_zero (T : X → X) (a : X → ι) :
    iteratedPartitionLabel T a 0 = fun _ ↦ Fin.elim0 :=
  funext fun _ ↦ funext fun k ↦ k.elim0

/-- The length-one itinerary is the label itself, viewed as a constant tuple. -/
theorem iteratedPartitionLabel_one (T : X → X) (a : X → ι) :
    iteratedPartitionLabel T a 1 = Function.const (Fin 1) ∘ a :=
  funext fun x ↦ funext fun k ↦ by simp [Fin.fin_one_eq_zero k]

/-- Under the identity every itinerary repeats the label. -/
theorem iteratedPartitionLabel_id (a : X → ι) (n : ℕ) :
    iteratedPartitionLabel id a n = Function.const (Fin n) ∘ a :=
  funext fun x ↦ funext fun k ↦ by simp

/-- Itineraries of a measurable label under a measurable map are measurable. -/
theorem measurable_iteratedPartitionLabel [MeasurableSpace ι] {T : X → X} (hT : Measurable T)
    {a : X → ι} (ha : Measurable a) (n : ℕ) : Measurable (iteratedPartitionLabel T a n) :=
  measurable_pi_iff.mpr fun k ↦ ha.comp (hT.iterate k)

/-- The entropy rate of the label `a` under `T`: the infimum over `n ≥ 1` of the entropy of the
length-`n` itinerary divided by `n`. -/
noncomputable def partitionEntropyRate (μ : Measure X) (T : X → X) (a : X → ι) : ℝ≥0∞ :=
  ⨅ n : ℕ, countablePartitionEntropy μ (iteratedPartitionLabel T a (n + 1)) / (n + 1)

theorem partitionEntropyRate_def (μ : Measure X) (T : X → X) (a : X → ι) :
    partitionEntropyRate μ T a =
      ⨅ n : ℕ, countablePartitionEntropy μ (iteratedPartitionLabel T a (n + 1)) / (n + 1) :=
  (rfl)

/-- The entropy rate is at most the entropy of every positive-length itinerary divided by its
length. -/
theorem partitionEntropyRate_le_div {n : ℕ} (hn : 0 < n) (μ : Measure X) (T : X → X)
    (a : X → ι) :
    partitionEntropyRate μ T a ≤
      countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, Nat.cast_succ]
  exact iInf_le _ m

/-- A lower bound for the entropy rate is a lower bound for every normalised itinerary entropy of
positive length. -/
theorem le_partitionEntropyRate_iff {T : X → X} {a : X → ι} {c : ℝ≥0∞} :
    c ≤ partitionEntropyRate μ T a ↔
      ∀ n, 0 < n → c ≤ countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n := by
  refine ⟨fun h n hn ↦ h.trans (partitionEntropyRate_le_div hn μ T a), fun h ↦ le_iInf fun n ↦ ?_⟩
  have := h (n + 1) n.succ_pos
  rwa [Nat.cast_succ] at this

/-- The Kolmogorov–Sinai entropy of `T` with respect to `μ`: the supremum of the entropy rates of
the measurable labels `a : X → ℕ` of finite entropy. -/
noncomputable def measureEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ⨆ (a : X → ℕ) (_ : Measurable a) (_ : countablePartitionEntropy μ a ≠ ∞),
    partitionEntropyRate μ T a

theorem measureEntropy_def (μ : Measure X) (T : X → X) :
    measureEntropy μ T = ⨆ (a : X → ℕ) (_ : Measurable a)
      (_ : countablePartitionEntropy μ a ≠ ∞), partitionEntropyRate μ T a :=
  (rfl)

/-- An upper bound for the measure entropy is an upper bound for the rate of every measurable
label into `ℕ` of finite entropy. -/
theorem measureEntropy_le_iff {T : X → X} {c : ℝ≥0∞} :
    measureEntropy μ T ≤ c ↔ ∀ a : X → ℕ, Measurable a → countablePartitionEntropy μ a ≠ ∞ →
      partitionEntropyRate μ T a ≤ c := by
  simp only [measureEntropy_def, iSup_le_iff]

/-- The rate of a measurable label of finite entropy is at most the measure entropy. -/
theorem partitionEntropyRate_le_measureEntropy {T : X → X} {a : X → ℕ} (ha : Measurable a)
    (hfin : countablePartitionEntropy μ a ≠ ∞) :
    partitionEntropyRate μ T a ≤ measureEntropy μ T :=
  le_iSup₂_of_le a ha (le_iSup_of_le hfin le_rfl)

/-- The entropy rate is at most the entropy of the label itself. -/
theorem partitionEntropyRate_le (μ : Measure X) (T : X → X) (a : X → ι) :
    partitionEntropyRate μ T a ≤ countablePartitionEntropy μ a := by
  refine (partitionEntropyRate_le_div one_pos μ T a).trans_eq ?_
  rw [Nat.cast_one, div_one, iteratedPartitionLabel_one,
    countablePartitionEntropy_comp_of_injective a Function.const_injective]

/-- Under the identity the length-`(n + 1)` itinerary is the label repeated `n + 1` times, and so
has the same entropy as the label. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_id (μ : Measure X) (a : X → ι)
    (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel id a (n + 1)) =
      countablePartitionEntropy μ a := by
  rw [iteratedPartitionLabel_id]
  exact countablePartitionEntropy_comp_of_injective a Function.const_injective

/-- A label of finite entropy has rate zero under the identity. -/
theorem partitionEntropyRate_id {a : X → ι} (hfin : countablePartitionEntropy μ a ≠ ∞) :
    partitionEntropyRate μ id a = 0 := by
  rw [partitionEntropyRate_def]
  simp only [countablePartitionEntropy_iteratedPartitionLabel_id]
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp
  have h' : Tendsto (fun n : ℕ ↦ countablePartitionEntropy μ a / ((n : ℝ≥0∞) + 1)) atTop
      (𝓝 0) := by
    simpa [div_eq_mul_inv] using ENNReal.Tendsto.const_mul h (Or.inr hfin)
  exact le_antisymm (ge_of_tendsto' h' fun n ↦ iInf_le _ n) bot_le

/-- The identity has Kolmogorov–Sinai entropy zero. -/
@[simp]
theorem measureEntropy_id : measureEntropy μ id = 0 :=
  nonpos_iff_eq_zero.mp <|
    measureEntropy_le_iff.mpr fun _ _ hfin ↦ (partitionEntropyRate_id hfin).le

/-- If every measurable label into `ℕ` has entropy zero, every map has entropy zero. -/
theorem measureEntropy_eq_zero_of_forall
    (h : ∀ a : X → ℕ, Measurable a → countablePartitionEntropy μ a = 0) (T : X → X) :
    measureEntropy μ T = 0 :=
  nonpos_iff_eq_zero.mp (measureEntropy_le_iff.mpr fun a ha _ ↦
    (partitionEntropyRate_le μ T a).trans (h a ha).le)

/-- The Kolmogorov–Sinai entropy of any map with respect to a Dirac probability is zero. -/
@[simp]
theorem measureEntropy_dirac (x : X) (T : X → X) : measureEntropy (Measure.dirac x) T = 0 :=
  measureEntropy_eq_zero_of_forall (fun a _ ↦ countablePartitionEntropy_dirac a x) T

/-- The Kolmogorov–Sinai entropy of any map with respect to the zero measure is zero. -/
@[simp]
theorem measureEntropy_zero_measure (T : X → X) : measureEntropy (0 : Measure X) T = 0 :=
  measureEntropy_eq_zero_of_forall (fun a _ ↦ countablePartitionEntropy_zero_measure a) T

/-- An itinerary of length `m + n` is the join of the length-`m` itinerary with the
length-`n` itinerary started at `T^[m] x`, relabeled by `Fin.append`. -/
theorem iteratedPartitionLabel_add (T : X → X) (a : X → ι) (m n : ℕ) :
    iteratedPartitionLabel T a (m + n) = (fun p ↦ Fin.append p.1 p.2) ∘
      fun x ↦ (iteratedPartitionLabel T a m x, iteratedPartitionLabel T a n (T^[m] x)) := by
  funext x k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · simp
  · simp [← Function.iterate_add_apply, add_comm]

/-- A countable label is a coarsening of every itinerary of positive length, so its entropy is at
most the entropy of the itinerary, for every measure. -/
theorem countablePartitionEntropy_le_iteratedPartitionLabel [Countable ι] (T : X → X)
    (a : X → ι) {n : ℕ} (hn : 0 < n) :
    countablePartitionEntropy μ a ≤ countablePartitionEntropy μ (iteratedPartitionLabel T a n) :=
  (countablePartitionEntropy_comp_le _ fun u ↦ u ⟨0, hn⟩).trans_eq' <|
    congrArg _ <| funext fun x ↦ by simp

section Subadditive

variable [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {T : X → X}
  {a : X → ι}

/-- **Subadditivity of itinerary entropies.** For a measure-preserving map under a probability
(or zero) measure, `H(join_{m+n} a) ≤ H(join_m a) + H(join_n a)`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_add_le [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) (m n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T a (m + n)) ≤
      countablePartitionEntropy μ (iteratedPartitionLabel T a m) +
        countablePartitionEntropy μ (iteratedPartitionLabel T a n) := by
  have hb := measurable_iteratedPartitionLabel hT.measurable ha
  have hinj : Function.Injective fun p : (Fin m → ι) × (Fin n → ι) ↦ Fin.append p.1 p.2 :=
    (Fin.appendEquiv m n).injective
  rw [iteratedPartitionLabel_add, countablePartitionEntropy_comp_of_injective _ hinj]
  refine (countablePartitionEntropy_pair_le_add (hb m)
    ((hb n).comp (hT.measurable.iterate m))).trans_eq ?_
  rw [countablePartitionEntropy_comp_of_measurePreserving (hT.iterate m) (hb n)]

/-- Under a probability (or zero) measure, the entropy of the length-`n` itinerary of a
measure-preserving map is at most `n` times the entropy of the label. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_le_mul [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T a n) ≤
      n * countablePartitionEntropy μ a := by
  induction n with
  | zero => simp [iteratedPartitionLabel_zero]
  | succ n ih =>
    refine (countablePartitionEntropy_iteratedPartitionLabel_add_le hT ha n 1).trans ?_
    rw [iteratedPartitionLabel_one, countablePartitionEntropy_comp_of_injective a
      Function.const_injective, Nat.cast_succ, add_mul, one_mul]
    gcongr

/-- For a measure-preserving map under a probability (or zero) measure, a label of finite entropy
has itineraries of finite entropy. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_ne_top [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) (hfin : countablePartitionEntropy μ a ≠ ∞)
    (n : ℕ) : countablePartitionEntropy μ (iteratedPartitionLabel T a n) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hfin)
    (countablePartitionEntropy_iteratedPartitionLabel_le_mul hT ha n)

/-- **Fekete limit.** For a measure-preserving map of a probability space (or the zero measure)
and a measurable countable label `a`, the normalised itinerary entropies `H(join_n a) / n`
converge to the entropy rate, which is their infimum over `n ≥ 1`. When `H(a) = ∞` all of them
are `∞` for `n ≥ 1`. -/
theorem tendsto_partitionEntropyRate [IsZeroOrProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) :
    Tendsto (fun n : ℕ ↦ countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n) atTop
      (𝓝 (partitionEntropyRate μ T a)) := by
  set H : ℕ → ℝ≥0∞ := fun n ↦ countablePartitionEntropy μ (iteratedPartitionLabel T a n)
  rcases eq_or_ne (countablePartitionEntropy μ a) ∞ with htop | hfin
  · have hH : ∀ n, 0 < n → H n / n = ∞ := fun n hn ↦ by
      have := countablePartitionEntropy_le_iteratedPartitionLabel T a hn (μ := μ)
      rw [htop, top_le_iff] at this
      simp only [H, this]
      exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top n)
    have hrate : partitionEntropyRate μ T a = ∞ :=
      top_le_iff.mp (le_partitionEntropyRate_iff.mpr fun n hn ↦ (hH n hn).ge)
    rw [hrate]
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun n hn ↦ (hH n hn).symm⟩)
  have hHfin : ∀ n, H n ≠ ∞ := countablePartitionEntropy_iteratedPartitionLabel_ne_top hT ha hfin
  set u : ℕ → ℝ := fun n ↦ (H n).toReal
  have hu : Subadditive u := fun m n ↦ by
    rw [← ENNReal.toReal_add (hHfin m) (hHfin n)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hHfin m, hHfin n⟩)
      (countablePartitionEntropy_iteratedPartitionLabel_add_le hT ha m n)
  have hbdd : BddBelow (Set.range fun n ↦ u n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  have hHu : ∀ n, 0 < n → H n / n = ENNReal.ofReal (u n / n) := fun n hn ↦ by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_toReal (hHfin n),
      ENNReal.ofReal_natCast]
  have hlim : Tendsto (fun n ↦ H n / n) atTop (𝓝 (ENNReal.ofReal hu.lim)) :=
    (ENNReal.tendsto_ofReal (hu.tendsto_lim hbdd)).congr'
      (eventually_atTop.mpr ⟨1, fun n hn ↦ (hHu n hn).symm⟩)
  convert hlim using 2
  refine le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun n hn ↦
    partitionEntropyRate_le_div hn μ T a⟩)) (le_partitionEntropyRate_iff.mpr fun n hn ↦ ?_)
  rw [hHu n hn]
  exact ENNReal.ofReal_le_ofReal (hu.lim_le_div hbdd hn.ne')

end Subadditive

/-- **Periodic maps.** If `T^[p] = id` for some `p ≥ 1` and `T` preserves `μ`, then `T` has
Kolmogorov–Sinai entropy zero under a probability measure (or the zero measure): every itinerary is
a relabeling of the length-`p` one. -/
theorem measureEntropy_eq_zero_of_iterate_eq_id [IsZeroOrProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {p : ℕ} (hp : 0 < p) (hTp : T^[p] = id) :
    measureEntropy μ T = 0 := by
  refine nonpos_iff_eq_zero.mp (measureEntropy_le_iff.mpr fun a ha hfin ↦ ?_)
  set C := countablePartitionEntropy μ (iteratedPartitionLabel T a p)
  have hle : ∀ n, countablePartitionEntropy μ (iteratedPartitionLabel T a n) ≤ C := fun n ↦ by
    have : iteratedPartitionLabel T a n =
        (fun u (k : Fin n) ↦ u ⟨k % p, Nat.mod_lt _ hp⟩) ∘ iteratedPartitionLabel T a p := by
      funext x k
      simp only [Function.comp_apply, iteratedPartitionLabel_apply]
      rw [Function.IsPeriodicPt.iterate_mod_apply (congrFun hTp x)]
    rw [this]
    exact countablePartitionEntropy_comp_le _ _
  have hC : C ≠ ∞ := countablePartitionEntropy_iteratedPartitionLabel_ne_top hT ha hfin p
  have h0 : Tendsto (fun n : ℕ ↦ countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n)
      atTop (𝓝 0) := by
    have hCn : Tendsto (fun n : ℕ ↦ C * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCn
      (fun _ ↦ zero_le) fun n ↦ ?_
    rw [div_eq_mul_inv]
    gcongr
    exact hle n
  exact (tendsto_nhds_unique (tendsto_partitionEntropyRate hT ha) h0).le

end TauCeti
