/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.FinitePartition
public import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Trim

/-!
# The Kolmogorov–Sinai theorem for one-sided generators

A measurable countable label `ξ` of finite entropy is a one-sided generator of a measure-preserving
map `T` when the σ-algebras of the labels `ξ ∘ T^[k]`, `k : ℕ`, generate the σ-algebra of `X`
modulo `μ`-null sets. The Kolmogorov–Sinai theorem says that the entropy rate of such a generator
is the Kolmogorov–Sinai entropy: `h_μ(T) = h_μ(T, ξ)`.

The proof approximates every finite label `η` by labels `b` that factor through a finite
itinerary of `ξ`: the probability that `η` and `b` disagree can be made arbitrarily small, and
then so can the conditional entropy `H(η | b)`. The bound `h(T, η) ≤ h(T, b) + H(η | b)` of
`TauCeti.partitionEntropyRate_le_add_conditionalPartitionEntropy`, the bound
`h(T, join_N ξ) ≤ h(T, ξ)` for the itineraries, and the finite-partition formula
`TauCeti.measureEntropy_eq_iSup_fin` then give the theorem.

## Main results

* `TauCeti.exists_measurableSet_measure_symmDiff_lt_of_monotone`: a set measurable for the
  supremum of an increasing sequence of sub-σ-algebras is approximated in measure by sets
  measurable for its members.
* `TauCeti.conditionalPartitionEntropy_le_mismatch`: `H(a | b)` is at most the entropy of the label
  recording where `a` and `b` disagree, together with the value of `a` there.
* `TauCeti.tendsto_countablePartitionEntropy_mismatchLabel`: the entropy of the disagreement label
  tends to zero when the probability of disagreement does.
* `TauCeti.partitionEntropyRate_iteratedPartitionLabel_le`: `h(T, join_N ξ) ≤ h(T, ξ)`.
* `TauCeti.exists_measure_ne_comp_iteratedPartitionLabel_le`: for a one-sided generator `ξ`, every
  measurable finite label agrees, outside a set of small measure, with a label factoring through an
  itinerary of `ξ`.
* `TauCeti.partitionEntropyRate_le_of_generator`: `h(T, η) ≤ h(T, ξ)` for every measurable finite
  label `η` and one-sided generator `ξ`.
* `TauCeti.measureEntropy_eq_partitionEntropyRate_of_generator`: the Kolmogorov–Sinai theorem
  for one-sided generators.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Definition 4.4 and Theorem 4.4, p. 111
  (a one-sided generator there is a strong generator). Entropies there are in base 2; here they
  use natural logarithms.
-/

public section

open MeasureTheory Filter Topology Real
open scoped ENNReal symmDiff

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X} {T : X → X}

/-- A set measurable for the supremum of an increasing sequence of sub-σ-algebras is approximated,
for a finite measure, by sets measurable for a member of the sequence: the symmetric difference has
measure less than any given `ε > 0`. -/
theorem exists_measurableSet_measure_symmDiff_lt_of_monotone [IsFiniteMeasure μ]
    {m : ℕ → MeasurableSpace X} (hm : Monotone m) (hle : ∀ n, m n ≤ mX) {s : Set X}
    (hs : MeasurableSet[⨆ n, m n] s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n t, MeasurableSet[m n] t ∧ μ (t ∆ s) < ε := by
  have hle' : (⨆ n, m n) ≤ mX := iSup_le hle
  set C : Set (Set X) := ⋃ n, {t | MeasurableSet[m n] t}
  have hC : IsSetRing C := by
    refine ⟨Set.mem_iUnion.2 ⟨0, @MeasurableSet.empty X (m 0)⟩, ?_, ?_⟩ <;>
    · intro s t hs ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hs
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 ht
      refine Set.mem_iUnion.2 ⟨max i j, ?_⟩
      have hi' : MeasurableSet[m (max i j)] s := hm (le_max_left i j) _ hi
      have hj' : MeasurableSet[m (max i j)] t := hm (le_max_right i j) _ hj
      first
      | exact hi'.union hj'
      | exact hi'.diff hj'
  have hgen : (⨆ n, m n) = MeasurableSpace.generateFrom C :=
    (MeasurableSpace.generateFrom_iUnion_measurableSet m).symm
  obtain ⟨t, htC, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (mα := ⨆ n, m n) (μ := μ.trim hle') hC ⟨{Set.univ}, Set.countable_singleton _,
      Set.singleton_subset_iff.2 (Set.mem_iUnion.2 ⟨0, @MeasurableSet.univ X (m 0)⟩), by simp⟩
      hgen hs hε
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 htC
  have htm : MeasurableSet[⨆ n, m n] t := (le_iSup m n) _ hn
  refine ⟨n, t, hn, ?_⟩
  rwa [trim_measurableSet_eq hle' (htm.symmDiff hs)] at ht

/-- The label recording where the labels `a` and `b` disagree, and the value of `a` there: it is
`Sum.inr ()` where `a x = b x` and `Sum.inl (a x)` elsewhere. -/
def mismatchLabel [DecidableEq ι] (a b : X → ι) : X → ι ⊕ Unit :=
  fun x ↦ if a x = b x then Sum.inr () else Sum.inl (a x)

/-- Unfolding `mismatchLabel`. -/
theorem mismatchLabel_apply [DecidableEq ι] (a b : X → ι) (x : X) :
    mismatchLabel a b x = if a x = b x then Sum.inr () else Sum.inl (a x) :=
  (rfl)

/-- The disagreement label of measurable countable labels is measurable. -/
theorem measurable_mismatchLabel [DecidableEq ι] [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a b : X → ι} (ha : Measurable a) (hb : Measurable b) :
    Measurable (mismatchLabel a b) :=
  (measurable_of_countable fun p : ι × ι ↦
    if p.1 = p.2 then (Sum.inr () : ι ⊕ Unit) else Sum.inl p.1).comp (ha.prodMk hb)

/-- **Conditional entropy and disagreement.** Under a probability measure (or the zero measure),
for measurable countable labels `a`, `b` into the same type, `H(a | b)` is at most the entropy of
`mismatchLabel a b`: knowing `b` and where `a` differs from `b`, with the value of `a` there,
determines `a`. -/
theorem conditionalPartitionEntropy_le_mismatch [IsZeroOrProbabilityMeasure μ] [DecidableEq ι]
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {a b : X → ι}
    (ha : Measurable a) (hb : Measurable b) :
    conditionalPartitionEntropy μ a b ≤ countablePartitionEntropy μ (mismatchLabel a b) := by
  have : MeasurableSingletonClass (ι ⊕ Unit) := ⟨fun o ↦ by
    rcases o with i | u
    · simpa using (measurableSet_singleton i).inl_image (β := Unit)
    · simpa using (measurableSet_singleton u).inr_image (α := ι)⟩
  have hd := measurable_mismatchLabel ha hb
  have hab : a = (fun p : (ι ⊕ Unit) × ι ↦ p.1.elim id fun _ ↦ p.2) ∘
      fun x ↦ (mismatchLabel a b x, b x) := by
    funext x
    by_cases h : a x = b x <;> simp [mismatchLabel_apply, h]
  calc conditionalPartitionEntropy μ a b
      ≤ conditionalPartitionEntropy μ (fun x ↦ (mismatchLabel a b x, b x)) b := by
        conv_lhs => rw [hab]
        exact conditionalPartitionEntropy_comp_le _ _ hb
    _ ≤ conditionalPartitionEntropy μ (mismatchLabel a b) b +
          conditionalPartitionEntropy μ b b :=
        conditionalPartitionEntropy_pair_left_le_add hd hb hb
    _ ≤ countablePartitionEntropy μ (mismatchLabel a b) := by
        rw [conditionalPartitionEntropy_self, add_zero]
        exact conditionalPartitionEntropy_le _ hb

/-- If measurable labels `b n` into a finite type agree with the measurable label `a` outside
sets of probabilities tending to zero, the entropies of the disagreement labels
`mismatchLabel a (b n)` tend to zero. -/
theorem tendsto_countablePartitionEntropy_mismatchLabel [IsProbabilityMeasure μ] [DecidableEq ι]
    [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {a : X → ι} {b : ℕ → X → ι}
    (ha : Measurable a) (hb : ∀ n, Measurable (b n))
    (h : Tendsto (fun n ↦ μ.real {x | a x ≠ b n x}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ countablePartitionEntropy μ (mismatchLabel a (b n))) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  simp only [countablePartitionEntropy_def, tsum_fintype]
  rw [show (0 : ℝ≥0∞) = ∑ _ : ι ⊕ Unit, ENNReal.ofReal (negMulLog 0) by simp]
  refine tendsto_finsetSum _ fun o _ ↦ ?_
  rcases o with i | u
  · -- The atom `Sum.inl i` lies in the disagreement set.
    refine ENNReal.tendsto_ofReal ((continuous_negMulLog.tendsto 0).comp ?_)
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ measureReal_mono ?_) h
    intro x hx
    simp only [Set.mem_preimage, mismatchLabel_apply, Set.mem_singleton_iff] at hx
    split_ifs at hx with hax
    exact hax
  · -- The atom `Sum.inr ()` is the agreement set, of probability tending to one.
    rw [show negMulLog 0 = negMulLog 1 by simp]
    refine ENNReal.tendsto_ofReal ((continuous_negMulLog.tendsto 1).comp ?_)
    have hreal (n : ℕ) : μ.real (mismatchLabel a (b n) ⁻¹' {Sum.inr u}) =
        1 - μ.real {x | a x ≠ b n x} := by
      have hset : mismatchLabel a (b n) ⁻¹' {Sum.inr u} = {x | a x ≠ b n x}ᶜ := by
        ext x
        by_cases hx : a x = b n x <;> simp [mismatchLabel_apply, hx]
      have hmeas : MeasurableSet {x | a x ≠ b n x} :=
        (ha.prodMk (hb n)) (Set.to_countable {p : ι × ι | p.1 ≠ p.2}).measurableSet
      rw [hset, measureReal_compl hmeas, probReal_univ]
    simp only [hreal]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- The length-`n` itinerary of the length-`N` itinerary of `a` is read off the length-`(n + N)`
itinerary of `a`. -/
theorem iteratedPartitionLabel_iteratedPartitionLabel (T : X → X) (a : X → ι) (N n : ℕ) :
    iteratedPartitionLabel T (iteratedPartitionLabel T a N) n =
      (fun w (j : Fin n) (i : Fin N) ↦ w ⟨j + i, Nat.add_lt_add j.isLt i.isLt⟩) ∘
        iteratedPartitionLabel T a (n + N) := by
  funext x j i
  simp only [iteratedPartitionLabel_apply, Function.comp_apply]
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-- For a measure-preserving map of a probability space (or the zero measure) and a measurable
countable label `a`, the entropy rate of a finite itinerary of `a` is at most that of `a`:
`h(T, join_N a) ≤ h(T, a)`. -/
theorem partitionEntropyRate_iteratedPartitionLabel_le [IsZeroOrProbabilityMeasure μ]
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (hT : MeasurePreserving T μ μ)
    {a : X → ι} (ha : Measurable a) (N : ℕ) :
    partitionEntropyRate μ T (iteratedPartitionLabel T a N) ≤ partitionEntropyRate μ T a := by
  rcases eq_or_ne (countablePartitionEntropy μ a) ∞ with htop | hfin
  · -- Every itinerary of `a` has infinite entropy, so the rate of `a` is `∞`.
    refine le_of_le_of_eq le_top ?_
    rw [partitionEntropyRate_def, eq_comm, iInf_eq_top]
    intro n
    have := countablePartitionEntropy_le_iteratedPartitionLabel (μ := μ) T a n.succ_pos
    rw [htop, top_le_iff] at this
    exact ENNReal.div_eq_top.2 (Or.inr ⟨this, by simp⟩)
  set C := countablePartitionEntropy μ (iteratedPartitionLabel T a N)
  have hC : C ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hfin)
    (countablePartitionEntropy_iteratedPartitionLabel_le_mul hT ha N)
  have hlim : Tendsto (fun n : ℕ ↦
      countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n + C / n) atTop
        (𝓝 (partitionEntropyRate μ T a + 0)) := by
    refine (tendsto_partitionEntropyRate hT ha).add ?_
    simp only [div_eq_mul_inv]
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  refine (partitionEntropyRate_le_div hn μ T _).trans ?_
  rw [← ENNReal.add_div]
  refine ENNReal.div_le_div_right ?_ _
  rw [iteratedPartitionLabel_iteratedPartitionLabel]
  exact (countablePartitionEntropy_comp_le _ _).trans
    (countablePartitionEntropy_iteratedPartitionLabel_add_le hT ha n N)

/-- A shorter itinerary is a restriction of a longer one. -/
theorem iteratedPartitionLabel_eq_comp_of_le (T : X → X) (a : X → ι) {N N' : ℕ} (h : N ≤ N') :
    iteratedPartitionLabel T a N =
      (fun w i ↦ w (Fin.castLE h i)) ∘ iteratedPartitionLabel T a N' := by
  funext x i
  simp [iteratedPartitionLabel_apply]

/-- The σ-algebras generated by the itineraries of a label increase with the length. -/
theorem monotone_comap_iteratedPartitionLabel [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (T : X → X) (a : X → ι) :
    Monotone fun N ↦ MeasurableSpace.comap (iteratedPartitionLabel T a N) inferInstance :=
  fun N N' h ↦ by
    simp only
    rw [iteratedPartitionLabel_eq_comp_of_le T a h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_countable _).comap_le

/-- The σ-algebra generated by the shifted labels `a ∘ T^[k]` is contained in the supremum of the
σ-algebras generated by the itineraries of `a`. -/
theorem iSup_comap_iterate_le_iSup_comap_iteratedPartitionLabel [MeasurableSpace ι]
    (T : X → X) (a : X → ι) :
    (⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ a (T^[k] x)) ‹MeasurableSpace ι›) ≤
      ⨆ N, MeasurableSpace.comap (iteratedPartitionLabel T a N) inferInstance := by
  refine iSup_le fun k ↦ le_iSup_of_le (k + 1) ?_
  have : (fun x ↦ a (T^[k] x)) =
      (fun w : Fin (k + 1) → ι ↦ w (Fin.last k)) ∘ iteratedPartitionLabel T a (k + 1) := by
    funext x
    simp [iteratedPartitionLabel_apply]
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- **Approximation through itineraries.** Let `ξ` be a measurable countable label whose shifted
labels `ξ ∘ T^[k]` generate the σ-algebra of `X` modulo `μ`-null sets. Every measurable label `η`
into a finite type is approximated by labels factoring through an itinerary of `ξ`: for `ε > 0`
there are `N` and `g` with `μ {η ≠ g ∘ join_N ξ} ≤ card κ * ε`. -/
theorem exists_measure_ne_comp_iteratedPartitionLabel_le [IsFiniteMeasure μ] (hT : Measurable T)
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {ξ : X → ι} (hξ : Measurable ξ)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (T^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t)
    [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {η : X → κ}
    (hη : Measurable η) (κ₀ : κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : ℕ) (g : (Fin N → ι) → κ),
      μ {x | η x ≠ g (iteratedPartitionLabel T ξ N x)} ≤ Fintype.card κ * ε := by
  classical
  have hle (N : ℕ) : MeasurableSpace.comap (iteratedPartitionLabel T ξ N) inferInstance ≤ mX :=
    (measurable_iteratedPartitionLabel hT hξ N).comap_le
  -- Approximate each atom of `η` by a set measurable for some itinerary.
  have happrox (i : κ) : ∃ N, ∃ S : Set (Fin N → ι),
      μ ((iteratedPartitionLabel T ξ N ⁻¹' S) ∆ (η ⁻¹' {i})) < ε := by
    obtain ⟨t, ht, hst⟩ := hgen _ (hη (measurableSet_singleton i))
    obtain ⟨N, t', ⟨S, -, rfl⟩, hlt⟩ :=
      exists_measurableSet_measure_symmDiff_lt_of_monotone (μ := μ)
        (monotone_comap_iteratedPartitionLabel T ξ) hle
        (iSup_comap_iterate_le_iSup_comap_iteratedPartitionLabel T ξ _ ht) hε
    exact ⟨N, S, by rwa [measure_congr (ae_eq_set_symmDiff (EventuallyEqSet.refl _ _) hst)]⟩
  choose Ni S hS using happrox
  set N := Finset.univ.sup Ni
  have hNi (i : κ) : Ni i ≤ N := Finset.le_sup (Finset.mem_univ i)
  set S' : κ → Set (Fin N → ι) := fun i ↦ (fun w j ↦ w (Fin.castLE (hNi i) j)) ⁻¹' S i
  have hS' (i : κ) :
      iteratedPartitionLabel T ξ N ⁻¹' S' i = iteratedPartitionLabel T ξ (Ni i) ⁻¹' S i := by
    simp only [S', ← Set.preimage_comp]
    rw [← iteratedPartitionLabel_eq_comp_of_le T ξ (hNi i)]
  set g : (Fin N → ι) → κ := fun w ↦ if h : ∃ i, w ∈ S' i then h.choose else κ₀
  refine ⟨N, g, ?_⟩
  have hsub : {x | η x ≠ g (iteratedPartitionLabel T ξ N x)} ⊆
      ⋃ i, (iteratedPartitionLabel T ξ N ⁻¹' S' i) ∆ (η ⁻¹' {i}) := by
    intro x hx
    simp only [Set.mem_ofPred_eq, g] at hx
    split_ifs at hx with h
    · refine Set.mem_iUnion.2 ⟨h.choose, Or.inl ⟨h.choose_spec, ?_⟩⟩
      simpa [eq_comm] using hx
    · refine Set.mem_iUnion.2 ⟨η x, Or.inr ⟨rfl, fun hmem ↦ h ⟨η x, hmem⟩⟩⟩
  calc μ {x | η x ≠ g (iteratedPartitionLabel T ξ N x)}
      ≤ ∑ i, μ ((iteratedPartitionLabel T ξ N ⁻¹' S' i) ∆ (η ⁻¹' {i})) :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le μ _)
    _ ≤ ∑ _i : κ, ε := Finset.sum_le_sum fun i _ ↦ by rw [hS']; exact (hS i).le
    _ = Fintype.card κ * ε := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The entropy rate of a measurable finite label is at most that of a one-sided generator. -/
theorem partitionEntropyRate_le_of_generator [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ξ : X → ι} (hξ : Measurable ξ)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (T^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t)
    [Finite κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {η : X → κ}
    (hη : Measurable η) :
    partitionEntropyRate μ T η ≤ partitionEntropyRate μ T ξ := by
  classical
  have := Fintype.ofFinite κ
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hε (k : ℕ) : (0 : ℝ≥0∞) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  choose N g hg using fun k : ℕ ↦
    exists_measure_ne_comp_iteratedPartitionLabel_le hT.measurable hξ hgen hη (η x₀) (hε k)
  set b : ℕ → X → κ := fun k ↦ g k ∘ iteratedPartitionLabel T ξ (N k)
  have hζ (k : ℕ) := measurable_iteratedPartitionLabel hT.measurable hξ (N k)
  have hb (k : ℕ) : Measurable (b k) := (measurable_of_countable _).comp (hζ k)
  have hsmall : Tendsto (fun k ↦ μ.real {x | η x ≠ b k x}) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun k ↦ ?_)
      ((tendsto_const_div_atTop_nhds_zero_nat (Fintype.card κ : ℝ)).comp
        (tendsto_add_atTop_nat 1))
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.2 (by positivity))) (hg k)
    simpa [measureReal_def, b, div_eq_mul_inv, ENNReal.toReal_add] using this
  have hkey (k : ℕ) : partitionEntropyRate μ T η ≤
      partitionEntropyRate μ T ξ + countablePartitionEntropy μ (mismatchLabel η (b k)) :=
    calc partitionEntropyRate μ T η
        ≤ partitionEntropyRate μ T (iteratedPartitionLabel T ξ (N k)) +
            conditionalPartitionEntropy μ η (iteratedPartitionLabel T ξ (N k)) :=
          partitionEntropyRate_le_add_conditionalPartitionEntropy hT hη (hζ k)
      _ ≤ partitionEntropyRate μ T ξ + conditionalPartitionEntropy μ η (b k) :=
          add_le_add (partitionEntropyRate_iteratedPartitionLabel_le hT hξ _)
            (conditionalPartitionEntropy_le_comp _ (hζ k) _)
      _ ≤ _ := add_le_add le_rfl (conditionalPartitionEntropy_le_mismatch hη (hb k))
  have hlim := (tendsto_const_nhds (x := partitionEntropyRate μ T ξ)).add
    (tendsto_countablePartitionEntropy_mismatchLabel hη hb hsmall)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hkey

/-- **The Kolmogorov–Sinai theorem.** Let `T` preserve a probability measure `μ`, and let `ξ` be a
measurable countable label of finite entropy that is a one-sided generator: the σ-algebras of the
labels `ξ ∘ T^[k]`, `k : ℕ`, generate the σ-algebra of `X` modulo `μ`-null sets. Then the
Kolmogorov–Sinai entropy is the entropy rate of `ξ` (Sarig 2023, Theorem 4.4). -/
theorem measureEntropy_eq_partitionEntropyRate_of_generator [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ξ : X → ι} (hξ : Measurable ξ) (hH : countablePartitionEntropy μ ξ ≠ ∞)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (T^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t) :
    measureEntropy μ T = partitionEntropyRate μ T ξ := by
  refine le_antisymm ?_ (partitionEntropyRate_le_measureEntropy_of_countable T hξ hH)
  rw [measureEntropy_eq_iSup_fin hT]
  exact iSup₂_le fun n η ↦ iSup_le fun hη ↦ partitionEntropyRate_le_of_generator hT hξ hgen hη

end TauCeti
