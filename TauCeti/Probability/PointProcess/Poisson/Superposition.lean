/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.Sum
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.Floor

/-!
# Finite independent superposition of Poisson random measures

Adding independent Poisson random measures adds their intensity measures. Independence of
counts on disjoint sets is preserved, not merely the individual Poisson count laws.
The result holds on arbitrary measurable spaces, permits atomic intensities and multiple
occurrences, and includes the empty family. Counts on sets of infinite intensity remain
almost surely infinite.

The proof uses the finite Poisson allocation law from
`TauCeti.Probability.Distributions.Poisson.Sum`: flatten the independent array indexed by
components and disjoint test sets, then aggregate over the component index.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.3 (superposition).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : ι → Ω → Measure X} {Λ : ι → Measure X}

/-- On a set of finite intensity, converting a Poisson count to a natural number recovers
its native Poisson law, and casting back agrees almost surely with the original count. -/
private theorem poisson_count_floor_toNNReal {M : Ω → Measure X} {ν : Measure X}
    (h : IsPoissonRandomMeasure P M ν) {A : Set X} (hA : MeasurableSet A)
    (hfin : ν A < ∞) :
    HasLaw (fun ω => ⌊(M ω A).toNNReal⌋₊) (poissonMeasure (ν A).toNNReal) P ∧
      ∀ᵐ ω ∂P, (⌊(M ω A).toNNReal⌋₊ : ℝ≥0∞) = M ω A := by
  have hlaw := h.hasLaw hA hfin
  have hm : Measurable (fun x : ℝ≥0∞ => ⌊x.toNNReal⌋₊) :=
    Nat.measurable_floor.comp ENNReal.measurable_toNNReal
  constructor
  · simpa [Measure.map_map hm Measurable.of_discrete, Function.comp_def] using
      (hasLaw_map hm.aemeasurable).comp hlaw
  · have hs : MeasurableSet {x : ℝ≥0∞ | (⌊x.toNNReal⌋₊ : ℝ≥0∞) = x} :=
      measurableSet_eq_fun (Measurable.of_discrete.comp hm) measurable_id
    apply (ae_map_iff hlaw.aemeasurable hs).mp
    rw [hlaw.map_eq]
    exact (ae_map_iff Measurable.of_discrete.aemeasurable hs).mpr
      (ae_of_all _ fun k => by simp)

/-- The joint count law of a finite independent superposition, on a finite disjoint
family of measurable sets of finite total intensity. -/
private theorem hasLaw_sum_counts [Fintype ι]
    (hind : iIndepFun N P) (h : ∀ i, IsPoissonRandomMeasure P (N i) (Λ i))
    {n : ℕ} {A : Fin n → Set X} (hA : ∀ j, MeasurableSet (A j))
    (hfin : ∀ j, (∑ i, Λ i) (A j) < ∞) (hdisj : Pairwise (Disjoint on A)) :
    HasLaw (fun ω j => (∑ i, N i ω) (A j))
      (Measure.pi fun j =>
        (poissonMeasure (((∑ i, Λ i) (A j)).toNNReal)).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  classical
  have hfi (i : ι) (j : Fin n) : Λ i (A j) < ∞ := by
    have hj := hfin j
    rw [sum_apply] at hj
    exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans_lt hj
  let Z (i : ι) (j : Fin n) (ω : Ω) := ⌊(N i ω (A j)).toNNReal⌋₊
  let r (p : ι × Fin n) := (Λ p.1 (A p.2)).toNNReal
  have hm (i : ι) (j : Fin n) : Measurable (Z i j) :=
    Nat.measurable_floor.comp (ENNReal.measurable_toNNReal.comp
      ((Measure.measurable_coe (hA j)).comp (h i).measurable))
  have hrows : iIndepFun (fun i ω j => Z i j ω) P :=
    hind.comp (fun _ M j => ⌊(M (A j)).toNNReal⌋₊)
      (fun _ => measurable_pi_iff.mpr fun j =>
        Nat.measurable_floor.comp (ENNReal.measurable_toNNReal.comp
          (Measure.measurable_coe (hA j))))
  have hall := iIndepFun_uncurry' hm hrows (fun i =>
    ((h i).iIndepFun hA (hfi i) hdisj).comp (fun _ x => ⌊x.toNNReal⌋₊)
      (fun _ => Nat.measurable_floor.comp ENNReal.measurable_toNNReal))
  have hlaw : HasLaw (fun ω (p : ι × Fin n) => Z p.1 p.2 ω)
      (Measure.pi fun p => poissonMeasure (r p)) P :=
    iIndepFun.hasLaw_pi (fun p => (poisson_count_floor_toNNReal (h p.1) (hA p.2)
      (hfi p.1 p.2)).1) hall
  have hsum := (hasLaw_map (X := FunOnFinite.map (M := ℕ) (Prod.snd : ι × Fin n → Fin n))
    Measurable.of_discrete.aemeasurable).comp hlaw
  rw [map_funOnFinite_map_pi_poissonMeasure] at hsum
  have hrate (j : Fin n) : (∑ p : ι × Fin n with p.2 = j, r p) =
      ((∑ i, Λ i) (A j)).toNNReal := by
    rw [sum_apply, ENNReal.toNNReal_sum (fun i _ => (hfi i j).ne)]
    simp [r, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [hrate] at hsum
  have hcast := (hasLaw_map (X := fun k : Fin n → ℕ => fun j => (k j : ℝ≥0∞))
    Measurable.of_discrete.aemeasurable).comp hsum
  rw [Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable)] at hcast
  apply hcast.congr
  have hae : ∀ᵐ ω ∂P, ∀ i j, (⌊(N i ω (A j)).toNNReal⌋₊ : ℝ≥0∞) = N i ω (A j) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      (poisson_count_floor_toNNReal (h i) (hA j) (hfi i j)).2
  filter_upwards [hae] with ω hω
  ext j
  simp [FunOnFinite.map_apply_apply, Finset.sum_filter, Fintype.sum_prod_type, Z, sum_apply, hω]

/-- Superposition over a finite type; the finset form below also permits independence and
Poisson assumptions restricted to the selected components. -/
private theorem poisson_fintype_sum [Fintype ι]
    (hind : iIndepFun N P) (h : ∀ i, IsPoissonRandomMeasure P (N i) (Λ i)) :
    IsPoissonRandomMeasure P (fun ω => ∑ i, N i ω) (∑ i, Λ i) := by
  have := hind.isProbabilityMeasure
  classical
  refine isPoissonRandomMeasure_iff.mpr ⟨Finset.measurable_sum _ (fun i _ =>
    (h i).measurable), ?_, ?_⟩
  · intro n A hA hd
    have hlaw := hasLaw_sum_counts hind h (fun j => (hA j).1) (fun j => (hA j).2) hd
    have hmarg (j : Fin n) := (measurePreserving_eval _ j).hasLaw.comp hlaw
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi hmarg).mpr hlaw, hmarg⟩
  · intro A hA htop
    have hex : ∃ i, Λ i A = ∞ := by
      contrapose! htop
      simpa only [sum_apply] using ENNReal.sum_ne_top.mpr (fun i _ => htop i)
    obtain ⟨i, hi⟩ := hex
    filter_upwards [(h i).ae_eq_top hA hi] with ω hω
    have hle : N i ω A ≤ (∑ k, N k ω) A := by
      rw [sum_apply]
      exact Finset.single_le_sum (f := fun k => N k ω A) (fun _ _ => bot_le)
        (Finset.mem_univ i)
    exact top_unique (hω ▸ hle)

/-- A finite superposition of independent Poisson random measures is Poisson with the sum
of their intensities. Only the selected components need be independent or Poisson.
Atomic and infinite intensities, zero components and the empty family are allowed.
No topology, simplicity or local finiteness assumption is required. -/
theorem isPoissonRandomMeasure_finsetSum {s : Finset ι}
    (h : ∀ i ∈ s, IsPoissonRandomMeasure P (N i) (Λ i))
    (hind : iIndepFun (fun i : s => N i) P) :
    IsPoissonRandomMeasure P (fun ω => ∑ i ∈ s, N i ω) (∑ i ∈ s, Λ i) := by
  have hs := poisson_fintype_sum hind (fun i : s => h i i.property)
  have he (ω : Ω) : (∑ i : s, N i ω) = ∑ i ∈ s, N i ω :=
    Finset.sum_coe_sort s (fun i => N i ω)
  rwa [funext he, Finset.sum_coe_sort] at hs

end TauCeti.Probability
