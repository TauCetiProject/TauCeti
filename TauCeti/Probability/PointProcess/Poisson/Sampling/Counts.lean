/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.PointProcess.Poisson.Finite
import TauCeti.Probability.Distributions.Multinomial.Sampling
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Independent counts in finite Poisson sampling

The law obtained by sampling a Poisson number of independent locations is a Poisson
random measure with intensity equal to the sampling rate times the location law.
Counts on disjoint measurable sets have the product of their Poisson laws, including
zero rates, null sets and repeated locations. No topology on the location space is needed.

The proof assigns a category to each tested set and one further category to its complement,
then uses the Poisson allocation theorem for categorical samples in
`TauCeti.Probability.Distributions.Multinomial.Sampling`. This verifies the independent-count
criterion for the finite-intensity building block of the general Poisson construction.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process* (2018), Theorem 3.6.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

private theorem map_singleton_finitePoissonLaw_categorical {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (r : ℝ≥0) (p : StdSimplex ℝ≥0 ι) :
    (finitePoissonLaw r (categoricalMeasure p)).map (fun ξ i => ξ {i}) =
      (Measure.pi fun i => poissonMeasure (r * p.weights i)).map
        (fun k i => (k i : ℝ≥0∞)) := by
  classical
  have hm : Measurable fun z : ℕ × (ℕ → ι) =>
      ∑ j ∈ Finset.range z.1, Measure.dirac (z.2 j) :=
    measurable_from_prod_countable_right fun n =>
      Finset.measurable_sum (Finset.range n) fun j _ =>
        Measure.measurable_dirac.comp (measurable_pi_apply j)
  have hk : Measurable fun z : ℕ × (ℕ → ι) => fun i =>
      ((Finset.range z.1).filter fun j => z.2 j = i).card := by
    apply measurable_from_prod_countable_right
    intro n
    apply measurable_pi_iff.2
    intro i
    simp_rw [Finset.card_filter]
    exact Finset.measurable_sum _ fun j _ => measurable_const.ite
      (measurableSet_eq_fun (measurable_pi_apply j) measurable_const) measurable_const
  rw [finitePoissonLaw_eq_map_prod_infinitePi,
    Measure.map_map TauCeti.MeasureTheory.measurable_singleton_evals hm,
    ← map_card_filter_prod_poissonMeasure, Measure.map_map (by fun_prop) hk]
  congr 1
  funext z i
  simp only [Function.comp_apply, sum_apply, Measure.dirac_apply' _
    (measurableSet_singleton i), indicator_apply, mem_singleton_iff,
    Pi.one_apply, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem map_eval_preimage_finitePoissonLaw {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
    (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q]
    (c : X → Option ι) (hcm : Measurable c) (p : StdSimplex ℝ≥0 (Option ι))
    (hp : categoricalMeasure p = Q.map c) :
    (finitePoissonLaw r Q).map (fun ξ i => ξ (c ⁻¹' {some i})) =
      Measure.pi (fun i : ι => (poissonMeasure (r * p.weights (some i))).map
        (Nat.cast : ℕ → ℝ≥0∞)) := by
  have hmap := congrArg (fun ν : Measure (Option ι → ℝ≥0∞) =>
    ν.map (fun k i => k (some i))) (map_singleton_finitePoissonLaw_categorical r p)
  rw [hp, ← map_finitePoissonLaw r Q hcm] at hmap
  have hselect : Measurable fun k : Option ι → ℝ≥0∞ => fun i : ι => k (some i) := by
    fun_prop
  rw [Measure.map_map TauCeti.MeasureTheory.measurable_singleton_evals
      (Measure.measurable_map c hcm),
    Measure.map_map hselect
      (TauCeti.MeasureTheory.measurable_singleton_evals.comp
        (Measure.measurable_map c hcm))] at hmap
  simp only [Function.comp_def, Measure.map_apply hcm (measurableSet_singleton _)] at hmap
  rw [hmap]
  have hproj : (Measure.pi fun i => poissonMeasure (r * p.weights i)).map
      (fun k => fun i : ι => k (some i)) =
      Measure.pi fun i : ι => poissonMeasure (r * p.weights (some i)) := by
    exact ((iIndepFun_pi (fun i => (measurable_id (α := ℕ)).aemeasurable)).precomp
      (Option.some_injective ι)).hasLaw_pi
        (fun i => (measurePreserving_eval _ (some i)).hasLaw) |>.map_eq
  calc
    _ = ((Measure.pi fun i => poissonMeasure (r * p.weights i)).map
        (fun k => fun i : ι => k (some i))).map (fun k i => (k i : ℝ≥0∞)) := by
      rw [Measure.map_map hselect (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [hproj]
      exact Measure.pi_map_pi (fun _ : ι =>
        (measurable_of_countable (Nat.cast : ℕ → ℝ≥0∞)).aemeasurable)

/-- The joint counts on a finite disjoint measurable family under finite Poisson sampling
have the product of the corresponding Poisson laws, viewed as extended nonnegative counts.
The sets need not cover the space, and the family may be empty. -/
theorem map_eval_finitePoissonLaw {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A)) :
    (finitePoissonLaw r Q).map (fun ξ i => ξ (A i)) =
      Measure.pi (fun i => (poissonMeasure (r * (Q (A i)).toNNReal)).map
        (Nat.cast : ℕ → ℝ≥0∞)) := by
  classical
  let : MeasurableSpace (Option ι) := ⊤
  -- Add an unused category for locations outside all tested sets.
  let c (x : X) : Option ι := if h : ∃ i, x ∈ A i then some h.choose else none
  have hc (x : X) (i : ι) : c x = some i ↔ x ∈ A i := by
    dsimp [c]
    split_ifs with hx
    · have hmem := hx.choose_spec
      constructor
      · intro he
        simpa only [Option.some.inj he] using hmem
      · intro hi
        congr 1
        by_contra hne
        exact Set.disjoint_left.1 (hd hne) hmem hi
    · simp only [false_iff]
      exact fun hi => hx ⟨i, hi⟩
  have hpre (i : ι) : c ⁻¹' {some i} = A i := Set.ext fun x => hc x i
  have hcm : Measurable c := by
    apply measurable_to_countable'
    intro i
    cases i with
    | some i =>
      rw [hpre]
      exact hA i
    | none =>
      have he : c ⁻¹' {none} = (⋃ i, A i)ᶜ := by
        ext x
        simp [c]
      rw [he]
      exact (MeasurableSet.iUnion hA).compl
  obtain ⟨p, hp⟩ := (Q.map c).exists_categoricalMeasure_eq
  have hweights (i : ι) : p.weights (some i) = (Q (A i)).toNNReal := by
    have hi := congrArg (fun μ : Measure (Option ι) => (μ {some i}).toNNReal) hp
    simpa only [categoricalMeasure_singleton, ENNReal.toNNReal_coe,
      Measure.map_apply hcm (measurableSet_singleton _), hpre] using hi
  simpa only [hpre, hweights] using map_eval_preimage_finitePoissonLaw r Q c hcm p hp

/-- Sampling a Poisson number of independent locations gives a Poisson random measure
with intensity equal to the sampling rate times the location law. -/
theorem isPoissonRandomMeasure_finitePoissonLaw {X : Type*} [MeasurableSpace X]
    (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    IsPoissonRandomMeasure (finitePoissonLaw r Q) id ((r : ℝ≥0∞) • Q) := by
  classical
  refine isPoissonRandomMeasure_iff.mpr ⟨measurable_id, ?_, ?_⟩
  · intro n A hA hd
    have hrate (i : Fin n) : (((r : ℝ≥0∞) • Q) (A i)).toNNReal =
        r * (Q (A i)).toNNReal := by simp
    have hlaw : HasLaw (fun ξ : Measure X => fun i => ξ (A i))
        (Measure.pi fun i => (poissonMeasure (r * (Q (A i)).toNNReal)).map
          (Nat.cast : ℕ → ℝ≥0∞)) (finitePoissonLaw r Q) :=
      ⟨(measurable_pi_iff.2 fun i => Measure.measurable_coe (hA i).1).aemeasurable,
        map_eval_finitePoissonLaw r Q A (fun i => (hA i).1) hd⟩
    have hm (i : Fin n) := (measurePreserving_eval
      (fun i => (poissonMeasure (r * (Q (A i)).toNNReal)).map
        (Nat.cast : ℕ → ℝ≥0∞)) i).hasLaw.comp hlaw
    simp only [hrate]
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi hm).2 hlaw, hm⟩
  · intro A _ htop
    let := Q.smul_finite (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
    exact False.elim (measure_ne_top ((r : ℝ≥0∞) • Q) A htop)

end TauCeti.Probability
