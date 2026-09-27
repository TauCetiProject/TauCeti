/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Sampling
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.HomDensity
public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.CutDistance
public import TauCeti.Combinatorics.DenseGraphLimits.Separation.Forward

/-!
# Inverse counting: homomorphism densities separate graphons

Two graphons with the same homomorphism density for every finite graph are at cut distance zero.
Together with the forward direction
`TauCeti.DenseGraphLimits.forall_homDensity_eq_of_cutDist_eq_zero` this is the separation
theorem: the cut distance vanishes exactly when all homomorphism densities agree, and the
homomorphism densities are a complete set of coordinates on graphon space.

The graphons may live on different probability spaces, and no standard-Borel or atomlessness
hypothesis is needed on either carrier.

The inverse direction rests on the second sampling lemma
`TauCeti.DenseGraphLimits.sampleGraph_cutDist_tendsto_inProbability`: the homomorphism densities
determine the sampling laws (`TauCeti.DenseGraphLimits.sampleGraph_eq_of_forall_homDensity_eq`),
and the sampling laws determine the graphon up to cut distance.

## Main results

* `TauCeti.DenseGraphLimits.cutDist_eq_zero_of_forall_homDensity_eq` — graphons with the same
  homomorphism densities are at cut distance zero (the inverse counting lemma);
* `TauCeti.DenseGraphLimits.cutDist_eq_zero_iff_forall_homDensity_eq` — the separation theorem;
* `TauCeti.DenseGraphLimits.graphonSpace_ext_iff_homDensity` — points of graphon space are equal
  exactly when all their homomorphism densities agree.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Theorem 11.3 and Lemma 10.16.
* C. Borgs, J. Chayes, L. Lovász, V. Sós, K. Vesztergombi, *Convergent sequences of dense graphs
  I: Subgraph frequencies, metric properties and testing*, Adv. Math. 219 (2008), 1801–1851,
  Theorem 3.8.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Theorem 8.10.
-/

public section

noncomputable section

open Filter MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

section CrossCarrier

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- Two graphons with the same sampling laws have a common finite graph within `ε` of both in cut
distance. This is the bridge from sampling laws to cut distance behind
`TauCeti.DenseGraphLimits.cutDist_eq_zero_of_forall_homDensity_eq`. -/
private theorem exists_cutDist_finiteGraphGraphon_lt (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : ∀ n, sampleGraph U n = sampleGraph W n) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      cutDist (finiteGraphGraphon G) U < ε ∧ cutDist (finiteGraphGraphon G) W < ε := by
  have hU := (tendsto_order.1 (sampleGraph_cutDist_tendsto_inProbability U hε)).2 (1 / 2)
    (by norm_num)
  have hW := (tendsto_order.1 (sampleGraph_cutDist_tendsto_inProbability W hε)).2 (1 / 2)
    (by norm_num)
  obtain ⟨n, hUn, hWn⟩ := (hU.and hW).exists
  rw [h n] at hUn
  have hne : {G : SimpleGraph (Fin n) | ε ≤ cutDist (finiteGraphGraphon G) U} ∪
      {G | ε ≤ cutDist (finiteGraphGraphon G) W} ≠ Set.univ := by
    intro heq
    have := measureReal_union_le (μ := sampleGraph W n)
      {G : SimpleGraph (Fin n) | ε ≤ cutDist (finiteGraphGraphon G) U}
      {G | ε ≤ cutDist (finiteGraphGraphon G) W}
    rw [heq, probReal_univ] at this
    linarith
  obtain ⟨G, hG⟩ := Set.nonempty_compl.2 hne
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hG
  exact ⟨n, G, hG⟩

/-- **The inverse counting lemma.** Two graphons, on arbitrary probability carriers, with the same
homomorphism density for every finite graph are at cut distance zero. The graphons need not share
a carrier, and no standard-Borel or atomlessness hypothesis is needed on either carrier. -/
theorem cutDist_eq_zero_of_forall_homDensity_eq (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (h : ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensity F U = homDensity F W) :
    cutDist U W = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (cutDist_nonneg U W)
  obtain ⟨n, G, hGU, hGW⟩ := exists_cutDist_finiteGraphGraphon_lt U W
    (fun n => sampleGraph_eq_of_forall_homDensity_eq U W n (h n)) (half_pos hε)
  calc cutDist U W
      ≤ cutDist U (finiteGraphGraphon G) + cutDist (finiteGraphGraphon G) W :=
        cutDist_triangle U (finiteGraphGraphon G) W
    _ = cutDist (finiteGraphGraphon G) U + cutDist (finiteGraphGraphon G) W := by
        rw [cutDist_comm U]
    _ ≤ 0 + ε := by linarith

/-- **Separation of graphons by homomorphism densities.** Two graphons, on arbitrary probability
carriers, are at cut distance zero if and only if every finite graph has the same homomorphism
density in them. -/
theorem cutDist_eq_zero_iff_forall_homDensity_eq (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) :
    cutDist U W = 0 ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        homDensity F U = homDensity F W :=
  ⟨forall_homDensity_eq_of_cutDist_eq_zero U W, cutDist_eq_zero_of_forall_homDensity_eq U W⟩

end CrossCarrier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Separation on graphon space.** Two points of graphon space are equal if and only if every
finite graph has the same homomorphism density at them: the homomorphism densities are a complete
set of coordinates on graphon space. -/
theorem graphonSpace_ext_iff_homDensity (U W : GraphonSpace Ω μ) :
    U = W ↔ ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      homDensityOnSpace F U = homDensityOnSpace F W := by
  obtain ⟨U, rfl⟩ := SeparationQuotient.surjective_mk U
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk W
  simp only [graphonSpace_mk_eq_mk_iff, homDensityOnSpace_mk]
  exact cutDist_eq_zero_iff_forall_homDensity_eq U W

end DenseGraphLimits

end TauCeti
