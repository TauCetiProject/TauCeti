/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Eval
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The subspace topology on the rational points of a closed polydisc

Let `K` be a complete ultrametric normed field and `D = closedPolydisc k K` the closed unit
polydisc `Spa (K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)`. Given a point `x ∈ Spa (K, K°)`, each tuple
`a ∈ (K°)ᵏ` determines the classical evaluation point `classicalPoint x a ha ∈ D`.

Using the evaluation continuity proved in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Eval`,
the classical-point map `a ↦ classicalPoint x a ha` is continuous for every complete ultrametric
normed field `K`. Although the basic opens of `Spv K⟨T⟩` cut out weak inequalities
`‖f(a)‖ ≤ ‖g(a)‖ ≠ 0`, the ultrametric inequality preserves them on a neighbourhood where `g`
varies by less than `‖g(a₀)‖` and `f` varies by less than `‖g(a₀)‖`, so preimages of basic opens
are open in `(K°)ᵏ`.

Conversely, for any nonzero scalar `c ∈ K` and any centre `a₀ ∈ (K°)ᵏ`, the rational subset
`R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)` pulls back along the classical-point map to the metric closed
ball of radius `‖c‖` about `a₀`. When `K` is nontrivially normed, such balls form a neighbourhood
basis in `(K°)ᵏ`, so the classical-point map is a topological embedding and induces a homeomorphism
from `(K°)ᵏ` onto the subspace `D(K)` of `K`-rational points. (Over a trivially normed infinite
field the subspace topology on `D(K)` is strictly coarser than the discrete topology of `Kᵏ`.)

Since `(K°)ᵏ` is the closed unit ball in the complete finite product `Kᵏ`, it is complete as a
metric space. Transporting along the homeomorphism shows that `D(K)` is completely metrizable and
hence a Baire space.

## Main definitions

* `TauCeti.ValuationSpectrum.classicalPointRangeHomeomorph`: for a complete nontrivially normed
  ultrametric field `K`, the homeomorphism from `{a : Fin k → K // ∀ i, IsPowerBounded (a i)}`
  onto the subspace of `K`-rational classical points of `closedPolydisc k K`.

## Main results

* `TauCeti.ValuationSpectrum.continuous_classicalPoint`: the classical-point map
  `(K°)ᵏ → closedPolydisc k K` is continuous.
* `TauCeti.ValuationSpectrum.preimage_rationalSubset_classicalPoint_closedBall`: the preimage of
  `R({Tᵢ - a₀,ᵢ} / c)` under the classical-point map is the closed metric ball of radius `‖c‖`
  about `a₀`.
* `TauCeti.ValuationSpectrum.isEmbedding_classicalPoint`: over a complete nontrivially normed
  ultrametric field, the classical-point map is a topological embedding.
* `TauCeti.ValuationSpectrum.isCompletelyMetrizableSpace_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.baireSpace_range_classicalPoint`: the subspace of `K`-rational points
  of `closedPolydisc k K` is completely metrizable and a Baire space.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5, p. 60.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open Filter Topology TauCeti.Huber
open scoped Topology

section NormedField

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Membership of a classical point in a basic open `Spv(K⟨T⟩)(f/g)` reduces to comparing norms
of evaluations: `‖f(a)‖ ≤ ‖g(a)‖` and `0 < ‖g(a)‖`. -/
theorem classicalPoint_mem_basicOpen_iff (x : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (classicalPoint x a ha).val ∈ basicOpen f g ↔
      ‖evalAtHom a ha f‖ ≤ ‖evalAtHom a ha g‖ ∧ 0 < ‖evalAtHom a ha g‖ := by
  rw [mem_basicOpen_iff, classicalPoint_vle, classicalPoint_vle, map_zero,
    vle_iff_norm_le_of_mem_spa x.property, vle_iff_norm_le_of_mem_spa x.property, norm_zero,
    not_le]

/-- **Continuity of the classical-point map `(K°)ᵏ → closedPolydisc k K`.** Every basic open
`Spv(K⟨T⟩)(f/g)` pulls back to `{a | ‖f(a)‖ ≤ ‖g(a)‖ ∧ 0 < ‖g(a)‖}`. By continuity of evaluation
and the ultrametric inequality, if `a₀` satisfies these conditions then they persist on the open
neighbourhood where `f` and `g` each vary by strictly less than `‖g(a₀)‖`. -/
theorem continuous_classicalPoint (x : spa (powerBoundedSubring K)) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property := by
  refine continuous_induced_rng.mpr ?_
  rw [instTopologicalSpace_eq_generateFrom, continuous_generateFrom_iff]
  rintro _ ⟨f, g, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro a₀ ha₀
  rw [Set.mem_preimage, Function.comp_apply, classicalPoint_mem_basicOpen_iff] at ha₀
  obtain ⟨hfg, hgpos⟩ := ha₀
  set r : ℝ := ‖evalAtHom a₀.val a₀.property g‖
  have hopen : IsOpen ({a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} |
        ‖evalAtHom a.val a.property f - evalAtHom a₀.val a₀.property f‖ < r} ∩
      {a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} |
        ‖evalAtHom a.val a.property g - evalAtHom a₀.val a₀.property g‖ < r}) :=
    (isOpen_lt ((continuous_evalAtHom_arg f).sub continuous_const).norm continuous_const).inter
      (isOpen_lt ((continuous_evalAtHom_arg g).sub continuous_const).norm continuous_const)
  refine mem_nhds_iff.mpr ⟨_, fun a ha ↦ ?_, hopen, by simp [hgpos]⟩
  obtain ⟨hf_lt, hg_lt⟩ := ha
  have hga : ‖evalAtHom a.val a.property g‖ = r := by
    rw [← sub_add_cancel (evalAtHom a.val a.property g) (evalAtHom a₀.val a₀.property g),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hg_lt.ne, max_eq_right hg_lt.le]
  have hfa : ‖evalAtHom a.val a.property f‖ ≤ r := by
    rw [← sub_add_cancel (evalAtHom a.val a.property f) (evalAtHom a₀.val a₀.property f)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hf_lt.le hfg)
  rw [Set.mem_preimage, Function.comp_apply, classicalPoint_mem_basicOpen_iff, hga]
  exact ⟨hfa, hgpos⟩

open scoped Classical in
/-- **Rational balls pull back to metric closed balls on `(K°)ᵏ`.** For any centre `a₀ ∈ (K°)ᵏ`
and any nonzero `c ∈ K`, the preimage of the rational subset `R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)`
under the classical-point map is the closed ball of radius `‖c‖` about `a₀`. -/
theorem preimage_rationalSubset_classicalPoint_closedBall (x : spa (powerBoundedSubring K))
    (a₀ : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) {c : K} (hc : c ≠ 0) :
    (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) ⁻¹'
      (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
        (Finset.univ.image fun i : Fin k ↦
          weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
            weightedC _ isWeightFamily_one_weight (a₀.val i))
        (weightedC _ isWeightFamily_one_weight c)) =
      Metric.closedBall a₀ ‖c‖ := by
  ext a
  simp only [Set.mem_preimage, mem_rationalSubset_iff, ← closedPolydisc_def,
    (classicalPoint x a.val a.property).property, true_and, Finset.mem_image, Finset.mem_univ,
    true_and, forall_exists_index, forall_apply_eq_imp_iff, classicalPoint_vle, map_sub, map_zero,
    evalAtHom_weightedX, evalAtHom_weightedC, vle_iff_norm_le_of_mem_spa x.property, norm_zero,
    not_le, norm_pos_iff.mpr hc, and_true, Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm,
    pi_norm_le_iff_of_nonneg (norm_nonneg c), Pi.sub_apply]

end NormedField

section NontriviallyNormedField

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The classical-point map `(K°)ᵏ → closedPolydisc k K` is a topological embedding.**
Continuity holds by `continuous_classicalPoint`, injectivity by
`classicalPoint_injective_of_isField`, and metric closed balls of arbitrarily small positive radius
`‖c‖` arise as preimages of rational subsets `R({Tᵢ - a₀,ᵢ} / c)`. -/
theorem isEmbedding_classicalPoint (x : spa (powerBoundedSubring K)) :
    Topology.IsEmbedding fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property := by
  classical
  refine Topology.IsEmbedding.mk (Topology.isInducing_iff_nhds.mpr fun a₀ ↦ ?_)
    (classicalPoint_injective_of_isField (Field.toIsField K) x)
  refine le_antisymm ((continuous_classicalPoint x).continuousAt.tendsto.le_comap) ?_
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨c, hcpos, hcε⟩ := NormedField.exists_norm_lt K hε
  have hc : c ≠ 0 := norm_pos_iff.mp hcpos
  set T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight) :=
    Finset.univ.image fun i : Fin k ↦
      weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
        weightedC _ isWeightFamily_one_weight (a₀.val i)
  set V : Set (closedPolydisc k K) :=
    Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T (weightedC _ _ c)
  have hpre : (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property) ⁻¹' V = Metric.closedBall a₀ ‖c‖ :=
    preimage_rationalSubset_classicalPoint_closedBall x a₀ hc
  have hVopen : IsOpen V :=
    isOpen_val_preimage_rationalSubset_closedPolydisc T (weightedC _ _ c)
  have ha₀V : classicalPoint x a₀.val a₀.property ∈ V :=
    (Set.ext_iff.mp hpre a₀).mpr (Metric.mem_closedBall_self (norm_nonneg c))
  refine Filter.mem_comap.mpr ⟨V, hVopen.mem_nhds ha₀V, ?_⟩
  rw [hpre]
  exact (Metric.closedBall_subset_ball hcε).trans hball

/-- **Homeomorphism from `(K°)ᵏ` onto the `K`-rational points of `closedPolydisc k K`.** With the
subspace topology inherited from the adic spectrum, the `K`-rational points `D(K)` are homeomorphic
to `(K°)ᵏ` with its valuation topology. -/
noncomputable def classicalPointRangeHomeomorph (x : spa (powerBoundedSubring K)) :
    {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ≃ₜ
      Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) :=
  (isEmbedding_classicalPoint x).toHomeomorph

@[simp]
theorem classicalPointRangeHomeomorph_apply_coe (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointRangeHomeomorph x a : closedPolydisc k K) =
      classicalPoint x a.val a.property := (rfl)

@[simp]
theorem classicalPointRangeHomeomorph_symm_apply (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointRangeHomeomorph x).symm ⟨classicalPoint x a.val a.property, ⟨a, rfl⟩⟩ = a :=
  (isEmbedding_classicalPoint x).toHomeomorph_symm_apply a

/-- **The `K`-rational points of a closed polydisc form a completely metrizable space.** -/
theorem isCompletelyMetrizableSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    TopologicalSpace.IsCompletelyMetrizableSpace
      (Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) := by
  have : CompleteSpace {a : Fin k → K // ∀ i, IsPowerBounded (a i)} :=
    completeSpace_subtype_forall_isPowerBounded
  exact (classicalPointRangeHomeomorph x).symm.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **The `K`-rational points of a closed polydisc form a Baire space.** -/
theorem baireSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    BaireSpace
      (Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) := by
  have := isCompletelyMetrizableSpace_range_classicalPoint (k := k) x
  exact BaireSpace.of_completelyPseudoMetrizable

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
