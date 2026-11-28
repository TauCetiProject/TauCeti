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
polydisc `Spa (K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)`. Each integral tuple `a : Fin k → K°` determines the
canonical rational point
`normClassicalPoint (fun i ↦ (a i : K)) (fun i ↦ mem_powerBoundedSubring.mp (a i).property) ∈ D`.

Using the evaluation continuity proved in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Eval`,
this canonical rational-point map `(Fin k → K°) → closedPolydisc k K` is continuous for every
complete ultrametric normed field `K`. Although the basic opens of `Spv K⟨T⟩` cut out weak
inequalities `‖f(a)‖ ≤ ‖g(a)‖ ≠ 0`, the ultrametric inequality preserves them on a neighbourhood
where `g` varies by less than `‖g(a₀)‖` and `f` varies by less than `‖g(a₀)‖`, so preimages of
basic opens are open in `Fin k → K°`.

Conversely, for any nonzero scalar `c ∈ K` and any centre `a₀ : Fin k → K°`, the basic open
`R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)` pulls back along the canonical rational-point map to the metric
closed ball of radius `‖c‖` about `a₀`. When `K` is nontrivially normed, such balls form a
neighbourhood basis in `Fin k → K°`, so the map is a topological embedding and induces a
homeomorphism from `Fin k → K°` onto the subspace `rationalPoints k K` of `K`-rational points. (In
positive dimension `k ≥ 1` over a trivially normed infinite field, the subspace topology on
`rationalPoints k K` is strictly coarser than the discrete topology of `(K°)ᵏ`.)

Since `K°` is closed in the complete space `K`, the finite product `Fin k → K°` is complete as a
metric space. When `K` is nontrivially normed, transporting along this homeomorphism shows that
`rationalPoints k K` is completely metrizable (and hence automatically a Baire space via Mathlib's
`BaireSpace.of_completelyPseudoMetrizable`).

## Main definitions

* `TauCeti.ValuationSpectrum.rationalPointHomeomorph`: for a complete nontrivially normed
  ultrametric field `K`, the homeomorphism from `Fin k → powerBoundedSubring K` onto
  `rationalPoints k K`.

## Main results

* `TauCeti.ValuationSpectrum.continuous_normClassicalPoint`: the canonical rational-point map
  `(Fin k → powerBoundedSubring K) → closedPolydisc k K` is continuous.
* `TauCeti.ValuationSpectrum.preimage_normClassicalPoint_rationalSubset_eq_closedBall`: the preimage
  of the basic open `R({Tᵢ - a₀,ᵢ} / c)` under the canonical rational-point map is the closed metric
  ball of radius `‖c‖` about `a₀`.
* `TauCeti.ValuationSpectrum.isEmbedding_normClassicalPoint`: over a complete nontrivially normed
  ultrametric field, the canonical rational-point map is a topological embedding.
* `TauCeti.ValuationSpectrum.isCompletelyMetrizableSpace_rationalPoints`: over a complete
  nontrivially normed ultrametric field, the subspace `rationalPoints k K` of `closedPolydisc k K`
  is completely metrizable.

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

private def powerBoundedPiEquiv (k : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    (Fin k → powerBoundedSubring K) → {a : Fin k → K // ∀ i, IsPowerBounded (a i)} :=
  fun a ↦ ⟨fun i ↦ (a i : K), fun i ↦ mem_powerBoundedSubring.mp (a i).property⟩

omit [CompleteSpace K] in
private theorem continuous_powerBoundedPiEquiv :
    Continuous (powerBoundedPiEquiv k K) :=
  (continuous_pi fun i ↦ continuous_subtypeVal.comp (continuous_apply i)).subtype_mk _

/-- **Continuity of the canonical rational-point map `(Fin k → K°) → closedPolydisc k K`.** Every
basic open `Spv(K⟨T⟩)(f/g)` pulls back to `{a | ‖f(a)‖ ≤ ‖g(a)‖ ∧ 0 < ‖g(a)‖}`. By continuity of
evaluation and the ultrametric inequality, if `a₀` satisfies these conditions then they persist on
the open neighbourhood where `f` and `g` each vary by strictly less than `‖g(a₀)‖`. -/
theorem continuous_normClassicalPoint :
    Continuous fun a : Fin k → powerBoundedSubring K ↦
      normClassicalPoint (fun i ↦ (a i : K))
        (fun i ↦ mem_powerBoundedSubring.mp (a i).property) := by
  refine continuous_induced_rng.mpr ?_
  rw [instTopologicalSpace_eq_generateFrom, continuous_generateFrom_iff]
  rintro _ ⟨f, g, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro a₀ ha₀
  rw [Set.mem_preimage, Function.comp_apply, normClassicalPoint_mem_basicOpen_iff] at ha₀
  obtain ⟨hfg, hgne⟩ := ha₀
  have hgpos : 0 < ‖evalAtHom (powerBoundedPiEquiv k K a₀).val
      (powerBoundedPiEquiv k K a₀).property g‖ :=
    norm_pos_iff.mpr hgne
  set r : ℝ := ‖evalAtHom (powerBoundedPiEquiv k K a₀).val
    (powerBoundedPiEquiv k K a₀).property g‖
  have hcont_f : Continuous fun a : Fin k → powerBoundedSubring K ↦
      evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property f :=
    (continuous_evalAtHom_arg f).comp continuous_powerBoundedPiEquiv
  have hcont_g : Continuous fun a : Fin k → powerBoundedSubring K ↦
      evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property g :=
    (continuous_evalAtHom_arg g).comp continuous_powerBoundedPiEquiv
  have hopen : IsOpen ({a : Fin k → powerBoundedSubring K |
        ‖evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property f -
          evalAtHom (powerBoundedPiEquiv k K a₀).val
            (powerBoundedPiEquiv k K a₀).property f‖ < r} ∩
      {a : Fin k → powerBoundedSubring K |
        ‖evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property g -
          evalAtHom (powerBoundedPiEquiv k K a₀).val
            (powerBoundedPiEquiv k K a₀).property g‖ < r}) :=
    (isOpen_lt (hcont_f.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (hcont_g.sub continuous_const).norm continuous_const)
  refine mem_nhds_iff.mpr ⟨_, fun a ha ↦ ?_, hopen, by simp [hgpos]⟩
  obtain ⟨hf_lt, hg_lt⟩ := ha
  have hga : ‖evalAtHom (powerBoundedPiEquiv k K a).val
      (powerBoundedPiEquiv k K a).property g‖ = r := by
    rw [← sub_add_cancel
        (evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property g)
        (evalAtHom (powerBoundedPiEquiv k K a₀).val (powerBoundedPiEquiv k K a₀).property g),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hg_lt.ne, max_eq_right hg_lt.le]
  have hfa : ‖evalAtHom (powerBoundedPiEquiv k K a).val
      (powerBoundedPiEquiv k K a).property f‖ ≤ r := by
    rw [← sub_add_cancel
        (evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property f)
        (evalAtHom (powerBoundedPiEquiv k K a₀).val (powerBoundedPiEquiv k K a₀).property f)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hf_lt.le hfg)
  rw [Set.mem_preimage, Function.comp_apply, normClassicalPoint_mem_basicOpen_iff]
  change ‖evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property f‖ ≤
      ‖evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property g‖ ∧
    evalAtHom (powerBoundedPiEquiv k K a).val (powerBoundedPiEquiv k K a).property g ≠ 0
  rw [hga]
  exact ⟨hfa, norm_ne_zero_iff.mp (hga ▸ hgpos.ne')⟩

open scoped Classical in
/-- **Basic-open balls pull back to metric closed balls on `Fin k → K°`.** For any centre
`a₀ : Fin k → K°` and any nonzero `c ∈ K`, the preimage of the basic open
`R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)` under the canonical rational-point map is the closed ball of
radius `‖c‖` about `a₀`. -/
theorem preimage_normClassicalPoint_rationalSubset_eq_closedBall
    (a₀ : Fin k → powerBoundedSubring K) {c : K} (hc : c ≠ 0) :
    (fun a : Fin k → powerBoundedSubring K ↦
        normClassicalPoint (fun i ↦ (a i : K))
          (fun i ↦ mem_powerBoundedSubring.mp (a i).property)) ⁻¹'
      (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
        (Finset.univ.image fun i : Fin k ↦
          weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
            weightedC _ isWeightFamily_one_weight (a₀ i : K))
        (weightedC _ isWeightFamily_one_weight c)) =
      Metric.closedBall a₀ ‖c‖ := by
  ext a
  simp only [Set.mem_preimage, normClassicalPoint_mem_rationalSubset_iff, Finset.mem_image,
    Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff, map_sub,
    evalAtHom_weightedX, evalAtHom_weightedC, hc, ne_eq, not_false_eq_true, and_true,
    Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg (norm_nonneg c), Pi.sub_apply,
    AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]

end NormedField

section NontriviallyNormedField

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Over a complete nontrivially normed ultrametric field `K`, the canonical rational-point map
`(Fin k → K°) → closedPolydisc k K` is a topological embedding.** Continuity holds by
`continuous_normClassicalPoint`, injectivity by `normClassicalPoint_injective`, and metric closed
balls of arbitrarily small positive radius `‖c‖` arise as preimages of basic opens
`R({Tᵢ - a₀,ᵢ} / c)`. -/
theorem isEmbedding_normClassicalPoint :
    Topology.IsEmbedding fun a : Fin k → powerBoundedSubring K ↦
      normClassicalPoint (fun i ↦ (a i : K))
        (fun i ↦ mem_powerBoundedSubring.mp (a i).property) := by
  classical
  refine Topology.IsEmbedding.mk (Topology.isInducing_iff_nhds.mpr fun a₀ ↦ ?_) fun a b hab ↦ ?_
  · refine le_antisymm (continuous_normClassicalPoint.continuousAt.tendsto.le_comap) ?_
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨c, hcpos, hcε⟩ := NormedField.exists_norm_lt K hε
    have hc : c ≠ 0 := norm_pos_iff.mp hcpos
    set T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
        isWeightFamily_one_weight) :=
      Finset.univ.image fun i : Fin k ↦
        weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
          weightedC _ isWeightFamily_one_weight (a₀ i : K)
    set V : Set (closedPolydisc k K) :=
      Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T (weightedC _ _ c)
    have hpre : (fun a : Fin k → powerBoundedSubring K ↦
        normClassicalPoint (fun i ↦ (a i : K))
          (fun i ↦ mem_powerBoundedSubring.mp (a i).property)) ⁻¹' V =
        Metric.closedBall a₀ ‖c‖ :=
      preimage_normClassicalPoint_rationalSubset_eq_closedBall a₀ hc
    have hVopen : IsOpen V :=
      isOpen_val_preimage_rationalSubset_closedPolydisc T (weightedC _ _ c)
    have ha₀V : normClassicalPoint (fun i ↦ (a₀ i : K))
        (fun i ↦ mem_powerBoundedSubring.mp (a₀ i).property) ∈ V :=
      (Set.ext_iff.mp hpre a₀).mpr (Metric.mem_closedBall_self (norm_nonneg c))
    refine Filter.mem_comap.mpr ⟨V, hVopen.mem_nhds ha₀V, ?_⟩
    rw [hpre]
    exact (Metric.closedBall_subset_ball hcε).trans hball
  · have hpi := normClassicalPoint_injective (k := k) (K := K)
      (a₁ := ⟨fun i ↦ (a i : K), fun i ↦ mem_powerBoundedSubring.mp (a i).property⟩)
      (a₂ := ⟨fun i ↦ (b i : K), fun i ↦ mem_powerBoundedSubring.mp (b i).property⟩) hab
    exact funext fun i ↦ Subtype.ext (congrFun (congrArg Subtype.val hpi) i)

/-- **The homeomorphism between `Fin k → powerBoundedSubring K` and `rationalPoints k K`**, over a
complete nontrivially normed ultrametric field. -/
noncomputable def rationalPointHomeomorph :
    (Fin k → powerBoundedSubring K) ≃ₜ rationalPoints k K :=
  isEmbedding_normClassicalPoint.toHomeomorph.trans
    (Homeomorph.setCongr <| by
      ext v
      simp only [mem_rationalPoints_iff, Set.mem_range]
      refine ⟨?_, ?_⟩
      · rintro ⟨a, rfl⟩
        exact ⟨_, _, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨fun i ↦ ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩, rfl⟩)

/-- Applying `rationalPointHomeomorph` returns `normClassicalPoint` at the tuple of underlying
elements of `K`. -/
@[simp]
theorem rationalPointHomeomorph_apply (a : Fin k → powerBoundedSubring K) :
    (rationalPointHomeomorph a : closedPolydisc k K) =
      normClassicalPoint (fun i ↦ (a i : K))
        (fun i ↦ mem_powerBoundedSubring.mp (a i).property) := by
  rw [rationalPointHomeomorph]
  rfl

/-- The inverse of `rationalPointHomeomorph` recovers `a` from its canonical rational point. -/
@[simp]
theorem rationalPointHomeomorph_symm_apply_normClassicalPoint
    (a : Fin k → powerBoundedSubring K) :
    rationalPointHomeomorph.symm
        ⟨normClassicalPoint (fun i ↦ (a i : K))
            (fun i ↦ mem_powerBoundedSubring.mp (a i).property),
          normClassicalPoint_mem_rationalPoints _ _⟩ = a := by
  have h : (⟨normClassicalPoint (fun i ↦ (a i : K))
        (fun i ↦ mem_powerBoundedSubring.mp (a i).property),
      normClassicalPoint_mem_rationalPoints _ _⟩ : rationalPoints k K) =
      rationalPointHomeomorph a :=
    Subtype.ext (rationalPointHomeomorph_apply a).symm
  rw [h, rationalPointHomeomorph.symm_apply_apply]

/-- **The subspace `rationalPoints k K` of a closed polydisc is completely metrizable**, being
homeomorphic to `Fin k → powerBoundedSubring K`. -/
instance isCompletelyMetrizableSpace_rationalPoints :
    TopologicalSpace.IsCompletelyMetrizableSpace (rationalPoints k K) :=
  (rationalPointHomeomorph (k := k) (K := K)).symm.isClosedEmbedding
    |>.IsCompletelyMetrizableSpace

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
