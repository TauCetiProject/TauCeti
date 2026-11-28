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

Conversely, for any nonzero scalar `c ∈ K` and any centre `a₀ ∈ (K°)ᵏ`, the basic open
`R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)` pulls back along the classical-point map to the metric closed
ball of radius `‖c‖` about `a₀`. When `K` is nontrivially normed, such balls form a neighbourhood
basis in `(K°)ᵏ`, so the classical-point map is a topological embedding and induces a homeomorphism
from `(K°)ᵏ` onto the subspace `D(K)` of `K`-rational points. (In positive dimension `k ≥ 1` over a
trivially normed infinite field, the subspace topology on `D(K)` is strictly coarser than the
discrete topology of `Kᵏ`.)

Since `(K°)ᵏ` is the closed unit ball in the complete finite product `Kᵏ`, it is complete as a
metric space. When `K` is nontrivially normed, transporting along this homeomorphism shows that
`D(K)` is completely metrizable and hence a Baire space.

## Main definitions

* `TauCeti.ValuationSpectrum.classicalPointHomeomorph` and
  `TauCeti.ValuationSpectrum.classicalPointPowerBoundedHomeomorph`: for a complete nontrivially
  normed ultrametric field `K`, the homeomorphisms from
  `{a : Fin k → K // ∀ i, IsPowerBounded (a i)}` and `Fin k → powerBoundedSubring K` onto
  `classicalPoints k K`.

## Main results

* `TauCeti.ValuationSpectrum.continuous_classicalPoint`: the classical-point map
  `(K°)ᵏ → closedPolydisc k K` is continuous.
* `TauCeti.ValuationSpectrum.preimage_classicalPoint_rationalSubset_eq_closedBall`: the preimage of
  the basic open `R({Tᵢ - a₀,ᵢ} / c)` under the classical-point map is the closed metric ball of
  radius `‖c‖` about `a₀`.
* `TauCeti.ValuationSpectrum.isEmbedding_classicalPoint`: over a complete nontrivially normed
  ultrametric field, the classical-point map is a topological embedding.
* `TauCeti.ValuationSpectrum.isCompletelyMetrizableSpace_classicalPoints` and
  `TauCeti.ValuationSpectrum.baireSpace_classicalPoints`: over a complete nontrivially normed
  ultrametric field, the subspace `classicalPoints k K` of `closedPolydisc k K` is completely
  metrizable and a Baire space.

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
  rw [Set.mem_preimage, Function.comp_apply, classicalPoint_eq_normClassicalPoint,
    normClassicalPoint_mem_basicOpen_iff] at ha₀
  obtain ⟨hfg, hgne⟩ := ha₀
  have hgpos : 0 < ‖evalAtHom a₀.val a₀.property g‖ := norm_pos_iff.mpr hgne
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
  rw [Set.mem_preimage, Function.comp_apply, classicalPoint_eq_normClassicalPoint,
    normClassicalPoint_mem_basicOpen_iff, hga]
  exact ⟨hfa, norm_ne_zero_iff.mp (hga ▸ hgpos.ne')⟩

open scoped Classical in
/-- **Basic-open balls pull back to metric closed balls on `(K°)ᵏ`.** For any centre `a₀ ∈ (K°)ᵏ`
and any nonzero `c ∈ K`, the preimage of the basic open `R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)`
under the classical-point map is the closed ball of radius `‖c‖` about `a₀`. -/
theorem preimage_classicalPoint_rationalSubset_eq_closedBall (x : spa (powerBoundedSubring K))
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

/-- **Over a complete nontrivially normed ultrametric field `K`, the classical-point map
`(K°)ᵏ → closedPolydisc k K` is a topological embedding.** Continuity holds by
`continuous_classicalPoint`, injectivity by `classicalPoint_injective_of_isField`, and metric
closed balls of arbitrarily small positive radius `‖c‖` arise as preimages of basic opens
`R({Tᵢ - a₀,ᵢ} / c)`. -/
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
    preimage_classicalPoint_rationalSubset_eq_closedBall x a₀ hc
  have hVopen : IsOpen V :=
    isOpen_val_preimage_rationalSubset_closedPolydisc T (weightedC _ _ c)
  have ha₀V : classicalPoint x a₀.val a₀.property ∈ V :=
    (Set.ext_iff.mp hpre a₀).mpr (Metric.mem_closedBall_self (norm_nonneg c))
  refine Filter.mem_comap.mpr ⟨V, hVopen.mem_nhds ha₀V, ?_⟩
  rw [hpre]
  exact (Metric.closedBall_subset_ball hcε).trans hball

/-- **The homeomorphism between `(K°)ᵏ` and `classicalPoints k K`**, over a complete nontrivially
normed ultrametric field. -/
noncomputable def classicalPointHomeomorph :
    {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ≃ₜ classicalPoints k K :=
  (isEmbedding_classicalPoint (normSpaPoint K)).toHomeomorph.trans
    (Homeomorph.setCongr (range_classicalPoint_eq_classicalPoints (normSpaPoint K)))

/-- Applying `classicalPointHomeomorph` returns `normClassicalPoint` at `a`. -/
@[simp]
theorem classicalPointHomeomorph_apply (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointHomeomorph a : closedPolydisc k K) = normClassicalPoint a.val a.property :=
  classicalPoint_eq_normClassicalPoint (normSpaPoint K) a.val a.property

/-- The inverse of `classicalPointHomeomorph` recovers `a` from its classical point. -/
@[simp]
theorem classicalPointHomeomorph_symm_apply_normClassicalPoint
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    classicalPointHomeomorph.symm
        ⟨normClassicalPoint a.val a.property,
          mem_classicalPoints_iff.mpr ⟨a.val, a.property, rfl⟩⟩ = a := by
  have h : (⟨normClassicalPoint a.val a.property,
      mem_classicalPoints_iff.mpr ⟨a.val, a.property, rfl⟩⟩ : classicalPoints k K) =
      classicalPointHomeomorph a :=
    Subtype.ext (classicalPointHomeomorph_apply a).symm
  rw [h, classicalPointHomeomorph.symm_apply_apply]

/-- **The homeomorphism between `Fin k → powerBoundedSubring K` and `classicalPoints k K`**, over a
complete nontrivially normed ultrametric field. -/
noncomputable def classicalPointPowerBoundedHomeomorph :
    (Fin k → powerBoundedSubring K) ≃ₜ classicalPoints k K :=
  Homeomorph.trans
    { toFun := fun f ↦ ⟨fun i ↦ (f i : K), fun i ↦ mem_powerBoundedSubring.mp (f i).property⟩
      invFun := fun a i ↦ ⟨a.val i, mem_powerBoundedSubring.mpr (a.property i)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        (continuous_pi fun i ↦ continuous_subtypeVal.comp (continuous_apply i)).subtype_mk _
      continuous_invFun :=
        continuous_pi fun i ↦
          ((continuous_apply i).comp continuous_subtypeVal).subtype_mk _ }
    classicalPointHomeomorph

/-- Applying `classicalPointPowerBoundedHomeomorph` returns `normClassicalPoint` at the tuple of
underlying elements of `K`. -/
@[simp]
theorem classicalPointPowerBoundedHomeomorph_apply (a : Fin k → powerBoundedSubring K) :
    (classicalPointPowerBoundedHomeomorph a : closedPolydisc k K) =
      normClassicalPoint (fun i ↦ (a i : K)) (fun i ↦ mem_powerBoundedSubring.mp (a i).property) :=
  classicalPointHomeomorph_apply _

/-- The inverse of `classicalPointPowerBoundedHomeomorph` recovers `a` from its classical point. -/
@[simp]
theorem classicalPointPowerBoundedHomeomorph_symm_apply_normClassicalPoint
    (a : Fin k → powerBoundedSubring K) :
    classicalPointPowerBoundedHomeomorph.symm
        ⟨normClassicalPoint (fun i ↦ (a i : K))
            (fun i ↦ mem_powerBoundedSubring.mp (a i).property),
          mem_classicalPoints_iff.mpr
            ⟨fun i ↦ (a i : K), fun i ↦ mem_powerBoundedSubring.mp (a i).property, rfl⟩⟩ = a := by
  have h : (⟨normClassicalPoint (fun i ↦ (a i : K))
        (fun i ↦ mem_powerBoundedSubring.mp (a i).property),
      mem_classicalPoints_iff.mpr
        ⟨fun i ↦ (a i : K), fun i ↦ mem_powerBoundedSubring.mp (a i).property, rfl⟩⟩ :
      classicalPoints k K) = classicalPointPowerBoundedHomeomorph a :=
    Subtype.ext (classicalPointPowerBoundedHomeomorph_apply a).symm
  rw [h, classicalPointPowerBoundedHomeomorph.symm_apply_apply]

/-- **The subspace `classicalPoints k K` of a closed polydisc is completely metrizable**, being
homeomorphic to the closed unit ball `(K°)ᵏ` of the complete metric space `Kᵏ`. -/
instance isCompletelyMetrizableSpace_classicalPoints :
    TopologicalSpace.IsCompletelyMetrizableSpace (classicalPoints k K) := by
  have : CompleteSpace {a : Fin k → K // ∀ i, IsPowerBounded (a i)} :=
    completeSpace_subtype_forall_isPowerBounded
  exact (classicalPointHomeomorph (k := k) (K := K)).symm.isClosedEmbedding
    |>.IsCompletelyMetrizableSpace

/-- **The subspace `classicalPoints k K` of a closed polydisc is a Baire space**, by the Baire
category theorem for completely metrizable spaces. -/
instance baireSpace_classicalPoints : BaireSpace (classicalPoints k K) :=
  BaireSpace.of_completelyPseudoMetrizable

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
