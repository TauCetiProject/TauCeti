/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import Mathlib.Topology.Baire.CompleteMetrizable

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The subspace topology on the rational points of a closed polydisc

Let `K` be a complete ultrametric normed field and `D = closedPolydisc k K` the closed unit
polydisc `Spa (K⟨T₁, …, Tₖ⟩, K⟨T₁, …, Tₖ⟩°)`. Given a point `x ∈ Spa (K, K°)`, each tuple
`a ∈ (K°)ᵏ` determines the classical evaluation point `classicalPoint x a ha ∈ D`.

This file identifies the evaluation homomorphism `evalAtHom a ha` with the normed evaluation
`MvPowerSeries.restrictedEval₂` through the Gauss comparison `restrictedMvPowerSeriesGaussEquiv`,
which transfers the Lipschitz and continuity bounds in the evaluation argument `a` to `evalAtHom`.

Consequently the classical-point map `a ↦ classicalPoint x a ha` is continuous for every complete
ultrametric normed field `K`. Although the basic opens of `Spv K⟨T⟩` cut out weak inequalities
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
hence a Baire space. In dimension `0`, every point of `closedPolydisc 0 K` is classical, so
`closedPolydisc 0 K` is a subsingleton coinciding with the range of `classicalPoint`.

## Main definitions

* `TauCeti.ValuationSpectrum.classicalPointRangeHomeomorph`: for a complete nontrivially normed
  ultrametric field `K`, the homeomorphism from `{a : Fin k → K // ∀ i, IsPowerBounded (a i)}`
  onto the subspace of `K`-rational classical points of `closedPolydisc k K`.

## Main results

* `TauCeti.ValuationSpectrum.evalAtHom_eq_restrictedEval₂`: comparison of `evalAtHom` with
  `MvPowerSeries.restrictedEval₂` via `restrictedMvPowerSeriesGaussEquiv`.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_le` and
  `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_le`: Gauss-norm bound and Lipschitz bound for
  `evalAtHom` in its evaluation point.
* `TauCeti.ValuationSpectrum.continuous_evalAtHom_arg`: for fixed `f`, `a ↦ evalAtHom a.1 a.2 f`
  is continuous on `(K°)ᵏ`.
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
* `TauCeti.ValuationSpectrum.eq_classicalPoint_zero` and
  `TauCeti.ValuationSpectrum.range_classicalPoint_zero_eq_univ`: in dimension `0`, every point of
  `closedPolydisc 0 K` is the unique classical point.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5, p. 60.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open Filter Topology TauCeti.Huber
open scoped Topology

section NormedCommRing

variable {k : ℕ} {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Comparison of `evalAtHom` with normed restricted evaluation.** Through the Gauss-norm
comparison `restrictedMvPowerSeriesGaussEquiv`, Wedhorn's evaluation `evalAtHom a ha` agrees with
`MvPowerSeries.restrictedEval₂` along the identity of `A`. -/
theorem evalAtHom_eq_restrictedEval₂ (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    evalAtHom a ha f =
      MvPowerSeries.restrictedEval₂ (RingHom.id A) a (fun _ ↦ le_rfl) ha'
        (restrictedMvPowerSeriesGaussEquiv f) := by
  have heq : (evalAtHom a ha).comp restrictedMvPowerSeriesGaussEquiv.symm.toRingHom =
      MvPowerSeries.restrictedEval₂ (RingHom.id A) a (fun _ ↦ le_rfl) ha' := by
    refine MvPowerSeries.eq_restrictedEval₂ (RingHom.id A) a (fun _ ↦ le_rfl) ha' _
      ((continuous_evalAtHom a ha).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm)
      (fun r ↦ ?_) fun i ↦ ?_
    · have hC : restrictedMvPowerSeriesGaussEquiv.symm
          (algebraMap A (MvPowerSeries.IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1)) r) =
          weightedC _ isWeightFamily_one_weight r :=
        restrictedMvPowerSeriesGaussEquiv.injective (by simp)
      simp [hC]
    · have hX : restrictedMvPowerSeriesGaussEquiv.symm
          ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_monomial _ (Finsupp.single i 1) 1⟩ =
          weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :=
        restrictedMvPowerSeriesGaussEquiv.injective (by simp)
      simp [hX]
  simpa using RingHom.congr_fun heq (restrictedMvPowerSeriesGaussEquiv f)

/-- **Gauss-norm bound on evaluation.** Evaluating `f ∈ A⟨T⟩` at a point `a` with `‖a i‖ ≤ 1`
produces an element of norm at most the unit Gauss norm of `f`. -/
theorem norm_evalAtHom_le (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f‖ ≤ ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂ a ha ha' f]
  exact MvPowerSeries.norm_restrictedEval₂_le (RingHom.id A) a (fun _ ↦ le_rfl) ha' _

/-- **Ultrametric Lipschitz bound for `evalAtHom` in its argument.** If `a` and `b` lie in the
closed unit polydisc and satisfy `‖a i - b i‖ ≤ δ` for every `i`, then
`‖f(a) - f(b)‖ ≤ δ * ‖f‖`. -/
theorem norm_evalAtHom_sub_le {a b : Fin k → A} (ha : ∀ i, IsPowerBounded (a i))
    (ha' : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, IsPowerBounded (b i)) (hb' : ∀ i, ‖b i‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hab : ∀ i, ‖a i - b i‖ ≤ δ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤ δ * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂ a ha ha' f, evalAtHom_eq_restrictedEval₂ b hb hb' f]
  exact MvPowerSeries.norm_restrictedEval₂_sub_le (RingHom.id A) (fun _ ↦ le_rfl) ha' hb' hδ
    (fun i ↦ by simpa using hab i) (restrictedMvPowerSeriesGaussEquiv f)

end NormedCommRing

section NormedField

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Evaluation of a fixed restricted series is continuous in its argument** on `(K°)ᵏ`. -/
theorem continuous_evalAtHom_arg
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f := by
  let e : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} →
      {a : Fin k → K // ∀ i, ‖a i‖ ≤ (1 : ℝ)} :=
    fun a ↦ ⟨a.1, fun i ↦ isPowerBounded_iff_norm_le_one.mp (a.2 i)⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have hfun : (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f) =
      (fun a : {a : Fin k → K // ∀ i, ‖a i‖ ≤ (1 : ℝ)} ↦
        MvPowerSeries.restrictedEval₂ (RingHom.id K) a.1 (fun _ ↦ le_rfl) a.2
          (restrictedMvPowerSeriesGaussEquiv f)) ∘ e :=
    funext fun a ↦ evalAtHom_eq_restrictedEval₂ a.1 a.2 (fun i ↦
      isPowerBounded_iff_norm_le_one.mp (a.2 i)) f
  rw [hfun]
  exact (MvPowerSeries.continuous_restrictedEval₂_arg (RingHom.id K) (fun _ ↦ le_rfl)
    (restrictedMvPowerSeriesGaussEquiv f)).comp he

/-- **Continuity of the classical-point map `(K°)ᵏ → closedPolydisc k K`.** Every basic open
`Spv(K⟨T⟩)(f/g)` pulls back to `{a | ‖f(a)‖ ≤ ‖g(a)‖ ∧ 0 < ‖g(a)‖}`. By continuity of evaluation
and the ultrametric inequality, if `a₀` satisfies these conditions then they persist on the open
neighbourhood where `f` and `g` each vary by strictly less than `‖g(a₀)‖`. -/
theorem continuous_classicalPoint (x : spa (powerBoundedSubring K)) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2 := by
  refine continuous_induced_rng.mpr ?_
  rw [instTopologicalSpace_eq_generateFrom, continuous_generateFrom_iff]
  rintro _ ⟨f, g, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro a₀ ha₀
  rw [Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle, classicalPoint_vle, map_zero,
    vle_iff_norm_le_of_mem_spa x.2, vle_iff_norm_le_of_mem_spa x.2, norm_zero, not_le] at ha₀
  obtain ⟨hfg, hgpos⟩ := ha₀
  set r : ℝ := ‖evalAtHom a₀.1 a₀.2 g‖
  have hopen : IsOpen ({a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} |
        ‖evalAtHom a.1 a.2 f - evalAtHom a₀.1 a₀.2 f‖ < r} ∩
      {a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} |
        ‖evalAtHom a.1 a.2 g - evalAtHom a₀.1 a₀.2 g‖ < r}) :=
    (isOpen_lt ((continuous_evalAtHom_arg f).sub continuous_const).norm continuous_const).inter
      (isOpen_lt ((continuous_evalAtHom_arg g).sub continuous_const).norm continuous_const)
  refine mem_nhds_iff.mpr ⟨_, fun a ha ↦ ?_, hopen, by simp [hgpos]⟩
  obtain ⟨hf_lt, hg_lt⟩ := ha
  have hga : ‖evalAtHom a.1 a.2 g‖ = r := by
    rw [← sub_add_cancel (evalAtHom a.1 a.2 g) (evalAtHom a₀.1 a₀.2 g),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hg_lt.ne, max_eq_right hg_lt.le]
  have hfa : ‖evalAtHom a.1 a.2 f‖ ≤ r := by
    rw [← sub_add_cancel (evalAtHom a.1 a.2 f) (evalAtHom a₀.1 a₀.2 f)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hf_lt.le hfg)
  rw [Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle, classicalPoint_vle, map_zero,
    vle_iff_norm_le_of_mem_spa x.2, vle_iff_norm_le_of_mem_spa x.2, norm_zero, not_le, hga]
  exact ⟨hfa, hgpos⟩

open scoped Classical in
/-- **Rational balls pull back to metric closed balls on `(K°)ᵏ`.** For any centre `a₀ ∈ (K°)ᵏ`
and any nonzero `c ∈ K`, the preimage of the rational subset `R({T₁ - a₀,₁, …, Tₖ - a₀,ₖ} / c)`
under the classical-point map is the closed ball of radius `‖c‖` about `a₀`. -/
theorem preimage_rationalSubset_classicalPoint_closedBall (x : spa (powerBoundedSubring K))
    (a₀ : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) {c : K} (hc : c ≠ 0) :
    (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ classicalPoint x a.1 a.2) ⁻¹'
      (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
        (Finset.univ.image fun i : Fin k ↦
          weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
            weightedC _ isWeightFamily_one_weight (a₀.1 i))
        (weightedC _ isWeightFamily_one_weight c)) =
      Metric.closedBall a₀ ‖c‖ := by
  ext a
  simp only [Set.mem_preimage, mem_rationalSubset_iff, ← closedPolydisc_def,
    (classicalPoint x a.1 a.2).2, true_and, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, classicalPoint_vle, map_sub, map_zero,
    evalAtHom_weightedX, evalAtHom_weightedC, vle_iff_norm_le_of_mem_spa x.2, norm_zero,
    not_le, norm_pos_iff.mpr hc, and_true, Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm,
    pi_norm_le_iff_of_nonneg (norm_nonneg c), Pi.sub_apply]

end NormedField

section DimensionZero

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **In dimension `0`, every point of `closedPolydisc 0 K` is the unique classical point.** -/
theorem eq_classicalPoint_zero (x : spa (powerBoundedSubring K)) (v : closedPolydisc 0 K) :
    v = classicalPoint x Fin.elim0 (fun i ↦ i.elim0) := by
  let e := weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set K))
  have he : ∀ a : K, e.symm a = weightedC _ isWeightFamily_one_weight a := fun a ↦
    Subtype.ext (by simp [e])
  refine Subtype.ext (ext' fun f g ↦ ?_)
  rw [← e.symm_apply_apply f, ← e.symm_apply_apply g, he, he,
    closedPolydisc_vle_weightedC_iff, classicalPoint_vle, evalAtHom_weightedC,
    evalAtHom_weightedC, vle_iff_norm_le_of_mem_spa x.2]

/-- In dimension `0`, `closedPolydisc 0 K` has at most one point (indeed exactly one whenever
`Spa (K, K°)` is nonempty). -/
theorem subsingleton_closedPolydisc_zero : Subsingleton (closedPolydisc 0 K) where
  allEq v w := by
    let x : spa (powerBoundedSubring K) := ⟨_, comap_weightedC_mem_spa v⟩
    rw [eq_classicalPoint_zero x v, eq_classicalPoint_zero x w]

/-- **In dimension `0`, the classical points exhaust `closedPolydisc 0 K`.** -/
theorem range_classicalPoint_zero_eq_univ (x : spa (powerBoundedSubring K)) :
    Set.range (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) = Set.univ := by
  ext v
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩, (eq_classicalPoint_zero x v).symm⟩

end DimensionZero

section NontriviallyNormedField

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The classical-point map `(K°)ᵏ → closedPolydisc k K` is a topological embedding.**
Continuity holds by `continuous_classicalPoint`, injectivity by
`classicalPoint_injective_of_isField`, and metric closed balls of arbitrarily small positive radius
`‖c‖` arise as preimages of rational subsets `R({Tᵢ - a₀,ᵢ} / c)`. -/
theorem isEmbedding_classicalPoint (x : spa (powerBoundedSubring K)) :
    Topology.IsEmbedding fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2 := by
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
        weightedC _ isWeightFamily_one_weight (a₀.1 i)
  set V : Set (closedPolydisc k K) :=
    Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T (weightedC _ _ c)
  have hpre : (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) ⁻¹' V = Metric.closedBall a₀ ‖c‖ :=
    preimage_rationalSubset_classicalPoint_closedBall x a₀ hc
  have hVopen : IsOpen V := by
    have h := isOpen_val_preimage_rationalSubset
      (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
        isWeightFamily_one_weight)) T (weightedC _ _ c)
    rw [← closedPolydisc_def] at h
    exact h
  have ha₀V : classicalPoint x a₀.1 a₀.2 ∈ V :=
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
        classicalPoint x a.1 a.2) :=
  (isEmbedding_classicalPoint x).toHomeomorph

@[simp]
theorem classicalPointRangeHomeomorph_apply_coe (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointRangeHomeomorph x a : closedPolydisc k K) = classicalPoint x a.1 a.2 := (rfl)

@[simp]
theorem classicalPointRangeHomeomorph_symm_apply (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointRangeHomeomorph x).symm ⟨classicalPoint x a.1 a.2, ⟨a, rfl⟩⟩ = a :=
  (isEmbedding_classicalPoint x).toHomeomorph_symm_apply a

/-- **The `K`-rational points of a closed polydisc form a completely metrizable space.** -/
theorem isCompletelyMetrizableSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    TopologicalSpace.IsCompletelyMetrizableSpace
      (Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2)) := by
  have : CompleteSpace {a : Fin k → K // ∀ i, IsPowerBounded (a i)} :=
    completeSpace_subtype_forall_isPowerBounded
  exact (classicalPointRangeHomeomorph x).symm.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **The `K`-rational points of a closed polydisc form a Baire space.** -/
theorem baireSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    BaireSpace
      (Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2)) := by
  have := isCompletelyMetrizableSpace_range_classicalPoint (k := k) x
  exact BaireSpace.of_completelyPseudoMetrizable

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
