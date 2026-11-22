/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Eval
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Topology of the rational points of a closed polydisc

Let `K` be a complete ultrametric normed field and `D = closedPolydisc k K` the closed unit
polydisc of dimension `k` over `K`. Its locus `classicalPoints k K` of `K`-rational classical
points is parametrized by the power-bounded tuples `a ∈ (K°)ᵏ` via
`a ↦ normClassicalPoint a ha`.

Because evaluation of a fixed restricted power series `f ∈ K⟨T⟩` is Lipschitz on `(K°)ᵏ`
(`TauCeti.ValuationSpectrum.lipschitzWith_evalAtHom_apply`), every basic open `Spv(K⟨T⟩)(f/s)`
pulls back to an open subset of `(K°)ᵏ`: at any point `a` with `‖f(a)‖ ≤ ‖s(a)‖ ≠ 0`, on a small
metric ball around `a` the value `s(b)` has constant norm `‖s(a)‖` while `f(b)` changes by strictly
less than `‖s(a)‖`, so the ultrametric inequality preserves `‖f(b)‖ ≤ ‖s(b)‖`. Hence
`normClassicalPoint` is continuous on `(K°)ᵏ` over every complete ultrametric normed field,
including trivially normed ones.

Conversely, for any `a₀ ∈ (K°)ᵏ` and any nonzero `c ∈ K`, the closed metric ball
`{a ∈ (K°)ᵏ | ∀ i, ‖a i - a₀ i‖ ≤ ‖c‖}` is the preimage under `normClassicalPoint` of the
rational subset `R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)`. When `K` is nontrivially normed, nonzero scalars
attain arbitrarily small norms, so these rational traces form a neighbourhood basis of `a₀`.
Combined with injectivity (`TauCeti.ValuationSpectrum.normClassicalPoint_injective`),
`normClassicalPoint` is a topological embedding and therefore a homeomorphism from `(K°)ᵏ` onto
`classicalPoints k K`. Because `(K°)ᵏ` is a closed subset of the complete metric space `Kᵏ`,
`classicalPoints k K` is completely metrizable and a Baire space.

## Main definitions

* `TauCeti.ValuationSpectrum.classicalPointHomeomorph`: for a complete nontrivially normed
  ultrametric field `K`, the homeomorphism from `{a : Fin k → K // ∀ i, IsPowerBounded (a i)}`
  onto `classicalPoints k K`.
* `TauCeti.ValuationSpectrum.classicalPointPowerBoundedHomeomorph`: the corresponding homeomorphism
  from `Fin k → powerBoundedSubring K` onto `classicalPoints k K`.

## Main results

* `TauCeti.ValuationSpectrum.normClassicalPoint_mem_basicOpen_iff` and
  `TauCeti.ValuationSpectrum.normClassicalPoint_mem_rationalSubset_iff`: membership of a classical
  point in a basic open or rational subset expressed by norm inequalities on evaluations.
* `TauCeti.ValuationSpectrum.continuous_normClassicalPoint`: the canonical classical-point map into
  `closedPolydisc k K` is continuous.
* `TauCeti.ValuationSpectrum.preimage_normClassicalPoint_rationalSubset_closedBall` and
  `TauCeti.ValuationSpectrum.closedBall_eq_preimage_normClassicalPoint_rationalSubset`:
  closed metric balls of radii `‖c‖` (`c ≠ 0`) in `(K°)ᵏ` are rational traces.
* `TauCeti.ValuationSpectrum.isEmbedding_normClassicalPoint`: when `K` is nontrivially normed, the
  canonical classical-point map is a topological embedding.
* `TauCeti.ValuationSpectrum.isCompletelyMetrizableSpace_classicalPoints` and
  `TauCeti.ValuationSpectrum.baireSpace_classicalPoints`: the subspace `classicalPoints k K` is
  completely metrizable and a Baire space.

## References

* Sean Howe and Christian Klevdal, *Admissible pairs and p-adic Hodge structures II: the
  bi-analytic Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50,
  Definition 7.29 and Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Filter Topology
open scoped NNReal

section Continuity

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Membership of `normClassicalPoint a ha` in a basic open `Spv(K⟨T⟩)(f/s)` is the norm
inequality `‖f(a)‖ ≤ ‖s(a)‖` together with `s(a) ≠ 0`. -/
theorem normClassicalPoint_mem_basicOpen_iff (a : Fin k → K) (ha : ∀ i, IsPowerBounded (a i))
    (f s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (normClassicalPoint a ha).val ∈ basicOpen f s ↔
      ‖evalAtHom a ha f‖ ≤ ‖evalAtHom a ha s‖ ∧ evalAtHom a ha s ≠ 0 := by
  simp only [mem_basicOpen_iff, normClassicalPoint_vle, map_zero, norm_zero, norm_le_zero_iff]

/-- Membership of `normClassicalPoint a ha` in a rational subset `R(T/s)` of `closedPolydisc k K`
is the family of norm inequalities `‖t(a)‖ ≤ ‖s(a)‖` for `t ∈ T` together with `s(a) ≠ 0`. -/
theorem normClassicalPoint_mem_rationalSubset_iff (a : Fin k → K) (ha : ∀ i, IsPowerBounded (a i))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (normClassicalPoint a ha).val ∈ rationalSubset (powerBoundedSubring _) T s ↔
      (∀ t ∈ T, ‖evalAtHom a ha t‖ ≤ ‖evalAtHom a ha s‖) ∧ evalAtHom a ha s ≠ 0 := by
  have hmem : (normClassicalPoint a ha).val ∈ spa (powerBoundedSubring _) :=
    closedPolydisc_def k K ▸ (normClassicalPoint a ha).property
  simp only [mem_rationalSubset_iff, hmem, true_and, normClassicalPoint_vle, map_zero,
    norm_zero, norm_le_zero_iff]

/-- **The canonical classical-point map into the closed polydisc is continuous.** On a small metric
ball around `a` where `‖f(b) - f(a)‖ < ‖s(a)‖` and `‖s(b) - s(a)‖ < ‖s(a)‖`, the ultrametric law
keeps `‖s(b)‖ = ‖s(a)‖` and preserves the weak inequality `‖f(b)‖ ≤ ‖s(b)‖`. This holds over
every complete ultrametric normed field, without assuming a nontrivial norm. -/
theorem continuous_normClassicalPoint :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      normClassicalPoint a.val a.property := by
  refine Continuous.subtype_mk (continuous_generateFrom_iff.mpr ?_) _
  rintro _ ⟨f, s, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro a ha
  rw [Set.mem_preimage, normClassicalPoint_mem_basicOpen_iff] at ha
  obtain ⟨hle, hs⟩ := ha
  have hr : 0 < ‖evalAtHom a.val a.property s‖ := norm_pos_iff.mpr hs
  have hf_nhds := (continuous_evalAtHom_apply f).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds (evalAtHom a.val a.property f) hr)
  have hs_nhds := (continuous_evalAtHom_apply s).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds (evalAtHom a.val a.property s) hr)
  refine Filter.mem_of_superset (Filter.inter_mem hf_nhds hs_nhds) fun b ⟨hfb, hsb⟩ ↦ ?_
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hfb hsb
  rw [Set.mem_preimage, normClassicalPoint_mem_basicOpen_iff]
  have hs_eq : ‖evalAtHom b.val b.property s‖ = ‖evalAtHom a.val a.property s‖ := by
    rw [← add_sub_cancel (evalAtHom a.val a.property s) (evalAtHom b.val b.property s),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsb.ne', max_eq_left hsb.le]
  refine ⟨?_, norm_pos_iff.mp (hs_eq ▸ hr)⟩
  rw [hs_eq, ← add_sub_cancel (evalAtHom a.val a.property f) (evalAtHom b.val b.property f)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hle hfb.le)

open scoped Classical in
/-- **A rational ball cuts out a closed metric ball among classical points.** For any centre
`a₀ : Fin k → K` and nonzero `c : K`, the rational subset `R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)`
pulls back along `normClassicalPoint` to the closed polydisc of radius `‖c‖` about `a₀`. -/
theorem preimage_normClassicalPoint_rationalSubset_closedBall
    (a₀ : Fin k → K) {c : K} (hc : c ≠ 0) :
    (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
          (normClassicalPoint a.val a.property).val) ⁻¹'
        rationalSubset (powerBoundedSubring _)
          (Finset.univ.image fun i : Fin k ↦
            weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
              weightedC _ isWeightFamily_one_weight (a₀ i))
          (weightedC _ isWeightFamily_one_weight c) =
      {a | ∀ i, ‖a.val i - a₀ i‖ ≤ ‖c‖} := by
  ext a
  simp only [Set.mem_preimage, normClassicalPoint_mem_rationalSubset_iff, evalAtHom_weightedC,
    Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff,
    map_sub, evalAtHom_weightedX, hc, ne_eq, not_false_eq_true, and_true, Set.mem_ofPred_eq]

open scoped Classical in
/-- For a point `a₀ ∈ (K°)ᵏ` and nonzero `c : K`, the closed metric ball `Metric.closedBall a₀ ‖c‖`
is the preimage under `normClassicalPoint` of the rational subset
`R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)`. -/
theorem closedBall_eq_preimage_normClassicalPoint_rationalSubset
    (a₀ : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) {c : K} (hc : c ≠ 0) :
    Metric.closedBall a₀ ‖c‖ =
      (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
          normClassicalPoint a.val a.property) ⁻¹'
        (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
          (Finset.univ.image fun i : Fin k ↦
            weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
              weightedC _ isWeightFamily_one_weight (a₀.val i))
          (weightedC _ isWeightFamily_one_weight c)) := by
  rw [Set.preimage_preimage, preimage_normClassicalPoint_rationalSubset_closedBall a₀.val hc]
  ext a
  simp only [Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm,
    pi_norm_le_iff_of_nonneg (norm_nonneg c), Pi.sub_apply, Set.mem_ofPred_eq]

end Continuity

section Embedding

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The canonical classical-point map is a topological embedding** over a complete nontrivially
normed ultrametric field. Rational balls `R({Tᵢ - a₀ᵢ} / c)` cut out closed metric balls of
arbitrarily small radius `‖c‖`, so the subspace topology on `classicalPoints k K` agrees with the
valuation topology on `(K°)ᵏ`. -/
theorem isEmbedding_normClassicalPoint :
    Topology.IsEmbedding fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      normClassicalPoint a.val a.property := by
  classical
  refine ⟨Topology.isInducing_iff_nhds.mpr fun a₀ ↦ le_antisymm
      continuous_normClassicalPoint.continuousAt.tendsto.le_comap ?_,
      normClassicalPoint_injective⟩
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨c, hc₀, hcε⟩ := NormedField.exists_norm_lt K hε
  have hc : c ≠ 0 := norm_pos_iff.mp hc₀
  set U : Set (closedPolydisc k K) :=
    Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
      (Finset.univ.image fun i : Fin k ↦
        weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
          weightedC _ isWeightFamily_one_weight (a₀.val i))
      (weightedC _ isWeightFamily_one_weight c)
  have hpre : Metric.closedBall a₀ ‖c‖ =
      (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        normClassicalPoint a.val a.property) ⁻¹' U :=
    closedBall_eq_preimage_normClassicalPoint_rationalSubset a₀ hc
  have hU_open : IsOpen U := by
    dsimp only [U]
    rw [closedPolydisc_def]
    exact isOpen_val_preimage_rationalSubset _ _ _
  have ha₀U : normClassicalPoint a₀.val a₀.property ∈ U := by
    have : a₀ ∈ Metric.closedBall a₀ ‖c‖ := Metric.mem_closedBall_self (norm_nonneg c)
    rwa [hpre, Set.mem_preimage] at this
  refine Filter.mem_comap.mpr ⟨U, hU_open.mem_nhds ha₀U, ?_⟩
  rw [← hpre]
  exact (Metric.closedBall_subset_ball hcε).trans hball

/-- **The homeomorphism between `(K°)ᵏ` and `classicalPoints k K`**, over a complete nontrivially
normed ultrametric field. -/
noncomputable def classicalPointHomeomorph :
    {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ≃ₜ classicalPoints k K :=
  isEmbedding_normClassicalPoint.toHomeomorph.trans (Homeomorph.setCongr classicalPoints_def.symm)

/-- Applying `classicalPointHomeomorph` returns `normClassicalPoint` at `a`. -/
@[simp]
theorem classicalPointHomeomorph_apply (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointHomeomorph a : closedPolydisc k K) = normClassicalPoint a.val a.property :=
  (rfl)

/-- The inverse of `classicalPointHomeomorph` recovers `a` from its classical point. -/
@[simp]
theorem classicalPointHomeomorph_symm_apply_normClassicalPoint
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    classicalPointHomeomorph.symm
        ⟨normClassicalPoint a.val a.property,
          mem_classicalPoints_iff.mpr ⟨a.val, a.property, rfl⟩⟩ = a :=
  classicalPointHomeomorph.symm_apply_apply a

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
  (rfl)

/-- The inverse of `classicalPointPowerBoundedHomeomorph` recovers `a` from its classical point. -/
@[simp]
theorem classicalPointPowerBoundedHomeomorph_symm_apply_normClassicalPoint
    (a : Fin k → powerBoundedSubring K) :
    classicalPointPowerBoundedHomeomorph.symm
        ⟨normClassicalPoint (fun i ↦ (a i : K))
            (fun i ↦ mem_powerBoundedSubring.mp (a i).property),
          mem_classicalPoints_iff.mpr
            ⟨fun i ↦ (a i : K), fun i ↦ mem_powerBoundedSubring.mp (a i).property, rfl⟩⟩ = a :=
  classicalPointPowerBoundedHomeomorph.symm_apply_apply a

/-- **The subspace `classicalPoints k K` of a closed polydisc is completely metrizable**, being
homeomorphic to the closed unit ball `(K°)ᵏ` of the complete metric space `Kᵏ`. -/
theorem isCompletelyMetrizableSpace_classicalPoints :
    TopologicalSpace.IsCompletelyMetrizableSpace (classicalPoints k K) := by
  have hclosed : IsClosed {a : Fin k → K | ∀ i, IsPowerBounded (a i)} := by
    have heq : {a : Fin k → K | ∀ i, IsPowerBounded (a i)} =
        Metric.closedBall (0 : Fin k → K) 1 := by
      ext a
      simp only [Set.mem_ofPred_eq, mem_closedBall_zero_iff,
        pi_norm_le_iff_of_nonneg zero_le_one, isPowerBounded_iff_norm_le_one]
    rw [heq]
    exact Metric.isClosed_closedBall
  have : CompleteSpace {a : Fin k → K // ∀ i, IsPowerBounded (a i)} := hclosed.completeSpace_coe
  exact (classicalPointHomeomorph (k := k)
    (K := K)).symm.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **The subspace `classicalPoints k K` of a closed polydisc is a Baire space**, by the Baire
category theorem for completely metrizable spaces. -/
theorem baireSpace_classicalPoints : BaireSpace (classicalPoints k K) := by
  have := isCompletelyMetrizableSpace_classicalPoints (k := k) (K := K)
  exact BaireSpace.of_completelyPseudoMetrizable

end Embedding

end TauCeti.ValuationSpectrum
