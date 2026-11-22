/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Topology of the rational points of a closed polydisc

Let `K` be a complete ultrametric normed field and `D = closedPolydisc k K` the closed unit
polydisc of dimension `k` over `K`. The classical points `a ↦ classicalPoint x a ha` parametrize
the `K`-rational points of `D` by the power-bounded tuples `a ∈ (K°)ᵏ`.

Because the norm on `K` is ultrametric, evaluating a fixed restricted power series `f ∈ K⟨T⟩` is
Lipschitz on the unit polydisc `(K°)ᵏ` with constant the unit Gauss norm of `f`. This implies that
every basic open `Spv(K⟨T⟩)(f/s)` pulls back to an open subset of `(K°)ᵏ`: at any point `a` with
`‖f(a)‖ ≤ ‖s(a)‖ ≠ 0`, on a small metric ball around `a` the value `s(b)` has constant norm
`‖s(a)‖` while `f(b)` changes by strictly less than `‖s(a)‖`, so the ultrametric inequality
preserves the weak inequality `‖f(b)‖ ≤ ‖s(b)‖`. Hence the classical-point map is continuous on
`(K°)ᵏ` over every complete ultrametric normed field, including trivially normed ones.

Conversely, for any `a₀ ∈ (K°)ᵏ` and any nonzero `c ∈ K`, the closed metric ball
`{a ∈ (K°)ᵏ | ∀ i, ‖a i - a₀ i‖ ≤ ‖c‖}` is the preimage under `classicalPoint x` of the rational
subset `R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)`. When `K` is nontrivially normed, nonzero scalars attain
arbitrarily small norms, so these rational traces form a neighbourhood basis of `a₀`. Combined with
injectivity (`TauCeti.ValuationSpectrum.classicalPoint_injective_of_isField`), the classical-point
map is a topological embedding and therefore a homeomorphism from `(K°)ᵏ` onto its image in `D`.
Because `(K°)ᵏ` is a closed subset of the complete metric space `Kᵏ`, the subspace of classical
points is completely metrizable and a Baire space.

## Main definitions

* `TauCeti.ValuationSpectrum.classicalPointHomeomorph`: for a complete nontrivially normed
  ultrametric field `K`, the homeomorphism from `{a : Fin k → K // ∀ i, IsPowerBounded (a i)}`
  onto the subspace of classical points of `closedPolydisc k K`.
* `TauCeti.ValuationSpectrum.classicalPointPowerBoundedHomeomorph`: the corresponding homeomorphism
  from `Fin k → powerBoundedSubring K` onto the subspace of classical points.

## Main results

* `TauCeti.ValuationSpectrum.evalAtHom_eq_restrictedEval₂`: over a complete ultrametric normed
  commutative ring, `evalAtHom` agrees with `MvPowerSeries.restrictedEval₂` through
  `restrictedMvPowerSeriesGaussEquiv`.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_le` and
  `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_evalAtHom_le`: evaluation of a restricted series on
  the unit polydisc is bounded by and Lipschitz with constant its unit Gauss norm.
* `TauCeti.ValuationSpectrum.lipschitzWith_evalAtHom_apply` and
  `TauCeti.ValuationSpectrum.continuous_evalAtHom_apply`: evaluation of a fixed restricted series
  is Lipschitz and continuous in the point `a ∈ (K°)ᵏ`.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_basicOpen_iff` and
  `TauCeti.ValuationSpectrum.classicalPoint_mem_rationalSubset_iff`: membership of a classical
  point in a basic open or rational subset expressed by norm inequalities on evaluations.
* `TauCeti.ValuationSpectrum.continuous_classicalPoint`: the classical-point map into
  `closedPolydisc k K` is continuous.
* `TauCeti.ValuationSpectrum.preimage_classicalPoint_rationalSubset_closedBall` and
  `TauCeti.ValuationSpectrum.closedBall_eq_preimage_classicalPoint_rationalSubset`: closed metric
  balls of radii `‖c‖` (`c ≠ 0`) in `(K°)ᵏ` are rational traces.
* `TauCeti.ValuationSpectrum.isEmbedding_classicalPoint`: when `K` is nontrivially normed, the
  classical-point map is a topological embedding.
* `TauCeti.ValuationSpectrum.isCompletelyMetrizableSpace_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.baireSpace_range_classicalPoint`: the subspace of classical points is
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

section EvalLipschitz

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- Over a complete ultrametric normed commutative ring, `evalAtHom` agrees with
`MvPowerSeries.restrictedEval₂` through `restrictedMvPowerSeriesGaussEquiv`. -/
theorem evalAtHom_eq_restrictedEval₂ {a : Fin k → R} (ha : ∀ i, IsPowerBounded (a i))
    (ha₁ : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    evalAtHom a ha f =
      MvPowerSeries.restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha₁
        (restrictedMvPowerSeriesGaussEquiv f) := by
  have heq : (evalAtHom a ha).comp restrictedMvPowerSeriesGaussEquiv.symm.toRingHom =
      MvPowerSeries.restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha₁ := by
    refine MvPowerSeries.eq_restrictedEval₂ _ _ _ _ _
      ((continuous_evalAtHom a ha).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm)
      (fun r ↦ ?_) (fun i ↦ ?_)
    · rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← restrictedMvPowerSeriesGaussEquiv_weightedC, RingEquiv.symm_apply_apply,
        evalAtHom_weightedC, RingHom.id_apply]
    · rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← restrictedMvPowerSeriesGaussEquiv_weightedX, RingEquiv.symm_apply_apply,
        evalAtHom_weightedX]
  have h := RingHom.congr_fun heq (restrictedMvPowerSeriesGaussEquiv f)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] using h

/-- **Evaluation on the closed unit polydisc is bounded by the unit Gauss norm.** -/
theorem norm_evalAtHom_le {a : Fin k → R} (ha : ∀ i, IsPowerBounded (a i))
    (ha₁ : ∀ i, ‖a i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f‖ ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ)) (f : MvPowerSeries (Fin k) R) := by
  rw [evalAtHom_eq_restrictedEval₂ ha ha₁ f]
  have h := MvPowerSeries.norm_restrictedEval₂_le (RingHom.id R) a (fun _ ↦ le_rfl) ha₁
    (restrictedMvPowerSeriesGaussEquiv f)
  rwa [MvPowerSeries.norm_eq_gaussNorm, coe_restrictedMvPowerSeriesGaussEquiv] at h

/-- **Evaluation of a restricted power series is Lipschitz on the closed unit polydisc**, with
Lipschitz constant its unit Gauss norm. -/
theorem norm_evalAtHom_sub_evalAtHom_le {a b : Fin k → R}
    (ha : ∀ i, IsPowerBounded (a i)) (hb : ∀ i, IsPowerBounded (b i))
    (ha₁ : ∀ i, ‖a i‖ ≤ 1) (hb₁ : ∀ i, ‖b i‖ ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤
      MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ)) (f : MvPowerSeries (Fin k) R) *
        ‖a - b‖ := by
  set f' := restrictedMvPowerSeriesGaussEquiv f
  have hsum : HasSum
      (fun ν : Fin k →₀ ℕ ↦ weightedEvalTerm (RingHom.id R) a (f' : MvPowerSeries (Fin k) R) ν -
        weightedEvalTerm (RingHom.id R) b (f' : MvPowerSeries (Fin k) R) ν)
      (evalAtHom a ha f - evalAtHom b hb f) := by
    rw [evalAtHom_eq_restrictedEval₂ ha ha₁ f, evalAtHom_eq_restrictedEval₂ hb hb₁ f]
    exact (MvPowerSeries.hasSum_restrictedEval₂ (RingHom.id R) a (fun _ ↦ le_rfl) ha₁ f').sub
      (MvPowerSeries.hasSum_restrictedEval₂ (RingHom.id R) b (fun _ ↦ le_rfl) hb₁ f')
  rw [← hsum.tsum_eq, ← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg f') (norm_nonneg (a - b))) fun ν ↦ ?_
  rw [weightedEvalTerm_def, weightedEvalTerm_def, RingHom.id_apply, ← mul_sub]
  have hmon : ‖∏ i, a i ^ ν i - ∏ i, b i ^ ν i‖ ≤ ‖a - b‖ := by
    rw [← Finsupp.prod_fintype ν (a · ^ ·) fun _ ↦ pow_zero _,
      ← Finsupp.prod_fintype ν (b · ^ ·) fun _ ↦ pow_zero _, Finsupp.prod, Finsupp.prod]
    simpa only [one_pow, mul_one] using TauCeti.norm_prod_sub_prod_le (s := ν.support)
      (M := 1) (ε := ‖a - b‖) (norm_nonneg _)
      (fun i hi ↦ (norm_pow_le' (a i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_one₀ (norm_nonneg _) (ha₁ i)))
      (fun i hi ↦ (norm_pow_le' (b i) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
        (pow_le_one₀ (norm_nonneg _) (hb₁ i)))
      (fun i _ ↦ by
        have hpow : ‖a i ^ ν i - b i ^ ν i‖ ≤ ‖a i - b i‖ := by
          simpa using TauCeti.norm_prod_sub_prod_le (s := Finset.range (ν i))
            (f := fun _ ↦ a i) (g := fun _ ↦ b i) (M := 1) (norm_nonneg _)
            (fun _ _ ↦ ha₁ i) (fun _ _ ↦ hb₁ i) (fun _ _ ↦ le_rfl)
        exact hpow.trans (norm_le_pi_norm (a - b) i))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ hmon (norm_nonneg _) (norm_nonneg f'))
  simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one] using
    MvPowerSeries.norm_coeff_mul_prod_le f' ν

end EvalLipschitz

section Continuity

variable {k : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is Lipschitz on
`(K°)ᵏ` with constant the unit Gauss norm of `f`. -/
theorem lipschitzWith_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    LipschitzWith
      (Real.toNNReal (MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ))
        (f : MvPowerSeries (Fin k) K)))
      fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.val a.property f := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  have hnonneg : 0 ≤ MvPowerSeries.gaussNorm norm (fun _ : Fin k ↦ (1 : ℝ))
      (f : MvPowerSeries (Fin k) K) := by
    rw [← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
    exact norm_nonneg _
  rw [Real.coe_toNNReal _ hnonneg, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  exact norm_evalAtHom_sub_evalAtHom_le a.property b.property
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (a.property i))
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (b.property i)) f

/-- For a fixed restricted power series `f ∈ K⟨T₁, …, Tₖ⟩`, evaluation `a ↦ f(a)` is continuous on
`(K°)ᵏ`. -/
theorem continuous_evalAtHom_apply
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      evalAtHom a.val a.property f :=
  (lipschitzWith_evalAtHom_apply f).continuous

/-- Membership of a classical point in a basic open `Spv(K⟨T⟩)(f/s)` is the norm inequality
`‖f(a)‖ ≤ ‖s(a)‖` together with `s(a) ≠ 0`. -/
theorem classicalPoint_mem_basicOpen_iff (x : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (classicalPoint x a ha).val ∈ basicOpen f s ↔
      ‖evalAtHom a ha f‖ ≤ ‖evalAtHom a ha s‖ ∧ evalAtHom a ha s ≠ 0 := by
  simp only [mem_basicOpen_iff, classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.property,
    map_zero, norm_zero, norm_le_zero_iff]

/-- Membership of a classical point in a rational subset `R(T/s)` of `closedPolydisc k K` is the
family of norm inequalities `‖t(a)‖ ≤ ‖s(a)‖` for `t ∈ T` together with `s(a) ≠ 0`. -/
theorem classicalPoint_mem_rationalSubset_iff (x : spa (powerBoundedSubring K)) (a : Fin k → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (classicalPoint x a ha).val ∈ rationalSubset (powerBoundedSubring _) T s ↔
      (∀ t ∈ T, ‖evalAtHom a ha t‖ ≤ ‖evalAtHom a ha s‖) ∧ evalAtHom a ha s ≠ 0 := by
  have hmem : (classicalPoint x a ha).val ∈ spa (powerBoundedSubring _) :=
    closedPolydisc_def k K ▸ (classicalPoint x a ha).property
  simp only [mem_rationalSubset_iff, hmem, true_and, classicalPoint_vle,
    vle_iff_norm_le_of_mem_spa x.property, map_zero, norm_zero, norm_le_zero_iff]

/-- **The classical-point map into the closed polydisc is continuous.** On a small metric ball
around `a` where `‖f(b) - f(a)‖ < ‖s(a)‖` and `‖s(b) - s(a)‖ < ‖s(a)‖`, the ultrametric law keeps
`‖s(b)‖ = ‖s(a)‖` and preserves the weak inequality `‖f(b)‖ ≤ ‖s(b)‖`. This holds over every
complete ultrametric normed field, without assuming a nontrivial norm. -/
theorem continuous_classicalPoint (x : spa (powerBoundedSubring K)) :
    Continuous fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property := by
  refine Continuous.subtype_mk (continuous_generateFrom_iff.mpr ?_) _
  rintro _ ⟨f, s, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro a ha
  rw [Set.mem_preimage, classicalPoint_mem_basicOpen_iff] at ha
  obtain ⟨hle, hs⟩ := ha
  have hr : 0 < ‖evalAtHom a.val a.property s‖ := norm_pos_iff.mpr hs
  have hf_nhds := (continuous_evalAtHom_apply f).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds (evalAtHom a.val a.property f) hr)
  have hs_nhds := (continuous_evalAtHom_apply s).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds (evalAtHom a.val a.property s) hr)
  refine Filter.mem_of_superset (Filter.inter_mem hf_nhds hs_nhds) fun b ⟨hfb, hsb⟩ ↦ ?_
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hfb hsb
  rw [Set.mem_preimage, classicalPoint_mem_basicOpen_iff]
  have hs_eq : ‖evalAtHom b.val b.property s‖ = ‖evalAtHom a.val a.property s‖ := by
    rw [← add_sub_cancel (evalAtHom a.val a.property s) (evalAtHom b.val b.property s),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsb.ne', max_eq_left hsb.le]
  refine ⟨?_, norm_pos_iff.mp (hs_eq ▸ hr)⟩
  rw [hs_eq, ← add_sub_cancel (evalAtHom a.val a.property f) (evalAtHom b.val b.property f)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hle hfb.le)

open scoped Classical in
/-- **A rational ball cuts out a closed metric ball among classical points.** For any centre
`a₀ : Fin k → K` and nonzero `c : K`, the rational subset `R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)`
pulls back along `classicalPoint x` to the closed polydisc of radius `‖c‖` about `a₀`. -/
theorem preimage_classicalPoint_rationalSubset_closedBall
    (x : spa (powerBoundedSubring K)) (a₀ : Fin k → K) {c : K} (hc : c ≠ 0) :
    (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
          (classicalPoint x a.val a.property).val) ⁻¹'
        rationalSubset (powerBoundedSubring _)
          (Finset.univ.image fun i : Fin k ↦
            weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
              weightedC _ isWeightFamily_one_weight (a₀ i))
          (weightedC _ isWeightFamily_one_weight c) =
      {a | ∀ i, ‖a.val i - a₀ i‖ ≤ ‖c‖} := by
  ext a
  simp only [Set.mem_preimage, classicalPoint_mem_rationalSubset_iff, evalAtHom_weightedC,
    Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff,
    map_sub, evalAtHom_weightedX, hc, ne_eq, not_false_eq_true, and_true, Set.mem_ofPred_eq]

open scoped Classical in
/-- For a point `a₀ ∈ (K°)ᵏ` and nonzero `c : K`, the closed metric ball `Metric.closedBall a₀ ‖c‖`
is the preimage under `classicalPoint x` of the rational subset
`R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)`. -/
theorem closedBall_eq_preimage_classicalPoint_rationalSubset
    (x : spa (powerBoundedSubring K)) (a₀ : {a : Fin k → K // ∀ i, IsPowerBounded (a i)})
    {c : K} (hc : c ≠ 0) :
    Metric.closedBall a₀ ‖c‖ =
      (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.val a.property) ⁻¹'
        (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
          (Finset.univ.image fun i : Fin k ↦
            weightedX (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight i -
              weightedC _ isWeightFamily_one_weight (a₀.val i))
          (weightedC _ isWeightFamily_one_weight c)) := by
  rw [Set.preimage_preimage, preimage_classicalPoint_rationalSubset_closedBall x a₀.val hc]
  ext a
  simp only [Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm,
    pi_norm_le_iff_of_nonneg (norm_nonneg c), Pi.sub_apply, Set.mem_ofPred_eq]

end Continuity

section RationalBall

open scoped Classical in
/-- The rational subset `R({T₁ - a₀₁, …, Tₖ - a₀ₖ} / c)` with unit denominator `c` belongs to the
rational family of `Spa (R⟨T₁, …, Tₖ⟩, R⟨T⟩°)`. -/
theorem val_preimage_rationalSubset_closedBall_mem_spaRationalFamily {k : ℕ} {R : Type*}
    [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    (a₀ : Fin k → R) {c : R} (hc : IsUnit c) :
    (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _)
        (Finset.univ.image fun i : Fin k ↦
          weightedX (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight i -
            weightedC _ isWeightFamily_one_weight (a₀ i))
        (weightedC _ isWeightFamily_one_weight c) : Set (spa (powerBoundedSubring _))) ∈
      spaRationalFamily (powerBoundedSubring _) :=
  val_preimage_rationalSubset_mem_spaRationalFamily_of_isUnit _ _
    (hc.map (weightedC _ isWeightFamily_one_weight))

/-- Every rational subset `R(T/s)` has open trace on `closedPolydisc k R`. -/
theorem isOpen_val_preimage_rationalSubset_closedPolydisc {k : ℕ} {R : Type*}
    [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    (T : Finset (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    IsOpen (Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s :
      Set (closedPolydisc k R)) := by
  rw [closedPolydisc_def]
  exact isOpen_val_preimage_rationalSubset _ T s

end RationalBall

section Embedding

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The classical-point map is a topological embedding** over a complete nontrivially normed
ultrametric field. Rational balls `R({Tᵢ - a₀ᵢ} / c)` cut out closed metric balls of arbitrarily
small radius `‖c‖`, so the subspace topology on the classical points agrees with the valuation
topology on `(K°)ᵏ`. -/
theorem isEmbedding_classicalPoint (x : spa (powerBoundedSubring K)) :
    Topology.IsEmbedding fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property := by
  classical
  refine ⟨Topology.isInducing_iff_nhds.mpr fun a₀ ↦ le_antisymm
      (continuous_classicalPoint x).continuousAt.tendsto.le_comap ?_,
      classicalPoint_injective_of_isField (Field.toIsField K) x⟩
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
        classicalPoint x a.val a.property) ⁻¹' U :=
    closedBall_eq_preimage_classicalPoint_rationalSubset x a₀ hc
  have hU_open : IsOpen U := isOpen_val_preimage_rationalSubset_closedPolydisc _ _
  have ha₀U : classicalPoint x a₀.val a₀.property ∈ U := by
    have : a₀ ∈ Metric.closedBall a₀ ‖c‖ := Metric.mem_closedBall_self (norm_nonneg c)
    rwa [hpre, Set.mem_preimage] at this
  refine Filter.mem_comap.mpr ⟨U, hU_open.mem_nhds ha₀U, ?_⟩
  rw [← hpre]
  exact (Metric.closedBall_subset_ball hcε).trans hball

/-- **The homeomorphism between `(K°)ᵏ` and the classical points of the closed polydisc**, over a
complete nontrivially normed ultrametric field. -/
noncomputable def classicalPointHomeomorph (x : spa (powerBoundedSubring K)) :
    {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ≃ₜ
      Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) :=
  (isEmbedding_classicalPoint x).toHomeomorph

/-- Applying `classicalPointHomeomorph` returns the classical point at `a`. -/
@[simp]
theorem classicalPointHomeomorph_apply (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointHomeomorph x a : closedPolydisc k K) = classicalPoint x a.val a.property := (rfl)

/-- The inverse of `classicalPointHomeomorph` recovers `a` from its classical point. -/
@[simp]
theorem classicalPointHomeomorph_symm_apply_classicalPoint (x : spa (powerBoundedSubring K))
    (a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)}) :
    (classicalPointHomeomorph x).symm ⟨classicalPoint x a.val a.property, ⟨a, rfl⟩⟩ = a :=
  (classicalPointHomeomorph x).symm_apply_apply a

/-- **The homeomorphism between `Fin k → powerBoundedSubring K` and the classical points of the
closed polydisc**, over a complete nontrivially normed ultrametric field. -/
noncomputable def classicalPointPowerBoundedHomeomorph (x : spa (powerBoundedSubring K)) :
    (Fin k → powerBoundedSubring K) ≃ₜ
      Set.range (fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) :=
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
    (classicalPointHomeomorph x)

/-- Applying `classicalPointPowerBoundedHomeomorph` returns the classical point at the tuple of
underlying elements of `K`. -/
@[simp]
theorem classicalPointPowerBoundedHomeomorph_apply (x : spa (powerBoundedSubring K))
    (a : Fin k → powerBoundedSubring K) :
    (classicalPointPowerBoundedHomeomorph x a : closedPolydisc k K) =
      classicalPoint x (fun i ↦ (a i : K)) (fun i ↦ mem_powerBoundedSubring.mp (a i).property) :=
  (rfl)

/-- The inverse of `classicalPointPowerBoundedHomeomorph` recovers `a` from its classical point. -/
@[simp]
theorem classicalPointPowerBoundedHomeomorph_symm_apply_classicalPoint
    (x : spa (powerBoundedSubring K)) (a : Fin k → powerBoundedSubring K) :
    (classicalPointPowerBoundedHomeomorph x).symm
        ⟨classicalPoint x (fun i ↦ (a i : K)) (fun i ↦ mem_powerBoundedSubring.mp (a i).property),
          ⟨⟨fun i ↦ (a i : K), fun i ↦ mem_powerBoundedSubring.mp (a i).property⟩, rfl⟩⟩ = a :=
  (classicalPointPowerBoundedHomeomorph x).symm_apply_apply a

/-- **The subspace of classical points of a closed polydisc is completely metrizable**, being
homeomorphic to the closed unit ball `(K°)ᵏ` of the complete metric space `Kᵏ`. -/
theorem isCompletelyMetrizableSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    TopologicalSpace.IsCompletelyMetrizableSpace
      (Set.range fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) := by
  have hclosed : IsClosed {a : Fin k → K | ∀ i, IsPowerBounded (a i)} := by
    have heq : {a : Fin k → K | ∀ i, IsPowerBounded (a i)} =
        Metric.closedBall (0 : Fin k → K) 1 := by
      ext a
      simp only [Set.mem_ofPred_eq, mem_closedBall_zero_iff,
        pi_norm_le_iff_of_nonneg zero_le_one, isPowerBounded_iff_norm_le_one]
    rw [heq]
    exact Metric.isClosed_closedBall
  have : CompleteSpace {a : Fin k → K // ∀ i, IsPowerBounded (a i)} := hclosed.completeSpace_coe
  exact (classicalPointHomeomorph x).symm.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **The subspace of classical points of a closed polydisc is a Baire space**, by the Baire
category theorem for completely metrizable spaces. -/
theorem baireSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    BaireSpace
      (Set.range fun a : {a : Fin k → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) := by
  have := isCompletelyMetrizableSpace_range_classicalPoint (k := k) x
  exact BaireSpace.of_completelyPseudoMetrizable

end Embedding

end TauCeti.ValuationSpectrum
