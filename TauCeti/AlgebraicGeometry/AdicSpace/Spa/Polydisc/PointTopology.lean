/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topology of the classical points of the closed unit polydisc

Let `K` be a complete ultrametric normed field and
`D = Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` the closed unit polydisc of dimension `n` over `K`. The
classical points attached to a point `x : Spa (K, K°)` are parametrised by tuples `a ∈ (K°)ⁿ`
through `TauCeti.ValuationSpectrum.classicalPoint x a ha`.

This file compares the valuation topology on `(K°)ⁿ` (equivalently `(𝒪[K])ⁿ`) with the
subspace topology on the image `D(K) ⊆ |D|`.

1. **Continuity in the argument.** Under the Gauss comparison, `evalAtHom a ha f` is
   `MvPowerSeries.restrictedEval₂` at `a`, so perturbing `a` changes `f(a)` by at most
   `‖a - b‖ * ‖f‖`. In particular, `a ↦ f(a)` is Lipschitz and hence continuous on `(K°)ⁿ`.
2. **Continuity of the classical-point map.** A basic open `Spv(K⟨T⟩)(f/s)` pulls back to
   `{a | ‖f(a)‖ ≤ ‖s(a)‖ ∧ 0 < ‖s(a)‖}`. By the ultrametric law, on a neighbourhood of `a` where
   `f` and `s` vary by strictly less than `‖s(a)‖`, the norm `‖s‖` stays constant and the weak
   inequality `‖f(b)‖ ≤ ‖s(b)‖` is preserved. Hence `a ↦ classicalPoint x a ha` is continuous;
   ordinary real continuity alone would not preserve weak inequalities. This step does not
   require `K` to be nontrivially normed.
3. **Topological embedding and completeness.** When `K` is nontrivially normed, for any
   `a₀ ∈ (K°)ⁿ` and `c ∈ Kˣ`, the rational subset `{|Tᵢ - a₀ᵢ| ≤ |c|}` cuts out on `D(K)` the
   closed metric ball of radius `‖c‖` about `a₀`. Because nonzero norms get arbitrarily small,
   `a ↦ classicalPoint x a ha` is a topological embedding and induces homeomorphisms from
   `(K°)ⁿ` and `(𝒪[K])ⁿ` onto `D(K)`. Since `(K°)ⁿ` is a closed ball in the complete finite
   product `Kⁿ`, the subspace `D(K)` is completely metrizable and a Baire space.
4. **Dimension zero.** For `n = 0`, `closedPolydisc 0 K` is a subsingleton, so the unique
   classical point exhausts the entire space.

## Main definitions

* `TauCeti.ValuationSpectrum.forallIsPowerBoundedHomeomorphPiInteger`: the coordinatewise
  homeomorphism `{a : Fin n → K // ∀ i, IsPowerBounded (a i)} ≃ₜ (Fin n → 𝒪[K])`.
* `TauCeti.ValuationSpectrum.classicalPointRangeHomeomorph`: for a complete nontrivially normed
  ultrametric field `K`, the homeomorphism from `{a : Fin n → K // ∀ i, IsPowerBounded (a i)}`
  onto the subspace of `K`-rational classical points of `closedPolydisc n K`.
* `TauCeti.ValuationSpectrum.classicalPointIntegerHomeomorph`: the same homeomorphism phrased
  with domain `Fin n → 𝒪[K]`.

## Main results

* `TauCeti.ValuationSpectrum.evalAtHom_eq_restrictedEval₂`: Huber evaluation `evalAtHom` agrees
  with normed evaluation `MvPowerSeries.restrictedEval₂` under the Gauss comparison.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_sub_le` and
  `TauCeti.ValuationSpectrum.lipschitzWith_evalAtHom_arg`: `a ↦ evalAtHom a ha f` is Lipschitz
  with constant `‖f‖`.
* `TauCeti.ValuationSpectrum.continuous_classicalPoint`: `a ↦ classicalPoint x a ha` is
  continuous for every ultrametric complete normed field `K`.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_rationalSubset_ball_iff`: the rational subset
  `{|Tᵢ - a₀ᵢ| ≤ |c|}` cuts out the closed ball of radius `‖c‖` around `a₀` in `D(K)`.
* `TauCeti.ValuationSpectrum.isEmbedding_classicalPoint`: for nontrivially normed complete `K`,
  `a ↦ classicalPoint x a ha` is a topological embedding.
* `TauCeti.ValuationSpectrum.isCompletelyMetrizableSpace_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.baireSpace_range_classicalPoint`: the subspace of `K`-rational
  classical points is completely metrizable and a Baire space.
* `TauCeti.ValuationSpectrum.subsingleton_closedPolydisc_zero` and
  `TauCeti.ValuationSpectrum.range_classicalPoint_zero_eq_univ`: in dimension `0`, the closed
  polydisc has at most one point, and the classical point exhausts it.

## References

* S. Howe and C. Klevdal, *p*-adic families of automorphic forms, proof of Lemma 9.3.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50,
  Definition 7.29, and Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Filter Topology
open scoped NormedField Valued

section NormedDivisionRing

variable {n : ℕ} {K : Type*} [NormedDivisionRing K]

/-- In a normed division ring, the tuples of power-bounded coordinates form the closed unit ball
of `Fin n → K`. -/
theorem setOf_forall_isPowerBounded_eq_closedBall :
    {a : Fin n → K | ∀ i, IsPowerBounded (a i)} = Metric.closedBall (0 : Fin n → K) 1 := by
  ext a
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg zero_le_one, isPowerBounded_iff_norm_le_one]

/-- The set of tuples of power-bounded coordinates is closed in `Fin n → K`. -/
theorem isClosed_setOf_forall_isPowerBounded :
    IsClosed {a : Fin n → K | ∀ i, IsPowerBounded (a i)} := by
  rw [setOf_forall_isPowerBounded_eq_closedBall]
  exact Metric.isClosed_closedBall

/-- Over a complete normed division ring, the subspace of power-bounded `n`-tuples is complete. -/
theorem completeSpace_subtype_forall_isPowerBounded [CompleteSpace K] :
    CompleteSpace {a : Fin n → K // ∀ i, IsPowerBounded (a i)} :=
  (isClosed_setOf_forall_isPowerBounded (n := n) (K := K)).completeSpace_coe

end NormedDivisionRing

section NormedField

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Coordinatewise identification between `{a : Fin n → K // ∀ i, IsPowerBounded (a i)}` and
`Fin n → 𝒪[K]` as a homeomorphism for the product and subspace topologies. -/
noncomputable def forallIsPowerBoundedHomeomorphPiInteger :
    {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ≃ₜ (Fin n → 𝒪[K]) where
  toFun a i := ⟨a.1 i, by
    rw [← powerBoundedSubring_eq_integer, mem_powerBoundedSubring]
    exact a.2 i⟩
  invFun a := ⟨fun i ↦ (a i : K), fun i ↦ by
    rw [← mem_powerBoundedSubring, powerBoundedSubring_eq_integer]
    exact (a i).2⟩
  left_inv a := by ext i; rfl
  right_inv a := by ext i; rfl
  continuous_toFun := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := Continuous.subtype_mk
    (continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)) _

/-- Forward evaluation of `forallIsPowerBoundedHomeomorphPiInteger` on coordinates. -/
@[simp]
theorem coe_forallIsPowerBoundedHomeomorphPiInteger_apply
    (a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)}) (i : Fin n) :
    ((forallIsPowerBoundedHomeomorphPiInteger a i : 𝒪[K]) : K) = a.1 i :=
  (rfl)

/-- Inverse evaluation of `forallIsPowerBoundedHomeomorphPiInteger` on coordinates. -/
@[simp]
theorem coe_forallIsPowerBoundedHomeomorphPiInteger_symm_apply (a : Fin n → 𝒪[K]) (i : Fin n) :
    (forallIsPowerBoundedHomeomorphPiInteger.symm a).1 i = (a i : K) :=
  (rfl)

variable [NonarchimedeanRing K]

/-- **In dimension `0`, the closed polydisc has at most one point.** Every series in `0` variables
is constant, and every point of `closedPolydisc 0 K` compares constants by their norms. -/
theorem subsingleton_closedPolydisc_zero : Subsingleton (closedPolydisc 0 K) := by
  refine ⟨fun v w ↦ Subtype.ext <| ext' fun f g ↦ ?_⟩
  have hconst (h : weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set K))
      isWeightFamily_one_weight) :
      h = weightedC _ isWeightFamily_one_weight
        (MvPowerSeries.constantCoeff (h : MvPowerSeries (Fin 0) K)) := by
    apply Subtype.ext
    ext ν
    rw [Subsingleton.elim ν 0]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hconst f, hconst g, closedPolydisc_vle_weightedC_iff, closedPolydisc_vle_weightedC_iff]

variable [CompleteSpace K]

/-- Huber evaluation `evalAtHom` agrees with normed evaluation `MvPowerSeries.restrictedEval₂`
through the unit-radius Gauss comparison. -/
theorem evalAtHom_eq_restrictedEval₂ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    evalAtHom a ha f =
      MvPowerSeries.restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl)
        (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i))
        (restrictedMvPowerSeriesGaussEquiv f) := by
  have heq : evalAtHom a ha =
      (MvPowerSeries.restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl)
        (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i))).comp
          restrictedMvPowerSeriesGaussEquiv.toRingHom :=
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (continuous_evalAtHom a ha)
      ((MvPowerSeries.continuous_restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl)
        (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i))).comp
          continuous_restrictedMvPowerSeriesGaussEquiv)
      (fun r ↦ by simp) (fun i ↦ by simp)
  exact RingHom.congr_fun heq f

/-- **Perturbation bound for `evalAtHom` in its argument:** changing `a` to `b` changes `f(a)` by
at most `‖a - b‖ * ‖f‖`. -/
theorem norm_evalAtHom_sub_le (a b : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (hb : ∀ i, IsPowerBounded (b i))
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    ‖evalAtHom a ha f - evalAtHom b hb f‖ ≤
      ‖a - b‖ * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [evalAtHom_eq_restrictedEval₂, evalAtHom_eq_restrictedEval₂]
  refine MvPowerSeries.norm_restrictedEval₂_sub_le (RingHom.id K) (fun _ ↦ le_rfl)
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i))
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (hb i)) (norm_nonneg (a - b)) (fun i ↦ ?_)
    (restrictedMvPowerSeriesGaussEquiv f)
  simpa only [mul_one, Pi.sub_apply] using norm_le_pi_norm (a - b) i

/-- Evaluation `a ↦ evalAtHom a ha f` is Lipschitz in its argument with constant `‖f‖`. -/
theorem lipschitzWith_evalAtHom_arg
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    LipschitzWith ‖restrictedMvPowerSeriesGaussEquiv f‖₊
      fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro a b
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, coe_nnNorm, mul_comm]
  exact norm_evalAtHom_sub_le a.1 b.1 a.2 b.2 f

/-- Evaluation `a ↦ evalAtHom a ha f` is uniformly continuous in its argument. -/
theorem uniformContinuous_evalAtHom_arg
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    UniformContinuous
      fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f :=
  (lipschitzWith_evalAtHom_arg f).uniformContinuous

/-- Evaluation `a ↦ evalAtHom a ha f` is continuous in its argument. -/
theorem continuous_evalAtHom_arg
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    Continuous
      fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦ evalAtHom a.1 a.2 f :=
  (lipschitzWith_evalAtHom_arg f).continuous

/-- **The classical-point map is continuous** from `(K°)ⁿ` (with the valuation topology) into
`closedPolydisc n K`.

The pullback of a basic open `Spv(K⟨T⟩)(f/s)` is `{a | ‖f(a)‖ ≤ ‖s(a)‖ ∧ 0 < ‖s(a)‖}`. By the
ultrametric inequality, perturbing `f(a)` and `s(a)` by strictly less than `‖s(a)‖` keeps
`‖s‖` constant and preserves the weak inequality `‖f‖ ≤ ‖s‖`. -/
theorem continuous_classicalPoint (x : spa (powerBoundedSubring K)) :
    Continuous fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2 := by
  rw [continuous_induced_rng, instTopologicalSpace_eq_generateFrom, continuous_generateFrom_iff]
  rintro _ ⟨f, s, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro a ha
  simp only [Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle,
    vle_iff_norm_le_of_mem_spa x.2, map_zero, norm_zero, not_le, norm_pos_iff] at ha
  obtain ⟨hfs, hs0⟩ := ha
  have hspos : 0 < ‖evalAtHom a.1 a.2 s‖ := norm_pos_iff.mpr hs0
  have hmem :
      ((fun b : {b : Fin n → K // ∀ i, IsPowerBounded (b i)} ↦ evalAtHom b.1 b.2 f) ⁻¹'
          Metric.ball (evalAtHom a.1 a.2 f) ‖evalAtHom a.1 a.2 s‖) ∩
        ((fun b : {b : Fin n → K // ∀ i, IsPowerBounded (b i)} ↦ evalAtHom b.1 b.2 s) ⁻¹'
          Metric.ball (evalAtHom a.1 a.2 s) ‖evalAtHom a.1 a.2 s‖) ∈ 𝓝 a :=
    Filter.inter_mem
      ((continuous_evalAtHom_arg f).continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hspos))
      ((continuous_evalAtHom_arg s).continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hspos))
  refine Filter.mem_of_superset hmem fun b ⟨hbf, hbs⟩ ↦ ?_
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hbf hbs
  have hsb : ‖evalAtHom b.1 b.2 s‖ = ‖evalAtHom a.1 a.2 s‖ := by
    have hsum : evalAtHom b.1 b.2 s =
        (evalAtHom b.1 b.2 s - evalAtHom a.1 a.2 s) + evalAtHom a.1 a.2 s := by ring
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hbs.ne, max_eq_right hbs.le]
  have hfb : ‖evalAtHom b.1 b.2 f‖ ≤ ‖evalAtHom b.1 b.2 s‖ := by
    have hsum : evalAtHom b.1 b.2 f =
        (evalAtHom b.1 b.2 f - evalAtHom a.1 a.2 f) + evalAtHom a.1 a.2 f := by ring
    rw [hsum, hsb]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbf.le hfs)
  simp only [Set.mem_preimage, mem_basicOpen_iff, classicalPoint_vle,
    vle_iff_norm_le_of_mem_spa x.2, map_zero, norm_zero, not_le]
  exact ⟨hfb, hsb.symm ▸ hspos⟩

open scoped Classical in
/-- A classical point `classicalPoint x a ha` lies in the finite-numerator basic open
`Spv(K⟨T⟩)({Tᵢ - a₀ᵢ} / c)` (for `c ≠ 0`) if and only if `‖aᵢ - a₀ᵢ‖ ≤ ‖c‖` for all `i`. -/
theorem classicalPoint_mem_basicOpenFinset_ball_iff (x : spa (powerBoundedSubring K))
    (a₀ a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) {c : K} (hc : c ≠ 0) :
    (classicalPoint x a ha).1 ∈
      basicOpenFinset
        (Finset.univ.image fun i : Fin n ↦
          weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i -
            weightedC _ isWeightFamily_one_weight (a₀ i))
        (weightedC _ isWeightFamily_one_weight c) ↔
      ∀ i : Fin n, ‖a i - a₀ i‖ ≤ ‖c‖ := by
  simp only [mem_basicOpenFinset_iff, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, classicalPoint_vle,
    vle_iff_norm_le_of_mem_spa x.2, map_sub, map_zero, evalAtHom_weightedX, evalAtHom_weightedC,
    norm_zero, not_le, norm_pos_iff]
  exact and_iff_left hc

open scoped Classical in
/-- **Rational closed balls cut out metric closed balls on `D(K)`.** For `c ≠ 0`, a classical
point `classicalPoint x a ha` lies in the rational subset `{|Tᵢ - a₀ᵢ| ≤ |c|}` of
`closedPolydisc n K` exactly when `‖aᵢ - a₀ᵢ‖ ≤ ‖c‖` for every coordinate `i`. -/
theorem classicalPoint_mem_rationalSubset_ball_iff (x : spa (powerBoundedSubring K))
    (a₀ a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)) {c : K} (hc : c ≠ 0) :
    (classicalPoint x a ha).1 ∈
      rationalSubset
        (powerBoundedSubring
          (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight))
        (Finset.univ.image fun i : Fin n ↦
          weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i -
            weightedC _ isWeightFamily_one_weight (a₀ i))
        (weightedC _ isWeightFamily_one_weight c) ↔
      ∀ i : Fin n, ‖a i - a₀ i‖ ≤ ‖c‖ := by
  rw [rationalSubset_def, Set.mem_inter_iff,
    and_iff_right (closedPolydisc_def n K ▸ (classicalPoint x a ha).2),
    classicalPoint_mem_basicOpenFinset_ball_iff x a₀ a ha hc]

/-- In dimension `0`, the range of the classical-point map is all of `closedPolydisc 0 K`. -/
theorem range_classicalPoint_zero_eq_univ (x : spa (powerBoundedSubring K)) :
    Set.range (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2) = Set.univ := by
  have := subsingleton_closedPolydisc_zero (K := K)
  refine Set.eq_univ_iff_forall.mpr fun p ↦ ?_
  refine ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩, Subsingleton.elim _ p⟩

end NormedField

section NontriviallyNormedField

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K] [CompleteSpace K]

/-- **The classical-point map is a topological embedding** from `(K°)ⁿ` into `closedPolydisc n K`
for any complete nontrivially normed ultrametric field `K`.

Injectivity is `classicalPoint_injective_of_isField`; continuity is `continuous_classicalPoint`;
and the subspace topology is at least as fine as the metric topology because the rational subsets
`{|Tᵢ - aᵢ| ≤ |c|}` (`c ∈ Kˣ`) cut out metric closed balls of arbitrarily small radius. -/
theorem isEmbedding_classicalPoint (x : spa (powerBoundedSubring K)) :
    Topology.IsEmbedding fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2 := by
  classical
  refine Topology.IsEmbedding.mk ?_ (classicalPoint_injective_of_isField (Field.toIsField K) x)
  rw [Topology.isInducing_iff_nhds]
  intro a
  refine le_antisymm ((continuous_classicalPoint x).continuousAt.le_comap) ?_
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨c, hc0, hcε⟩ := NormedField.exists_norm_lt K hε
  have hcne : c ≠ 0 := norm_pos_iff.mp hc0
  let T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight) :=
    Finset.univ.image fun i : Fin n ↦
      weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i -
        weightedC _ isWeightFamily_one_weight (a.1 i)
  let s := weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight c
  refine Filter.mem_comap.mpr ⟨Subtype.val ⁻¹' basicOpenFinset T s, ?_, ?_⟩
  · refine ((isOpen_basicOpenFinset T s).preimage continuous_subtype_val).mem_nhds ?_
    rw [Set.mem_preimage, classicalPoint_mem_basicOpenFinset_ball_iff x a.1 a.1 a.2 hcne]
    intro i
    simp [norm_nonneg]
  · intro b hb
    rw [Set.mem_preimage, Set.mem_preimage,
      classicalPoint_mem_basicOpenFinset_ball_iff x a.1 b.1 b.2 hcne] at hb
    refine hball ?_
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    exact ((pi_norm_le_iff_of_nonneg (norm_nonneg c)).mpr hb).trans_lt hcε

/-- **Homeomorphism between `(K°)ⁿ` and the subspace `D(K)` of `K`-rational classical points** of
the closed unit polydisc `closedPolydisc n K`. -/
noncomputable def classicalPointRangeHomeomorph (x : spa (powerBoundedSubring K)) :
    {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ≃ₜ
      Set.range (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) :=
  (isEmbedding_classicalPoint x).toHomeomorph

/-- The forward map of `classicalPointRangeHomeomorph` sends `a` to `classicalPoint x a.1 a.2`. -/
@[simp]
theorem coe_classicalPointRangeHomeomorph_apply (x : spa (powerBoundedSubring K))
    (a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)}) :
    ((classicalPointRangeHomeomorph x a :
        Set.range fun b : {b : Fin n → K // ∀ i, IsPowerBounded (b i)} ↦
          classicalPoint x b.1 b.2) : closedPolydisc n K) =
      classicalPoint x a.1 a.2 :=
  (rfl)

/-- **Homeomorphism between `(𝒪[K])ⁿ` and the subspace `D(K)` of `K`-rational classical points**
of the closed unit polydisc `closedPolydisc n K`. -/
noncomputable def classicalPointIntegerHomeomorph (x : spa (powerBoundedSubring K)) :
    (Fin n → 𝒪[K]) ≃ₜ
      Set.range (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) :=
  forallIsPowerBoundedHomeomorphPiInteger.symm.trans (classicalPointRangeHomeomorph x)

/-- The forward map of `classicalPointIntegerHomeomorph` sends an integral tuple
`a : Fin n → 𝒪[K]` to its classical point in `closedPolydisc n K`. -/
@[simp]
theorem coe_classicalPointIntegerHomeomorph_apply (x : spa (powerBoundedSubring K))
    (a : Fin n → 𝒪[K]) :
    ((classicalPointIntegerHomeomorph x a :
        Set.range fun b : {b : Fin n → K // ∀ i, IsPowerBounded (b i)} ↦
          classicalPoint x b.1 b.2) : closedPolydisc n K) =
      classicalPoint x (fun i ↦ (a i : K)) fun i ↦
        mem_powerBoundedSubring.mp ((powerBoundedSubring_eq_integer K).symm ▸ (a i).2) :=
  (rfl)

/-- **The subspace `D(K)` of `K`-rational classical points is completely metrizable.** -/
theorem isCompletelyMetrizableSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    TopologicalSpace.IsCompletelyMetrizableSpace
      (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) := by
  have : CompleteSpace {a : Fin n → K // ∀ i, IsPowerBounded (a i)} :=
    completeSpace_subtype_forall_isPowerBounded
  exact (classicalPointRangeHomeomorph x).symm.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **The subspace `D(K)` of `K`-rational classical points is a Baire space.** -/
theorem baireSpace_range_classicalPoint (x : spa (powerBoundedSubring K)) :
    BaireSpace
      (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.1 a.2) := by
  have := isCompletelyMetrizableSpace_range_classicalPoint (n := n) x
  exact BaireSpace.of_completelyPseudoMetrizable

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
