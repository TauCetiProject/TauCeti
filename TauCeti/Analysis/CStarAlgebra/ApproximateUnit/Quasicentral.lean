/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.CStarAlgebra.ApproximateUnit.Basic
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Decomposition
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Unitization
import TauCeti.Analysis.CStarAlgebra.Representation.Ideal
import TauCeti.Analysis.LocallyConvex.Mazur
import TauCeti.Analysis.Normed.Ring.ApproximateUnit
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Quasicentral approximate units for closed two-sided ideals

Let `A` be a (possibly nonunital) complex C⋆-algebra and `I : TwoSidedIdeal A` a closed two-sided
ideal. A positive contractive approximate unit of `I` is *quasicentral* in `A` if
`e * a - a * e → 0` in norm for every `a : A`. Arveson's theorem asserts that every closed
two-sided ideal admits a quasicentral approximate unit, and when `A` is separable it admits a
monotone increasing sequence of positive strict contractions forming a quasicentral approximate
unit.

The proof follows Arveson's Hahn–Banach / Mazur convexification argument:

1. Along any eventually norm-bounded left approximate unit `l` of `I` (and in particular along any
   increasing approximate unit of `I`), the commutators `e * a - a * e` converge weakly to `0` in
   `A` (`TwoSidedIdeal.tendsto_toWeakSpace_commutator` and
   `TwoSidedIdeal.tendsto_toWeakSpace_commutator_of_isIncreasingApproximateUnit`).
   By the positive-functional characterization of weak convergence
   (`TauCeti.CStarAlgebra.tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap`), it suffices
   to test against positive continuous linear functionals `ω : A →P[ℂ] ℂ`. Passing to the
   restricted GNS representation `ω.gnsInr`, its further restriction `πS` to `I` converges strongly
   along `l` to the essential projection `P := πS.nonUnitalMultiplierExtension 1`
   (`NonUnitalStarAlgHom.tendsto_nonUnitalMultiplierExtension_apply`). Because `I` is a two-sided
   ideal, `P` commutes with `ω.gnsInr a`
   (`NonUnitalStarAlgHom.commute_nonUnitalMultiplierExtension_one`), so `ω (e * a - a * e) → 0`.
2. Applying Mazur's lemma (`TauCeti.mem_closure_convexHull_range_of_tendsto_weak`) in the finite
   product `F → A` produces positive strict contractions in `I` above any given positive strict
   contraction `e₀ ∈ I` whose commutators with all elements of `F` have norm `< ε`
   (`TwoSidedIdeal.exists_ge_norm_lt_one_commutator_lt`).
3. These sections form a filter basis for `TwoSidedIdeal.quasicentralApproximateUnit I : Filter A`,
   whose pullback to `I.toNonUnitalStarSubalgebra` refines the canonical approximate unit of `I`,
   yielding `TwoSidedIdeal.exists_quasicentral_approximateUnit` and, in the separable case,
   `TwoSidedIdeal.exists_seq_quasicentral_approximateUnit`.

## Main declarations

* `TwoSidedIdeal.tendsto_toWeakSpace_commutator` and
  `TwoSidedIdeal.tendsto_toWeakSpace_commutator_of_isIncreasingApproximateUnit`: commutators with
  any eventually norm-bounded left approximate unit (or increasing approximate unit) of a closed
  two-sided ideal tend weakly to `0`.
* `TwoSidedIdeal.exists_ge_norm_lt_one_commutator_lt`: finite-set commutator approximation by a
  positive strict contraction above a given positive strict contraction in a closed two-sided ideal.
* `TwoSidedIdeal.quasicentralApproximateUnit`: the canonical quasicentral approximate unit filter
  of a closed two-sided ideal, with basis `TwoSidedIdeal.hasBasis_quasicentralApproximateUnit` and
  universal property `TwoSidedIdeal.le_quasicentralApproximateUnit_iff`.
* `TwoSidedIdeal.exists_quasicentral_approximateUnit`: existence of a positive contractive
  quasicentral approximate unit filter for any closed two-sided ideal.
* `TwoSidedIdeal.exists_seq_quasicentral_approximateUnit`: in a separable C⋆-algebra, every closed
  two-sided ideal admits a monotone increasing sequential quasicentral approximate unit.

## References

* William Arveson, *Notes on extensions of C*-algebras*, Duke Math. J. 44 (1977), 329–355,
  Theorem 1.
* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.4.3, Proposition II.4.3.2.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace BigOperators

namespace TwoSidedIdeal

section WeakConvergence

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)]

/-- Along any eventually norm-bounded left approximate unit of a closed two-sided ideal `I`, the
commutators `e * a - a * e` converge weakly to `0` in `A` for every `a : A`. -/
theorem tendsto_toWeakSpace_commutator {l : Filter I.toNonUnitalStarSubalgebra} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ x : I.toNonUnitalStarSubalgebra, Tendsto (· * x) l (𝓝 x)) (a : A) :
    Tendsto (fun e : I.toNonUnitalStarSubalgebra =>
        toWeakSpace ℂ A ((e : A) * a - a * (e : A)))
      l (𝓝 (toWeakSpace ℂ A 0)) := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  let S := I.toNonUnitalStarSubalgebra
  rw [TauCeti.CStarAlgebra.tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap]
  intro ω
  rw [map_zero]
  let f : A⁺¹ →ₚ[ℂ] ℂ := ω.extendUnitization.toPositiveLinearMap
  let πS : S →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    ω.gnsInr.comp (NonUnitalStarSubalgebraClass.subtype S)
  let P : f.GNS →L[ℂ] f.GNS := πS.nonUnitalMultiplierExtension 1
  let T : f.GNS →L[ℂ] f.GNS := ω.gnsInr a
  have hPT : P * T = T * P :=
    (ω.gnsInr.commute_nonUnitalMultiplierExtension_one I.mul_mem_toNonUnitalStarSubalgebra a).eq
  -- In the GNS representation `ω.gnsInr`, `πS e → P` strongly along `l`.
  have hstrong : ∀ ξ : f.GNS, Tendsto (fun e : S => πS e ξ) l (𝓝 (P ξ)) := fun ξ => by
    simpa only [DoubleCentralizer.one_fst, one_apply_eq_self] using
      πS.tendsto_nonUnitalMultiplierExtension_apply hC hl 1 ξ
  -- Evaluate `ω (e * a - a * e)` as a difference of inner products and pass to the limit.
  have hterm : ∀ e : S, ω ((e : A) * a - a * (e : A)) =
      ⟪f.gnsVector, πS e (T f.gnsVector)⟫_ℂ - ⟪f.gnsVector, T (πS e f.gnsVector)⟫_ℂ := fun e => by
    simp only [πS, T, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype]
    rw [map_sub, ← ω.inner_gnsVector_gnsInr, ← ω.inner_gnsVector_gnsInr,
      map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
  have hinner₁ : Tendsto (fun e : S => ⟪f.gnsVector, πS e (T f.gnsVector)⟫_ℂ) l
      (𝓝 ⟪f.gnsVector, P (T f.gnsVector)⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp (hstrong (T f.gnsVector))
  have hinner₂ : Tendsto (fun e : S => ⟪f.gnsVector, T (πS e f.gnsVector)⟫_ℂ) l
      (𝓝 ⟪f.gnsVector, T (P f.gnsVector)⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp
      ((T.continuous.tendsto _).comp (hstrong f.gnsVector))
  have hdiff := hinner₁.sub hinner₂
  have hzero : ⟪f.gnsVector, P (T f.gnsVector)⟫_ℂ - ⟪f.gnsVector, T (P f.gnsVector)⟫_ℂ = 0 := by
    have hEq : P (T f.gnsVector) = T (P f.gnsVector) := by
      simpa only [mul_apply_eq_comp] using
        congrArg (fun op : f.GNS →L[ℂ] f.GNS => op f.gnsVector) hPT
    rw [hEq, sub_self]
  rw [hzero] at hdiff
  exact hdiff.congr fun e => (hterm e).symm

/-- Along any increasing approximate unit of a closed two-sided ideal `I`, the commutators
`e * a - a * e` converge weakly to `0` in `A` for every `a : A`. -/
theorem tendsto_toWeakSpace_commutator_of_isIncreasingApproximateUnit [PartialOrder A]
    {l : Filter I.toNonUnitalStarSubalgebra} (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e : I.toNonUnitalStarSubalgebra =>
        toWeakSpace ℂ A ((e : A) * a - a * (e : A)))
      l (𝓝 (toWeakSpace ℂ A 0)) :=
  have := hl.neBot
  I.tendsto_toWeakSpace_commutator hl.eventually_norm hl.tendsto_mul_right a

end WeakConvergence

section Quasicentral

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)]

/-- Given a positive strict contraction `e₀` in a closed two-sided ideal `I`, a finite set `F` of
elements of `A`, and `ε > 0`, there exists a positive contraction `e ∈ I` above `e₀` whose
commutator with every element of `F` has norm strictly less than `ε`. -/
private theorem exists_ge_norm_le_one_commutator_lt {e₀ : A} (he₀I : e₀ ∈ I) (he₀₀ : 0 ≤ e₀)
    (he₀₁ : ‖e₀‖ < 1) (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ e ∈ I, e₀ ≤ e ∧ ‖e‖ ≤ 1 ∧ ∀ a ∈ F, ‖e * a - a * e‖ < ε := by
  classical
  -- 1. Weak convergence of commutators along the approximate-unit tail `U = {e ≥ e₀ | ‖e‖ ≤ 1}`.
  let S := I.toNonUnitalStarSubalgebra
  let s₀ : S := ⟨e₀, I.mem_toNonUnitalStarSubalgebra.mpr he₀I⟩
  let U : Set S := {e : S | s₀ ≤ e ∧ ‖e‖ ≤ 1}
  have hU_mem : U ∈ CStarAlgebra.approximateUnit S := by
    have hU_eq : U = {x : S | s₀ ≤ x} ∩ Metric.closedBall 0 1 := by
      ext x
      simp [U, Metric.mem_closedBall]
    rw [hU_eq]
    exact (CStarAlgebra.hasBasis_approximateUnit S).mem_of_mem ⟨he₀₀, he₀₁⟩
  let lU : Filter U := (CStarAlgebra.approximateUnit S).comap ((↑) : U → S)
  have hlU_neBot : lU.NeBot :=
    Filter.comap_coe_neBot_of_le_principal (le_principal_iff.mpr hU_mem)
  let φ : U → (F → A) := fun e a => ((e.val : A) * a.val - a.val * (e.val : A))
  have hweak : Tendsto (fun e : U => toWeakSpace ℂ (F → A) (φ e)) lU
      (𝓝 (toWeakSpace ℂ (F → A) 0)) :=
    TauCeti.tendsto_toWeakSpace_pi_iff.mpr fun a =>
      (I.tendsto_toWeakSpace_commutator_of_isIncreasingApproximateUnit
        (CStarAlgebra.increasingApproximateUnit S) a.val).comp tendsto_comap
  -- 2. Apply Mazur's lemma to find a convex combination with small commutator norms on `F`.
  have h0_mem : (0 : F → A) ∈ closure (convexHull ℝ (Set.range φ)) :=
    TauCeti.mem_closure_convexHull_range_of_tendsto_weak hweak
  obtain ⟨y, hy_ball, hy_hull⟩ :=
    mem_closure_iff_nhds.mp h0_mem (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rw [convexHull_range_eq_exists_affineCombination] at hy_hull
  obtain ⟨s, w, hw, hsum, rfl⟩ := hy_hull
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hy_ball
  -- 3. Verify that the convex combination lies in `I`, dominates `e₀`, and is a contraction.
  let e : S := ∑ i ∈ s, w i • i.val
  have he_ge : s₀ ≤ e := by
    have h1 : s₀ = ∑ i ∈ s, w i • s₀ := by rw [← Finset.sum_smul, hsum, one_smul]
    rw [h1]
    exact Finset.sum_le_sum fun i hi => smul_le_smul_of_nonneg_left i.property.1 (hw i hi)
  have he_coe : (e : A) = ∑ i ∈ s, w i • (i.val : A) := by simp [e]
  have he_norm : ‖(e : A)‖ ≤ 1 := by
    calc ‖(e : A)‖ = ‖∑ i ∈ s, w i • (i.val : A)‖ := by rw [he_coe]
      _ ≤ ∑ i ∈ s, ‖w i • (i.val : A)‖ := norm_sum_le s _
      _ = ∑ i ∈ s, w i * ‖(i.val : A)‖ := Finset.sum_congr rfl fun i hi => by
          rw [norm_smul, Real.norm_of_nonneg (hw i hi)]
      _ ≤ ∑ i ∈ s, w i * 1 := Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left i.property.2 (hw i hi)
      _ = 1 := by simp [hsum]
  refine ⟨(e : A), I.mem_toNonUnitalStarSubalgebra.mp e.property, he_ge, he_norm, fun a ha => ?_⟩
  have hcomm : (e : A) * a - a * (e : A) = (∑ i ∈ s, w i • φ i) ⟨a, ha⟩ := by
    simp only [he_coe, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_apply, Pi.smul_apply, φ, smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hcomm]
  have hy_lt : ‖∑ i ∈ s, w i • φ i‖ < ε := by simpa [Metric.mem_ball] using hy_ball
  exact (norm_le_pi_norm (∑ i ∈ s, w i • φ i) ⟨a, ha⟩).trans_lt hy_lt

/-- Given a positive strict contraction `e₀` in a closed two-sided ideal `I`, a finite set `F` of
elements of `A`, and `ε > 0`, there exists a positive strict contraction `e ∈ I` above `e₀` whose
commutator with every element of `F` has norm strictly less than `ε`. -/
theorem exists_ge_norm_lt_one_commutator_lt {e₀ : A} (he₀I : e₀ ∈ I) (he₀₀ : 0 ≤ e₀)
    (he₀₁ : ‖e₀‖ < 1) (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ e ∈ I, e₀ ≤ e ∧ ‖e‖ < 1 ∧ ∀ a ∈ F, ‖e * a - a * e‖ < ε := by
  let t : ℝ := (1 + ‖e₀‖) / 2
  have ht_pos : 0 < t := by
    have := norm_nonneg e₀
    positivity
  have ht_lt : t < 1 := by
    dsimp [t]
    linarith
  have he₀'_mem : t⁻¹ • e₀ ∈ I := by
    rw [← Complex.coe_smul]
    exact I.smul_mem_of_isClosed _ he₀I
  have he₀'_nonneg : 0 ≤ t⁻¹ • e₀ := smul_nonneg (inv_nonneg.mpr ht_pos.le) he₀₀
  have he₀'_norm : ‖t⁻¹ • e₀‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht_pos.le), inv_mul_lt_iff₀ ht_pos, mul_one]
    dsimp [t]
    linarith
  obtain ⟨e, heI, he_ge, he_norm, he_comm⟩ :=
    I.exists_ge_norm_le_one_commutator_lt he₀'_mem he₀'_nonneg he₀'_norm F hε
  refine ⟨t • e, ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [← Complex.coe_smul]
    exact I.smul_mem_of_isClosed _ heI
  · simpa [smul_smul, mul_inv_cancel₀ ht_pos.ne'] using
      smul_le_smul_of_nonneg_left he_ge ht_pos.le
  · rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
    exact (mul_le_of_le_one_right ht_pos.le he_norm).trans_lt ht_lt
  · have hEq : (t • e) * a - a * (t • e) = t • (e * a - a * e) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [hEq, norm_smul, Real.norm_of_nonneg ht_pos.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht_lt.le).trans_lt (he_comm a ha)

/-- Filter basis generating the canonical quasicentral approximate unit of a closed two-sided
ideal `I`. -/
private lemma isBasis_quasicentralApproximateUnit :
    IsBasis (fun p : {e₀ : A // e₀ ∈ I ∧ 0 ≤ e₀ ∧ ‖e₀‖ < 1} × Finset A × ℝ => 0 < p.snd.snd)
      (fun p => {e : A | e ∈ I ∧ (p.fst : A) ≤ e ∧ ‖e‖ ≤ 1 ∧
        ∀ a ∈ p.snd.fst, ‖e * a - a * e‖ < p.snd.snd}) where
  nonempty := ⟨(⟨0, I.zero_mem, le_rfl, by simp⟩, ∅, 1), zero_lt_one⟩
  inter {p q} hp hq := by
    classical
    let S := I.toNonUnitalStarSubalgebra
    let x : S := ⟨p.fst.val, I.mem_toNonUnitalStarSubalgebra.mpr p.fst.property.1⟩
    let y : S := ⟨q.fst.val, I.mem_toNonUnitalStarSubalgebra.mpr q.fst.property.1⟩
    have hx : x ∈ {z : S | 0 ≤ z} ∩ Metric.ball 0 1 :=
      ⟨p.fst.property.2.1, by simpa [x] using p.fst.property.2.2⟩
    have hy : y ∈ {z : S | 0 ≤ z} ∩ Metric.ball 0 1 :=
      ⟨q.fst.property.2.1, by simpa [y] using q.fst.property.2.2⟩
    obtain ⟨z, ⟨hz₀, hz₁⟩, hxz, hyz⟩ := CStarAlgebra.directedOn_nonneg_ball x hx y hy
    have hxz' : (p.fst : A) ≤ (z : A) := hxz
    have hyz' : (q.fst : A) ≤ (z : A) := hyz
    refine ⟨(⟨z.val, I.mem_toNonUnitalStarSubalgebra.mp z.property, hz₀, by simpa using hz₁⟩,
      p.snd.fst ∪ q.snd.fst, min p.snd.snd q.snd.snd), lt_min hp hq, fun e he => ?_⟩
    exact ⟨⟨he.1, hxz'.trans he.2.1, he.2.2.1, fun a ha =>
        (he.2.2.2 a (Finset.mem_union_left _ ha)).trans_le (min_le_left _ _)⟩,
      ⟨he.1, hyz'.trans he.2.1, he.2.2.1, fun a ha =>
        (he.2.2.2 a (Finset.mem_union_right _ ha)).trans_le (min_le_right _ _)⟩⟩

/-- The canonical quasicentral approximate unit filter of a closed two-sided ideal `I` in `A`,
generated by sections `{e ∈ I | e₀ ≤ e ∧ ‖e‖ ≤ 1 ∧ ∀ a ∈ F, ‖e * a - a * e‖ < ε}` where `e₀ ∈ I`
is a positive strict contraction, `F` is a finite subset of `A`, and `ε > 0`. -/
def quasicentralApproximateUnit : Filter A :=
  I.isBasis_quasicentralApproximateUnit.filter

/-- Basis characterization of `I.quasicentralApproximateUnit`. -/
theorem hasBasis_quasicentralApproximateUnit :
    I.quasicentralApproximateUnit.HasBasis
      (fun p : {e₀ : A // e₀ ∈ I ∧ 0 ≤ e₀ ∧ ‖e₀‖ < 1} × Finset A × ℝ => 0 < p.snd.snd)
      (fun p => {e : A | e ∈ I ∧ (p.fst : A) ≤ e ∧ ‖e‖ ≤ 1 ∧
        ∀ a ∈ p.snd.fst, ‖e * a - a * e‖ < p.snd.snd}) :=
  I.isBasis_quasicentralApproximateUnit.hasBasis

instance neBot_quasicentralApproximateUnit : I.quasicentralApproximateUnit.NeBot :=
  I.hasBasis_quasicentralApproximateUnit.neBot_iff.mpr fun {p} hp => by
    obtain ⟨e, heI, he_ge, he_norm, he_comm⟩ :=
      I.exists_ge_norm_lt_one_commutator_lt p.fst.property.1 p.fst.property.2.1
        p.fst.property.2.2 p.snd.fst hp
    exact ⟨e, heI, he_ge, he_norm.le, he_comm⟩

/-- Elements of `I.quasicentralApproximateUnit` eventually lie in `I` and are positive
contractions. -/
theorem eventually_mem_quasicentralApproximateUnit :
    ∀ᶠ e in I.quasicentralApproximateUnit, e ∈ I ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 := by
  refine Filter.mem_of_superset
    (I.hasBasis_quasicentralApproximateUnit.mem_of_mem (i := (⟨0, I.zero_mem, le_rfl, by simp⟩,
      ∅, 1)) zero_lt_one) ?_
  intro e he
  exact ⟨he.1, he.2.1, he.2.2.1⟩

/-- The pullback of `I.quasicentralApproximateUnit` to `I.toNonUnitalStarSubalgebra` refines
`CStarAlgebra.approximateUnit I.toNonUnitalStarSubalgebra`. -/
theorem comap_quasicentralApproximateUnit_le :
    I.quasicentralApproximateUnit.comap ((↑) : I.toNonUnitalStarSubalgebra → A) ≤
      CStarAlgebra.approximateUnit I.toNonUnitalStarSubalgebra := by
  let S := I.toNonUnitalStarSubalgebra
  refine (CStarAlgebra.hasBasis_approximateUnit S).ge_iff.mpr fun s₀ hs₀ => ?_
  rw [Filter.mem_comap]
  refine ⟨{e : A | e ∈ I ∧ (s₀ : A) ≤ e ∧ ‖e‖ ≤ 1 ∧ ∀ a ∈ (∅ : Finset A), ‖e * a - a * e‖ < 1},
    I.hasBasis_quasicentralApproximateUnit.mem_of_mem
      (i := (⟨s₀.val, I.mem_toNonUnitalStarSubalgebra.mp s₀.property, hs₀.1, hs₀.2⟩, ∅, 1))
      zero_lt_one, ?_⟩
  intro x hx
  exact ⟨hx.2.1, by simpa [Metric.mem_closedBall] using hx.2.2.1⟩

/-- The pullback of `I.quasicentralApproximateUnit` to `I.toNonUnitalStarSubalgebra` is an
increasing approximate unit of `I.toNonUnitalStarSubalgebra`. -/
theorem isIncreasingApproximateUnit_comap_quasicentralApproximateUnit :
    (I.quasicentralApproximateUnit.comap
      ((↑) : I.toNonUnitalStarSubalgebra → A)).IsIncreasingApproximateUnit := by
  have hmem : (I.toNonUnitalStarSubalgebra : Set A) ∈ I.quasicentralApproximateUnit :=
    I.eventually_mem_quasicentralApproximateUnit.mono fun _ he =>
      I.mem_toNonUnitalStarSubalgebra.mpr he.1
  have : (I.quasicentralApproximateUnit.comap ((↑) : I.toNonUnitalStarSubalgebra → A)).NeBot :=
    Filter.comap_coe_neBot_of_le_principal (le_principal_iff.mpr hmem)
  exact (CStarAlgebra.increasingApproximateUnit I.toNonUnitalStarSubalgebra).mono
    I.comap_quasicentralApproximateUnit_le

private theorem map_comap_quasicentralApproximateUnit :
    (I.quasicentralApproximateUnit.comap ((↑) : I.toNonUnitalStarSubalgebra → A)).map
      ((↑) : I.toNonUnitalStarSubalgebra → A) = I.quasicentralApproximateUnit := by
  have hmem : (I.toNonUnitalStarSubalgebra : Set A) ∈ I.quasicentralApproximateUnit :=
    I.eventually_mem_quasicentralApproximateUnit.mono fun _ he =>
      I.mem_toNonUnitalStarSubalgebra.mpr he.1
  rw [Filter.map_comap, Subtype.range_coe, inf_eq_left.mpr (le_principal_iff.mpr hmem)]

/-- `I.quasicentralApproximateUnit` is a left approximate unit for `I`. -/
theorem tendsto_mul_right_quasicentralApproximateUnit {a : A} (ha : a ∈ I) :
    Tendsto (fun e => e * a) I.quasicentralApproximateUnit (𝓝 a) := by
  have hS := I.isIncreasingApproximateUnit_comap_quasicentralApproximateUnit.tendsto_mul_right
    ⟨a, I.mem_toNonUnitalStarSubalgebra.mpr ha⟩
  rw [← I.map_comap_quasicentralApproximateUnit, Filter.tendsto_map'_iff]
  exact (continuous_subtypeVal.tendsto _).comp hS

/-- `I.quasicentralApproximateUnit` is a right approximate unit for `I`. -/
theorem tendsto_mul_left_quasicentralApproximateUnit {a : A} (ha : a ∈ I) :
    Tendsto (fun e => a * e) I.quasicentralApproximateUnit (𝓝 a) := by
  have hS := I.isIncreasingApproximateUnit_comap_quasicentralApproximateUnit.tendsto_mul_left
    ⟨a, I.mem_toNonUnitalStarSubalgebra.mpr ha⟩
  rw [← I.map_comap_quasicentralApproximateUnit, Filter.tendsto_map'_iff]
  exact (continuous_subtypeVal.tendsto _).comp hS

/-- `I.quasicentralApproximateUnit` is quasicentral in `A`: `e * a - a * e → 0` for every
`a : A`. -/
theorem tendsto_commutator_quasicentralApproximateUnit (a : A) :
    Tendsto (fun e => e * a - a * e) I.quasicentralApproximateUnit (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  refine Filter.mem_of_superset
    (I.hasBasis_quasicentralApproximateUnit.mem_of_mem
      (i := (⟨0, I.zero_mem, le_rfl, by simp⟩, {a}, ε)) hε) ?_
  intro e he
  simpa [dist_zero_right] using he.2.2.2 a (Finset.mem_singleton_self a)

/-- A filter `l` on `A` refines `I.quasicentralApproximateUnit` if and only if it refines the image
of `CStarAlgebra.approximateUnit I.toNonUnitalStarSubalgebra` under coercion and every ambient
commutator `e * a - a * e` tends to `0` along `l`. -/
theorem le_quasicentralApproximateUnit_iff {l : Filter A} :
    l ≤ I.quasicentralApproximateUnit ↔
      l ≤ (CStarAlgebra.approximateUnit I.toNonUnitalStarSubalgebra).map
          ((↑) : I.toNonUnitalStarSubalgebra → A) ∧
        ∀ a : A, Tendsto (fun e => e * a - a * e) l (𝓝 0) := by
  refine ⟨fun hle => ⟨hle.trans ?_,
      fun a => (I.tendsto_commutator_quasicentralApproximateUnit a).mono_left hle⟩, ?_⟩
  · exact I.map_comap_quasicentralApproximateUnit ▸
      Filter.map_mono I.comap_quasicentralApproximateUnit_le
  · rintro ⟨hle, hcomm⟩
    refine I.hasBasis_quasicentralApproximateUnit.ge_iff.mpr
      fun ⟨⟨e₀, he₀I, he₀₀, he₀₁⟩, F, ε⟩ hε => ?_
    let S := I.toNonUnitalStarSubalgebra
    let s₀ : S := ⟨e₀, I.mem_toNonUnitalStarSubalgebra.mpr he₀I⟩
    have hs₀_mem : ((↑) '' ({x : S | s₀ ≤ x} ∩ Metric.closedBall 0 1) : Set A) ∈ l :=
      hle (Filter.image_mem_map ((CStarAlgebra.hasBasis_approximateUnit S).mem_of_mem ⟨he₀₀, he₀₁⟩))
    have hcomm_mem : ∀ᶠ e in l, ∀ a ∈ F, ‖e * a - a * e‖ < ε := by
      rw [Filter.eventually_all_finset]
      intro a _
      simpa [dist_zero_right] using Metric.tendsto_nhds.mp (hcomm a) ε hε
    filter_upwards [hs₀_mem, hcomm_mem] with e he₁ he₂
    rcases he₁ with ⟨x, hx, rfl⟩
    exact ⟨I.mem_toNonUnitalStarSubalgebra.mp x.property, hx.1,
      by simpa [Metric.mem_closedBall] using hx.2, he₂⟩

/-- **Arveson's theorem**: every closed two-sided ideal of a (possibly nonunital) C⋆-algebra
admits a positive contractive approximate unit that is quasicentral in the ambient algebra. -/
theorem exists_quasicentral_approximateUnit :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ I ∧ 0 ≤ e ∧ ‖e‖ ≤ 1) ∧
      (∀ a ∈ I, Tendsto (fun e ↦ e * a) l (𝓝 a)) ∧
      (∀ a ∈ I, Tendsto (fun e ↦ a * e) l (𝓝 a)) ∧
      (∀ a : A, Tendsto (fun e ↦ e * a - a * e) l (𝓝 0)) :=
  ⟨I.quasicentralApproximateUnit, inferInstance,
    I.eventually_mem_quasicentralApproximateUnit,
    fun _ ha => I.tendsto_mul_right_quasicentralApproximateUnit ha,
    fun _ ha => I.tendsto_mul_left_quasicentralApproximateUnit ha,
    I.tendsto_commutator_quasicentralApproximateUnit⟩

/-- Inductive step for building a monotone sequential quasicentral approximate unit. -/
private theorem exists_seq_step (dA : ℕ → A) (dI : ℕ → I.toNonUnitalStarSubalgebra)
    (n : ℕ) (x : I.toNonUnitalStarSubalgebra) (hx₀ : 0 ≤ x) (hx₁ : ‖x‖ < 1) :
    ∃ y : I.toNonUnitalStarSubalgebra, x ≤ y ∧ 0 ≤ y ∧ ‖y‖ < 1 ∧
      (∀ k ≤ n, ‖y * dI k - dI k‖ < ((n + 1 : ℕ) : ℝ)⁻¹) ∧
      (∀ k ≤ n, ‖(y : A) * dA k - dA k * (y : A)‖ < ((n + 1 : ℕ) : ℝ)⁻¹) := by
  classical
  let S := I.toNonUnitalStarSubalgebra
  have hε : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hev : ∀ᶠ z in CStarAlgebra.approximateUnit S,
      x ≤ z ∧ ∀ k ≤ n, ‖z * dI k - dI k‖ < ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have hge : ∀ᶠ z in CStarAlgebra.approximateUnit S, x ≤ z :=
      Filter.mem_of_superset
        ((CStarAlgebra.hasBasis_approximateUnit S).mem_of_mem ⟨hx₀, hx₁⟩) fun _ hz => hz.1
    have hfin : ∀ᶠ z in CStarAlgebra.approximateUnit S,
        ∀ k ∈ Finset.range (n + 1), ‖z * dI k - dI k‖ < ((n + 1 : ℕ) : ℝ)⁻¹ := by
      rw [Filter.eventually_all_finset]
      intro k _
      have hlim := (CStarAlgebra.increasingApproximateUnit S).tendsto_mul_right (dI k)
      simpa [dist_eq_norm] using Metric.tendsto_nhds.mp hlim _ hε
    filter_upwards [hge, hfin] with z hz₁ hz₂
    exact ⟨hz₁, fun k hk => hz₂ k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩
  obtain ⟨v, ⟨hv₀, hv₁⟩, hv⟩ := (CStarAlgebra.hasBasis_approximateUnit S).eventually_iff.mp hev
  have hxv : x ≤ v := (hv ⟨le_rfl, by simpa [Metric.mem_closedBall] using hv₁.le⟩).1
  obtain ⟨e, heI, hve, he_norm, he_comm⟩ :=
    I.exists_ge_norm_lt_one_commutator_lt (I.mem_toNonUnitalStarSubalgebra.mp v.property) hv₀
      hv₁ ((Finset.range (n + 1)).image dA) hε
  let y : S := ⟨e, I.mem_toNonUnitalStarSubalgebra.mpr heI⟩
  have hy_in_v : y ∈ {z : S | v ≤ z} ∩ Metric.closedBall 0 1 :=
    ⟨hve, by simpa [Metric.mem_closedBall] using he_norm.le⟩
  refine ⟨y, hxv.trans hve, hx₀.trans (hxv.trans hve), he_norm, (hv hy_in_v).2, fun k hk => ?_⟩
  exact he_comm (dA k) (Finset.mem_image_of_mem dA (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

/-- In a separable C⋆-algebra, every closed two-sided ideal admits a monotone increasing sequence
of positive strict contractions forming a quasicentral approximate unit. -/
theorem exists_seq_quasicentral_approximateUnit [TopologicalSpace.SeparableSpace A] :
    ∃ u : ℕ → A, Monotone u ∧ (∀ n, u n ∈ I ∧ 0 ≤ u n ∧ ‖u n‖ < 1) ∧
      (∀ a ∈ I, Tendsto (fun n => u n * a) atTop (𝓝 a)) ∧
      (∀ a ∈ I, Tendsto (fun n => a * u n) atTop (𝓝 a)) ∧
      (∀ a : A, Tendsto (fun n => u n * a - a * u n) atTop (𝓝 0)) := by
  -- Construct the monotone sequence recursively from dense sequences in `A` and `I`.
  let S := I.toNonUnitalStarSubalgebra
  have : SecondCountableTopology A := UniformSpace.secondCountable_of_separable A
  have : TopologicalSpace.SeparableSpace S := inferInstance
  obtain ⟨dA, hdA⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨dI, hdI⟩ := TopologicalSpace.exists_dense_seq S
  choose f hf_ge hf_nonneg hf_norm hf_approx hf_comm using I.exists_seq_step dA dI
  let seq : ℕ → {x : S // 0 ≤ x ∧ ‖x‖ < 1} :=
    Nat.rec ⟨0, le_rfl, by simp⟩ fun n prev =>
      ⟨f n prev.val prev.property.1 prev.property.2,
        hf_nonneg n prev.val prev.property.1 prev.property.2,
        hf_norm n prev.val prev.property.1 prev.property.2⟩
  let u : ℕ → A := fun n => (seq n).val.val
  have hu_mono : Monotone u :=
    monotone_nat_of_le_succ fun n =>
      hf_ge n (seq n).val (seq n).property.1 (seq n).property.2
  have hu_prop : ∀ n, u n ∈ I ∧ 0 ≤ u n ∧ ‖u n‖ < 1 := fun n =>
    ⟨I.mem_toNonUnitalStarSubalgebra.mp (seq n).val.property,
      (seq n).property.1, (seq n).property.2⟩
  -- Extend left and right approximate-unit convergence from `dI` to all of `I`.
  have hS_lim : ∀ x : S, Tendsto (fun n => (seq n).val * x) atTop (𝓝 x) :=
    TauCeti.tendsto_mul_right_of_dense hdI (C := 1)
      (.of_forall fun n => (seq n).property.2.le) <| by
      rintro _ ⟨k, rfl⟩
      refine tendsto_sub_nhds_zero_iff.mp <| (tendsto_add_atTop_iff_nat 1).mp ?_
      refine TauCeti.tendsto_zero_of_eventually_norm_le_inv ?_
      filter_upwards [Filter.eventually_ge_atTop (max k 1)] with m hm
      refine (hf_approx m (seq m).val (seq m).property.1 (seq m).property.2 k
        ((le_max_left k 1).trans hm)).le.trans ?_
      exact inv_anti₀ (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one
        ((le_max_right k 1).trans hm))) (by norm_cast; omega)
  have hu_mul_right : ∀ a ∈ I, Tendsto (fun n => u n * a) atTop (𝓝 a) := fun a ha =>
    ((continuous_subtypeVal.tendsto _).comp
      (hS_lim ⟨a, I.mem_toNonUnitalStarSubalgebra.mpr ha⟩)).congr fun n => by
        simp only [Function.comp_apply, MulMemClass.coe_mul, u]
  have hS_approx : (atTop.map (fun n => (seq n).val)).IsIncreasingApproximateUnit :=
    .of_tendsto_mul_right
      (eventually_map.mpr (Eventually.of_forall fun n => (seq n).property.1))
      (eventually_map.mpr (Eventually.of_forall fun n => (seq n).property.2.le))
      (fun x => tendsto_map'_iff.mpr (hS_lim x))
  have hu_mul_left : ∀ a ∈ I, Tendsto (fun n => a * u n) atTop (𝓝 a) := fun a ha =>
    ((continuous_subtypeVal.tendsto _).comp
      (tendsto_map'_iff.mp
        (hS_approx.tendsto_mul_left ⟨a, I.mem_toNonUnitalStarSubalgebra.mpr ha⟩))).congr
      fun n => by simp only [Function.comp_apply, MulMemClass.coe_mul, u]
  -- Extend commutator convergence from `dA` to all of `A`.
  have hu_comm : ∀ a : A, Tendsto (fun n => u n * a - a * u n) atTop (𝓝 0) :=
    TauCeti.tendsto_commutator_of_dense hdA (C := 1)
      (.of_forall fun n => (hu_prop n).2.2.le) <| by
      rintro _ ⟨k, rfl⟩
      refine (tendsto_add_atTop_iff_nat 1).mp ?_
      refine TauCeti.tendsto_zero_of_eventually_norm_le_inv ?_
      filter_upwards [Filter.eventually_ge_atTop (max k 1)] with m hm
      refine (hf_comm m (seq m).val (seq m).property.1 (seq m).property.2 k
        ((le_max_left k 1).trans hm)).le.trans ?_
      exact inv_anti₀ (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one
        ((le_max_right k 1).trans hm))) (by norm_cast; omega)
  exact ⟨u, hu_mono, hu_prop, hu_mul_right, hu_mul_left, hu_comm⟩

end Quasicentral

end TwoSidedIdeal

end
