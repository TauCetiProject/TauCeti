/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity
public import Mathlib.Analysis.Normed.Lp.lpHolder
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Multiplication semigroups on ℓᵖ

For an arbitrary nonnegative multiplier `m : ι → ℝ≥0`, the operators
`S(t)x i = exp (-t * m i) * x i` form a contraction semigroup on real `ℓᵖ`, for
`1 ≤ p < ∞`. No boundedness of `m` is assumed. Its generator has exactly the natural domain
`{x | Memℓp (fun i => m i * x i) p}` and acts as multiplication by `-m`.
For `λ > 0`, its resolvent is multiplication by `(λ + m)⁻¹`.

The finite-exponent hypothesis is essential: unbounded multipliers need not yield strong
continuity on `ℓ∞`.

## References

K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Section I.4.c (multiplication semigroups).
-/

public section

noncomputable section

open scoped NNReal ENNReal Topology
open Filter MeasureTheory

namespace TauCeti.Semigroups

variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem lp_exp_multiplier_norm_le (m : ι → ℝ≥0) (t : ℝ≥0) (i : ι) :
    ‖Real.exp (-((t : ℝ) * m i)) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
  simp only [norm_smul, ContinuousLinearMap.norm_id, mul_one,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

private def lpMultiplicationOperator (m : ι → ℝ≥0) (t : ℝ≥0) :
    lp (fun _ : ι => ℝ) p →L[ℝ] lp (fun _ : ι => ℝ) p :=
  lp.mapCLM p (fun i => Real.exp (-((t : ℝ) * m i)) • ContinuousLinearMap.id ℝ ℝ)
    zero_le_one (lp_exp_multiplier_norm_le m t)

private theorem lpMultiplicationOperator_apply (m : ι → ℝ≥0) (t : ℝ≥0)
    (x : lp (fun _ : ι => ℝ) p) (i : ι) :
    lpMultiplicationOperator m t x i = Real.exp (-((t : ℝ) * m i)) * x i := by
  simp [lpMultiplicationOperator]

private theorem lpMultiplicationOperator_norm_le (m : ι → ℝ≥0) (t : ℝ≥0) :
    ‖lpMultiplicationOperator (p := p) m t‖ ≤ 1 :=
  lp.norm_mapCLM_le p _ zero_le_one (lp_exp_multiplier_norm_le m t)

private theorem lpMultiplicationOperator_single [DecidableEq ι] (m : ι → ℝ≥0) (t : ℝ≥0)
    (i : ι) (a : ℝ) :
    lpMultiplicationOperator m t (lp.single p i a) =
      lp.single p i (Real.exp (-((t : ℝ) * m i)) * a) := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp [lpMultiplicationOperator_apply]
  · simp [lpMultiplicationOperator_apply, lp.single_apply, h]

private theorem lpMultiplicationOperator_continuousAt_zero (hp : p ≠ ∞)
    (m : ι → ℝ≥0) (x : lp (fun _ : ι => ℝ) p) :
    ContinuousAt (fun t : ℝ≥0 => lpMultiplicationOperator m t x) 0 := by
  classical
  let D : Set (lp (fun _ : ι => ℝ) p) :=
    {y | ∃ (s : Finset ι) (a : ι → ℝ), y = ∑ i ∈ s, lp.single p i (a i)}
  have hD : Dense D := by
    intro y
    exact mem_closure_of_tendsto (lp.hasSum_single hp y)
      (Eventually.of_forall fun s => ⟨s, y, rfl⟩)
  have hsingle (i : ι) (a : ℝ) :
      ContinuousAt (fun t : ℝ≥0 => lpMultiplicationOperator m t (lp.single p i a)) 0 := by
    simp_rw [lpMultiplicationOperator_single]
    exact (lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) p i).continuous.continuousAt.comp
      (by fun_prop)
  have hzero : lpMultiplicationOperator (p := p) m 0 = ContinuousLinearMap.id ℝ _ := by
    ext y i
    simp [lpMultiplicationOperator_apply]
  rw [ContinuousAt, hzero]
  apply ContinuousLinearMap.tendsto_apply_of_dense hD
    (Eventually.of_forall fun t => lpMultiplicationOperator_norm_le m t) _ x
  rintro y ⟨s, a, rfl⟩
  simp_rw [map_sum]
  simpa only [hzero, ContinuousLinearMap.id_apply] using
    (tendsto_finsetSum s fun i hi => (hsingle i (a i)).tendsto)

/-- The contraction semigroup of multiplication by `exp (-t * m)` on real ℓᵖ, for
`1 ≤ p < ∞`. The nonnegative multiplier `m` may be unbounded. -/
def ContractionSemigroup.ofLpMultiplication (hp : p ≠ ∞) (m : ι → ℝ≥0) :
    ContractionSemigroup (lp (fun _ : ι => ℝ) p) where
  toFun := lpMultiplicationOperator m
  map_zero' := by
    ext x i
    simp [lpMultiplicationOperator_apply]
  map_add' s t := by
    ext x i
    simp only [ContinuousLinearMap.comp_apply, lpMultiplicationOperator_apply,
      NNReal.coe_add]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  continuousAt_zero' := lpMultiplicationOperator_continuousAt_zero hp m
  contracting := lpMultiplicationOperator_norm_le m

/-- Coordinate action of the ℓᵖ multiplication semigroup. -/
@[simp]
theorem ContractionSemigroup.ofLpMultiplication_apply_apply_apply (hp : p ≠ ∞)
    (m : ι → ℝ≥0) (t : ℝ≥0) (x : lp (fun _ : ι => ℝ) p) (i : ι) :
    ofLpMultiplication hp m t x i = Real.exp (-((t : ℝ) * m i)) * x i :=
  lpMultiplicationOperator_apply m t x i

/-- The Laplace resolvent acts coordinatewise by multiplication with `(λ + m i)⁻¹`. -/
@[simp]
theorem ContractionSemigroup.ofLpMultiplication_resolvent_apply_apply (hp : p ≠ ∞)
    (m : ι → ℝ≥0) {c : ℝ} (hc : 0 < c) (x : lp (fun _ : ι => ℝ) p) (i : ι) :
    (ofLpMultiplication hp m).resolvent c hc x i = (c + (m i : ℝ))⁻¹ * x i := by
  let S := ofLpMultiplication hp m
  have hcomm := (lp.evalCLM ℝ (fun _ : ι => ℝ) p i).integral_comp_comm
    (S.toStronglyContinuousSemigroup.integrableOn_resolvent_integrand
      S.hasGrowthBound c (by simpa using hc) x).integrable
  have heval : (S.resolvent c hc x) i =
      ∫ t : ℝ in Set.Ioi 0, Real.exp (-(c * t)) *
        Real.exp (-(t * (m i : ℝ))) * x i := by
    -- `evalCLM` is the bundled evaluator used to commute evaluation and integration.
    change lp.evalCLM ℝ (fun _ : ι => ℝ) p i (S.resolvent c hc x) = _
    rw [S.resolvent_apply, ← hcomm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [map_smul, StronglyContinuousSemigroup.realOperator_def,
      smul_eq_mul]
    rw [ContractionSemigroup.toStronglyContinuousSemigroup_apply]
    -- The evaluator was built from `evalₗ`, whose application lemma exposes the coordinate.
    change Real.exp (-(c * t)) * (S t.toNNReal x) i = _
    simp only [S, ofLpMultiplication_apply_apply_apply, Real.coe_toNNReal t ht.le, mul_assoc]
  rw [heval]
  have hexp (t : ℝ) : Real.exp (-(c * t)) * Real.exp (-(t * (m i : ℝ))) * x i =
      Real.exp (-((c + (m i : ℝ)) * t)) * x i := by
    rw [← Real.exp_add]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hexp t), integral_mul_const]
  have hint : ∫ t : ℝ in Set.Ioi 0, Real.exp (-((c + (m i : ℝ)) * t)) =
      (c + (m i : ℝ))⁻¹ := by
    simpa using integral_pow_mul_exp_neg_mul_Ioi 0 (by positivity : 0 < c + (m i : ℝ))
  rw [hint]

/-- The infinitesimal generator of the multiplication semigroup acts coordinatewise as `-m`.
Its domain is characterized by `ofLpMultiplication_mem_domain_iff`. -/
@[simp]
theorem ContractionSemigroup.ofLpMultiplication_generator_apply_apply (hp : p ≠ ∞)
    (m : ι → ℝ≥0)
    (x : (ofLpMultiplication hp m).toStronglyContinuousSemigroup.generator.domain) (i : ι) :
    (ofLpMultiplication hp m).toStronglyContinuousSemigroup.generator x i =
      -(m i : ℝ) * (x : lp (fun _ : ι => ℝ) p) i := by
  let S := ofLpMultiplication hp m
  have hx : (x : lp (fun _ : ι => ℝ) p) ∈ S.toStronglyContinuousSemigroup.domain := by
    simpa only [StronglyContinuousSemigroup.generator_domain] using x.property
  have h := congrArg (fun y : lp (fun _ : ι => ℝ) p => y i)
    (S.resolventLeftInv 1 zero_lt_one ⟨x, hx⟩)
  rw [ofLpMultiplication_resolvent_apply_apply] at h
  simp only [one_smul, lp.coeFn_sub, Pi.sub_apply] at h
  have hne : (1 + (m i : ℝ)) ≠ 0 := by positivity
  field_simp [hne] at h
  dsimp only [S] at h
  linarith

/-- The generator domain is exactly the vectors whose product with the multiplier is in ℓᵖ.
This characterizes the natural domain even when the multiplier is unbounded. -/
@[simp]
theorem ContractionSemigroup.ofLpMultiplication_mem_domain_iff (hp : p ≠ ∞)
    (m : ι → ℝ≥0) (x : lp (fun _ : ι => ℝ) p) :
    x ∈ (ofLpMultiplication hp m).toStronglyContinuousSemigroup.domain ↔
      Memℓp (fun i => (m i : ℝ) * x i) p := by
  let S := ofLpMultiplication hp m
  constructor
  · intro hx
    let x' : S.toStronglyContinuousSemigroup.generator.domain :=
      ⟨x, by rwa [StronglyContinuousSemigroup.generator_domain]⟩
    have heq : (fun i => (m i : ℝ) * x i) =
        ⇑(-S.toStronglyContinuousSemigroup.generator x') := by
      funext i
      simp only [lp.coeFn_neg, Pi.neg_apply]
      rw [ofLpMultiplication_generator_apply_apply]
      simp [x']
    rw [heq]
    exact lp.memℓp _
  · intro hx
    let z : lp (fun _ : ι => ℝ) p := ⟨fun i => (m i : ℝ) * x i, hx⟩
    have heq : S.resolvent 1 zero_lt_one (x + z) = x := by
      ext i
      rw [ofLpMultiplication_resolvent_apply_apply]
      simp only [lp.coeFn_add, Pi.add_apply]
      have hne : (1 + (m i : ℝ)) ≠ 0 := by positivity
      -- The subtype `z` records the assumed summability of the weighted vector.
      simp only [z]
      field_simp [hne]
    rw [← heq]
    exact S.resolvent_mem_domain 1 zero_lt_one (x + z)

/-- An unbounded nonnegative multiplier gives a semigroup that is not continuous in operator
norm at zero, although it is strongly continuous. -/
theorem ContractionSemigroup.ofLpMultiplication_not_continuousAt_zero (hp : p ≠ ∞)
    (m : ι → ℝ≥0) (hm : ¬ BddAbove (Set.range fun i => (m i : ℝ))) :
    ¬ ContinuousAt (fun t : ℝ≥0 => ofLpMultiplication hp m t) 0 := by
  classical
  intro hcont
  have he : 0 < 1 - Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hcont (1 - Real.exp (-1)) he
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp hm δ⁻¹
  have hmi : 0 < (m i : ℝ) := (inv_pos.mpr hδ).trans hi
  let t : ℝ≥0 := (m i)⁻¹
  have ht : dist t 0 < δ := by
    simpa [t, NNReal.dist_eq, abs_of_nonneg (inv_nonneg.mpr (m i).coe_nonneg)] using
      (inv_lt_comm₀ hmi hδ).mpr hi
  have hs := hsmall ht
  let e : lp (fun _ : ι => ℝ) p := lp.single p i 1
  let T := ofLpMultiplication hp m t - ofLpMultiplication hp m 0
  have hnorm : ‖e‖ = 1 := by
    simpa [e] using lp.norm_single (E := fun _ : ι => ℝ)
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)) i (1 : ℝ)
  have heval : (T e) i = Real.exp (-1) - 1 := by
    simp only [T, sub_apply, lp.coeFn_sub, Pi.sub_apply,
      ofLpMultiplication_apply_apply_apply, NNReal.coe_zero, zero_mul, neg_zero,
      Real.exp_zero, one_mul]
    simp [t, e, inv_mul_cancel₀ hmi.ne']
  have hbound : 1 - Real.exp (-1) ≤ ‖T‖ := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (T e) i).trans (T.le_opNorm e)
    rw [hnorm, mul_one, heval, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : Real.exp (-1) - 1 ≤ 0)] at h
    linarith
  rw [dist_eq_norm] at hs
  exact (not_lt_of_ge hbound) hs

/-- On ℓᵖ indexed by the natural numbers, the unbounded multiplier `m n = n + 1` gives a
multiplication contraction semigroup that is not continuous in operator norm at zero. -/
theorem ContractionSemigroup.ofLpMultiplication_nat_not_continuousAt_zero (hp : p ≠ ∞) :
    ¬ ContinuousAt
      (fun t : ℝ≥0 => ofLpMultiplication hp (fun n : ℕ => (n : ℝ≥0) + 1) t) 0 := by
  apply ofLpMultiplication_not_continuousAt_zero hp
  rw [not_bddAbove_iff]
  intro c
  obtain ⟨n, hn⟩ := exists_nat_gt c
  refine ⟨_, ⟨n, rfl⟩, ?_⟩
  simpa using (lt_add_of_lt_of_pos hn zero_lt_one)

end TauCeti.Semigroups
