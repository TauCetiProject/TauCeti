/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import TauCeti.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Evaluation
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic

/-!
# Exponential and logarithm of Novikov series

Let `K` be a commutative `ℚ`-algebra, `H` an additive commutative monoid and `N : H →+ ℝ` a
period homomorphism. In the nonnegative subring of the Novikov ring `Nov(K, H, N)`, a series `a`
of the positive ideal is topologically nilpotent, so the series of Mathlib's exponential
`NormedSpace.exp` and logarithm `NormedSpace.log`

`exp a = ∑ aⁿ / n!`,    `log (1 + a) = ∑ (-1)ⁿ⁺¹ aⁿ / n`

converge in the period topology (`TauCeti.NovikovSeries.hasSum_exp`,
`TauCeti.NovikovSeries.hasSum_log`). The exponential maps the positive ideal into the principal
unit group of the units `u` with `u - 1` in the positive ideal, the logarithm maps that group
back into the positive ideal, and the two maps are mutually inverse group isomorphisms
(`TauCeti.NovikovSeries.expMulEquiv`). The dynamical zeta function of a closed one-form is
defined as the exponential of a rational logarithmic series of periodic orbits lying in the
positive ideal; by this isomorphism it is a principal unit.

The formal identities `exp (log (1 + X)) = 1 + X` and `log (exp X) = X` are Mathlib's
`PowerSeries.subst_exp_log` and `PowerSeries.subst_log_exp_sub_one`. They are transported to
Novikov series by evaluating power series at a series `a` of the positive ideal: the nonnegative
subring is a complete, linearly topologized `K`-algebra, so Mathlib's continuous evaluation
`PowerSeries.aeval` applies, and it is compatible with substitution
(`PowerSeries.aeval_subst`). The coefficients in `K` carry the discrete topology for this
evaluation. The functional equation `exp (a + b) = exp a * exp b` is the Cauchy product of the
exponential series in the complete nonarchimedean ring, matched coefficientwise with Mathlib's
`PowerSeries.exp_mul_exp_eq_exp_add`; its proof follows that of Mathlib's
`NormedSpace.exp_add_of_commute_of_mem_ball`.

## Main definitions

* `TauCeti.NovikovSeries.expMulEquiv`: the exponential, as an isomorphism from the additive group
  of the positive ideal onto the principal unit group, with inverse the logarithm.

## Main results

* `TauCeti.NovikovSeries.hasSum_exp`, `TauCeti.NovikovSeries.hasSum_log`: convergence of the two
  series in the period topology.
* `TauCeti.NovikovSeries.exp_log`, `TauCeti.NovikovSeries.log_exp`: the two inverse identities.
* `TauCeti.NovikovSeries.exp_add`, `TauCeti.NovikovSeries.log_mul`: the functional equations.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

open Filter Topology PowerSeries Nat

namespace TauCeti

namespace NovikovSeries

variable {H K : Type*} [AddCommMonoid H] {N : H →+ ℝ} [CommRing K]

attribute [local instance] DiscreteTopology.instContinuousSMul

section Evaluation

/- The statement in terms of `PowerSeries.HasEval`, whose topology on the nonnegative subring is
read off from its uniform structure. Passing `isTopologicallyNilpotent_of_mem_posIdeal'` directly
to `PowerSeries.aeval` makes the elaborator unfold both topologies, which times out. -/
private theorem hasEval_of_mem_posIdeal {a : nonnegSubring K N} (ha : a ∈ posIdeal K N) :
    PowerSeries.HasEval a :=
  isTopologicallyNilpotent_of_mem_posIdeal' ha

variable [UniformSpace K] [DiscreteUniformity K] {a : nonnegSubring K N}

/-- Evaluating a power series without constant term at a series of the positive ideal gives a
series of the positive ideal. -/
private theorem aeval_mem_posIdeal (ha : a ∈ posIdeal K N) {f : K⟦X⟧}
    (hf : constantCoeff f = 0) :
    PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal ha) f ∈ posIdeal K N := by
  refine isClosed_posIdeal.mem_of_tendsto (hasSum_aeval (hasEval_of_mem_posIdeal ha) f)
    (Eventually.of_forall fun s => Submodule.sum_mem _ fun n _ => ?_)
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [hf]
  · rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha n hn)

end Evaluation

variable [Algebra ℚ K]

section Evaluation

variable [UniformSpace K] [DiscreteUniformity K] {a u : nonnegSubring K N}

private theorem hasSum_exp_aeval (ha : a ∈ posIdeal K N) :
    HasSum (fun n : ℕ => (n ! : ℚ)⁻¹ • a ^ n)
      (PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal ha) (PowerSeries.exp K)) :=
  hasSum_smul_pow_aeval (hasEval_of_mem_posIdeal ha) fun n => by rw [coeff_exp, one_div]

private theorem hasSum_log_aeval (hu : u - 1 ∈ posIdeal K N) :
    HasSum (fun n : ℕ => ((-1) ^ (n + 1) / n : ℚ) • (u - 1) ^ n)
      (PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal hu) (PowerSeries.log K)) :=
  hasSum_smul_pow_aeval (hasEval_of_mem_posIdeal hu) fun n => by
    rw [coeff_log]
    split_ifs with hn <;> simp [hn]

private theorem exp_eq_aeval (ha : a ∈ posIdeal K N) :
    NormedSpace.exp a =
      PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal ha) (PowerSeries.exp K) := by
  rw [NormedSpace.exp_eq_tsum_rat]
  exact (hasSum_exp_aeval ha).tsum_eq

private theorem log_eq_aeval (hu : u - 1 ∈ posIdeal K N) :
    NormedSpace.log u =
      PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal hu) (PowerSeries.log K) := by
  rw [NormedSpace.log_eq_tsum ℚ]
  exact (hasSum_log_aeval hu).tsum_eq

end Evaluation

variable {a b u v : nonnegSubring K N}

/-- For `a` in the positive ideal, the exponential series `∑ aⁿ / n!` converges to `exp a`. -/
theorem hasSum_exp (ha : a ∈ posIdeal K N) :
    HasSum (fun n : ℕ => (n ! : ℚ)⁻¹ • a ^ n) (NormedSpace.exp a) := by
  let : UniformSpace K := ⊥
  rw [exp_eq_aeval ha]
  exact hasSum_exp_aeval ha

/-- For `u - 1` in the positive ideal, the logarithm series `∑ (-1)ⁿ⁺¹ (u - 1)ⁿ / n` converges
to `log u`. -/
theorem hasSum_log (hu : u - 1 ∈ posIdeal K N) :
    HasSum (fun n : ℕ => ((-1) ^ (n + 1) / n : ℚ) • (u - 1) ^ n) (NormedSpace.log u) := by
  let : UniformSpace K := ⊥
  rw [log_eq_aeval hu]
  exact hasSum_log_aeval hu

theorem exp_sub_one_mem_posIdeal (ha : a ∈ posIdeal K N) :
    NormedSpace.exp a - 1 ∈ posIdeal K N := by
  let : UniformSpace K := ⊥
  rw [exp_eq_aeval ha, ← map_one (PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal ha)),
    ← map_sub]
  exact aeval_mem_posIdeal ha (by simp)

theorem log_mem_posIdeal (hu : u - 1 ∈ posIdeal K N) : NormedSpace.log u ∈ posIdeal K N := by
  let : UniformSpace K := ⊥
  rw [log_eq_aeval hu]
  exact aeval_mem_posIdeal hu constantCoeff_log

/-- The exponential of the logarithm: `exp (log u) = u` when `u - 1` lies in the positive
ideal. -/
theorem exp_log (hu : u - 1 ∈ posIdeal K N) : NormedSpace.exp (NormedSpace.log u) = u := by
  let : UniformSpace K := ⊥
  rw [log_eq_aeval hu, exp_eq_aeval (aeval_mem_posIdeal hu constantCoeff_log),
    ← PowerSeries.aeval_subst (HasSubst.of_constantCoeff_zero' constantCoeff_log)
      (continuous_aeval (hasEval_of_mem_posIdeal hu)),
    subst_exp_log, map_add, map_one, PowerSeries.aeval_X (hasEval_of_mem_posIdeal hu),
    add_sub_cancel]

/-- The logarithm of the exponential: `log (exp a) = a` when `a` lies in the positive ideal. -/
theorem log_exp (ha : a ∈ posIdeal K N) : NormedSpace.log (NormedSpace.exp a) = a := by
  let : UniformSpace K := ⊥
  have hg : PowerSeries.aeval (R := K) (hasEval_of_mem_posIdeal ha) (PowerSeries.exp K - 1) =
      NormedSpace.exp a - 1 := by
    rw [map_sub, map_one, exp_eq_aeval ha]
  have h := PowerSeries.aeval_subst (HasSubst.of_constantCoeff_zero' (by simp))
    (continuous_aeval (hasEval_of_mem_posIdeal ha))
    (hg ▸ hasEval_of_mem_posIdeal (exp_sub_one_mem_posIdeal ha)) (PowerSeries.log K)
  rw [subst_log_exp_sub_one, PowerSeries.aeval_X (hasEval_of_mem_posIdeal ha)] at h
  rw [log_eq_aeval (exp_sub_one_mem_posIdeal ha)]
  convert h.symm using 3
  exact hg.symm

/-- The exponential turns sums of series of the positive ideal into products. -/
theorem exp_add (ha : a ∈ posIdeal K N) (hb : b ∈ posIdeal K N) :
    NormedSpace.exp (a + b) = NormedSpace.exp a * NormedSpace.exp b := by
  -- The Cauchy product is stated for abstract families: instantiating it directly at the
  -- exponential series makes the elaborator unfold the scalar actions, which times out.
  have cauchy : ∀ f g : ℕ → nonnegSubring K N, Summable f → Summable g →
      (∑' n, f n) * ∑' n, g n = ∑' n, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 :=
    fun f g hf hg => hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg (hf.mul_of_nonarchimedean hg)
  rw [← (hasSum_exp ha).tsum_eq, ← (hasSum_exp hb).tsum_eq, ← (hasSum_exp (add_mem ha hb)).tsum_eq,
    cauchy _ _ (hasSum_exp ha).summable (hasSum_exp hb).summable]
  refine tsum_congr fun n => ?_
  -- Coefficientwise, this is the formal identity `e^{aX} * e^{bX} = e^{(a + b)X}`.
  have h := congrArg (PowerSeries.coeff n) (PowerSeries.exp_mul_exp_eq_exp_add a b)
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    one_div] at h
  simpa only [Algebra.smul_def, map_inv₀, map_natCast, mul_mul_mul_comm, mul_comm, eq_comm]
    using h

/-- The logarithm turns products into sums: `log (u * v) = log u + log v` when `u - 1` and
`v - 1` lie in the positive ideal. -/
theorem log_mul (hu : u - 1 ∈ posIdeal K N) (hv : v - 1 ∈ posIdeal K N) :
    NormedSpace.log (u * v) = NormedSpace.log u + NormedSpace.log v := by
  rw [← log_exp (add_mem (log_mem_posIdeal hu) (log_mem_posIdeal hv)),
    exp_add (log_mem_posIdeal hu) (log_mem_posIdeal hv), exp_log hu, exp_log hv]

variable (K N) in
/-- **Exponential and logarithm** of Novikov series: over a `ℚ`-algebra `K`, the exponential is
an isomorphism from the additive group of the positive ideal onto the principal unit group of the
nonnegative subring, with inverse the logarithm. -/
def expMulEquiv : Multiplicative (posIdeal K N) ≃* principalUnitGroup K N where
  toFun a := ⟨⟨NormedSpace.exp a.toAdd, NormedSpace.exp (-a.toAdd),
      by rw [← exp_add a.toAdd.2 (neg_mem a.toAdd.2), add_neg_cancel, NormedSpace.exp_zero],
      by rw [← exp_add (neg_mem a.toAdd.2) a.toAdd.2, neg_add_cancel, NormedSpace.exp_zero]⟩,
    mem_principalUnitGroup.2 (exp_sub_one_mem_posIdeal a.toAdd.2)⟩
  invFun u := .ofAdd ⟨NormedSpace.log ((u : (nonnegSubring K N)ˣ) : nonnegSubring K N),
    log_mem_posIdeal (mem_principalUnitGroup.1 u.2)⟩
  left_inv a := Subtype.ext (log_exp a.toAdd.2)
  right_inv u := Subtype.ext (Units.ext (exp_log (mem_principalUnitGroup.1 u.2)))
  map_mul' a b := Subtype.ext (Units.ext (exp_add a.toAdd.2 b.toAdd.2))

@[simp]
theorem coe_expMulEquiv_apply (a : posIdeal K N) :
    ((expMulEquiv K N (.ofAdd a) : (nonnegSubring K N)ˣ) : nonnegSubring K N) =
      NormedSpace.exp (a : nonnegSubring K N) :=
  (rfl)

@[simp]
theorem coe_expMulEquiv_symm_apply (u : principalUnitGroup K N) :
    (((expMulEquiv K N).symm u).toAdd : nonnegSubring K N) =
      NormedSpace.log ((u : (nonnegSubring K N)ˣ) : nonnegSubring K N) :=
  (rfl)

end NovikovSeries

end TauCeti
