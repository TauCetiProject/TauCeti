/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import TauCeti.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology

/-!
# Exponential and logarithm of topologically nilpotent elements

Let `S` be a complete, separated, linearly topologized commutative `ℚ`-algebra. For a
topologically nilpotent `a : S`, the series of Mathlib's exponential `NormedSpace.exp` and
logarithm `NormedSpace.log`

`exp a = ∑ aⁿ / n!`,    `log (1 + a) = ∑ (-1)ⁿ⁺¹ aⁿ / n`

converge (`IsTopologicallyNilpotent.hasSum_exp`, `IsTopologicallyNilpotent.hasSum_log`), the two
maps are mutually inverse, and they satisfy the functional equations. So for an ideal `I` of
topologically nilpotent elements, the exponential is an isomorphism from the additive group of `I`
onto its principal unit group of units `u` with `u - 1 ∈ I`, with inverse the logarithm
(`Ideal.expMulEquiv`).

The formal identities `exp (log (1 + X)) = 1 + X` and `log (exp X) = X` are Mathlib's
`PowerSeries.subst_exp_log` and `PowerSeries.subst_log_exp_sub_one`. They are transported to `S`
by evaluating power series at `a` through Mathlib's continuous evaluation `PowerSeries.aeval`,
which is compatible with substitution (`PowerSeries.aeval_subst`). A power series without constant
term evaluates to a multiple of `a`, which keeps `exp a - 1` and `log (1 + a)` topologically
nilpotent and in every ideal containing `a`. The functional equation
`exp (a + b) = exp a * exp b` is the Cauchy product of the exponential series in the complete
nonarchimedean ring `S`, matched coefficientwise with Mathlib's
`PowerSeries.exp_mul_exp_eq_exp_add`; its proof follows that of Mathlib's
`NormedSpace.exp_add_of_commute_of_mem_ball`.

## Main definitions

* `Ideal.expMulEquiv`: for an ideal `I` of topologically nilpotent elements, the exponential as an
  isomorphism from the additive group of `I` onto `Ideal.principalUnitGroup I`, with inverse the
  logarithm.

## Main results

* `IsTopologicallyNilpotent.hasSum_exp`, `IsTopologicallyNilpotent.hasSum_log`: convergence of
  the two series.
* `IsTopologicallyNilpotent.exp_sub_one`, `IsTopologicallyNilpotent.log`: `exp a - 1` and
  `log (1 + a)` are topologically nilpotent.
* `IsTopologicallyNilpotent.exp_sub_one_mem`, `IsTopologicallyNilpotent.log_mem`: `exp a - 1`
  and `log (1 + a)` lie in every ideal containing `a`.
* `IsTopologicallyNilpotent.exp_log`, `IsTopologicallyNilpotent.log_exp`: the two inverse
  identities.
* `IsTopologicallyNilpotent.exp_add`, `IsTopologicallyNilpotent.log_mul`: the functional
  equations.
-/

public section

noncomputable section

open Filter Topology PowerSeries Nat

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsTopologicalRing S] [IsLinearTopology S S] [T2Space S] [CompleteSpace S]

namespace IsTopologicallyNilpotent

variable {a b u v : S}

section Evaluation

variable [Algebra ℚ S]

private theorem hasSum_exp_aeval (ha : IsTopologicallyNilpotent a) :
    HasSum (fun n : ℕ => (n ! : ℚ)⁻¹ • a ^ n)
      (PowerSeries.aeval (R := S) ha (PowerSeries.exp S)) :=
  hasSum_smul_pow_aeval ha fun n => by rw [coeff_exp, one_div]

private theorem hasSum_log_aeval (hu : IsTopologicallyNilpotent (u - 1)) :
    HasSum (fun n : ℕ => ((-1) ^ (n + 1) / n : ℚ) • (u - 1) ^ n)
      (PowerSeries.aeval (R := S) hu (PowerSeries.log S)) :=
  hasSum_smul_pow_aeval hu fun n => by
    rw [coeff_log]
    split_ifs with hn <;> simp [hn]

private theorem exp_eq_aeval (ha : IsTopologicallyNilpotent a) :
    NormedSpace.exp a = PowerSeries.aeval (R := S) ha (PowerSeries.exp S) := by
  rw [NormedSpace.exp_eq_tsum_rat]
  exact (hasSum_exp_aeval ha).tsum_eq

private theorem log_eq_aeval (hu : IsTopologicallyNilpotent (u - 1)) :
    NormedSpace.log u = PowerSeries.aeval (R := S) hu (PowerSeries.log S) := by
  rw [NormedSpace.log_eq_tsum ℚ]
  exact (hasSum_log_aeval hu).tsum_eq

private theorem exists_exp_sub_one_eq_mul (ha : IsTopologicallyNilpotent a) :
    ∃ c : S, NormedSpace.exp a - 1 = a * c := by
  rw [exp_eq_aeval ha, ← map_one (PowerSeries.aeval (R := S) ha), ← map_sub]
  exact exists_aeval_eq_mul_of_constantCoeff_eq_zero ha (by simp)

private theorem exists_log_eq_mul (hu : IsTopologicallyNilpotent (u - 1)) :
    ∃ c : S, NormedSpace.log u = (u - 1) * c := by
  rw [log_eq_aeval hu]
  exact exists_aeval_eq_mul_of_constantCoeff_eq_zero hu constantCoeff_log

end Evaluation

variable [Algebra ℚ S]

/-- For a topologically nilpotent `a`, the exponential series `∑ aⁿ / n!` converges to
`exp a`. -/
theorem hasSum_exp (ha : IsTopologicallyNilpotent a) :
    HasSum (fun n : ℕ => (n ! : ℚ)⁻¹ • a ^ n) (NormedSpace.exp a) := by
  rw [exp_eq_aeval ha]
  exact hasSum_exp_aeval ha

/-- For a topologically nilpotent `u - 1`, the logarithm series `∑ (-1)ⁿ⁺¹ (u - 1)ⁿ / n`
converges to `log u`. -/
theorem hasSum_log (hu : IsTopologicallyNilpotent (u - 1)) :
    HasSum (fun n : ℕ => ((-1) ^ (n + 1) / n : ℚ) • (u - 1) ^ n) (NormedSpace.log u) := by
  rw [log_eq_aeval hu]
  exact hasSum_log_aeval hu

/-- If `a` is topologically nilpotent, so is `exp a - 1`. -/
theorem exp_sub_one (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (NormedSpace.exp a - 1) := by
  obtain ⟨c, hc⟩ := exists_exp_sub_one_eq_mul ha
  exact hc ▸ ha.mul_right c

/-- If `u - 1` is topologically nilpotent, so is `log u`. -/
theorem log (hu : IsTopologicallyNilpotent (u - 1)) :
    IsTopologicallyNilpotent (NormedSpace.log u) := by
  obtain ⟨c, hc⟩ := exists_log_eq_mul hu
  exact hc ▸ hu.mul_right c

/-- `exp a - 1` lies in every ideal containing the topologically nilpotent `a`, so `exp a` lies
in its principal unit group. -/
theorem exp_sub_one_mem (ha : IsTopologicallyNilpotent a) {I : Ideal S} (haI : a ∈ I) :
    NormedSpace.exp a - 1 ∈ I := by
  obtain ⟨c, hc⟩ := exists_exp_sub_one_eq_mul ha
  exact hc ▸ I.mul_mem_right c haI

/-- `log u` lies in every ideal containing the topologically nilpotent `u - 1`. -/
theorem log_mem (hu : IsTopologicallyNilpotent (u - 1)) {I : Ideal S} (huI : u - 1 ∈ I) :
    NormedSpace.log u ∈ I := by
  obtain ⟨c, hc⟩ := exists_log_eq_mul hu
  exact hc ▸ I.mul_mem_right c huI

/-- The exponential of the logarithm: `exp (log u) = u` when `u - 1` is topologically
nilpotent. -/
theorem exp_log (hu : IsTopologicallyNilpotent (u - 1)) :
    NormedSpace.exp (NormedSpace.log u) = u := by
  rw [log_eq_aeval hu, exp_eq_aeval
      (isTopologicallyNilpotent_aeval_of_constantCoeff_eq_zero hu constantCoeff_log),
    ← PowerSeries.aeval_subst (HasSubst.of_constantCoeff_zero' constantCoeff_log)
      (continuous_aeval hu),
    subst_exp_log, map_add, map_one, PowerSeries.aeval_X hu, add_sub_cancel]

/-- The logarithm of the exponential: `log (exp a) = a` when `a` is topologically nilpotent. -/
theorem log_exp (ha : IsTopologicallyNilpotent a) : NormedSpace.log (NormedSpace.exp a) = a := by
  have hg : PowerSeries.aeval (R := S) ha (PowerSeries.exp S - 1) = NormedSpace.exp a - 1 := by
    rw [map_sub, map_one, exp_eq_aeval ha]
  have h := PowerSeries.aeval_subst (HasSubst.of_constantCoeff_zero' (by simp))
    (continuous_aeval ha) (hg ▸ ha.exp_sub_one) (PowerSeries.log S)
  rw [subst_log_exp_sub_one, PowerSeries.aeval_X ha] at h
  rw [log_eq_aeval ha.exp_sub_one]
  convert h.symm using 3
  exact hg.symm

/-- The exponential turns sums of topologically nilpotent elements into products. -/
theorem exp_add (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    NormedSpace.exp (a + b) = NormedSpace.exp a * NormedSpace.exp b := by
  have := IsLinearTopology.nonarchimedeanRing S
  have ha' := ha.hasSum_exp
  have hb' := hb.hasSum_exp
  rw [← ha'.tsum_eq, ← hb'.tsum_eq, ← (ha.add hb).hasSum_exp.tsum_eq,
    ha'.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hb'.summable
      (ha'.summable.mul_of_nonarchimedean hb'.summable)]
  refine tsum_congr fun n => ?_
  -- Coefficientwise, this is the formal identity `e^{aX} * e^{bX} = e^{(a + b)X}`.
  have h := congrArg (PowerSeries.coeff n) (PowerSeries.exp_mul_exp_eq_exp_add a b)
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    one_div] at h
  rw [Algebra.smul_def, mul_comm, ← h]
  refine Finset.sum_congr rfl fun kl _ => ?_
  simp only [Algebra.smul_def]
  ring

/-- The logarithm turns products into sums: `log (u * v) = log u + log v` when `u - 1` and
`v - 1` are topologically nilpotent. -/
theorem log_mul (hu : IsTopologicallyNilpotent (u - 1)) (hv : IsTopologicallyNilpotent (v - 1)) :
    NormedSpace.log (u * v) = NormedSpace.log u + NormedSpace.log v := by
  rw [← (hu.log.add hv.log).log_exp, hu.log.exp_add hv.log, hu.exp_log, hv.exp_log]

end IsTopologicallyNilpotent

namespace Ideal

variable [Algebra ℚ S] (I : Ideal S) (hI : ∀ a ∈ I, IsTopologicallyNilpotent a)

/-- **Exponential and logarithm**: for an ideal `I` of topologically nilpotent elements, the
exponential is an isomorphism from the additive group of `I` onto its principal unit group, with
inverse the logarithm. -/
def expMulEquiv : Multiplicative I ≃* I.principalUnitGroup where
  toFun a := ⟨⟨NormedSpace.exp (a.toAdd : S), NormedSpace.exp (-a.toAdd : S),
      by rw [← (hI _ a.toAdd.2).exp_add (hI _ (neg_mem a.toAdd.2)), add_neg_cancel,
        NormedSpace.exp_zero],
      by rw [← (hI _ (neg_mem a.toAdd.2)).exp_add (hI _ a.toAdd.2), neg_add_cancel,
        NormedSpace.exp_zero]⟩,
    mem_principalUnitGroup.2 ((hI _ a.toAdd.2).exp_sub_one_mem a.toAdd.2)⟩
  invFun u := .ofAdd ⟨NormedSpace.log ((u : Sˣ) : S),
    (hI _ (mem_principalUnitGroup.1 u.2)).log_mem (mem_principalUnitGroup.1 u.2)⟩
  left_inv a := Subtype.ext (hI _ a.toAdd.2).log_exp
  right_inv u := Subtype.ext (Units.ext (hI _ (mem_principalUnitGroup.1 u.2)).exp_log)
  map_mul' a b := Subtype.ext (Units.ext ((hI _ a.toAdd.2).exp_add (hI _ b.toAdd.2)))

/-- `Ideal.expMulEquiv` sends `a` to the unit `exp a`. -/
@[simp]
theorem coe_expMulEquiv_apply (a : I) :
    ((I.expMulEquiv hI (.ofAdd a) : Sˣ) : S) = NormedSpace.exp (a : S) :=
  (rfl)

/-- The inverse of `Ideal.expMulEquiv` sends a unit `u` to `log u`. -/
@[simp]
theorem coe_expMulEquiv_symm_apply (u : I.principalUnitGroup) :
    (((I.expMulEquiv hI).symm u).toAdd : S) = NormedSpace.log ((u : Sˣ) : S) :=
  (rfl)

end Ideal
