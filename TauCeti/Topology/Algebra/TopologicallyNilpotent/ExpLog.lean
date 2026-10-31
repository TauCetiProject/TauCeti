/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import TauCeti.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries
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
`NormedSpace.exp_add_of_commute_of_mem_ball`. Since `exp a - 1` lies in every open ideal
containing `a`, the exponential is continuous on an ideal of topologically nilpotent elements, so
it carries convergent sums to convergent products, as Mathlib's `HasSum.exp` does for complete
normed algebras. A continuous derivation differentiates the
logarithm series termwise, and the geometric series for `u⁻¹` gives `u * D (log u) = D u`.

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
* `IsTopologicallyNilpotent.hasSum_log_one_sub`: `log (1 - a) = -∑ aⁿ⁺¹ / (n + 1)`.
* `HasSum.exp_of_mem_ideal`: inside an ideal of topologically nilpotent elements, the exponential
  turns convergent sums into convergent products.
* `IsTopologicallyNilpotent.mul_derivation_log`: a continuous derivation `D` satisfies
  `u * D (log u) = D u`.
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

/-- `exp a - 1` lies in every ideal containing the topologically nilpotent `a`. -/
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

/-- For a topologically nilpotent `a`, the logarithm of `1 - a` is `-∑ₙ aⁿ⁺¹ / (n + 1)`. -/
theorem hasSum_log_one_sub (ha : IsTopologicallyNilpotent a) :
    HasSum (fun n : ℕ => -(((n + 1 : ℕ) : ℚ)⁻¹ • a ^ (n + 1))) (NormedSpace.log (1 - a)) := by
  have h := hasSum_log (u := 1 - a) (by rw [sub_sub_cancel_left]; exact ha.neg)
  rw [← hasSum_nat_add_iff' 1] at h
  convert h using 1
  · funext n
    have hneg : (-a) ^ (n + 1) = ((-1 : ℚ) ^ (n + 1)) • a ^ (n + 1) := by
      simp [neg_pow a, Algebra.smul_def]
    -- The sign of the `(n + 1)`-th term of the logarithm series cancels that of `(-a) ^ (n + 1)`.
    have hsign : (-1 : ℚ) ^ (n + 1 + 1) / (n + 1 : ℕ) * (-1) ^ (n + 1) = -((n + 1 : ℕ) : ℚ)⁻¹ := by
      rw [div_mul_eq_mul_div, ← pow_add, Odd.neg_one_pow ⟨n + 1, by ring⟩, neg_div, one_div]
    rw [sub_sub_cancel_left, hneg]
    simp only [smul_smul, hsign, neg_smul]
  · simp

/-- A continuous derivation `D` differentiates the logarithm as `D (log u) = u⁻¹ * D u`, in the
form `u * D (log u) = D u`, when `u - 1` is topologically nilpotent. -/
theorem mul_derivation_log {R : Type*} [CommSemiring R] [Algebra R S] (D : Derivation R S S)
    (hD : Continuous D) (hu : IsTopologicallyNilpotent (u - 1)) :
    u * D (NormedSpace.log u) = D u := by
  -- The derivative of the `n + 1`-st term of the logarithm series is `(1 - u) ^ n * D u`.
  have hterm (n : ℕ) : D (((-1) ^ (n + 1 + 1) / (n + 1 : ℕ) : ℚ) • (u - 1) ^ (n + 1)) =
      (-(u - 1)) ^ n * D (u - 1) := by
    have hq : ((-1) ^ (n + 1 + 1) / (n + 1 : ℕ) : ℚ) * (n + 1 : ℕ) = (-1) ^ n := by
      field_simp
      ring
    rw [map_rat_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, hq, neg_pow (u - 1), mul_assoc]
    simp [Algebra.smul_def]
  have hlog : HasSum (fun n : ℕ => (-(u - 1)) ^ n * D (u - 1)) (D (NormedSpace.log u)) := by
    have h := (hasSum_nat_add_iff' 1).2 (hu.hasSum_log.map D hD)
    rw [Finset.sum_range_one] at h
    convert h using 1
    · exact funext fun n => (hterm n).symm
    · simp
  have := IsLinearTopology.nonarchimedeanAddGroup S (M := S)
  have hgeom := hu.neg.summable_pow
  rw [hlog.unique (hgeom.hasSum.mul_right _), ← mul_assoc]
  -- Write the remaining factor `u` as `1 - q` with `q = -(u - 1)`, so that the geometric series
  -- identity `(1 - q) * ∑ qⁿ = 1` applies.
  nth_rw 1 [show u = 1 - -(u - 1) by ring]
  rw [hgeom.one_sub_mul_tsum_pow, one_mul, map_sub, Derivation.map_one_eq_zero, sub_zero]

end IsTopologicallyNilpotent

/-- **The exponential of a sum is the product of the exponentials.** If `f` has sum `a`, with all
`f i` and `a` in an ideal `I` of topologically nilpotent elements, then `exp ∘ f` has product
`exp a`. -/
theorem HasSum.exp_of_mem_ideal [Algebra ℚ S] {ι : Type*} {I : Ideal S}
    (hI : ∀ a ∈ I, IsTopologicallyNilpotent a) {f : ι → S} {a : S} (h : HasSum f a)
    (hf : ∀ i, f i ∈ I) (ha : a ∈ I) :
    HasProd (NormedSpace.exp ∘ f) (NormedSpace.exp a) := by
  have hs (s : Finset ι) : ∑ i ∈ s, f i ∈ I := I.sum_mem fun i _ => hf i
  have hprod (s : Finset ι) :
      ∏ i ∈ s, NormedSpace.exp (f i) = NormedSpace.exp (∑ i ∈ s, f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [NormedSpace.exp_zero]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        (hI _ (hf i)).exp_add (hI _ (hs s))]
  -- Near `a`, `exp (∑ i ∈ s, f i) - exp a = exp a * (exp (∑ i ∈ s, f i - a) - 1)` lies in any
  -- open ideal containing `∑ i ∈ s, f i - a`.
  have hexp : Tendsto (fun s : Finset ι => NormedSpace.exp (∑ i ∈ s, f i)) atTop
      (𝓝 (NormedSpace.exp a)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have h' := tendsto_sub_nhds_zero_iff.2 h
    refine IsLinearTopology.hasBasis_ideal.tendsto_right_iff.2 fun J hJ => ?_
    filter_upwards [h'.eventually (IsLinearTopology.hasBasis_ideal.mem_of_mem hJ)] with s hsJ
    have hsI : ∑ i ∈ s, f i - a ∈ I := sub_mem (hs s) ha
    have heq : ∑ i ∈ s, f i = a + (∑ i ∈ s, f i - a) := by abel
    rw [SetLike.mem_coe, heq, (hI _ ha).exp_add (hI _ hsI), ← _root_.mul_sub_one]
    exact J.mul_mem_left _ ((hI _ hsI).exp_sub_one_mem hsJ)
  -- As for Mathlib's `HasSum.exp`, the partial products are the exponentials of partial sums.
  exact Tendsto.congr (fun s => (hprod s).symm) hexp

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
