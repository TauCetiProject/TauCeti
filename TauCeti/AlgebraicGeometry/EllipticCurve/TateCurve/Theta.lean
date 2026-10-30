/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.ZPowers
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import TauCeti.Data.Int.MulPred
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# The theta function of the Tate curve

For a unit `q` of norm less than one in a complete normed field, the theta function of the Tate
curve is the bilateral series

`θ(u) = ∑_{n ∈ ℤ} (-1)ⁿ q^(n (n - 1) / 2) uⁿ`.

Its Laurent coefficients are explicit, and it satisfies the functional equations

`θ(q u) = -u⁻¹ θ(u)`,  `θ(u⁻¹) = -u⁻¹ θ(u)`.

By Jacobi's triple product identity it equals `∏_{n ≥ 1} (1 - qⁿ) (1 - qⁿ⁻¹ u) (1 - qⁿ / u)`;
this file neither uses nor proves that identity. Over a complete non-archimedean field it instead
computes the norm of `θ` directly: on the fundamental annulus `‖q‖ < ‖u‖ ≤ 1` one has
`‖θ(u)‖ = ‖1 - u‖`. Together with the functional equation this shows that the zeros of `θ` are
exactly the powers of `q`.

In Tate's theory the meromorphic functions on `Kˣ` invariant under `u ↦ q u` are expressed
through products of translates `θ(u / a)`, whose zeros are located by the zero set of `θ`.

## Main definitions

* `TauCeti.tateTheta q u`: the theta series `θ(u)` of the Tate curve with parameter `q`.

## Main results

* `TauCeti.hasSum_tateTheta`: the series converges for `‖q‖ < 1` in a complete normed field.
* `TauCeti.tateTheta_zpow_mul`, `TauCeti.tateTheta_self_mul`: the transformation law under
  `u ↦ qᵏ u`.
* `TauCeti.tateTheta_inv`: `θ(u⁻¹) = -u⁻¹ θ(u)`.
* `TauCeti.tateTheta_one`: `θ(1) = 0`.
* `TauCeti.norm_tateTheta`: `‖θ(u)‖ = ‖1 - u‖` on the fundamental annulus `‖q‖ < ‖u‖ ≤ 1`, over a
  complete non-archimedean field.
* `TauCeti.tateTheta_eq_zero_iff`: `θ(u) = 0` exactly when `u ∈ q^ℤ`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
* P. Roquette, *Analytic theory of elliptic functions over local fields*, Hamburger
  Mathematische Einzelschriften (N.F.) 1, Vandenhoeck & Ruprecht (1970).
-/

public section

open Filter Topology

namespace TauCeti

variable {K : Type*} [NormedField K]

/-! ### The series -/

/-- The theta function of the Tate curve with parameter `q`, the bilateral series
`θ(u) = ∑_{n ∈ ℤ} (-1)ⁿ q^(n (n - 1) / 2) uⁿ`. The series converges when `‖q‖ < 1` and the
field is complete (`TauCeti.hasSum_tateTheta`); otherwise the value is that of `tsum`. -/
noncomputable def tateTheta (q u : Kˣ) : K :=
  ∑' n : ℤ, (-1) ^ n * (q : K) ^ (n * (n - 1) / 2) * (u : K) ^ n

/-- The series formula for the theta function. -/
theorem tateTheta_def (q u : Kˣ) :
    tateTheta q u = ∑' n : ℤ, (-1) ^ n * (q : K) ^ (n * (n - 1) / 2) * (u : K) ^ n := (rfl)

/-- The `n`-th term `(-1)ⁿ q^(n (n - 1) / 2) uⁿ` of the theta series. -/
private noncomputable def thetaTerm (q u : Kˣ) (n : ℤ) : K :=
  (-1) ^ n * (q : K) ^ (n * (n - 1) / 2) * (u : K) ^ n

private theorem tateTheta_eq_tsum_thetaTerm (q u : Kˣ) :
    tateTheta q u = ∑' n : ℤ, thetaTerm q u n := (rfl)

/-- Consecutive terms of the theta series differ by the factor `-qⁿ u`. -/
private theorem thetaTerm_add_one (q u : Kˣ) (n : ℤ) :
    thetaTerm q u (n + 1) = -((q : K) ^ n * u) * thetaTerm q u n := by
  rw [thetaTerm, thetaTerm, Int.add_mul_add_sub_one_ediv_two n 1,
    zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_add₀ q.ne_zero, zpow_add₀ q.ne_zero,
    zpow_add₀ u.ne_zero]
  simp only [zpow_one, sub_self, mul_zero, Int.zero_ediv, zpow_zero, mul_one]
  ring

private theorem summable_thetaTerm [CompleteSpace K] (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Summable (thetaTerm q u) := by
  have hne (n : ℤ) : thetaTerm q u n ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (zpow_ne_zero _ q.ne_zero)) (zpow_ne_zero _ u.ne_zero)
  -- The ratio of consecutive norms is `‖q‖ⁿ C` in both directions, which tends to zero.
  have ht (C : ℝ) : Tendsto (fun n : ℕ ↦ ‖(q : K)‖ ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq).mul_const C
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine summable_of_ratio_test_tendsto_lt_one zero_lt_one (.of_forall fun n ↦ hne n)
      ((ht ‖(u : K)‖).congr fun n ↦ ?_)
    rw [Nat.cast_succ, thetaTerm_add_one, norm_mul, norm_neg, norm_mul, norm_zpow, zpow_natCast,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr (hne n))]
  · refine summable_of_ratio_test_tendsto_lt_one zero_lt_one (.of_forall fun n ↦ hne _)
      ((ht (‖(q : K)‖ ^ 2 / ‖(u : K)‖)).congr fun n ↦ ?_)
    -- Apply the step law at index `-(n + 2)`. Both indices are then written with the natural
    -- number `n + 2`, which lets `zpow_natCast` turn `‖q‖ ^ (n + 2)` into a natural power.
    have hstep : -((n : ℤ) + 2) + 1 = -((n : ℤ) + 1) := by ring
    have hcast : (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
    have hidx : -(((n + 1 : ℕ) : ℤ) + 1) = -(((n + 2 : ℕ) : ℤ)) := by push_cast; ring
    have h := congrArg norm (thetaTerm_add_one q u (-((n : ℤ) + 2)))
    rw [hstep, norm_mul, norm_neg, norm_mul, norm_zpow, zpow_neg, hcast, zpow_natCast] at h
    rw [hidx, h]
    have hq₀ : ‖(q : K)‖ ≠ 0 := norm_ne_zero_iff.mpr q.ne_zero
    have hu₀ : ‖(u : K)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
    have h₀ : ‖thetaTerm q u (-((n + 2 : ℕ) : ℤ))‖ ≠ 0 := norm_ne_zero_iff.mpr (hne _)
    field_simp
    ring

/-- **The theta series converges** for `‖q‖ < 1` in a complete normed field. -/
theorem hasSum_tateTheta [CompleteSpace K] (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n : ℤ ↦ (-1) ^ n * (q : K) ^ (n * (n - 1) / 2) * (u : K) ^ n)
      (tateTheta q u) :=
  (summable_thetaTerm q u hq).hasSum

/-! ### Functional equations -/

private theorem thetaTerm_add (q u : Kˣ) (n k : ℤ) :
    thetaTerm q u (n + k) =
      (-1) ^ k * (q : K) ^ (k * (k - 1) / 2) * (u : K) ^ k * thetaTerm q (q ^ k * u) n := by
  rw [thetaTerm, thetaTerm, Int.add_mul_add_sub_one_ediv_two,
    zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_add₀ q.ne_zero, zpow_add₀ q.ne_zero,
    zpow_add₀ u.ne_zero, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_zpow, ← zpow_mul,
    mul_comm k n]
  ring

/-- **The transformation law of the theta function** under `u ↦ qᵏ u`. -/
theorem tateTheta_zpow_mul (q u : Kˣ) (k : ℤ) :
    tateTheta q (q ^ k * u) =
      (-1) ^ k * (q : K) ^ (-(k * (k - 1) / 2)) * (u : K) ^ (-k) * tateTheta q u := by
  have h := (Equiv.addRight k).tsum_eq (thetaTerm q u)
  simp only [Equiv.coe_addRight, thetaTerm_add, tsum_mul_left] at h
  have h₁ : (-1 : K) ^ k * (-1) ^ k = 1 := by
    rw [← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  have h₂ : (q : K) ^ (-(k * (k - 1) / 2)) * (q : K) ^ (k * (k - 1) / 2) = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ q.ne_zero)]
  have h₃ : (u : K) ^ (-k) * (u : K) ^ k = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ u.ne_zero)]
  rw [tateTheta_eq_tsum_thetaTerm, tateTheta_eq_tsum_thetaTerm, ← h]
  calc ∑' n, thetaTerm q (q ^ k * u) n
      = ((-1) ^ k * (-1) ^ k) * ((q : K) ^ (-(k * (k - 1) / 2)) * (q : K) ^ (k * (k - 1) / 2)) *
          ((u : K) ^ (-k) * (u : K) ^ k) * ∑' n, thetaTerm q (q ^ k * u) n := by
        rw [h₁, h₂, h₃, one_mul, one_mul, one_mul]
    _ = _ := by ring

/-- Multiplying the parameter by `q` multiplies the theta function by `-u⁻¹`. -/
@[simp]
theorem tateTheta_self_mul (q u : Kˣ) :
    tateTheta q (q * u) = -(u : K)⁻¹ * tateTheta q u := by
  simpa using tateTheta_zpow_mul q u 1

private theorem thetaTerm_one_sub (q u : Kˣ) (n : ℤ) :
    thetaTerm q u⁻¹ (1 - n) = -(u : K)⁻¹ * thetaTerm q u n := by
  rw [thetaTerm, thetaTerm, Int.one_sub_mul_one_sub_sub_one_ediv_two, sub_eq_add_neg,
    zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_one, zpow_neg, ← inv_zpow, inv_neg_one,
    Units.val_inv_eq_inv_val, inv_zpow', neg_add, neg_neg, zpow_add₀ u.ne_zero, zpow_neg_one]
  field_simp

/-- **The inversion law of the theta function**: `θ(u⁻¹) = -u⁻¹ θ(u)`. -/
@[simp]
theorem tateTheta_inv (q u : Kˣ) : tateTheta q u⁻¹ = -(u : K)⁻¹ * tateTheta q u := by
  have h := (Equiv.subLeft (1 : ℤ)).tsum_eq (thetaTerm q u⁻¹)
  simp only [Equiv.subLeft_apply, thetaTerm_one_sub, tsum_mul_left] at h
  rw [tateTheta_eq_tsum_thetaTerm, tateTheta_eq_tsum_thetaTerm, ← h]

/-- The pair of terms of indices `k + 1` and `-k` of the theta series, divided by `u - 1`:
`(-1)ᵏ⁺¹ q^(k (k + 1) / 2) u⁻ᵏ (1 + u + ⋯ + u²ᵏ)`. -/
private noncomputable def pairTerm (q u : Kˣ) (k : ℕ) : K :=
  (-1) ^ ((k : ℤ) + 1) * (q : K) ^ (((k : ℤ) + 1) * k / 2) * (u : K) ^ (-(k : ℤ)) *
    ∑ j ∈ Finset.range (2 * k + 1), (u : K) ^ j

private theorem pairTerm_zero (q u : Kˣ) : pairTerm q u 0 = -1 := by
  simp [pairTerm]

/-- The terms of indices `k + 1` and `-k` of the theta series combine to `(u - 1)` times the
paired term. -/
private theorem thetaTerm_add_one_add_thetaTerm_neg (q u : Kˣ) (k : ℕ) :
    thetaTerm q u ((k : ℤ) + 1) + thetaTerm q u (-k) = ((u : K) - 1) * pairTerm q u k := by
  have hT : -(k : ℤ) * (-(k : ℤ) - 1) / 2 = ((k : ℤ) + 1) * k / 2 := by
    congr 1
    ring
  have hgeom := geom_sum_mul (u : K) (2 * k + 1)
  rw [thetaTerm, thetaTerm, pairTerm, hT, add_sub_cancel_right, zpow_neg (-1 : K), ← inv_zpow,
    inv_neg_one, zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_one, zpow_neg, zpow_natCast,
    zpow_add₀ u.ne_zero, zpow_natCast, zpow_one]
  field_simp
  linear_combination hgeom

/-- The theta series, grouped into the pairs of terms of indices `k + 1` and `-k`. -/
private theorem hasSum_thetaTerm_pair [CompleteSpace K] (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun k : ℕ ↦ thetaTerm q u ((k : ℤ) + 1) + thetaTerm q u (-k)) (tateTheta q u) := by
  have h := ((Equiv.addRight (1 : ℤ)).hasSum_iff.mpr
    (summable_thetaTerm q u hq).hasSum).nat_add_neg_add_one
  rw [tateTheta_eq_tsum_thetaTerm]
  simpa only [Function.comp_apply, Equiv.coe_addRight, neg_add_rev, neg_add_cancel_comm] using h

/-- **The theta function vanishes at `1`.** -/
@[simp]
theorem tateTheta_one (q : Kˣ) : tateTheta q 1 = 0 := by
  by_cases hs : Summable (thetaTerm q 1)
  · have h := ((Equiv.addRight (1 : ℤ)).hasSum_iff.mpr hs.hasSum).nat_add_neg_add_one
    simp only [Function.comp_apply, Equiv.coe_addRight, neg_add_rev, neg_add_cancel_comm,
      thetaTerm_add_one_add_thetaTerm_neg, Units.val_one, sub_self, zero_mul] at h
    exact h.unique hasSum_zero
  · rw [tateTheta_eq_tsum_thetaTerm, tsum_eq_zero_of_not_summable hs]

/-! ### The norm on the fundamental annulus and the zeros -/

variable [IsUltrametricDist K]

/-- On the fundamental annulus every paired term after the first has norm at most
`‖q‖ / ‖u‖ < 1`. -/
private theorem norm_pairTerm_succ_le (q u : Kˣ) (hu₁ : ‖(q : K)‖ < ‖(u : K)‖)
    (hu₂ : ‖(u : K)‖ ≤ 1) (k : ℕ) : ‖pairTerm q u (k + 1)‖ ≤ ‖(q : K)‖ / ‖(u : K)‖ := by
  have hu₀ : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hgeom : ‖∑ j ∈ Finset.range (2 * (k + 1) + 1), (u : K) ^ j‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ ↦ by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hu₂
  -- The exponent `(k + 2) (k + 1) / 2` of `q` is at least `k + 1`.
  have hT : ((k + 1 : ℕ) : ℤ) ≤ (((k + 1 : ℕ) : ℤ) + 1) * (k + 1 : ℕ) / 2 := by
    refine Int.le_ediv_of_mul_le two_pos ?_
    push_cast
    nlinarith
  have hpow : ‖(q : K)‖ ^ ((((k + 1 : ℕ) : ℤ) + 1) * (k + 1 : ℕ) / 2) ≤ ‖(q : K)‖ ^ (k + 1) := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ (norm_pos_iff.mpr q.ne_zero) (hu₁.le.trans hu₂) hT
  rw [pairTerm, norm_mul, norm_mul, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
    norm_zpow, norm_zpow, zpow_neg, zpow_natCast]
  calc ‖(q : K)‖ ^ ((((k + 1 : ℕ) : ℤ) + 1) * (k + 1 : ℕ) / 2) * (‖(u : K)‖ ^ (k + 1))⁻¹ *
        ‖∑ j ∈ Finset.range (2 * (k + 1) + 1), (u : K) ^ j‖
      ≤ ‖(q : K)‖ ^ (k + 1) * (‖(u : K)‖ ^ (k + 1))⁻¹ * 1 := by gcongr
    _ = (‖(q : K)‖ / ‖(u : K)‖) ^ (k + 1) := by rw [mul_one, div_pow, div_eq_mul_inv]
    _ ≤ ‖(q : K)‖ / ‖(u : K)‖ :=
      pow_le_of_le_one (div_nonneg (norm_nonneg _) hu₀.le) ((div_le_one hu₀).mpr hu₁.le)
        (Nat.succ_ne_zero k)

variable [CompleteSpace K]

/-- **The norm of the theta function on the fundamental annulus.** Over a complete
non-archimedean field, `‖θ(u)‖ = ‖1 - u‖` whenever `‖q‖ < ‖u‖ ≤ 1`. In particular `θ` has no
zero on that annulus other than `u = 1`. -/
theorem norm_tateTheta (q u : Kˣ) (hu₁ : ‖(q : K)‖ < ‖(u : K)‖) (hu₂ : ‖(u : K)‖ ≤ 1) :
    ‖tateTheta q u‖ = ‖1 - (u : K)‖ := by
  have hq : ‖(q : K)‖ < 1 := hu₁.trans_le hu₂
  have h := hasSum_thetaTerm_pair q u hq
  simp only [thetaTerm_add_one_add_thetaTerm_neg] at h
  rcases eq_or_ne (u : K) 1 with hu | hu
  · simp only [hu, sub_self, zero_mul] at h
    rw [h.unique hasSum_zero, hu, sub_self]
  -- Divided by `u - 1`, the series is `-1` plus terms of norm below one.
  have hS : HasSum (pairTerm q u) (tateTheta q u / ((u : K) - 1)) := by
    convert h.div_const ((u : K) - 1) using 1
    funext k
    rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr hu)]
  have htail : ‖∑' k, pairTerm q u (k + 1)‖ < 1 :=
    (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
      (norm_pairTerm_succ_le q u hu₁ hu₂)).trans_lt
      ((div_lt_one (norm_pos_iff.mpr u.ne_zero)).mpr hu₁)
  have hnorm : ‖tateTheta q u / ((u : K) - 1)‖ = 1 := by
    rw [← hS.tsum_eq, hS.summable.tsum_eq_zero_add, pairTerm_zero,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact
        htail.ne'), norm_neg, norm_one, max_eq_left htail.le]
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hu))] at hnorm
  rw [hnorm, norm_sub_rev]

/-- **The zeros of the theta function** are exactly the powers of `q`. -/
theorem tateTheta_eq_zero_iff (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateTheta q u = 0 ↔ u ∈ Subgroup.zpowers q := by
  constructor
  · intro h
    obtain ⟨n, ⟨hn₁, hn₂⟩, -⟩ := existsUnique_norm_zpow_mul_mem_Ioc q u hq
    have h' : tateTheta q (q ^ n * u) = 0 := by rw [tateTheta_zpow_mul, h, mul_zero]
    rw [← norm_eq_zero, norm_tateTheta q _ hn₁ hn₂, norm_eq_zero, sub_eq_zero, eq_comm,
      Units.val_eq_one] at h'
    exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by rw [zpow_neg, inv_eq_of_mul_eq_one_right h']⟩
  · rintro ⟨n, rfl⟩
    simpa using tateTheta_zpow_mul q 1 n

end TauCeti

end
