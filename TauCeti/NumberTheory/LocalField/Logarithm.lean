/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.NumberTheory.Padics.PadicValNat
import TauCeti.RingTheory.Valuation.PowSubPow
import TauCeti.Topology.Algebra.ValuativeRel.HasSum

/-!
# The logarithm on the principal units of a finite extension of `ℚ_[p]`

Let `K` be a finite extension of `ℚ_[p]`, with absolute ramification index `e`. This file studies
Mathlib's logarithm `NormedSpace.log x = ∑ n, (-1) ^ (n + 1) / n * (x - 1) ^ n` on `K`.

In this overview `v_K` denotes the normalized *additive* valuation of `K`, with `v_K(π) = 1` for
a uniformizer `π`, so greater `v_K` means deeper. The normalized valuation of `n` in `K` is
`v_K(n) = e * padicValNat p n`, which grows only logarithmically in `n`. Hence the series
converges on the whole disc `v_K(x - 1) ≥ 1`, that is on `U(K,1)`: this is
`TauCeti.hasSum_log_of_mem_unitFiltration_one`. The same estimate bounds the difference of two
logarithm series uniformly, so the logarithm is continuous on `U(K,1)`.

At a depth `i` with `(p - 1) * i > e`, the terms of degree `n ≥ 2` are strictly deeper than the
linear term, uniformly in the argument: for `x, y ∈ 𝓂[K] ^ i` one has
`e * v_p(n) < i * (n - 1)`, and hence
`v_K((x ^ n - y ^ n) / n) > v_K(x - y)`. Summing, the logarithm is an isometry on `U(K,i)`:

`v_K(log u - log w) = v_K(u - w)` for `u, w ∈ U(K,i)`.

In particular it is injective on `U(K,i)`, and `v_K(log u) = v_K(u - 1)`, so it maps
`U(K,i)` into `𝓂[K] ^ i`. These are the analytic inputs for the isomorphism
`U(K,i) ≃ 𝓂[K] ^ i` given by the logarithm, with the exponential as its inverse.

## Main results

* `TauCeti.hasSum_log_of_mem_unitFiltration_one`: the logarithm series converges to
  `NormedSpace.log u` for every `u ∈ U(K,1)`.
* `TauCeti.continuous_log_unitFiltration`: the logarithm is continuous on `U(K,i)` for `i ≥ 1`.
* `TauCeti.valuation_log_sub_log_sub_sub_lt`: on `U(K,i)` with `(p - 1) * i > e`, the difference
  `log u - log w` agrees with `u - w` up to strictly deeper terms.
* `TauCeti.valuation_log_sub_log`: the logarithm is an isometry on `U(K,i)`.
* `TauCeti.valuation_log`: `v(log u) = v(u - 1)` on `U(K,i)`, and
  `TauCeti.exists_mem_maximalIdeal_pow_eq_log`: `log u` lies in `𝓂[K] ^ i`.
* `TauCeti.log_unitFiltration_injective`: the logarithm is injective on `U(K,i)`.

## Implementation notes

The valuation in the statements is Mathlib's multiplicative `ValuativeRel.valuation K`, for which
greater depth means a smaller value; an inequality `v_K(a) > v_K(b)` above is stated as
`valuation K a < valuation K b`. The depth hypothesis is the integer inequality
`absoluteRamificationIndex K p < (p - 1) * i`, so that no division of natural numbers occurs.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
* Mathlib's `NormedSpace.log` (Kevin Buzzard), whose TODO list asks for ultrametric convergence
  and for `‖log x‖ = ‖x - 1‖`; here these are proved for finite extensions of `ℚ_[p]`, the
  latter on the deep units `U(K,i)` with `(p - 1) * i > e`.
-/

public section
noncomputable section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField NormedSpace

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The valuation of a logarithm-series term: dividing by `n` multiplies the valuation by
`v(π) ^ (-e * padicValNat p n)`. -/
private theorem valuation_logSeries_coeff_mul (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]
    {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) (z : K) :
    valuation K ((-1) ^ (n + 1) / n * z) *
        valuation K (π : K) ^ (absoluteRamificationIndex K p * padicValNat p n) =
      valuation K z := by
  have hnK : (n : K) ≠ 0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
        (Nat.cast_ne_zero.mpr hn : (n : ℚ_[p]) ≠ 0)
  -- The power of `v(π)` is the valuation of `n`, which cancels the division by `n`.
  have hcancel : (-1) ^ (n + 1) / n * z * n = (-1) ^ (n + 1) * z := by
    field_simp
  rw [← natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p n hn,
    ← valuation_natCast_eq_pow hπ, ← map_mul, hcancel]
  simp

/-- On a finite extension of `ℚ_[p]`, the logarithm series converges to `NormedSpace.log u` for
every principal unit `u ∈ U(K,1)`. -/
theorem hasSum_log_of_mem_unitFiltration_one (p : ℕ) [Fact p.Prime]
    [FinitePadicExtension K p] {u : Kˣ} (hu : u ∈ unitFiltration K 1) :
    HasSum (fun n : ℕ => (-1) ^ (n + 1) / n * ((u : K) - 1) ^ n) (log (u : K)) := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hγ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hγ0 : 0 < valuation K (π : K) := by
    simpa [zero_lt_iff] using hπ.ne_zero
  have hxγ : valuation K ((u : K) - 1) ≤ valuation K (π : K) := by
    simpa using ((mem_unitFiltration_iff_valuation_le hπ).mp hu).2
  have hsum : Summable (fun n : ℕ => (-1) ^ (n + 1) / n * ((u : K) - 1) ^ n) := by
    let _ : NonarchimedeanRing K := by
      rw [(valuation K).toTopologicalSpace_eq]
      exact ValuativeRel.nonarchimedeanRing K
    let _ := IsTopologicalAddGroup.rightUniformSpace K
    let _ := isUniformAddGroup_of_addCommGroup (G := K)
    rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
    refine (IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff.mpr fun δ hδ => ?_
    obtain ⟨M, hM⟩ := exists_pow_lt₀ hγ1 (Units.mk0 δ hδ)
    filter_upwards [eventually_add_mul_padicValNat_le p M (absoluteRamificationIndex K p),
      eventually_ne_atTop 0] with n hn hn0
    refine lt_of_le_of_lt ?_ hM
    rw [← mul_le_mul_iff_left₀ (pow_pos hγ0 (absoluteRamificationIndex K p * padicValNat p n)),
      valuation_logSeries_coeff_mul p hπ hn0, ← pow_add, map_pow]
    exact (pow_le_pow_left₀ zero_le hxγ n).trans (pow_le_pow_right_of_le_one' hγ1.le hn)
  rw [log_eq_tsum K]
  simpa only [smul_eq_mul] using hsum.hasSum

/-- The difference of two logarithm series on `U(K,1)`, summed termwise. -/
private theorem hasSum_log_sub_log (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p] {u w : Kˣ}
    (hu : u ∈ unitFiltration K 1) (hw : w ∈ unitFiltration K 1) :
    HasSum (fun n : ℕ => (-1) ^ (n + 1) / n * (((u : K) - 1) ^ n - ((w : K) - 1) ^ n))
      (log (u : K) - log (w : K)) := by
  simpa only [mul_sub] using
    (hasSum_log_of_mem_unitFiltration_one p hu).sub (hasSum_log_of_mem_unitFiltration_one p hw)

/-- On `𝓂[K]`, a term of degree `n ≥ 1` of the difference of two logarithm series is bounded by
`v(a - b)` up to a factor `v(π) ^ (-(C + 1))` independent of `n`, where `e * v_p(n) ≤ n + C`. -/
private theorem valuation_logSeries_coeff_mul_pow_sub_pow_mul_le (p : ℕ) [Fact p.Prime]
    [FinitePadicExtension K p] {π : 𝒪[K]} (hπ : Irreducible π) {C : ℕ}
    (hC : ∀ n, absoluteRamificationIndex K p * padicValNat p n ≤ n + C) {a b : K}
    (ha : valuation K a ≤ valuation K (π : K)) (hb : valuation K b ≤ valuation K (π : K))
    {n : ℕ} (hn : n ≠ 0) :
    valuation K ((-1) ^ (n + 1) / n * (a ^ n - b ^ n)) * valuation K (π : K) ^ (C + 1) ≤
      valuation K (a - b) := by
  have hγ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hγ0 : 0 < valuation K (π : K) := by
    simpa [zero_lt_iff] using hπ.ne_zero
  have hexp : absoluteRamificationIndex K p * padicValNat p n ≤ n - 1 + (C + 1) := by
    have := hC n
    omega
  rw [← mul_le_mul_iff_left₀ (pow_pos hγ0 (n - 1))]
  calc valuation K ((-1) ^ (n + 1) / n * (a ^ n - b ^ n)) * valuation K (π : K) ^ (C + 1) *
        valuation K (π : K) ^ (n - 1)
      = valuation K ((-1) ^ (n + 1) / n * (a ^ n - b ^ n)) *
          valuation K (π : K) ^ (n - 1 + (C + 1)) := by
        rw [mul_assoc, ← pow_add, add_comm (C + 1)]
    _ ≤ valuation K ((-1) ^ (n + 1) / n * (a ^ n - b ^ n)) *
          valuation K (π : K) ^ (absoluteRamificationIndex K p * padicValNat p n) :=
        mul_le_mul_right (pow_le_pow_right_of_le_one' hγ1.le hexp) _
    _ = valuation K (a ^ n - b ^ n) := valuation_logSeries_coeff_mul p hπ hn _
    _ ≤ valuation K (a - b) * valuation K (π : K) ^ (1 * (n - 1)) := by
        rw [one_mul]
        exact (valuation K).map_pow_sub_pow_le ha hb n
    _ = valuation K (a - b) * valuation K (π : K) ^ (n - 1) := by rw [one_mul]

/-- On a finite extension of `ℚ_[p]`, the logarithm is continuous on `U(K,i)` for every
`i ≥ 1`. -/
theorem continuous_log_unitFiltration (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p] {i : ℕ}
    (hi : 1 ≤ i) : Continuous fun u : unitFiltration K i => log ((u : Kˣ) : K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨C, hC⟩ := exists_mul_padicValNat_le_add p (absoluteRamificationIndex K p)
  have hπ0 : valuation K (π : K) ≠ 0 := by
    simpa using hπ.ne_zero
  have hc : Continuous fun u : unitFiltration K i => ((u : Kˣ) : K) :=
    Units.continuous_val.comp continuous_subtype_val
  have hdisc : ∀ u : unitFiltration K i, valuation K (((u : Kˣ) : K) - 1) ≤ valuation K (π : K) :=
    fun u => by simpa using ((mem_unitFiltration_iff_valuation_le hπ).mp
      (unitFiltration_antitone hi u.2)).2
  refine continuous_iff_continuousAt.2 fun u => ?_
  refine (IsValuativeTopology.hasBasis_nhds _).tendsto_right_iff.2 fun γ _ => ?_
  -- Inputs within `γ * v(π) ^ (C + 1)` of `u` have logarithms within `γ` of `log u`.
  filter_upwards [(IsValuativeTopology.hasBasis_nhds _).tendsto_right_iff.1 (hc.tendsto u)
    (γ * Units.mk0 _ hπ0 ^ (C + 1)) trivial] with w hw
  refine valuation_lt_of_hasSum (hasSum_log_sub_log p (unitFiltration_antitone hi w.2)
    (unitFiltration_antitone hi u.2)) γ fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [← mul_lt_mul_iff_left₀ (pow_pos (zero_lt_iff.mpr hπ0) (C + 1))]
  refine (valuation_logSeries_coeff_mul_pow_sub_pow_mul_le p hπ hC (hdisc w) (hdisc u)
    hn).trans_lt ?_
  simpa only [sub_sub_sub_cancel_right, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_mk0] using hw

variable {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p]

/-- At a depth with `(p - 1) * i > e`, a term of degree `n ≥ 2` of the difference of two
logarithm series on `𝓂[K] ^ i` is smaller than the linear term by at least a factor `v(π)`. -/
private theorem valuation_logSeries_coeff_mul_pow_sub_pow_le {π : 𝒪[K]} (hπ : Irreducible π)
    {i : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i) {a b : K}
    (ha : valuation K a ≤ valuation K (π : K) ^ i) (hb : valuation K b ≤ valuation K (π : K) ^ i)
    {n : ℕ} (hn : 2 ≤ n) :
    valuation K ((-1) ^ (n + 1) / n * (a ^ n - b ^ n)) ≤
      valuation K (a - b) * valuation K (π : K) := by
  have hγ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hγ0 : 0 < valuation K (π : K) := by
    simpa [zero_lt_iff] using hπ.ne_zero
  rw [← mul_le_mul_iff_left₀ (pow_pos hγ0 (absoluteRamificationIndex K p * padicValNat p n)),
    valuation_logSeries_coeff_mul p hπ (by omega)]
  calc valuation K (a ^ n - b ^ n)
      ≤ valuation K (a - b) * (valuation K (π : K) ^ i) ^ (n - 1) :=
        (valuation K).map_pow_sub_pow_le ha hb n
    _ ≤ valuation K (a - b) * valuation K (π : K) ^
          (absoluteRamificationIndex K p * padicValNat p n + 1) := by
        rw [← pow_mul]
        exact mul_le_mul_right (pow_le_pow_right_of_le_one' hγ1.le
          (mul_padicValNat_lt_mul_sub_one hi hn)) _
    _ = _ := by rw [pow_succ, mul_right_comm, mul_assoc]

/-- On `U(K,i)` with `(p - 1) * i > e`, the logarithm agrees with the identity up to strictly
deeper terms: `v(log u - log w - (u - w)) < v(u - w)` for `u ≠ w`, where `v` is the
multiplicative valuation. -/
theorem valuation_log_sub_log_sub_sub_lt {i : ℕ}
    (hi : absoluteRamificationIndex K p < (p - 1) * i) {u w : Kˣ}
    (hu : u ∈ unitFiltration K i) (hw : w ∈ unitFiltration K i) (huw : u ≠ w) :
    valuation K (log (u : K) - log (w : K) - ((u : K) - w)) < valuation K ((u : K) - w) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hγ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hi1 : 1 ≤ i := by
    by_contra h
    simp_all
  have hu1 := ((mem_unitFiltration_iff_valuation_le hπ).mp hu).2
  have hw1 := ((mem_unitFiltration_iff_valuation_le hπ).mp hw).2
  have huw0 : valuation K ((u : K) - w) ≠ 0 := by
    simpa [sub_eq_zero] using Units.val_injective.ne huw
  -- The difference of the two logarithm series, and its linear term `u - w`.
  set f := fun n : ℕ => (-1) ^ (n + 1) / n * (((u : K) - 1) ^ n - ((w : K) - 1) ^ n)
    with hf_def
  have hf : HasSum f (log (u : K) - log (w : K)) :=
    hasSum_log_sub_log p (unitFiltration_antitone hi1 hu) (unitFiltration_antitone hi1 hw)
  have hf1 : f 1 = (u : K) - w := by
    simp only [hf_def]
    ring
  -- Every other term has valuation less than `v(u - w)`.
  have hlt : ∀ n, valuation K (Function.update f 1 0 n) < valuation K ((u : K) - w) := by
    intro n
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa [zero_lt_iff] using huw0
    rw [Function.update_of_ne hn1]
    rcases eq_or_ne n 0 with rfl | hn0
    · simpa [hf_def, zero_lt_iff] using huw0
    refine lt_of_le_of_lt ?_ (mul_lt_of_lt_one_right (zero_lt_iff.mpr huw0) hγ1)
    simpa only [sub_sub_sub_cancel_right] using
      valuation_logSeries_coeff_mul_pow_sub_pow_le hπ hi hu1 hw1 (by omega : 2 ≤ n)
  -- The modified series sums to `log u - log w - (u - w)`.
  have hsum := valuation_lt_of_hasSum (hf.update 1 0) (Units.mk0 _ huw0) hlt
  rwa [hf1, zero_sub, neg_add_eq_sub] at hsum

/-- The logarithm is an isometry on `U(K,i)` when `(p - 1) * i > e`. -/
theorem valuation_log_sub_log {i : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u w : Kˣ} (hu : u ∈ unitFiltration K i) (hw : w ∈ unitFiltration K i) :
    valuation K (log (u : K) - log (w : K)) = valuation K ((u : K) - w) := by
  rcases eq_or_ne u w with rfl | huw
  · simp
  rw [← sub_add_cancel (log (u : K) - log (w : K)) ((u : K) - w)]
  exact Valuation.map_add_eq_of_lt_right _ (valuation_log_sub_log_sub_sub_lt hi hu hw huw)

/-- On `U(K,i)` with `(p - 1) * i > e`, the logarithm preserves the valuation of `u - 1`; in
particular it maps `U(K,i)` into `𝓂[K] ^ i` (see `exists_mem_maximalIdeal_pow_eq_log`). -/
theorem valuation_log {i : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i) {u : Kˣ}
    (hu : u ∈ unitFiltration K i) :
    valuation K (log (u : K)) = valuation K ((u : K) - 1) := by
  simpa using valuation_log_sub_log hi hu (one_mem _)

/-- On `U(K,i)` with `(p - 1) * i > e`, the logarithm of `u` is an element of `𝓂[K] ^ i`. -/
theorem exists_mem_maximalIdeal_pow_eq_log {i : ℕ}
    (hi : absoluteRamificationIndex K p < (p - 1) * i) {u : Kˣ} (hu : u ∈ unitFiltration K i) :
    ∃ z ∈ 𝓂[K] ^ i, (z : K) = log (u : K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hv : valuation K (log (u : K)) ≤ valuation K (π : K) ^ i := by
    rw [valuation_log hi hu]
    exact ((mem_unitFiltration_iff_valuation_le hπ).mp hu).2
  have hint : log (u : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr
    (hv.trans (pow_le_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ).le))
  refine ⟨⟨_, hint⟩, ?_, rfl⟩
  exact (Set.ext_iff.mp (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) i) _).mpr hv

/-- The logarithm is injective on `U(K,i)` when `(p - 1) * i > e`. -/
theorem log_unitFiltration_injective {i : ℕ}
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    Function.Injective fun u : unitFiltration K i => log ((u : Kˣ) : K) := by
  intro u w huw
  dsimp only at huw
  have h := valuation_log_sub_log hi u.2 w.2
  rw [huw, sub_self, map_zero, eq_comm, (valuation K).zero_iff, sub_eq_zero] at h
  exact Subtype.ext (Units.val_injective h)

end TauCeti
