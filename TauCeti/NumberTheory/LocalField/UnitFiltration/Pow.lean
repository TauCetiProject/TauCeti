/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Powers of deep units

Let `K` be a nonarchimedean local field, let `n` be a natural number with `(n : K) ≠ 0`, and write
`v_K(n)` for its normalized valuation `natCastValuation K n hn`. This file shows that at every
depth `i` with `v_K(p) < (p - 1) * i` for each prime `p ∣ n`, in particular at every depth
`i > v_K(n)`, the `n`-th power map is an isomorphism of the unit filtration step `U(K,i)` onto
`U(K, i + v_K(n))`:

* it maps `U(K,i)` onto `U(K, i + v_K(n))`;
* it is injective on `U(K,i)`, that is, `U(K,i)` contains no nontrivial `n`-th root of unity.

For a prime `p` the depth condition is the usual `v_K(p) < (p - 1) * i`, stated as an integer
inequality so that no division of natural numbers occurs. When `p` is not the residue
characteristic, `v_K(p) = 0` and the condition is just `i ≥ 1`.

The argument is the binomial expansion: for `x ∈ 𝓂[K] ^ i`,

`(1 + x) ^ p = 1 + p x + r`, with `v_K(r) > v_K(p x)`,

because the middle binomial coefficients are divisible by `p` and `v_K(x ^ p) = p v_K(x)` exceeds
`v_K(p x) = v_K(p) + v_K(x)` exactly under the threshold. Hence `(1 + x) ^ p ≡ 1 + p x` modulo
`𝓂[K] ^ (i + v_K(p) + 1)`. This gives the inclusion `U(K,i) ^ p ⊆ U(K, i + v_K(p))` and the
injectivity at once. For the reverse inclusion the congruence shows that every element of
`U(K, j + v_K(p))` is a `p`-th power of an element of `U(K,j)` up to `U(K, j + v_K(p) + 1)`.
Iterating, `U(K, i + v_K(p))` lies in `U(K,i) ^ p · U(K,m)` for every `m`, hence in the
closure of `U(K,i) ^ p`, which is closed as the image of the compact set `U(K,i)`. The general
exponent follows by induction on the prime factorization of `n`.

In mixed characteristic this is the input that computes the `p`-primary part of the power
classes `Kˣ ⧸ (Kˣ)ⁿ` (`TauCeti.card_powerClasses`): it identifies the deep subgroup `U(K,i) ^ n`
of `(Kˣ)ⁿ` with a step of the filtration, which is open in `Kˣ`.

## Main results

* `TauCeti.map_powMonoidHom_unitFiltration_of_prime`: for `v_K(p) < (p - 1) * i`,
  `U(K,i) ^ p = U(K, i + v_K(p))`.
* `TauCeti.disjoint_rootsOfUnity_unitFiltration_of_prime`: for `v_K(p) < (p - 1) * i`, the group
  `U(K,i)` contains no nontrivial `p`-th root of unity.
* `TauCeti.map_powMonoidHom_unitFiltration`: if `v_K(p) < (p - 1) * i` for every prime `p ∣ n`,
  then `U(K,i) ^ n = U(K, i + v_K(n))`.
* `TauCeti.unitFiltration_le_range_powMonoidHom`: under the same depth condition, every unit in
  `U(K, i + v_K(n))` is an `n`-th power.
* `TauCeti.disjoint_rootsOfUnity_unitFiltration`: under the same depth condition, the group
  `U(K,i)` contains no nontrivial `n`-th root of unity.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter XIV, §4, Proposition 9.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The binomial estimate on deep units.** If `v_K(p) < (p - 1) * i` and `x ∈ 𝓂[K] ^ i`, then
`(1 + x) ^ p = 1 + p x + r` with `r` deeper than `p x` by at least one step. -/
private theorem valuation_one_add_pow_sub_sub_le {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {π : 𝒪[K]} (hπ : Irreducible π) {i : ℕ} (hi : natCastValuation K p hpK < (p - 1) * i)
    {x : K} (hx : valuation K x ≤ valuation K (π : K) ^ i) :
    valuation K ((1 + x) ^ p - 1 - p * x) ≤ valuation K (p * x) * valuation K (π : K) := by
  set γ := valuation K (π : K)
  set e := natCastValuation K p hpK
  have hγ1 : γ < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hγ0 : 0 < γ := Valuation.integer.v_irreducible_pos hπ
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hvp : valuation K (p : K) = γ ^ e := valuation_natCast_eq_pow hπ p hpK
  have hxγ : valuation K x ≤ γ :=
    hx.trans (pow_le_of_le_one hγ0.le hγ1.le hi0)
  have hx1 : valuation K x ≤ 1 := hxγ.trans hγ1.le
  -- Expand `(1 + x) ^ p` and discard the terms of degree `0` and `1`.
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hexp : (1 + x) ^ (m + 2) - 1 - ((m + 2 : ℕ) : K) * x =
      ∑ k ∈ Finset.range (m + 1), x ^ (k + 2) * ((m + 2).choose (k + 2) : K) := by
    rw [add_comm (1 : K) x, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, zero_add,
      pow_one, Nat.choose_one_right]
    ring
  rw [hexp]
  refine (valuation K).map_sum_le fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [map_mul, map_pow, map_mul, hvp]
  rcases Nat.lt_or_ge (k + 2) (m + 2) with hkp | hkp
  · -- A middle term: the binomial coefficient is divisible by `p`, and `v(x) ^ 2 ≤ v(x) γ`.
    obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := k + 2) (by omega) hkp
    have hc1 : valuation K (c : K) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).mp (natCast_mem 𝒪[K] c)
    have hchoose : valuation K ((m + 2).choose (k + 2) : K) ≤ γ ^ e := by
      rw [hc, Nat.cast_mul, map_mul, hvp]
      exact mul_le_of_le_one_right' hc1
    calc valuation K x ^ (k + 2) * valuation K ((m + 2).choose (k + 2) : K)
        ≤ valuation K x * γ * γ ^ e := by
          rw [pow_add, pow_two]
          refine mul_le_mul' ?_ hchoose
          calc valuation K x ^ k * (valuation K x * valuation K x)
              ≤ 1 * (valuation K x * γ) :=
                mul_le_mul' (pow_le_one₀ zero_le hx1) (mul_le_mul_right hxγ _)
            _ = valuation K x * γ := one_mul _
      _ = γ ^ e * valuation K x * γ := by ac_rfl
  · -- The top term `x ^ p`: here the threshold `v_K(p) < (p - 1) * i` is used.
    have hk' : k = m := by omega
    subst hk'
    calc valuation K x ^ (k + 2) * valuation K ((k + 2).choose (k + 2) : K)
        = valuation K x * valuation K x ^ (k + 1) := by
          rw [Nat.choose_self, Nat.cast_one, map_one, mul_one, pow_succ']
      _ ≤ valuation K x * (γ ^ i) ^ (k + 1) :=
          mul_le_mul_right (pow_le_pow_left₀ zero_le hx _) _
      _ ≤ valuation K x * γ ^ (e + 1) := by
          rw [← pow_mul]
          refine mul_le_mul_right (pow_le_pow_of_le_one hγ0.le hγ1.le ?_) _
          have : e < (k + 1) * i := by simpa [e] using hi
          nlinarith
      _ = γ ^ e * valuation K x * γ := by rw [pow_succ]; ac_rfl

/-- For `v_K(p) < (p - 1) * i`, the `p`-th power of a unit in `U(K,i)` lies in
`U(K, i + v_K(p))`. -/
private theorem map_powMonoidHom_unitFiltration_le_of_prime {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {i : ℕ} (hi : natCastValuation K p hpK < (p - 1) * i) :
    (unitFiltration K i).map (powMonoidHom p) ≤
      unitFiltration K (i + natCastValuation K p hpK) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set γ := valuation K (π : K)
  set e := natCastValuation K p hpK
  have hγ1 : γ < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, mem_unitFiltration_iff_valuation_sub_one_le hi0 hπ] at hu
  rw [powMonoidHom_apply, mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ]
  have hr := valuation_one_add_pow_sub_sub_le hp hpK hπ hi hu
  have hpx : valuation K (p * ((u : K) - 1)) ≤ γ ^ (i + e) := by
    rw [map_mul, valuation_natCast_eq_pow hπ p hpK, pow_add, mul_comm]
    exact mul_le_mul_left hu _
  have hsplit : ((u ^ p : Kˣ) : K) - 1 =
      p * ((u : K) - 1) + ((1 + ((u : K) - 1)) ^ p - 1 - p * ((u : K) - 1)) := by
    push_cast
    ring
  rw [hsplit]
  exact (valuation K).map_add_le hpx
    (hr.trans ((mul_le_of_le_one_right' hγ1.le).trans hpx))

/-- For `v_K(p) < (p - 1) * j`, every unit in `U(K, j + v_K(p))` is the `p`-th power of a unit
in `U(K,j)` up to a unit one step deeper. -/
private theorem unitFiltration_le_map_powMonoidHom_sup_of_prime {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {j : ℕ} (hj : natCastValuation K p hpK < (p - 1) * j) :
    unitFiltration K (j + natCastValuation K p hpK) ≤
      (unitFiltration K j).map (powMonoidHom p) ⊔
        unitFiltration K (j + natCastValuation K p hpK + 1) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set γ := valuation K (π : K)
  set e := natCastValuation K p hpK
  have hγ1 : γ < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hγ0 : 0 < γ := Valuation.integer.v_irreducible_pos hπ
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hj
  have hvp : valuation K (p : K) = γ ^ e := valuation_natCast_eq_pow hπ p hpK
  have hvp0 : 0 < valuation K (p : K) := by
    rw [hvp]
    exact pow_pos hγ0 e
  intro w hw
  rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ] at hw
  -- The candidate root is `u = 1 + x` with `x = (w - 1) / p`.
  set x : K := ((w : K) - 1) / p with hx_def
  have hx : valuation K x ≤ γ ^ j := by
    rw [hx_def, map_div₀, div_le_iff₀ hvp0, hvp, ← pow_add]
    exact hw
  have hxγ : valuation K x < 1 :=
    hx.trans_lt (pow_lt_one₀ hγ0.le hγ1 hj0)
  have hu1 : valuation K (1 + x) = 1 := (valuation K).map_one_add_of_lt hxγ
  have hu0 : (1 + x : K) ≠ 0 := by
    intro h
    simp [h] at hu1
  set u : Kˣ := Units.mk0 (1 + x) hu0
  have hu : u ∈ unitFiltration K j := by
    rw [mem_unitFiltration_iff_valuation_sub_one_le hj0 hπ]
    simpa [u] using hx
  have hr := valuation_one_add_pow_sub_sub_le hp hpK hπ hj hx
  have hpx : (p : K) * x = (w : K) - 1 := by
    rw [hx_def]
    field_simp
  refine Subgroup.mem_sup.mpr ⟨u ^ p, ⟨u, hu, rfl⟩, (u ^ p)⁻¹ * w, ?_, by group⟩
  rw [mem_unitFiltration_iff_valuation_sub_one_le (by omega) hπ]
  -- `(u ^ p)⁻¹ w - 1 = (w - u ^ p) / u ^ p`, and `u ^ p` has valuation one.
  have hup : valuation K ((u : K) ^ p) = 1 := by
    rw [map_pow]
    simp [u, hu1]
  have hdiff : (((u ^ p)⁻¹ * w : Kˣ) : K) - 1 =
      -((1 + x) ^ p - 1 - p * x) * ((u : K) ^ p)⁻¹ := by
    have hw' : (w : K) = p * x + 1 := by rw [hpx]; ring
    have h0 : (1 + x) ^ p ≠ 0 := pow_ne_zero _ hu0
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, u,
      Units.val_mk0, hw']
    field_simp
    ring
  rw [hdiff, map_mul, map_inv₀, hup, inv_one, mul_one, Valuation.map_neg, pow_succ]
  refine hr.trans (mul_le_mul_left ?_ _)
  rw [hpx]
  exact hw

/-- **Deep units are `p`-th powers.** For a prime `p` with `(p : K) ≠ 0` and a depth `i` with
`v_K(p) < (p - 1) * i`, the `p`-th power map carries `U(K,i)` onto `U(K, i + v_K(p))`. -/
theorem map_powMonoidHom_unitFiltration_of_prime {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {i : ℕ} (hi : natCastValuation K p hpK < (p - 1) * i) :
    (unitFiltration K i).map (powMonoidHom p) =
      unitFiltration K (i + natCastValuation K p hpK) := by
  set e := natCastValuation K p hpK
  set P := (unitFiltration K i).map (powMonoidHom p)
  refine le_antisymm (map_powMonoidHom_unitFiltration_le_of_prime hp hpK hi) ?_
  -- Iterating the one-step approximation, `U(K, i + e)` lies in `P · U(K, i + e + k)` for all `k`.
  have hchain : ∀ k, unitFiltration K (i + e) ≤ P ⊔ unitFiltration K (i + e + k) := by
    intro k
    induction k with
    | zero => exact le_sup_right
    | succ k ih =>
      have hstep := unitFiltration_le_map_powMonoidHom_sup_of_prime hp hpK (j := i + k)
        (hi.trans_le (Nat.mul_le_mul_left _ (Nat.le_add_right i k)))
      have hmono : (unitFiltration K (i + k)).map (powMonoidHom p) ≤ P :=
        Subgroup.map_mono (unitFiltration_antitone (Nat.le_add_right i k))
      calc unitFiltration K (i + e)
          ≤ P ⊔ unitFiltration K (i + e + k) := ih
        _ ≤ P ⊔ (P ⊔ unitFiltration K (i + e + (k + 1))) := by
          refine sup_le_sup_left ?_ _
          -- `hstep` is stated at depth `i + k + e`; reorder it to the depths `i + e + k` of `ih`.
          rw [Nat.add_right_comm i k e] at hstep
          rw [← add_assoc (i + e) k 1]
          exact hstep.trans (sup_le_sup_right hmono _)
        _ = P ⊔ unitFiltration K (i + e + (k + 1)) := by rw [← sup_assoc, sup_idem]
  -- Hence `U(K, i + e)` lies in `P · U(K,m)` for every `m`, so in the closure of `P`, which is `P`
  -- because `P` is the image of the compact set `U(K,i)` in the Hausdorff group `Kˣ`.
  have hP : IsClosed (P : Set Kˣ) := by
    simpa [P, Subgroup.coe_map] using
      ((isCompact_unitFiltration i).image (continuous_pow p)).isClosed
  intro w hw
  rw [← SetLike.mem_coe, ← hP.closure_eq,
    ← hasBasis_nhds_one_unitFiltration.iInter_mul_right_eq_closure, Set.mem_iInter₂]
  intro m _
  rw [← Subgroup.mul_normal]
  exact sup_le_sup_left (unitFiltration_antitone (Nat.le_add_left m (i + e))) _ (hchain m hw)

/-- **Deep units carry no `p`-torsion.** For a prime `p` with `(p : K) ≠ 0` and a depth `i` with
`v_K(p) < (p - 1) * i`, the only `p`-th root of unity in `U(K,i)` is `1`. -/
theorem disjoint_rootsOfUnity_unitFiltration_of_prime {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {i : ℕ} (hi : natCastValuation K p hpK < (p - 1) * i) :
    Disjoint (rootsOfUnity p K) (unitFiltration K i) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hγ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  refine Subgroup.disjoint_def.mpr fun {u} hup hu ↦ ?_
  rw [mem_unitFiltration_iff_valuation_sub_one_le hi0 hπ] at hu
  have hr := valuation_one_add_pow_sub_sub_le hp hpK hπ hi hu
  have hpow : (u : K) ^ p = 1 := by
    simpa using congrArg Units.val ((mem_rootsOfUnity p u).mp hup)
  -- Since `(1 + x) ^ p = 1`, the remainder is `-(p x)`, which cannot be deeper than itself.
  have hrem : (1 + ((u : K) - 1)) ^ p - 1 - p * ((u : K) - 1) = -(p * ((u : K) - 1)) := by
    rw [add_sub_cancel, hpow]
    ring
  rw [hrem, Valuation.map_neg] at hr
  have h0 : valuation K (p * ((u : K) - 1)) = 0 := by
    by_contra h
    exact (mul_lt_of_lt_one_right (zero_lt_iff.mpr h) hγ1).not_ge hr
  rw [Valuation.zero_iff, mul_eq_zero, sub_eq_zero] at h0
  exact Units.ext (h0.resolve_left hpK)

/-- **Deep units are `n`-th powers.** For `(n : K) ≠ 0` and a depth `i` with
`v_K(p) < (p - 1) * i` for every prime `p ∣ n`, the `n`-th power map carries `U(K,i)` onto
`U(K, i + v_K(n))`. The depth condition holds in particular for every `i > v_K(n)`, by
`natCastValuation_lt_sub_one_mul_of_lt_of_dvd`. -/
theorem map_powMonoidHom_unitFiltration {n : ℕ} (hn : (n : K) ≠ 0) {i : ℕ}
    (hi : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ n →
      natCastValuation K p hpK < (p - 1) * i) :
    (unitFiltration K i).map (powMonoidHom n) = unitFiltration K (i + natCastValuation K n hn) := by
  induction n using Nat.recOnMul generalizing i with
  | zero => simp at hn
  | one =>
    rw [natCastValuation_one, add_zero]
    ext x
    simp
  | prime p hp => exact map_powMonoidHom_unitFiltration_of_prime hp hn (hi p hp hn dvd_rfl)
  | mul a b iha ihb =>
    have ha : (a : K) ≠ 0 := left_ne_zero_of_mul (by simpa using hn)
    have hb : (b : K) ≠ 0 := right_ne_zero_of_mul (by simpa using hn)
    rw [natCastValuation_mul K ha hb]
    have hcomp : (powMonoidHom (a * b) : Kˣ →* Kˣ) = (powMonoidHom b).comp (powMonoidHom a) := by
      ext
      simp [pow_mul]
    -- The depth condition passes to `a` at depth `i` and to `b` at the deeper depth `i + v_K(a)`.
    rw [hcomp, ← Subgroup.map_map,
      iha ha fun p hp hpK hpa ↦ hi p hp hpK (hpa.mul_right b),
      ihb hb fun p hp hpK hpb ↦ (hi p hp hpK (hpb.mul_left a)).trans_le
        (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)), add_assoc]

/-- Under the depth condition of `map_powMonoidHom_unitFiltration`, every unit in
`U(K, i + v_K(n))` is an `n`-th power in `Kˣ`. -/
theorem unitFiltration_le_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) {i : ℕ}
    (hi : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ n →
      natCastValuation K p hpK < (p - 1) * i) :
    unitFiltration K (i + natCastValuation K n hn) ≤ (powMonoidHom n : Kˣ →* Kˣ).range :=
  (map_powMonoidHom_unitFiltration hn hi).symm.le.trans (Subgroup.map_le_range _ _)

/-- **Deep units carry no `n`-torsion.** For `(n : K) ≠ 0` and a depth `i` with
`v_K(p) < (p - 1) * i` for every prime `p ∣ n`, the only `n`-th root of unity in `U(K,i)` is `1`.
The depth condition holds in particular for every `i > v_K(n)`, by
`natCastValuation_lt_sub_one_mul_of_lt_of_dvd`. -/
theorem disjoint_rootsOfUnity_unitFiltration {n : ℕ} (hn : (n : K) ≠ 0) {i : ℕ}
    (hi : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ n →
      natCastValuation K p hpK < (p - 1) * i) :
    Disjoint (rootsOfUnity n K) (unitFiltration K i) := by
  induction n using Nat.recOnMul generalizing i with
  | zero => simp at hn
  | one => simp
  | prime p hp => exact disjoint_rootsOfUnity_unitFiltration_of_prime hp hn (hi p hp hn dvd_rfl)
  | mul a b iha ihb =>
    have ha : (a : K) ≠ 0 := left_ne_zero_of_mul (by simpa using hn)
    have hb : (b : K) ≠ 0 := right_ne_zero_of_mul (by simpa using hn)
    have hia : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ a →
        natCastValuation K p hpK < (p - 1) * i :=
      fun p hp hpK hpa ↦ hi p hp hpK (hpa.mul_right b)
    refine Subgroup.disjoint_def.mpr fun {u} hu hui ↦ ?_
    -- `u ^ a` is a `b`-th root of unity in `U(K, i + v_K(a))`, hence trivial.
    have hua : u ^ a ∈ unitFiltration K (i + natCastValuation K a ha) :=
      (map_powMonoidHom_unitFiltration ha hia).le ⟨u, hui, rfl⟩
    have hub : u ^ a ∈ rootsOfUnity b K := by
      rw [mem_rootsOfUnity, ← pow_mul]
      exact (mem_rootsOfUnity _ u).mp hu
    have h1 : u ^ a = 1 := Subgroup.disjoint_def.mp (ihb hb fun p hp hpK hpb ↦
      (hi p hp hpK (hpb.mul_left a)).trans_le (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))
      hub hua
    exact Subgroup.disjoint_def.mp (iha ha hia) ((mem_rootsOfUnity a u).mpr h1) hui

end TauCeti
