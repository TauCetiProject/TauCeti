/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Kummer
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
import Mathlib.FieldTheory.Perfect
import TauCeti.RingTheory.HahnSeries.Inverse
import TauCeti.RingTheory.HahnSeries.Multiplication
import TauCeti.RingTheory.LaurentSeries.IntegrallyClosed
import TauCeti.RingTheory.PowerSeries.Hensel
import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed

/-!
# Substitutions and formal coordinate changes of the Puiseux field

Let `K` be a field and `φ ∈ K⟦X⟧` a nonzero power series with zero constant coefficient, inducing
the Laurent-series substitution `f ↦ f (φ)` (`TauCeti.LaurentSeries.substAlgHom`). This file
studies `K`-algebra endomorphisms `ρ` of the Puiseux field `puiseuxField K` that extend
`f ↦ f (φ)` on `K⸨X⸩`.

Since `K` is integrally closed in each ramified level `K⸨t ^ (1 / n)⸩`
(`TauCeti.LaurentSeries.isIntegrallyClosedIn`), `K` is integrally closed in `puiseuxField K`; in
particular, all roots of unity in `puiseuxField K` lie in `K` (via `TauCeti.rootsOfUnityMulEquiv`),
and any two Puiseux series with equal `n`-th powers and equal leading coefficients are equal.

Over any field `K` of any characteristic, every algebraic lift `ρ` of `f ↦ f (φ)` is rigidly
controlled on each ramified level `K⸨t ^ (1 / n)⸩`: the image `ρ (t ^ (1 / n))` is an `n`-th root
of `φ` in `puiseuxField K`, and any `n`-th root of a level-`m` non-unit power series automatically
lies in level `m * n` as a power series `ψ ∈ X K⟦X⟧` of the same order. In positive characteristic
`p`, factors of `p` in `n` are peeled off using the Frobenius expansion formula
`PowerSeries.map_frobenius_expand`; the remaining factor invertible in `K` is handled by Hensel's
lemma for `n`-th roots of units (`PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow`) together with
integral closure of `K` in `puiseuxField K`. Since each level has power basis
`1, t ^ (1 / n), ..., t ^ ((n - 1) / n)` over `K⸨X⸩`, `ρ` restricts on level `n` to
`LaurentSeries.substAlgHom` for `ψ`.

This levelwise formula has four immediate consequences, all valid over an arbitrary field `K`:

* **Valuation scaling**: `ord (ρ x) = ord φ * ord x` and `v (ρ x) = v x ^ ord φ`.
* **Automatic continuity**: every algebraic lift `ρ` is a topological embedding for the valuation
  topology, and in particular continuous (`puiseuxField K →A[K] puiseuxField K`).
* **Formal coordinates**: if `φ` is a formal coordinate (order one), then on every level `n` the
  restricted series `ψ` is again a formal coordinate, so `ρ` is automatically bijective and
  valuation-preserving, and upgrades to a bicontinuous automorphism
  `puiseuxField K ≃A[K] puiseuxField K`.
* **Uniqueness up to the Kummer action**: any two `K`-algebra endomorphisms of `puiseuxField K`
  agreeing on `K⸨X⸩` differ by precomposition with a unique Kummer automorphism `kummer K ζ`,
  `ζ ∈ lim_n μₙ(K)`.

Finally, when `K` is algebraically closed (of any characteristic), compatible `n`-th roots of the
leading coefficient of `φ` and the unique leading-coefficient-one `n`-th roots of its normalized
unit part assemble into a compatible family of levelwise substitutions, proving that every
Laurent substitution lifts to a continuous endomorphism of `puiseuxField K` and every formal
coordinate lifts to a bicontinuous automorphism.

## Main definitions

* `TauCeti.puiseuxField.continuousAlgHomOfSubstAlgHom`: upgrades an algebraic lift of
  `LaurentSeries.substAlgHom` to a continuous `K`-algebra endomorphism.
* `TauCeti.puiseuxField.continuousAlgEquivOfSubstAlgEquiv`: upgrades an algebraic lift of
  `LaurentSeries.substAlgEquiv` to a bicontinuous `K`-algebra automorphism.

## Main results

* `TauCeti.puiseuxField.isIntegrallyClosedIn`: `K` is integrally closed in `puiseuxField K`, over
  any field `K`.
* `TauCeti.puiseuxField.exists_eq_levelEmbedding_of_pow_eq_levelEmbedding`: an `n`-th root in
  `puiseuxField K` of a level-`m` series `φ ∈ X K⟦X⟧` lies in level `m * n` as a series in
  `X K⟦X⟧` of the same order.
* `TauCeti.puiseuxField.exists_levelEmbedding_eq_substAlgHom`: every algebraic lift of
  `LaurentSeries.substAlgHom hφ hφ₀` acts on level `n` as Laurent substitution by an order-`ord φ`
  power series.
* `TauCeti.puiseuxField.addVal_apply_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.valuation_apply_of_apply_algebraMap_substAlgHom`: order and valuation
  scaling for lifts of Laurent substitutions.
* `TauCeti.puiseuxField.isEmbedding_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.continuous_of_apply_algebraMap_substAlgHom`: automatic continuity of
  algebraic lifts.
* `TauCeti.puiseuxField.existsUnique_kummer_comp_eq_of_apply_algebraMap_eq`: lifts agreeing on
  `K⸨X⸩` differ by a unique Kummer automorphism.
* `TauCeti.puiseuxField.exists_levelEmbedding_eq_substAlgEquiv`,
  `TauCeti.puiseuxField.bijective_of_apply_algebraMap_substAlgEquiv`: lifts of formal coordinates
  act by formal coordinates on every level and are automatically bijective.
* `TauCeti.puiseuxField.exists_continuousAlgHom_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv`: existence of
  continuous lifts over algebraically closed fields of any characteristic.
-/

public section

open Filter HahnSeries LaurentSeries PowerSeries Topology WithZero
open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

section Roots

/-- A field `K` is integrally closed in `puiseuxField K`: the Puiseux series algebraic over `K`
are the constants. -/
instance isIntegrallyClosedIn (K : Type*) [Field K] : IsIntegrallyClosedIn K (puiseuxField K) := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K (puiseuxField K)).injective, fun {x} hx ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    ((isIntegral_algHom_iff (levelEmbedding K n) (levelEmbedding K n).injective).mp hx)
  exact ⟨c, (AlgHom.commutes (levelEmbedding K n) c).symm⟩

variable {K : Type*} [Field K]

/-- Two Puiseux series with equal `n`-th powers and equal leading coefficients are equal. -/
private theorem eq_of_pow_eq_of_leadingCoeff_eq {n : ℕ+} {x y : puiseuxField K}
    (hpow : x ^ (n : ℕ) = y ^ (n : ℕ))
    (hlead : (x : HahnSeries ℚ K).leadingCoeff = (y : HahnSeries ℚ K).leadingCoeff) :
    x = y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa [n.ne_zero] using hpow
  have hqpow : (x / y) ^ (n : ℕ) = 1 := by
    rw [div_pow, hpow, div_self (pow_ne_zero _ hy0)]
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := K) (A := puiseuxField K) n.pos (hqpow ▸ isIntegral_one)
  have hylead : (y : HahnSeries ℚ K).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Subtype.coe_ne_coe.mpr hy0)
  have hc1 : c = 1 := by
    have hqlead : ((x / y : puiseuxField K) : HahnSeries ℚ K).leadingCoeff = 1 := by
      rw [IntermediateField.coe_div, leadingCoeff_div, hlead, div_self hylead]
    have hcoe : (algebraMap K (puiseuxField K) c : HahnSeries ℚ K) = HahnSeries.single 0 c := by
      simp [HahnSeries.algebraMap_apply', HahnSeries.C_apply]
    rwa [← hc, hcoe, leadingCoeff_of_single] at hqlead
  rw [hc1, map_one] at hc
  exact (div_eq_one_iff_eq hy0).mp hc.symm

/-- When `(n : K) = 0`, the characteristic `p = ringChar K` is prime and divides `n`, giving a
strictly smaller positive factor `n'` with `p * n' = n`. -/
private theorem exists_prime_char_mul_lt {n : ℕ+} (hn : ((n : ℕ) : K) = 0) :
    ∃ p n' : ℕ+, CharP K p ∧ (p : ℕ).Prime ∧ p * n' = n ∧ n' < n := by
  have hchar0 : ringChar K ≠ 0 := by
    intro h0
    have : CharP K 0 := h0 ▸ ringChar.charP K
    have : CharZero K := CharP.charP_to_charZero K
    exact (Nat.cast_ne_zero.mpr n.ne_zero) hn
  have hp : (ringChar K).Prime :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar0
  have hdvd : ringChar K ∣ (n : ℕ) := (ringChar.spec K n).mp hn
  let p : ℕ+ := ⟨ringChar K, hp.pos⟩
  let n' : ℕ+ := ⟨(n : ℕ) / p, Nat.div_pos (Nat.le_of_dvd n.pos hdvd) hp.pos⟩
  exact ⟨p, n', ringChar.charP K, hp, PNat.eq (Nat.mul_div_cancel' hdvd),
    Nat.div_lt_self n.pos hp.one_lt⟩

/-- The level-`n` embedding preserves the leading coefficient of a Laurent series. -/
private theorem leadingCoeff_ramifiedEmbedding (n : ℕ+) (f : K⸨X⸩) :
    (ramifiedEmbedding K n f).leadingCoeff = f.leadingCoeff := by
  rw [leadingCoeff_eq, leadingCoeff_eq, order_ramifiedEmbedding,
    coeff_ramifiedEmbedding_intCast_div]

/-- In characteristic `p`, the `(p * j)`-th coefficient of `g ^ p` is `(g.coeff j) ^ p`. -/
private theorem coeff_pow_char_mul {p : ℕ} [CharP K p] (hp : p.Prime) (g : K⸨X⸩) (j : ℤ) :
    (g ^ p).coeff ((p : ℤ) * j) = g.coeff j ^ p := by
  rcases eq_or_ne g 0 with rfl | _
  · simp [zero_pow hp.ne_zero]
  have : ExpChar K p := .prime hp
  have hpow : g ^ p = HahnSeries.single ((p : ℤ) * g.order) 1 *
      ((((_root_.LaurentSeries.powerSeriesPart g).expand p hp.ne_zero).map
        (frobenius K p) : K⟦X⟧) : K⸨X⸩) := by
    conv_lhs => rw [← _root_.LaurentSeries.single_order_mul_powerSeriesPart g]
    rw [mul_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul,
      ← map_pow (ofPowerSeries ℤ K), PowerSeries.map_frobenius_expand]
  rw [hpow, coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  by_cases hj : j < g.order
  · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hlt : (p : ℤ) * j - (p : ℤ) * g.order < 0 := by nlinarith
    simp only [hlt, ↓reduceIte, coeff_eq_zero_of_lt_order hj, zero_pow hp.ne_zero]
  · have : g.order ≤ j := not_lt.mp hj
    have : (0 : ℤ) ≤ p := by exact_mod_cast hp.pos.le
    have hnotlt : ¬((p : ℤ) * j - (p : ℤ) * g.order < 0) := not_lt.mpr (by nlinarith)
    simp only [hnotlt, ↓reduceIte]
    have habs : ((p : ℤ) * j - (p : ℤ) * g.order).natAbs = p * (j - g.order).natAbs := by
      rw [← mul_sub, Int.natAbs_mul, Int.natAbs_natCast]
    rw [habs, PowerSeries.coeff_map, PowerSeries.coeff_expand_mul, frobenius_def]
    congr 1
    conv_rhs => rw [← _root_.LaurentSeries.single_order_mul_powerSeriesPart g]
    have hnotlt' : ¬(j - g.order < 0) := by omega
    simp only [coeff_single_mul, one_mul, PowerSeries.coeff_coe, hnotlt', ↓reduceIte]

/-- When `(n : K) ≠ 0`, an `n`-th root in `puiseuxField K` of a level-`m` series `φ ∈ X K⟦X⟧`
lies in level `m * n` as a series in `X K⟦X⟧` of the same order. -/
private theorem exists_eq_levelEmbedding_of_pow_eq_levelEmbedding_of_ne_zero (m n : ℕ+)
    (hn : ((n : ℕ) : K) ≠ 0) {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {α : puiseuxField K} (hα : α ^ (n : ℕ) = levelEmbedding K m (φ : K⸨X⸩)) :
    ∃ ψ : K⟦X⟧, PowerSeries.constantCoeff ψ = 0 ∧ ψ ≠ 0 ∧ ψ.order = φ.order ∧
      levelEmbedding K (m * n) (ψ : K⸨X⸩) = α := by
  have hφcoe0 : (φ : K⸨X⸩) ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr hφ₀
  set e : ℕ := φ.order.toNat
  have he : e ≠ 0 := PowerSeries.toNat_order_ne_zero hφ hφ₀
  set u : K⟦X⟧ := _root_.LaurentSeries.powerSeriesPart (φ : K⸨X⸩)
  have hφeq : φ = PowerSeries.X ^ e * u := ofPowerSeries_injective <| by
    rw [map_mul (ofPowerSeries ℤ K), map_pow (ofPowerSeries ℤ K), PowerSeries.coe_X,
      HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one, ← PowerSeries.order_coe,
      _root_.LaurentSeries.single_order_mul_powerSeriesPart]
  set c : K := (α : HahnSeries ℚ K).leadingCoeff
  have hc_pow : c ^ (n : ℕ) = PowerSeries.constantCoeff u := by
    rw [← TauCeti.hahnSeries_leadingCoeff_pow, ← SubmonoidClass.coe_pow, hα, coe_levelEmbedding,
      leadingCoeff_ramifiedEmbedding, ← PowerSeries.coeff_zero_eq_constantCoeff,
      _root_.LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero, leadingCoeff_eq]
  have hc0 : c ≠ 0 := fun h ↦ by
    rw [h, zero_pow n.ne_zero] at hc_pow
    exact (PowerSeries.isUnit_iff_constantCoeff.mp
      (TauCeti.LaurentSeries.isUnit_powerSeriesPart hφcoe0)).ne_zero hc_pow.symm
  obtain ⟨v, hv, hvc⟩ := PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow hn hc0 hc_pow.symm
  set ψ : K⟦X⟧ := PowerSeries.X ^ e * PowerSeries.expand (n : ℕ) n.ne_zero v
  have hψv_unit : IsUnit (PowerSeries.expand (n : ℕ) n.ne_zero v) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_expand, hvc]
    exact hc0.isUnit
  have hψord : ψ.order = φ.order := by
    rw [PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_isUnit hψv_unit, add_zero, PowerSeries.coe_toNat_order hφ₀]
  have hψ0 : ψ ≠ 0 := fun h ↦ hφ₀ (PowerSeries.order_eq_top.mp (by rw [← hψord, h]; simp))
  have hψpow : ψ ^ (n : ℕ) = PowerSeries.expand (n : ℕ) n.ne_zero φ := by
    rw [mul_pow, ← pow_mul, mul_comm e n, pow_mul, ← map_pow, hv, hφeq, map_mul, map_pow,
      PowerSeries.expand_X]
  set β : puiseuxField K := levelEmbedding K (m * n) (ψ : K⸨X⸩)
  have hβpow : β ^ (n : ℕ) = α ^ (n : ℕ) := by
    rw [← map_pow, ← map_pow (ofPowerSeries ℤ K), hψpow, ← expand_coe,
      levelEmbedding_expand, hα]
  have hβlead : (β : HahnSeries ℚ K).leadingCoeff = c := by
    rw [coe_levelEmbedding, leadingCoeff_ramifiedEmbedding, leadingCoeff_eq, PowerSeries.order_coe,
      hψord, PowerSeries.coeff_coe]
    have hnotlt : ¬((φ.order.toNat : ℤ) < 0) := by omega
    simp only [hnotlt, ↓reduceIte, Int.natAbs_natCast, ψ, e]
    simpa only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.constantCoeff_expand, hvc] using
      PowerSeries.coeff_X_pow_mul (PowerSeries.expand (n : ℕ) n.ne_zero v) φ.order.toNat 0
  exact ⟨ψ, by simp [ψ, he], hψ0, hψord, eq_of_pow_eq_of_leadingCoeff_eq hβpow hβlead⟩

/-- In characteristic `p`, any `p`-th root in `puiseuxField K` of a level-`m` series lies in
level `m * p`. -/
private theorem mem_range_levelEmbedding_of_pow_char_eq_levelEmbedding (m p : ℕ+)
    [CharP K p] (hp : (p : ℕ).Prime) {f : K⸨X⸩} {γ : puiseuxField K}
    (hγ : γ ^ (p : ℕ) = levelEmbedding K m f) :
    γ ∈ (levelEmbedding K (m * p)).range := by
  obtain ⟨k, hk⟩ := exists_mem_range_levelEmbedding γ
  obtain ⟨g, hg⟩ := (AlgHom.mem_range _).mp hk
  have hmul_mem {q : ℚ} (hq : q ∈ (γ : HahnSeries ℚ K).support) :
      ((p : ℕ) : ℚ) * q ∈ (ramifiedEmbedding K m f).support := by
    rw [mem_support, ← coe_levelEmbedding, ← hγ, SubmonoidClass.coe_pow, ← hg,
      ← SubmonoidClass.coe_pow, ← map_pow, coe_levelEmbedding]
    rw [mem_support, ← hg, coe_levelEmbedding] at hq
    have hqden : q.den ∣ k :=
      (mem_range_ramifiedEmbedding_iff k).mp ⟨g, rfl⟩ q ((mem_support _ _).mpr hq)
    obtain ⟨j, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div k.ne_zero).mp hqden
    rw [coeff_ramifiedEmbedding_intCast_div] at hq
    have heq : ((p : ℕ) : ℚ) * ((j : ℚ) / k) = (((p : ℤ) * j : ℤ) : ℚ) / k := by
      push_cast; ring
    rw [heq, coeff_ramifiedEmbedding_intCast_div, coeff_pow_char_mul hp]
    exact pow_ne_zero _ hq
  rw [mem_range_levelEmbedding_iff, mem_range_ramifiedEmbedding_iff]
  intro q hq
  have hmem := hmul_mem hq
  rw [support_ramifiedEmbedding] at hmem
  obtain ⟨r, -, hr⟩ := hmem
  refine (Rat.den_dvd_iff_exists_eq_intCast_div (m * p).ne_zero).mpr ⟨r, ?_⟩
  have hpq : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast p.ne_zero
  push_cast
  field_simp [hpq] at hr ⊢
  linarith

/-- In characteristic `p`, a `p`-th root in `puiseuxField K` of a level-`m` series `φ ∈ X K⟦X⟧`
lies in level `m * p` as a series in `X K⟦X⟧` of the same order. -/
private theorem exists_eq_levelEmbedding_of_pow_char_eq_levelEmbedding (m p : ℕ+)
    [CharP K p] (hp : (p : ℕ).Prime) {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0)
    (hφ₀ : φ ≠ 0) {γ : puiseuxField K}
    (hγ : γ ^ (p : ℕ) = levelEmbedding K m (φ : K⸨X⸩)) :
    ∃ ψ : K⟦X⟧, PowerSeries.constantCoeff ψ = 0 ∧ ψ ≠ 0 ∧ ψ.order = φ.order ∧
      levelEmbedding K (m * p) (ψ : K⸨X⸩) = γ := by
  have hφcoe0 : (φ : K⸨X⸩) ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr hφ₀
  obtain ⟨g', hg'⟩ := (AlgHom.mem_range _).mp
    (mem_range_levelEmbedding_of_pow_char_eq_levelEmbedding m p hp hγ)
  have hg'0 : g' ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hg'
    rw [← hg', zero_pow p.ne_zero] at hγ
    exact hφcoe0 ((levelEmbedding K m).injective (by simp [← hγ]))
  have hg'ord : g'.order = (φ.order.toNat : ℤ) := by
    have hord := congrArg (addVal K) hγ
    rw [AddValuation.map_pow, ← hg', addVal_levelEmbedding, addVal_levelEmbedding,
      ← order_eq_orderTop_of_ne_zero hg'0, ← order_eq_orderTop_of_ne_zero hφcoe0,
      WithTop.map_coe, WithTop.map_coe, ← WithTop.coe_nsmul, WithTop.coe_eq_coe,
      nsmul_eq_mul, PowerSeries.order_coe] at hord
    have hmq : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hpq : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast p.ne_zero
    have hq : (g'.order : ℚ) = (φ.order.toNat : ℚ) := by
      push_cast at hord ⊢
      field_simp [hmq, hpq] at hord ⊢
      linarith
    exact_mod_cast hq
  set e : ℕ := φ.order.toNat
  have he : e ≠ 0 := PowerSeries.toNat_order_ne_zero hφ hφ₀
  set ψ : K⟦X⟧ := PowerSeries.X ^ e * _root_.LaurentSeries.powerSeriesPart g'
  have hψcoe : (ψ : K⸨X⸩) = g' := by
    rw [map_mul (ofPowerSeries ℤ K), map_pow (ofPowerSeries ℤ K), PowerSeries.coe_X,
      HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one, ← hg'ord,
      _root_.LaurentSeries.single_order_mul_powerSeriesPart]
  have hψord : ψ.order = φ.order := by
    rw [PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_isUnit (TauCeti.LaurentSeries.isUnit_powerSeriesPart hg'0),
      add_zero, PowerSeries.coe_toNat_order hφ₀]
  have hψ0 : ψ ≠ 0 := fun h ↦ by rw [h, map_zero] at hψcoe; exact hg'0 hψcoe.symm
  exact ⟨ψ, by simp [ψ, he], hψ0, hψord, by rw [hψcoe, hg']⟩

/-- **Levelwise power-series roots in the Puiseux field.** Over any field `K` of any
characteristic, an `n`-th root `α ∈ puiseuxField K` of the level-`m` image of a nonzero power
series `φ ∈ X K⟦X⟧` automatically lies in level `m * n` as the image of a power series `ψ ∈ X K⟦X⟧`
of the same order as `φ`. -/
theorem exists_eq_levelEmbedding_of_pow_eq_levelEmbedding (m n : ℕ+) {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {α : puiseuxField K}
    (hα : α ^ (n : ℕ) = levelEmbedding K m (φ : K⸨X⸩)) :
    ∃ ψ : K⟦X⟧, PowerSeries.constantCoeff ψ = 0 ∧ ψ ≠ 0 ∧ ψ.order = φ.order ∧
      levelEmbedding K (m * n) (ψ : K⸨X⸩) = α := by
  refine PNat.strongInductionOn (p := fun n ↦ ∀ (m : ℕ+) {φ : K⟦X⟧},
    PowerSeries.constantCoeff φ = 0 → φ ≠ 0 →
      α ^ (n : ℕ) = levelEmbedding K m (φ : K⸨X⸩) →
      ∃ ψ : K⟦X⟧, PowerSeries.constantCoeff ψ = 0 ∧ ψ ≠ 0 ∧ ψ.order = φ.order ∧
        levelEmbedding K (m * n) (ψ : K⸨X⸩) = α) n ?_ m hφ hφ₀ hα
  intro n ih m φ hφ hφ₀ hα
  by_cases hn : ((n : ℕ) : K) = 0
  · obtain ⟨p, n', _, hp, hpn', hlt⟩ := exists_prime_char_mul_lt hn
    have hγ : (α ^ (n' : ℕ)) ^ (p : ℕ) = levelEmbedding K m (φ : K⸨X⸩) := by
      rw [← pow_mul, mul_comm, ← PNat.mul_coe, hpn', hα]
    obtain ⟨φ₁, hφ₁, hφ₁₀, hφ₁ord, hφ₁eq⟩ :=
      exists_eq_levelEmbedding_of_pow_char_eq_levelEmbedding m p hp hφ hφ₀ hγ
    obtain ⟨ψ, hψ, hψ₀, hψord, hψeq⟩ := ih n' hlt (m * p) hφ₁ hφ₁₀ hφ₁eq.symm
    exact ⟨ψ, hψ, hψ₀, hψord.trans hφ₁ord, by rwa [mul_assoc, hpn'] at hψeq⟩
  · exact exists_eq_levelEmbedding_of_pow_eq_levelEmbedding_of_ne_zero m n hn hφ hφ₀ hα

end Roots

section SubstAlgHom

variable {K : Type*} [Field K]

/-- Two `LaurentSeries.substAlgHom` maps with equal target power series are equal. -/
private theorem substAlgHom_congr {φ₁ φ₂ : K⟦X⟧} (h : φ₁ = φ₂)
    (h₁ : PowerSeries.constantCoeff φ₁ = 0) (h₁₀ : φ₁ ≠ 0)
    (h₂ : PowerSeries.constantCoeff φ₂ = 0) (h₂₀ : φ₂ ≠ 0) :
    LaurentSeries.substAlgHom h₁ h₁₀ = LaurentSeries.substAlgHom h₂ h₂₀ := by
  subst h; rfl

/-- **Levelwise substitution formula for lifts of Laurent substitutions.** Let `φ ∈ X K⟦X⟧` be
nonzero and `ρ : puiseuxField K →ₐ[K] puiseuxField K` a `K`-algebra endomorphism extending
`LaurentSeries.substAlgHom hφ hφ₀`. Then on every ramified level `n`, `ρ` agrees with
`LaurentSeries.substAlgHom` for a nonzero power series `ψ ∈ X K⟦X⟧` of the same order as `φ`. -/
theorem exists_levelEmbedding_eq_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (n : ℕ+) :
    ∃ (ψ : K⟦X⟧) (hψ : PowerSeries.constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0),
      ψ.order = φ.order ∧
      ∀ f, ρ (levelEmbedding K n f) =
        levelEmbedding K n (LaurentSeries.substAlgHom hψ hψ₀ f) := by
  have hpow : ρ (levelEmbedding K n (HahnSeries.single 1 1)) ^ (n : ℕ) =
      levelEmbedding K 1 (φ : K⸨X⸩) := by
    rw [← map_pow, ← map_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one,
      levelEmbedding_single_self, ← levelEmbedding_single_self 1, PNat.one_coe, Nat.cast_one,
      ← algebraMap_laurentSeries_apply, hρ, LaurentSeries.substAlgHom_single_one,
      algebraMap_laurentSeries_apply]
  obtain ⟨ψ, hψ, hψ₀, hψord, hψeq⟩ :=
    exists_eq_levelEmbedding_of_pow_eq_levelEmbedding 1 n hφ hφ₀ hpow
  rw [one_mul] at hψeq
  -- On `K⸨X⸩`, `ψ ^ n = expand n φ`, so `subst ψ ∘ expand n = expand n ∘ subst φ`.
  have hψn : ψ ^ (n : ℕ) = PowerSeries.expand (n : ℕ) n.ne_zero φ :=
    ofPowerSeries_injective <| (levelEmbedding K n).injective <| by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, hψeq, hpow, ← expand_coe,
        levelEmbedding_expand_self, algebraMap_laurentSeries_apply]
  have hcomm (g : K⸨X⸩) :
      LaurentSeries.substAlgHom hψ hψ₀ (expand K n g) =
        expand K n (LaurentSeries.substAlgHom hφ hφ₀ g) := by
    rw [← LaurentSeries.substAlgHom_X_pow_eq_expand,
      LaurentSeries.substAlgHom_comp_substAlgHom_apply,
      LaurentSeries.substAlgHom_comp_substAlgHom_apply]
    have hsub : ((PowerSeries.X : K⟦X⟧) ^ (n : ℕ)).subst ψ =
        φ.subst ((PowerSeries.X : K⟦X⟧) ^ (n : ℕ)) := by
      rw [PowerSeries.subst_pow (.of_constantCoeff_zero' hψ),
        PowerSeries.subst_X (.of_constantCoeff_zero' hψ), hψn, PowerSeries.expand_apply]
    exact congrArg (· g) (substAlgHom_congr hsub _ _ _ _)
  refine ⟨ψ, hψ, hψ₀, hψord, fun f ↦ ?_⟩
  -- Decompose `f = ∑ r : Fin n, X ^ r * expand n (contract n f r)` and compare term by term.
  conv_lhs => rw [← sum_single_mul_expand_contract n f]
  conv_rhs => rw [← sum_single_mul_expand_contract n f]
  simp only [map_sum, map_mul, levelEmbedding_expand_self, hρ, hcomm]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hr : HahnSeries.single (r : ℤ) (1 : K) = HahnSeries.single 1 1 ^ (r : ℕ) := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  rw [hr, map_pow, map_pow, map_pow, map_pow, LaurentSeries.substAlgHom_single_one, hψeq]

/-- **Order scaling.** An algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀` multiplies the
additive Puiseux valuation by `φ.order.toNat`. -/
theorem addVal_apply_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = φ.order.toNat • addVal K x := by
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨ψ, hψ, hψ₀, hψord, hlevel⟩ := exists_levelEmbedding_eq_substAlgHom hφ hφ₀ hρ n
  rw [hlevel, addVal_levelEmbedding, addVal_levelEmbedding,
    LaurentSeries.orderTop_substAlgHom, hψord]
  cases hf : f.orderTop with
  | top =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (PowerSeries.toNat_order_ne_zero hφ hφ₀)
    simp [hm, succ_nsmul]
  | coe k =>
    rw [← WithTop.coe_nsmul, WithTop.map_coe, WithTop.map_coe, ← WithTop.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_div_assoc]

/-- **Rational order scaling.** An algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀` multiplies
the rational Hahn-series order by `φ.order.toNat`. -/
theorem order_apply_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = φ.order.toNat * (x : HahnSeries ℚ K).order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hρx : ρ x ≠ 0 := (map_ne_zero_iff ρ ρ.toRingHom.injective).mpr hx
  have h := addVal_apply_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x
  rw [addVal_apply, addVal_apply,
    ← order_eq_orderTop_of_ne_zero (Subtype.coe_ne_coe.mpr hρx),
    ← order_eq_orderTop_of_ne_zero (Subtype.coe_ne_coe.mpr hx),
    ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul] at h
  exact h

/-- **Valuation scaling.** An algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀` raises the
multiplicative Puiseux valuation to the power `φ.order.toNat`. -/
theorem valuation_apply_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x ^ φ.order.toNat := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, zero_pow (PowerSeries.toNat_order_ne_zero hφ hφ₀)]
  have hρx : ρ x ≠ 0 := (map_ne_zero_iff ρ ρ.toRingHom.injective).mpr hx
  rw [valuation_apply, valuation_apply,
    HahnSeries.valuation_eq_exp_neg_order (Subtype.coe_ne_coe.mpr hρx),
    HahnSeries.valuation_eq_exp_neg_order (Subtype.coe_ne_coe.mpr hx),
    order_apply_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x,
    ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul]

/-- **Automatic topological embedding.** Every algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀`
to `puiseuxField K` is a topological embedding for the valuation topology. -/
theorem isEmbedding_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    IsEmbedding ρ := by
  set e : ℕ := φ.order.toNat
  have he : (0 : ℚ) < e := by
    exact_mod_cast Nat.pos_of_ne_zero (PowerSeries.toNat_order_ne_zero hφ hφ₀)
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr (le_antisymm ?_ ?_),
    ρ.toRingHom.injective⟩
  · -- Continuity at `0`: the ball `q / e ≤ ord x` maps into `q ≤ ord (ρ x)`.
    refine Filter.tendsto_iff_comap.mp <|
      (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).mpr fun q _ ↦
        ⟨q / e, trivial, fun x hx ↦ ?_⟩
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [addVal_apply_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x]
    have hq : (q : WithTop ℚ) = e • ((q / e : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ he.ne']
    rw [hq]
    exact nsmul_le_nsmul_right hx e
  · -- Open onto its image at `0`: `e * q ≤ ord (ρ x)` forces `q ≤ ord x`.
    refine (hasBasis_nhds_zero.comap ρ).le_basis_iff hasBasis_nhds_zero |>.mpr fun q _ ↦
      ⟨e * q, trivial, fun x hx ↦ ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    rw [addVal_apply_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x] at hx
    cases hord : addVal K x with
    | top => exact le_top
    | coe r =>
      rw [hord, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul] at hx
      exact WithTop.coe_le_coe.mpr (le_of_mul_le_mul_left hx he)

/-- **Automatic continuity.** Every algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀` to
`puiseuxField K` is continuous for the valuation topology. -/
theorem continuous_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ :=
  (isEmbedding_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ).continuous

/-- Upgrade an algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀` to a continuous `K`-algebra
endomorphism of `puiseuxField K`. -/
noncomputable def continuousAlgHomOfSubstAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    puiseuxField K →A[K] puiseuxField K where
  __ := ρ
  cont := continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ

@[simp]
theorem toAlgHom_continuousAlgHomOfSubstAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (continuousAlgHomOfSubstAlgHom hφ hφ₀ hρ).toAlgHom = ρ :=
  (rfl)

@[simp]
theorem coe_continuousAlgHomOfSubstAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    ⇑(continuousAlgHomOfSubstAlgHom hφ hφ₀ hρ) = ⇑ρ :=
  (rfl)

/-- Build the compatible Tate-module element measuring the ratio `ρ₂(t^(1/m)) / ρ₁(t^(1/m))`
for two endomorphisms agreeing on `K⸨X⸩`. -/
private theorem exists_tateModule_of_apply_algebraMap_eq
    {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    ∃ ζ : PrimeToPTateModule 1 K,
      ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1},
        ρ₂ (single K (1 / (m : ℕ)) 1) / ρ₁ (single K (1 / (m : ℕ)) 1) =
          algebraMap K (puiseuxField K) ((PrimeToPTateModule.proj m ζ : Kˣ) : K) := by
  have hroot (m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) :
      ∃ c : rootsOfUnity m K,
        ρ₂ (single K (1 / (m : ℕ)) 1) / ρ₁ (single K (1 / (m : ℕ)) 1) =
          algebraMap K (puiseuxField K) (c : Kˣ) := by
    have : NeZero (m : ℕ) := ⟨m.2.1⟩
    have hpow : (ρ₂ (single K (1 / (m : ℕ)) 1) / ρ₁ (single K (1 / (m : ℕ)) 1)) ^ (m : ℕ) = 1 := by
      have hmul : ((m : ℕ) : ℚ) * (1 / ((m : ℕ) : ℚ)) = 1 :=
        mul_one_div_cancel (Nat.cast_ne_zero.mpr m.2.1)
      rw [div_pow, ← map_pow, ← map_pow, single_pow, one_pow, hmul,
        ← levelEmbedding_single_self 1, PNat.one_coe, Nat.cast_one,
        ← algebraMap_laurentSeries_apply, hρ, div_self]
      exact (map_ne_zero_iff ρ₂ ρ₂.injective).mpr (by simp)
    refine ⟨(TauCeti.rootsOfUnityMulEquiv K (puiseuxField K) (m : ℕ)).symm
      (rootsOfUnity.mkOfPowEq _ hpow), ?_⟩
    simp [TauCeti.algebraMap_rootsOfUnityMulEquiv_symm_apply]
  choose c hc using hroot
  have hcompat : c ∈ primeToPTateModuleSubgroup 1 K := by
    rw [mem_primeToPTateModuleSubgroup_iff]
    intro m n hdvd
    have hpow_single : single K (1 / (m : ℕ)) 1 ^ ((m : ℕ) / n) = single K (1 / (n : ℕ)) 1 := by
      rw [single_pow, one_pow]
      congr 1
      have hmn : (((m : ℕ) / n : ℕ) : ℚ) * (n : ℕ) = m := by
        exact_mod_cast Nat.div_mul_cancel hdvd
      have hm0 : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.2.1
      have hn0 : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.2.1
      field_simp [hm0, hn0]
      linarith
    apply Units.ext
    apply (algebraMap K (puiseuxField K)).injective
    rw [Units.val_pow_eq_pow_val, map_pow, ← hc m, ← hc n, div_pow, ← map_pow, ← map_pow,
      hpow_single]
  exact ⟨PrimeToPTateModule.mk c hcompat, fun m ↦ by rw [PrimeToPTateModule.proj_mk, hc m]⟩

/-- **Uniqueness of lifts up to the Kummer action.** Any two `K`-algebra endomorphisms of
`puiseuxField K` that agree on `K⸨X⸩` differ by precomposition with a unique Kummer automorphism
`kummer K ζ`, `ζ ∈ lim_n μₙ(K)`. -/
theorem existsUnique_kummer_comp_eq_of_apply_algebraMap_eq
    {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    ∃! ζ : PrimeToPTateModule 1 K,
      ρ₁.comp ((kummer K ζ).restrictScalars K).toAlgHom = ρ₂ := by
  obtain ⟨ζ, hζ⟩ := exists_tateModule_of_apply_algebraMap_eq hρ
  have hsingle (n : ℕ+) : levelEmbedding K n (HahnSeries.single 1 1) = single K (1 / n) 1 :=
    Subtype.ext (by simp)
  have hne (n : ℕ+) : ρ₁ (single K (1 / n) 1) ≠ 0 :=
    (map_ne_zero_iff ρ₁ ρ₁.toRingHom.injective).mpr (by simp)
  have hcomp : ρ₁.comp ((kummer K ζ).restrictScalars K).toAlgHom = ρ₂ := by
    refine AlgHom.ext fun x ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
    obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
    let m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1} := ⟨n, n.ne_zero, Nat.coprime_one_right _⟩
    have hk_single :
        ρ₁ (kummer K ζ (levelEmbedding K n (HahnSeries.single 1 1))) =
          ρ₂ (levelEmbedding K n (HahnSeries.single 1 1)) := by
      have hmul : ((1 : ℤ) : ℚ) = (1 / (n : ℚ)) * ((m : ℕ) : ℚ) := by simp [m, one_div]
      rw [hsingle, kummer_single, ← algebraMap_mul_single, map_mul, AlgHom.commutes,
        PrimeToPTateModule.ratChar_ofAdd_eq_zpow ζ m hmul, zpow_one, ← hζ m,
        div_mul_cancel₀ _ (hne n)]
    conv_lhs => rw [← sum_single_mul_expand_contract n f]
    conv_rhs => rw [← sum_single_mul_expand_contract n f]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_restrictScalars,
      map_sum, map_mul, levelEmbedding_expand_self, AlgEquiv.commutes, hρ]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hr : HahnSeries.single (r : ℤ) (1 : K) = HahnSeries.single 1 1 ^ (r : ℕ) := by
      rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
    rw [hr, map_pow, map_pow, map_pow, map_pow, hk_single]
  refine ⟨ζ, hcomp, fun ζ' hζ' ↦ ?_⟩
  apply kummer_injective
  refine AlgEquiv.ext fun x ↦ ?_
  exact ρ₁.toRingHom.injective (by simpa using AlgHom.congr_fun (hζ'.trans hcomp.symm) x)

end SubstAlgHom

section FormalCoordinate

variable {K : Type*} [Field K]

/-- **Levelwise formal-coordinate formula.** An algebraic lift of `LaurentSeries.substAlgEquiv φ`
for a formal coordinate `φ` acts on every ramified level `n` as `LaurentSeries.substAlgEquiv ψ`
for a formal coordinate `ψ`. -/
theorem exists_levelEmbedding_eq_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (n : ℕ+) :
    ∃ ψ : FormalCoordinate K, ∀ f, ρ (levelEmbedding K n f) =
      levelEmbedding K n (LaurentSeries.substAlgEquiv ψ f) := by
  have hρ' : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K)
        (LaurentSeries.substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero f) :=
    fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ f
  obtain ⟨ψ₀, hψ₀, hψ₀ne, hord, hlevel⟩ :=
    exists_levelEmbedding_eq_substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
      hρ' n
  rw [φ.order_toPowerSeries] at hord
  have hunit : IsUnit (PowerSeries.coeff 1 ψ₀) :=
    ((PowerSeries.order_eq_nat.mp hord).1).isUnit
  exact ⟨⟨ψ₀, hψ₀, hunit⟩, fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hlevel f⟩

/-- **Automatic bijectivity for formal-coordinate lifts.** Any `K`-algebra endomorphism of
`puiseuxField K` extending `LaurentSeries.substAlgEquiv φ` is automatically bijective. -/
theorem bijective_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    Function.Bijective ρ := by
  refine ⟨ρ.toRingHom.injective, fun y ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding y
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨ψ, hlevel⟩ := exists_levelEmbedding_eq_substAlgEquiv φ hρ n
  exact ⟨levelEmbedding K n ((LaurentSeries.substAlgEquiv ψ).symm f), by
    rw [hlevel, AlgEquiv.apply_symm_apply]⟩

/-- A lift of a formal coordinate preserves the additive Puiseux valuation. -/
theorem addVal_apply_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = addVal K x := by
  have hρ' := fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ f
  simpa [φ.order_toPowerSeries] using
    addVal_apply_of_apply_algebraMap_substAlgHom
      φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero hρ' x

/-- A lift of a formal coordinate preserves the rational Hahn-series order. -/
theorem order_apply_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = (x : HahnSeries ℚ K).order := by
  have hρ' := fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ f
  simpa [φ.order_toPowerSeries] using
    order_apply_of_apply_algebraMap_substAlgHom
      φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero hρ' x

/-- A lift of a formal coordinate preserves the multiplicative Puiseux valuation. -/
theorem valuation_apply_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x := by
  have hρ' := fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ f
  simpa [φ.order_toPowerSeries] using
    valuation_apply_of_apply_algebraMap_substAlgHom
      φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero hρ' x

/-- A lift of a formal coordinate is continuous for the valuation topology. -/
theorem continuous_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    Continuous ρ :=
  continuous_of_apply_algebraMap_substAlgHom
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
    fun f ↦ by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ f

/-- Upgrade an algebraic lift of `LaurentSeries.substAlgEquiv φ` to a bicontinuous `K`-algebra
automorphism of `puiseuxField K`. -/
noncomputable def continuousAlgEquivOfSubstAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    puiseuxField K ≃A[K] puiseuxField K :=
  let e : puiseuxField K ≃ₐ[K] puiseuxField K :=
    AlgEquiv.ofBijective ρ (bijective_of_apply_algebraMap_substAlgEquiv φ hρ)
  { __ := e
    continuous_toFun := continuous_of_apply_algebraMap_substAlgEquiv φ hρ
    continuous_invFun := by
      refine continuous_of_apply_algebraMap_substAlgEquiv φ⁻¹ (ρ := e.symm.toAlgHom) fun f ↦ ?_
      rw [AlgEquiv.coe_toAlgHom, e.symm_apply_eq]
      simp only [e, AlgEquiv.coe_ofBijective, hρ, ← LaurentSeries.substAlgEquiv_symm,
        AlgEquiv.apply_symm_apply] }

@[simp]
theorem coe_continuousAlgEquivOfSubstAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    ⇑(continuousAlgEquivOfSubstAlgEquiv φ hρ) = ⇑ρ :=
  (rfl)

@[simp]
theorem toAlgHom_continuousAlgEquivOfSubstAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (continuousAlgEquivOfSubstAlgEquiv φ hρ).toAlgEquiv.toAlgHom = ρ :=
  AlgHom.ext fun _ ↦ rfl

end FormalCoordinate

section Existence

section Helpers

variable {K : Type*} [Field K]

/-- A compatible family of level homomorphisms gives the same value on any two level
representatives of the same Puiseux series. -/
private theorem glueLevels_wellDefined (ρLevel : ℕ+ → K⸨X⸩ →ₐ[K] puiseuxField K)
    (hcompat : ∀ (n d : ℕ+) (f : K⸨X⸩), ρLevel (n * d) (expand K d f) = ρLevel n f)
    {n m : ℕ+} {f g : K⸨X⸩} (h : levelEmbedding K n f = levelEmbedding K m g) :
    ρLevel n f = ρLevel m g := by
  have hfg : expand K m f = expand K n g := (levelEmbedding K (n * m)).injective <| by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [levelEmbedding_expand, mul_comm n m, levelEmbedding_expand, h]
  rw [← hcompat n m f, hfg, mul_comm n m, hcompat m n g]

/-- Assemble a compatible family of level homomorphisms `K⸨X⸩ →ₐ[K] puiseuxField K` into a
single endomorphism of `puiseuxField K`. -/
private noncomputable def glueLevels (ρLevel : ℕ+ → K⸨X⸩ →ₐ[K] puiseuxField K)
    (hcompat : ∀ (n d : ℕ+) (f : K⸨X⸩), ρLevel (n * d) (expand K d f) = ρLevel n f) :
    puiseuxField K →ₐ[K] puiseuxField K := by
  let toFun (x : puiseuxField K) : puiseuxField K :=
    let n := Classical.choose (exists_mem_range_levelEmbedding x)
    let f := Classical.choose
      ((AlgHom.mem_range _).mp (Classical.choose_spec (exists_mem_range_levelEmbedding x)))
    ρLevel n f
  have htoFun (n : ℕ+) (f : K⸨X⸩) : toFun (levelEmbedding K n f) = ρLevel n f :=
    glueLevels_wellDefined ρLevel hcompat <| Classical.choose_spec
      ((AlgHom.mem_range _).mp
        (Classical.choose_spec (exists_mem_range_levelEmbedding (levelEmbedding K n f))))
  exact
    { toFun := toFun
      map_one' := by
        calc toFun 1 = toFun (levelEmbedding K 1 1) := by rw [map_one]
          _ = ρLevel 1 1 := htoFun 1 1
          _ = 1 := map_one _
      map_zero' := by
        calc toFun 0 = toFun (levelEmbedding K 1 0) := by rw [map_zero]
          _ = ρLevel 1 0 := htoFun 1 0
          _ = 0 := map_zero _
      map_mul' x y := by
        obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
        obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
        obtain ⟨m, hm⟩ := exists_mem_range_levelEmbedding y
        obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hm
        have hxy : levelEmbedding K n f * levelEmbedding K m g =
            levelEmbedding K (n * m) (expand K m f * expand K n g) := by
          rw [map_mul, levelEmbedding_expand, mul_comm n m, levelEmbedding_expand]
        rw [hxy, htoFun, htoFun, htoFun, map_mul, hcompat, mul_comm n m, hcompat]
      map_add' x y := by
        obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
        obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
        obtain ⟨m, hm⟩ := exists_mem_range_levelEmbedding y
        obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hm
        have hxy : levelEmbedding K n f + levelEmbedding K m g =
            levelEmbedding K (n * m) (expand K m f + expand K n g) := by
          rw [map_add, levelEmbedding_expand, mul_comm n m, levelEmbedding_expand]
        rw [hxy, htoFun, htoFun, htoFun, map_add, hcompat, mul_comm n m, hcompat]
      commutes' c := by
        calc toFun (algebraMap K (puiseuxField K) c)
            = toFun (levelEmbedding K 1 (algebraMap K K⸨X⸩ c)) := by rw [AlgHom.commutes]
          _ = ρLevel 1 (algebraMap K K⸨X⸩ c) := htoFun 1 _
          _ = algebraMap K (puiseuxField K) c := AlgHom.commutes _ c }

/-- Evaluating `glueLevels` on level `n` recovers `ρLevel n`. -/
private theorem glueLevels_levelEmbedding (ρLevel : ℕ+ → K⸨X⸩ →ₐ[K] puiseuxField K)
    (hcompat : ∀ (n d : ℕ+) (f : K⸨X⸩), ρLevel (n * d) (expand K d f) = ρLevel n f)
    (n : ℕ+) (f : K⸨X⸩) :
    glueLevels ρLevel hcompat (levelEmbedding K n f) = ρLevel n f :=
  glueLevels_wellDefined ρLevel hcompat <| Classical.choose_spec
    ((AlgHom.mem_range _).mp
      (Classical.choose_spec (exists_mem_range_levelEmbedding (levelEmbedding K n f))))

end Helpers

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field `K`, every element `c : K` admits a compatible system of
`n`-th roots `r : ℕ+ → K` with `r 1 = c` and `r (n * d) ^ d = r n`. -/
private theorem exists_compatible_pow_root (c : K) :
    ∃ r : ℕ+ → K, r 1 = c ∧ ∀ n d : ℕ+, r (n * d) ^ (d : ℕ) = r n := by
  let a : ℕ → K := Nat.rec c fun k ak ↦
    Classical.choose (IsAlgClosed.exists_pow_nat_eq ak (Nat.succ_pos k))
  have ha (k : ℕ) : a (k + 1) ^ (k + 1) = a k :=
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (a k) (Nat.succ_pos k))
  have ha_pow {k m : ℕ} (h : k ≤ m) : a m ^ (m.factorial / k.factorial) = a k := by
    induction m, h using Nat.le_induction with
    | base => rw [Nat.div_self (Nat.factorial_pos k), pow_one]
    | succ m hkm ih =>
      rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hkm),
        pow_mul, ha m, ih]
  refine ⟨fun n ↦ a n ^ ((n : ℕ).factorial / (n : ℕ)), ?_, fun n d ↦ ?_⟩
  · dsimp only
    rw [PNat.one_coe, Nat.factorial_one, Nat.div_self zero_lt_one]
    exact ha 0
  · have hnd : (n : ℕ) ≤ (n * d : ℕ+) := Nat.le_mul_of_pos_right n d.pos
    have hfac : ((n * d : ℕ+) : ℕ).factorial / ((n * d : ℕ+) : ℕ) * (d : ℕ) =
        (((n * d : ℕ+) : ℕ).factorial / (n : ℕ).factorial) *
          ((n : ℕ).factorial / (n : ℕ)) := by
      have hdvd1 : ((n * d : ℕ+) : ℕ) ∣ ((n * d : ℕ+) : ℕ).factorial :=
        Nat.dvd_factorial (n * d).pos le_rfl
      have hdvd2 : (n : ℕ).factorial ∣ ((n * d : ℕ+) : ℕ).factorial :=
        Nat.factorial_dvd_factorial hnd
      have hdvd3 : (n : ℕ) ∣ (n : ℕ).factorial := Nat.dvd_factorial n.pos le_rfl
      refine Nat.eq_of_mul_eq_mul_right n.pos ?_
      calc (((n * d : ℕ+) : ℕ).factorial / ((n * d : ℕ+) : ℕ) * (d : ℕ)) * (n : ℕ)
          = ((n * d : ℕ+) : ℕ).factorial / ((n * d : ℕ+) : ℕ) * ((n * d : ℕ+) : ℕ) := by
            rw [PNat.mul_coe]; ring
        _ = ((n * d : ℕ+) : ℕ).factorial := Nat.div_mul_cancel hdvd1
        _ = (((n * d : ℕ+) : ℕ).factorial / (n : ℕ).factorial) * (n : ℕ).factorial :=
            (Nat.div_mul_cancel hdvd2).symm
        _ = (((n * d : ℕ+) : ℕ).factorial / (n : ℕ).factorial) *
              (((n : ℕ).factorial / (n : ℕ)) * (n : ℕ)) := by
            rw [Nat.div_mul_cancel hdvd3]
        _ = _ := by ring
    rw [← pow_mul, hfac, pow_mul, ha_pow hnd]

/-- Over an algebraically closed field `K` (of any characteristic), a level-`m` power series with
constant coefficient `1` has an `n`-th root in `puiseuxField K` with leading coefficient `1`. -/
private theorem exists_pow_eq_levelEmbedding_leadingCoeff_one (m n : ℕ+) {u : K⟦X⟧}
    (hu : PowerSeries.constantCoeff u = 1) :
    ∃ w : puiseuxField K,
      w ^ (n : ℕ) = levelEmbedding K m (u : K⸨X⸩) ∧ (w : HahnSeries ℚ K).leadingCoeff = 1 := by
  refine PNat.strongInductionOn (p := fun n ↦ ∀ (m : ℕ+) {u : K⟦X⟧},
    PowerSeries.constantCoeff u = 1 →
      ∃ w : puiseuxField K,
        w ^ (n : ℕ) = levelEmbedding K m (u : K⸨X⸩) ∧ (w : HahnSeries ℚ K).leadingCoeff = 1)
    n ?_ m hu
  intro n ih m u hu
  by_cases hn : ((n : ℕ) : K) = 0
  · obtain ⟨p, n', _, hp, hpn', hlt⟩ := exists_prime_char_mul_lt hn
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    have : ExpChar K p := .prime hp
    let u' : K⟦X⟧ := u.map (frobeniusEquiv K p).symm.toRingHom
    have hu'const : PowerSeries.constantCoeff u' = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hu, map_one]
    have hu'pow : u' ^ (p : ℕ) = PowerSeries.expand (p : ℕ) p.ne_zero u := by
      rw [← PowerSeries.map_frobenius_expand (hp := p.ne_zero)]
      ext k
      rw [PowerSeries.coeff_map, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      split_ifs
      · rw [PowerSeries.coeff_map, ← coe_frobeniusEquiv, RingEquiv.toRingHom_eq_coe,
          RingHom.coe_coe, RingEquiv.apply_symm_apply]
      · exact map_zero _
    obtain ⟨w, hw, hlead⟩ := ih n' hlt (m * p) hu'const
    refine ⟨w, ?_, hlead⟩
    rw [← hpn', PNat.mul_coe, mul_comm, pow_mul, hw, ← map_pow, ← map_pow (ofPowerSeries ℤ K),
      hu'pow, ← expand_coe, levelEmbedding_expand]
  · obtain ⟨v, hv, hvc⟩ := PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow hn one_ne_zero
      (by rw [one_pow, hu])
    refine ⟨levelEmbedding K m (v : K⸨X⸩), by rw [← map_pow, ← map_pow (ofPowerSeries ℤ K), hv],
      ?_⟩
    rw [coe_levelEmbedding, leadingCoeff_ramifiedEmbedding, leadingCoeff_eq,
      PowerSeries.order_coe, PowerSeries.order_zero_of_isUnit
        (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hvc]; exact isUnit_one)),
      ENat.toNat_zero, Nat.cast_zero, PowerSeries.coeff_coe]
    simp only [lt_irrefl, ↓reduceIte, Int.natAbs_zero, PowerSeries.coeff_zero_eq_constantCoeff, hvc]

/-- Over an algebraically closed field `K`, any nonzero `φ ∈ X K⟦X⟧` admits a compatible system of
`n`-th roots `α : ℕ+ → puiseuxField K` with `α n ^ n = φ` and `α (n * d) ^ d = α n`. -/
private theorem exists_compatible_pow_roots_of_powerSeries {φ : K⟦X⟧} (hφ₀ : φ ≠ 0) :
    ∃ α : ℕ+ → puiseuxField K,
      (∀ n : ℕ+, α n ^ (n : ℕ) = levelEmbedding K 1 (φ : K⸨X⸩)) ∧
      (∀ n d : ℕ+, α (n * d) ^ (d : ℕ) = α n) := by
  have hφcoe0 : (φ : K⸨X⸩) ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr hφ₀
  set e : ℕ := φ.order.toNat
  set u : K⟦X⟧ := _root_.LaurentSeries.powerSeriesPart (φ : K⸨X⸩)
  set c : K := PowerSeries.constantCoeff u
  have hc0 : c ≠ 0 :=
    (PowerSeries.isUnit_iff_constantCoeff.mp
      (TauCeti.LaurentSeries.isUnit_powerSeriesPart hφcoe0)).ne_zero
  set u₁ : K⟦X⟧ := PowerSeries.C c⁻¹ * u
  have hu₁ : PowerSeries.constantCoeff u₁ = 1 := by simp [u₁, c, inv_mul_cancel₀ hc0]
  have hφsplit : levelEmbedding K 1 (φ : K⸨X⸩) =
      single K (e : ℚ) c * levelEmbedding K 1 (u₁ : K⸨X⸩) := by
    apply Subtype.ext
    rw [coe_levelEmbedding, MulMemClass.coe_mul, coe_single, coe_levelEmbedding]
    have hu₁coe : (u₁ : K⸨X⸩) = HahnSeries.C c⁻¹ * (u : K⸨X⸩) := by simp [u₁]
    rw [hu₁coe, map_mul, HahnSeries.C_apply, ramifiedEmbedding_single, Int.cast_zero, zero_div,
      ← mul_assoc, HahnSeries.single_mul_single, add_zero, mul_inv_cancel₀ hc0]
    have hsingle : HahnSeries.single (e : ℚ) (1 : K) =
        ramifiedEmbedding K 1 (HahnSeries.single (e : ℤ) 1) := by
      rw [ramifiedEmbedding_single]; simp
    rw [hsingle, ← map_mul, ← PowerSeries.order_coe,
      _root_.LaurentSeries.single_order_mul_powerSeriesPart]
  obtain ⟨r, hr1, hrpow⟩ := exists_compatible_pow_root c
  choose w hwpow hwlead using fun n : ℕ+ ↦
    exists_pow_eq_levelEmbedding_leadingCoeff_one 1 n hu₁
  have hwcompat (n d : ℕ+) : w (n * d) ^ (d : ℕ) = w n :=
    eq_of_pow_eq_of_leadingCoeff_eq (n := n)
      (by rw [← pow_mul, mul_comm, ← PNat.mul_coe, hwpow, hwpow])
      (by rw [SubmonoidClass.coe_pow, TauCeti.hahnSeries_leadingCoeff_pow, hwlead, one_pow, hwlead])
  refine ⟨fun n ↦ single K ((e : ℚ) / n) (r n) * w n, fun n ↦ ?_, fun n d ↦ ?_⟩
  · rw [mul_pow, single_pow, mul_div_cancel₀ _ (by exact_mod_cast n.ne_zero), hwpow, hφsplit]
    have hrn : r n ^ (n : ℕ) = c := by simpa [hr1] using hrpow 1 n
    rw [hrn]
  · rw [mul_pow, single_pow, hrpow, hwcompat]
    congr 2
    push_cast
    field_simp [(by exact_mod_cast n.ne_zero : ((n : ℕ) : ℚ) ≠ 0),
      (by exact_mod_cast d.ne_zero : ((d : ℕ) : ℚ) ≠ 0)]

/-- **Existence of continuous lifts of Laurent substitutions.** Over an algebraically closed field
`K` of any characteristic, every Laurent substitution `LaurentSeries.substAlgHom hφ hφ₀` lifts to
a continuous `K`-algebra endomorphism of `puiseuxField K`. -/
theorem exists_continuousAlgHom_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) :
    ∃ ρ : puiseuxField K →A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
  obtain ⟨α, hαpow, hαcompat⟩ := exists_compatible_pow_roots_of_powerSeries hφ₀
  choose ψ hψ hψ₀ _ hψeq using fun n : ℕ+ ↦
    exists_eq_levelEmbedding_of_pow_eq_levelEmbedding 1 n hφ hφ₀ (hαpow n)
  simp only [one_mul] at hψeq
  let ρLevel (n : ℕ+) : K⸨X⸩ →ₐ[K] puiseuxField K :=
    (levelEmbedding K n).comp (LaurentSeries.substAlgHom (hψ n) (hψ₀ n))
  have hcompat (n d : ℕ+) (f : K⸨X⸩) : ρLevel (n * d) (expand K d f) = ρLevel n f := by
    have hψd : ψ (n * d) ^ (d : ℕ) = PowerSeries.expand (d : ℕ) d.ne_zero (ψ n) :=
      ofPowerSeries_injective <| (levelEmbedding K (n * d)).injective <| by
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, hψeq, hαcompat,
          ← expand_coe, levelEmbedding_expand]
    simp only [ρLevel, AlgHom.comp_apply, ← LaurentSeries.substAlgHom_X_pow_eq_expand,
      LaurentSeries.substAlgHom_comp_substAlgHom_apply]
    have hsub : ((PowerSeries.X : K⟦X⟧) ^ (d : ℕ)).subst (ψ (n * d)) =
        (ψ n).subst ((PowerSeries.X : K⟦X⟧) ^ (d : ℕ)) := by
      rw [PowerSeries.subst_pow (.of_constantCoeff_zero' (hψ (n * d))),
        PowerSeries.subst_X (.of_constantCoeff_zero' (hψ (n * d))), hψd,
        PowerSeries.expand_apply]
    rw [← levelEmbedding_expand n d, ← LaurentSeries.substAlgHom_X_pow_eq_expand,
      LaurentSeries.substAlgHom_comp_substAlgHom_apply]
    exact congrArg (levelEmbedding K (n * d)) (congrArg (· f) (substAlgHom_congr hsub _ _ _ _))
  let ρ : puiseuxField K →ₐ[K] puiseuxField K := glueLevels ρLevel hcompat
  have hψ1 : ψ 1 = φ := ofPowerSeries_injective <| (levelEmbedding K 1).injective <| by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψeq 1]
    simpa [pow_one] using hαpow 1
  have hρ (f : K⸨X⸩) : ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
    rw [algebraMap_laurentSeries_apply, glueLevels_levelEmbedding]
    simp only [ρLevel, AlgHom.comp_apply, algebraMap_laurentSeries_apply]
    congr 1
    subst hψ1
    rfl
  exact ⟨continuousAlgHomOfSubstAlgHom hφ hφ₀ hρ, hρ⟩

/-- **Existence of bicontinuous lifts of formal coordinates.** Over an algebraically closed field
`K` of any characteristic, every formal coordinate `φ` lifts to a bicontinuous `K`-algebra
automorphism of `puiseuxField K`. -/
theorem exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K) :
    ∃ ρ : puiseuxField K ≃A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_continuousAlgHom_apply_algebraMap_substAlgHom
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
  have hρ₀' : ∀ f, ρ₀.toAlgHom (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) :=
    fun f ↦ by simpa only [ContinuousAlgHom.coe_coe, LaurentSeries.coe_substAlgEquiv] using hρ₀ f
  exact ⟨continuousAlgEquivOfSubstAlgEquiv φ hρ₀', hρ₀'⟩

end Existence

end TauCeti.puiseuxField
