/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Valuation.Discrete.Comap
import TauCeti.RingTheory.Valuation.NontrivialComap

/-!
# Uniqueness of rank-one discrete valuations on rank-one Henselian valued fields

Let `K` be a field equipped with a nontrivial rank-one valuation `v₀` whose valuation ring is
Henselian (`HenselianRing v₀.integer (maximalIdeal v₀.integer)`), and let `v` be any rank-one
discrete valuation on `K` (not assumed Henselian). This file proves that `v` is equivalent to `v₀`.

The argument is elementary and needs neither completeness nor finiteness of the residue field.
Since `2` and `3` cannot both lie in the maximal ideal of the local ring `v₀.integer`, some
`ℓ ∈ {2, 3}` is invertible in `v₀.integer`. By Hensel's lemma, every element `1 + y` with
`v₀ y < 1` is an `ℓ ^ k`-th power in `v₀.integer` for every `k : ℕ`. Because the value group of
`v` is cyclic (hence has no nontrivial `ℓ`-divisible element), `v (1 + y) = 1` and therefore
`v y ≤ 1` whenever `v₀ y < 1`. Archimedeanity of the two value groups then upgrades this to
`v x < 1 ↔ v₀ x < 1`, which is equivalence of the two valuations.

As a consequence, a rank-one Henselian valuative relation on `K` is the only rank-one discrete
valuative relation on `K`, and every integral algebra `L / K` into a ring carrying a rank-one
discrete valuative relation is automatically a `ValuativeExtension K L`. In particular, any finite
algebra structure between nonarchimedean local fields is automatically compatible with their
valuations.

Without the rank-one hypothesis on `v₀`, the result is false: a rank-two Henselian valuation ring
such as `ℚ[[t]] + s ℚ((t))[[s]]` on `ℚ((t))((s))` admits the inequivalent rank-one discrete
`s`-adic valuation as a coarsening. Without discreteness of `v`, it is also false: a `q`-adic
valuation on `ℚ` (`q ≠ p`) extends to a non-discrete valuation on `ℚ_p`.

## Main results

* `Valuation.isEquiv_of_isRankOneDiscrete_of_henselianRing`: every rank-one discrete valuation on
  a field carrying a nontrivial rank-one Henselian valuation is equivalent to it.
* `Valuation.isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing`: the `ValuativeRel` form.
* `ValuativeRel.eq_of_isRankOneDiscrete_of_henselianRing`: a field with a nontrivial rank-one
  Henselian valuative relation carries no other rank-one discrete valuative relation.
* `RingHom.map_vle_map_iff_of_isRankOneDiscrete`: a ring homomorphism from a nontrivial rank-one
  Henselian valued field into a ring with a rank-one discrete valuative relation preserves and
  reflects `≤ᵥ` whenever the pullback valuation is nontrivial.
* `ValuativeExtension.of_isRankOneDiscrete`: an integral algebra from a nontrivial rank-one
  Henselian valued field to a ring with a rank-one discrete valuative relation is a
  `ValuativeExtension`.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. 108 (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], §4.4.
-/

public section

open ValuativeRel IsLocalRing
open scoped ValuativeRel

namespace Valuation

section Valuation

variable {K Γ₀ Γ : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]

/-- Every commutative local ring has an integer `ℓ > 1` that is a unit (`ℓ = 2` or `ℓ = 3`). -/
private theorem exists_one_lt_isUnit_natCast (R : Type*) [CommRing R] [IsLocalRing R] :
    ∃ ℓ : ℕ, 1 < ℓ ∧ IsUnit (ℓ : R) := by
  by_cases h2 : IsUnit ((2 : ℕ) : R)
  · exact ⟨2, by decide, h2⟩
  · refine ⟨3, by decide, ?_⟩
    by_contra h3
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have hsub := (maximalIdeal R).sub_mem ((mem_maximalIdeal _).mpr h3)
        ((mem_maximalIdeal _).mpr h2)
      have heq : ((3 : ℕ) : R) - ((2 : ℕ) : R) = 1 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
      rwa [heq] at hsub
    exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- In a rank-one discrete valuation, a nonzero element that admits `ℓ ^ k`-th roots for all `k`
(for some `ℓ > 1`) has valuation `1`. -/
private theorem val_eq_one_of_forall_exists_pow_eq (v : Valuation K Γ) [v.IsRankOneDiscrete]
    {ℓ : ℕ} (hℓ : 1 < ℓ) {x : K} (hx : v x ≠ 0) (h : ∀ k : ℕ, ∃ z : K, z ^ ℓ ^ k = x) :
    v x = 1 := by
  set γ := IsRankOneDiscrete.generator v
  have hγ : γ < 1 := IsRankOneDiscrete.generator_lt_one v
  have mem_zpowers {a : K} (ha : v a ≠ 0) : ∃ n : ℤ, γ ^ n = Units.mk0 (v a) ha :=
    Subgroup.mem_zpowers_iff.mp <|
      (IsRankOneDiscrete.generator_zpowers_eq_valueGroup v).symm ▸
        MonoidWithZeroHom.mem_valueGroup _ ⟨a, rfl⟩
  obtain ⟨m, hm⟩ := mem_zpowers hx
  suffices hm0 : m = 0 by
    rw [hm0, zpow_zero] at hm
    exact congrArg Units.val hm.symm
  by_contra hm0
  obtain ⟨z, hz⟩ := h m.natAbs
  have hz0 : v z ≠ 0 := fun h0 ↦
    hx (by rw [← hz, map_pow, h0, zero_pow (pow_ne_zero _ (by omega))])
  obtain ⟨n, hn⟩ := mem_zpowers hz0
  have hpow : γ ^ (n * (ℓ ^ m.natAbs : ℕ)) = γ ^ m := by
    rw [zpow_mul, zpow_natCast, hn, hm]
    ext
    simp [← map_pow, hz]
  have heq : n * (ℓ ^ m.natAbs : ℕ) = m := (zpow_right_strictAnti hγ).injective hpow
  have hdvd : ℓ ^ m.natAbs ∣ m.natAbs :=
    ⟨n.natAbs, by
      conv_lhs => rw [← heq]
      rw [Int.natAbs_mul, Int.natAbs_natCast, mul_comm]⟩
  exact (Nat.lt_pow_self hℓ).not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) hdvd)

/-- On a field with a Henselian valuation `v₀`, every rank-one discrete valuation `v` is bounded by
`1` on the open unit ball `{y | v₀ y < 1}` of `v₀`. -/
private theorem val_le_one_of_lt_one_of_henselianRing (v : Valuation K Γ) [v.IsRankOneDiscrete]
    (v₀ : Valuation K Γ₀) [HenselianRing v₀.integer (maximalIdeal v₀.integer)]
    {y : K} (hy : v₀ y < 1) : v y ≤ 1 := by
  obtain ⟨ℓ, hℓ, hℓu⟩ := exists_one_lt_isUnit_natCast v₀.integer
  -- Every principal unit `1 + y` is an `ℓ ^ k`-th power in `v₀.integer` by Hensel's lemma, hence
  -- has `v`-valuation `1`.
  have h1y_ne : v (1 + y) ≠ 0 := by
    rw [ne_zero_iff]
    intro h0
    have h1 := v₀.map_one_add_of_lt hy
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have h1y : v (1 + y) = 1 := by
    refine val_eq_one_of_forall_exists_pow_eq v hℓ h1y_ne fun k ↦ ?_
    have hℓk : IsUnit ((ℓ ^ k : ℕ) : v₀.integer) := by
      simpa only [Nat.cast_pow] using hℓu.pow k
    have hy' : (⟨1 + y, (v₀.map_one_add_of_lt hy).le⟩ : v₀.integer) - 1 ∈
        maximalIdeal v₀.integer := by
      have hsub : (⟨1 + y, (v₀.map_one_add_of_lt hy).le⟩ : v₀.integer) - 1 = ⟨y, hy.le⟩ :=
        Subtype.ext (add_sub_cancel_left 1 y)
      rw [hsub]
      exact v₀.mem_maximalIdeal_iff.mpr hy
    obtain ⟨a, ha, -⟩ :=
      TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem le_rfl hℓk hy'
    exact ⟨(a : K), by simpa using congrArg Subtype.val ha⟩
  by_contra hlt
  rw [not_le] at hlt
  have h1lt : v 1 < v y := by rwa [map_one]
  exact hlt.ne' ((v.map_add_eq_of_lt_right h1lt).symm.trans h1y)

/-- The value group with zero of a rank-one discrete valuation is multiplicatively Archimedean. -/
private theorem mulArchimedean_valueGroup₀_of_isRankOneDiscrete (v : Valuation K Γ)
    [v.IsRankOneDiscrete] : MulArchimedean v.ValueGroup₀ where
  arch x {y} hy := by
    obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.mp (zero_lt_one.trans hy).ne'
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, zero_le⟩
    obtain ⟨t, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx0
    set γ := IsRankOneDiscrete.generator v
    have hγ : γ < 1 := IsRankOneDiscrete.generator_lt_one v
    have ht : t.1 ∈ Subgroup.zpowers γ := by
      rw [IsRankOneDiscrete.generator_zpowers_eq_valueGroup]; exact t.2
    have hu : u.1 ∈ Subgroup.zpowers γ := by
      rw [IsRankOneDiscrete.generator_zpowers_eq_valueGroup]; exact u.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hu1 : (1 : v.valueGroup) < u := WithZero.coe_lt_coe.mp hy
    have hkneg : k < 0 :=
      (zpow_right_strictAnti hγ).lt_iff_gt.mp (by simpa [hk] using (show (1 : Γˣ) < u.1 from hu1))
    refine ⟨m.natAbs, ?_⟩
    suffices t.1 ≤ u.1 ^ m.natAbs by
      have hsub : t ≤ u ^ m.natAbs := by
        change t.1 ≤ (u ^ m.natAbs).1
        simpa only [Subgroup.coe_pow] using this
      exact_mod_cast hsub
    rw [← hm, ← hk, ← zpow_natCast, ← zpow_mul, (zpow_right_strictAnti hγ).le_iff_ge]
    have hneg : -(m.natAbs : ℤ) ≤ m := by omega
    nlinarith

/-- For a rank-one valuation `w`, powers of any nonzero element with `w x < 1` make any element
`y` smaller than `1`. -/
private theorem exists_pow_mul_lt_one (w : Valuation K Γ) [MulArchimedean w.ValueGroup₀]
    {x : K} (hx0 : x ≠ 0) (hx : w x < 1) (y : K) : ∃ n : ℕ, w (x ^ n * y) < 1 := by
  have hxinv : 1 < w.restrict x⁻¹ := by
    rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt, map_one,
      Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀,
      coe_toMonoidWithZeroHom, map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (w.ne_zero_iff.mpr hx0), hx⟩
  obtain ⟨n, hn⟩ := MulArchimedean.arch (w.restrict y) hxinv
  refine ⟨n + 1, ?_⟩
  have hlt : w y < (w x⁻¹) ^ (n + 1) := by
    simpa only [map_pow, Valuation.restrict_def,
      MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀, coe_toMonoidWithZeroHom] using
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (hn.trans_lt (pow_lt_pow_right₀ hxinv n.lt_succ_self))
  rw [map_inv₀ w x, inv_pow] at hlt
  rw [map_mul, map_pow]
  have hpos : 0 < w x ^ (n + 1) := pow_pos (zero_lt_iff.mpr (w.ne_zero_iff.mpr hx0)) _
  simpa [mul_inv_cancel₀ hpos.ne'] using mul_lt_mul_of_pos_left hlt hpos

/-- Two nontrivial rank-one valuations on a field are equivalent as soon as one is bounded by `1`
on the open unit ball of the other. -/
private theorem isEquiv_of_forall_lt_one_le_one (v : Valuation K Γ) [v.IsNontrivial]
    [MulArchimedean v.ValueGroup₀] (v₀ : Valuation K Γ₀) [v₀.IsNontrivial]
    [MulArchimedean v₀.ValueGroup₀] (hle : ∀ {y : K}, v₀ y < 1 → v y ≤ 1) :
    v.IsEquiv v₀ := by
  refine isEquiv_iff_val_lt_one.mpr fun {x} ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- If `v x < 1` and `1 ≤ v₀ x`, pick `a` with `0 < v₀ a < 1`. Large powers of `x⁻¹` make
    -- `v (a * x⁻¹ ^ n) > 1` while keeping `v₀ (a * x⁻¹ ^ n) ≤ v₀ a < 1`.
    by_contra hx1
    rw [not_lt] at hx1
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx1
    obtain ⟨a, ha0, ha1⟩ := IsNontrivial.exists_lt_one (v := v₀)
    obtain ⟨n, hn⟩ := exists_pow_mul_lt_one v hx0 hx a⁻¹
    have hv0_lt : v₀ (a * x⁻¹ ^ n) < 1 := by
      rw [map_mul, map_pow, map_inv₀]
      exact (mul_le_of_le_one_right zero_le
        (pow_le_one₀ zero_le (inv_le_one_of_one_le₀ hx1))).trans_lt ha1
    have hpos : 0 < v (x ^ n * a⁻¹) :=
      zero_lt_iff.mpr (v.ne_zero_iff.mpr (mul_ne_zero (pow_ne_zero n hx0) (inv_ne_zero ha0)))
    have hv_gt : 1 < v (a * x⁻¹ ^ n) := by
      have heq : v (a * x⁻¹ ^ n) = (v (x ^ n * a⁻¹))⁻¹ := by
        simp [map_mul, map_pow, map_inv₀]
      rw [heq]
      exact one_lt_inv_iff₀.mpr ⟨hpos, hn⟩
    exact hv_gt.not_ge (hle hv0_lt)
  · -- If `v₀ x < 1` and `x ≠ 0` with `v x = 1`, pick `b` with `0 < v b < 1`. Large powers of `x`
    -- make `v₀ (x ^ n * b⁻¹) < 1` while `v (x ^ n * b⁻¹) = v b⁻¹ > 1`.
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    refine lt_of_le_of_ne (hle hx) fun hvx1 ↦ ?_
    obtain ⟨b, hb0, hb1⟩ := IsNontrivial.exists_lt_one (v := v)
    obtain ⟨n, hn⟩ := exists_pow_mul_lt_one v₀ hx0 hx b⁻¹
    have hgt : 1 < v b⁻¹ := by
      rw [map_inv₀]
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (v.ne_zero_iff.mpr hb0), hb1⟩
    have hv_eq : v (x ^ n * b⁻¹) = v b⁻¹ := by
      rw [map_mul, map_pow, hvx1, one_pow, one_mul]
    exact hgt.not_ge (hv_eq ▸ hle hn)

/-- **Uniqueness of rank-one discrete valuations on rank-one Henselian valued fields.** If `v₀` is
a nontrivial rank-one valuation on a field `K` whose valuation ring is Henselian, then every
rank-one discrete valuation `v` on `K` is equivalent to `v₀`. -/
theorem isEquiv_of_isRankOneDiscrete_of_henselianRing (v : Valuation K Γ) [v.IsRankOneDiscrete]
    (v₀ : Valuation K Γ₀) [v₀.IsNontrivial] [MulArchimedean v₀.ValueGroup₀]
    [HenselianRing v₀.integer (maximalIdeal v₀.integer)] :
    v.IsEquiv v₀ :=
  have : MulArchimedean v.ValueGroup₀ := mulArchimedean_valueGroup₀_of_isRankOneDiscrete v
  isEquiv_of_forall_lt_one_le_one v v₀ (val_le_one_of_lt_one_of_henselianRing v v₀)

end Valuation

section ValuativeRel

variable {K Γ : Type*} [Field K] [ValuativeRel K]
  [ValuativeRel.IsNontrivial K] [ValuativeRel.IsRankLeOne K]
  [HenselianRing (valuation K).integer (maximalIdeal (valuation K).integer)]
  [LinearOrderedCommGroupWithZero Γ]

/-- **Uniqueness of rank-one discrete valuations for a `ValuativeRel`.** On a field carrying a
nontrivial rank-one Henselian valuative relation, every rank-one discrete valuation is equivalent
to `ValuativeRel.valuation K`. -/
theorem isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing (v : Valuation K Γ)
    [v.IsRankOneDiscrete] : v.IsEquiv (valuation K) :=
  have : MulArchimedean (valuation K).ValueGroup₀ :=
    MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  v.isEquiv_of_isRankOneDiscrete_of_henselianRing (valuation K)

end ValuativeRel

end Valuation

namespace ValuativeRel

/-- **Uniqueness of a rank-one discrete valuative relation.** If `r₁` and `r₂` are valuative
relations on a field `K` such that `r₁` is nontrivial, rank at most one, and Henselian, while `r₂`
has a rank-one discrete valuation, then `r₁ = r₂`. -/
theorem eq_of_isRankOneDiscrete_of_henselianRing {K : Type*} [Field K]
    (r₁ r₂ : ValuativeRel K) [@IsNontrivial K _ r₁] [@IsRankLeOne K _ r₁]
    [HenselianRing (@valuation K _ r₁).integer (maximalIdeal (@valuation K _ r₁).integer)]
    [(@valuation K _ r₂).IsRankOneDiscrete] : r₁ = r₂ := by
  have h : (@valuation K _ r₂).IsEquiv (@valuation K _ r₁) := by
    let := r₁
    exact Valuation.isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing (@valuation K _ r₂)
  ext a b
  have h₁ : r₁.vle a b ↔ @valuation K _ r₁ a ≤ @valuation K _ r₁ b := by
    let := r₁
    exact (valuation K).vle_iff_le
  have h₂ : r₂.vle a b ↔ @valuation K _ r₂ a ≤ @valuation K _ r₂ b := by
    let := r₂
    exact (valuation K).vle_iff_le
  exact h₁.trans ((h a b).symm.trans h₂.symm)

end ValuativeRel

section RingHom

variable {K L : Type*} [Field K] [ValuativeRel K]
  [ValuativeRel.IsNontrivial K] [ValuativeRel.IsRankLeOne K]
  [HenselianRing (valuation K).integer (maximalIdeal (valuation K).integer)]
  [Ring L] [ValuativeRel L] [(valuation L).IsRankOneDiscrete]

/-- **A ring homomorphism into a rank-one discretely valued ring preserves and reflects `≤ᵥ`.**
If `K` carries a nontrivial rank-one Henselian valuative relation and the pullback of the rank-one
discrete valuation of `L` along `f : K →+* L` is nontrivial, then `f x ≤ᵥ f y ↔ x ≤ᵥ y`. -/
theorem RingHom.map_vle_map_iff_of_isRankOneDiscrete (f : K →+* L)
    [((valuation L).comap f).IsNontrivial] (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  have := (valuation L).isRankOneDiscrete_comap f
  have h := ((valuation L).comap f).isEquiv_valuation_of_isRankOneDiscrete_of_henselianRing
  rw [(valuation L).vle_iff_le, (valuation K).vle_iff_le]
  exact h x y

end RingHom

section Algebra

variable (K L : Type*) [Field K] [ValuativeRel K]
  [ValuativeRel.IsNontrivial K] [ValuativeRel.IsRankLeOne K]
  [HenselianRing (valuation K).integer (maximalIdeal (valuation K).integer)]
  [Ring L] [ValuativeRel L] [(valuation L).IsRankOneDiscrete]

/-- **Automatic valuation compatibility for integral extensions.** Every integral algebra from a
nontrivial rank-one Henselian valued field `K` to a ring `L` carrying a rank-one discrete valuative
relation is a `ValuativeExtension K L`. In particular, any finite algebra between nonarchimedean
local fields is automatically compatible with their valuations. -/
theorem ValuativeExtension.of_isRankOneDiscrete [Algebra K L] [Algebra.IsIntegral K L] :
    ValuativeExtension K L :=
  have : ((valuation L).comap (algebraMap K L)).IsNontrivial :=
    (valuation L).isNontrivial_comap_algebraMap
  ⟨fun {a b} ↦ (algebraMap K L).map_vle_map_iff_of_isRankOneDiscrete a b⟩

end Algebra
