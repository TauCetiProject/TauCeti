/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic

import TauCeti.RingTheory.HahnSeries.Multiplication
import TauCeti.RingTheory.LaurentSeries.Puiseux.IntegrallyClosed
import TauCeti.RingTheory.LaurentSeries.Root
import TauCeti.RingTheory.PowerSeries.Hensel
import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed
import TauCeti.RingTheory.RootsOfUnity.PowFiber

/-!
# Roots and level membership in the Puiseux field

This file develops the purely algebraic theory of `d`-th roots in the Puiseux field
`puiseuxField K`, in arbitrary characteristic:

* **Level membership of roots**: over any field `K`, if `y ^ d` lies in the level-`m` subfield of
  `puiseuxField K`, then `y` lies in the level-`(m * d)` subfield
  (`mem_range_levelEmbedding_of_pow_mem_range`). Factoring `d` into primes splits this into the
  characteristic-`p` coefficient formula (`coeff_pow_charP`) and the tame case `(p : K) ≠ 0`, which
  uses Hensel's lemma and descent of roots of unity (`TauCeti.rootsOfUnityMulEquiv`).
* **Rootability of the unit group**: `(puiseuxField K)ˣ` is `ℕ`-rootable if and only if `Kˣ` is
  `ℕ`-rootable (`nonempty_rootableBy_units_nat_iff`), with `instRootableByUnitsNat` registered when
  `[RootableBy Kˣ ℕ]`.

## Main definitions

* `TauCeti.puiseuxField.instRootableByUnitsNat`: `(puiseuxField K)ˣ` is `ℕ`-rootable whenever `Kˣ`
  is `ℕ`-rootable.

## Main results

* `TauCeti.puiseuxField.coeff_pow_charP`: in characteristic `p`,
  `(y ^ p).coeff (p * q) = (y.coeff q) ^ p`.
* `TauCeti.puiseuxField.mul_mem_support_pow_charP_iff`: in positive characteristic `p`, `p * q`
  lies in the support of `y ^ p` if and only if `q` lies in the support of `y`.
* `TauCeti.puiseuxField.mul_mem_range_levelEmbedding_of_pow_eq`: tame rescaling of a `d`-th root
  back into level `m`.
* `TauCeti.puiseuxField.mem_range_levelEmbedding_of_pow_mem_range`,
  `TauCeti.puiseuxField.mem_range_levelEmbedding_of_pow_eq_algebraMap`: if `y ^ d` lies in level
  `m` (or `K⸨X⸩`), then `y` lies in level `m * d` (or level `d`).
* `TauCeti.puiseuxField.exists_pow_eq`: over a field `K` with `[RootableBy Kˣ ℕ]`, every Puiseux
  series has a `d`-th root in `puiseuxField K`.
* `TauCeti.puiseuxField.nonempty_rootableBy_units_nat_iff`: `(puiseuxField K)ˣ` is `ℕ`-rootable if
  and only if `Kˣ` is `ℕ`-rootable.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K]

private theorem coe_ne_zero {x : puiseuxField K} (hx : x ≠ 0) :
    (x : HahnSeries ℚ K) ≠ 0 :=
  ZeroMemClass.coe_eq_zero.not.mpr hx

/-- In characteristic `p`, raising a Puiseux series `y` to the `p`-th power moves its `q`-th
coefficient (raised to the `p`-th power) to exponent `p * q`. -/
theorem coeff_pow_charP (p : ℕ) [CharP K p] (y : puiseuxField K) (q : ℚ) :
    ((y ^ p : puiseuxField K) : HahnSeries ℚ K).coeff ((p : ℚ) * q) =
      ((y : HahnSeries ℚ K).coeff q) ^ p := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  let d : ℕ+ := ⟨p, Nat.pos_of_ne_zero hp0⟩
  have hp_prime : Nat.Prime d := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  have hexp : ExpChar K d := .prime hp_prime
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding y
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hn
  have hd_eq : (d : ℕ) = p := rfl
  rw [← hd_eq, ← map_pow, ← mapRingHom_frobenius_expand d g, coe_levelEmbedding,
    coe_levelEmbedding]
  by_cases hq : q.den ∣ n
  · obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hq
    have hmul : (d : ℚ) * ((k : ℚ) / n) = (((d : ℤ) * k : ℤ) : ℚ) / n := by
      push_cast
      ring
    rw [hmul, coeff_ramifiedEmbedding_intCast_div, coeff_ramifiedEmbedding_intCast_div,
      coeff_mapRingHom, _root_.LaurentSeries.coeff_expand_mul, frobenius_def]
  · rw [coeff_ramifiedEmbedding_of_not_den_dvd n g hq, zero_pow d.ne_zero]
    by_cases hmq : ((d : ℚ) * q).den ∣ n
    · obtain ⟨m, hm⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mp hmq
      rw [hm, coeff_ramifiedEmbedding_intCast_div, coeff_mapRingHom]
      have hndvd : ¬ ((d : ℤ) ∣ m) := by
        rintro ⟨k, rfl⟩
        apply hq
        refine (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mpr ⟨k, ?_⟩
        have hd_ne : (d : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
        apply mul_left_cancel₀ hd_ne
        rw [hm]
        push_cast
        ring
      rw [_root_.LaurentSeries.coeff_expand_of_not_dvd d g hndvd, map_zero]
    · exact coeff_ramifiedEmbedding_of_not_den_dvd n _ hmq

/-- In positive characteristic `p`, an exponent `p * q` lies in the support of `y ^ p` if and only
if `q` lies in the support of `y`. -/
theorem mul_mem_support_pow_charP_iff {p : ℕ} [CharP K p] (hp : p ≠ 0)
    (y : puiseuxField K) (q : ℚ) :
    (p : ℚ) * q ∈ ((y ^ p : puiseuxField K) : HahnSeries ℚ K).support ↔
      q ∈ (y : HahnSeries ℚ K).support := by
  rw [mem_support, mem_support, coeff_pow_charP p y q, pow_ne_zero_iff hp]

/-- If `z ^ d` is the level-`m` embedding of a unit power series `u`, then `z` has order `0` and
the `d`-th power of its constant term is `constantCoeff u`. -/
private theorem coeff_zero_pow_eq_constantCoeff_of_pow_eq_levelEmbedding {m d : ℕ+}
    {z : puiseuxField K} {u : K⟦X⟧} (hu : IsUnit u)
    (hzd : z ^ (d : ℕ) = levelEmbedding K m (u : K⸨X⸩)) :
    (z : HahnSeries ℚ K).coeff 0 ≠ 0 ∧
      PowerSeries.constantCoeff u = ((z : HahnSeries ℚ K).coeff 0) ^ (d : ℕ) := by
  have hz0 : z ≠ 0 := fun h0 ↦
    hu.ne_zero (ofPowerSeries_injective ((levelEmbedding K m).toRingHom.injective
      (by simpa [h0, zero_pow d.ne_zero] using hzd.symm)))
  have hz_ord : (z : HahnSeries ℚ K).order = 0 := by
    have hzd_ord : ((z ^ (d : ℕ) : puiseuxField K) : HahnSeries ℚ K).order = 0 := by
      rw [hzd, coe_levelEmbedding, order_ramifiedEmbedding, PowerSeries.order_coe,
        PowerSeries.order_zero_of_isUnit hu, ENat.toNat_zero, Nat.cast_zero, Int.cast_zero,
        zero_div]
    rw [IntermediateField.coe_pow, HahnSeries.order_pow, nsmul_eq_mul] at hzd_ord
    exact (mul_eq_zero.mp hzd_ord).resolve_left (by exact_mod_cast d.ne_zero)
  have hc0 : (z : HahnSeries ℚ K).coeff 0 ≠ 0 := by
    rw [← hz_ord, ← leadingCoeff_eq]
    exact leadingCoeff_ne_zero.mpr (coe_ne_zero hz0)
  refine ⟨hc0, ?_⟩
  have hlhs : ((z ^ (d : ℕ) : puiseuxField K) : HahnSeries ℚ K).leadingCoeff =
      PowerSeries.constantCoeff u := by
    rw [hzd, coe_levelEmbedding, leadingCoeff_eq, order_ramifiedEmbedding, PowerSeries.order_coe,
      PowerSeries.order_zero_of_isUnit hu, ENat.toNat_zero, Nat.cast_zero,
      coeff_ramifiedEmbedding_intCast_div]
    simp [PowerSeries.coeff_coe]
  rw [← hlhs, IntermediateField.coe_pow, HahnSeries.leadingCoeff_pow, leadingCoeff_eq, hz_ord]

/-- When `(d : K) ≠ 0`, if `y ^ d = levelEmbedding K m f`, then rescaling `y` by
`levelEmbedding K (m * d) (single (-f.order) 1)` places it in the unramified level `m`. -/
theorem mul_mem_range_levelEmbedding_of_pow_eq {m d : ℕ+} (hd : ((d : ℕ) : K) ≠ 0)
    {y : puiseuxField K} {f : K⸨X⸩} (hf : y ^ (d : ℕ) = levelEmbedding K m f) :
    levelEmbedding K (m * d) (HahnSeries.single (-f.order) 1) * y ∈
      (levelEmbedding K m).range := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have hy0 : y = 0 := (pow_eq_zero_iff d.ne_zero).mp (by simpa using hf)
    simp [hy0]
  set s : puiseuxField K := levelEmbedding K (m * d) (HahnSeries.single (-f.order) 1)
  set z : puiseuxField K := s * y
  have hzd : z ^ (d : ℕ) = levelEmbedding K m (f.powerSeriesPart : K⸨X⸩) := by
    rw [mul_pow, ← map_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, hf]
    have hexp : levelEmbedding K (m * d) (HahnSeries.single ((d : ℤ) * -f.order) 1) =
        levelEmbedding K m (HahnSeries.single (-f.order) 1) := by
      rw [← levelEmbedding_expand m d, expand_single]
    rw [hexp, ← map_mul]
    congr 1
    nth_rw 2 [← single_order_mul_powerSeriesPart f]
    rw [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
      ← HahnSeries.C_apply, map_one, one_mul]
  obtain ⟨hc0, hc_pow⟩ := coeff_zero_pow_eq_constantCoeff_of_pow_eq_levelEmbedding
    (TauCeti.LaurentSeries.isUnit_powerSeriesPart hf0) hzd
  obtain ⟨v, hv, -⟩ := PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow hd hc0 hc_pow
  set z₀ : puiseuxField K := levelEmbedding K m (v : K⸨X⸩)
  have hz₀_pow : z₀ ^ (d : ℕ) = z ^ (d : ℕ) := by
    rw [hzd, ← map_pow, ← PowerSeries.coe_pow, hv]
  obtain ⟨ζ, hζ⟩ := (TauCeti.pow_eq_pow_iff_exists_rootsOfUnity_smul d.ne_zero).mp hz₀_pow
  have : NeZero (d : ℕ) := ⟨d.ne_zero⟩
  let η : rootsOfUnity (d : ℕ) K := (TauCeti.rootsOfUnityMulEquiv K (puiseuxField K) d).symm ζ
  refine (AlgHom.mem_range _).mpr ⟨algebraMap K K⸨X⸩ ((η : Kˣ) : K) * (v : K⸨X⸩), ?_⟩
  rw [map_mul, AlgHom.commutes, TauCeti.algebraMap_rootsOfUnityMulEquiv_symm_apply,
    ← rootsOfUnity.smul_eq_mul, hζ]

/-- **Level membership of roots**: over any field `K`, if `y ^ d` lies in the level-`m` subfield
of `puiseuxField K`, then `y` lies in the level-`(m * d)` subfield. -/
theorem mem_range_levelEmbedding_of_pow_mem_range {m d : ℕ+} {y : puiseuxField K}
    (hy : y ^ (d : ℕ) ∈ (levelEmbedding K m).range) :
    y ∈ (levelEmbedding K (m * d)).range := by
  induction hd : (d : ℕ) using Nat.strong_induction_on generalizing m d y with
  | ind n ih =>
    subst hd
    by_cases hd1 : d = 1
    · subst hd1
      simpa using hy
    · obtain ⟨p, hp, hpd⟩ := PNat.exists_prime_and_dvd hd1
      let k := d.divExact p
      have hdk : k * p = d := by rw [mul_comm, PNat.mul_div_exact hpd]
      have hk_lt : (k : ℕ) < d := by
        have hp1 : 1 < (p : ℕ) := hp.one_lt
        have hk0 : 0 < (k : ℕ) := k.pos
        have : (k : ℕ) * p = d := congrArg PNat.val hdk
        nlinarith
      have hyp : (y ^ (p : ℕ)) ^ (k : ℕ) ∈ (levelEmbedding K m).range := by
        rwa [← pow_mul, mul_comm (p : ℕ), ← PNat.mul_coe, hdk]
      have hyp_mem : y ^ (p : ℕ) ∈ (levelEmbedding K (m * k)).range :=
        ih k hk_lt hyp rfl
      have hy_mem : y ∈ (levelEmbedding K (m * k * p)).range := by
        by_cases hp0 : ((p : ℕ) : K) = 0
        · have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
          rw [mem_range_levelEmbedding_iff, mem_range_ramifiedEmbedding_iff] at hyp_mem ⊢
          intro q hq
          obtain ⟨j, hj⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div (m * k).ne_zero).mp
            (hyp_mem _ ((mul_mem_support_pow_charP_iff p.ne_zero y q).mpr hq))
          refine (Rat.den_dvd_iff_exists_eq_intCast_div (m * k * p).ne_zero).mpr ⟨j, ?_⟩
          have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast p.ne_zero
          apply mul_left_cancel₀ hp_ne
          rw [hj]; simp only [PNat.mul_coe, Nat.cast_mul]; field_simp
        · obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hyp_mem
          set s : puiseuxField K := levelEmbedding K (m * k * p) (HahnSeries.single (-f.order) 1)
          have hs0 : s ≠ 0 := by simp [s]
          have hy_eq : y = s⁻¹ * (s * y) := by rw [inv_mul_cancel_left₀ hs0]
          rw [hy_eq]
          refine Subalgebra.mul_mem _ ((AlgHom.mem_range _).mpr ⟨HahnSeries.single f.order 1, ?_⟩)
            (range_levelEmbedding_le_of_dvd (dvd_mul_right (m * k) p)
              (mul_mem_range_levelEmbedding_of_pow_eq hp0 hf.symm))
          rw [← map_inv₀ (levelEmbedding K (m * k * p)), HahnSeries.inv_single, inv_one, neg_neg]
      rwa [mul_assoc, hdk] at hy_mem

/-- If `y ^ d` lies in `K⸨X⸩` (level one), then `y` lies in level `d`. -/
theorem mem_range_levelEmbedding_of_pow_eq_algebraMap {d : ℕ+} {y : puiseuxField K} {f : K⸨X⸩}
    (hy : y ^ (d : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) f) :
    y ∈ (levelEmbedding K d).range := by
  have h1 : y ^ (d : ℕ) ∈ (levelEmbedding K 1).range :=
    (AlgHom.mem_range _).mpr ⟨f, (algebraMap_laurentSeries_apply f).symm.trans hy.symm⟩
  simpa using mem_range_levelEmbedding_of_pow_mem_range h1

/-- Over a field `K` with `ℕ`-rootable unit group, every Puiseux series has a `d`-th root in
`puiseuxField K`, in arbitrary characteristic. -/
theorem exists_pow_eq [RootableBy Kˣ ℕ] (d : ℕ+) (x : puiseuxField K) :
    ∃ y : puiseuxField K, y ^ (d : ℕ) = x := by
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  obtain ⟨g, hg⟩ := exists_pow_eq_expand d f
  exact ⟨levelEmbedding K (n * d) g, by rw [← map_pow, hg, levelEmbedding_expand]⟩

/-- When `Kˣ` is `ℕ`-rootable, the unit group `(puiseuxField K)ˣ` is `ℕ`-rootable. -/
noncomputable instance instRootableByUnitsNat [RootableBy Kˣ ℕ] :
    RootableBy (puiseuxField K)ˣ ℕ :=
  rootableByOfPowLeftSurj _ _ fun {n} hn u ↦ by
    let d : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
    obtain ⟨y, hy⟩ := exists_pow_eq d u.val
    have hy' : y ^ n = u.val := hy
    have hy0 : y ≠ 0 := fun h0 ↦ u.ne_zero (by rw [← hy', h0, zero_pow hn])
    exact ⟨Units.mk0 y hy0, Units.ext hy'⟩

/-- The unit group `(puiseuxField K)ˣ` is `ℕ`-rootable if and only if `Kˣ` is `ℕ`-rootable. -/
theorem nonempty_rootableBy_units_nat_iff :
    Nonempty (RootableBy (puiseuxField K)ˣ ℕ) ↔ Nonempty (RootableBy Kˣ ℕ) := by
  refine ⟨fun ⟨_⟩ ↦ ⟨rootableByOfPowLeftSurj _ _ fun {n} hn u ↦ ?_⟩,
    fun ⟨_⟩ ↦ ⟨inferInstance⟩⟩
  let u' : (puiseuxField K)ˣ := Units.map (algebraMap K (puiseuxField K)).toMonoidHom u
  obtain ⟨y, hy⟩ := RootableBy.surjective_pow (puiseuxField K)ˣ ℕ hn u'
  have hy_val : (y : puiseuxField K) ^ n = algebraMap K (puiseuxField K) u := by
    simpa [u'] using congrArg Units.val hy
  have hy_int : IsIntegral K (y : puiseuxField K) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hy_val ▸ isIntegral_algebraMap)
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hy_int
  have hc0 : c ≠ 0 := fun h0 ↦ y.ne_zero (by rw [← hc, h0, map_zero])
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact (algebraMap K (puiseuxField K)).injective (by rw [map_pow, hc, hy_val])

end TauCeti.puiseuxField
