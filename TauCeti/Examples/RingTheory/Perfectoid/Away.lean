/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Perfectoid.Away
import TauCeti.RingTheory.Perfectoid.Padic
import TauCeti.RingTheory.Perfectoid.Pair
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for perfectoid Tate rings from integral perfectoid rings

These checks exercise `TauCeti.RingTheory.Perfectoid.Away` on `ℂ_p` regarded as `ℂ_p°[1/π]`, where
`π ∈ ℂ_p°` satisfies `π ^ p = p`:

* `algebraMap_mul_mem_range_of_isPowerBounded` recovers `π x ∈ ℂ_p°` for power-bounded `x ∈ ℂ_p`;
* `isUniform_of_dvd_of_pow_dvd_pow` and `isPerfectoidTateRing_of_bijective_frobeniusModPow` certify
  uniformity and perfectoidness of `ℂ_p` purely from its integral perfectoid subring `ℂ_p°`;
* `π⁻¹` satisfies the `n = 0` condition `π * π⁻¹ = 1 ∈ ℂ_p°` while failing power-boundedness,
  showing that the `n = 0` condition alone in
  `isPowerBounded_iff_forall_untilt_mul_mem_range` does not suffice.
-/

open Filter Ideal Topology TauCeti.Huber TauCeti.Perfectoid
open scoped nonZeroDivisors

namespace TauCeti.Examples.PerfectoidAway

variable (p : ℕ) [hp : Fact p.Prime]

-- On `ℂ_p = ℂ_p°[1/π]` with `π ^ p = p`, `Away.lean` yields `π A° ⊆ A₀`, `IsUniform ℂ_p`, and
-- `IsPerfectoidTateRing p ℂ_p`, while `π⁻¹` shows `π * x ∈ A₀` alone does not force `x ∈ A°`.
example :
    ∃ π : powerBoundedSubring ℂ_[p],
      π ^ p = (p : powerBoundedSubring ℂ_[p]) ∧
      IsLocalization.Away π ℂ_[p] ∧
      (∀ x : ℂ_[p], IsPowerBounded x →
        algebraMap (powerBoundedSubring ℂ_[p]) ℂ_[p] π * x ∈
          (algebraMap (powerBoundedSubring ℂ_[p]) ℂ_[p]).range) ∧
      IsUniform ℂ_[p] ∧
      IsPerfectoidTateRing p ℂ_[p] ∧
      ((π : ℂ_[p]) * (π : ℂ_[p])⁻¹ ∈ (algebraMap (powerBoundedSubring ℂ_[p]) ℂ_[p]).range ∧
        ¬IsPowerBounded ((π : ℂ_[p])⁻¹)) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (p : ℂ_[p]) hp.out.pos
  let π : powerBoundedSubring ℂ_[p] :=
    ⟨r, mem_powerBoundedSubring.mpr <| IsPowerBounded.of_pow hp.out.ne_zero <| by
      rw [hr]
      exact mem_powerBoundedSubring.mp (natCast_mem (powerBoundedSubring ℂ_[p]) p)⟩
  have hπ_pow : π ^ p = (p : powerBoundedSubring ℂ_[p]) := Subtype.ext hr
  have hr_ne : (π : ℂ_[p]) ≠ 0 := fun h0 ↦
    have hr0 : r = 0 := h0
    Nat.cast_ne_zero.mpr hp.out.ne_zero <| by
      rw [← hr, hr0, zero_pow hp.out.ne_zero]
  have hnorm_lt : ‖(π : ℂ_[p])‖ < 1 := by
    by_contra h
    push Not at h
    have hpow : 1 ≤ ‖r ^ p‖ := by simpa only [norm_pow] using one_le_pow₀ h
    rw [hr] at hpow
    exact not_lt_of_ge hpow (PadicComplex.norm_p_lt_one p)
  have hpu : IsPseudoUniformizer (π : ℂ_[p]) :=
    isPseudoUniformizer_iff_norm_lt_one.mpr ⟨hr_ne, hnorm_lt⟩
  have hloc : IsLocalization.Away π ℂ_[p] :=
    (powerBoundedSubring ℂ_[p]).isLocalizationAway_of_isOpen
      (isOpen_powerBoundedSubring ℂ_[p]) π hpu.isTopologicallyNilpotent hpu.isUnit
  have hbasis : (𝓝 (0 : ℂ_[p])).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (awayNhd π ℂ_[p] n : Set ℂ_[p]) := by
    let D : PairOfDefinition ℂ_[p] := PairOfDefinition.ofIsPseudoUniformizer
      (powerBoundedSubring ℂ_[p]) (isOpen_powerBoundedSubring ℂ_[p])
      (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]).isBounded hpu π.property
    refine (hpu.hasBasis_nhds_zero D).congr (fun _ ↦ Iff.rfl) fun n _ ↦ ?_
    ext x
    simp only [SetLike.mem_coe, mem_awayNhd, D,
      PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ ⟨⟨y, hy⟩, by
        rw [← hyx, map_mul, map_pow]; exact (smul_eq_mul _ _).symm⟩,
      fun ⟨a, hax⟩ ↦ ⟨(a : ℂ_[p]), a.property, by
        rw [← hax, map_mul, map_pow]; exact smul_eq_mul _ _⟩⟩
  have hreg : π ∈ (powerBoundedSubring ℂ_[p])⁰ :=
    mem_nonZeroDivisors_of_ne_zero fun h0 ↦ hr_ne (congrArg Subtype.val h0)
  have hroot : ∀ a : powerBoundedSubring ℂ_[p], π ^ p ∣ a ^ p → π ∣ a := by
    intro a ha
    rw [powerBoundedSubring.dvd_iff_norm_le] at ha ⊢
    rw [Subring.coe_pow, Subring.coe_pow, norm_pow, norm_pow] at ha
    by_contra! hlt
    exact not_lt_of_ge ha (pow_lt_pow_left₀ hlt (norm_nonneg _) hp.out.ne_zero)
  have hdvd : π ^ p ∣ (p : powerBoundedSubring ℂ_[p]) := ⟨1, by rw [mul_one, hπ_pow]⟩
  have : IsAdicComplete (span {π}) (powerBoundedSubring ℂ_[p]) :=
    (isRingOfIntegralElements_powerBoundedSubring ℂ_[p]).isAdicComplete_span_singleton π hpu
  have hbij : Function.Bijective (frobeniusModPow p hdvd) := by
    refine ⟨(frobeniusModPow_injective_iff hdvd).mpr hroot,
      (frobeniusModPow_surjective_iff hdvd).mpr fun a ↦ ?_⟩
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[p]) hp.out.pos
    have hb_pb : b ∈ powerBoundedSubring ℂ_[p] :=
      mem_powerBoundedSubring.mpr (IsPowerBounded.of_pow hp.out.ne_zero
        (hb.symm ▸ mem_powerBoundedSubring.mp a.property))
    refine ⟨⟨b, hb_pb⟩, ?_⟩
    have hsub : a - ⟨b, hb_pb⟩ ^ p = 0 := Subtype.ext (by simpa [sub_eq_zero] using hb.symm)
    rw [hsub]
    exact dvd_zero _
  refine ⟨π, hπ_pow, hloc,
    fun x hx ↦ algebraMap_mul_mem_range_of_isPowerBounded hbasis hp.out.one_lt hreg hroot hx,
    isUniform_of_dvd_of_pow_dvd_pow hbasis hp.out.one_lt hreg hroot,
    isPerfectoidTateRing_of_bijective_frobeniusModPow hbasis hreg hbij,
    ⟨⟨1, by simp [mul_inv_cancel₀ hr_ne]⟩, ?_⟩⟩
  rw [isPowerBounded_iff_norm_le_one, norm_inv, not_le]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hr_ne)).mpr hnorm_lt

end TauCeti.Examples.PerfectoidAway
