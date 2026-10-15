/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Trace
public import TauCeti.NumberTheory.LocalField.Norm.Basic
import Mathlib.RingTheory.NormTrace

/-!
# The norm does not preserve the depth of units in a ramified extension

For a finite extension `L/K` of nonarchimedean local fields with ramification index
`e = e(L/K)`, the norm carries `U(L, e i)` into `U(K, i)`
(`TauCeti.map_normUnits_unitFiltration_le`), and for `L/K` Galois it carries `U(L, ψℕ_{L/K}(i))`
into `U(K, i)` (`TauCeti.map_normUnits_unitFiltration_psiNat_le`). This file shows that a shift
of the depth is genuinely needed: when `L/K` is separable and tamely ramified,

* the inclusion `N_{L/K}(U(L, e i)) ⊆ U(K, i)` is sharp at every positive depth `i`: the image
  of `U(L, e i)` is not contained in `U(K, i + 1)`;
* if moreover `L/K` is ramified, the unshifted inclusion `N_{L/K}(U(L, i)) ⊆ U(K, i)` fails at
  every depth `i ≥ 2`.

Tameness is exactly the condition that the trace maps `𝒪[L]` onto `𝒪[K]`
(`TauCeti.intTrace_surjective_iff_isTamelyRamified`), so there is an integer `u` of `L` of trace
`1`. For a uniformizer `π` of `K`, the unit `1 + π ^ i u` lies in `U(L, e i)`, and its norm is
`1 + π ^ i Tr(u) = 1 + π ^ i` modulo `π ^ (2 i)` (`Algebra.norm_one_add_smul`), which lies outside
`U(K, i + 1)`. For example, in a tamely ramified quadratic extension in odd residue characteristic,
some element of `U(L, 2)` has norm outside `U(K, 2)`.

Separability is assumed because the trace criterion for tameness is stated for separable
extensions. It is automatic in characteristic zero, and it holds whenever `[L : K]` is prime to the
residue characteristic.

## Main results

* `TauCeti.not_map_normUnits_unitFiltration_le_succ`: for `L/K` separable and tame,
  `N_{L/K}(U(L, e (i + 1))) ⊄ U(K, i + 2)`.
* `TauCeti.not_map_normUnits_unitFiltration_le_of_one_lt_ramificationIndex`: for `L/K`
  separable and tame with `e(L/K) > 1`, `N_{L/K}(U(L, i)) ⊄ U(K, i)` for every `i ≥ 2`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §§2–3 and §6.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable (K L) in
/-- **The ramification shift of the norm is sharp.** If `L/K` is separable and tamely ramified,
then for every `i` the norm does not carry `U(L, e(L/K) (i + 1))` into `U(K, i + 2)`. Thus the
inclusion `N_{L/K}(U(L, e(L/K) i)) ⊆ U(K, i)` of `map_normUnits_unitFiltration_le` cannot be
improved by one step at any positive depth. -/
theorem not_map_normUnits_unitFiltration_le_succ [Algebra.IsSeparable K L]
    (ht : IsTamelyRamified K L) (i : ℕ) :
    ¬ (unitFiltration L (ramificationIndex K L * (i + 1))).map (Algebra.normUnits K) ≤
      unitFiltration K (i + 2) := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  -- An integer of `L` of trace one, which exists because `L/K` is tame.
  obtain ⟨u, hu⟩ := (intTrace_surjective_iff_isTamelyRamified K L).mpr ht 1
  rw [Algebra.intTrace_eq_trace] at hu
  have hπm : π ∈ 𝓂[K] := hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  -- The witness `1 + π ^ (i + 1) u` lies in `U(L, e(L/K) (i + 1))`.
  have hx : π ^ (i + 1) • u ∈ 𝓂[L] ^ (ramificationIndex K L * (i + 1)) := by
    rw [pow_mul, ← map_maximalIdeal_eq_maximalIdeal_pow, ← Ideal.map_pow, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hπm _))
  have hz : IsUnit (1 + π ^ (i + 1) • u) := by
    simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem (Ideal.pow_le_self
      (Nat.mul_ne_zero (ramificationIndex_pos (K := K) (L := L)).ne' i.succ_ne_zero) hx))
  obtain ⟨v, hv, hvN⟩ := mem_unitFiltration_iff_exists.mp
    (h ⟨Units.map (Subring.subtype 𝒪[L]).toMonoidHom hz.unit,
      mem_unitFiltration_iff_exists.mpr ⟨hz.unit, by simpa using hx, rfl⟩, rfl⟩)
  -- Its norm is `1 + π ^ (i + 1)` modulo `π ^ (2 (i + 1))`, so it is not in `U(K, i + 2)`.
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (π ^ (i + 1)) u
  rw [hu, one_mul] at hr
  have hveq : (v : 𝒪[K]) = 1 + (π ^ (i + 1) + r * (π ^ (i + 1)) ^ 2) := by
    rw [← add_assoc, ← hr]
    exact Subtype.ext (by simpa [Algebra.coe_normUnits] using hvN)
  have hsq : r * (π ^ (i + 1)) ^ 2 ∈ 𝓂[K] ^ (i + 2) := by
    rw [← pow_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hπm _))
  rw [hveq, add_sub_cancel_left] at hv
  have := (Submodule.add_mem_iff_left _ hsq).mp hv
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at this
  omega

variable (K L) in
/-- **The unshifted norm inclusion fails in a ramified extension.** If `L/K` is separable, tamely
ramified and ramified, then for every depth `i ≥ 2` the norm does not carry `U(L, i)` into
`U(K, i)`. -/
theorem not_map_normUnits_unitFiltration_le_of_one_lt_ramificationIndex
    [Algebra.IsSeparable K L] (ht : IsTamelyRamified K L) (he : 1 < ramificationIndex K L)
    {i : ℕ} (hi : 2 ≤ i) :
    ¬ (unitFiltration L i).map (Algebra.normUnits K) ≤ unitFiltration K i := by
  -- With `k = ⌊(i - 1) / e⌋` we have `i ≤ e (k + 1)` and `k + 2 ≤ i`, because `e ≥ 2`.
  set e := ramificationIndex K L
  have he_pos : 0 < e := by omega
  have he_two : 2 ≤ e := he
  have h₁ : i ≤ e * ((i - 1) / e + 1) := by
    have := Nat.lt_mul_div_succ (i - 1) he_pos
    omega
  have h₂ : (i - 1) / e + 2 ≤ i := by
    have := Nat.div_le_div_left (a := i - 1) he_two two_pos
    omega
  intro h
  exact not_map_normUnits_unitFiltration_le_succ K L ht ((i - 1) / e)
    ((Subgroup.map_mono (unitFiltration_antitone h₁)).trans
      (h.trans (unitFiltration_antitone h₂)))

end TauCeti
