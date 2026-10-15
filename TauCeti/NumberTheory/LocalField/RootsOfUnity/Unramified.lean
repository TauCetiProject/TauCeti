/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Basic

/-!
# Dyadic roots of unity in unramified extensions

An unramified extension of `ℚ₂` contains no primitive fourth root of unity. Indeed, if `ζ` were
primitive of order four, then `(ζ - 1)² = -2ζ`. Roots of unity have normalized valuation zero,
whereas unramifiedness makes the normalized valuation of `2` equal to one. Taking valuations in
the displayed identity would therefore express `1` as twice an integer.

Consequently the `2`-power roots of unity in every finite unramified extension of `ℚ₂` are just
`{1, -1}`. This is useful when a concrete unramified field is presented by a polynomial, since it
reduces the roots-of-unity computation to proving unramifiedness.

## Main result

* `TauCeti.localRootOfUnityOrder_two_of_isUnramified`: the group of `2`-power roots of unity in
  an unramified extension of `ℚ₂` has order two.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
-/

public section

open ValuativeRel

namespace TauCeti

/-- The `2`-power roots of unity in an unramified extension of `ℚ₂` have order two.

A primitive fourth root `ζ` would give `(ζ - 1)² = -2ζ`. The left-hand side has even normalized
valuation, while the right-hand side has valuation one because roots of unity have valuation zero
and the extension is unramified. -/
theorem localRootOfUnityOrder_two_of_isUnramified
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[2] L] [ValuativeExtension ℚ_[2] L]
    [IsUnramified ℚ_[2] L] (h2 : (2 : L) ≠ 0) :
    localRootOfUnityOrder 2 L (finite_pPowerRootsOfUnity h2) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hq
  obtain ⟨ζ, hζ⟩ := (localRootOfUnityOrder_ne_two_iff (K := L) h2).mp hq
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  let u : Lˣ := Units.mk0 ζ hζ0
  let d : Lˣ := Units.mk0 (ζ - 1) (sub_ne_zero.mpr hζ1)
  let t : Lˣ := Units.mk0 (2 : L) h2
  have hu_mem : u ∈ rootsOfUnity 4 L := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    simpa [u] using hζ.pow_eq_one
  have huval : normalizedValuation L u = 1 := by
    rw [normalizedValuation_eq_one_iff]
    exact (mem_unitFiltration_zero u).mp
      (rootsOfUnity_le_unitFiltration_zero L (by norm_num) hu_mem)
  have hmval : normalizedValuation L (-1 : Lˣ) = 1 := by
    rw [normalizedValuation_eq_one_iff]
    exact (mem_unitFiltration_zero (-1 : Lˣ)).mp
      (rootsOfUnity_le_unitFiltration_zero L (n := 2) (by norm_num) (by simp))
  have hζ2 : ζ ^ 2 = -1 := by
    apply (sq_eq_one_iff.mp ?_).resolve_left
    · exact fun h ↦ (by norm_num : ¬4 ∣ 2) ((hζ.pow_eq_one_iff_dvd 2).mp h)
    · rw [← pow_mul, show 2 * 2 = 4 by norm_num, hζ.pow_eq_one]
  have hd : d ^ 2 = (-1 : Lˣ) * t * u := by
    apply Units.ext
    -- Extensionality reduces the unit identity to the corresponding field identity.
    change (ζ - 1) ^ 2 = -1 * 2 * ζ
    linear_combination hζ2
  have htval : (normalizedValuation L t).toAdd = 1 := by
    dsimp only [t]
    calc
      _ = (natCastValuation L 2 h2 : ℤ) := toAdd_normalizedValuation_natCast L 2 h2
      _ = 1 := by
        norm_cast
        rw [natCastValuation_eq_ramificationIndex_mul (K := ℚ_[2]) 2 (by norm_num),
          IsUnramified.ramificationIndex_eq_one, Padic.natCastValuation_self, one_mul]
  have hv := congrArg (fun x : Lˣ ↦ (normalizedValuation L x).toAdd) hd
  simp only [map_pow, map_mul] at hv
  simp only [toAdd_pow, toAdd_mul] at hv
  rw [hmval, huval, htval, toAdd_one] at hv
  simp only [zero_add, add_zero, nsmul_eq_mul] at hv
  omega

end TauCeti
