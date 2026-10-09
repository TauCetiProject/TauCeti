/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Herbrand
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
import TauCeti.NumberTheory.LocalField.UnitFiltration.Map
import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow

/-!
# The norm on the unit filtration without the Herbrand shift

For a finite Galois extension `L/K` of nonarchimedean local fields, the norm carries
`U(L, ψℕ_{L/K}(n))` into `U(K, n)` (`TauCeti.map_normUnits_unitFiltration_psiNat_le`). This file
records what the shifted inclusion says about an unshifted depth `i` of `L`, and why the shift
cannot be dropped.

* Since `ψℕ_{L/K}(⌊φ_{L/K}(i)⌋) ≤ i`, the norm carries `U(L, i)` into `U(K, ⌊φ_{L/K}(i)⌋)`.
* The naive inclusion `N_{L/K}(U(L, i)) ⊆ U(K, i)` fails for every ramified extension of degree
  prime to the residue characteristic `p`, at every depth `i ≥ 2`. The `[L : K]`-th power map
  carries `U(K, i - 1)` onto itself, so some `x ∈ U(K, i - 1)` has `x ^ [L : K] ∉ U(K, i)`. As
  `e(L/K) ≥ 2`, the image of `x` lies in `U(L, e(L/K) (i - 1)) ⊆ U(L, i)`, and its norm is
  `x ^ [L : K]`. For instance, in a tamely ramified quadratic extension in residue
  characteristic `3`, the norm of some element of `U(L, 2)` lies outside `U(K, 2)`. Conversely an
  unramified extension satisfies `N_{L/K}(U(L, i)) ⊆ U(K, i)` at every depth, so under these
  hypotheses the naive inclusion characterizes unramified extensions.

The bound `2 ≤ i` is sharp, since the naive inclusion holds at depth `1` for every finite
extension. The degree hypothesis cannot be dropped either. In the wildly ramified extension
`ℚ_2(√2)/ℚ_2`, `N(1 + 2y) = 1 + 2 Tr(y) + 4 N(y)` with `Tr(y) ∈ 2ℤ_2` for `y ∈ ℤ_2[√2]`, so the
norm carries `U(L, 2)` into `U(K, 2)`.

## Main results

* `TauCeti.map_normUnits_unitFiltration_le_floor_herbrand`:
  `N_{L/K}(U(L, i)) ⊆ U(K, ⌊φ_{L/K}(i)⌋)` for `L/K` finite Galois.
* `TauCeti.map_normUnits_unitFiltration_le_iff_isUnramified`: if `p ∤ [L : K]` and `2 ≤ i`, then
  `N_{L/K}(U(L, i)) ⊆ U(K, i)` exactly when `L/K` is unramified.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §6.
-/

public section

open ValuativeRel IsLocalRing Module TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

section Galois

variable [Module.Finite K L] [IsGalois K L]

variable (K L) in
/-- **The unshifted norm inclusion.** For a finite Galois extension `L/K` of nonarchimedean local
fields, the norm carries `U(L, i)` into `U(K, ⌊φ_{L/K}(i)⌋)`, because
`ψℕ_{L/K}(⌊φ_{L/K}(i)⌋) ≤ i`. -/
theorem map_normUnits_unitFiltration_le_floor_herbrand (i : ℕ) :
    (unitFiltration L i).map (Algebra.normUnits K) ≤
      unitFiltration K ⌊(herbrand K L ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ : ℝ)⌋₊ := by
  -- `φ(i) ≥ φ(0) = 0`, so the floor of `φ(i)` is at most `φ(i)`.
  have h0 : (0 : ℝ) ≤ herbrand K L ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ := by
    have h := (herbrand_strictMono K L).monotone
      (show (⟨(0 : ℕ), Nat.cast_mem_ramificationIndexDomain 0⟩ : RamificationIndexDomain) ≤
        ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ from
        Subtype.mk_le_mk.2 (Nat.cast_le.2 i.zero_le))
    rw [herbrand_of_coe_le_zero K L (by simp)] at h
    simpa using Subtype.coe_le_coe.2 h
  exact (Subgroup.map_mono (unitFiltration_antitone
    ((psiNat_le_iff K L).2 (Nat.floor_le h0)))).trans
    (map_normUnits_unitFiltration_psiNat_le K L _)

end Galois

/-- If `p ∤ n` and `i ≥ 1`, the `n`-th power of some unit of `U(K, i)` lies outside
`U(K, i + 1)`: the `n`-th power map carries `U(K, i)` onto itself, and `U(K, i)` is not contained
in `U(K, i + 1)`. -/
private theorem exists_mem_unitFiltration_pow_notMem {n : ℕ} (hn : ¬ ringChar 𝓀[K] ∣ n) {i : ℕ}
    (hi : 1 ≤ i) : ∃ x ∈ unitFiltration K i, x ^ n ∉ unitFiltration K (i + 1) := by
  have hnK : (n : K) ≠ 0 := natCast_ne_zero_of_isUnit (IsLocalRing.isUnit_natCast_iff_not_dvd.2 hn)
  have hv : natCastValuation K n hnK = 0 := (natCastValuation_eq_zero_iff_not_dvd K n hnK).2 hn
  have hsurj := map_powMonoidHom_unitFiltration hnK (i := i) fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_lt_of_dvd hnK (by rw [hv]; omega) hp hpK hpn
  rw [hv, add_zero] at hsurj
  obtain ⟨y, hy, hy'⟩ := IsConcreteLE.not_le_iff_exists.1
    ((unitFiltration_le_unitFiltration_iff (K := K) (i := i + 1) (j := i) (Or.inl (by omega))).not.2
      (by omega))
  rw [← hsurj] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, hy'⟩

/-- **The norm without the Herbrand shift characterizes unramified extensions.** Let `L/K` be an
extension of nonarchimedean local fields whose degree is prime to the residue characteristic `p`
of `K`. At every depth `i ≥ 2`, the norm carries `U(L, i)` into `U(K, i)` exactly when `L/K` is
unramified. For a ramified extension, a unit `x ∈ U(K, i - 1)` with `x ^ [L : K] ∉ U(K, i)` lies
in `U(L, e(L/K) (i - 1)) ⊆ U(L, i)` and has norm `x ^ [L : K]`. -/
theorem map_normUnits_unitFiltration_le_iff_isUnramified (hp : ¬ ringChar 𝓀[K] ∣ finrank K L)
    {i : ℕ} (hi : 2 ≤ i) :
    (unitFiltration L i).map (Algebra.normUnits K) ≤ unitFiltration K i ↔ IsUnramified K L := by
  refine ⟨fun h ↦ ?_, fun _ ↦ by
    simpa using map_normUnits_unitFiltration_le K L i⟩
  rw [isUnramified_iff_ramificationIndex_eq_one]
  by_contra he
  have he : 2 ≤ ramificationIndex K L := by
    have := ramificationIndex_pos (K := K) (L := L)
    omega
  obtain ⟨x, hx, hxn⟩ := exists_mem_unitFiltration_pow_notMem (K := K) hp (i := i - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hxn
  -- The image of `x` in `L` lies in `U(L, e (i - 1)) ⊆ U(L, i)`, and its norm is `x ^ [L : K]`.
  have hxL : Units.map (algebraMap K L : K →* L) x ∈ unitFiltration L i :=
    unitFiltration_antitone (by have := Nat.mul_le_mul_right (i - 1) he; omega)
      (unitsMap_algebraMap_mem_unitFiltration (L := L) hx)
  have hN : Algebra.normUnits K (Units.map (algebraMap K L : K →* L) x) = x ^ finrank K L :=
    Units.ext (by simp)
  exact hxn (hN ▸ h ⟨_, hxL, rfl⟩)

end TauCeti
