/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm
public import TauCeti.Topology.Algebra.Group.Torsion

/-!
# The p-adic units modulo torsion

The logarithmic unit decomposition identifies the quotient of `ℤ_[p]ˣ` by its full torsion
subgroup with `Multiplicative ℤ_[p]`, with its quotient topology. The class of
`padicUnitsGenerator p` has coordinate `1`. This supplies a coordinate in which multiplication
by the chosen generator becomes translation by `+1`, as used in continuous difference equations.

The finite factor is the image of `padicUnitsSection p`: the `(p - 1)`-st roots of unity for
odd primes, but `{±1}` at `2`. In particular the dyadic quotient removes the sign factor,
not merely the trivial group of first roots of unity.

We use the logarithmic splitting `padicIntUnitsEquivZModUnitsProd` and the general topological
torsion-quotient construction `quotientTorsionContinuousMulEquiv`.

## References

* J.-P. Serre, *Corps Locaux*, Chapter II, §4.
* Douglas–Francis–Henriques–Hill (eds.), *Topological Modular Forms*, Chapter 6.
-/

public section

namespace TauCeti

open Multiplicative Additive CommGroup

variable (p : ℕ) [Fact p.Prime]

/-- Reorder and retag the existing unit decomposition for the torsion-quotient API. -/
private noncomputable def unitsTorsionDecomposition :
    ℤ_[p]ˣ ≃ₜ* Multiplicative (ℤ_[p] × Additive (ZMod (p ^ padicUnitsDepth p))ˣ) where
  toFun u := ofAdd ((padicIntUnitsEquivZModUnitsProd p u).2.toAdd,
    Additive.ofMul (padicIntUnitsEquivZModUnitsProd p u).1)
  invFun x := (padicIntUnitsEquivZModUnitsProd p).symm (x.toAdd.2.toMul, ofAdd x.toAdd.1)
  left_inv u := by
    simpa only [toAdd_ofAdd, toMul_ofMul, ofAdd_toAdd, Prod.mk.eta] using
      (padicIntUnitsEquivZModUnitsProd p).symm_apply_apply u
  right_inv x := by
    simp only [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd, ofMul_toMul,
      ofAdd_toAdd, Prod.mk.eta]
  map_mul' u v := by
    rw [map_mul]
    rfl
  continuous_toFun := continuous_ofAdd.comp
    ((continuous_toAdd.comp ((padicIntUnitsEquivZModUnitsProd p).continuous.snd)).prodMk
      (continuous_ofMul.comp ((padicIntUnitsEquivZModUnitsProd p).continuous.fst)))
  continuous_invFun := (padicIntUnitsEquivZModUnitsProd p).symm.continuous.comp
    ((continuous_toMul.comp (continuous_snd.comp continuous_toAdd)).prodMk
      (continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)))

/-- A p-adic unit has finite order exactly when its logarithmic coordinate vanishes. -/
theorem mem_torsion_padicIntUnits_iff (u : ℤ_[p]ˣ) :
    u ∈ torsion ℤ_[p]ˣ ↔ (padicIntUnitsEquivZModUnitsProd p u).2 = 1 := by
  exact (mem_torsion_iff_of_mulEquiv (x := u) isAddTorsion_of_finite
    (unitsTorsionDecomposition p).toMulEquiv).trans toAdd_eq_zero

/-- The full torsion subgroup is precisely the finite section of reduction modulo `p`, or
modulo `4` at the prime `2`. -/
theorem torsion_padicIntUnits_eq_range_section :
    torsion ℤ_[p]ˣ = (padicUnitsSection p).range := by
  ext u
  rw [mem_torsion_padicIntUnits_iff]
  constructor
  · intro h
    refine ⟨(padicIntUnitsEquivZModUnitsProd p u).1, ?_⟩
    have hu := (padicIntUnitsEquivZModUnitsProd p).symm_apply_apply u
    rw [padicIntUnitsEquivZModUnitsProd_symm_apply, h, map_one, OneMemClass.coe_one,
      mul_one] at hu
    exact hu
  · rintro ⟨δ, rfl⟩
    simp

/-- The topological logarithmic coordinate on the units modulo their full torsion subgroup. -/
noncomputable def padicIntUnitsQuotientTorsionEquiv :
    ℤ_[p]ˣ ⧸ torsion ℤ_[p]ˣ ≃ₜ* Multiplicative ℤ_[p] :=
  quotientTorsionContinuousMulEquiv isAddTorsion_of_finite (unitsTorsionDecomposition p)

/-- On the class of a unit, the quotient coordinate is the logarithmic component of its
finite-times-principal decomposition. -/
@[simp]
theorem padicIntUnitsQuotientTorsionEquiv_mk (u : ℤ_[p]ˣ) :
    padicIntUnitsQuotientTorsionEquiv p (QuotientGroup.mk u) =
      (padicIntUnitsEquivZModUnitsProd p u).2 := by
  rw [padicIntUnitsQuotientTorsionEquiv, quotientTorsionContinuousMulEquiv_mk]
  rfl

/-- The inverse coordinate is represented by the exponential principal unit. -/
@[simp]
theorem padicIntUnitsQuotientTorsionEquiv_symm_apply (s : Multiplicative ℤ_[p]) :
    (padicIntUnitsQuotientTorsionEquiv p).symm s =
      QuotientGroup.mk (((unitsPrincipalLogEquiv p).symm s :
        unitsPrincipal p (padicUnitsDepth p)) : ℤ_[p]ˣ) := by
  rw [padicIntUnitsQuotientTorsionEquiv, quotientTorsionContinuousMulEquiv_symm_apply]
  have h (x) : (unitsTorsionDecomposition p).symm x =
      (padicIntUnitsEquivZModUnitsProd p).symm (x.toAdd.2.toMul, ofAdd x.toAdd.1) := (rfl)
  rw [h, toAdd_ofAdd]
  simp only [toMul_zero, ofAdd_toAdd, padicIntUnitsEquivZModUnitsProd_symm_apply,
    map_one, one_mul]

/-- At an odd prime, the full torsion subgroup consists of the `(p - 1)`-st roots of unity. -/
theorem torsion_padicIntUnits_of_ne_two (hp : p ≠ 2) :
    torsion ℤ_[p]ˣ = rootsOfUnity (p - 1) ℤ_[p] := by
  ext u
  constructor
  · intro hu
    rw [torsion_padicIntUnits_eq_range_section] at hu
    obtain ⟨δ, rfl⟩ := hu
    rw [mem_rootsOfUnity]
    simpa [padicUnitsDepth_of_ne_two hp, Nat.totient_prime (Fact.out : p.Prime)] using
      padicUnitsSection_pow_totient (p := p) δ
  · intro hu
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p - 1, Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt, (mem_rootsOfUnity _ _).mp hu⟩

/-- At `2`, the full torsion subgroup is the sign subgroup `{±1}`. -/
theorem torsion_padicIntUnits_two : torsion ℤ_[2]ˣ = Subgroup.zpowers (-1) := by
  ext u
  constructor
  · intro hu
    rw [torsion_padicIntUnits_eq_range_section] at hu
    obtain ⟨δ, rfl⟩ := hu
    have h : padicUnitsSection 2 δ ^ 2 = 1 := by
      have ht : Nat.totient 4 = 2 := by decide
      simpa only [padicUnitsDepth_two, Nat.reducePow, ht] using
        padicUnitsSection_pow_totient (p := 2) δ
    rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one, sq_eq_one_iff] at h
    rcases h with h | h
    · have he : padicUnitsSection 2 δ = 1 := Units.ext h
      rw [he]
      exact Subgroup.one_mem _
    · have he : padicUnitsSection 2 δ = -1 := Units.ext h
      rw [he]
      exact Subgroup.mem_zpowers _
  · intro hu
    have hneg : (-1 : ℤ_[2]ˣ) ∈ torsion ℤ_[2]ˣ :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, by simp⟩
    exact (Subgroup.zpowers_le.mpr hneg) hu

end TauCeti
