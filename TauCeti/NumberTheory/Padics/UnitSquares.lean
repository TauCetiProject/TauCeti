/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.SquareClasses

/-!
# Square classes of odd-prime `p`-adic units via the Legendre symbol

At an odd prime `p`, Hensel's lemma identifies the square classes of `p`-adic units `ℤ_[p]ˣ` with
the square classes of `(ℤ/pℤ)ˣ`, and hence with the Legendre symbol. An integer `t` congruent
modulo `p` to a unit `u ∈ ℤ_[p]ˣ` has `(t / p) = 1` if and only if `u` is a square in `ℤ_[p]ˣ`, and
two finite products of `p`-adic units agree modulo squares if and only if the products of the
Legendre symbols of any integer representatives modulo `p` agree.

The Hensel lifting uses `TauCeti.HenselianLocalRing.isSquare_iff_residue_isSquare` together with
`PadicInt.toZMod_eq_residueField_comp_residue` and Mathlib's `legendreSym.eq_one_iff`.

## Main results

* `PadicInt.isSquare_iff_legendreSym_eq_one`: for odd `p`, a unit `u ∈ ℤ_[p]ˣ` congruent to an
  integer `t` modulo `p` is a square if and only if `legendreSym p t = 1`.
* `PadicInt.isSquare_prod_mul_prod_iff_prod_legendreSym_eq`: for odd `p`, two finite products of
  units of `ℤ_[p]` agree modulo squares if and only if the products of the Legendre symbols of any
  integer representatives modulo `p` are equal.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3.3.
-/

public section

namespace PadicInt

/-- Over `ℤ_[p]` for an odd prime `p`, a unit `u` congruent to an integer `t` modulo `p` is a
square in `ℤ_[p]ˣ` if and only if `legendreSym p t = 1`. -/
theorem isSquare_iff_legendreSym_eq_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {u : ℤ_[p]ˣ} {t : ℤ} (ht : (p : ℤ_[p]) ∣ u - t) :
    IsSquare u ↔ legendreSym p t = 1 := by
  have htoZMod : toZMod (u : ℤ_[p]) = (t : ZMod p) := toZMod_eq_intCast_of_dvd ht
  have ht0 : (t : ZMod p) ≠ 0 := by
    rw [← htoZMod]
    exact (u.isUnit.map toZMod).ne_zero
  have hres : IsSquare (IsLocalRing.residue ℤ_[p] (u : ℤ_[p])) ↔
      IsSquare (toZMod (u : ℤ_[p])) := by
    simp only [toZMod_eq_residueField_comp_residue, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact ⟨fun h ↦ h.map residueField, fun h ↦ by simpa using h.map residueField.symm⟩
  rw [← Units.isSquare_coe_iff,
    TauCeti.HenselianLocalRing.isSquare_iff_residue_isSquare (isUnit_two hp) u.isUnit,
    hres, htoZMod, ← legendreSym.eq_one_iff p ht0]

/-- Over `ℤ_[p]` for an odd prime `p`, two finite products of units agree modulo squares if and
only if the Legendre symbols of any integer representatives modulo `p` have equal products. -/
theorem isSquare_prod_mul_prod_iff_prod_legendreSym_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {α β : Type*} [Fintype α] [Fintype β] (u : α → ℤ_[p]ˣ) (v : β → ℤ_[p]ˣ)
    {θ : α → ℤ} {η : β → ℤ} (hθ : ∀ i, (p : ℤ_[p]) ∣ u i - θ i)
    (hη : ∀ j, (p : ℤ_[p]) ∣ v j - η j) :
    IsSquare ((∏ i, u i) * ∏ j, v j) ↔
      ∏ i, legendreSym p (θ i) = ∏ j, legendreSym p (η j) := by
  set U : ℤ_[p]ˣ := (∏ i, u i) * ∏ j, v j
  set Θ : ℤ := (∏ i, θ i) * ∏ j, η j with hΘ
  have hUΘ : (p : ℤ_[p]) ∣ U - Θ := by
    rw [← toZMod_eq_iff_dvd_sub, map_intCast]
    simp only [U, hΘ]
    push_cast
    rw [map_mul, map_prod, map_prod]
    congr 1
    · exact Finset.prod_congr rfl fun i _ ↦ (toZMod_eq_intCast_of_dvd (hθ i)).symm
    · exact Finset.prod_congr rfl fun j _ ↦ (toZMod_eq_intCast_of_dvd (hη j)).symm
  rw [isSquare_iff_legendreSym_eq_one hp hUΘ, hΘ, ← legendreSym.hom_apply p]
  simp only [map_mul, map_prod, legendreSym.hom_apply]
  have hηsq : (∏ j, legendreSym p (η j)) * ∏ j, legendreSym p (η j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ ↦ ?_
    simpa only [pow_two] using legendreSym.sq_one p
      ((ZMod.isUnit_intCast_iff_isCoprime (η j) p).mpr (isCoprime_of_dvd_unit_sub (hη j))).ne_zero
  constructor
  · intro h
    calc ∏ i, legendreSym p (θ i)
        = (∏ i, legendreSym p (θ i)) * ((∏ j, legendreSym p (η j)) * ∏ j, legendreSym p (η j)) := by
          rw [hηsq, mul_one]
      _ = ∏ j, legendreSym p (η j) := by rw [← mul_assoc, h, one_mul]
  · intro h
    rw [h, hηsq]

end PadicInt
