/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.RankOne

/-!
# Continuous automorphisms of the `p`-adic integers

Every continuous automorphism of the additive group of `ℤ_[p]` is multiplication by a unique unit
of `ℤ_[p]`, namely its value at `1`. This file records the resulting topological group
isomorphism `ContinuousAut (Multiplicative ℤ_[p]) ≃ₜ* ℤ_[p]ˣ`, for the congruence topology on
`ContinuousAut`, together with its explicit formulas: an automorphism goes to its value at `1`,
and a unit `u` goes to the automorphism `x ↦ u * x`.

The additive group of `ℤ_[p]` is the free pro-`p` group on one generator, with generator `1`
(`TauCeti.freeProP.equivPadicInt`), so the isomorphism is the case `F = Multiplicative ℤ_[p]` of
`TauCeti.Peripheral.continuousAutEquivUnits`, the identification of the continuous automorphism
group of a free pro-`p` group of rank one with `ℤ_[p]ˣ`. It is the `p`-adic counterpart of
`TauCeti.zHat.continuousAutEquivUnits` for the profinite integers.

## Main definitions

* `TauCeti.PadicInt.continuousAutEquivUnits`: the topological group isomorphism
  `ContinuousAut (Multiplicative ℤ_[p]) ≃ₜ* ℤ_[p]ˣ`.

## Main results

* `TauCeti.PadicInt.continuousAutEquivUnits_eq_iff`,
  `TauCeti.PadicInt.coe_continuousAutEquivUnits_apply`: an automorphism goes to its value at `1`.
* `TauCeti.PadicInt.continuousAutEquivUnits_symm_apply`: a unit `u` goes to multiplication
  by `u`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Sections 4.3 and 4.4.
-/

public section

namespace TauCeti

namespace PadicInt

open Multiplicative

variable {p : ℕ} [Fact p.Prime]

/-- **Continuous automorphisms of `ℤ_p`.** The topological group isomorphism from the continuous
automorphisms of the additive group of `ℤ_[p]`, with the congruence topology, to the units of
`ℤ_[p]`, sending an automorphism to its value at `1`
(`TauCeti.PadicInt.coe_continuousAutEquivUnits_apply`). Its inverse sends a unit `u` to
multiplication by `u` (`TauCeti.PadicInt.continuousAutEquivUnits_symm_apply`). -/
noncomputable def continuousAutEquivUnits : ContinuousAut (Multiplicative ℤ_[p]) ≃ₜ* ℤ_[p]ˣ :=
  Peripheral.continuousAutEquivUnits (isProP_multiplicative_padicInt p)
    (freeProP.equivPadicInt p (Fin 1)).symm

/-- A continuous automorphism of `ℤ_[p]` goes to the unit `u` exactly when it sends `1` to `u`. -/
theorem continuousAutEquivUnits_eq_iff (φ : ContinuousAut (Multiplicative ℤ_[p])) (u : ℤ_[p]ˣ) :
    continuousAutEquivUnits φ = u ↔ φ (ofAdd 1) = ofAdd (u : ℤ_[p]) := by
  have hbasis : Peripheral.basis (freeProP.equivPadicInt p (Fin 1)).symm 0 = ofAdd 1 := by
    simp [Peripheral.basis_apply]
  have h := Peripheral.continuousAutEquivUnits_eq_iff (isProP_multiplicative_padicInt p)
    (freeProP.equivPadicInt p (Fin 1)).symm φ u
  rwa [hbasis, IsProP.padicPow_ofAdd_one_padicInt] at h

/-- The unit attached to a continuous automorphism of `ℤ_[p]` is its value at `1`. -/
@[simp]
theorem coe_continuousAutEquivUnits_apply (φ : ContinuousAut (Multiplicative ℤ_[p])) :
    (continuousAutEquivUnits φ : ℤ_[p]) = (φ (ofAdd 1)).toAdd := by
  rw [(continuousAutEquivUnits_eq_iff φ _).mp rfl, toAdd_ofAdd]

/-- The continuous automorphism of `ℤ_[p]` attached to a unit `u` is multiplication by `u`. -/
@[simp]
theorem continuousAutEquivUnits_symm_apply (u : ℤ_[p]ˣ) (x : Multiplicative ℤ_[p]) :
    continuousAutEquivUnits.symm u x = ofAdd ((u : ℤ_[p]) * x.toAdd) := by
  have hu := coe_continuousAutEquivUnits_apply (continuousAutEquivUnits.symm u)
  rw [ContinuousMulEquiv.apply_symm_apply] at hu
  have h := toAdd_apply_multiplicative_padicInt
    (continuousAutEquivUnits.symm u : Multiplicative ℤ_[p] →ₜ* Multiplicative ℤ_[p]) x
  rw [ContinuousMonoidHom.coe_coe, ← hu] at h
  rw [← h, ofAdd_toAdd]

end PadicInt

end TauCeti
