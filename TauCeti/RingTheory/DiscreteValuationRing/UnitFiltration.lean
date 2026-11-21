/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.UnitFiltration

/-!
# Uniformizer coordinates on the unit filtration of a discrete valuation ring

Let `S` be a discrete valuation ring with maximal ideal `𝔪` and residue field `k`. Fixing a
uniformizer `π` identifies each positive graded piece `U_{n+1} / U_{n+2}` of
`TauCeti.IsLocalRing.unitFiltration` with the additive group of `k`: the class of a principal unit
`u` with `(u : S) - 1 = y * π ^ (n + 1)` is sent to `residue S y`. If `π' = π * a` for a unit `a`,
the coordinate relative to `π` equals `(residue S a) ^ (n + 1)` times the coordinate relative to
`π'` (equivalently, replacing `π` by `π'` divides the coordinate by `(residue S a) ^ (n + 1)`).

## Main definitions

* `TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField`:
  the additive isomorphism `Additive (UnitFiltrationGraded S (n + 1)) ≃+ ResidueField S`
  determined by a uniformizer `π`.

## Main results

* `TauCeti.IsDiscreteValuationRing.mem_unitFiltration_iff_le_addVal`: membership in `U_i` is the
  inequality `i ≤ addVal S ((u : S) - 1)`.
* `TauCeti.IsDiscreteValuationRing.mem_unitFiltration_iff_mul_irreducible_mem`: membership in
  `U_i` read after multiplying `(u : S) - 1` by a uniformizer.
* `TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField_eq_residue` and
  `TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField_change`: explicit
  representative evaluation and change-of-uniformizer scaling.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

variable {S : Type*} [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S]

/-- Membership in `unitFiltration S i` is the additive-valuation inequality
`i ≤ addVal S ((u : S) - 1)`. -/
theorem mem_unitFiltration_iff_le_addVal {i : ℕ} {u : Sˣ} :
    u ∈ unitFiltration S i ↔ (i : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal S ((u : S) - 1) := by
  rw [mem_unitFiltration_iff, mem_maximalIdeal_pow_iff_le_addVal]

/-- A unit `u` lies in `unitFiltration S i` if and only if `((u : S) - 1) * ϖ ∈ 𝔪 ^ (i + 1)` for a
uniformizer `ϖ`. -/
theorem mem_unitFiltration_iff_mul_irreducible_mem {ϖ : S} (hϖ : Irreducible ϖ) {i : ℕ} {u : Sˣ} :
    u ∈ unitFiltration S i ↔ ((u : S) - 1) * ϖ ∈ maximalIdeal S ^ (i + 1) := by
  rw [mem_unitFiltration_iff, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ,
    mul_dvd_mul_iff_right hϖ.ne_zero]

/-- Fixing a uniformizer `π` identifies the `n`-th positive graded piece `U_{n+1} / U_{n+2}` of
the unit filtration with the additive residue field, sending the class of `u` with
`(u : S) - 1 = y * π ^ (n + 1)` to `residue S y`. -/
noncomputable def unitFiltrationGradedSuccEquivResidueField (n : ℕ) (π : S)
    (hπ : Irreducible π) :
    Additive (UnitFiltrationGraded S (n + 1)) ≃+ ResidueField S :=
  (unitFiltrationGradedSuccEquivMaximalIdealGraded S n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative _).trans <|
      (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).symm.toAddEquiv

/-- Multiplying the uniformizer coordinate of `u` by `π ^ (n + 1)` recovers the class of
`(u : S) - 1` in `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueField_ofMul_mk (n : ℕ) (π : S)
    (hπ : Irreducible π) (u : unitFiltration S (n + 1)) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (unitFiltrationGradedSuccEquivResidueField n π hπ
          (Additive.ofMul (QuotientGroup.mk u))) =
      Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, mem_unitFiltration_iff.mp u.property⟩ := by
  rw [unitFiltrationGradedSuccEquivResidueField]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    unitFiltrationGradedSuccEquivMaximalIdealGraded_mk]
  exact LinearEquiv.apply_symm_apply _ _

/-- If `(u : S) - 1 = y * π ^ (n + 1)`, then the uniformizer coordinate of the class of `u` in
`U_{n+1} / U_{n+2}` is `residue S y`. -/
theorem unitFiltrationGradedSuccEquivResidueField_eq_residue (n : ℕ) (π : S)
    (hπ : Irreducible π) (u : unitFiltration S (n + 1)) (y : S)
    (hy : ((u : Sˣ) : S) - 1 = y * π ^ (n + 1)) :
    unitFiltrationGradedSuccEquivResidueField n π hπ
        (Additive.ofMul (QuotientGroup.mk u)) =
      residue S y := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).injective
  rw [unitFiltrationGradedSuccEquivResidueField_ofMul_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hy)

/-- If `π' = π * a`, the positive-depth unit-filtration coordinate relative to `π` equals
`(residue S a) ^ (n + 1)` times the coordinate relative to `π'` (equivalently, replacing `π` by
`π'` divides the coordinate by `(residue S a) ^ (n + 1)`). -/
theorem unitFiltrationGradedSuccEquivResidueField_change (n : ℕ) (π π' : S)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded S (n + 1))) :
    unitFiltrationGradedSuccEquivResidueField n π hπ x =
      residue S (uniformizerChangeUnit π π' hπ hπ' : S) ^ (n + 1) *
        unitFiltrationGradedSuccEquivResidueField n π' hπ' x :=
  residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ' (n + 1) _

end TauCeti.IsDiscreteValuationRing
