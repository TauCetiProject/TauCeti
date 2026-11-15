/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.UnitFiltration

/-!
# Uniformizer coordinates on the unit filtration of a discrete valuation ring

Let `S` be a discrete valuation ring with maximal ideal `𝔪` and residue field `k`. Fixing a
uniformizer `π` identifies each positive graded piece `U_{n+1} / U_{n+2}` of
`TauCeti.IsLocalRing.unitFiltration` with the additive group of `k`: the class of a principal unit
`u` with `(u : S) - 1 = y * π ^ (n + 1)` is sent to `residue S y`. Replacing `π` by `π' = π * a`
multiplies this coordinate by `(residue S a) ^ (n + 1)`.

Without any finiteness assumption on `k`, this additive identification determines the torsion of
the positive graded pieces: when `k` has characteristic `p`, every positive graded piece satisfies
`x ^ p = 1` and is therefore a `p`-group; when `k` has characteristic zero, every positive graded
piece is torsion-free.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField`:
  the additive isomorphism `Additive (UnitFiltrationGraded S (n + 1)) ≃+ ResidueField S`
  determined by a uniformizer `π`.

## Main results

* `TauCeti.IsDiscreteValuationRing.mem_unitFiltration_iff_le_addVal`: membership in `U_i` is the
  inequality `i ≤ addVal S ((u : S) - 1)`.
* `TauCeti.IsDiscreteValuationRing.mem_unitFiltration_iff_mul_irreducible_mem` and
  `TauCeti.IsDiscreteValuationRing.mem_unitFiltration_iff_irreducible_mul_mem`: membership in `U_i`
  read after multiplying `(u : S) - 1` by a uniformizer.
* `TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField_eq_residue` and
  `TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField_change`: explicit
  representative evaluation and change-of-uniformizer scaling.
* `TauCeti.IsDiscreteValuationRing.isPGroup_unitFiltrationGraded_succ`: for the residue
  characteristic `p`, every positive graded piece `U_{n+1} / U_{n+2}` is a `p`-group.
* `TauCeti.IsDiscreteValuationRing.eq_one_of_pow_eq_one_unitFiltrationGraded_succ_of_charZero`:
  in residue characteristic zero, every positive graded piece `U_{n+1} / U_{n+2}` is torsion-free.

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

/-- A unit `u` lies in `unitFiltration S i` if and only if `ϖ * ((u : S) - 1) ∈ 𝔪 ^ (i + 1)` for a
uniformizer `ϖ`. -/
theorem mem_unitFiltration_iff_irreducible_mul_mem {ϖ : S} (hϖ : Irreducible ϖ) {i : ℕ} {u : Sˣ} :
    u ∈ unitFiltration S i ↔ ϖ * ((u : S) - 1) ∈ maximalIdeal S ^ (i + 1) := by
  rw [mul_comm, mem_unitFiltration_iff_mul_irreducible_mem hϖ]

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
      Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, mem_unitFiltration_iff.mp u.2⟩ := by
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

/-- Replacing `π` by `π' = π * a` scales the positive-depth unit-filtration coordinate by the
residue of `a ^ (n + 1)`. -/
theorem unitFiltrationGradedSuccEquivResidueField_change (n : ℕ) (π π' : S)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded S (n + 1))) :
    unitFiltrationGradedSuccEquivResidueField n π hπ x =
      residue S (uniformizerChangeUnit π π' hπ hπ' : S) ^ (n + 1) *
        unitFiltrationGradedSuccEquivResidueField n π' hπ' x :=
  residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ' (n + 1) _

variable (S) in
/-- When the residue field has characteristic `p`, every element of a positive graded piece
`U_{n+1} / U_{n+2}` satisfies `x ^ p = 1`. -/
theorem unitFiltrationGraded_succ_pow_eq_one_of_charP (p : ℕ) [CharP (ResidueField S) p] (n : ℕ)
    (x : UnitFiltrationGraded S (n + 1)) :
    x ^ p = 1 := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  let e := unitFiltrationGradedSuccEquivResidueField n π hπ
  apply Additive.ofMul.injective
  apply e.injective
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofMul_one, map_zero]

variable (S) in
/-- For the residue characteristic `p`, every positive graded piece `U_{n+1} / U_{n+2}` of the
unit filtration is a `p`-group. No finiteness assumption on the residue field is needed. -/
theorem isPGroup_unitFiltrationGraded_succ (p : ℕ) [CharP (ResidueField S) p] (n : ℕ) :
    IsPGroup p (UnitFiltrationGraded S (n + 1)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  exact fun x ↦ ⟨1, by rw [pow_one, unitFiltrationGraded_succ_pow_eq_one_of_charP S p n x]⟩

/-- In residue characteristic zero, every positive graded piece `U_{n+1} / U_{n+2}` of the unit
filtration is torsion-free. -/
theorem eq_one_of_pow_eq_one_unitFiltrationGraded_succ_of_charZero [CharZero (ResidueField S)]
    {n k : ℕ} (hk : k ≠ 0) {x : UnitFiltrationGraded S (n + 1)} (hx : x ^ k = 1) :
    x = 1 := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  let e := unitFiltrationGradedSuccEquivResidueField n π hπ
  have he : (k : ResidueField S) * e (Additive.ofMul x) = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, ← ofMul_pow, hx, ofMul_one, map_zero]
  have hx0 : e (Additive.ofMul x) = 0 :=
    (mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr hk)
  exact Additive.ofMul.injective (e.injective (hx0.trans (map_zero e).symm))

end TauCeti.IsDiscreteValuationRing
