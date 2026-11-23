/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
import TauCeti.RingTheory.Ideal.Operations

/-!
# Successive quotients of the principal unit filtration of a local ring

For a local ring `S` with maximal ideal `𝔪`, the subgroups `(𝔪 ^ i).principalUnitGroup` filter `Sˣ`:
at `i = 0` one recovers `Sˣ` itself (`Ideal.principalUnitGroup_top`), and at `i ≥ 1` one obtains
the congruence subgroups `1 + 𝔪 ^ i`. This file names the successive quotients of this filtration
and identifies them with residue-field data at depth `0` and with maximal-ideal graded pieces at
positive depth.

At depth `0`, reduction modulo `𝔪` identifies
`(𝔪 ^ 0).principalUnitGroup ⧸ (𝔪 ^ 1).principalUnitGroup` with `(ResidueField S)ˣ`. At depth
`n + 1`, `Ideal.principalUnitGroupPowQuotientEquiv` identifies
`(1 + 𝔪 ^ (n + 1)) ⧸ (1 + 𝔪 ^ (n + 2))` with the additive group `𝔪 ^ (n + 1) ⧸ 𝔪 • 𝔪 ^ (n + 1)`
via `u ↦ u - 1`. Over a discrete valuation ring, combining the positive-depth equivalence with a
choice of uniformizer identifies each positive graded piece with the additive residue field
(`TauCeti.principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer`).

The graded unit-filtration API here generalizes the nonarchimedean local-field development in
`TauCeti/NumberTheory/LocalField/UnitFiltration/Basic.lean` and
`TauCeti/NumberTheory/LocalField/UnitFiltration/Graded.lean` to an arbitrary commutative local ring.

## Main definitions

* `TauCeti.IsLocalRing.PrincipalUnitGroupGraded`: the `i`-th successive quotient of the filtration
  of `Sˣ` by `(maximalIdeal S ^ i).principalUnitGroup`.
* `TauCeti.IsLocalRing.principalUnitGroupGradedZeroEquivResidueFieldUnits`: the depth-`0`
  isomorphism `PrincipalUnitGroupGraded S 0 ≃* (ResidueField S)ˣ`.
* `TauCeti.IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded`: the positive-depth
  isomorphism `PrincipalUnitGroupGraded S (n + 1) ≃* Multiplicative (𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–6.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti

namespace IsLocalRing

variable (S : Type*) [CommRing S] [IsLocalRing S]

/-- The `i`-th successive quotient of the unit filtration `(maximalIdeal S ^ i).principalUnitGroup`
on a local ring `S`: `Sˣ ⧸ (1 + 𝔪)` at `i = 0`, and `(1 + 𝔪 ^ i) ⧸ (1 + 𝔪 ^ (i + 1))` for
`i ≥ 1`. -/
abbrev PrincipalUnitGroupGraded (i : ℕ) :=
  (maximalIdeal S ^ i).principalUnitGroup ⧸
    ((maximalIdeal S ^ (i + 1)).principalUnitGroup.subgroupOf
      (maximalIdeal S ^ i).principalUnitGroup)

/-- At depth `0`, the quotient `(𝔪 ^ 0).principalUnitGroup ⧸ (𝔪 ^ 1).principalUnitGroup` is
canonically isomorphic to `(ResidueField S)ˣ` via reduction modulo `𝔪` (compare
`Ideal.unitsQuotientPrincipalUnitGroupEquiv` on `Sˣ ⧸ (1 + 𝔪)`). -/
def principalUnitGroupGradedZeroEquivResidueFieldUnits :
    PrincipalUnitGroupGraded S 0 ≃* (ResidueField S)ˣ :=
  (QuotientGroup.congr _ (maximalIdeal S).principalUnitGroup
      ((MulEquiv.subgroupCongr (by simp)).trans Subgroup.topEquiv)
      (by ext; simp [Subgroup.mem_subgroupOf])).trans
    (Ideal.unitsQuotientPrincipalUnitGroupEquiv
      (jacobson_eq_maximalIdeal (R := S) ⊥ bot_ne_top).ge)

/-- Evaluating `principalUnitGroupGradedZeroEquivResidueFieldUnits` on the class of a unit reduces
that unit modulo the maximal ideal. -/
@[simp]
theorem principalUnitGroupGradedZeroEquivResidueFieldUnits_mk
    (u : (maximalIdeal S ^ 0).principalUnitGroup) :
    principalUnitGroupGradedZeroEquivResidueFieldUnits S (QuotientGroup.mk u) =
      Units.map (residue S).toMonoidHom (u : Sˣ) := by
  rw [principalUnitGroupGradedZeroEquivResidueFieldUnits]
  -- `ResidueField S` is a semireducible `def` for `S ⧸ maximalIdeal S` with its own derived
  -- `Field`/`CommRing` instance, so `rw [MulEquiv.trans_apply]` fails at `implicit` transparency
  -- on `Ideal.unitsQuotientPrincipalUnitGroupEquiv`; `change` exposes the composed equivalence
  -- across that defeq gap, and `rfl` bridges `(S ⧸ maximalIdeal S)ˣ` vs `(ResidueField S)ˣ`
  -- after reducing the `Subgroup.topEquiv`/`MulEquiv.subgroupCongr` wrappers and `residue`.
  change Ideal.unitsQuotientPrincipalUnitGroupEquiv _
      (QuotientGroup.congr _ _ _ _ (QuotientGroup.mk u)) = _
  rw [QuotientGroup.congr_mk, Ideal.unitsQuotientPrincipalUnitGroupEquiv_mk]
  simp only [MulEquiv.trans_apply, Subgroup.topEquiv_apply, MulEquiv.subgroupCongr_apply, residue]
  rfl

/-- At positive depth `n + 1`, the quotient `(1 + 𝔪 ^ (n + 1)) ⧸ (1 + 𝔪 ^ (n + 2))` is isomorphic
to the multiplicative form of the graded piece `𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤` via `u ↦ u - 1`. -/
def principalUnitGroupGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    PrincipalUnitGroupGraded S (n + 1) ≃*
      Multiplicative
        (↥(maximalIdeal S ^ (n + 1)) ⧸
          (maximalIdeal S • ⊤ : Submodule S ↥(maximalIdeal S ^ (n + 1)))) :=
  (Ideal.principalUnitGroupPowQuotientEquiv
      (jacobson_eq_maximalIdeal (R := S) ⊥ bot_ne_top).ge n).trans
    (Submodule.quotEquivOfEq _ _
      (pow_succ (maximalIdeal S) (n + 1) ▸
        ((maximalIdeal S ^ (n + 1)).smul_top_eq_comap_mul (maximalIdeal S)).symm)).toMultiplicative

/-- Evaluating `principalUnitGroupGradedSuccEquivMaximalIdealGraded` on the class of `u` gives the
class of `u - 1` in `𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤`. -/
@[simp]
theorem principalUnitGroupGradedSuccEquivMaximalIdealGraded_mk (n : ℕ)
    (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) :
    principalUnitGroupGradedSuccEquivMaximalIdealGraded S n (QuotientGroup.mk u) =
      .ofAdd (Submodule.Quotient.mk
        ⟨((u : Sˣ) : S) - 1, Ideal.mem_principalUnitGroup.mp u.property⟩) := by
  simp only [principalUnitGroupGradedSuccEquivMaximalIdealGraded, MulEquiv.trans_apply,
    Ideal.principalUnitGroupPowQuotientEquiv_mk]
  rfl

end IsLocalRing

end TauCeti
