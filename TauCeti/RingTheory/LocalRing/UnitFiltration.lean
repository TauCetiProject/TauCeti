/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic

/-!
# The unit filtration of a local ring

For a commutative local ring `S` with maximal ideal `𝔪` and residue field `k`, the **unit
filtration** is the decreasing sequence of subgroups of `Sˣ` given by the principal unit groups of
the powers of `𝔪`:

`unitFiltration S i = (𝔪 ^ i).principalUnitGroup = {u : Sˣ | (u : S) - 1 ∈ 𝔪 ^ i}`.

Because `𝔪 ^ 0 = ⊤`, the zeroth step `unitFiltration S 0` is the whole unit group `⊤ : Subgroup Sˣ`,
while `unitFiltration S i = 1 + 𝔪 ^ i` for `i ≥ 1`. Since `𝔪` is the Jacobson radical of `S`,
reduction modulo `𝔪` identifies the zeroth successive quotient `U_0 / U_1` with `kˣ`, and
subtracting `1` identifies each positive successive quotient `U_{n+1} / U_{n+2}` with the additive
graded piece `𝔪 ^ (n + 1) / 𝔪 ^ (n + 2)` (written `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)` to match
`TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`). Without any finiteness or DVR
assumption, this additive identification determines the torsion of each positive graded piece: when
`k` has characteristic `p`, every element satisfies `x ^ p = 1` and `U_{n+1} / U_{n+2}` is a
`p`-group; when `k` has characteristic zero, `U_{n+1} / U_{n+2}` is torsion-free.

When a group `G` acts on `S` by ring automorphisms, an element `σ` in the `i`-th ramification
group moves every unit `u : Sˣ` by a factor `(σ • u) / u` lying in `U_{i+1}`. Over a discrete
valuation ring, this is what makes the uniformizer ratio `σ ϖ / ϖ` independent of the choice of
uniformizer `ϖ` and multiplicative modulo `U_{i+1}`.

## Main definitions

* `TauCeti.IsLocalRing.unitFiltration S i`: the `i`-th step `(𝔪 ^ i).principalUnitGroup` of the
  unit filtration of `Sˣ`.
* `TauCeti.IsLocalRing.UnitFiltrationGraded S i`: the successive quotient `U_i / U_{i+1}`.
* `TauCeti.IsLocalRing.unitFiltrationGradedZeroEquivResidueFieldUnits`: the canonical isomorphism
  `U_0 / U_1 ≃* (ResidueField S)ˣ` induced by `residue S`.
* `TauCeti.IsLocalRing.unitFiltrationGradedSuccEquivMaximalIdealGraded`: the canonical isomorphism
  `U_{n+1} / U_{n+2} ≃* Multiplicative (𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤))` given by `u ↦ (u : S) - 1`.

## Main results

* `TauCeti.IsLocalRing.unitFiltration_zero`, `TauCeti.IsLocalRing.unitFiltration_one`, and
  `TauCeti.IsLocalRing.unitFiltration_antitone`: shallow steps and monotonicity.
* `TauCeti.IsLocalRing.iInf_unitFiltration_eq_bot`: over a Noetherian local ring, the unit
  filtration separates points (`⨅ i, U_i = ⊥`).
* `TauCeti.IsLocalRing.unitFiltrationGraded_succ_pow_eq_one_of_charP`,
  `TauCeti.IsLocalRing.isPGroup_unitFiltrationGraded_succ`, and
  `TauCeti.IsLocalRing.eq_one_of_pow_eq_one_unitFiltrationGraded_succ_of_charZero`: torsion of the
  positive graded pieces determined by the residue characteristic.
* `TauCeti.IsLocalRing.unitsMap_div_mem_unitFiltration_succ`: an element of the `i`-th ramification
  group moves every unit of `S` by a factor in `U_{i+1}`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

section Basic

variable (S : Type*) [CommRing S] [IsLocalRing S]

/-- The `i`-th step of the **unit filtration** of a local ring `S`: the subgroup of units `u : Sˣ`
with `(u : S) - 1 ∈ 𝔪 ^ i`. For `i = 0` this is `⊤`, and for `i ≥ 1` it is `1 + 𝔪 ^ i`. -/
def unitFiltration (i : ℕ) : Subgroup Sˣ :=
  (maximalIdeal S ^ i).principalUnitGroup

/-- Unfolds `unitFiltration` to the principal unit group of `𝔪 ^ i`. -/
theorem unitFiltration_def (i : ℕ) :
    unitFiltration S i = (maximalIdeal S ^ i).principalUnitGroup :=
  (rfl)

variable {S}

/-- Membership in `unitFiltration S i` is congruence to `1` modulo `𝔪 ^ i`. -/
@[simp]
theorem mem_unitFiltration_iff {i : ℕ} {u : Sˣ} :
    u ∈ unitFiltration S i ↔ (u : S) - 1 ∈ maximalIdeal S ^ i :=
  Ideal.mem_principalUnitGroup

/-- At depth `1`, a unit lies in `unitFiltration S 1` exactly when its residue is `1`. -/
theorem mem_unitFiltration_one_iff_residue_eq_one {u : Sˣ} :
    u ∈ unitFiltration S 1 ↔ residue S (u : S) = 1 := by
  rw [mem_unitFiltration_iff, pow_one, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]

variable (S)

/-- The depth-zero step of the unit filtration is the whole unit group `Sˣ`. -/
@[simp]
theorem unitFiltration_zero : unitFiltration S 0 = ⊤ := by
  rw [unitFiltration_def, pow_zero, Ideal.one_eq_top, Ideal.principalUnitGroup_top]

/-- The depth-one step of the unit filtration is the principal unit group of the maximal ideal. -/
@[simp]
theorem unitFiltration_one : unitFiltration S 1 = (maximalIdeal S).principalUnitGroup := by
  rw [unitFiltration_def, pow_one]

/-- The unit filtration is decreasing. -/
theorem unitFiltration_antitone : Antitone (unitFiltration S) :=
  (maximalIdeal S).principalUnitGroup_pow_antitone

/-- The `i`-th successive quotient `U_i / U_{i+1}` of the unit filtration of a local ring `S`. -/
abbrev UnitFiltrationGraded (i : ℕ) :=
  unitFiltration S i ⧸ (unitFiltration S (i + 1)).subgroupOf (unitFiltration S i)

/-- Over a Noetherian local ring, the unit filtration intersects in the trivial subgroup. -/
theorem iInf_unitFiltration_eq_bot [IsNoetherianRing S] :
    ⨅ i : ℕ, unitFiltration S i = ⊥ := by
  ext u
  rw [Subgroup.mem_iInf, Subgroup.mem_bot, Units.ext_iff, Units.val_one, ← sub_eq_zero,
    ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal S).ne_top,
    Ideal.mem_iInf]
  simp only [mem_unitFiltration_iff]

end Basic

section Graded

variable (S : Type*) [CommRing S] [IsLocalRing S]

/-- Reduction modulo the maximal ideal identifies the depth-zero graded piece `U_0 / U_1` of the
unit filtration with the multiplicative group `(ResidueField S)ˣ`. -/
noncomputable def unitFiltrationGradedZeroEquivResidueFieldUnits :
    UnitFiltrationGraded S 0 ≃* (ResidueField S)ˣ :=
  (QuotientGroup.congr
    ((unitFiltration S 1).subgroupOf (unitFiltration S 0))
    (maximalIdeal S).principalUnitGroup
    ((MulEquiv.subgroupCongr (unitFiltration_zero S)).trans Subgroup.topEquiv)
    (by
      ext v
      simp [unitFiltration_one, Subgroup.mem_subgroupOf])).trans
    (Ideal.unitsQuotientPrincipalUnitGroupEquiv (maximalIdeal_le_jacobson (⊥ : Ideal S)))

/-- Evaluates `unitFiltrationGradedZeroEquivResidueFieldUnits` on the class of `u` via `Units.map`
along `residue S`. -/
@[simp]
theorem unitFiltrationGradedZeroEquivResidueFieldUnits_mk (u : unitFiltration S 0) :
    unitFiltrationGradedZeroEquivResidueFieldUnits S (QuotientGroup.mk u) =
      Units.map (residue S).toMonoidHom (u : Sˣ) :=
  (MulEquiv.trans_apply ..).trans <|
    (congrArg _ (QuotientGroup.congr_mk ..)).trans <|
      Ideal.unitsQuotientPrincipalUnitGroupEquiv_mk
        (maximalIdeal_le_jacobson (⊥ : Ideal S)) (u : Sˣ)

/-- The underlying residue-field value of `unitFiltrationGradedZeroEquivResidueFieldUnits` on the
class of `u` is `residue S u`. -/
theorem coe_unitFiltrationGradedZeroEquivResidueFieldUnits_mk (u : unitFiltration S 0) :
    ((unitFiltrationGradedZeroEquivResidueFieldUnits S (QuotientGroup.mk u) :
        (ResidueField S)ˣ) : ResidueField S) =
      residue S ((u : Sˣ) : S) := by
  simp [unitFiltrationGradedZeroEquivResidueFieldUnits_mk]

private theorem comap_maximalIdeal_pow_succ_eq_smul_top (n : ℕ) :
    Submodule.comap (maximalIdeal S ^ (n + 1)).subtype (maximalIdeal S ^ (n + 2)) =
      (maximalIdeal S • ⊤ : Submodule S (maximalIdeal S ^ (n + 1) : Ideal S)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_smul_top_iff, smul_eq_mul,
    pow_succ']

/-- Subtracting `1` identifies each positive graded piece `U_{n+1} / U_{n+2}` of the unit
filtration with the multiplicative copy of the maximal-ideal graded piece
`𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. -/
noncomputable def unitFiltrationGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    UnitFiltrationGraded S (n + 1) ≃*
      Multiplicative ((maximalIdeal S ^ (n + 1) : Ideal S) ⧸
        (maximalIdeal S • ⊤ : Submodule S (maximalIdeal S ^ (n + 1) : Ideal S))) :=
  (Ideal.principalUnitGroupPowQuotientEquiv (maximalIdeal_le_jacobson (⊥ : Ideal S)) n).trans
    (Submodule.quotEquivOfEq _ _ (comap_maximalIdeal_pow_succ_eq_smul_top S n)).toMultiplicative

/-- Evaluates `unitFiltrationGradedSuccEquivMaximalIdealGraded` on the class of `u` as the class of
`(u : S) - 1`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivMaximalIdealGraded_mk (n : ℕ)
    (u : unitFiltration S (n + 1)) :
    unitFiltrationGradedSuccEquivMaximalIdealGraded S n (QuotientGroup.mk u) =
      Multiplicative.ofAdd
        (Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, mem_unitFiltration_iff.mp u.property⟩) :=
  (MulEquiv.trans_apply ..).trans <|
    (congrArg _ (Ideal.principalUnitGroupPowQuotientEquiv_mk ..)).trans <|
      congrArg Multiplicative.ofAdd
        (Submodule.quotEquivOfEq_mk _ _ (comap_maximalIdeal_pow_succ_eq_smul_top S n) _)

/-- When the residue field has characteristic `p`, every element of a positive graded piece
`U_{n+1} / U_{n+2}` satisfies `x ^ p = 1`. -/
theorem unitFiltrationGraded_succ_pow_eq_one_of_charP (p : ℕ) [CharP (ResidueField S) p]
    (n : ℕ) (x : UnitFiltrationGraded S (n + 1)) :
    x ^ p = 1 := by
  let e := unitFiltrationGradedSuccEquivMaximalIdealGraded S n
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [map_pow, map_one, toAdd_pow, toAdd_one]
  have hp : (p : S) ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  induction (e x).toAdd using Submodule.Quotient.induction_on with
  | _ a =>
    rw [← Nat.cast_smul_eq_nsmul S, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hp Submodule.mem_top

/-- For the residue characteristic `p`, every positive graded piece `U_{n+1} / U_{n+2}` of the
unit filtration is a `p`-group. No finiteness or DVR assumption is needed. -/
theorem isPGroup_unitFiltrationGraded_succ (p : ℕ) [CharP (ResidueField S) p] (n : ℕ) :
    IsPGroup p (UnitFiltrationGraded S (n + 1)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  exact fun x ↦ ⟨1, by rw [pow_one, unitFiltrationGraded_succ_pow_eq_one_of_charP S p n x]⟩

variable {S} in
/-- In residue characteristic zero, every positive graded piece `U_{n+1} / U_{n+2}` of the unit
filtration is torsion-free. -/
theorem eq_one_of_pow_eq_one_unitFiltrationGraded_succ_of_charZero [CharZero (ResidueField S)]
    {n k : ℕ} (hk : k ≠ 0) {x : UnitFiltrationGraded S (n + 1)} (hx : x ^ k = 1) :
    x = 1 := by
  let e := unitFiltrationGradedSuccEquivMaximalIdealGraded S n
  have hkm : (k : S) • (e x).toAdd = 0 := by
    rw [Nat.cast_smul_eq_nsmul, ← toAdd_pow, ← map_pow, hx, map_one, toAdd_one]
  have hu : IsUnit (k : S) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, map_natCast]
    exact Nat.cast_ne_zero.mpr hk
  exact e.injective (Multiplicative.toAdd.injective
    (by rw [hu.smul_eq_zero.mp hkm, map_one, toAdd_one]))

end Graded

section Action

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- For an element `σ` in the `i`-th ramification group of a local ring `S` and any unit `u : Sˣ`,
the ratio `(σ • u) / u` lies one step deeper in the unit filtration, in `unitFiltration S (i + 1)`.
-/
theorem unitsMap_div_mem_unitFiltration_succ {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S (i : ℤ)) (u : Sˣ) :
    Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom u / u ∈
      unitFiltration S (i + 1) := by
  rw [mem_unitFiltration_iff, div_eq_mul_inv]
  have hsub :
      ((Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom u * u⁻¹ : Sˣ) : S) - 1 =
        (σ • (u : S) - (u : S)) * (u⁻¹ : Sˣ) := by
    simp [sub_mul]
  rw [hsub]
  exact Ideal.mul_mem_right _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : S))

end Action

end TauCeti.IsLocalRing
