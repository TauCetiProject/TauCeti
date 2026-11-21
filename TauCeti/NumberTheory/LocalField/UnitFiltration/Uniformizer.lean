/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer

/-!
# Uniformizer coordinates on unit-filtration graded pieces

Fixing a uniformizer `π` identifies the `m`th positive graded piece of the unit filtration
with the additive residue field: the class of `u` has coordinate `(u - 1) / π ^ m` modulo the
maximal ideal.  This file identifies `unitFiltration K i` with
`(maximalIdeal 𝒪[K] ^ i).principalUnitGroup` and `UnitFiltrationGraded K i` with
`(maximalIdeal 𝒪[K]).PrincipalUnitGroupPowGraded i`, and transports the discrete-valuation-ring
coordinate
`TauCeti.maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer` along this
identification.

If `π' = π * a` for a unit `a` of the integer ring, then the coordinate relative to `π` is
`a ^ m` times the coordinate relative to `π'`.  Thus the identification is independent of the
uniformizer up to the additive automorphism of the residue field induced by multiplication by
the residue of `a ^ m`.

## Main definitions

* `TauCeti.unitFiltrationEquivPrincipalUnitGroup`: identification of `unitFiltration K i` with
  `(maximalIdeal 𝒪[K] ^ i).principalUnitGroup`.
* `TauCeti.unitFiltrationGradedEquivPrincipalUnitGroupPowGraded`: identification of
  `UnitFiltrationGraded K i` with `(maximalIdeal 𝒪[K]).PrincipalUnitGroupPowGraded i`.
* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer`: the residue coordinate
  determined by a uniformizer.

## Main results

* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue`: its value
  on a representative whose difference from one is given explicitly.
* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change`: changing the
  uniformizer scales the coordinate by the corresponding residue-field unit.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A unit of `𝒪[K]` maps into `U(K,i)` if and only if it belongs to the `i`-th principal unit
group of `maximalIdeal 𝒪[K]`. -/
theorem mem_unitFiltration_iff_mem_principalUnitGroup (i : ℕ) (u : 𝒪[K]ˣ) :
    Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u ∈ unitFiltration K i ↔
      u ∈ (maximalIdeal 𝒪[K] ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup]
  cases i with
  | zero =>
    simp
  | succ n =>
    rw [← RingHom.toMonoidHom_eq_coe]
    exact mem_unitFiltration_succ_congr n u

/-- The `i`-th step `U(K,i)` of the unit filtration is multiplicatively isomorphic to the
principal unit group `(maximalIdeal 𝒪[K] ^ i).principalUnitGroup` inside `𝒪[K]ˣ`. -/
noncomputable def unitFiltrationEquivPrincipalUnitGroup (i : ℕ) :
    unitFiltration K i ≃* (maximalIdeal 𝒪[K] ^ i).principalUnitGroup where
  toFun x := ⟨unitFiltrationToIntegerUnits i x,
    (mem_unitFiltration_iff_mem_principalUnitGroup i _).mp <| by
      rw [unitsMap_subtype_unitFiltrationToIntegerUnits]
      exact x.property⟩
  invFun u := ⟨Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) (u : 𝒪[K]ˣ),
    (mem_unitFiltration_iff_mem_principalUnitGroup i (u : 𝒪[K]ˣ)).mpr u.property⟩
  left_inv x := Subtype.ext <| by
    simp only [unitsMap_subtype_unitFiltrationToIntegerUnits]
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    apply Subtype.coe_injective
    exact coe_unitFiltrationToIntegerUnits i _
  map_mul' x y := Subtype.ext (map_mul (unitFiltrationToIntegerUnits i) x y)

/-- Coerced to `𝒪[K]ˣ`, `unitFiltrationEquivPrincipalUnitGroup` agrees with
`unitFiltrationToIntegerUnits`. -/
@[simp]
theorem coe_unitFiltrationEquivPrincipalUnitGroup_apply (i : ℕ) (x : unitFiltration K i) :
    (unitFiltrationEquivPrincipalUnitGroup i x : 𝒪[K]ˣ) = unitFiltrationToIntegerUnits i x :=
  (rfl)

/-- Coerced to `Kˣ`, the inverse of `unitFiltrationEquivPrincipalUnitGroup` is the inclusion of
`𝒪[K]ˣ` into `Kˣ`. -/
@[simp]
theorem coe_unitFiltrationEquivPrincipalUnitGroup_symm_apply (i : ℕ)
    (u : (maximalIdeal 𝒪[K] ^ i).principalUnitGroup) :
    ((unitFiltrationEquivPrincipalUnitGroup i).symm u : Kˣ) =
      Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) (u : 𝒪[K]ˣ) :=
  (rfl)

/-- The `i`-th graded piece `U(K,i) / U(K,i+1)` of the unit filtration is multiplicatively
isomorphic to `(maximalIdeal 𝒪[K]).PrincipalUnitGroupPowGraded i`. -/
noncomputable def unitFiltrationGradedEquivPrincipalUnitGroupPowGraded (i : ℕ) :
    UnitFiltrationGraded K i ≃* (maximalIdeal 𝒪[K]).PrincipalUnitGroupPowGraded i :=
  QuotientGroup.congr _ _ (unitFiltrationEquivPrincipalUnitGroup i) (by
    ext u
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (unitFiltrationEquivPrincipalUnitGroup i x : 𝒪[K]ˣ) ∈
        (maximalIdeal 𝒪[K] ^ (i + 1)).principalUnitGroup
      rw [coe_unitFiltrationEquivPrincipalUnitGroup_apply]
      exact (mem_unitFiltration_iff_mem_principalUnitGroup (i + 1) _).mp <| by
        simpa only [unitsMap_subtype_unitFiltrationToIntegerUnits] using hx
    · intro hu
      refine ⟨(unitFiltrationEquivPrincipalUnitGroup i).symm u, ?_,
        (unitFiltrationEquivPrincipalUnitGroup i).apply_symm_apply u⟩
      rw [coe_unitFiltrationEquivPrincipalUnitGroup_symm_apply]
      exact (mem_unitFiltration_iff_mem_principalUnitGroup (i + 1) _).mpr hu)

/-- Evaluating `unitFiltrationGradedEquivPrincipalUnitGroupPowGraded` on a quotient class. -/
@[simp]
theorem unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_mk (i : ℕ)
    (x : unitFiltration K i) :
    unitFiltrationGradedEquivPrincipalUnitGroupPowGraded i (QuotientGroup.mk x) =
      QuotientGroup.mk (unitFiltrationEquivPrincipalUnitGroup i x) :=
  QuotientGroup.congr_mk _ _ _ _ x

/-- Evaluating the inverse of `unitFiltrationGradedEquivPrincipalUnitGroupPowGraded` on a
quotient class. -/
@[simp]
theorem unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_symm_mk (i : ℕ)
    (u : (maximalIdeal 𝒪[K] ^ i).principalUnitGroup) :
    (unitFiltrationGradedEquivPrincipalUnitGroupPowGraded i).symm (QuotientGroup.mk u) =
      QuotientGroup.mk ((unitFiltrationEquivPrincipalUnitGroup i).symm u) := by
  rw [MulEquiv.symm_apply_eq, unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_mk,
    MulEquiv.apply_symm_apply]

/-- The positive-depth unit-filtration coordinate associated to a uniformizer.  The class of
`u ∈ U(K,n+1)` is sent to the residue of `(u - 1) / π^(n+1)`. -/
noncomputable def unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) : Additive (UnitFiltrationGraded K (n + 1)) ≃+ 𝓀[K] :=
  (unitFiltrationGradedEquivPrincipalUnitGroupPowGraded (n + 1)).toAdditive.trans
    (maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer n π hπ)

private theorem val_coe_unitFiltrationEquivPrincipalUnitGroup_sub_one (n : ℕ)
    (x : unitFiltration K (n + 1)) :
    ((unitFiltrationEquivPrincipalUnitGroup (n + 1) x : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
      (unitFiltrationDifference n x : 𝒪[K]) := by
  apply Subtype.coe_injective
  dsimp only
  rw [AddSubgroupClass.coe_sub, coe_coe_unitFiltrationDifference, Subring.coe_one,
    coe_unitFiltrationEquivPrincipalUnitGroup_apply, coe_unitFiltrationToIntegerUnits]

/-- The uniformizer coordinate of the class of `u` is characterized by multiplying it by
`π^(n+1)`: the result is the class of `u - 1` in the maximal-ideal graded piece. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) (x : unitFiltration K (n + 1)) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ
          (Additive.ofMul (QuotientGroup.mk x))) =
      Submodule.Quotient.mk (unitFiltrationDifference n x) := by
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer, AddEquiv.trans_apply,
    MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_mk,
    maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk]
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (val_coe_unitFiltrationEquivPrincipalUnitGroup_sub_one n x))

/-- If `u - 1 = y * π^(n+1)`, then the uniformizer coordinate of the class of `u` is the
residue of `y`. This is the representative form of the positive-depth graded equivalence used in
ramification computations. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    (n : ℕ) (π : 𝒪[K]) (hπ : Irreducible π) (x : unitFiltration K (n + 1)) (y : 𝒪[K])
    (hxy : (unitFiltrationDifference n x : 𝒪[K]) = y * π ^ (n + 1)) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ
        (Additive.ofMul (QuotientGroup.mk x)) =
      IsLocalRing.residue 𝒪[K] y := by
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer, AddEquiv.trans_apply,
    MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_mk]
  exact
    maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
      n π hπ _ y ((val_coe_unitFiltrationEquivPrincipalUnitGroup_sub_one n x).trans hxy)

/-- Coordinates attached to `π` and `π'` differ by multiplication by the residue of the
`(n+1)`st power of the unit carrying `π` to `π'`. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change (n : ℕ)
    (π π' : 𝒪[K]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded K (n + 1))) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ x =
      IsLocalRing.residue 𝒪[K] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) ^ (n + 1) *
        unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π' hπ' x :=
  maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer_change
    n π π' hπ hπ' _

end TauCeti
