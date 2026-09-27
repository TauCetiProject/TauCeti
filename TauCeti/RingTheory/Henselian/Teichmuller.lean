/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.RingTheory.RootsOfUnity.Finite
public import TauCeti.RingTheory.RootsOfUnity.Henselian
public import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed

import TauCeti.GroupTheory.OrderOfElement.Basic

/-!
# The Teichmüller lift of a Henselian local ring with finite residue field

Let `R` be a Henselian local ring whose residue field `k` is finite, of cardinality `q`. Reduction
`Rˣ → kˣ` identifies the `(q - 1)`-st roots of unity on both sides, because `q - 1` is a
unit in `R`. Since every unit of `k` is a `(q - 1)`-st root of unity, the inverse equivalence gives
the *Teichmüller lift* `teichmuller R : kˣ →* Rˣ`.

Thus this construction reuses the general Henselian roots-of-unity equivalence. Its public
characterization says that the lift of `x` is the unique `(q - 1)`-st root of unity reducing to
`x`; in particular its image is exactly `μ_{q-1}(R)`, and it is the *only* multiplicative section
of reduction.

Since the lift is a section of reduction, `Rˣ` is the internal direct product of `μ_{q-1}(R)`
and the kernel `1 + 𝔪` of reduction on units, the *principal units*: this is the Teichmüller
splitting `Rˣ ≃* μ_{q-1}(R) × (1 + 𝔪)`, whose inverse is multiplication.

A ring `R` that is moreover integrally closed in an `R`-algebra `A` has the same `(q - 1)`-st
roots of unity as `A`, since roots of unity are integral. This gives the corresponding
identification `μ_{q-1}(A) ≃* kˣ`; the case of a fraction ring of `R` is the one used for local
fields.

## Main results

* `TauCeti.teichmuller`: the Teichmüller lift `kˣ →* Rˣ`.
* `TauCeti.teichmuller_eq_iff`: the characterization of its values.
* `TauCeti.eq_teichmuller`: it is the only multiplicative section of reduction.
* `TauCeti.range_teichmuller`: its image is exactly `μ_{q-1}(R)`.
* `TauCeti.rootsOfUnityMulEquivUnitsResidueField`: reduction is an isomorphism `μ_{q-1}(R) ≃* kˣ`.
* `TauCeti.isComplement'_rootsOfUnity_ker_unitsMap_residue`,
  `TauCeti.unitsMulEquivRootsOfUnityProdKerResidue`: the Teichmüller splitting
  `Rˣ ≃* μ_{q-1}(R) × (1 + 𝔪)`.
* `TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField`: if `R` is integrally closed in an
  `R`-algebra `A`, then `μ_{q-1}(A) ≃* kˣ`.

## References

* J.-P. Serre, *Corps Locaux*, II §4.
* J. Neukirch, *Algebraic Number Theory*, II §5.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- A finite field has at least two elements, so the exponent `q - 1` is nonzero. -/
theorem card_residueField_sub_one_ne_zero : Nat.card (ResidueField R) - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt Finite.one_lt_card

private theorem isUnit_card_residueField_sub_one :
    IsUnit ((Nat.card (ResidueField R) - 1 : ℕ) : R) := by
  rw [← residue_ne_zero_iff_isUnit, map_natCast,
    TauCeti.natCast_natCard_sub_one_eq_neg_one, neg_ne_zero]
  exact one_ne_zero

/-- Reduction identifies the `(q - 1)`-st roots of unity of `R` with the units of its residue
field. -/
noncomputable def rootsOfUnityMulEquivUnitsResidueField :
    rootsOfUnity (Nat.card (ResidueField R) - 1) R ≃* (ResidueField R)ˣ :=
  (rootsOfUnityEquivResidueField (isUnit_card_residueField_sub_one R)).trans
    (rootsOfUnityEquivUnits (ResidueField R))

@[simp] theorem coe_rootsOfUnityMulEquivUnitsResidueField
    (u : rootsOfUnity (Nat.card (ResidueField R) - 1) R) :
    (rootsOfUnityMulEquivUnitsResidueField R u : ResidueField R) = residue R (u : Rˣ) := by
  rw [rootsOfUnityMulEquivUnitsResidueField, MulEquiv.trans_apply, rootsOfUnityEquivUnits_apply]
  exact coe_rootsOfUnityEquivResidueField _ u

/-- The **Teichmüller lift** of a Henselian local ring `R` with finite residue field `k` of
cardinality `q`: the multiplicative section of reduction that sends `x` to the unique
`(q - 1)`-st root of unity above `x`. -/
noncomputable def teichmuller : (ResidueField R)ˣ →* Rˣ :=
  (rootsOfUnity (Nat.card (ResidueField R) - 1) R).subtype.comp
    (rootsOfUnityMulEquivUnitsResidueField R).symm.toMonoidHom

/-- The Teichmüller lift is the inverse of the roots-of-unity equivalence, read in `Rˣ`. This
unfolds the definition of `teichmuller`; stating it once lets the proofs below work with the
equivalence. -/
@[simp] theorem rootsOfUnityMulEquivUnitsResidueField_symm_apply (x : (ResidueField R)ˣ) :
    ((rootsOfUnityMulEquivUnitsResidueField R).symm x : Rˣ) = teichmuller R x := by
  rw [teichmuller, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply]

/-- The Teichmüller lift takes its values in the `(q - 1)`-st roots of unity. -/
theorem teichmuller_pow_card_sub_one (x : (ResidueField R)ˣ) :
    teichmuller R x ^ (Nat.card (ResidueField R) - 1) = 1 := by
  rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply]
  exact (mem_rootsOfUnity _ _).1 ((rootsOfUnityMulEquivUnitsResidueField R).symm x).2

/-- The simplifier-normalized form of the torsion property of the Teichmüller lift, stated with
`Fintype.card` rather than `Nat.card`. -/
@[simp] theorem teichmuller_pow_fintype_card_sub_one (x : (ResidueField R)ˣ) :
    teichmuller R x ^ (@Fintype.card (ResidueField R) (Fintype.ofFinite _) - 1) = 1 := by
  rw [← @Nat.card_eq_fintype_card (ResidueField R) (Fintype.ofFinite _)]
  exact teichmuller_pow_card_sub_one R x

/-- The Teichmüller lift is a section of reduction. -/
@[simp] theorem residue_teichmuller (x : (ResidueField R)ˣ) :
    residue R (teichmuller R x : R) = x := by
  rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply,
    ← coe_rootsOfUnityMulEquivUnitsResidueField, MulEquiv.apply_symm_apply]

/-- The Teichmüller lift is a section of reduction, read in the unit group of the residue field. -/
@[simp] theorem unitsMap_residue_teichmuller (x : (ResidueField R)ˣ) :
    Units.map (residue R : R →* ResidueField R) (teichmuller R x) = x :=
  Units.ext (residue_teichmuller R x)

/-- The Teichmüller lift of `x` is the unique root of unity of order dividing `q - 1` above
`x`. -/
theorem teichmuller_eq_iff {x : (ResidueField R)ˣ} {u : Rˣ} :
    teichmuller R x = u ↔
      u ^ (Nat.card (ResidueField R) - 1) = 1 ∧ residue R (u : R) = x := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨teichmuller_pow_card_sub_one R x, residue_teichmuller R x⟩
  · rintro ⟨hpow, hres⟩
    let v : rootsOfUnity (Nat.card (ResidueField R) - 1) R := ⟨u, hpow⟩
    have hv : rootsOfUnityMulEquivUnitsResidueField R v = x := by
      apply Units.ext
      simpa only [coe_rootsOfUnityMulEquivUnitsResidueField] using hres
    have hv' := congrArg (rootsOfUnityMulEquivUnitsResidueField R).symm hv
    rw [MulEquiv.symm_apply_apply] at hv'
    rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply, ← hv']

/-- The Teichmüller lift is injective, being a section of reduction. -/
theorem teichmuller_injective : Function.Injective (teichmuller R) := fun x y h ↦ by
  simpa using congrArg (Units.map (residue R : R →* ResidueField R)) h

/-- The Teichmüller lift is the only multiplicative section of reduction. No torsion assumption on
the section is needed: a monoid hom out of `kˣ`, a group of order `q - 1`, automatically takes
`(q - 1)`-st roots of unity as values. -/
theorem eq_teichmuller (s : (ResidueField R)ˣ →* Rˣ) (hsec : ∀ x, residue R (s x : R) = x) :
    s = teichmuller R :=
  MonoidHom.ext fun x ↦ ((teichmuller_eq_iff R).2
    ⟨by rw [← map_pow, ← Nat.card_units, pow_card_eq_one', map_one], hsec x⟩).symm

/-- The image of the Teichmüller lift is `μ_{q-1}(R)`. -/
theorem range_teichmuller :
    (teichmuller R).range = rootsOfUnity (Nat.card (ResidueField R) - 1) R := by
  ext u
  simp only [MonoidHom.mem_range, mem_rootsOfUnity]
  refine ⟨?_, fun h ↦ ⟨rootsOfUnityMulEquivUnitsResidueField R ⟨u, h⟩, ?_⟩⟩
  · rintro ⟨x, rfl⟩
    exact teichmuller_pow_card_sub_one R x
  · rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply, MulEquiv.symm_apply_apply]

/-- A Henselian local ring with residue field of cardinality `q` has exactly `q - 1` roots of
unity of order dividing `q - 1`. -/
theorem card_rootsOfUnity :
    Nat.card (rootsOfUnity (Nat.card (ResidueField R) - 1) R) =
      Nat.card (ResidueField R) - 1 := by
  rw [Nat.card_congr (rootsOfUnityMulEquivUnitsResidueField R).toEquiv, Nat.card_units]

/-! ### The Teichmüller splitting of the unit group

The Teichmüller lift is a section of reduction `Rˣ → kˣ`, so `Rˣ` is the internal direct product
of `μ_{q-1}(R)`, the image of the lift, and the kernel `1 + 𝔪` of reduction on units, the
*principal units*. -/

section Splitting

/-- **The Teichmüller splitting**, as complementary subgroups: every unit of `R` is uniquely the
product of a `(q - 1)`-st root of unity and a principal unit, that is a unit reducing to `1` in
the residue field. -/
theorem isComplement'_rootsOfUnity_ker_unitsMap_residue :
    (rootsOfUnity (Nat.card (ResidueField R) - 1) R).IsComplement'
      (Units.map (residue R : R →* ResidueField R)).ker := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · -- A root of unity reducing to `1` is the Teichmüller lift of `1`.
    refine Subgroup.disjoint_def.mpr fun {ζ} hζ hker ↦ ?_
    rw [MonoidHom.mem_ker] at hker
    have h := (teichmuller_eq_iff R (x := 1) (u := ζ)).mpr
      ⟨(mem_rootsOfUnity _ _).mp hζ, by simpa using congrArg Units.val hker⟩
    rw [← h, map_one]
  · -- `u = ω(ū) * (ω(ū)⁻¹ * u)`, and the second factor reduces to `1`.
    refine Set.eq_univ_of_forall fun u ↦ ?_
    refine Set.mem_mul.mpr ⟨teichmuller R (Units.map (residue R : R →* ResidueField R) u),
      ?_, (teichmuller R (Units.map (residue R : R →* ResidueField R) u))⁻¹ * u, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← range_teichmuller]
      exact ⟨_, rfl⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, unitsMap_residue_teichmuller,
        inv_mul_cancel]
    · rw [mul_inv_cancel_left]

/-- **The Teichmüller splitting of the unit group**, `Rˣ ≃* μ_{q-1}(R) × (1 + 𝔪)`: a unit `u`
goes to the Teichmüller representative `ω(ū)` of its residue class together with the principal
unit `ω(ū)⁻¹ * u`, and the inverse is multiplication. -/
noncomputable def unitsMulEquivRootsOfUnityProdKerResidue :
    Rˣ ≃* rootsOfUnity (Nat.card (ResidueField R) - 1) R ×
      (Units.map (residue R : R →* ResidueField R)).ker :=
  (MulEquiv.ofBijective ((rootsOfUnity _ R).subtype.coprod (Units.map _).ker.subtype)
    ((Subgroup.isComplement_iff_bijective _ _).mp
      (isComplement'_rootsOfUnity_ker_unitsMap_residue R))).symm

/-- The inverse of the Teichmüller splitting is multiplication, `(ζ, v) ↦ ζ * v`. -/
@[simp]
theorem unitsMulEquivRootsOfUnityProdKerResidue_symm_apply
    (x : rootsOfUnity (Nat.card (ResidueField R) - 1) R ×
      (Units.map (residue R : R →* ResidueField R)).ker) :
    (unitsMulEquivRootsOfUnityProdKerResidue R).symm x = x.1 * x.2 :=
  (rfl)

/-- The root-of-unity component of a unit `u` is the Teichmüller representative of its residue
class. -/
@[simp]
theorem coe_unitsMulEquivRootsOfUnityProdKerResidue_apply_fst (u : Rˣ) :
    ((unitsMulEquivRootsOfUnityProdKerResidue R u).1 : Rˣ) =
      teichmuller R (Units.map (residue R : R →* ResidueField R) u) := by
  have h := (unitsMulEquivRootsOfUnityProdKerResidue R).symm_apply_apply u
  rw [unitsMulEquivRootsOfUnityProdKerResidue_symm_apply] at h
  symm
  rw [teichmuller_eq_iff]
  refine ⟨(mem_rootsOfUnity _ _).mp (unitsMulEquivRootsOfUnityProdKerResidue R u).1.2, ?_⟩
  have h' := congrArg (Units.map (residue R : R →* ResidueField R)) h
  rw [map_mul, MonoidHom.mem_ker.mp (unitsMulEquivRootsOfUnityProdKerResidue R u).2.2,
    mul_one] at h'
  exact congrArg Units.val h'

/-- The principal-unit component of a unit `u` is `u` divided by the Teichmüller representative
of its residue class. -/
@[simp]
theorem coe_unitsMulEquivRootsOfUnityProdKerResidue_apply_snd (u : Rˣ) :
    ((unitsMulEquivRootsOfUnityProdKerResidue R u).2 : Rˣ) =
      (teichmuller R (Units.map (residue R : R →* ResidueField R) u))⁻¹ * u := by
  have h := (unitsMulEquivRootsOfUnityProdKerResidue R).symm_apply_apply u
  rw [unitsMulEquivRootsOfUnityProdKerResidue_symm_apply,
    coe_unitsMulEquivRootsOfUnityProdKerResidue_apply_fst] at h
  rw [eq_inv_mul_iff_mul_eq, h]

end Splitting

section IsIntegrallyClosedIn

variable (A : Type*) [CommRing A] [Algebra R A] [IsIntegrallyClosedIn R A]

/-- If `R` is integrally closed in an `R`-algebra `A`, reduction identifies `μ_{q-1}(A)` with
the unit group of the residue field: the roots of unity of `A` are integral over `R`, hence
already lie in `R`. -/
noncomputable def rootsOfUnityAlgebraMulEquivUnitsResidueField :
    rootsOfUnity (Nat.card (ResidueField R) - 1) A ≃* (ResidueField R)ˣ :=
  haveI : NeZero (Nat.card (ResidueField R) - 1) := ⟨card_residueField_sub_one_ne_zero R⟩
  (rootsOfUnityMulEquiv R A _).symm.trans (rootsOfUnityMulEquivUnitsResidueField R)

@[simp] theorem rootsOfUnityAlgebraMulEquivUnitsResidueField_symm_apply
    (x : (ResidueField R)ˣ) :
    (((rootsOfUnityAlgebraMulEquivUnitsResidueField R A).symm x : Aˣ) : A) =
      algebraMap R A (teichmuller R x : R) := by
  have : NeZero (Nat.card (ResidueField R) - 1) := ⟨card_residueField_sub_one_ne_zero R⟩
  simp [rootsOfUnityAlgebraMulEquivUnitsResidueField]

/-- The forward direction of the equivalence, read in `A`: the Teichmüller lift of the value at a
root of unity `u` of `A` is `u` itself. -/
@[simp] theorem algebraMap_teichmuller_rootsOfUnityAlgebraMulEquivUnitsResidueField
    (u : rootsOfUnity (Nat.card (ResidueField R) - 1) A) :
    algebraMap R A (teichmuller R (rootsOfUnityAlgebraMulEquivUnitsResidueField R A u) : R) =
      ((u : Aˣ) : A) := by
  rw [← rootsOfUnityAlgebraMulEquivUnitsResidueField_symm_apply, MulEquiv.symm_apply_apply]

/-- The value of the equivalence at a root of unity `u` of `A` is the reduction of the element of
`R` that `u` comes from. -/
theorem coe_rootsOfUnityAlgebraMulEquivUnitsResidueField
    (u : rootsOfUnity (Nat.card (ResidueField R) - 1) A) {y : R}
    (hy : algebraMap R A y = ((u : Aˣ) : A)) :
    (rootsOfUnityAlgebraMulEquivUnitsResidueField R A u : ResidueField R) = residue R y := by
  have hinj : Function.Injective (algebraMap R A) := IsIntegralClosure.algebraMap_injective R R A
  have h : (teichmuller R (rootsOfUnityAlgebraMulEquivUnitsResidueField R A u) : R) = y :=
    hinj (by rw [algebraMap_teichmuller_rootsOfUnityAlgebraMulEquivUnitsResidueField, hy])
  rw [← h, residue_teichmuller]

end IsIntegrallyClosedIn

end TauCeti
