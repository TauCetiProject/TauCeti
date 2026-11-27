/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Power
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit.OfUnits

/-!
# Torsion of the `S`-units

Let `R` be a Dedekind domain with fraction field `K` and `S` any set of height-one primes of `R`.
An element of finite order of `Kˣ` has a power equal to `1`, so it is an `S`-unit for every `S` by
`Set.pow_mem_unit_iff`; in particular it is a unit of `R`.
Consequently inverting the primes of `S` creates no new torsion: the torsion subgroup of the
`S`-units, equivalently of the units of the ring of `S`-integers `S.integer K`, is the torsion
subgroup of `Rˣ`, through the canonical map `TauCeti.SUnit.unitOfUnits`.

For the ring of integers of a number field, the torsion of `Rˣ` is the group of roots of unity of
the field, so the units of every ring of `S`-integers have that same torsion subgroup. Only the
free part of the unit group grows with `S`.

## Main results

* `Set.mem_unit_of_isOfFinOrder`: an element of finite order of `Kˣ` is an `S`-unit for every
  `S`, in particular an `∅`-unit.
* `Set.unitTorsionEquiv`: the torsion of the `S`-units is the torsion of `Rˣ`.
* `Set.unitsIntegerTorsionEquiv`: the torsion of the units of the `S`-integers is the torsion
  of `Rˣ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 11.6 (the `S`-units and their
  torsion).
-/

public section

open IsDedekindDomain

namespace Set

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An element of finite order of `Kˣ` is an `S`-unit for every set `S` of primes, by
`Set.pow_mem_unit_iff` applied to a nonzero power equal to `1`; for `S = ∅` this says that it is
the image of a unit of `R`. -/
theorem mem_unit_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x) : x ∈ S.unit K := by
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
  exact (pow_mem_unit_iff S K hn.ne').1 (hxn ▸ one_mem _)

/-- **The torsion of the `S`-units is the torsion of `Rˣ`.** A torsion `S`-unit is an `∅`-unit
(`Set.mem_unit_of_isOfFinOrder`), hence comes from a unit of `R`, and the inverse map is
`TauCeti.SUnit.unitOfUnits`. -/
noncomputable def unitTorsionEquiv : CommGroup.torsion (S.unit K) ≃* CommGroup.torsion Rˣ where
  toFun x := ⟨unitEmptyEquivUnits K ⟨x, mem_unit_of_isOfFinOrder ∅ K
      ((S.unit K).subtype.isOfFinOrder x.property)⟩,
    (unitEmptyEquivUnits K).toMonoidHom.isOfFinOrder
      ((Subgroup.inclusion_injective (unit_mono K (empty_subset S))).isOfFinOrder_iff.1
        x.property)⟩
  invFun u := ⟨TauCeti.SUnit.unitOfUnits S K u,
    (TauCeti.SUnit.unitOfUnits S K).isOfFinOrder u.property⟩
  left_inv x := by
    ext
    simp
  right_inv u := by
    ext
    apply IsFractionRing.injective R K
    simp
  map_mul' x y := by
    ext
    apply IsFractionRing.injective R K
    simp

/-- The unit of `R` attached to a torsion `S`-unit `x` maps to `x` in `K`. -/
@[simp]
theorem algebraMap_unitTorsionEquiv_apply (x : CommGroup.torsion (S.unit K)) :
    algebraMap R K ((unitTorsionEquiv S K x : Rˣ) : R) = (((x : S.unit K) : Kˣ) : K) :=
  algebraMap_unitEmptyEquivUnits_apply K _

/-- The torsion `S`-unit attached to a torsion unit `u` of `R` is the image of `u` in `Kˣ`. -/
@[simp]
theorem coe_unitTorsionEquiv_symm_apply (u : CommGroup.torsion Rˣ) :
    (((unitTorsionEquiv S K).symm u : S.unit K) : Kˣ) = Units.map (algebraMap R K) (u : Rˣ) :=
  TauCeti.SUnit.coe_unitOfUnits S K u

/-- **The torsion of the units of the `S`-integers is the torsion of `Rˣ`.** -/
noncomputable def unitsIntegerTorsionEquiv :
    CommGroup.torsion (S.integer K)ˣ ≃* CommGroup.torsion Rˣ :=
  ((unitEquivUnitsInteger S K).symm.subgroupMap (CommGroup.torsion (S.integer K)ˣ)).trans
    ((MulEquiv.subgroupCongr ((unitEquivUnitsInteger S K).symm.map_torsion)).trans
      (unitTorsionEquiv S K))

/-- The unit of `R` attached to a torsion unit `x` of the `S`-integers maps to `x` in `K`. -/
@[simp]
theorem algebraMap_unitsIntegerTorsionEquiv_apply (x : CommGroup.torsion (S.integer K)ˣ) :
    algebraMap R K ((unitsIntegerTorsionEquiv S K x : Rˣ) : R) =
      (((x : (S.integer K)ˣ) : S.integer K) : K) := by
  simp [unitsIntegerTorsionEquiv]

/-- The torsion unit of the `S`-integers attached to a torsion unit `u` of `R` is the image of `u`
in `K`. -/
@[simp]
theorem coe_unitsIntegerTorsionEquiv_symm_apply (u : CommGroup.torsion Rˣ) :
    ((((unitsIntegerTorsionEquiv S K).symm u : (S.integer K)ˣ) : S.integer K) : K) =
      algebraMap R K (u : Rˣ) := by
  simp [unitsIntegerTorsionEquiv]

end Set
