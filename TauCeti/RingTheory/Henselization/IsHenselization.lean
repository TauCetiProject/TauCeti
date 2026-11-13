/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.IndEtale
public import TauCeti.RingTheory.Henselization.Local
public import TauCeti.RingTheory.IsHenselization
import TauCeti.RingTheory.Henselization.Residue

/-!
# The ordinary henselization as a recognised henselization

For an ideal `I` of a commutative ring `R`, the quotient of `Henselization.algebra I` by its
extended ideal `extended I` is canonically `R`-isomorphic to `R ⧸ I` (`quotientEquiv`), giving a
canonical surjective `R`-algebra map `toQuotient I : algebra I →ₐ[R] R ⧸ I` with kernel
`extended I`. When `I` is maximal, any surjective `R`-algebra map from `R ⧸ I` onto a field `L`
exhibits `algebra I` as a henselization of `R` at `L` (`isHenselization_comp_toQuotient`).

Specialising to a local ring `R` and `I = maximalIdeal R`, the canonical residue map
`toResidueField R : algebra (maximalIdeal R) →ₐ[R] ResidueField R` is an instance of
`TauCeti.IsHenselization` (`isHenselization_toResidueField`). Moreover, maps out of
`algebra (maximalIdeal R)` produced by `IsHenselization.lift` agree with `Henselization.lift`, and
when `R` is already Henselian local, the recognition isomorphism `IsHenselization.algEquiv` agrees
with `Henselization.algEquivOfHenselianRing`.

## Main declarations

* `TauCeti.Henselization.quotientEquiv`, `TauCeti.Henselization.toQuotient`: the quotient
  identification `(R ⧸ I) ≃ₐ[R] (algebra I ⧸ extended I)` and canonical map `algebra I →ₐ[R] R ⧸ I`.
* `TauCeti.Henselization.isHenselization_comp_toQuotient`: for a maximal ideal `I`, composing
  `toQuotient I` with a surjective `R`-algebra map onto a field gives an `IsHenselization`.
* `TauCeti.Henselization.residueFieldEquiv`, `TauCeti.Henselization.toResidueField`: the residue
  identification `ResidueField R ≃ₐ[R] ResidueField (algebra (maximalIdeal R))` and canonical
  residue map `algebra (maximalIdeal R) →ₐ[R] ResidueField R` for a local ring `R`.
* `TauCeti.Henselization.isHenselization_toResidueField`: `toResidueField R` satisfies
  `IsHenselization`.
* `TauCeti.Henselization.algEquiv_toResidueField_eq`: for a Henselian local ring `R`, the
  recognition isomorphism `IsHenselization.algEquiv` agrees with `algEquivOfHenselianRing`.

## References

* [Stacks Project, Definition 10.155.3 (04GQ)](https://stacks.math.columbia.edu/tag/04GQ)
* [Stacks Project, Lemma 15.12.3 (0A03)](https://stacks.math.columbia.edu/tag/0A03)
-/

public section

open IsLocalRing

universe u v w

namespace TauCeti.Henselization

section Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The canonical `R`-algebra isomorphism `(R ⧸ I) ≃ₐ[R] (algebra I ⧸ extended I)` induced by the
structure map of the henselization. -/
noncomputable def quotientEquiv : (R ⧸ I) ≃ₐ[R] (algebra I ⧸ extended I) :=
  have he : ⇑(IsScalarTower.toAlgHom R (R ⧸ I) (algebra I ⧸ extended I)) =
      reducedMap I (algebra I) := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) (algebra I ⧸ extended I))
    (he ▸ quotient_bijective I)

/-- `quotientEquiv I` sends the class of `r` to the class of `algebraMap R (algebra I) r`. -/
@[simp]
theorem quotientEquiv_mk (r : R) :
    quotientEquiv I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (extended I) (algebraMap R (algebra I) r) := by
  simp [quotientEquiv]

/-- The canonical surjective `R`-algebra map `algebra I →ₐ[R] R ⧸ I` factoring the quotient map
modulo `extended I` through `(quotientEquiv I).symm`. -/
noncomputable def toQuotient : algebra I →ₐ[R] R ⧸ I :=
  (quotientEquiv I).symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (extended I))

/-- Composing `toQuotient I` with `quotientEquiv I` recovers the quotient map modulo
`extended I`. -/
@[simp]
theorem quotientEquiv_toQuotient (x : algebra I) :
    quotientEquiv I (toQuotient I x) = Ideal.Quotient.mk (extended I) x :=
  (quotientEquiv I).apply_symm_apply _

/-- `toQuotient I` is surjective. -/
theorem toQuotient_surjective : Function.Surjective (toQuotient I) :=
  (quotientEquiv I).symm.surjective.comp Ideal.Quotient.mk_surjective

/-- The kernel of `toQuotient I` is the extended ideal `extended I`. -/
@[simp]
theorem ker_toQuotient : RingHom.ker (toQuotient I) = extended I := by
  ext x
  rw [RingHom.mem_ker, ← (quotientEquiv I).map_eq_zero_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- `toQuotient I` is the unique `R`-algebra map `algebra I →ₐ[R] R ⧸ I`. -/
theorem eq_toQuotient (f : algebra I →ₐ[R] R ⧸ I) : f = toQuotient I :=
  algHom_ext_of_map_le_jacobson (by simp [Ideal.Quotient.algebraMap_eq])

/-- When `I` is a maximal ideal of `R` and `φ : R ⧸ I →ₐ[R] L` is a surjective `R`-algebra map onto
a field `L`, the composite `φ ∘ toQuotient I` exhibits `algebra I` as a henselization of `R` at
`L`. -/
theorem isHenselization_comp_toQuotient [I.IsMaximal] {L : Type w} [Field L] [Algebra R L]
    (φ : (R ⧸ I) →ₐ[R] L) (hφ : Function.Surjective φ) :
    IsHenselization (φ.comp (toQuotient I)) where
  henselianLocalRing := inferInstance
  indEtale := inferInstance
  surjective := hφ.comp (toQuotient_surjective I)

end Ideal

section IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- For a local ring `R`, the structure map of the henselization along `maximalIdeal R` induces an
`R`-algebra isomorphism between `ResidueField R` and `ResidueField (algebra (maximalIdeal R))`. -/
noncomputable def residueFieldEquiv :
    ResidueField R ≃ₐ[R] ResidueField (algebra (maximalIdeal R)) :=
  have he : ⇑(IsScalarTower.toAlgHom R (ResidueField R)
      (ResidueField (algebra (maximalIdeal R)))) =
      ResidueField.map (algebraMap R (algebra (maximalIdeal R))) := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField (algebra (maximalIdeal R))))
    (he ▸ residueField_map_bijective R)

/-- `residueFieldEquiv R` sends `residue R r` to the residue of `algebraMap R _ r`. -/
@[simp]
theorem residueFieldEquiv_residue (r : R) :
    residueFieldEquiv R (residue R r) =
      residue (algebra (maximalIdeal R)) (algebraMap R (algebra (maximalIdeal R)) r) :=
  (rfl)

/-- The canonical `R`-algebra map from the henselization of a local ring `R` onto `ResidueField R`,
obtained by composing the residue map of `algebra (maximalIdeal R)` with
`(residueFieldEquiv R).symm`. -/
noncomputable def toResidueField : algebra (maximalIdeal R) →ₐ[R] ResidueField R :=
  (residueFieldEquiv R).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (algebra (maximalIdeal R))
      (ResidueField (algebra (maximalIdeal R))))

/-- Applying `residueFieldEquiv R` after `toResidueField R` recovers the residue map of
`algebra (maximalIdeal R)`. -/
@[simp]
theorem residueFieldEquiv_toResidueField (x : algebra (maximalIdeal R)) :
    residueFieldEquiv R (toResidueField R x) = residue (algebra (maximalIdeal R)) x :=
  (residueFieldEquiv R).apply_symm_apply _

/-- `toResidueField R` is surjective. -/
theorem toResidueField_surjective : Function.Surjective (toResidueField R) :=
  (residueFieldEquiv R).symm.surjective.comp residue_surjective

/-- The kernel of `toResidueField R` is the maximal ideal of `algebra (maximalIdeal R)`. -/
@[simp]
theorem ker_toResidueField :
    RingHom.ker (toResidueField R) = maximalIdeal (algebra (maximalIdeal R)) :=
  IsLocalRing.ker_eq_maximalIdeal (toResidueField R).toRingHom (toResidueField_surjective R)

/-- `toResidueField R` is the unique `R`-algebra map
`algebra (maximalIdeal R) →ₐ[R] ResidueField R`. -/
theorem eq_toResidueField (f : algebra (maximalIdeal R) →ₐ[R] ResidueField R) :
    f = toResidueField R :=
  algHom_ext_of_map_le_jacobson <| Ideal.map_le_iff_le_comap.mpr fun _ hr ↦ by
    simp [ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr hr]

/-- For any local ring `R`, the henselization `algebra (maximalIdeal R)` equipped with
`toResidueField R` is a henselization of `R` at `ResidueField R` in the sense of
`TauCeti.IsHenselization`. -/
@[stacks 04GQ "ordinary henselization of a local ring"]
instance isHenselization_toResidueField : IsHenselization (toResidueField R) where
  henselianLocalRing := inferInstance
  indEtale := inferInstance
  surjective := toResidueField_surjective R

variable {R} in
/-- Whenever a Henselian local `R`-algebra `S` carries `(maximalIdeal R).map (algebraMap R S)` into
`maximalIdeal S`, the map `IsHenselization.lift ψ hχ` out of `algebra (maximalIdeal R)` agrees with
`Henselization.lift`. -/
theorem isHenselization_lift_eq_lift {S : Type v} {L : Type w} [CommRing S] [Algebra R S]
    [HenselianLocalRing S] [Field L] [Algebra R L]
    (hRS : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S)
    (ψ : algebra (maximalIdeal R) →ₐ[R] L) {χ : S →ₐ[R] L} (hχ : Function.Surjective χ) :
    IsHenselization.lift ψ hχ = lift hRS :=
  eq_lift hRS _

end IsLocalRing

/-- If `R` is already a Henselian local ring, the recognition isomorphism `IsHenselization.algEquiv`
comparing `toResidueField R` with `Algebra.ofId R (ResidueField R)` agrees with
`algEquivOfHenselianRing (maximalIdeal R)`. -/
theorem algEquiv_toResidueField_eq (R : Type u) [CommRing R] [HenselianLocalRing R] :
    IsHenselization.algEquiv (toResidueField R) (Algebra.ofId R (ResidueField R)) =
      algEquivOfHenselianRing (maximalIdeal R) :=
  (IsHenselization.eq_algEquiv (eq_toResidueField R _)).symm

end TauCeti.Henselization
