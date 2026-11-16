/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.IndEtale
public import TauCeti.RingTheory.Henselization.Local
public import TauCeti.RingTheory.Henselization.Residue
public import TauCeti.RingTheory.IsHenselization

/-!
# The ordinary henselization as a recognised henselization

For a maximal ideal `I` of a commutative ring `R`, any surjective `R`-algebra map from `R ⧸ I`
onto a field `L` composed with `Henselization.toQuotient I : algebra I →ₐ[R] R ⧸ I` exhibits
`Henselization.algebra I` as a henselization of `R` at `L` (`isHenselization_comp_toQuotient`),
and any lift produced by `IsHenselization.lift` out of `algebra I` agrees with
`Henselization.lift` (`isHenselizationLift_eq_lift`).

Specialising to a local ring `R` and `I = maximalIdeal R`, the canonical residue map
`toResidueField R : algebra (maximalIdeal R) →ₐ[R] ResidueField R` is an instance of
`TauCeti.IsHenselization` (`isHenselization_toResidueField`) whose induced residue-field
equivalence agrees with `(residueFieldEquiv R).symm`
(`isHenselizationResidueFieldEquiv_toResidueField`). When `R` is already Henselian local, the
recognition isomorphism `IsHenselization.algEquiv` agrees with
`Henselization.algEquivOfHenselianRing` (`algEquiv_toResidueField_eq`).

## Main declarations

* `TauCeti.Henselization.isHenselization_comp_toQuotient`: for a maximal ideal `I`, composing
  `toQuotient I` with a surjective `R`-algebra map onto a field gives an `IsHenselization`.
* `TauCeti.Henselization.isHenselizationLift_eq_lift`: lifts out of `algebra I` produced by
  `IsHenselization.lift` agree with `Henselization.lift`.
* `TauCeti.Henselization.isHenselization_toResidueField`: `toResidueField R` satisfies
  `IsHenselization`.
* `TauCeti.Henselization.isHenselizationResidueFieldEquiv_toResidueField`: reconciles
  `IsHenselization.residueFieldEquiv (toResidueField R)` with `(residueFieldEquiv R).symm`.
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

/-- When `I` is a maximal ideal of `R` and `φ : R ⧸ I →ₐ[R] L` is a surjective `R`-algebra map onto
a field `L`, the composite `φ ∘ toQuotient I` exhibits `algebra I` as a henselization of `R` at
`L`. -/
theorem isHenselization_comp_toQuotient [I.IsMaximal] {L : Type w} [Field L] [Algebra R L]
    (φ : (R ⧸ I) →ₐ[R] L) (hφ : Function.Surjective φ) :
    IsHenselization (φ.comp (toQuotient I)) where
  henselianLocalRing := inferInstance
  indEtale := inferInstance
  surjective := hφ.comp (toQuotient_surjective I)

variable {I} in
/-- Whenever a Henselian local `R`-algebra `S` carries `I.map (algebraMap R S)` into
`maximalIdeal S`, the map `IsHenselization.lift ψ hχ` out of `algebra I` agrees with
`Henselization.lift`. -/
theorem isHenselizationLift_eq_lift {S : Type v} {L : Type w} [CommRing S] [Algebra R S]
    [HenselianLocalRing S] [Field L] [Algebra R L]
    (hIS : I.map (algebraMap R S) ≤ maximalIdeal S)
    (ψ : algebra I →ₐ[R] L) {χ : S →ₐ[R] L} (hχ : Function.Surjective χ) :
    IsHenselization.lift ψ hχ = lift hIS :=
  eq_lift hIS _

end Ideal

section IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- For any local ring `R`, the henselization `algebra (maximalIdeal R)` equipped with
`toResidueField R` is a henselization of `R` at `ResidueField R` in the sense of
`TauCeti.IsHenselization`. -/
@[stacks 04GQ "ordinary henselization of a local ring"]
instance isHenselization_toResidueField : IsHenselization (toResidueField R) where
  henselianLocalRing := inferInstance
  indEtale := inferInstance
  surjective := toResidueField_surjective R

/-- The residue-field equivalence `IsHenselization.residueFieldEquiv (toResidueField R)` agrees
with `(residueFieldEquiv R).symm`. -/
@[simp]
theorem isHenselizationResidueFieldEquiv_toResidueField :
    IsHenselization.residueFieldEquiv (toResidueField R) = (residueFieldEquiv R).symm :=
  AlgEquiv.ext fun x ↦ by
    obtain ⟨a, rfl⟩ := residue_surjective x
    simp

end IsLocalRing

/-- If `R` is already a Henselian local ring, the recognition isomorphism `IsHenselization.algEquiv`
comparing `toResidueField R` with `Algebra.ofId R (ResidueField R)` agrees with
`algEquivOfHenselianRing (maximalIdeal R)`. -/
theorem algEquiv_toResidueField_eq (R : Type u) [CommRing R] [HenselianLocalRing R] :
    IsHenselization.algEquiv (toResidueField R) (Algebra.ofId R (ResidueField R)) =
      algEquivOfHenselianRing (maximalIdeal R) :=
  (IsHenselization.eq_algEquiv (eq_toResidueField R _)).symm

end TauCeti.Henselization
