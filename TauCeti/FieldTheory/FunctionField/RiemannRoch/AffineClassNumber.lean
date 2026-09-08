/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.AffineModel
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.ClassNumber

/-!
# The ideal class group of an affine model of a function field

`TauCeti.FieldTheory.FunctionField.RiemannRoch.ClassNumber` proves that the degree-zero divisor
class group `Cl⁰(F)` of an algebraic function field with a *finite* constant field is finite, and
`TauCeti.FieldTheory.FunctionField.Divisor.AffineModel` exhibits the ideal class group of an
affine model `R` of `F / k` as a quotient of the full divisor class group,

`⟨[P] : P ∤ R⟩ → Cl(F) → ClassGroup R → 0`.

This file joins the two: **the ideal class group of every affine model of an algebraic function
field with a finite constant field is finite.**

The transfer is not immediate, because `Cl(F)` itself is infinite — the degree map
`deg : Cl(F) → ℤ` has finite kernel `Cl⁰(F)` but nonzero image.  What kills the degree is that a
model always has a place `P` at infinity (`TauCeti.Place.exists_algebraMap_notMem_integers`),
whose class dies in `ClassGroup R`.  Correcting a preimage by a multiple of `[P]` therefore moves
its degree into `[0, deg P)` without changing its image, so `ClassGroup R` is the image of the
divisor classes of degree `0, …, deg P − 1`, of which there are finitely many because each degree
fibre is empty or a coset of the finite group `Cl⁰(F)`.

Only the finiteness of `Cl⁰(F)` enters, so that is the hypothesis the results below take; over a
finite constant field `TauCeti.Divisor.finite_ker_degreeClass` supplies it.

There is no separability hypothesis and no chosen rational subfield: `R` is any Dedekind
`k`-subalgebra of `F` with fraction field `F`.  Mathlib's
`FunctionField.RingOfIntegers.instFintypeClassGroup` is the special case where `R` is the
integral closure of `𝔽_q[X]` in `F`, and it is proved by a different route (Minkowski-style
counting through `ClassGroup.fintypeOfAdmissibleOfFinite`) under the extra hypothesis that `F` is
separable over `𝔽_q(X)`.

`TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc` runs the bridge on the rational function
field and its model `k[X]`, where it gives `Cl⁰(k(x)) = 0` and the class number `h = 1`.

## Main results

* `TauCeti.Divisor.finite_classGroup`: **the ideal class group of an affine model of an algebraic
  function field with a finite degree-zero class group is finite**; over a finite constant field
  this is the affine half of Stichtenoth's Proposition 5.1.3.
* `TauCeti.Divisor.card_classGroup_dvd_classNumber`: when some place infinite on the model is
  rational, the class number of the model divides the class number of `F / k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.4 and V.1.
-/

public section

open IsDedekindDomain

namespace TauCeti

open AlgebraicGeometry AlgebraicGeometry.WeilDivisor

universe u v w

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra k R] [Algebra R F]
  [IsScalarTower k R F] [IsFractionRing R F]

namespace Divisor

variable (R) in
/-- **The ideal class group of an affine model of an algebraic function field with a finite
degree-zero divisor class group is finite** — over a finite constant field, where
`TauCeti.Divisor.finite_ker_degreeClass` supplies `hker`, this is the affine half of Stichtenoth's
Proposition 5.1.3.  Every ideal class of the model comes from a divisor class whose degree lies in
`[0, deg P)` for a place `P` at infinity
(`TauCeti.Divisor.exists_degreeClass_mem_Ico_and_classGroupHom_eq`), and only finitely many
divisor classes have degree in that range.

No separability hypothesis and no chosen rational subfield are needed: `R` is an arbitrary
Dedekind `k`-subalgebra of `F` with fraction field `F`. -/
theorem finite_classGroup (hF : IsFunctionField k F) (hker : Finite (degreeClass hF).ker) :
    Finite (ClassGroup R) := by
  obtain ⟨P, hP⟩ := Place.exists_algebraMap_notMem_integers k F R hF
  have hfin : Finite (Additive (ClassGroup R)) := by
    refine Set.finite_univ_iff.mp (Set.Finite.subset
      (Set.Finite.image (classGroupHom R hF)
        (finite_preimage_degreeClass hF hker (Set.finite_Ico (0 : ℤ) (P.degree : ℤ))))
      fun x _ ↦ ?_)
    obtain ⟨c, hc, hcx⟩ := exists_degreeClass_mem_Ico_and_classGroupHom_eq R hF hP x
    exact ⟨c, hc, hcx⟩
  exact Finite.of_equiv _ (Additive.ofMul (α := ClassGroup R)).symm

variable (R) in
/-- **With a rational place at infinity, the class number of the model divides the class number of
`F / k`**: the ideal class group of the model is then a quotient of `Cl⁰(F)`
(`TauCeti.Divisor.classGroupHom_comp_subtype_surjective`).  The statement carries content when
`Cl⁰(F)` is finite, for instance over a finite constant field; otherwise `classNumber hF` is the
junk value `0` and the divisibility is vacuous. -/
theorem card_classGroup_dvd_classNumber (hF : IsFunctionField k F) {P : Place k F}
    (hP : ∃ r : R, algebraMap R F r ∉ P.integers) (hdeg : P.degree = 1) :
    Nat.card (ClassGroup R) ∣ classNumber hF := by
  rw [Nat.card_congr (Additive.ofMul (α := ClassGroup R)), classNumber_def]
  exact AddSubgroup.card_dvd_of_surjective _
    (classGroupHom_comp_subtype_surjective R hF hP hdeg)

end Divisor

end TauCeti
