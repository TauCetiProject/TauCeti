/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree

/-!
# Elliptic function fields

An algebraic function field `F / k` is *elliptic* when it has genus one and carries a divisor of
degree one.  The degree-one divisor belongs to the definition and is not a consequence of the
genus: it is what Riemann–Roch converts into a place of degree one, and nothing about a
genus-one function field over a general constant field produces one.

This file proves the basic dictionary of an elliptic function field over an exact constant
field.  A divisor of degree one is linearly equivalent to exactly one place of degree one, so an
elliptic function field has a place of degree one; and once a place `P₀` of degree one is
chosen, `P ↦ [P - P₀]` is a bijection from the places of degree one onto the degree-zero divisor
class group `Cl⁰(F)`.  The addition of `Cl⁰(F)` transported along that bijection is the
intrinsic group law of the degree-one places: it makes the bijection an isomorphism of groups,
and `P ⊕ Q = R` exactly when the divisors `P + Q` and `R + P₀` are linearly equivalent.  The
transported group depends on the choice of `P₀`, so it is a definition, not an instance.

## Main definitions

* `TauCeti.IsEllipticFunctionField`: genus one together with a divisor of degree one.
* `TauCeti.Place.degreeOneEquivDegreeZeroClassGroup`: the bijection `P ↦ [P - P₀]` from the
  degree-one places of a genus-one function field onto `Cl⁰(F)`.
* `TauCeti.Place.degreeOneAddCommGroup` and
  `TauCeti.Place.degreeOneAddEquivDegreeZeroClassGroup`: the addition of `Cl⁰(F)` transported
  along that bijection, and the bijection read as an isomorphism of groups.

## Main results

* `TauCeti.Divisor.exists_linearlyEquivalent_ofPoint_of_genus_eq_one` and
  `TauCeti.Place.eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one`: in genus one a divisor of
  degree one is linearly equivalent to exactly one place of degree one.
* `TauCeti.IsEllipticFunctionField.exists_place_degree_eq_one`: an elliptic function field has
  a place of degree one;
  `TauCeti.isEllipticFunctionField_iff_genus_eq_one_and_exists_place_degree_eq_one` is the
  converse.
* `TauCeti.Place.degreeOneAddCommGroup_add_eq_iff`: the group law of the degree-one places,
  `P ⊕ Q = R ↔ P + Q ∼ R + P₀`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section VI.1: Definition 6.1.1, Proposition 6.1.6 and Proposition 6.1.7.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- An **elliptic function field** (Stichtenoth, Definition 6.1.1): this predicate records the
two conditions of the definition, genus one and the existence of a divisor of degree one.

Being an algebraic function field is *not* part of the predicate: the hypothesis
`TauCeti.IsFunctionField`, like the exactness of the constant field, is kept as a separate
hypothesis on the statements that need it, as everywhere in this development. -/
structure IsEllipticFunctionField (k F : Type*) [Field k] [Field F] [Algebra k F] : Prop where
  /-- An elliptic function field has genus one. -/
  genus_eq_one : genus k F = 1
  /-- An elliptic function field carries a divisor of degree one. -/
  exists_divisor_degree_eq_one : ∃ D : Divisor k F, Divisor.degree D = 1

/-! ### Degree-one divisors and degree-one places -/

/-- **A divisor of degree one with a nonzero Riemann–Roch space is linearly equivalent to a place
of degree one**: this is the genus-free half of Stichtenoth, Proposition 6.1.6(a).  A nonzero
`L(D)` puts an effective divisor in the class of `D`, and an effective divisor of degree one is
the prime divisor of a place of degree one. -/
theorem Divisor.exists_linearlyEquivalent_ofPoint_of_degree_eq_one (hF : IsFunctionField k F)
    {D : Divisor k F} (hD : Divisor.degree D = 1) (hne : riemannRochSpace D ≠ ⊥) :
    ∃ P : Place k F, P.degree = 1 ∧
      (Place.orderSystem hF).LinearlyEquivalent D (WeilDivisor.ofPoint P) := by
  obtain ⟨E, hE, hlin⟩ := (riemannRochSpace_ne_bot_iff hF).mp hne
  obtain ⟨P, hP, rfl⟩ := Divisor.exists_eq_ofPoint_of_degree_eq_one hF hE
    (by rw [← Divisor.degree_eq_of_linearlyEquivalent hF hlin, hD])
  exact ⟨P, hP, hlin⟩

/-- **A divisor of degree one of a genus-one function field is linearly equivalent to a place of
degree one** (Stichtenoth, Proposition 6.1.6(a)): in genus one Riemann–Roch gives `ℓ(D) = 1`, so
`L(D)` is nonzero. -/
theorem Divisor.exists_linearlyEquivalent_ofPoint_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {D : Divisor k F}
    (hD : Divisor.degree D = 1) :
    ∃ P : Place k F, P.degree = 1 ∧
      (Place.orderSystem hF).LinearlyEquivalent D (WeilDivisor.ofPoint P) := by
  have hdim : (Divisor.dim D : ℤ) = 1 := by
    rw [Divisor.dim_eq_degree_of_genus_eq_one hF hex hg (by rw [hD]; norm_num), hD]
  exact Divisor.exists_linearlyEquivalent_ofPoint_of_degree_eq_one hF hD
    ((Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF D).mp (by omega))

/-- **Linearly equivalent places of degree one of a genus-one function field are equal**
(Stichtenoth, Proposition 6.1.6(b)): over an exact constant field `ℓ(P) = 1` forces the complete
linear system of `P` to be the single divisor `P`. -/
theorem Place.eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P Q : Place k F} (hP : P.degree = 1)
    (h : (Place.orderSystem hF).LinearlyEquivalent
      (WeilDivisor.ofPoint P) (WeilDivisor.ofPoint Q)) :
    P = Q := by
  have hdim : Divisor.dim (WeilDivisor.ofPoint P : Divisor k F) = 1 := by
    have := Divisor.dim_eq_degree_of_genus_eq_one hF hex hg
      (D := (WeilDivisor.ofPoint P : Divisor k F)) (by rw [Divisor.degree_ofPoint, hP]; norm_num)
    rw [Divisor.degree_ofPoint, hP] at this
    exact_mod_cast this
  exact WeilDivisor.ofPoint_injective (Divisor.eq_of_linearlyEquivalent_of_dim_eq_one hF hex
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P))
    (WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint Q)) hdim h)

/-! ### Places of degree one -/

/-- **An elliptic function field has a place of degree one** (Stichtenoth,
Proposition 6.1.6(a)). -/
theorem IsEllipticFunctionField.exists_place_degree_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (he : IsEllipticFunctionField k F) :
    ∃ P : Place k F, P.degree = 1 := by
  obtain ⟨D, hD⟩ := he.exists_divisor_degree_eq_one
  obtain ⟨P, hP, -⟩ := Divisor.exists_linearlyEquivalent_ofPoint_of_genus_eq_one hF hex
    he.genus_eq_one hD
  exact ⟨P, hP⟩

/-- Over an exact constant field, a function field is elliptic exactly when it has genus one and
a place of degree one. -/
theorem isEllipticFunctionField_iff_genus_eq_one_and_exists_place_degree_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    IsEllipticFunctionField k F ↔ genus k F = 1 ∧ ∃ P : Place k F, P.degree = 1 := by
  refine ⟨fun he ↦ ⟨he.genus_eq_one, he.exists_place_degree_eq_one hF hex⟩, fun ⟨hg, P, hP⟩ ↦
    ⟨hg, WeilDivisor.ofPoint P, ?_⟩⟩
  rw [Divisor.degree_ofPoint, hP]
  norm_num

/-! ### The degree-one places as the degree-zero divisor class group -/

namespace Place

variable {P₀ : Place k F}

/-- **Distinct places of degree one of a genus-one function field have distinct classes**
relative to a base place. -/
theorem eq_of_divisorClass_pointDifference_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P Q : Place k F} (hP : P.degree = 1)
    (h : (Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference P P₀) =
      (Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference Q P₀)) :
    P = Q := by
  refine eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one hF hex hg hP ?_
  have hdiff : WeilDivisor.pointDifference P P₀ - WeilDivisor.pointDifference Q P₀ =
      WeilDivisor.ofPoint P - WeilDivisor.ofPoint Q := by
    rw [WeilDivisor.pointDifference, WeilDivisor.pointDifference]
    abel
  rw [WeilDivisor.OrderSystem.divisorClass_eq_iff,
    WeilDivisor.OrderSystem.linearlyEquivalent_iff, hdiff] at h
  exact ((Place.orderSystem hF).linearlyEquivalent_iff).mpr h

/-- **Every degree-zero divisor class of a genus-one function field is the class of a difference
of places of degree one** (Stichtenoth, Proposition 6.1.6(b)). -/
theorem exists_degree_eq_one_and_divisorClass_pointDifference_eq (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1)
    {c : (Place.orderSystem hF).ClassGroup} (hc : Divisor.degreeClass hF c = 0) :
    ∃ P : Place k F, P.degree = 1 ∧
      (Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference P P₀) = c := by
  obtain ⟨D, rfl⟩ := (Place.orderSystem hF).divisorClass_surjective c
  rw [Divisor.degreeClass_divisorClass] at hc
  obtain ⟨P, hP, hlin⟩ := Divisor.exists_linearlyEquivalent_ofPoint_of_genus_eq_one hF hex hg
    (D := D + WeilDivisor.ofPoint P₀) (by rw [Divisor.degree_add, Divisor.degree_ofPoint, hc,
      hP₀, Nat.cast_one, zero_add])
  refine ⟨P, hP, ?_⟩
  rw [WeilDivisor.OrderSystem.divisorClass_eq_iff, WeilDivisor.OrderSystem.linearlyEquivalent_iff]
  have hdiff : WeilDivisor.pointDifference P P₀ - D =
      -(D + WeilDivisor.ofPoint P₀ - WeilDivisor.ofPoint P) := by
    rw [WeilDivisor.pointDifference]
    abel
  rw [hdiff]
  exact (Place.orderSystem hF).principalSubgroup.neg_mem
    (((Place.orderSystem hF).linearlyEquivalent_iff).mp hlin)

/-- **The places of degree one of an elliptic function field are the degree-zero divisor
classes** (Stichtenoth, Proposition 6.1.6(b)): relative to a chosen place `P₀` of degree one,
`P ↦ [P - P₀]` is a bijection onto `Cl⁰(F)`. -/
noncomputable def degreeOneEquivDegreeZeroClassGroup (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1) :
    {P : Place k F // P.degree = 1} ≃ (Divisor.degreeClass hF).ker :=
  Equiv.ofBijective
    (fun P ↦ ⟨(Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference P.1 P₀), by
      rw [AddMonoidHom.mem_ker, Divisor.degreeClass_divisorClass, WeilDivisor.pointDifference,
        Divisor.degree_sub, Divisor.degree_ofPoint, Divisor.degree_ofPoint, P.2, hP₀, sub_self]⟩)
    ⟨fun P Q h ↦ Subtype.ext (eq_of_divisorClass_pointDifference_eq hF hex hg P.2
        (congrArg Subtype.val h)),
      fun c ↦ by
        obtain ⟨P, hP, hc⟩ := exists_degree_eq_one_and_divisorClass_pointDifference_eq hF hex hg hP₀
          (c := (c : (Place.orderSystem hF).ClassGroup)) c.2
        exact ⟨⟨P, hP⟩, Subtype.ext hc⟩⟩

/-- The class attached to a degree-one place by the bijection onto `Cl⁰(F)`. -/
@[simp]
theorem val_degreeOneEquivDegreeZeroClassGroup_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1)
    (P : {P : Place k F // P.degree = 1}) :
    (degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀ P : (Place.orderSystem hF).ClassGroup) =
      (Place.orderSystem hF).divisorClass (WeilDivisor.pointDifference P.1 P₀) := by
  -- the bijection is `Equiv.ofBijective` applied to this function; unfold it to see that.
  rw [degreeOneEquivDegreeZeroClassGroup]
  rfl

/-- The base place is the zero of the group law. -/
@[simp]
theorem degreeOneEquivDegreeZeroClassGroup_base (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1) :
    degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀ ⟨P₀, hP₀⟩ = 0 :=
  Subtype.ext (by rw [val_degreeOneEquivDegreeZeroClassGroup_apply,
    WeilDivisor.pointDifference_self, map_zero, ZeroMemClass.coe_zero])

/-- **Addition of the classes of two degree-one places** (Stichtenoth, Proposition 6.1.7): the
images of `P` and `Q` in `Cl⁰(F)` add up to the image of `R` exactly when the divisors `P + Q`
and `R + P₀` are linearly equivalent. -/
theorem degreeOneEquivDegreeZeroClassGroup_add_eq_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1)
    (P Q R : {P : Place k F // P.degree = 1}) :
    degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀ P +
        degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀ Q =
      degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀ R ↔
      (Place.orderSystem hF).LinearlyEquivalent
        (WeilDivisor.ofPoint P.1 + WeilDivisor.ofPoint Q.1)
        (WeilDivisor.ofPoint R.1 + WeilDivisor.ofPoint P₀) := by
  rw [Subtype.ext_iff, AddMemClass.coe_add, val_degreeOneEquivDegreeZeroClassGroup_apply,
    val_degreeOneEquivDegreeZeroClassGroup_apply, val_degreeOneEquivDegreeZeroClassGroup_apply,
    ← map_add, WeilDivisor.OrderSystem.divisorClass_eq_iff,
    WeilDivisor.OrderSystem.linearlyEquivalent_iff,
    WeilDivisor.OrderSystem.linearlyEquivalent_iff]
  have hdiff : WeilDivisor.pointDifference P.1 P₀ + WeilDivisor.pointDifference Q.1 P₀ -
      WeilDivisor.pointDifference R.1 P₀ =
      WeilDivisor.ofPoint P.1 + WeilDivisor.ofPoint Q.1 -
        (WeilDivisor.ofPoint R.1 + WeilDivisor.ofPoint P₀) := by
    rw [WeilDivisor.pointDifference, WeilDivisor.pointDifference, WeilDivisor.pointDifference]
    abel
  rw [hdiff]

/-- **The group law of the degree-one places of an elliptic function field** (Stichtenoth,
Proposition 6.1.7): the addition of `Cl⁰(F)` transported along the bijection
`P ↦ [P - P₀]`.  It depends on the base place `P₀`, so it is a definition and not an instance;
`TauCeti.Place.degreeOneAddCommGroup_add_eq_iff` characterises it by linear equivalence. -/
@[instance_reducible]
noncomputable def degreeOneAddCommGroup (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1) :
    AddCommGroup {P : Place k F // P.degree = 1} :=
  (degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀).addCommGroup

/-- **The degree-one places of an elliptic function field are the group `Cl⁰(F)`** (Stichtenoth,
Proposition 6.1.7): for the transported addition, `P ↦ [P - P₀]` is an isomorphism of groups. -/
noncomputable def degreeOneAddEquivDegreeZeroClassGroup (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1) :
    letI := degreeOneAddCommGroup hF hex hg hP₀
    {P : Place k F // P.degree = 1} ≃+ (Divisor.degreeClass hF).ker :=
  (degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀).addEquiv

/-- The isomorphism of groups is the underlying bijection. -/
@[simp]
theorem degreeOneAddEquivDegreeZeroClassGroup_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1)
    (P : {P : Place k F // P.degree = 1}) :
    degreeOneAddEquivDegreeZeroClassGroup hF hex hg hP₀ P =
      degreeOneEquivDegreeZeroClassGroup hF hex hg hP₀ P := by
  -- the isomorphism is `Equiv.addEquiv` applied to the bijection; unfold it to see that.
  rw [degreeOneAddEquivDegreeZeroClassGroup]
  exact Equiv.addEquiv_apply _ P

/-- The zero of the transported group law is the base place. -/
@[simp]
theorem degreeOneAddCommGroup_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1) :
    letI := degreeOneAddCommGroup hF hex hg hP₀
    (0 : {P : Place k F // P.degree = 1}) = ⟨P₀, hP₀⟩ := by
  let := degreeOneAddCommGroup hF hex hg hP₀
  apply (degreeOneAddEquivDegreeZeroClassGroup hF hex hg hP₀).injective
  rw [map_zero, degreeOneAddEquivDegreeZeroClassGroup_apply,
    degreeOneEquivDegreeZeroClassGroup_base]

/-- **The group law of the degree-one places is linear equivalence of divisors** (Stichtenoth,
Proposition 6.1.7): `P ⊕ Q = R` exactly when `P + Q ∼ R + P₀`. -/
theorem degreeOneAddCommGroup_add_eq_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) (hP₀ : P₀.degree = 1)
    (P Q R : {P : Place k F // P.degree = 1}) :
    letI := degreeOneAddCommGroup hF hex hg hP₀
    P + Q = R ↔ (Place.orderSystem hF).LinearlyEquivalent
      (WeilDivisor.ofPoint P.1 + WeilDivisor.ofPoint Q.1)
      (WeilDivisor.ofPoint R.1 + WeilDivisor.ofPoint P₀) := by
  let := degreeOneAddCommGroup hF hex hg hP₀
  rw [← (degreeOneAddEquivDegreeZeroClassGroup hF hex hg hP₀).injective.eq_iff, map_add,
    degreeOneAddEquivDegreeZeroClassGroup_apply, degreeOneAddEquivDegreeZeroClassGroup_apply,
    degreeOneAddEquivDegreeZeroClassGroup_apply,
    degreeOneEquivDegreeZeroClassGroup_add_eq_iff]

end Place

end TauCeti
