/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.Elliptic.Basic

/-!
# `Pic⁰` of a curve of genus one

Let `X` be a proper integral curve over a field `k` whose codimension-one local rings are discrete
valuation rings, with `k` integrally closed in the function field `k(X)`, and suppose that `X` has
genus one, `dim_k H¹(X, 𝒪_X) = 1`. Fix a codimension-one point `x₀` of residue degree one, for
instance the image of a `k`-rational point. This file proves that the Abel–Jacobi map

`x ↦ [𝒪_X(x - x₀)]`

is a bijection from the codimension-one points of residue degree one onto the degree-zero part
`Pic⁰ X` of the Picard group, sending `x₀` to zero. Under it the group law of `Pic⁰ X` is read
on points by linear equivalence: the images of `x` and `y` add up to the image of `z` exactly when
the divisors `x + y` and `z + x₀` are linearly equivalent.

The two inputs are consequences of the Riemann–Roch theorem in genus one: a divisor of degree one
is linearly equivalent to exactly one point of residue degree one. They are transported from the
corresponding facts for elliptic function fields along the identification of codimension-one
points of `X` with the places of `k(X)` (`SchemeWeilDivisor.equivFunctionFieldDivisor`), which
preserves degrees and linear equivalence; the genus of `X` is the genus of `k(X)` by
`SchemeWeilDivisor.genus_eq_genus_functionField`.

## Main declarations

* `SchemeWeilDivisor.exists_linearlyEquivalent_ofPoint_of_genus_eq_one` and
  `SchemeWeilDivisor.eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one`: in genus one a divisor of
  degree one is linearly equivalent to exactly one point of residue degree one;
* `SchemeWeilDivisor.degreeOneEquivPicZero`: the bijection `x ↦ [𝒪_X(x - x₀)]` from the points of
  residue degree one onto `Pic⁰ X`, with `SchemeWeilDivisor.coe_degreeOneEquivPicZero_apply`;
* `SchemeWeilDivisor.degreeOneEquivPicZero_base` and
  `SchemeWeilDivisor.degreeOneEquivPicZero_add_eq_iff`: the base point goes to zero, and the group
  law of `Pic⁰ X` read on points.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009,
  Proposition III.3.4.
* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Propositions 6.1.6 and 6.1.7.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [hX : Fact (∀ y : X, coheight y ≤ 1)] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-! ### Divisors of degree one in genus one -/

section DegreeOne

/-- **A divisor of degree one on a curve of genus one is linearly equivalent to a point of residue
degree one.** Here `X` is a proper integral curve over `k` whose codimension-one local rings are
discrete valuation rings, with `k` integrally closed in `k(X)`. -/
theorem exists_linearlyEquivalent_ofPoint_of_genus_eq_one
    (hk : IsIntegrallyClosedIn k X.functionField) (hg : X.genus k = 1) {D : SchemeWeilDivisor X}
    (hD : relativeDegree (X ↘ Spec (.of k)) D = 1) :
    ∃ x : CodimensionOnePoint X, (X ↘ Spec (.of k)).residueDegree x = 1 ∧
      (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D (WeilDivisor.ofPoint x) := by
  -- A divisor of nonzero degree has a point in its support, so `X` has dimension one.
  obtain ⟨y, -⟩ : (Finsupp.support D).Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun h ↦ by simp [h] at hD
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
    (UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out y.2
  have hgF : genus k X.functionField = 1 :=
    (genus_eq_genus_functionField hex hX.out hF hk).symm.trans hg
  obtain ⟨P, hP, hlin⟩ := Divisor.exists_linearlyEquivalent_ofPoint_of_genus_eq_one hF hk hgF
    (D := equivFunctionFieldDivisor hex hX.out D) (by rw [degree_equivFunctionFieldDivisor, hD])
  have hPx : X.toPlace (k := k) ((CodimensionOnePoint.equivPlace hex hX.out).symm P : X) = P := by
    rw [← CodimensionOnePoint.equivPlace_apply (k := k) hex hX.out, Equiv.apply_symm_apply]
  refine ⟨(CodimensionOnePoint.equivPlace hex hX.out).symm P, ?_, ?_⟩
  · rw [← X.toPlace_degree_eq_residueDegree (k := k), hPx, hP]
  · rw [← linearlyEquivalent_equivFunctionFieldDivisor_iff hex hX.out hF,
      equivFunctionFieldDivisor_ofPoint, hPx]
    exact hlin

/-- **Linearly equivalent points of residue degree one on a curve of genus one are equal.** Here
`X` is a proper integral curve over `k` whose codimension-one local rings are discrete valuation
rings, with `k` integrally closed in `k(X)`, and only the point `x` is required to have residue
degree one. -/
theorem eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one
    (hk : IsIntegrallyClosedIn k X.functionField) (hg : X.genus k = 1) {x y : CodimensionOnePoint X}
    (hx : (X ↘ Spec (.of k)).residueDegree x = 1)
    (h : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent (WeilDivisor.ofPoint x)
      (WeilDivisor.ofPoint y)) :
    x = y := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
    (UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out x.2
  have hgF : genus k X.functionField = 1 :=
    (genus_eq_genus_functionField hex hX.out hF hk).symm.trans hg
  apply (CodimensionOnePoint.equivPlace hex hX.out).injective
  rw [CodimensionOnePoint.equivPlace_apply, CodimensionOnePoint.equivPlace_apply]
  refine Place.eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one hF hk hgF
    (by rw [X.toPlace_degree_eq_residueDegree, hx]) ?_
  rw [← equivFunctionFieldDivisor_ofPoint hex hX.out,
    ← equivFunctionFieldDivisor_ofPoint hex hX.out,
    linearlyEquivalent_equivFunctionFieldDivisor_iff hex hX.out hF]
  exact h

end DegreeOne

/-! ### The points of residue degree one as `Pic⁰ X` -/

section PicZero

variable {x₀ : CodimensionOnePoint X} (hx₀ : (X ↘ Spec (.of k)).residueDegree x₀ = 1)

/-- The Abel–Jacobi class `[x - x₀]` of a point, as a class of degree-zero divisors. -/
private abbrev abelJacobiClass (x : CodimensionOnePoint X) :
    (WeilDivisor.OrderSystem.ofScheme X).picZero
      (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
      (isWeightedDegreeZero_residueDegree k hX.out) :=
  (WeilDivisor.OrderSystem.ofScheme X).weightedAbelJacobiClass _
    (isWeightedDegreeZero_residueDegree k hX.out) (x₀ := x₀) (by simp [hx₀]) x

/-- At a point of residue degree one, the Abel–Jacobi class is the class of `x - x₀`. -/
private lemma coe_abelJacobiClass {x : CodimensionOnePoint X}
    (hx : (X ↘ Spec (.of k)).residueDegree x = 1) :
    (abelJacobiClass k hx₀ x : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass (WeilDivisor.pointDifference x x₀) := by
  rw [WeilDivisor.OrderSystem.coe_weightedAbelJacobiClass,
    WeilDivisor.weightedPointBaseDifference_eq_pointDifference_of_weight_eq_one (by simp [hx])]

/-- Equality in the degree-zero class group is linear equivalence of divisor representatives. -/
private lemma picZero_eq_iff_linearlyEquivalent
    {d e : (WeilDivisor.OrderSystem.ofScheme X).picZero
      (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
      (isWeightedDegreeZero_residueDegree k hX.out)}
    {D E : SchemeWeilDivisor X}
    (hd : (d : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass D)
    (he : (e : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) =
      (WeilDivisor.OrderSystem.ofScheme X).divisorClass E) :
    d = e ↔ (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E := by
  rw [Subtype.ext_iff, hd, he, WeilDivisor.OrderSystem.divisorClass_eq_iff]

/-- The sum of two Abel–Jacobi classes equals a third exactly when their point-difference
divisors are linearly equivalent. -/
private lemma abelJacobiClass_add_eq_iff_linearlyEquivalent
    (x y z : {x : CodimensionOnePoint X //
      (X ↘ Spec (.of k)).residueDegree x = 1}) :
    abelJacobiClass k hx₀ x + abelJacobiClass k hx₀ y = abelJacobiClass k hx₀ z ↔
      (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent
        (WeilDivisor.pointDifference x.1 x₀ + WeilDivisor.pointDifference y.1 x₀)
        (WeilDivisor.pointDifference z.1 x₀) := by
  exact picZero_eq_iff_linearlyEquivalent k (by
    rw [AddMemClass.coe_add, coe_abelJacobiClass k hx₀ x.2,
      coe_abelJacobiClass k hx₀ y.2, map_add]) (coe_abelJacobiClass k hx₀ z.2)

variable (hk : IsIntegrallyClosedIn k X.functionField) (hg : X.genus k = 1)
include hk hg

/-- In genus one, distinct points of residue degree one have distinct Abel–Jacobi classes. -/
private lemma injective_abelJacobiClass :
    Function.Injective fun x : {x : CodimensionOnePoint X //
      (X ↘ Spec (.of k)).residueDegree x = 1} ↦ abelJacobiClass k hx₀ x := by
  intro x y hxy
  have hlin := (picZero_eq_iff_linearlyEquivalent k
    (coe_abelJacobiClass k hx₀ x.2) (coe_abelJacobiClass k hx₀ y.2)).mp hxy
  have hdiff : WeilDivisor.pointDifference x.1 x₀ - WeilDivisor.pointDifference y.1 x₀ =
      WeilDivisor.ofPoint x.1 - WeilDivisor.ofPoint y.1 := by
    simp only [WeilDivisor.pointDifference]
    abel
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff, hdiff,
    ← WeilDivisor.OrderSystem.linearlyEquivalent_iff] at hlin
  exact Subtype.ext (eq_of_linearlyEquivalent_ofPoint_of_genus_eq_one k hk hg x.2 hlin)

/-- In genus one, every degree-zero divisor class is the Abel–Jacobi class of a point of residue
degree one: if `D` has degree zero, then `D + x₀` is linearly equivalent to a point `x`, so that
`D ∼ x - x₀`. -/
private lemma surjective_abelJacobiClass :
    Function.Surjective fun x : {x : CodimensionOnePoint X //
      (X ↘ Spec (.of k)).residueDegree x = 1} ↦ abelJacobiClass k hx₀ x := by
  intro d
  obtain ⟨D, hD⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective
    (d : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup)
  have hdeg : relativeDegree (X ↘ Spec (.of k)) D = 0 := by
    have := d.2
    rwa [← hD, WeilDivisor.OrderSystem.divisorClass_mem_picZero,
      WeilDivisor.weightedDegree_apply, ← relativeDegree_apply] at this
  obtain ⟨x, hx, hlin⟩ := exists_linearlyEquivalent_ofPoint_of_genus_eq_one k hk hg
    (D := D + WeilDivisor.ofPoint x₀) (by
      rw [map_add, relativeDegree_ofPoint, hdeg, hx₀, Nat.cast_one, zero_add])
  refine ⟨⟨x, hx⟩, ?_⟩
  apply (picZero_eq_iff_linearlyEquivalent k
    (coe_abelJacobiClass k hx₀ hx) hD.symm).mpr
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff]
  have hdiff : WeilDivisor.pointDifference x x₀ - D =
      WeilDivisor.ofPoint x - (D + WeilDivisor.ofPoint x₀) := by
    rw [WeilDivisor.pointDifference]
    abel
  rw [hdiff, ← WeilDivisor.OrderSystem.linearlyEquivalent_iff]
  exact hlin.symm

/-- In genus one, `x ↦ [𝒪_X(x - x₀)]` is a bijection from the points of residue degree one onto
`Pic⁰ X`. -/
private lemma bijective_abelJacobiPicZero :
    Function.Bijective fun x : {x : CodimensionOnePoint X //
      (X ↘ Spec (.of k)).residueDegree x = 1} ↦
        classGroupPicZeroAddEquivPicZero k X (abelJacobiClass k hx₀ x) :=
  (classGroupPicZeroAddEquivPicZero k X).bijective.comp
    ⟨injective_abelJacobiClass k hx₀ hk hg, surjective_abelJacobiClass k hx₀ hk hg⟩

/-- **The points of residue degree one of a curve of genus one form `Pic⁰`.** On a proper integral
curve of genus one over `k` whose codimension-one local rings are discrete valuation rings, with
`k` integrally closed in `k(X)` and a base point `x₀` of residue degree one, the Abel–Jacobi map
`x ↦ [𝒪_X(x - x₀)]` is a bijection from the codimension-one points of residue degree one onto
`Pic⁰ X`. -/
def degreeOneEquivPicZero :
    {x : CodimensionOnePoint X // (X ↘ Spec (.of k)).residueDegree x = 1} ≃
      LineBundleClass.picZero k X :=
  Equiv.ofBijective _ (bijective_abelJacobiPicZero k hx₀ hk hg)

/-- The class attached to a point `x` by `SchemeWeilDivisor.degreeOneEquivPicZero` is the class of
the line bundle `𝒪_X(x - x₀)`. -/
@[simp]
theorem coe_degreeOneEquivPicZero_apply
    (x : {x : CodimensionOnePoint X // (X ↘ Spec (.of k)).residueDegree x = 1}) :
    (degreeOneEquivPicZero k hx₀ hk hg x : Additive (LineBundleClass X)) =
      Additive.ofMul (toLineBundleClass hX.out (WeilDivisor.pointDifference x.1 x₀)) := by
  change (classGroupPicZeroAddEquivPicZero k X (abelJacobiClass k hx₀ x) :
    Additive (LineBundleClass X)) = _
  rw [coe_classGroupPicZeroAddEquivPicZero_apply,
    coe_abelJacobiClass k hx₀ x.2, classGroupAddEquivLineBundleClass_apply,
    classGroupToLineBundleClass_divisorClass]

/-- The base point goes to zero in `Pic⁰ X`. -/
@[simp]
theorem degreeOneEquivPicZero_base : degreeOneEquivPicZero k hx₀ hk hg ⟨x₀, hx₀⟩ = 0 := by
  rw [degreeOneEquivPicZero, Equiv.ofBijective_apply, abelJacobiClass,
    WeilDivisor.OrderSystem.weightedAbelJacobiClass_base, map_zero]

/-- **The group law of `Pic⁰ X` on the points of residue degree one.** The classes of `x` and `y`
add up to the class of `z` exactly when the divisors `x + y` and `z + x₀` are linearly
equivalent. -/
theorem degreeOneEquivPicZero_add_eq_iff
    (x y z : {x : CodimensionOnePoint X // (X ↘ Spec (.of k)).residueDegree x = 1}) :
    degreeOneEquivPicZero k hx₀ hk hg x + degreeOneEquivPicZero k hx₀ hk hg y =
        degreeOneEquivPicZero k hx₀ hk hg z ↔
      (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent
        (WeilDivisor.ofPoint x.1 + WeilDivisor.ofPoint y.1)
        (WeilDivisor.ofPoint z.1 + WeilDivisor.ofPoint x₀) := by
  change classGroupPicZeroAddEquivPicZero k X (abelJacobiClass k hx₀ x) +
      classGroupPicZeroAddEquivPicZero k X (abelJacobiClass k hx₀ y) =
      classGroupPicZeroAddEquivPicZero k X (abelJacobiClass k hx₀ z) ↔ _
  rw [← map_add, (classGroupPicZeroAddEquivPicZero k X).injective.eq_iff,
    abelJacobiClass_add_eq_iff_linearlyEquivalent k hx₀ x y z,
    WeilDivisor.OrderSystem.linearlyEquivalent_iff,
    WeilDivisor.OrderSystem.linearlyEquivalent_iff]
  have hdiff : WeilDivisor.pointDifference x.1 x₀ + WeilDivisor.pointDifference y.1 x₀ -
      WeilDivisor.pointDifference z.1 x₀ =
      WeilDivisor.ofPoint x.1 + WeilDivisor.ofPoint y.1 -
        (WeilDivisor.ofPoint z.1 + WeilDivisor.ofPoint x₀) := by
    rw [WeilDivisor.pointDifference, WeilDivisor.pointDifference, WeilDivisor.pointDifference]
    abel
  rw [hdiff]

end PicZero

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
