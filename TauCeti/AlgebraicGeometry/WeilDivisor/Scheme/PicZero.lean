/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Splitting
public import TauCeti.AlgebraicGeometry.WeilDivisor.PicZeroQuotient
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic

/-!
# The degree homomorphism on the Picard group, and `Pic⁰` of a curve

Let `X` be a proper integral curve over a field `k` whose codimension-one local rings are
discrete valuation rings and whose `H¹(X, 𝒪_X)` is finite-dimensional. Tensor product makes the
isomorphism classes of line bundles on `X` into the Picard group `Pic X`, and on it the
Euler-characteristic degree `deg L = χ(L) - χ(𝒪_X)` is additive. This file bundles that degree as
a homomorphism `Pic X →+ ℤ` and defines `Pic⁰ X`, the degree-zero part of the Picard group, as
its kernel.

`Pic⁰ X` is then compared with the divisor-side degree-zero class group. Under the isomorphism
`Cl(X) ≅ Pic X` of `TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Picard`, the degree of a line
bundle is the residue-degree-weighted degree `Σ_y D(y) [κ(y) : k]` of any divisor `D` of it, so
the two degree-zero subgroups correspond. Composing with the description of the abstract `Pic⁰`
as degree-zero divisors modulo principal divisors puts `Pic⁰ X` in the concrete form

`Pic⁰ X ≅ {D : deg D = 0} / {div f}`.

At a codimension-one point of residue degree one — for instance the image of a `k`-rational
point — the degree is surjective, so `Pic X ⧸ Pic⁰ X ≅ ℤ`.

## Main declarations

* `LineBundleClass.eulerDegreeHom`, the degree `Pic X →+ ℤ`, and `LineBundleClass.picZero`,
  the subgroup `Pic⁰ X` it cuts out;
* `SchemeWeilDivisor.eulerDegree_classGroupToLineBundleClass`: the degree of the line
  bundle of a divisor class is the weighted degree of that class;
* `SchemeWeilDivisor.classGroupPicZeroAddEquivPicZero`, the isomorphism `Cl⁰(X) ≅ Pic⁰(X)`, and
  `SchemeWeilDivisor.weightedDegreeZeroQuotientAddEquivPicZero`, which presents `Pic⁰ X` as the
  degree-zero divisors modulo the principal ones;
* `SchemeWeilDivisor.eulerDegreeHom_surjective` and
  `SchemeWeilDivisor.picQuotientPicZeroAddEquivInt`: at a point of residue degree one the degree
  is onto `ℤ`, so `Pic X ⧸ Pic⁰ X ≅ ℤ`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6 and Chapter IV, Section 1.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 7, Section 3.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [hX : Fact (∀ y : X, coheight y ≤ 1)] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

namespace LineBundleClass

variable (X) in
/-- The degree homomorphism `deg : Pic X →+ ℤ` of a proper curve over `k`, sending the class of a
line bundle `L` to `χ(L) - χ(𝒪_X)`. The Picard group is written additively, as `Additive` of the
tensor-product monoid of line-bundle classes. -/
def eulerDegreeHom : Additive (LineBundleClass X) →+ ℤ :=
  AddMonoidHom.mk' (fun a ↦ eulerDegree k a.toMul) fun a b ↦
    eulerDegree_mul k hX.out a.toMul b.toMul

/-- The degree homomorphism evaluates to the Euler-characteristic degree. -/
@[simp]
lemma eulerDegreeHom_apply (a : Additive (LineBundleClass X)) :
    eulerDegreeHom k X a = eulerDegree k a.toMul :=
  (rfl)

variable (X) in
/-- **`Pic⁰ X`**, the degree-zero part of the Picard group of a proper curve over `k`: the kernel
of the Euler-characteristic degree. -/
def picZero : AddSubgroup (Additive (LineBundleClass X)) :=
  (eulerDegreeHom k X).ker

variable (X) in
/-- `Pic⁰ X` is the kernel of the degree. -/
lemma picZero_eq_ker : picZero k X = (eulerDegreeHom k X).ker :=
  (rfl)

/-- A line-bundle class lies in `Pic⁰ X` exactly when its degree vanishes. -/
@[simp]
lemma mem_picZero_iff {a : Additive (LineBundleClass X)} :
    a ∈ picZero k X ↔ eulerDegree k a.toMul = 0 := by
  rw [picZero_eq_ker, AddMonoidHom.mem_ker, eulerDegreeHom_apply]

end LineBundleClass

namespace SchemeWeilDivisor

/-- **The degree on the Picard group computes the weighted degree of a divisor class.** Under
`Cl(X) ≅ Pic X`, the Euler-characteristic degree of the line bundle of a divisor class is the
residue-degree-weighted degree `Σ_y D(y) [κ(y) : k]` of that class. -/
@[simp]
theorem eulerDegree_classGroupToLineBundleClass
    (c : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) :
    LineBundleClass.eulerDegree k (classGroupToLineBundleClass hX.out c) =
      WeilDivisor.OrderSystem.weightedDegreeClass
        (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
        (isWeightedDegreeZero_residueDegree k hX.out) c := by
  obtain ⟨D, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective c
  have hdegree : relativeDegree (X ↘ Spec (.of k)) D =
      WeilDivisor.weightedDegree
        (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ)) D := by
    rw [WeilDivisor.weightedDegree_apply, ← relativeDegree_apply]
  simpa using hdegree

variable (X) in
/-- `Cl(X) ≅ Pic X` carries the degree-zero divisor classes onto `Pic⁰ X`. -/
theorem map_picZero :
    ((WeilDivisor.OrderSystem.ofScheme X).picZero
        (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
        (isWeightedDegreeZero_residueDegree k hX.out)).map
      (classGroupAddEquivLineBundleClass X).toAddMonoidHom =
      LineBundleClass.picZero k X := by
  ext a
  rw [AddSubgroup.mem_map]
  refine ⟨?_, fun ha ↦ ⟨(classGroupAddEquivLineBundleClass X).symm a, ?_, by simp⟩⟩
  · rintro ⟨c, hc, rfl⟩
    rw [LineBundleClass.mem_picZero_iff, AddEquiv.coe_toAddMonoidHom,
      classGroupAddEquivLineBundleClass_apply, toMul_ofMul]
    rwa [WeilDivisor.OrderSystem.mem_picZero,
      ← eulerDegree_classGroupToLineBundleClass] at hc
  · rw [WeilDivisor.OrderSystem.mem_picZero,
      ← eulerDegree_classGroupToLineBundleClass]
    have happly := congrArg Additive.toMul
      ((classGroupAddEquivLineBundleClass X).apply_symm_apply a)
    rw [classGroupAddEquivLineBundleClass_apply, toMul_ofMul] at happly
    rw [happly]
    exact (LineBundleClass.mem_picZero_iff (k := k)).mp ha

variable (X) in
/-- **`Cl⁰(X) ≅ Pic⁰(X)`.** On a proper integral curve over `k` whose codimension-one local rings
are discrete valuation rings, `D ↦ 𝒪_X(D)` identifies the degree-zero divisor classes with the
degree-zero part of the Picard group. -/
def classGroupPicZeroAddEquivPicZero :
    (WeilDivisor.OrderSystem.ofScheme X).picZero
        (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
        (isWeightedDegreeZero_residueDegree k hX.out) ≃+ LineBundleClass.picZero k X :=
  ((classGroupAddEquivLineBundleClass X).addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr (map_picZero k X))

/-- `Cl⁰(X) ≅ Pic⁰(X)` is the restriction of `Cl(X) ≅ Pic X`. -/
@[simp]
lemma coe_classGroupPicZeroAddEquivPicZero_apply
    (c : (WeilDivisor.OrderSystem.ofScheme X).picZero
      (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
      (isWeightedDegreeZero_residueDegree k hX.out)) :
    (classGroupPicZeroAddEquivPicZero k X c : Additive (LineBundleClass X)) =
      classGroupAddEquivLineBundleClass X (c : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) :=
  (rfl)

/-- The inverse of `Cl⁰(X) ≅ Pic⁰(X)` is the restriction of the inverse of `Cl(X) ≅ Pic X`. -/
@[simp]
lemma coe_classGroupPicZeroAddEquivPicZero_symm_apply (b : LineBundleClass.picZero k X) :
    ((classGroupPicZeroAddEquivPicZero k X).symm b :
        (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) =
      (classGroupAddEquivLineBundleClass X).symm (b : Additive (LineBundleClass X)) :=
  (rfl)

variable (X) in
/-- **`Pic⁰ X` is the group of degree-zero divisors modulo principal divisors.** -/
def weightedDegreeZeroQuotientAddEquivPicZero :
    WeilDivisor.weightedDegreeZeroSubgroup
        (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ)) ⧸
      (WeilDivisor.OrderSystem.ofScheme X).principalSubgroupOfWeightedDegreeZero
        (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ)) ≃+
      LineBundleClass.picZero k X :=
  ((WeilDivisor.OrderSystem.ofScheme X).weightedDegreeZeroQuotientEquivPicZero _
    (isWeightedDegreeZero_residueDegree k hX.out)).trans (classGroupPicZeroAddEquivPicZero k X)

/-- `Div⁰(X) / (principal divisors) ≅ Pic⁰ X` sends the class of a degree-zero divisor `D` to the
class of `𝒪_X(D)`. -/
@[simp]
lemma coe_weightedDegreeZeroQuotientAddEquivPicZero_mk
    (D : WeilDivisor.weightedDegreeZeroSubgroup
      (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))) :
    (weightedDegreeZeroQuotientAddEquivPicZero k X (QuotientAddGroup.mk D) :
        Additive (LineBundleClass X)) =
      Additive.ofMul (toLineBundleClass hX.out (D : SchemeWeilDivisor X)) := by
  rw [weightedDegreeZeroQuotientAddEquivPicZero, AddEquiv.trans_apply,
    coe_classGroupPicZeroAddEquivPicZero_apply,
    WeilDivisor.OrderSystem.coe_weightedDegreeZeroQuotientEquivPicZero_mk,
    classGroupAddEquivLineBundleClass_apply, classGroupToLineBundleClass_divisorClass]

section RationalPoint

variable {x₀ : CodimensionOnePoint X} (hx₀ : (X ↘ Spec (.of k)).residueDegree x₀ = 1)

include hx₀

/-- **The degree is onto `ℤ` at a point of residue degree one.** A codimension-one point with
residue field `k` — for instance the image of a `k`-rational point — carries a line bundle of
every degree. -/
theorem eulerDegreeHom_surjective :
    Function.Surjective (LineBundleClass.eulerDegreeHom k X) := fun n ↦ by
  obtain ⟨c, hc⟩ := (WeilDivisor.OrderSystem.ofScheme X).weightedDegreeClass_surjective
    (fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ))
    (isWeightedDegreeZero_residueDegree k hX.out) (x₀ := x₀) (by simp [hx₀]) n
  exact ⟨classGroupAddEquivLineBundleClass X c, by
    rw [LineBundleClass.eulerDegreeHom_apply, classGroupAddEquivLineBundleClass_apply,
      toMul_ofMul, eulerDegree_classGroupToLineBundleClass, hc]⟩

/-- **`Pic X ⧸ Pic⁰ X ≅ ℤ`** on a proper curve carrying a codimension-one point of residue
degree one, the isomorphism being the Euler-characteristic degree. -/
def picQuotientPicZeroAddEquivInt :
    Additive (LineBundleClass X) ⧸ LineBundleClass.picZero k X ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq (LineBundleClass.picZero_eq_ker k X)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (eulerDegreeHom_surjective k hx₀))

/-- The isomorphism `Pic X ⧸ Pic⁰ X ≅ ℤ` sends the class of a line bundle to its degree. -/
@[simp]
lemma picQuotientPicZeroAddEquivInt_mk (a : Additive (LineBundleClass X)) :
    picQuotientPicZeroAddEquivInt k hx₀ (QuotientAddGroup.mk a) =
      LineBundleClass.eulerDegree k a.toMul := by
  rw [picQuotientPicZeroAddEquivInt, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  -- The first-isomorphism equivalence is defined through `kerLift`; naming it exposes the
  -- quotient-map rewrite, there being no simp lemma for the composed equivalence.
  change QuotientAddGroup.kerLift (LineBundleClass.eulerDegreeHom k X)
      (QuotientAddGroup.mk a) = LineBundleClass.eulerDegree k a.toMul
  rw [QuotientAddGroup.kerLift_mk, LineBundleClass.eulerDegreeHom_apply]

end RationalPoint

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
