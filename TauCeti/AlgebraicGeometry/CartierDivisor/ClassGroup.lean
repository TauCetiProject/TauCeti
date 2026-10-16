/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Principal

/-!
# The Cartier class group and the Picard group

For an integral scheme `X`, the Cartier class group `CaCl(X)` is the group of Cartier divisors
modulo principal divisors. The map `D ↦ [𝒪_X(D)]` induces an additive equivalence
`CaCl(X) ≃+ Additive (LineBundleClass X)`. Thus two Cartier divisors define isomorphic line
bundles exactly when their difference is principal.

The equivalence combines the tensor-product law, representation of every line bundle by a
Cartier divisor, and the characterization of divisors with trivial associated line bundle.
No Noetherian, regularity, dimension, or properness hypothesis is needed.

## Main declarations

* `Scheme.CartierDivisor.ClassGroup`: Cartier divisors modulo principal divisors;
* `Scheme.CartierDivisor.divisorClass`: the additive quotient map;
* `Scheme.CartierDivisor.ClassGroup.lift`: descent of homomorphisms vanishing on principal divisors;
* `Scheme.CartierDivisor.classGroupAddEquivLineBundleClass`: the Cartier–Picard dictionary;
* `Scheme.CartierDivisor.nonempty_iso_sheaf_iff`: isomorphic divisor sheaves are characterized
  by a principal difference.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.15.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X]

/-- The subgroup of principal Cartier divisors. -/
def principalSubgroup (X : Scheme.{u}) [IsIntegral X] : AddSubgroup (CartierDivisor X) :=
  (principalCartierDivisorAddHom X).range

/-- A Cartier divisor belongs to the principal subgroup exactly when it is the divisor of a
nonzero rational function. -/
@[simp]
lemma mem_principalSubgroup {D : CartierDivisor X} :
    D ∈ principalSubgroup X ↔ ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D := by
  simp only [principalSubgroup, AddMonoidHom.mem_range, principalCartierDivisorAddHom_apply]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨f.toMul, hf⟩, fun ⟨f, hf⟩ ↦ ⟨Additive.ofMul f, hf⟩⟩

/-- The principal Cartier divisors are precisely the kernel of `D ↦ [𝒪_X(D)]`. -/
lemma principalSubgroup_eq_ker :
    principalSubgroup X = (toLineBundleClassHom (X := X)).ker := by
  ext D
  rw [mem_principalSubgroup, AddMonoidHom.mem_ker, toLineBundleClassHom_apply,
    ofMul_eq_zero, toLineBundleClass_eq_one_iff]

/-- The Cartier class group `CaCl(X)`, namely Cartier divisors modulo principal divisors. -/
abbrev ClassGroup (X : Scheme.{u}) [IsIntegral X] : Type u :=
  CartierDivisor X ⧸ principalSubgroup X

/-- The additive quotient map from Cartier divisors to the Cartier class group. -/
def divisorClass : CartierDivisor X →+ ClassGroup X :=
  QuotientAddGroup.mk' (principalSubgroup X)

/-- The Cartier divisor class is the canonical quotient projection. -/
lemma divisorClass_eq_mk' (D : CartierDivisor X) :
    divisorClass D = QuotientAddGroup.mk' (principalSubgroup X) D :=
  (rfl)

/-- Every Cartier divisor class has a Cartier divisor representative. -/
lemma divisorClass_surjective : Function.Surjective (divisorClass (X := X)) :=
  QuotientAddGroup.mk'_surjective _

/-- Equal Cartier divisor classes are characterized by a principal difference. -/
lemma divisorClass_eq_iff {D E : CartierDivisor X} :
    divisorClass D = divisorClass E ↔
      ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D - E := by
  rw [divisorClass_eq_mk', divisorClass_eq_mk']
  exact QuotientAddGroup.eq_iff_sub_mem.trans mem_principalSubgroup

/-- A Cartier divisor has zero class exactly when it is principal. -/
lemma divisorClass_eq_zero_iff {D : CartierDivisor X} :
    divisorClass D = 0 ↔
      ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D := by
  rw [divisorClass_eq_mk']
  exact (QuotientAddGroup.eq_zero_iff D).trans mem_principalSubgroup

/-- Principal Cartier divisors have zero class. -/
@[simp]
lemma divisorClass_principalCartierDivisor (f : X.functionFieldˣ) :
    divisorClass (principalCartierDivisor X f) = 0 :=
  divisorClass_eq_zero_iff.mpr ⟨f, rfl⟩

/-- The universal property of the Cartier class group: an additive homomorphism that vanishes
on principal Cartier divisors descends to the class group. -/
def ClassGroup.lift {H : Type*} [AddMonoid H] (φ : CartierDivisor X →+ H)
    (hφ : ∀ f : X.functionFieldˣ, φ (principalCartierDivisor X f) = 0) : ClassGroup X →+ H :=
  QuotientAddGroup.lift (principalSubgroup X) φ (by
    intro D hD
    obtain ⟨f, rfl⟩ := mem_principalSubgroup.mp hD
    exact AddMonoidHom.mem_ker.mpr (hφ f))

/-- The descended homomorphism evaluates on the class of a divisor as the original map. -/
@[simp]
lemma ClassGroup.lift_divisorClass {H : Type*} [AddMonoid H] (φ : CartierDivisor X →+ H)
    (hφ : ∀ f : X.functionFieldˣ, φ (principalCartierDivisor X f) = 0) (D : CartierDivisor X) :
    ClassGroup.lift φ hφ (divisorClass D) = φ D := by
  rw [ClassGroup.lift, divisorClass_eq_mk']
  exact QuotientAddGroup.lift_mk' (principalSubgroup X) _ D

/-- **The Cartier–Picard dictionary.** On any integral scheme, Cartier divisors modulo
principal divisors form the Picard group of line-bundle classes under tensor product. -/
def classGroupAddEquivLineBundleClass (X : Scheme.{u}) [IsIntegral X] :
    ClassGroup X ≃+ Additive (LineBundleClass X) :=
  QuotientAddGroup.liftEquiv (principalSubgroup X)
    (by
      intro a
      obtain ⟨D, hD⟩ := toLineBundleClass_surjective a.toMul
      exact ⟨D, by rw [toLineBundleClassHom_apply, hD, ofMul_toMul]⟩)
    principalSubgroup_eq_ker

/-- The Cartier–Picard equivalence sends the class of `D` to the class of `𝒪_X(D)`. -/
@[simp]
lemma classGroupAddEquivLineBundleClass_divisorClass (D : CartierDivisor X) :
    classGroupAddEquivLineBundleClass X (divisorClass D) = Additive.ofMul D.toLineBundleClass := by
  rw [divisorClass_eq_mk', QuotientAddGroup.mk'_apply, classGroupAddEquivLineBundleClass]
  exact (QuotientAddGroup.liftEquiv_mk (principalSubgroup X)
    (φ := toLineBundleClassHom (X := X)) _ principalSubgroup_eq_ker D).trans
      (toLineBundleClassHom_apply D)

/-- The inverse Cartier–Picard equivalence sends `𝒪_X(D)` back to the class of `D`. -/
@[simp]
lemma classGroupAddEquivLineBundleClass_symm_toLineBundleClass (D : CartierDivisor X) :
    (classGroupAddEquivLineBundleClass X).symm (Additive.ofMul D.toLineBundleClass) =
      divisorClass D := by
  rw [← classGroupAddEquivLineBundleClass_divisorClass,
    AddEquiv.symm_apply_apply]

/-- Two Cartier divisors give the same line-bundle class exactly when their difference is
principal. -/
lemma toLineBundleClass_eq_iff {D E : CartierDivisor X} :
    D.toLineBundleClass = E.toLineBundleClass ↔
      ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D - E := by
  rw [← divisorClass_eq_iff, ← (classGroupAddEquivLineBundleClass X).injective.eq_iff]
  simp only [classGroupAddEquivLineBundleClass_divisorClass, Additive.ofMul.injective.eq_iff]

/-- **Isomorphic Cartier divisor sheaves have a principal difference, and conversely.** -/
theorem nonempty_iso_sheaf_iff {D E : CartierDivisor X} :
    Nonempty (D.sheaf ≅ E.sheaf) ↔
      ∃ f : X.functionFieldˣ, principalCartierDivisor X f = D - E := by
  rw [← toLineBundleClass_eq_iff]
  have h : E.toLineBundleClass = LineBundleClass.mk E.toInvertibleSheaf := by
    apply toLineBundleClass_eq_mk_iff.mpr
    rw [toInvertibleSheaf_obj]
    exact ⟨Iso.refl _⟩
  rw [h, toLineBundleClass_eq_mk_iff, toInvertibleSheaf_obj]

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
