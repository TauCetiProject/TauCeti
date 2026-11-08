/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.Algebra.Category.ModuleCat.ModTwo
public import TauCeti.AlgebraicTopology.Singular.Coefficients.Bockstein
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients

import TauCeti.Algebra.Category.ModuleCat.AB
import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Integral and mod-two singular homology

The singular homology of a space with coefficients in `ℤ/2` can be formed in two ways: with the
integer module `ℤ/2` as coefficients in `ModuleCat ℤ`, which is how it appears in the coefficient
long exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0`, or with the field `𝔽₂ = ZMod 2` as coefficients in
`ModuleCat 𝔽₂`, which is how mod-two homology is computed, for instance by a spectral sequence of
`𝔽₂`-vector spaces. The two agree: restriction of scalars along `ℤ → 𝔽₂` preserves coproducts and
homology, so the integer-module homology is the mod-two homology with its scalars restricted
(`TopCat.singularHomologyModTwoIso`). In particular one vanishes exactly when the other does
(`TopCat.isZero_singularHomology_modTwo_iff`).

The coefficient long exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0` relates integral homology to mod-two
homology. Its first map induces multiplication by two on `Hₙ(X; ℤ)`
(`TopCat.singularHomologyFunctor_map_modTwoCoefficientSequence_f_app`), and its second map induces
the reduction `ρ : Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)` (`TopCat.singularHomologyReductionModTwo`). Exactness
says:

* a class reduces to zero exactly when it is twice a class
  (`TopCat.ker_singularHomologyReductionModTwo`);
* the reduction is onto in degree `n + 1` exactly when multiplication by two is injective on
  `Hₙ(X; ℤ)` (`TopCat.surjective_singularHomologyReductionModTwo_succ_iff`).

The zeroth integral homology is a free abelian group, so the reduction is onto in degree one
(`TopCat.surjective_singularHomologyReductionModTwo_one`), and it identifies the first mod-two
homology with the first integral homology modulo two
(`TopCat.singularHomologyOneModTwoAddEquiv`):

`H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)`.

The companion statement that mod-two acyclicity in two adjacent degrees makes multiplication by two
bijective is `TopCat.isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients) and Section 3.E (Bockstein homomorphisms).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace TopCat

/-! ### Comparison with homology over `𝔽₂` -/

/-- **Integral homology with `ℤ/2` coefficients is mod-two homology**: the singular homology with
coefficients in the integer module `ℤ/2` is the singular homology with coefficients in the field
`𝔽₂`, with its scalars restricted to `ℤ`. -/
def singularHomologyModTwoIso (X : TopCat.{u}) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X ≅
      (ModuleCat.restrictScalars (algebraMap ℤ (ZMod 2))).obj
        (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj X) :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod 2)
        (ULift.{u} (ZMod 2))).symm).app X ≪≫
    ((Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2)))
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) n).app X).symm

/-- The identification of integral `ℤ/2` homology with mod-two homology is the inverse of the
identification of `ℤ/2` with the restriction of `𝔽₂`, followed by the inverse of the comparison of
restricted mod-two homology with integral homology. -/
theorem singularHomologyModTwoIso_hom (X : TopCat.{u}) (n : ℕ) :
    (X.singularHomologyModTwoIso n).hom =
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod 2)
            (ULift.{u} (ZMod 2))).inv).app X ≫
        (Functor.singularHomologyFunctorObjCompIso
          (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2)))
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) n).inv.app X :=
  (rfl)

/-- The identification of integral `ℤ/2` homology with mod-two homology is natural in the space. -/
@[reassoc]
theorem singularHomologyModTwoIso_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).map f ≫ (Y.singularHomologyModTwoIso n).hom =
      (X.singularHomologyModTwoIso n).hom ≫
        (ModuleCat.restrictScalars (algebraMap ℤ (ZMod 2))).map
          (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).map f) := by
  rw [singularHomologyModTwoIso_hom, singularHomologyModTwoIso_hom, NatTrans.naturality_assoc]
  exact congrArg _ ((Functor.singularHomologyFunctorObjCompIso _ _ n).inv.naturality f)

/-- Singular homology with coefficients in the integer module `ℤ/2` vanishes exactly when singular
homology with coefficients in the field `𝔽₂` does. -/
theorem isZero_singularHomology_modTwo_iff (X : TopCat.{u}) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj X) := by
  rw [Iso.isZero_iff (singularHomologyModTwoIso X n), ModuleCat.isZero_iff_subsingleton,
    ModuleCat.isZero_iff_subsingleton]
  -- restriction of scalars does not change the underlying abelian group
  rfl

/-! ### The reduction modulo two -/

/-- The coefficient map `ℤ ⟶ ℤ` of the mod-two coefficient sequence induces multiplication by two on
integral singular homology. -/
theorem singularHomologyFunctor_map_modTwoCoefficientSequence_f_app (X : TopCat.{u}) (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
        TauCeti.modTwoCoefficientSequence.{u}.f).app X).hom =
      LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2 := by
  -- Mathlib's `singularHomologyFunctor` is by definition singular chains followed by homology
  change (HomologicalComplex.homologyMap (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map
    TauCeti.modTwoCoefficientSequence.f).app X) n).hom =
      LinearMap.lsmul ℤ ((((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X).homology n) 2
  ext x
  simp [HomologicalComplex.homologyMap_add, two_smul]

/-- The **reduction modulo two** `Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)`, induced by the coefficient map
`ℤ ⟶ ℤ/2`. -/
abbrev singularHomologyReductionModTwo (X : TopCat.{u}) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map TauCeti.modTwoCoefficientSequence.{u}.g).app X

/-- **The kernel of the reduction modulo two**: an integral homology class reduces to zero modulo
two exactly when it is twice a class. -/
theorem ker_singularHomologyReductionModTwo (X : TopCat.{u}) (n : ℕ) :
    LinearMap.ker (X.singularHomologyReductionModTwo n).hom =
      LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2) := by
  rw [← X.singularHomologyFunctor_map_modTwoCoefficientSequence_f_app n]
  exact ((X.singularHomology_exact_coefficient₂
    TauCeti.modTwoCoefficientSequence_shortExact.{u} n).moduleCat_range_eq_ker).symm

/-- The reduction modulo two is onto in degree `n + 1` exactly when multiplication by two is
injective on `Hₙ(X; ℤ)`. -/
theorem surjective_singularHomologyReductionModTwo_succ_iff (X : TopCat.{u}) (n : ℕ) :
    Function.Surjective (X.singularHomologyReductionModTwo (n + 1)) ↔
      Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2) := by
  have hS := TauCeti.modTwoCoefficientSequence_shortExact.{u}
  -- both conditions say that the Bockstein homomorphism vanishes
  rw [← ModuleCat.epi_iff_surjective,
    (X.singularHomology_exact_coefficient₃ hS (n + 1) n).epi_f_iff,
    ← (X.singularHomology_exact_coefficient₁ hS (n + 1) n).mono_g_iff, ModuleCat.mono_iff_injective,
    ← X.singularHomologyFunctor_map_modTwoCoefficientSequence_f_app n]

/-- The reduction modulo two is onto in degree one: the zeroth integral homology is a free abelian
group, so multiplication by two is injective on it. -/
theorem surjective_singularHomologyReductionModTwo_one (X : TopCat.{u}) :
    Function.Surjective (X.singularHomologyReductionModTwo 1) := by
  -- the zeroth integral homology is free (`ModuleCat.free_singularHomology_zero`)
  exact (X.surjective_singularHomologyReductionModTwo_succ_iff 0).2
    (smul_right_injective _ (two_ne_zero : (2 : ℤ) ≠ 0))

/-- **The first mod-two homology is the first integral homology modulo two**: reduction modulo two
induces `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)`. -/
def singularHomologyOneModTwoAddEquiv (X : TopCat.{u}) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⧸
        LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2)) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X :=
  ((Submodule.quotEquivOfEq _ _ (X.ker_singularHomologyReductionModTwo 1).symm).trans
    ((X.singularHomologyReductionModTwo 1).hom.quotKerEquivOfSurjective
      X.surjective_singularHomologyReductionModTwo_one) : _ ≃+ _)

/-- The identification `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)` sends the class of an integral class to
its reduction modulo two. -/
@[simp]
theorem singularHomologyOneModTwoAddEquiv_mk (X : TopCat.{u})
    (x : ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) :
    X.singularHomologyOneModTwoAddEquiv (Submodule.Quotient.mk x) =
      X.singularHomologyReductionModTwo 1 x := by
  simp [singularHomologyOneModTwoAddEquiv]

end TopCat
