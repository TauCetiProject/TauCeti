/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence

/-!
# Integral and mod-two singular homology

This file specializes the mod-`m` coefficient comparison and reduction API of
`TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence` to `m = 2`:

* `TopCat.singularHomologyModTwoIso` identifies singular homology with coefficients in the integer
  module `ℤ/2` with singular homology over `𝔽₂ = ZMod 2` with scalars restricted to `ℤ`, and
  `TopCat.isZero_singularHomology_modTwo_iff` says one vanishes exactly when the other does;
* `TopCat.singularHomologyReductionModTwo` is the reduction `ρ : Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)`, with
  kernel `2 Hₙ(X; ℤ)` (`TopCat.ker_singularHomologyReductionModTwo`) and surjectivity in degree
  `n + 1` equivalent to injectivity of multiplication by two on `Hₙ(X; ℤ)`
  (`TopCat.surjective_singularHomologyReductionModTwo_succ_iff`);
* in degree one, reduction modulo two is onto
  (`TopCat.surjective_singularHomologyReductionModTwo_one`) and identifies
  `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)` (`TopCat.singularHomologyOneModTwoAddEquiv`).

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
  X.singularHomologyZModIso 2 n

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
  X.singularHomologyZModIso_hom 2 n

/-- The identification of integral `ℤ/2` homology with mod-two homology is natural in the space. -/
@[reassoc]
theorem singularHomologyModTwoIso_hom_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).map f ≫ (Y.singularHomologyModTwoIso n).hom =
      (X.singularHomologyModTwoIso n).hom ≫
        (ModuleCat.restrictScalars (algebraMap ℤ (ZMod 2))).map
          (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
            (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).map f) :=
  singularHomologyZModIso_hom_naturality f 2 n

/-- Singular homology with coefficients in the integer module `ℤ/2` vanishes exactly when singular
homology with coefficients in the field `𝔽₂` does. -/
theorem isZero_singularHomology_modTwo_iff (X : TopCat.{u}) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj X) :=
  X.isZero_singularHomology_zmod_iff 2 n

/-! ### The reduction modulo two -/

/-- The **reduction modulo two** `Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)`, induced by the coefficient map
`ℤ ⟶ ℤ/2`. -/
abbrev singularHomologyReductionModTwo (X : TopCat.{u}) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X :=
  X.singularHomologyReductionZMod 2 n

/-- **The kernel of the reduction modulo two**: an integral homology class reduces to zero modulo
two exactly when it is twice a class. -/
theorem ker_singularHomologyReductionModTwo (X : TopCat.{u}) (n : ℕ) :
    LinearMap.ker (X.singularHomologyReductionModTwo n).hom =
      LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2) := by
  simpa only [Nat.cast_ofNat] using X.ker_singularHomologyReductionZMod 2 n

/-- The reduction modulo two is onto in degree `n + 1` exactly when multiplication by two is
injective on `Hₙ(X; ℤ)`. -/
theorem surjective_singularHomologyReductionModTwo_succ_iff (X : TopCat.{u}) (n : ℕ) :
    Function.Surjective (X.singularHomologyReductionModTwo (n + 1)) ↔
      Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2) := by
  simpa only [Nat.cast_ofNat] using X.surjective_singularHomologyReductionZMod_succ_iff 2 n

/-- The reduction modulo two is onto in degree one: the zeroth integral homology is a free abelian
group, so multiplication by two is injective on it. -/
theorem surjective_singularHomologyReductionModTwo_one (X : TopCat.{u}) :
    Function.Surjective (X.singularHomologyReductionModTwo 1) :=
  X.surjective_singularHomologyReductionZMod_one 2

/-- **The first mod-two homology is the first integral homology modulo two**: reduction modulo two
induces `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)`. -/
def singularHomologyOneModTwoAddEquiv (X : TopCat.{u}) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⧸
        LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2)) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X :=
  X.singularHomologyOneZModAddEquiv 2

/-- The identification `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)` sends the class of an integral class to
its reduction modulo two. -/
@[simp]
theorem singularHomologyOneModTwoAddEquiv_mk (X : TopCat.{u})
    (x : ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) :
    X.singularHomologyOneModTwoAddEquiv (Submodule.Quotient.mk x) =
      X.singularHomologyReductionModTwo 1 x :=
  X.singularHomologyOneZModAddEquiv_mk 2 x

end TopCat
