/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Singular.Coefficients.Bockstein
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence

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
(`TauCeti.singularHomologyModTwoNatIso`). In particular one vanishes exactly when the other does
(`TopCat.isZero_singularHomology_modTwo_iff`, and `TopCat.isZero_singularHomology_modTwo_iff'` for
spaces in the lowest universe, with the coefficients `ℤ/2` and `𝔽₂` themselves rather than lifted),
and a map induces an isomorphism on one exactly when it induces an isomorphism on the other
(`TopCat.Hom.isIso_singularHomologyMap_modTwo_iff`, and
`TopCat.Hom.isIso_singularHomologyMap_modTwo_iff'` in the lowest universe).

The coefficient long exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0` relates integral homology to mod-two
homology. Its first map induces multiplication by two on `Hₙ(X; ℤ)` (the case `m = 2` of
`TopCat.singularHomologyFunctor_map_zmodCoefficientSequence_f_app`, from
`TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence`), and its second map
induces the reduction `ρ : Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)` (`TopCat.singularHomologyReductionModTwo`).
Exactness says:

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

/-! ### Comparison with homology over `𝔽₂` -/

namespace TauCeti

/-- For any `ZMod 2`-module `M` carrying a compatible `ℤ`-module structure, singular homology with
`ℤ`-module coefficients `M` is naturally isomorphic to singular homology with `ZMod 2`-module
coefficients `M` followed by restriction of scalars along `ℤ →+* ZMod 2`. -/
def singularHomologyModTwoNatIso (M : Type u) [AddCommGroup M] [Module (ZMod 2) M]
    [IsScalarTower ℤ (ZMod 2) M] (n : ℕ) :
    (singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ M) ≅
      (singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj (ModuleCat.of (ZMod 2) M) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2)) :=
  (singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod 2) M).symm ≪≫
    (Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2)))
      (ModuleCat.of (ZMod 2) M) n).symm

/-- The forward component at `X` of `TauCeti.singularHomologyModTwoNatIso` is the identification of
`M` with the restriction of `M` over `ZMod 2`, followed by the inverse of the comparison of
restricted mod-two homology with integral homology. -/
theorem singularHomologyModTwoNatIso_hom_app (M : Type u) [AddCommGroup M] [Module (ZMod 2) M]
    [IsScalarTower ℤ (ZMod 2) M] (n : ℕ) (X : TopCat.{u}) :
    (singularHomologyModTwoNatIso M n).hom.app X =
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod 2) M).inv).app X ≫
        (Functor.singularHomologyFunctorObjCompIso
          (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2)))
          (ModuleCat.of (ZMod 2) M) n).inv.app X :=
  (rfl)

/-- The inverse component at `X` of `TauCeti.singularHomologyModTwoNatIso` is the comparison of
restricted mod-two homology with integral homology, followed by the identification of the
restriction of `M` over `ZMod 2` with `M`. -/
theorem singularHomologyModTwoNatIso_inv_app (M : Type u) [AddCommGroup M] [Module (ZMod 2) M]
    [IsScalarTower ℤ (ZMod 2) M] (n : ℕ) (X : TopCat.{u}) :
    (singularHomologyModTwoNatIso M n).inv.app X =
      (Functor.singularHomologyFunctorObjCompIso
          (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2)))
          (ModuleCat.of (ZMod 2) M) n).hom.app X ≫
        ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ZMod 2) M).hom).app X :=
  (rfl)

end TauCeti

namespace TopCat

/-- Singular homology with coefficients in the integer module `ℤ/2` vanishes exactly when singular
homology with coefficients in the field `𝔽₂` does. -/
theorem isZero_singularHomology_modTwo_iff (X : TopCat.{u}) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj X) := by
  rw [Iso.isZero_iff ((TauCeti.singularHomologyModTwoNatIso (ULift.{u} (ZMod 2)) n).app X),
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  -- restriction of scalars does not change the underlying abelian group
  rfl

/-- For a space in the lowest universe, singular homology with coefficients in the integer module
`ℤ/2` vanishes exactly when singular homology with coefficients in the field `𝔽₂` does, with the
coefficients `ℤ/2` and `𝔽₂` themselves rather than their universe lifts. -/
theorem isZero_singularHomology_modTwo_iff' (X : TopCat.{0}) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ZMod 2))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).obj X) := by
  rw [Iso.isZero_iff ((TauCeti.singularHomologyModTwoNatIso (ZMod 2) n).app X),
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  -- restriction of scalars does not change the underlying abelian group
  rfl

end TopCat

namespace TopCat.Hom

/-- A continuous map induces an isomorphism on singular homology with coefficients in the integer
module `ℤ/2` exactly when it induces one with coefficients in the field `𝔽₂`. -/
theorem isIso_singularHomologyMap_modTwo_iff {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).map f) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).map f) :=
  (NatIso.isIso_map_iff (TauCeti.singularHomologyModTwoNatIso (ULift.{u} (ZMod 2)) n) f).trans
    (isIso_iff_of_reflects_iso _ (ModuleCat.restrictScalars.{u} (algebraMap ℤ (ZMod 2))))

/-- For a morphism in the lowest universe, the induced map on singular homology with coefficients in
the integer module `ℤ/2` is an isomorphism exactly when the induced map on singular homology with
coefficients in the field `𝔽₂` is an isomorphism, with the coefficients themselves rather than their
universe lifts. -/
theorem isIso_singularHomologyMap_modTwo_iff' {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ (ZMod 2))).map f) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).map f) :=
  (NatIso.isIso_map_iff (TauCeti.singularHomologyModTwoNatIso (ZMod 2) n) f).trans
    (isIso_iff_of_reflects_iso _ (ModuleCat.restrictScalars.{0} (algebraMap ℤ (ZMod 2))))

end TopCat.Hom

namespace TopCat

/-! ### The reduction modulo two -/

/-- The **reduction modulo two** `Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)`, induced by the coefficient map
`ℤ ⟶ ℤ/2`. -/
abbrev singularHomologyReductionModTwo (X : TopCat.{u}) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⟶
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X :=
  ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).map
    (TauCeti.zmodCoefficientSequence.{u} 2).g).app X

/-- **The kernel of the reduction modulo two**: an integral homology class reduces to zero modulo
two exactly when it is twice a class. -/
theorem ker_singularHomologyReductionModTwo (X : TopCat.{u}) (n : ℕ) :
    LinearMap.ker (X.singularHomologyReductionModTwo n).hom =
      LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2) := by
  have h := X.singularHomologyFunctor_map_zmodCoefficientSequence_f_app 2 n
  rw [Nat.cast_ofNat] at h
  rw [← h]
  exact ((X.singularHomology_exact_coefficient₂
    (TauCeti.zmodCoefficientSequence_shortExact.{u} 2) n).moduleCat_range_eq_ker).symm

/-- The reduction modulo two is onto in degree `n + 1` exactly when multiplication by two is
injective on `Hₙ(X; ℤ)`. -/
theorem surjective_singularHomologyReductionModTwo_succ_iff (X : TopCat.{u}) (n : ℕ) :
    Function.Surjective (X.singularHomologyReductionModTwo (n + 1)) ↔
      Function.Injective (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2) := by
  have hS := TauCeti.zmodCoefficientSequence_shortExact.{u} 2
  have h := X.singularHomologyFunctor_map_zmodCoefficientSequence_f_app 2 n
  rw [Nat.cast_ofNat] at h
  -- both conditions say that the Bockstein homomorphism vanishes
  rw [← ModuleCat.epi_iff_surjective,
    (X.singularHomology_exact_coefficient₃ hS (n + 1) n).epi_f_iff,
    ← (X.singularHomology_exact_coefficient₁ hS (n + 1) n).mono_g_iff, ModuleCat.mono_iff_injective,
    ← h]

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
