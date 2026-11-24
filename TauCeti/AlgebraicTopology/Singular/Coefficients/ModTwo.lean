/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coefficients.Bockstein
public import TauCeti.AlgebraicTopology.Singular.Coefficients.RestrictScalars
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
(`TauCeti.singularHomologyRestrictScalarsNatIso`). In particular one vanishes exactly when the
other does (`TopCat.isZero_singularHomology_modTwo_iff`, and
`TopCat.isZero_singularHomology_modTwo_iff_of_ringEquiv` for any coefficient ring isomorphic to
`𝔽₂`), and a map induces an isomorphism on one exactly when it induces an isomorphism on the other
(`TopCat.Hom.isIso_singularHomologyMap_modTwo_iff` and
`TopCat.Hom.isIso_singularHomologyMap_modTwo_iff_of_ringEquiv`).

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

namespace TopCat

/-- Singular homology with coefficients in a `ZMod 2`-module `M`, viewed as an integer module,
vanishes exactly when singular homology with `ZMod 2`-module coefficients `M` does. -/
theorem isZero_singularHomology_modTwo_iff (X : TopCat.{u}) {M : Type u} [AddCommGroup M]
    [Module (ZMod 2) M] [IsScalarTower ℤ (ZMod 2) M] (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ M)).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) M)).obj X) :=
  X.isZero_singularHomology_restrictScalars_iff ℤ (ZMod 2) M n

/-- Singular homology with coefficients in the integer module `ℤ/2` vanishes exactly when singular
homology with coefficients in a ring `k ≅ 𝔽₂`, as a module over itself, does. For `k = ZMod 2` and
a space in the lowest universe this compares `ℤ/2` and `𝔽₂` themselves rather than their lifts. -/
theorem isZero_singularHomology_modTwo_iff_of_ringEquiv (X : TopCat.{u}) {k : Type u}
    [CommRing k] (e : k ≃+* ZMod 2) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X) := by
  -- `ℤ/2` and `k` are isomorphic abelian groups, and `k` as an integer module is `k` with its
  -- scalars restricted along `ℤ → k`, which preserves coproducts and homology
  rw [Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (AddEquiv.ulift.trans e.symm.toAddEquiv).toIntLinearEquiv.toModuleIso).app X)]
  exact X.isZero_singularHomology_restrictScalars_iff ℤ k k n

end TopCat

namespace TopCat.Hom

/-- A continuous map induces an isomorphism on singular homology with coefficients in a
`ZMod 2`-module `M`, viewed as an integer module, exactly when it induces one with
`ZMod 2`-module coefficients `M`. -/
theorem isIso_singularHomologyMap_modTwo_iff {X Y : TopCat.{u}} (f : X ⟶ Y) {M : Type u}
    [AddCommGroup M] [Module (ZMod 2) M] [IsScalarTower ℤ (ZMod 2) M] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj (ModuleCat.of ℤ M)).map f) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) n).obj
        (ModuleCat.of (ZMod 2) M)).map f) :=
  f.isIso_singularHomologyMap_restrictScalars_iff ℤ (ZMod 2) M n

/-- A continuous map induces an isomorphism on singular homology with coefficients in the integer
module `ℤ/2` exactly when it induces one with coefficients in a ring `k ≅ 𝔽₂`, as a module over
itself. For `k = ZMod 2` and spaces in the lowest universe this compares `ℤ/2` and `𝔽₂`
themselves rather than their lifts. -/
theorem isIso_singularHomologyMap_modTwo_iff_of_ringEquiv {X Y : TopCat.{u}} (f : X ⟶ Y)
    {k : Type u} [CommRing k] (e : k ≃+* ZMod 2) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).map f) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map f) := by
  rw [NatIso.isIso_map_iff ((singularHomologyFunctor (ModuleCat.{u} ℤ) n).mapIso
      (AddEquiv.ulift.trans e.symm.toAddEquiv).toIntLinearEquiv.toModuleIso) f]
  exact f.isIso_singularHomologyMap_restrictScalars_iff ℤ k k n

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
