/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField
public import TauCeti.AlgebraicTopology.Singular.Coefficients.RestrictScalars

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
`TopCat.isZero_singularHomology_zmod_iff_of_ringEquiv` of
`TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField` for any coefficient ring isomorphic to
`𝔽₂`), and a map induces an isomorphism on one exactly when it induces an isomorphism on the other
(`TopCat.Hom.isIso_singularHomologyMap_modTwo_iff` and
`TopCat.Hom.isIso_singularHomologyMap_modTwo_iff_of_ringEquiv`).

The coefficient long exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0` relates integral homology to mod-two
homology. Its first map induces multiplication by two on `Hₙ(X; ℤ)` and its second map induces the
reduction `ρ : Hₙ(X; ℤ) ⟶ Hₙ(X; ℤ/2)`, the case `m = 2` of `TopCat.singularHomologyReductionMod`
of `TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField`. There exactness shows that a class
reduces to zero exactly when it is twice a class (`TopCat.ker_singularHomologyReductionMod`), and
that the reduction is onto in degree `n + 1` exactly when multiplication by two is injective on
`Hₙ(X; ℤ)` (`TopCat.surjective_singularHomologyReductionMod_succ_iff`).

The zeroth integral homology is a free abelian group, so the reduction is onto in degree one
(`TopCat.surjective_singularHomologyReductionMod_two_one`), and it identifies the first mod-two
homology with the first integral homology modulo two
(`TopCat.singularHomologyOneModTwoAddEquiv`):

`H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)`.

So the first mod-two homology vanishes exactly when multiplication by two is onto `H₁(X; ℤ)`
(`TopCat.subsingleton_singularHomology_one_iff_surjective_zsmul`).

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

/-- The reduction modulo two is onto in degree one: the zeroth integral homology is a free abelian
group, so multiplication by two is injective on it. -/
theorem surjective_singularHomologyReductionMod_two_one (X : TopCat.{u}) :
    Function.Surjective (X.singularHomologyReductionMod 2 1) := by
  -- the zeroth integral homology is free (`ModuleCat.free_singularHomology_zero`)
  exact (X.surjective_singularHomologyReductionMod_succ_iff 2 0).2
    (smul_right_injective _ (Nat.cast_ne_zero.2 two_ne_zero))

/-- **The first mod-two homology is the first integral homology modulo two**: reduction modulo two
induces `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)`. -/
def singularHomologyOneModTwoAddEquiv (X : TopCat.{u}) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ⧸
        LinearMap.range (LinearMap.lsmul ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
          (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) 2)) ≃+
      ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X :=
  ((Submodule.quotEquivOfEq _ _
      (by rw [X.ker_singularHomologyReductionMod 2 1, Nat.cast_ofNat])).trans
    ((X.singularHomologyReductionMod 2 1).hom.quotKerEquivOfSurjective
      X.surjective_singularHomologyReductionMod_two_one) : _ ≃+ _)

/-- The identification `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ) ≃ H₁(X; ℤ/2)` sends the class of an integral class to
its reduction modulo two. -/
@[simp]
theorem singularHomologyOneModTwoAddEquiv_mk (X : TopCat.{u})
    (x : ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) :
    X.singularHomologyOneModTwoAddEquiv (Submodule.Quotient.mk x) =
      X.singularHomologyReductionMod 2 1 x := by
  simp [singularHomologyOneModTwoAddEquiv]

/-- **The first mod-two homology vanishes exactly when `H₁(X; ℤ)` is two-divisible**: with
coefficients in a ring `k` isomorphic to `ZMod 2`, `H₁(X; k) = 0` exactly when multiplication by
two is onto `H₁(X; ℤ)`. -/
theorem subsingleton_singularHomology_one_iff_surjective_zsmul (X : TopCat.{u}) {k : Type u}
    [CommRing k] (e : k ≃+* ZMod 2) :
    Subsingleton (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (ModuleCat.of k k)).obj X) ↔
      Function.Surjective fun y : ((singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X ↦ (2 : ℤ) • y := by
  rw [← ModuleCat.isZero_iff_subsingleton,
    ← X.isZero_singularHomology_zmod_iff_of_ringEquiv 2 e, ModuleCat.isZero_iff_subsingleton,
    ← X.singularHomologyOneModTwoAddEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff,
    LinearMap.range_eq_top]
  -- the integer action of the integer module agrees with that of the abelian group
  refine Iff.of_eq (congrArg Function.Surjective (funext fun y ↦ ?_))
  simp [two_smul, two_zsmul]

end TopCat
