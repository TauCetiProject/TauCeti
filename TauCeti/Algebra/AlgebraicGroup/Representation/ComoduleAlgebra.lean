/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.Polynomial
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.SymmetricAlgebra
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd
import TauCeti.Algebra.AlgebraicGroup.Tangent.Antipode

/-!
# Differentiating a comodule algebra

Let `A` be a comodule algebra over a commutative bialgebra `H`: geometrically, an action of the
affine monoid `Spec H` on `Spec A`. A tangent vector `d` at the identity of `Spec H` acts on `A`
through the differentiated representation `TauCeti.Comodule.differential`. Because the coaction is
multiplicative and `d` is a derivation at the counit, this action is a derivation of `A`: the
infinitesimal action of a Lie algebra element on functions is by vector fields.

For the symmetric algebra of a comodule `M`, with its multiplicative coaction, the differentiated
action is therefore the derivation of `Sym M` extending the differentiated action on the
generators `M`. Applied to the dual of a finite-basis representation `V` of a Hopf algebra, this
computes the infinitesimal action on the coordinate functions `X i` of `MvPolynomial ι R`.

## Main declarations

* `TauCeti.ComoduleAlgebra.differential_mul`: the Leibniz rule for the differentiated action.
* `TauCeti.ComoduleAlgebra.differential_one` and `TauCeti.ComoduleAlgebra.differential_algebraMap`:
  the differentiated action annihilates `1` and base-ring scalars.
* `TauCeti.ComoduleAlgebra.differentialDerivation`: the differentiated action on a commutative
  comodule algebra, bundled as an `R`-derivation `Derivation R A A`.
* `TauCeti.ComoduleAlgebra.differential_pow`: the power rule for the differentiated action on a
  commutative comodule algebra.
* `TauCeti.ComoduleAlgebra.differential_symmetricAlgebra_ι`: on a symmetric algebra, it commutes
  with the inclusion of generators.
* `TauCeti.ComoduleAlgebra.differential_symmetricAlgebra`: on a symmetric algebra, it is the
  derivation `SymmetricAlgebra.derivationOfEnd` induced by the action on generators.
* `TauCeti.ComoduleAlgebra.differential_polynomial_X`: on `ComoduleAlgebra.polynomial H b`, a
  tangent vector differentiates `X i` to `- ∑ j, b.coord i (d • b j) • X j`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
* J. S. Milne, *Algebraic Groups* (2017), §10.d.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

variable {R H : Type*} [CommRing R] [CommRing H] [Bialgebra R H]

section Ring

variable {A : Type*} [Ring A] [Algebra R A]

variable [ComoduleAlgebra R H A]

/-- **The Leibniz rule for a comodule algebra.** A tangent vector at the identity acts on a
comodule algebra by a derivation: `d • (a * b) = (d • a) * b + a * (d • b)`. -/
theorem differential_mul (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (a b : A) :
    Comodule.differential (R := R) (H := H) d (a * b) =
      Comodule.differential (R := R) (H := H) d a * b +
        a * Comodule.differential (R := R) (H := H) d b := by
  rw [Comodule.differential_apply, Comodule.differential_apply, Comodule.differential_apply,
    coact_mul, LinearMap.tensorComponent_mul <|
      Bialgebra.CounitAlgebra.algEquivSelf_comp_apply_mul d]
  simp only [← Comodule.coactComponent_apply, Comodule.coactComponent_counit, LinearMap.id_apply]

/-- A tangent vector at the identity annihilates `1` in any comodule algebra. -/
theorem differential_one (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    Comodule.differential (R := R) (H := H) d (1 : A) = 0 :=
  Comodule.differential_eq_zero_of_coact_eq_tmul_one coact_one d

/-- A tangent vector at the identity annihilates base-ring scalars in any comodule algebra. -/
theorem differential_algebraMap (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (r : R) :
    Comodule.differential (R := R) (H := H) d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, differential_one, smul_zero]

end Ring

section CommRing

variable {A : Type*} [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

/-- **The differentiated action on a commutative comodule algebra, bundled as a derivation.** -/
noncomputable def differentialDerivation (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    Derivation R A A :=
  Derivation.mk' (Comodule.differential (R := R) (H := H) d) fun x y ↦ by
    rw [differential_mul, smul_eq_mul, smul_eq_mul]; ring

@[simp]
theorem differentialDerivation_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (a : A) :
    differentialDerivation (R := R) (H := H) d a =
      Comodule.differential (R := R) (H := H) d a := by rfl

@[simp]
theorem differentialDerivation_toLinearMap (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    (differentialDerivation (R := R) (H := H) (A := A) d).toLinearMap =
      Comodule.differential (R := R) (H := H) (M := A) d := by rfl

/-- **The power rule for a commutative comodule algebra.** A tangent vector at the identity
differentiates `a ^ m` to `m • a ^ (m - 1) * (d • a)`. -/
theorem differential_pow (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (a : A) (m : ℕ) :
    Comodule.differential (R := R) (H := H) d (a ^ m) =
      m • a ^ (m - 1) * Comodule.differential (R := R) (H := H) d a := by
  simpa only [differentialDerivation_apply, smul_eq_mul, smul_mul_assoc] using
    (differentialDerivation (R := R) (H := H) (A := A) d).leibniz_pow a m

end CommRing

section SymmetricAlgebra

variable {M : Type*} [AddCommGroup M] [Module R M] [Comodule R H M]

attribute [local instance] symmetricAlgebra

/-- The differentiated action on a symmetric algebra commutes with the inclusion of generators,
since the coaction of a generator is the coaction on `M`. -/
theorem differential_symmetricAlgebra_ι (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (m : M) :
    Comodule.differential (R := R) (H := H) d (SymmetricAlgebra.ι R M m) =
      SymmetricAlgebra.ι R M (Comodule.differential (R := R) (H := H) d m) := by
  simp [Comodule.differential_apply, symmetricAlgebra_coact, LinearMap.rTensor_def,
    LinearMap.tensorComponent_map]

/-- **The differentiated action on a symmetric algebra.** A tangent vector at the identity acts on
the symmetric algebra of a comodule `M` by the derivation extending its action on `M`. -/
theorem differential_symmetricAlgebra (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    Comodule.differential (R := R) (H := H) (M := SymmetricAlgebra R M) d =
      (SymmetricAlgebra.derivationOfEnd R M
        (Comodule.differential (R := R) (H := H) (M := M) d)).toLinearMap := by
  have h : differentialDerivation (R := R) (H := H) (A := SymmetricAlgebra R M) d =
      SymmetricAlgebra.derivationOfEnd R M (Comodule.differential (R := R) (H := H) d) :=
    SymmetricAlgebra.derivation_ext fun m ↦ by
      rw [differentialDerivation_apply, differential_symmetricAlgebra_ι,
        SymmetricAlgebra.derivationOfEnd_ι]
  exact (differentialDerivation_toLinearMap (R := R) (H := H) (A := SymmetricAlgebra R M) d).symm
    |>.trans (congrArg Derivation.toLinearMap h)

end SymmetricAlgebra

section Polynomial

variable {R H V ι : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommGroup V] [Module R V] [Comodule R H V] [Fintype ι] [DecidableEq ι]

/-- **The differentiated action on polynomial coordinates.** On `MvPolynomial ι R` with the
contragredient polynomial comodule-algebra structure `ComoduleAlgebra.polynomial H b`, a tangent
vector `d` differentiates the coordinate `X i` to
`- ∑ j, b.coord i (Comodule.differential d (b j)) • X j`. -/
theorem differential_polynomial_X (b : Module.Basis ι R V)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (i : ι) :
    letI := ComoduleAlgebra.polynomial H b
    Comodule.differential (R := R) (H := H) d (MvPolynomial.X i : MvPolynomial ι R) =
      -∑ j, (b.coord i (Comodule.differential (R := R) (H := H) d (b j))) •
        (MvPolynomial.X j : MvPolynomial ι R) := by
  let _ := ComoduleAlgebra.polynomial H b
  rw [Comodule.differential_apply, Comodule.polynomial_coact_X, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [LinearMap.tensorComponent_tmul, LinearMap.comp_apply, Derivation.coeFn_coe,
    Derivation.apply_antipode, AlgEquiv.toLinearMap_apply, map_neg, neg_smul,
    Derivation.apply_matrixCoefficient]

end Polynomial

end TauCeti.ComoduleAlgebra
