/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.SymmetricAlgebra
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd

/-!
# Differentiating a comodule algebra

Let `A` be a comodule algebra over a commutative bialgebra `H`: geometrically, an action of the
affine monoid `Spec H` on `Spec A`. A tangent vector `d` at the identity of `Spec H` acts on `A`
through the differentiated representation `TauCeti.Comodule.differential`. Because the coaction is
multiplicative and `d` is a derivation at the counit, this action is a derivation of `A`: the
infinitesimal action of a Lie algebra element on functions is by vector fields.

For the symmetric algebra of a comodule `M`, with its multiplicative coaction, the differentiated
action is therefore the derivation of `Sym M` extending the differentiated action on the
generators `M`. Applied to the dual of a representation `V`, this computes the infinitesimal
action on the polynomial functions on `V`.

## Main declarations

* `TauCeti.ComoduleAlgebra.differential_mul`: the Leibniz rule for the differentiated action.
* `TauCeti.ComoduleAlgebra.differential_symmetricAlgebra_ι`: on a symmetric algebra, it commutes
  with the inclusion of generators.
* `TauCeti.ComoduleAlgebra.differential_symmetricAlgebra`: on a symmetric algebra, it is the
  derivation `SymmetricAlgebra.derivationOfEnd` induced by the action on generators.

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

end Ring

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
  let D : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
    Derivation.mk' (Comodule.differential (R := R) (H := H) d) fun a b ↦ by
      rw [differential_mul, smul_eq_mul, smul_eq_mul]
      ring
  have h : D = SymmetricAlgebra.derivationOfEnd R M (Comodule.differential (R := R) (H := H) d) :=
    SymmetricAlgebra.derivation_ext fun m ↦ by
      rw [Derivation.coe_mk', differential_symmetricAlgebra_ι,
        SymmetricAlgebra.derivationOfEnd_ι]
  exact LinearMap.ext fun p ↦ by
    rw [← h, Derivation.coe_mk'_linearMap]

end SymmetricAlgebra

end TauCeti.ComoduleAlgebra
