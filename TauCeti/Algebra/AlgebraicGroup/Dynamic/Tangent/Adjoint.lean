/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Coefficients
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# Infinitesimal conjugation by a cocharacter

The coefficients of the adjoint action of the generic cocharacter point on a tangent
vector are obtained by applying that vector to the coefficients of universal conjugation.
Together with the coefficient criteria for dynamic tangent spaces, this relates their
defining equations to the infinitesimal conjugation action, without choosing matrices
or imposing smoothness or finite projectivity on the cotangent module.

The argument uses the tensor contraction formula for the differential of universal
conjugation in `Tangent.Conjugation`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace Derivation

variable {R H B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B]

/-- The Laurent coefficients of infinitesimal conjugation are the derivatives of the
universal conjugation coefficients. This holds with arbitrary coefficient algebras. -/
theorem coeff_adDerivation_genericPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (l : H →ₐc[R] LaurentPolynomial R) (h : H) (n : ℤ) :
    (Bialgebra.CounitAlgebra.algEquivSelf R H (LaurentPolynomial B)
      (adDerivation (LaurentPolynomial B)
        (pointInCounitAlgebra (LaurentPolynomial B) (genericPoint B l))
        (mapValue (IsScalarTower.toAlgHom R B (LaurentPolynomial B)) d) h)).coeff n =
      Bialgebra.CounitAlgebra.algEquivSelf R H B
        (d ((Cocharacter.conjugationAlgHom l h).coeff n)) := by
  let P := genericPoint H l
  let Q := Cocharacter.constPoint H (toConv (AlgHom.id R H))
  have hc := AlgHom.congr_fun (HopfAlgebra.productMap_comp_conjugationAlgHom P Q) h
  have hfamily : (Algebra.TensorProduct.productMap P.ofConv Q.ofConv)
      (HopfAlgebra.conjugationAlgHom (R := R) (H := H) h) =
      Cocharacter.conjugationAlgHom l h := by
    rw [AlgHom.comp_apply] at hc
    ext n
    rw [hc, ← conjugate_apply]
    simpa only [ofConv_toConv, AlgHom.id_apply] using
      coeff_conjugate l (toConv (AlgHom.id R H)) h n
  rw [adDerivation_eq_lift_conjugationAlgHom, ← hfamily]
  generalize HopfAlgebra.conjugationAlgHom (R := R) (H := H) h = z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hx, hy]
  | tmul a b =>
    rw [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply', map_mul]
    have hp : Bialgebra.CounitAlgebra.algEquivSelf R H (LaurentPolynomial B)
        ((pointInCounitAlgebra (LaurentPolynomial B) (genericPoint B l)).ofConv a) =
        (genericPoint B l).ofConv a := by
      rw [pointInCounitAlgebra_apply]
      exact Bialgebra.CounitAlgebra.algEquivSelf_apply R H (LaurentPolynomial B) _
    simp only [AlgHom.toLinearMap_apply, Derivation.coeFn_coe]
    rw [hp, mapValue_apply, Bialgebra.CounitAlgebra.algEquivSelf_map]
    simp only [Algebra.TensorProduct.productMap_apply_tmul, P, Q,
      genericPoint_ofConv, constPoint_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
    rw [← LaurentPolynomial.C_eq_algebraMap (R := B),
      ← LaurentPolynomial.C_eq_algebraMap (R := H)]
    simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_mul_single_zero,
      AddMonoidAlgebra.coeff_mapAlgHom, Algebra.ofId_apply]
    rw [d.leibniz, d.map_algebraMap, smul_zero, add_zero,
      Bialgebra.CounitAlgebra.algEquivSelf_smul]
    simp

end Derivation
