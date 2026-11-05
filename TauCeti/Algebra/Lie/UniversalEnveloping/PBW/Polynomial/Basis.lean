/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Ordered polynomial bases of an enveloping algebra

Given an ordered finite basis `b` of a Lie algebra and a polynomial basis `p i` for each
coordinate, the ordered products of `p i k` evaluated at the generators `ι (b i)` form a
basis of the enveloping algebra. No commutativity of the generators is required.

`Module.Basis.pbwPolynomialEquiv` identifies the tensor product of the one-variable polynomial
spaces with the enveloping algebra, by ordered evaluation. Transporting tensor-product bases
along this equivalence gives `Module.Basis.pbwPolynomialBasis`. In particular, different
coordinates may use different polynomial bases, allowing binomial Cartan factors and
divided-power root factors in the same basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§17, 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The construction uses the ordered PBW basis and Mathlib's `Module.Basis.piTensorProduct`.
-/

public section

namespace Module.Basis

open Polynomial
open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {n : ℕ} (b : Basis (Fin n) R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Ordered evaluation of one polynomial in each basis generator, as a multilinear map. -/
private noncomputable def orderedPolynomialEvaluation :
    MultilinearMap R (fun _ : Fin n => R[X]) U :=
  (MultilinearMap.mkPiAlgebraFin R n U).compLinearMap
    (fun i => (aeval (_root_.UniversalEnvelopingAlgebra.ι R (b i))).toLinearMap)

private theorem orderedPolynomialEvaluation_apply (p : Fin n → R[X]) :
    b.orderedPolynomialEvaluation p =
      (List.ofFn fun i => aeval (_root_.UniversalEnvelopingAlgebra.ι R (b i)) (p i)).prod :=
  (rfl)

private theorem lift_orderedPolynomialEvaluation_monomials (a : Fin n → ℕ) :
    PiTensorProduct.lift b.orderedPolynomialEvaluation
        ((Basis.piTensorProduct fun _ : Fin n => Polynomial.basisMonomials R) a) =
      b.pbwBasis (Finsupp.equivFunOnFinite.symm a) := by
  rw [Basis.piTensorProduct_apply, PiTensorProduct.lift.tprod,
    orderedPolynomialEvaluation_apply, pbwBasis_eq_prod_pow_fin]
  simp [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow,
    List.ofFn_eq_map]

/-- Ordered polynomial evaluation is bijective by the ordinary PBW basis. -/
private theorem lift_orderedPolynomialEvaluation_bijective :
    Function.Bijective (PiTensorProduct.lift b.orderedPolynomialEvaluation) := by
  let e := (Basis.piTensorProduct fun _ : Fin n => Polynomial.basisMonomials R).equiv
    b.pbwBasis Finsupp.equivFunOnFinite.symm
  have he : e.toLinearMap = PiTensorProduct.lift b.orderedPolynomialEvaluation := by
    apply (Basis.piTensorProduct fun _ : Fin n => Polynomial.basisMonomials R).ext
    intro a
    rw [LinearEquiv.coe_toLinearMap, Basis.equiv_apply,
      lift_orderedPolynomialEvaluation_monomials]
  exact he ▸ e.bijective

/-- Ordered evaluation identifies the tensor product of polynomial spaces with the enveloping
algebra as modules, not generally as algebras. -/
noncomputable def pbwPolynomialEquiv :
    (⨂[R] _ : Fin n, R[X]) ≃ₗ[R] U :=
  LinearEquiv.ofBijective (PiTensorProduct.lift b.orderedPolynomialEvaluation)
    b.lift_orderedPolynomialEvaluation_bijective

/-- On pure tensors the polynomial PBW equivalence is the increasing ordered product of the
evaluated polynomials. -/
@[simp]
theorem pbwPolynomialEquiv_tprod (p : Fin n → R[X]) :
    b.pbwPolynomialEquiv (PiTensorProduct.tprod R p) =
      (List.ofFn fun i => aeval (_root_.UniversalEnvelopingAlgebra.ι R (b i)) (p i)).prod := by
  exact (PiTensorProduct.lift.tprod p).trans (b.orderedPolynomialEvaluation_apply p)

/-- The inverse polynomial PBW equivalence recovers the pure tensor from an ordered product.
Use this with `rw`: simplification unfolds the Lie generators inside the product. -/
theorem pbwPolynomialEquiv_symm_prod (p : Fin n → R[X]) :
    b.pbwPolynomialEquiv.symm
        ((List.ofFn fun i => aeval (_root_.UniversalEnvelopingAlgebra.ι R (b i)) (p i)).prod) =
      PiTensorProduct.tprod R p := by
  rw [← pbwPolynomialEquiv_tprod, LinearEquiv.symm_apply_apply]

/-- Any choice of polynomial basis in each coordinate gives an ordered basis of the enveloping
algebra. The polynomial bases need not be equal or homogeneous. -/
noncomputable def pbwPolynomialBasis {κ : Fin n → Type*}
    (p : (i : Fin n) → Basis (κ i) R R[X]) : Basis ((i : Fin n) → κ i) R U :=
  (Basis.piTensorProduct p).map b.pbwPolynomialEquiv

/-- A polynomial PBW basis vector is the ordered product of the chosen polynomial basis
vectors evaluated at the corresponding Lie generators. -/
@[simp]
theorem pbwPolynomialBasis_apply {κ : Fin n → Type*}
    (p : (i : Fin n) → Basis (κ i) R R[X]) (a : (i : Fin n) → κ i) :
    b.pbwPolynomialBasis p a =
      (List.ofFn fun i =>
        aeval (_root_.UniversalEnvelopingAlgebra.ι R (b i)) (p i (a i))).prod := by
  rw [pbwPolynomialBasis, Basis.map_apply, Basis.piTensorProduct_apply,
    pbwPolynomialEquiv_tprod]

end Module.Basis
