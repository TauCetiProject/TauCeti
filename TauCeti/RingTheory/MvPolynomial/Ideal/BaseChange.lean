/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Ideals under base change of multivariate polynomials

Faithfully flat extension of the coefficient ring reflects membership in any ideal of the
polynomial ring, with no finiteness restriction on the ideal or the variables.
-/

public section

namespace Ideal

attribute [local instance] MvPolynomial.algebraMvPolynomial Algebra.TensorProduct.rightAlgebra in
/-- Extending an ideal along a faithfully flat coefficient map and then contracting recovers
the original ideal. -/
theorem comap_map_mvPolynomial_eq_self_of_faithfullyFlat {σ R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal (MvPolynomial σ R)) {f : R →+* S} (hf : f.FaithfullyFlat) :
    (I.map (MvPolynomial.map f)).comap (MvPolynomial.map f) = I := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  let e := Algebra.IsPushout.equiv R (MvPolynomial σ R) S (MvPolynomial σ S)
  have : Module.FaithfullyFlat (MvPolynomial σ R) (MvPolynomial σ S) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ e.symm.toLinearEquiv
  exact I.comap_map_eq_self_of_faithfullyFlat (B := MvPolynomial σ S)

end Ideal
