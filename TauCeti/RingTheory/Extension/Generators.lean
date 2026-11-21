/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Generators

/-!
# Families of generators: extensionality and base change

Let `P` be a family of generators of an `R`-algebra `S`, that is, a surjection `R[ι] → S`.

## Main results

* `Algebra.Generators.algHom_ext`: two `R`-algebra homomorphisms out of `S` agreeing on the
  generators of `P` are equal.
* `Algebra.Generators.algebraMap_baseChange_map`: the base change of `P` along `R → T` is
  compatible with `P`: on polynomials with coefficients in `R`, the map `T[ι] → T ⊗[R] S` is
  `R[ι] → S` followed by `S → T ⊗[R] S`.
-/

public section

open MvPolynomial TensorProduct

namespace Algebra.Generators

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Generators R S ι)

/-- Two `R`-algebra homomorphisms out of `S` that agree on the generators of `P` are equal. -/
theorem algHom_ext {T : Type*} [Semiring T] [Algebra R T] {f g : S →ₐ[R] T}
    (h : ∀ i, f (P.val i) = g (P.val i)) : f = g :=
  (AlgHom.cancel_right P.aeval_val_surjective).1 <| MvPolynomial.algHom_ext fun i ↦ by simp [h]

/-- The base change `T[ι] → T ⊗[R] S` of generators `P` of `S` extends `R[ι] → S`: on
polynomials with coefficients in `R`, it is `R[ι] → S` followed by `S → T ⊗[R] S`. -/
theorem algebraMap_baseChange_map (T : Type*) [CommRing T] [Algebra R T] (x : P.Ring) :
    algebraMap (P.baseChange T).Ring (T ⊗[R] S) (map (algebraMap R T) x) =
      Algebra.TensorProduct.includeRight (algebraMap P.Ring S x) := by
  simp [algebraMap_apply, aeval_map_algebraMap, comp_aeval_apply, funext (baseChange_val T P)]

end Algebra.Generators
