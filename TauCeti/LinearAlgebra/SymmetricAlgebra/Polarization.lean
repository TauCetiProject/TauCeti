/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import Mathlib.LinearAlgebra.Dual.Basis
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
import TauCeti.RingTheory.MvPolynomial.Polarization

/-!
# Polarization in a symmetric algebra

Let `V` be a finite-dimensional vector space over a field `K` of characteristic zero. The
symmetric algebra `S(V*)` of its dual is the algebra of polynomial functions on `V`: a vector `v`
evaluates `p : S(V*)` through `SymmetricAlgebra.lift (Module.Dual.eval K V v)`. Call a set
`S ⊆ V` polynomially dense when the only polynomial function vanishing at every point of `S` is
zero.

The `n`-th powers `v ^ n` of the vectors of a polynomially dense set span the whole degree-`n`
component of `S(V)`. This is the coordinate-free form of
`TauCeti.MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule`, to which it is reduced by a
basis of `V` and its dual basis: the first identifies `S(V)` with a polynomial ring in which
`v ^ n` becomes the `n`-th power of the linear form with the coordinates of `v`, and the second
identifies the polynomial functions on `V` with polynomials in those coordinates.

## Main results

* `TauCeti.SymmetricAlgebra.span_pow_eq_homogeneous_of_polynomial_vanishing`: the `n`-th powers of
  the vectors of a polynomially dense set span the degree-`n` component of `S(V)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
-/

public section

namespace TauCeti.SymmetricAlgebra

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Polarization.** Over a field of characteristic zero, let `S` be a polynomially dense subset
of a finite-dimensional space `V`: the only polynomial function `p : S(V*)` vanishing at every
point of `S` is zero. Then the `n`-th powers of the vectors of `S` span the degree-`n` component
of the symmetric algebra `S(V)`. -/
theorem span_pow_eq_homogeneous_of_polynomial_vanishing (S : Set V)
    (hS : ∀ p : SymmetricAlgebra K (Module.Dual K V),
      (∀ v ∈ S, SymmetricAlgebra.lift (Module.Dual.eval K V v) p = 0) → p = 0) (n : ℕ) :
    Submodule.span K ((fun v ↦ SymmetricAlgebra.ι K V v ^ n) '' S) =
      homogeneousSubmodule K V n := by
  let b := Module.finBasis K V
  let e := SymmetricAlgebra.equivMvPolynomial b
  -- the coordinate vectors of `S` are polynomially dense, through the dual basis
  have hS' : ∀ q, (∀ x ∈ b.equivFun '' S, MvPolynomial.eval x q = 0) → q = 0 := by
    intro q hq
    have hzero := hS ((SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm q) fun v hv ↦ by
      rw [b.dualBasis.lift_apply_eq_eval_equivMvPolynomial,
        AlgEquiv.apply_symm_apply]
      simpa [Module.Basis.dualBasis_apply] using hq _ ⟨v, hv, rfl⟩
    simpa using hzero
  -- through `e`, the power `v ^ n` is the power of the linear form with the coordinates of `v`
  have himage : e.toLinearMap '' ((fun v ↦ SymmetricAlgebra.ι K V v ^ n) '' S) =
      (fun x ↦ (∑ i, x i • MvPolynomial.X i : MvPolynomial (Fin _) K) ^ n) ''
        (b.equivFun '' S) := by
    simp only [Set.image_image, AlgEquiv.toLinearMap_apply, map_pow,
      SymmetricAlgebra.equivMvPolynomial_ι, Module.Basis.constr_apply_fintype, e]
  apply Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective
  rw [Submodule.map_span, himage, map_homogeneousSubmodule_equivMvPolynomial,
    TauCeti.MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule _ hS' n]

end TauCeti.SymmetricAlgebra
