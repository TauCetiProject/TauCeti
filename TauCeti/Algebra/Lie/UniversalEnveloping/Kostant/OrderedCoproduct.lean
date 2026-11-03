/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Comultiplication
public import TauCeti.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Coproducts of ordered mixed Kostant monomials

The root divided powers and Cartan binomial coefficients have the same coefficient-one
coproduct. `kostantGenerator` puts both families in the integral form, indexed by a disjoint
union. The coproduct of an ordered product is the sum over all coordinatewise splittings
of its exponents, with the original factor order retained in both tensor factors.

In particular, the formula applies to negative-root / Cartan / positive-root ordered
monomials without commuting or reordering any factors. It describes their actual integral
coproduct, not merely its image in the rational tensor square. No basis, independence,
Chevalley relations, or finite-dimensionality hypothesis is needed.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantFormComul_prod_ofFn_generator`: the
  coefficient-one expansion for any ordered mixed product, including the empty product.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type v} {κ : Type w}

attribute [local instance] TauCeti.moduleNNRat

/-- **The integral coproduct of an ordered mixed Kostant monomial.** Split each exponent
independently into two nonnegative parts and retain the original order in each tensor leg.
Every coefficient is one; repeated indices and noncommuting factors are allowed. -/
theorem kostantFormComul_prod_ofFn_generator (e : ι → L) (h : κ → L)
    {r : ℕ} (i : Fin r → ι ⊕ κ) (n : Fin r → ℕ) :
    kostantFormComul e h (List.ofFn fun j ↦ kostantGenerator e h (i j) (n j)).prod =
      ∑ p ∈ Fintype.piFinset (fun j ↦ Finset.antidiagonal (n j)),
        (List.ofFn fun j ↦ kostantGenerator e h (i j) (p j).1).prod ⊗ₜ[ℤ]
          (List.ofFn fun j ↦ kostantGenerator e h (i j) (p j).2).prod := by
  classical
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def]
  simp_rw [kostantFormComul_generator]
  -- Multilinearity expands the ordered product without a commutativity assumption.
  have hexpand := (MultilinearMap.mkPiAlgebraFin ℤ r
    (kostantForm e h ⊗[ℤ] kostantForm e h)).map_sum_finset
      (fun j p ↦ kostantGenerator e h (i j) p.1 ⊗ₜ[ℤ] kostantGenerator e h (i j) p.2)
      (fun j ↦ Finset.antidiagonal (n j))
  simp only [MultilinearMap.mkPiAlgebraFin_apply] at hexpand
  rw [hexpand]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simpa only [List.map_ofFn, Function.comp_def] using
    List.prod_map_tmul (R := ℤ) (List.ofFn (fun j : Fin r ↦ j))
      (fun j ↦ kostantGenerator e h (i j) (p j).1)
      (fun j ↦ kostantGenerator e h (i j) (p j).2)

end TauCeti.UniversalEnvelopingAlgebra
