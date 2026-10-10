/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.HookLength.Formula
public import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Idempotent
-- Non-public: the comparison of the two Specht-module presentations and the standard basis of the
-- Specht module are both used inside proofs, never in the type of an exported declaration.
import TauCeti.RepresentationTheory.Symmetric.Specht.Comparison
import TauCeti.RepresentationTheory.Symmetric.Specht.StandardBasis

/-!
# The dimension of a Young-symmetrizer ideal, and the scalar of essential idempotence

The Young symmetrizer `c_t` of a tableau `t` of shape `μ` is essentially idempotent:
`TauCeti.YoungTableau.youngSymmetrizer_sq` says that
```
c_t * c_t = (n! / dim_ℚ ℚ[Sₙ] c_t) • c_t,
```
with the scalar carrying the dimension of the left ideal `ℚ[Sₙ] c_t` because that is what the
trace computation produces. This file evaluates that dimension and so puts the scalar in two
closed forms.

The dimension is the number `f^μ` of standard Young tableaux of shape `μ`
(`TauCeti.YoungTableau.finrank_spechtIdeal`): the ideal is equivalent, as a representation, to
the polytabloid Specht module `S^μ`
(`TauCeti.YoungTableau.spechtIdealEquivSpechtSubrepresentation`), and the standard polytabloids
are a basis of that module (`TauCeti.finrank_spechtSubrepresentation`). Hence essential
idempotence reads
```
c_t * c_t = (n! / f^μ) • c_t,
```
and, through the multiplicative hook-length formula
`TauCeti.standardCount_mul_prod_hookLength`, the division-free reading
```
c_t * c_t = (∏_{c ∈ μ} hookLength μ c) • c_t.
```
The second is the sharper statement: the scalar is a product of positive integers, visible from
the shape alone, so the normalisation that makes `c_t` a genuine idempotent is
`(∏ hooks)⁻¹ • c_t`.

## Main results

* `TauCeti.YoungTableau.finrank_spechtIdeal`: **the dimension of `ℚ[Sₙ] c_t` is `f^μ`.**
* `TauCeti.YoungTableau.finrank_spechtIdeal_mul_prod_hookLength` and
  `TauCeti.YoungTableau.finrank_spechtIdeal_eq_factorial_div_prod_hookLength`: the hook-length
  formula for that dimension, in multiplicative and in quotient form.
* `TauCeti.YoungTableau.youngSymmetrizer_sq_eq_factorial_div_standardCount`: **essential
  idempotence with the scalar `n! / f^μ`**, and
  `TauCeti.YoungTableau.standardCount_smul_youngSymmetrizer_sq` its division-free form.
* `TauCeti.YoungTableau.youngSymmetrizer_sq_eq_prod_hookLength`: **essential idempotence with the
  scalar read off the hook lengths**, with
  `TauCeti.YoungTableau.isIdempotentElem_prod_hookLength_inv_smul_youngSymmetrizer` the
  normalisation it gives, and
  `TauCeti.YoungTableau.youngSymmetrizerOver_sq_eq_prod_hookLength` the same identity in a
  `ℚ`-algebra.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lemma 4.26, where the
  scalar is `n! / dim V_λ`.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, for the hook-length formula.
-/

public section

open Finset Module

open scoped Nat

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ### The dimension of the ideal -/

-- Not a `simp` lemma, and cannot be one:
-- `TauCeti.YoungTableau.finrank_spechtIdeal_eq_spechtSubrepresentation` and
-- `TauCeti.finrank_spechtSubrepresentation` are both `simp` lemmas, so `simp` already rewrites
-- this left-hand side to `standardCount μ` in two steps, and `simpNF` rejects the tag as a
-- duplicate ("simp can prove this"). A consumer that imports this module without also importing
-- the comparison and the standard basis rewrites with `finrank_spechtIdeal` by name.
/-- **The dimension of the Young-symmetrizer ideal is the number of standard Young tableaux**,
`dim_ℚ ℚ[Sₙ] c_t = f^μ`. The ideal and the polytabloid Specht module `S^μ` are equivalent
representations, and the standard polytabloids are a basis of the latter. -/
theorem finrank_spechtIdeal (t : YoungTableau μ) :
    finrank ℚ (spechtIdeal t) = standardCount μ := by
  rw [finrank_spechtIdeal_eq_spechtSubrepresentation]
  exact finrank_spechtSubrepresentation μ

/-- **The hook-length formula for the dimension of the Young-symmetrizer ideal**, in
multiplicative form: the dimension of `ℚ[Sₙ] c_t`, times the product of the hook lengths of the
shape of `t`, is `n !`. -/
theorem finrank_spechtIdeal_mul_prod_hookLength (t : YoungTableau μ) :
    finrank ℚ (spechtIdeal t) * ∏ c ∈ μ.cells, μ.hookLength c = μ.card ! := by
  rw [finrank_spechtIdeal, standardCount_mul_prod_hookLength]

/-- **The hook-length formula for the dimension of the Young-symmetrizer ideal**, in quotient
form. The division is exact, by `YoungDiagram.prod_hookLength_dvd_factorial`. -/
theorem finrank_spechtIdeal_eq_factorial_div_prod_hookLength (t : YoungTableau μ) :
    finrank ℚ (spechtIdeal t) = μ.card ! / ∏ c ∈ μ.cells, μ.hookLength c := by
  rw [finrank_spechtIdeal, standardCount_eq_factorial_div_prod_hookLength]

/-! ### The scalar of essential idempotence -/

/-- **Essential idempotence of the Young symmetrizer, division-free.** The number `f^μ` of
standard Young tableaux of the shape of `t`, times the square of `c_t`, is `n !` times `c_t`. -/
theorem standardCount_smul_youngSymmetrizer_sq (t : YoungTableau μ) :
    (standardCount μ : ℚ) • (youngSymmetrizer t * youngSymmetrizer t) =
      (μ.card ! : ℚ) • youngSymmetrizer t := by
  rw [← finrank_spechtIdeal t, finrank_spechtIdeal_smul_youngSymmetrizer_sq]

/-- **Essential idempotence of the Young symmetrizer, in terms of the tableau count.** The square
of `c_t` is `c_t` scaled by `n !` over the number `f^μ` of standard Young tableaux of its
shape. -/
theorem youngSymmetrizer_sq_eq_factorial_div_standardCount (t : YoungTableau μ) :
    youngSymmetrizer t * youngSymmetrizer t =
      ((μ.card ! : ℚ) / (standardCount μ : ℚ)) • youngSymmetrizer t := by
  rw [← finrank_spechtIdeal t, youngSymmetrizer_sq]

/-- **Essential idempotence of the Young symmetrizer, read off the shape.** The square of `c_t` is
`c_t` scaled by the product of the hook lengths of its shape -- a product of positive integers, so
this form of the identity carries no division. -/
theorem youngSymmetrizer_sq_eq_prod_hookLength (t : YoungTableau μ) :
    youngSymmetrizer t * youngSymmetrizer t =
      (∏ c ∈ μ.cells, (μ.hookLength c : ℚ)) • youngSymmetrizer t := by
  rw [youngSymmetrizer_sq_eq_factorial_div_standardCount,
    cast_factorial_div_standardCount_eq_prod_hookLength]

/-- **The normalised Young symmetrizer is idempotent**, with the normalisation
`(f^μ / n !) • c_t`. -/
theorem isIdempotentElem_standardCount_div_factorial_smul_youngSymmetrizer (t : YoungTableau μ) :
    IsIdempotentElem (((standardCount μ : ℚ) / (μ.card ! : ℚ)) • youngSymmetrizer t) := by
  rw [← finrank_spechtIdeal t]
  exact isIdempotentElem_smul_youngSymmetrizer t

/-- **The normalised Young symmetrizer is idempotent**, with the normalisation read off the shape:
dividing `c_t` by the product of the hook lengths of its shape makes it idempotent. -/
theorem isIdempotentElem_prod_hookLength_inv_smul_youngSymmetrizer (t : YoungTableau μ) :
    IsIdempotentElem ((∏ c ∈ μ.cells, (μ.hookLength c : ℚ))⁻¹ • youngSymmetrizer t) := by
  rw [← one_div, ← cast_factorial_div_standardCount_eq_prod_hookLength, one_div_div]
  exact isIdempotentElem_standardCount_div_factorial_smul_youngSymmetrizer t

/-- **Essential idempotence over a `ℚ`-algebra, read off the shape.** The transported Young
symmetrizer squares to the product of the hook lengths of its shape, now read in `k`, times
itself. Unlike `TauCeti.YoungTableau.youngSymmetrizerOver_sq`, whose scalar is a quotient in `ℚ`
pushed forward along the structure map, this scalar is a product of natural numbers in `k`. -/
theorem youngSymmetrizerOver_sq_eq_prod_hookLength (k : Type*) [CommSemiring k] [Algebra ℚ k]
    (t : YoungTableau μ) :
    youngSymmetrizerOver k t * youngSymmetrizerOver k t =
      (∏ c ∈ μ.cells, (μ.hookLength c : k)) • youngSymmetrizerOver k t := by
  have hprod : (∏ c ∈ μ.cells, (μ.hookLength c : k))
      = algebraMap ℚ k (∏ c ∈ μ.cells, (μ.hookLength c : ℚ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun c _ => (map_natCast (algebraMap ℚ k) _).symm
  rw [youngSymmetrizerOver_sq, finrank_spechtIdeal,
    cast_factorial_div_standardCount_eq_prod_hookLength, ← hprod]

end YoungTableau

end TauCeti
