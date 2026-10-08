/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The trivial-coefficient homomorphism of a path algebra

Reading off the coordinates of an element of a path algebra on the trivial paths gives the
algebra homomorphism `TauCeti.PathAlgebra.trivialCoeff : pathAlgebra k Q →ₐ[k] (Q → k)`.
Concatenation adds path lengths, so a product path is trivial exactly when both factors are
trivial at the same vertex. This makes the coordinate projection multiplicative.

The map needs only a commutative base semiring and finitely many vertices. It is onto: a family
of coefficients is represented by the corresponding linear combination of vertex idempotents.
It kills every path of positive length and sends each vertex idempotent to the indicator of
that vertex. Its kernel is the arrow ideal. Over a commutative ring it induces the equivalence
`TauCeti.PathAlgebra.quotientArrowIdealAlgEquiv` of the quotient by the arrow ideal with `Q → k`,
constructed in `TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient`.

## Main definitions and results

* `TauCeti.PathAlgebra.trivialCoeff`: the trivial-coordinate algebra homomorphism.
* `TauCeti.PathAlgebra.trivialCoeff_apply`: evaluation on a vertex is the corresponding path
  coordinate.
* `TauCeti.PathAlgebra.trivialCoeff_ofPath_of_length_pos` and
  `TauCeti.PathAlgebra.trivialCoeff_ofArrow`: positive-length paths and arrows map to zero.
* `TauCeti.PathAlgebra.trivialCoeff_vertexIdempotent`: the vertex idempotent maps to its indicator.
* `TauCeti.PathAlgebra.trivialCoeff_surjective`: every family of trivial coordinates occurs.

## References

Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. II and III.
-/

public section

universe u v w

namespace TauCeti.PathAlgebra

/-! ### The trivial-coefficient homomorphism -/

section TrivialCoordinates

variable (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q]

variable {k Q} in
/-- The coordinate of a basis path on the trivial path at its own vertex. -/
private theorem repr_nil_single_self (v : Q) (c : k) :
    (pathAlgebraBasis k Q).repr
        (single (⟨v, v, Quiver.Path.nil⟩ : Quiver.TotalPath Q) c) ⟨v, v, Quiver.Path.nil⟩ = c := by
  rw [pathAlgebraBasis_repr_single, Finsupp.single_eq_same]

variable {k Q} in
/-- The coordinate of any other basis path on the trivial path at `v` vanishes. -/
private theorem repr_nil_single_of_ne {v : Q} {x : Quiver.TotalPath Q}
    (hx : x ≠ ⟨v, v, Quiver.Path.nil⟩) (c : k) :
    (pathAlgebraBasis k Q).repr (single x c) ⟨v, v, Quiver.Path.nil⟩ = 0 := by
  rw [pathAlgebraBasis_repr_single, Finsupp.single_eq_of_ne' hx]

variable {k Q} in
/-- Multiplicativity of the trivial coordinates on two basis paths: concatenation adds lengths, so
the concatenation is trivial exactly when both factors are. -/
private theorem repr_nil_single_mul_single (v : Q) (x y : Quiver.TotalPath Q) (a b : k) :
    (pathAlgebraBasis k Q).repr (single x a * single y b : pathAlgebra k Q)
        ⟨v, v, Quiver.Path.nil⟩ =
      (pathAlgebraBasis k Q).repr (single x a : pathAlgebra k Q) ⟨v, v, Quiver.Path.nil⟩ *
        (pathAlgebraBasis k Q).repr (single y b : pathAlgebra k Q) ⟨v, v, Quiver.Path.nil⟩ := by
  by_cases hx : x = (⟨v, v, Quiver.Path.nil⟩ : Quiver.TotalPath Q)
  · subst hx
    by_cases hy : y = (⟨v, v, Quiver.Path.nil⟩ : Quiver.TotalPath Q)
    · subst hy
      rw [single_mul_single_of_comp Quiver.Path.nil Quiver.Path.nil, Quiver.Path.nil_comp,
        repr_nil_single_self, repr_nil_single_self, repr_nil_single_self]
    · rw [repr_nil_single_of_ne hy, mul_zero]
      -- the product is either zero or the second factor again, and the second factor is not
      -- the trivial path at `v`
      by_cases hcomp : y.2.1 = v
      · obtain ⟨c, d, q⟩ := y
        subst hcomp
        rw [single_mul_single_of_comp Quiver.Path.nil q, Quiver.Path.comp_nil]
        exact repr_nil_single_of_ne hy _
      · rw [single_mul_single_of_not_composable hcomp, map_zero, Finsupp.zero_apply]
  · rw [repr_nil_single_of_ne hx, zero_mul]
    by_cases hcomp : y.2.1 = x.1
    · obtain ⟨s, t, p⟩ := x
      obtain ⟨c, d, q⟩ := y
      subst hcomp
      rw [single_mul_single_of_comp p q]
      refine repr_nil_single_of_ne (fun hz => hx ?_) _
      obtain ⟨hc, hlen⟩ := Quiver.TotalPath.eq_nil_iff.1 hz
      rw [Quiver.Path.length_comp, Nat.add_eq_zero_iff] at hlen
      refine Quiver.TotalPath.eq_nil_iff.2 ⟨?_, hlen.2⟩
      exact (q.eq_of_length_zero hlen.1).symm.trans hc
    · rw [single_mul_single_of_not_composable hcomp, map_zero, Finsupp.zero_apply]

variable {k Q} in
/-- Multiplicativity of the trivial coordinates. -/
private theorem repr_nil_mul (v : Q) (f g : pathAlgebra k Q) :
    (pathAlgebraBasis k Q).repr (f * g) ⟨v, v, Quiver.Path.nil⟩ =
      (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ *
        (pathAlgebraBasis k Q).repr g ⟨v, v, Quiver.Path.nil⟩ := by
  induction f using induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ =>
    rw [add_mul, map_add, Finsupp.add_apply, ih₁, ih₂, map_add, Finsupp.add_apply, add_mul]
  | single x a =>
    induction g using induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ =>
      rw [mul_add, map_add, Finsupp.add_apply, ih₁, ih₂, map_add, Finsupp.add_apply, mul_add]
    | single y b => exact repr_nil_single_mul_single v x y a b

variable [Finite Q]

variable {k Q} in
/-- The unit has coordinate `1` on every trivial path. -/
private theorem repr_nil_one (v : Q) :
    (pathAlgebraBasis k Q).repr (1 : pathAlgebra k Q) ⟨v, v, Quiver.Path.nil⟩ = 1 := by
  let := Fintype.ofFinite Q
  rw [one_def, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single v]
  · rw [vertexIdempotent_eq_single, repr_nil_single_self]
  · intro w _ hw
    rw [vertexIdempotent_eq_single]
    exact repr_nil_single_of_ne (fun h => hw (Quiver.TotalPath.eq_nil_iff.1 h).1) _
  · intro h
    exact absurd (Finset.mem_univ v) h

end TrivialCoordinates

section TrivialCoeff

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- **The trivial-coefficient homomorphism** of a path algebra: an element is sent to the family of
its coordinates on the trivial paths, one for each vertex. Concatenation adds lengths, so this is
multiplicative. It is surjective with kernel the arrow ideal. Over a commutative ring it induces
`TauCeti.PathAlgebra.quotientArrowIdealAlgEquiv`, the equivalence of the quotient by the arrow ideal
with `Q → k` constructed in `TauCeti.RepresentationTheory.Quiver.SemisimpleQuotient`. -/
noncomputable def trivialCoeff : pathAlgebra k Q →ₐ[k] (Q → k) where
  toFun f v := (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩
  map_one' := funext fun v => repr_nil_one v
  map_mul' f g := funext fun v => repr_nil_mul v f g
  map_zero' := funext fun _ => by simp
  map_add' f g := funext fun _ => by simp
  commutes' r := funext fun v => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, repr_nil_one v,
      smul_eq_mul, mul_one, Pi.algebraMap_apply, Algebra.algebraMap_self_apply]

variable {k Q}

/-- The trivial-coefficient homomorphism reads off a coordinate for the path basis. -/
@[simp]
theorem trivialCoeff_apply (f : pathAlgebra k Q) (v : Q) :
    trivialCoeff k Q f v = (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ :=
  (rfl)

/-- A basis path of positive length has all its trivial coordinates zero. -/
@[simp]
theorem trivialCoeff_ofPath_of_length_pos {x : Quiver.TotalPath Q} (hx : 0 < x.2.2.length) :
    trivialCoeff k Q (ofPath x) = 0 := by
  funext v
  rw [trivialCoeff_apply, ofPath_eq_single]
  exact repr_nil_single_of_ne (fun h => (Nat.ne_of_gt hx) (Quiver.TotalPath.eq_nil_iff.1 h).2) 1

/-- An arrow has all its trivial coordinates zero: the arrows are what the trivial-coefficient
homomorphism kills. Deliberately not a `simp` lemma, `TauCeti.PathAlgebra.ofArrow_eq_ofPath`
already rewriting its left-hand side. -/
theorem trivialCoeff_ofArrow {a b : Q} (e : a ⟶ b) : trivialCoeff k Q (ofArrow e) = 0 := by
  rw [ofArrow_eq_ofPath]
  exact trivialCoeff_ofPath_of_length_pos (by simp)

/-- The vertex idempotent at `v` is sent to the indicator of `v`. -/
@[simp]
theorem trivialCoeff_vertexIdempotent [DecidableEq Q] (v : Q) :
    trivialCoeff k Q (vertexIdempotent k v) = Pi.single v 1 := by
  funext w
  rw [trivialCoeff_apply, vertexIdempotent_eq_single]
  by_cases hvw : v = w
  · subst hvw
    rw [repr_nil_single_self, Pi.single_eq_same]
  · rw [repr_nil_single_of_ne (fun h => hvw (Quiver.TotalPath.eq_nil_iff.1 h).1) 1,
      Pi.single_eq_of_ne (Ne.symm hvw)]

variable (k Q)

/-- **Every family of scalars is the family of trivial coordinates of an element**: the
trivial-coefficient homomorphism is onto, a preimage of `c` being `∑ᵥ c v • eᵥ`. -/
theorem trivialCoeff_surjective : Function.Surjective (trivialCoeff k Q) := by
  let := Fintype.ofFinite Q
  intro c
  refine ⟨∑ v : Q, c v • vertexIdempotent k v, funext fun w => ?_⟩
  rw [trivialCoeff_apply, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single w]
  · rw [vertexIdempotent_eq_single, smul_single, mul_one, repr_nil_single_self]
  · intro u _ hu
    rw [vertexIdempotent_eq_single, smul_single]
    exact repr_nil_single_of_ne (fun h => hu (Quiver.TotalPath.eq_nil_iff.1 h).1) _
  · intro h
    exact absurd (Finset.mem_univ w) h

end TrivialCoeff

end TauCeti.PathAlgebra
