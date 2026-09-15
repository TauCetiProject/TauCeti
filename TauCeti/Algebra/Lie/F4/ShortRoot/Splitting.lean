/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.QuotientDerivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealDerivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationGradedInjectivity

/-!
# The derivations of the type-F4 multiplication in characteristic two

Over a ring of characteristic two the matrices differentiating the invariant symmetric
multiplication of the twenty-six-dimensional module of type `F₄` are exactly the combinations of
the twenty-six representing matrices `TauCeti.F4ShortRoot.quotientMatrix` and the twenty-six
multiplication operators `TauCeti.F4ShortRoot.multiplicationOperator`, with the short-root quotient
coordinates and single matrix entries as coefficients. Those fifty-two matrices are the represented
Chevalley algebra of type `F₄` modulo two, presented as the short-root ideal spanned by the
multiplication operators together with a complement mapping isomorphically to the quotient by it;
neither the Chevalley algebra nor the ideal is constructed here.

The inclusion of the span into the derivations is the content of
`TauCeti.Algebra.Lie.F4.ShortRoot.QuotientDerivation` and
`TauCeti.Algebra.Lie.F4.ShortRoot.IdealDerivation`. The reverse inclusion follows by decomposing a
derivation into root-lattice homogeneous parts and certifying the small linear system in each
degree. Subtracting from an arbitrary derivation the combination its coordinates prescribe leaves
a matrix whose homogeneous parts all vanish.

The splitting fails outside characteristic two: the multiplication operators span an ideal of the
Chevalley algebra only there, because the bracket of two short root vectors summing to a long root
carries the structure constant two.

## Main results

* `TauCeti.F4ShortRoot.eq_zero_of_isDerivation`: **a derivation with vanishing coordinates is
  zero.**
* `TauCeti.F4ShortRoot.eq_multiplicationBy_of_quotientCoordinate_eq_zero`: a derivation with
  vanishing short-root quotient coordinates is an operator of multiplication by a vector.
* `TauCeti.F4ShortRoot.eq_sum_quotientMatrix_add_multiplicationBy`: **the splitting of the
  derivations.**

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- **A derivation of the invariant multiplication with vanishing coordinates is zero.** -/
theorem eq_zero_of_isDerivation {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0) :
    X = 0 :=
  eq_zero_of_isDerivation_graded hX hq hi

/-! ## Coordinates of an operator of multiplication by a vector -/

omit [CharP R 2] in
/-- The quotient coordinates of a finite sum are the sum of the quotient coordinates. -/
theorem quotientCoordinate_sum {ι : Type*} (p : Fin 26) (s : Finset ι)
    (f : ι → Matrix (Fin 26) (Fin 26) R) :
    quotientCoordinate p (∑ i ∈ s, f i) = ∑ i ∈ s, quotientCoordinate p (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, quotientCoordinate_def]
    simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, quotientCoordinate_add, ih]

omit [CharP R 2] in
/-- The quotient coordinates of a difference are the difference of the quotient coordinates. -/
theorem quotientCoordinate_sub (p : Fin 26) (Y Z : Matrix (Fin 26) (Fin 26) R) :
    quotientCoordinate p (Y - Z) = quotientCoordinate p Y - quotientCoordinate p Z := by
  rw [sub_eq_add_neg, quotientCoordinate_add,
    show -Z = (-1 : R) • Z from (neg_one_smul R Z).symm, quotientCoordinate_smul]
  ring

/-- **An operator of multiplication by a vector differentiates the multiplication.** -/
theorem isDerivation_multiplicationBy (c : Fin 26 → R) : IsDerivation (multiplicationBy c) := by
  rw [multiplicationBy_def]
  exact IsDerivation.sum _ _ fun a _ => (isDerivation_map_multiplicationOperator a).smul (c a)

/-- **The short-root quotient coordinates annihilate every operator of multiplication by a
vector.** -/
theorem quotientCoordinate_multiplicationBy (p : Fin 26) (c : Fin 26 → R) :
    quotientCoordinate p (multiplicationBy c) = 0 := by
  rw [multiplicationBy_def, quotientCoordinate_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [quotientCoordinate_smul, quotientCoordinate_map_intCast,
    (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_multiplicationOperator p a),
    Int.cast_zero, mul_zero]

/-- **The ideal coordinates of an operator of multiplication by a vector are the coordinates of
that vector.** -/
theorem multiplicationBy_ideal (c : Fin 26 → R) (a : Fin 26) :
    multiplicationBy c (idealRow a) (idealCol a) = c a := by
  have hterm : ∀ b : Fin 26, (c b • (multiplicationOperator b).map (Int.cast : ℤ → R))
      (idealRow a) (idealCol a) = if b = a then c b else 0 := fun b => by
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      (CharP.intCast_eq_intCast R 2).mpr (multiplicationOperator_ideal a b)]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab, Ne.symm hab]
  rw [multiplicationBy_def, Matrix.sum_apply, Finset.sum_congr rfl fun b _ => hterm b,
    Finset.sum_ite_eq' Finset.univ a c]
  simp

/-! ## The splitting -/

/-- **A derivation with vanishing short-root quotient coordinates is an operator of multiplication
by a vector**, namely by the vector of its ideal coordinates. -/
theorem eq_multiplicationBy_of_quotientCoordinate_eq_zero {X : Matrix (Fin 26) (Fin 26) R}
    (hX : IsDerivation X) (hq : ∀ p, quotientCoordinate p X = 0) :
    X = multiplicationBy fun a => X (idealRow a) (idealCol a) := by
  refine sub_eq_zero.mp (eq_zero_of_isDerivation
    (hX.sub (isDerivation_multiplicationBy _)) (fun p => ?_) fun a => ?_)
  · rw [quotientCoordinate_sub, hq p, quotientCoordinate_multiplicationBy, sub_zero]
  · rw [Matrix.sub_apply, multiplicationBy_ideal, sub_self]

/-- **The splitting of the derivations of the invariant multiplication in characteristic two.**
Every derivation is the sum of a combination of the twenty-six representing matrices, with the
short-root quotient coordinates as coefficients, and an operator of multiplication by the vector
of its ideal coordinates. -/
theorem eq_sum_quotientMatrix_add_multiplicationBy {X : Matrix (Fin 26) (Fin 26) R}
    (hX : IsDerivation X) :
    X = (∑ q, quotientCoordinate q X • (quotientMatrix q).map (Int.cast : ℤ → R)) +
      multiplicationBy fun a => X (idealRow a) (idealCol a) := by
  set Y : Matrix (Fin 26) (Fin 26) R :=
    ∑ q, quotientCoordinate q X • (quotientMatrix q).map (Int.cast : ℤ → R) with hY
  have hYder : IsDerivation Y :=
    IsDerivation.sum _ _ fun q _ => (isDerivation_map_quotientMatrix q).smul _
  have hYcoord : ∀ p, quotientCoordinate p Y = quotientCoordinate p X := fun p => by
    rw [hY, quotientCoordinate_sum, Finset.sum_eq_single p]
    · rw [quotientCoordinate_smul, quotientCoordinate_map_intCast,
        (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_quotientMatrix p p)]
      simp
    · intro q _ hq
      rw [quotientCoordinate_smul, quotientCoordinate_map_intCast,
        (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_quotientMatrix p q)]
      simp [Ne.symm hq]
    · exact fun hp => absurd (Finset.mem_univ p) hp
  have hYideal : ∀ a, Y (idealRow a) (idealCol a) = 0 := fun a => by
    rw [hY, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      (CharP.intCast_eq_intCast R 2).mpr (quotientMatrix_ideal q a), Int.cast_zero, mul_zero]
  have hsub := eq_multiplicationBy_of_quotientCoordinate_eq_zero (hX.sub hYder) fun p => by
    rw [quotientCoordinate_sub, hYcoord p, sub_self]
  have hcol : (fun a => (X - Y) (idealRow a) (idealCol a)) =
      fun a => X (idealRow a) (idealCol a) := by
    funext a
    rw [Matrix.sub_apply, hYideal a, sub_zero]
  rw [hcol] at hsub
  rw [← hsub]
  abel

end TauCeti.F4ShortRoot
