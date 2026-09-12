/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Dimension
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# Schur polynomials at one and the Weyl dimension

Evaluating the Schur polynomial of a Young diagram `μ` at
`x₀ = ⋯ = xₙ₋₁ = 1` counts its semistandard tableaux with entries below `n`.  The
Gelfand--Tsetlin correspondence identifies those tableaux with the patterns over the weight of
`μ`, and the Gelfand--Tsetlin dimension formula identifies the resulting count with
`TauCeti.weylDimension`.

This file assembles those three existing descriptions into the numerical specialization of the
Weyl character formula for `GL n`:

`s_μ(1, …, 1) = # BoundedSSYT n μ = weylDimension (weightOfShape n μ)`.

The determinant-normalized form applies the same comparison to an arbitrary dominant integral
weight `l`.  Its polynomial shape `l.detShiftShape` has the same dimension because translating
all entries of a Gelfand--Tsetlin pattern by the determinant weight is a bijection.

## Main results

* `TauCeti.eval_one_diagramSchurPoly_eq_card_boundedSSYT`: evaluation at one is the bounded
  tableau count, over any commutative semiring.
* `TauCeti.card_boundedSSYT_eq_weylDimension`: the bounded tableau count is the Weyl dimension.
* `TauCeti.eval_one_diagramSchurPoly_eq_weylDimension`: the Schur polynomial of a bounded-height
  shape evaluates at one to its Weyl dimension.
* `TauCeti.eval_one_schurPoly_eq_weylDimension`: the same result for a partition-indexed Schur
  polynomial over an arbitrary finite alphabet.
* `TauCeti.eval_one_diagramSchurPoly_detShiftShape_eq_weylDimension`: the corresponding statement
  for the determinant-normalized shape of an arbitrary dominant weight.

## References

* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton1991], §15.3.
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- **A Schur polynomial evaluated at one counts bounded semistandard tableaux.**  Every monomial
in the tableau generating function contributes one, so the value is the cardinality of
`TauCeti.BoundedSSYT n μ`. -/
theorem eval_one_diagramSchurPoly_eq_card_boundedSSYT (n : ℕ) (μ : YoungDiagram) :
    eval (fun _ : Fin n => (1 : R)) (diagramSchurPoly n R μ) =
      (Nat.card (BoundedSSYT n μ) : R) := by
  rw [eval_diagramSchurPoly]
  simp only [one_pow, prod_const_one, sum_const, card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

/-- **Bounded semistandard tableaux are counted by the Weyl dimension formula.**  This is the
three-way combinatorial comparison: tableaux correspond to Gelfand--Tsetlin patterns with the
same top row, and those patterns are counted by `TauCeti.weylDimension`. -/
theorem card_boundedSSYT_eq_weylDimension (n : ℕ) (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ n) :
    Nat.card (BoundedSSYT n μ) = weylDimension (weightOfShape n μ) := by
  calc
    Nat.card (BoundedSSYT n μ) =
        Nat.card {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)} :=
      (card_gtPattern_topRow_eq_card_ssyt n μ hμ).symm
    _ = Nat.card {P : GTPattern n //
          P.topRow = (weightOfShape n μ : Fin n → ℤ)} := by
      congr 2
      ext P
      simp only [funext_iff, weightOfShape_apply]
    _ = weylDimension (weightOfShape n μ) :=
      GTPattern.card_topRow_eq_weylDimension (weightOfShape n μ)

/-- **The Schur polynomial at one is the Weyl dimension.**  For a Young diagram with at most
`n` rows, evaluating its Schur polynomial in `n` variables at all ones gives the Weyl product
attached to its dominant weight. -/
@[simp]
theorem eval_one_diagramSchurPoly_eq_weylDimension (n : ℕ) (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ n) :
    eval (fun _ : Fin n => (1 : R)) (diagramSchurPoly n R μ) =
      (weylDimension (weightOfShape n μ) : R) := by
  rw [eval_one_diagramSchurPoly_eq_card_boundedSSYT,
    card_boundedSSYT_eq_weylDimension n μ hμ]

/-- **A partition-indexed Schur polynomial at one is the Weyl dimension.**  This is
`TauCeti.eval_one_diagramSchurPoly_eq_weylDimension` transported from the ordered alphabet
`Fin (Fintype.card σ)` to an arbitrary finite alphabet `σ`. -/
@[simp]
theorem eval_one_schurPoly_eq_weylDimension {σ : Type*} [Fintype σ] {d : ℕ}
    (μ : d.Partition) (hμ : μ.parts.card ≤ Fintype.card σ) :
    eval (fun _ : σ => (1 : R)) (schurPoly σ R μ) =
      (weylDimension (weightOfShape (Fintype.card σ) (diagramOf μ)) : R) := by
  rw [schurPoly_eq_rename, eval_rename]
  simpa only [Function.comp_def] using
    (eval_one_diagramSchurPoly_eq_weylDimension
      (R := R) (Fintype.card σ) (diagramOf μ) (by simpa only [colLen_zero_diagramOf] using hμ))

/-- **Determinant-normalized Schur evaluation for a dominant weight.**  Evaluating the Schur
polynomial of `l.detShiftShape` at one gives the Weyl dimension of `l`; translating by the
determinant weight changes neither the Gelfand--Tsetlin pattern count nor the dimension. -/
@[simp]
theorem eval_one_diagramSchurPoly_detShiftShape_eq_weylDimension {n : ℕ}
    (l : DominantWeight n) :
    eval (fun _ : Fin n => (1 : R)) (diagramSchurPoly n R l.detShiftShape) =
      (weylDimension l : R) := by
  rw [eval_one_diagramSchurPoly_eq_card_boundedSSYT]
  exact congrArg (fun m : ℕ => (m : R))
    ((GTPattern.card_topWeight_eq_card_boundedSSYT_detShiftShape l).symm.trans
      (GTPattern.card_topWeight_eq_weylDimension l))

end TauCeti
