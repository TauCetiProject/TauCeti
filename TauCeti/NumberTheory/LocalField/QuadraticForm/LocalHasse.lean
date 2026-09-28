/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Induction
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Descent
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.NumberTheory.HilbertSymbol.Binary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
public import TauCeti.NumberTheory.LocalField.NatCastValuation
import TauCeti.NumberTheory.LocalField.SquareClasses

/-!
# The local Hasse invariant in odd residue characteristic

For a regular diagonal form `⟨a₁, …, aₙ⟩` over a nonarchimedean local field with odd
residue characteristic, its local Hasse invariant is the sign
`∏_{i<j} (aᵢ, aⱼ)ₖ`. Witt's chain theorem makes this independent of the diagonalization:
the Hilbert symbol is symmetric, multiplicative, and constant on isometric binary forms.

This odd-residue construction supplies one case of the roadmap's unrestricted `localHasse`.
The dyadic case requires the unrestricted Hilbert-symbol laws and is not defined here.

The orthogonal-sum formula has a cross term given by the Hilbert symbol of the two
discriminants. This is the convention of Serre's `ε` and Lam's `s`; O'Meara's product
over `i ≤ j` uses a different convention.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3.
-/

/- The construction and proofs are adapted from
`TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse`. -/

public section

open Finset QuadraticMap ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace RegularFormClass

section Auxiliary

variable [Invertible (2 : K)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localHasseProd_eq_of_permutationStep
    {n : ℕ} {w w' : Fin n → Kˣ} (h : PermutationStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) :=
  h.prod_prod_Ioi_eq hilbertSymbol_comm

private theorem localHasseProd_eq_of_binaryStep (h2 : IsUnit (2 : 𝒪[K]))
    {n : ℕ} {w w' : Fin n → Kˣ} (h : BinaryStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) := by
  exact h.prod_prod_Ioi_eq (fun a b c => hilbertSymbol_mul_left h2 c a b)
    (fun _ _ _ _ h => hilbertSymbol_eq_of_equivalent_binary h)

omit [Invertible (2 : K)] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
private theorem localHasseProd_rankOne (a b : Kˣ) :
    ∏ i : Fin 1, ∏ _j ∈ Ioi i, hilbertSymbol a a =
      ∏ i : Fin 1, ∏ _j ∈ Ioi i, hilbertSymbol b b := by
  simp

private theorem localHasseProd_scale (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ)
    {n : ℕ} (w : Fin n → Kˣ) :
    (∏ i, ∏ j ∈ Ioi i, hilbertSymbol (a * w i) (a * w j)) =
      (∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j)) *
        hilbertSymbol a (-1) ^ n.choose 2 *
        hilbertSymbol a (∏ i, w i) ^ (n - 1) :=
  prod_prod_Ioi_scale (s := -1) hilbertSymbol
    (hilbertSymbol_mul_right h2) hilbertSymbol_one_right hilbertSymbol_comm
    hilbertSymbol_self a w

end Auxiliary

/-- The product of pairwise Hilbert symbols on a regular-form class over a local field
of odd residue characteristic. It is independent of the diagonal presentation. -/
noncomputable def localHasseOfOdd (h2 : IsUnit (2 : 𝒪[K])) :
    RegularFormClass K → ℤˣ := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact liftDiagonal
    (fun p => ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j))
    localHasseProd_eq_of_permutationStep
    (localHasseProd_eq_of_binaryStep h2)
    (fun a b _ => localHasseProd_rankOne a b)

/-- On a diagonal presentation, the local Hasse invariant is the product of pairwise
Hilbert symbols. -/
@[simp]
theorem localHasseOfOdd_mk (h2 : IsUnit (2 : 𝒪[K])) (p : RegularFormPresentation K) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact liftDiagonal_mk _ localHasseProd_eq_of_permutationStep
    (localHasseProd_eq_of_binaryStep h2)
    (fun a b _ => localHasseProd_rankOne a b) p

/-- The local Hasse invariant of a regular form is read from any diagonalization. -/
theorem localHasseOfOdd_formClass (h2 : IsUnit (2 : 𝒪[K]))
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {n : ℕ}
    (w : Fin n → Kˣ) (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfOdd h2 (formClass Q hQ) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]),
    localHasseOfOdd_mk]

/-- The local Hasse invariant is `1` in ranks zero and one. -/
theorem localHasseOfOdd_eq_one_of_rank_le_one (h2 : IsUnit (2 : 𝒪[K]))
    {x : RegularFormClass K} (hx : x.rank ≤ 1) : localHasseOfOdd h2 x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    rw [localHasseOfOdd_mk]
    refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
    have hij := Fin.lt_def.mp (mem_Ioi.mp hj)
    have hj := j.isLt
    omega

/-- Every regular rank-one form has trivial local Hasse invariant. -/
theorem localHasseOfOdd_mk_rankOne (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = 1 :=
  localHasseOfOdd_eq_one_of_rank_le_one h2 (by rw [rank_mk])

/-- The local Hasse invariant of a binary form is its Hilbert symbol. -/
@[simp high]
theorem localHasseOfOdd_mk_binary (h2 : IsUnit (2 : 𝒪[K])) (a b : Kˣ) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      hilbertSymbol a b := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [localHasseOfOdd_mk]
  simp [Fin.prod_univ_succ]

/-- The empty diagonal form has trivial local Hasse invariant. -/
@[simp]
theorem localHasseOfOdd_zero (h2 : IsUnit (2 : 𝒪[K])) :
    localHasseOfOdd h2 (0 : RegularFormClass K) = 1 :=
  localHasseOfOdd_eq_one_of_rank_le_one h2 (by simp)

/-- The line `⟨1⟩` has trivial local Hasse invariant. -/
@[simp]
theorem localHasseOfOdd_one (h2 : IsUnit (2 : 𝒪[K])) :
    localHasseOfOdd h2 (1 : RegularFormClass K) = 1 :=
  localHasseOfOdd_eq_one_of_rank_le_one h2 rank_one.le

/-- The hyperbolic plane `⟨1, -1⟩` has trivial local Hasse invariant. -/
@[simp]
theorem localHasseOfOdd_hyperbolicClass (h2 : IsUnit (2 : 𝒪[K])) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfOdd h2 (hyperbolicClass K) = 1 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [hyperbolicClass_def, localHasseOfOdd_mk_binary, hilbertSymbol_one_left]

/-- The Hasse invariant of an orthogonal sum of diagonal presentations. The cross term
is the Hilbert symbol of their coefficient products. -/
theorem localHasseOfOdd_add_mk (h2 : IsUnit (2 : 𝒪[K]))
    (p q : RegularFormPresentation K) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p +
      Quotient.mk (regularFormSetoid K) q) =
      localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) *
        localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) q) *
        hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [mk_add_mk, RegularFormPresentation.append_def,
    localHasseOfOdd_mk, localHasseOfOdd_mk, localHasseOfOdd_mk]
  exact prod_prod_Ioi_append_of_mul hilbertSymbol hilbertSymbol_one_left
    hilbertSymbol_one_right (fun a b c => hilbertSymbol_mul_left h2 c a b)
    (hilbertSymbol_mul_right h2) p.2 q.2

/-- Scaling the coefficients of a diagonal presentation changes the local Hasse invariant
by a correction for each coefficient pair and a correction involving the discriminant. -/
theorem localHasseOfOdd_mk_scale (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ)
    (p : RegularFormPresentation K) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K)
      ⟨p.1, fun i => a * p.2 i⟩) =
      localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 *
        hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [localHasseOfOdd_mk, localHasseOfOdd_mk]
  exact localHasseProd_scale h2 a p.2

/-- Scaling by a rank-one class changes the local Hasse invariant by the Hilbert symbol
of the scale with `-1` for each coefficient pair, and with the coefficient product
for each of the remaining `p.1 - 1` occurrences. -/
theorem localHasseOfOdd_mk_rankOne_mul_mk (h2 : IsUnit (2 : 𝒪[K]))
    (a : Kˣ) (p : RegularFormPresentation K) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ *
      Quotient.mk (regularFormSetoid K) p) =
      localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 *
        hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [mk_mul_mk, RegularFormPresentation.rankOne_tmul, localHasseOfOdd_mk_scale]

/-- Orthogonal sum multiplies the two local Hasse invariants and the Hilbert
symbol of their discriminants as a cross term. -/
theorem localHasseOfOdd_add (h2 : IsUnit (2 : 𝒪[K])) (x y : RegularFormClass K) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfOdd h2 (x + y) = localHasseOfOdd h2 x * localHasseOfOdd h2 y *
      hilbertSymbolOnSquareClasses (discr x) (discr y) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      simpa only [discr_mk, hilbertSymbolOnSquareClasses_squareClass] using
        localHasseOfOdd_add_mk h2 p q

/-- Scaling a regular-form class by `⟨a⟩` changes its local Hasse invariant by the
Hilbert symbol of `a` with `-1` and with the class's discriminant. -/
theorem localHasseOfOdd_mk_rankOne_mul (h2 : IsUnit (2 : 𝒪[K]))
    (a : Kˣ) (x : RegularFormClass K) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
      localHasseOfOdd h2 x * hilbertSymbol a (-1) ^ (rank x).choose 2 *
        hilbertSymbolOnSquareClasses (squareClass a) (discr x) ^ (rank x - 1) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  induction x using Quotient.inductionOn with
  | h p =>
    simpa only [rank_mk, discr_mk, hilbertSymbolOnSquareClasses_squareClass] using
      localHasseOfOdd_mk_rankOne_mul_mk h2 a p

/-- Some regular binary form has negative local Hasse invariant. -/
theorem exists_localHasseOfOdd_eq_neg_one (h2 : IsUnit (2 : 𝒪[K])) :
    ∃ x : RegularFormClass K, localHasseOfOdd h2 x = -1 := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one h2 (not_isSquare_uniformizer hπ)
  exact ⟨Quotient.mk _ ⟨2, ![π, b]⟩, by simpa using hb⟩

end RegularFormClass

end TauCeti
