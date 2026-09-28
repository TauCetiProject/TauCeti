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

/-!
# The Hasse sign over a local field of odd residue characteristic

For a regular form diagonalized as `⟨a₁, …, aₙ⟩`, the Hasse sign is the product of the
norm-equation Hilbert symbols `(aᵢ, aⱼ)` over `i < j`. The sign is independent of the
diagonalization: the Hilbert symbol is symmetric, takes equal values on isometric binary
forms, and is multiplicative in the first argument when two is a unit of the valuation ring.

Together with dimension and discriminant, this sign enters the classification of regular
quadratic forms over local fields. The assumption that two is a unit excludes residue
characteristic two, where the norm groups require different arithmetic arguments.

The descent construction and orthogonal-sum and scaling formulas adapt the formalization
of `TauCeti.RegularFormClass.hasseInvariant` in
`TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse` to the local Hilbert sign.
O'Meara's `i ≤ j` Hasse symbol differs from this `i < j` sign by the Hilbert symbol of
the unsigned discriminant with `-1`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20.
-/

public section
noncomputable section

open Finset QuadraticMap ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace RegularFormClass

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem oddHasseProd_eq_of_permutationStep {n : ℕ} {w w' : Fin n → Kˣ}
    (h2 : IsUnit (2 : 𝒪[K])) (h : PermutationStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact h.prod_prod_Ioi_eq hilbertSymbol_comm

private theorem oddHasseProd_eq_of_binaryStep {n : ℕ} {w w' : Fin n → Kˣ}
    (h2 : IsUnit (2 : 𝒪[K])) (h : BinaryStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) := by
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact h.prod_prod_Ioi_eq (fun a b c => hilbertSymbol_mul_left h2 c a b)
    (fun _ _ _ _ hab => hilbertSymbol_eq_of_equivalent_binary hab)

/-- The pairwise-product Hasse sign of a regular-form class over a local field in which
two is a unit of the valuation ring. It uses the Lam–Serre `i < j` convention. -/
def oddResidueHasse (h2 : IsUnit (2 : 𝒪[K])) : RegularFormClass K → ℤˣ := by
  letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact liftDiagonal (fun p => ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j))
    (oddHasseProd_eq_of_permutationStep h2) (oddHasseProd_eq_of_binaryStep h2)
    (fun _ _ _ => by simp)

/-- On a diagonal presentation, the Hasse sign is the product of its pairwise Hilbert symbols. -/
@[simp]
theorem oddResidueHasse_mk (h2 : IsUnit (2 : 𝒪[K])) (p : RegularFormPresentation K) :
    oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) p) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j) := by
  simp only [oddResidueHasse, liftDiagonal_mk]

/-- O'Meara's `i ≤ j` Hasse symbol of local Hilbert signs is the Lam–Serre Hasse sign times
the symbol of the unsigned discriminant with `-1`. -/
theorem oddResidueOmearaHasseSymbol_eq (h2 : IsUnit (2 : 𝒪[K]))
    (p : RegularFormPresentation K) :
    (∏ i, ∏ j ∈ Ici i, hilbertSymbol (p.2 i) (p.2 j)) =
      oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbolOnSquareClasses
          (letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
           discr (Quotient.mk (regularFormSetoid K) p)) (squareClass (-1 : Kˣ)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  let f : Kˣ →* ℤˣ :=
    { toFun := fun a => hilbertSymbol a (-1)
      map_one' := hilbertSymbol_one_left _
      map_mul' := fun a b => hilbertSymbol_mul_left h2 _ a b }
  have hdiag : (∏ i, hilbertSymbol (p.2 i) (p.2 i)) =
      hilbertSymbol (∏ i, p.2 i) (-1) := by
    simp_rw [hilbertSymbol_self]
    exact (map_prod f p.2 Finset.univ).symm
  rw [prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag, oddResidueHasse_mk, discr_mk,
    hilbertSymbolOnSquareClasses_squareClass, hdiag, mul_comm]

/-- The Hasse sign of a regular form is computed from any diagonalization of that form. -/
theorem oddResidueHasse_formClass (h2 : IsUnit (2 : 𝒪[K]))
    {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {n : ℕ} (w : Fin n → Kˣ)
    (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    (letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
     oddResidueHasse h2 (formClass Q hQ) =
       ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]),
    oddResidueHasse_mk]

/-- A regular form of rank at most one has Hasse sign one. -/
theorem oddResidueHasse_eq_one_of_rank_le_one (h2 : IsUnit (2 : 𝒪[K]))
    {x : RegularFormClass K} (hx : x.rank ≤ 1) :
    oddResidueHasse h2 x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    rw [oddResidueHasse_mk]
    refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
    have hij := Fin.lt_def.mp (mem_Ioi.mp hj)
    omega

/-- The zero class has Hasse sign one. -/
@[simp]
theorem oddResidueHasse_zero (h2 : IsUnit (2 : 𝒪[K])) :
    oddResidueHasse h2 (0 : RegularFormClass K) = 1 :=
  oddResidueHasse_eq_one_of_rank_le_one h2 (by simp)

/-- The unit class has Hasse sign one. -/
@[simp]
theorem oddResidueHasse_one (h2 : IsUnit (2 : 𝒪[K])) :
    oddResidueHasse h2 (1 : RegularFormClass K) = 1 :=
  oddResidueHasse_eq_one_of_rank_le_one h2 rank_one.le

/-- A rank-one diagonal form has Hasse sign one. -/
theorem oddResidueHasse_mk_rankOne (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ) :
    oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = 1 :=
  oddResidueHasse_eq_one_of_rank_le_one h2 (by rw [rank_mk])

/-- The Hasse sign of a binary diagonal form is its Hilbert symbol. -/
@[simp high]
theorem oddResidueHasse_mk_binary (h2 : IsUnit (2 : 𝒪[K])) (a b : Kˣ) :
    oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      hilbertSymbol a b := by
  rw [oddResidueHasse_mk]
  simp [Fin.prod_univ_succ]

/-- The Hasse sign of an orthogonal sum of diagonal forms. -/
theorem oddResidueHasse_add_mk (h2 : IsUnit (2 : 𝒪[K]))
    (p q : RegularFormPresentation K) :
    oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) p +
      Quotient.mk (regularFormSetoid K) q) =
      oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) p) *
        oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) q) *
        hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [mk_add_mk, RegularFormPresentation.append_def, oddResidueHasse_mk,
    oddResidueHasse_mk, oddResidueHasse_mk]
  exact prod_prod_Ioi_append_of_mul hilbertSymbol hilbertSymbol_one_left
    hilbertSymbol_one_right (fun a b c => hilbertSymbol_mul_left h2 c a b)
    (hilbertSymbol_mul_right h2) p.2 q.2

/-- The Hasse sign of an orthogonal sum of regular-form classes. -/
theorem oddResidueHasse_add (h2 : IsUnit (2 : 𝒪[K])) (x y : RegularFormClass K) :
    (letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
     oddResidueHasse h2 (x + y) = oddResidueHasse h2 x * oddResidueHasse h2 y *
       hilbertSymbolOnSquareClasses (discr x) (discr y)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      simpa only [discr_mk, hilbertSymbolOnSquareClasses_squareClass] using
        oddResidueHasse_add_mk h2 p q

/-- Scaling a diagonal form changes its Hasse sign by the rank and coefficient product. -/
theorem oddResidueHasse_mk_scale (h2 : IsUnit (2 : 𝒪[K]))
    (a : Kˣ) (p : RegularFormPresentation K) :
    oddResidueHasse h2 (Quotient.mk (regularFormSetoid K)
      ⟨p.1, fun i => a * p.2 i⟩) =
      oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 *
        hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [oddResidueHasse_mk, oddResidueHasse_mk]
  exact prod_prod_Ioi_scale (s := -1) hilbertSymbol
    (hilbertSymbol_mul_right h2) hilbertSymbol_comm a
    (hilbertSymbol_self a) p.2

/-- Scaling a diagonal form by a rank-one class. -/
theorem oddResidueHasse_mk_rankOne_mul_mk (h2 : IsUnit (2 : 𝒪[K]))
    (a : Kˣ) (p : RegularFormPresentation K) :
    (letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
     oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ *
       Quotient.mk (regularFormSetoid K) p) =
       oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) p) *
         hilbertSymbol a (-1) ^ p.1.choose 2 *
         hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [mk_mul_mk, RegularFormPresentation.rankOne_tmul, oddResidueHasse_mk_scale]

/-- Scaling a regular-form class by a rank-one class. -/
theorem oddResidueHasse_mk_rankOne_mul (h2 : IsUnit (2 : 𝒪[K]))
    (a : Kˣ) (x : RegularFormClass K) :
    (letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
     oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
       oddResidueHasse h2 x * hilbertSymbol a (-1) ^ (rank x).choose 2 *
         hilbertSymbolOnSquareClasses (squareClass a) (discr x) ^ (rank x - 1)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  induction x using Quotient.inductionOn with
  | h p =>
    simpa only [rank_mk, discr_mk, hilbertSymbolOnSquareClasses_squareClass] using
      oddResidueHasse_mk_rankOne_mul_mk h2 a p

end RegularFormClass
end TauCeti
