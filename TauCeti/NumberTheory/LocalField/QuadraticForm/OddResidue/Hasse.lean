/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Induction
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Descent
public import TauCeti.NumberTheory.HilbertSymbol.Binary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# The Hasse sign over a local field of odd residue characteristic

For a regular form diagonalized as `⟨a₁, …, aₙ⟩`, the Hasse sign is the product of the
norm-equation Hilbert symbols `(aᵢ, aⱼ)` over `i < j`. The sign is independent of the
diagonalization: the Hilbert symbol is symmetric, takes equal values on isometric binary
forms, and is multiplicative in the first argument when two is a unit of the valuation ring.

The construction uses the same diagonal-chain descent as the Brauer-valued Hasse invariant.
Its odd-residue hypothesis records the presently available norm-index theorem; the
definition applies directly to the isometry classes needed for local classification.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
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

/-- The Hasse sign of a regular form is computed from any diagonalization of that form. -/
theorem oddResidueHasse_formClass [Invertible (2 : K)] (h2 : IsUnit (2 : 𝒪[K]))
    {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {n : ℕ} (w : Fin n → Kˣ)
    (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    oddResidueHasse h2 (formClass Q hQ) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) := by
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

/-- The Hasse sign of a binary diagonal form is its Hilbert symbol. -/
theorem oddResidueHasse_mk_binary (h2 : IsUnit (2 : 𝒪[K])) (a b : Kˣ) :
    oddResidueHasse h2 (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      hilbertSymbol a b := by
  rw [oddResidueHasse_mk]
  simp [Fin.prod_univ_succ]

end RegularFormClass
end TauCeti
