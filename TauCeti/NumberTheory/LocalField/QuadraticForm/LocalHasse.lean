/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Descent
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.NumberTheory.HilbertSymbol.Binary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Induction
public import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# The local Hasse sign in odd residue characteristic

For a regular quadratic form over a nonarchimedean local field with odd residue characteristic,
the local Hasse sign is the product of Hilbert symbols of pairs of diagonal coefficients. It is
independent of the diagonalization and therefore belongs to the isometry class, rather than to a
chosen list of coefficients. In odd residue characteristic, `2` is a unit of the valuation ring;
the corresponding norm-index theorem supplies the bimultiplicativity used in the descent.

The convention is `∏_{i<j} (aᵢ,aⱼ)`, as in Lam, *Introduction to Quadratic Forms over Fields*,
V.3.17, and Serre, *A Course in Arithmetic*, IV §2. The value is `1` in ranks zero and one.
-/

public section

open Finset QuadraticMap ValuativeRel

namespace TauCeti.RegularFormClass

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The Hilbert symbol on square classes of a nonarchimedean local field. -/
noncomputable def hilbertSymbolOnSquareClasses (x y : SquareClassGroup K) : ℤˣ :=
  hilbertSymbol (Additive.toMul (Quotient.out x)) (Additive.toMul (Quotient.out y))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The square-class pairing agrees with the Hilbert symbol on representatives. -/
@[simp]
theorem hilbertSymbolOnSquareClasses_squareClass (a b : Kˣ) :
    hilbertSymbolOnSquareClasses (squareClass a) (squareClass b) = hilbertSymbol a b := by
  unfold hilbertSymbolOnSquareClasses
  apply hilbertSymbol_congr_sq
  · apply (squareClass_eq_iff_isSquare_mul _ _).mp
    rw [squareClass_def, ofMul_toMul]
    exact Quotient.out_eq _
  · apply (squareClass_eq_iff_isSquare_mul _ _).mp
    rw [squareClass_def, ofMul_toMul]
    exact Quotient.out_eq _

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localHasseProd_eq_of_permutationStep (h2 : IsUnit (2 : 𝒪[K]))
    {n : ℕ} {w w' : Fin n → Kˣ} (h : PermutationStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact h.prod_prod_Ioi_eq hilbertSymbol_comm

private theorem localHasseProd_eq_of_binaryStep (h2 : IsUnit (2 : 𝒪[K]))
    {n : ℕ} {w w' : Fin n → Kˣ} (h : BinaryStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  exact h.prod_prod_Ioi_eq
    (fun a b c => hilbertSymbol_mul_left h2 c a b)
    (fun _ _ _ _ he => hilbertSymbol_eq_of_equivalent_binary he)

/-- The Hasse sign of an isometry class of regular forms over a nonarchimedean local field of odd
residue characteristic. It is the product of pairwise norm-equation Hilbert symbols on any
diagonal presentation. -/
noncomputable def localHasseOfIsUnitTwo (h2 : IsUnit (2 : 𝒪[K])) : RegularFormClass K → ℤˣ :=
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  liftDiagonal (fun p => ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j))
    (localHasseProd_eq_of_permutationStep h2) (localHasseProd_eq_of_binaryStep h2)
    (fun _ _ _ => by simp)

/-- The local Hasse sign of a diagonal presentation is its pairwise product of Hilbert symbols. -/
@[simp]
theorem localHasseOfIsUnitTwo_mk (h2 : IsUnit (2 : 𝒪[K])) (p : RegularFormPresentation K) :
    localHasseOfIsUnitTwo h2 (Quotient.mk (regularFormSetoid K) p) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j) :=
  by
    let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    exact liftDiagonal_mk _ (localHasseProd_eq_of_permutationStep h2)
      (localHasseProd_eq_of_binaryStep h2) (fun _ _ _ => by simp) p

/-- The Hasse sign is trivial in ranks zero and one. -/
theorem localHasseOfIsUnitTwo_eq_one_of_rank_le_one (h2 : IsUnit (2 : 𝒪[K]))
    {q : RegularFormClass K} (hq : q.rank ≤ 1) : localHasseOfIsUnitTwo h2 q = 1 := by
  induction q using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hq
    rw [localHasseOfIsUnitTwo_mk]
    refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
    have hij := Fin.lt_def.mp (mem_Ioi.mp hj)
    have hj' := j.isLt
    omega

/-- The zero class has trivial local Hasse sign. -/
@[simp]
theorem localHasseOfIsUnitTwo_zero (h2 : IsUnit (2 : 𝒪[K])) :
    localHasseOfIsUnitTwo h2 (0 : RegularFormClass K) = 1 :=
  localHasseOfIsUnitTwo_eq_one_of_rank_le_one h2 (by simp)

/-- A regular form has the Hasse sign of any of its diagonalizations. -/
theorem localHasseOfIsUnitTwo_formClass (h2 : IsUnit (2 : 𝒪[K]))
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {n : ℕ}
    (w : Fin n → Kˣ) (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfIsUnitTwo h2 (formClass Q hQ) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]),
    localHasseOfIsUnitTwo_mk]

/-- A unary diagonal form has trivial local Hasse sign. -/
theorem localHasseOfIsUnitTwo_mk_rankOne (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ) :
    localHasseOfIsUnitTwo h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = 1 :=
  localHasseOfIsUnitTwo_eq_one_of_rank_le_one h2 (by rw [rank_mk])

/-- A binary diagonal form has Hasse sign equal to its one Hilbert symbol. -/
@[simp 1100]
theorem localHasseOfIsUnitTwo_mk_binary (h2 : IsUnit (2 : 𝒪[K])) (a b : Kˣ) :
    localHasseOfIsUnitTwo h2 (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      hilbertSymbol a b := by
  rw [localHasseOfIsUnitTwo_mk]
  simp [Fin.prod_univ_succ]

/-- For diagonal forms, the Hasse sign of an orthogonal sum is the product of the two signs
times the Hilbert symbol of their discriminant representatives. The proof is adapted from
`RegularFormClass.hasseInvariant_add_mk`. -/
theorem localHasseOfIsUnitTwo_add_mk (h2 : IsUnit (2 : 𝒪[K]))
    (p q : RegularFormPresentation K) :
    localHasseOfIsUnitTwo h2 (Quotient.mk (regularFormSetoid K) p +
      Quotient.mk (regularFormSetoid K) q) =
      localHasseOfIsUnitTwo h2 (Quotient.mk (regularFormSetoid K) p) *
        localHasseOfIsUnitTwo h2 (Quotient.mk (regularFormSetoid K) q) *
        hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
  let h₁ (a : Kˣ) : Kˣ →* ℤˣ := {
    toFun := hilbertSymbol a
    map_one' := hilbertSymbol_one_right a
    map_mul' := hilbertSymbol_mul_right h2 a }
  let h₂ (b : Kˣ) : Kˣ →* ℤˣ := {
    toFun := fun a => hilbertSymbol a b
    map_one' := hilbertSymbol_one_left b
    map_mul' := fun a c => hilbertSymbol_mul_left h2 b a c }
  rw [mk_add_mk, localHasseOfIsUnitTwo_mk,
    localHasseOfIsUnitTwo_mk, localHasseOfIsUnitTwo_mk]
  rw [RegularFormPresentation.prod_prod_Ioi_append]
  congr 1
  calc
    (∏ i, ∏ j, hilbertSymbol (p.2 i) (q.2 j)) =
        ∏ i, hilbertSymbol (p.2 i) (∏ j, q.2 j) := by
          apply Finset.prod_congr rfl
          intro i _
          exact (map_prod (h₁ (p.2 i)) q.2 Finset.univ).symm
    _ = hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) :=
      (map_prod (h₂ (∏ j, q.2 j)) p.2 Finset.univ).symm

/-- The Hasse sign of an orthogonal sum, with its cross term on square-class discriminants. -/
theorem localHasseOfIsUnitTwo_add (h2 : IsUnit (2 : 𝒪[K]))
    (x y : RegularFormClass K) :
    letI : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
    localHasseOfIsUnitTwo h2 (x + y) =
      localHasseOfIsUnitTwo h2 x * localHasseOfIsUnitTwo h2 y *
        hilbertSymbolOnSquareClasses (discr x) (discr y) := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_isUnit_two h2)
      simpa only [discr_mk, hilbertSymbolOnSquareClasses_squareClass] using
        localHasseOfIsUnitTwo_add_mk h2 p q

end TauCeti.RegularFormClass
