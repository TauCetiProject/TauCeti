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

/-!
# The local Hasse invariant

Let `K` be a nonarchimedean local field in which `2` is invertible, in any residue
characteristic. For a regular quadratic form diagonalized as `⟨a₁, …, aₙ⟩`, the local Hasse
invariant is the product `∏_{i<j} (aᵢ, aⱼ)_K ∈ {±1}` of norm-equation Hilbert symbols, with the
empty product in ranks `0` and `1`. It is defined on `TauCeti.RegularFormClass`, so it depends
only on the isometry class of the form.

That the product does not depend on the diagonalization is Witt's chain theorem, through the
descent principle `TauCeti.RegularFormClass.liftDiagonal`: the Hilbert symbol is symmetric, takes
equal values on isometric binary forms, and is bimultiplicative over a local field, the last
including the dyadic case (`TauCeti.hilbertSymbol_mul_left`).

Together with the rank and the discriminant, this sign is the third invariant in the
classification of regular quadratic forms over a nonarchimedean local field. It is the
`{±1}`-valued counterpart of the Brauer-valued `TauCeti.RegularFormClass.hasseInvariant` of
`TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse`, whose construction and whose
orthogonal-sum and scaling formulas are adapted here to the Hilbert symbol. O'Meara's `i ≤ j`
Hasse symbol differs from this `i < j` sign by the Hilbert symbol of the discriminant with `-1`.

## Main definitions

* `TauCeti.RegularFormClass.localHasse`: the local Hasse invariant of an isometry class of
  regular quadratic forms.

## Main results

* `TauCeti.RegularFormClass.localHasse_mk`: its value `∏_{i<j} (aᵢ, aⱼ)_K` on a diagonal
  presentation `⟨a₁, …, aₙ⟩`.
* `TauCeti.RegularFormClass.localHasse_congr`: isometric diagonal forms have the same local
  Hasse invariant.
* `TauCeti.RegularFormClass.localHasse_formClass`: the same value on the class of any regular
  form isometric to `⟨a₁, …, aₙ⟩`.
* `TauCeti.RegularFormClass.localHasse_add`: `s(q ⊥ r) = s(q) · s(r) · (d(q), d(r))_K`.
* `TauCeti.RegularFormClass.localHasse_mk_rankOne_mul`: the formula for scaling by a unit.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20.
-/

public section
noncomputable section

open Finset QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

namespace RegularFormClass

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localHasseProd_eq_of_permutationStep {n : ℕ} {w w' : Fin n → Kˣ}
    (h : PermutationStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) :=
  h.prod_prod_Ioi_eq hilbertSymbol_comm

private theorem localHasseProd_eq_of_binaryStep {n : ℕ} {w w' : Fin n → Kˣ}
    (h : BinaryStep w w') :
    ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w' i) (w' j) :=
  h.prod_prod_Ioi_eq (fun a b c => hilbertSymbol_mul_left (Invertible.ne_zero 2) c a b)
    fun _ _ _ _ hab => hilbertSymbol_eq_of_equivalent_binary hab

/-- **The local Hasse invariant** of an isometry class of regular quadratic forms over a
nonarchimedean local field: for a diagonal presentation `⟨a₁, …, aₙ⟩` of the class, the product
`∏_{i<j} (aᵢ, aⱼ)_K` of Hilbert symbols, which is `1` in ranks `0` and `1`. It does not depend on
the presentation. -/
def localHasse : RegularFormClass K → ℤˣ :=
  liftDiagonal (fun p => ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j))
    localHasseProd_eq_of_permutationStep localHasseProd_eq_of_binaryStep fun _ _ _ => by simp

/-- The local Hasse invariant of the class of a diagonal presentation `⟨a₁, …, aₙ⟩` is
`∏_{i<j} (aᵢ, aⱼ)_K`. -/
@[simp]
theorem localHasse_mk (p : RegularFormPresentation K) :
    localHasse (Quotient.mk (regularFormSetoid K) p) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (p.2 i) (p.2 j) := by
  simp only [localHasse, liftDiagonal_mk]

/-- **The local Hasse invariant descends along `Quotient.mk`.** Isometric diagonal forms
`⟨a₁, …, aₘ⟩ ≅ ⟨b₁, …, bₙ⟩` have the same local Hasse invariant; by `localHasse_mk` this is
`∏_{i<j} (aᵢ, aⱼ)_K = ∏_{i<j} (bᵢ, bⱼ)_K`. -/
theorem localHasse_congr {m n : ℕ} {w : Fin m → Kˣ} {w' : Fin n → Kˣ}
    (h : (weightedSumSquares K fun i => (w i : K)).Equivalent
      (weightedSumSquares K fun i => (w' i : K))) :
    localHasse (Quotient.mk (regularFormSetoid K) ⟨m, w⟩) =
      localHasse (Quotient.mk (regularFormSetoid K) ⟨n, w'⟩) :=
  congrArg localHasse <|
    mk_eq_mk_iff.mpr (by simpa only [presentedForm_eq_weightedSumSquares_coe] using h)

/-- O'Meara's `i ≤ j` Hasse symbol of local Hilbert symbols is the local Hasse invariant times
the symbol of the discriminant with `-1`. -/
theorem omearaLocalHasseSymbol_eq (p : RegularFormPresentation K) :
    (∏ i, ∏ j ∈ Ici i, hilbertSymbol (p.2 i) (p.2 j)) =
      localHasse (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbolOnSquareClasses (discr (Quotient.mk (regularFormSetoid K) p))
          (squareClass (-1 : Kˣ)) := by
  let f : Kˣ →* ℤˣ :=
    { toFun := fun a => hilbertSymbol a (-1)
      map_one' := hilbertSymbol_one_left _
      map_mul' := fun a b => hilbertSymbol_mul_left (Invertible.ne_zero 2) _ a b }
  have hdiag : (∏ i, hilbertSymbol (p.2 i) (p.2 i)) = hilbertSymbol (∏ i, p.2 i) (-1) := by
    simp_rw [hilbertSymbol_self]
    exact (map_prod f p.2 Finset.univ).symm
  rw [prod_prod_Ici_eq_prod_prod_Ioi_mul_prod_diag, localHasse_mk, discr_mk,
    hilbertSymbolOnSquareClasses_squareClass, hdiag]

/-- The local Hasse invariant of a regular form isometric to `⟨a₁, …, aₙ⟩` is
`∏_{i<j} (aᵢ, aⱼ)_K`. -/
theorem localHasse_formClass {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {n : ℕ}
    (w : Fin n → Kˣ) (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    localHasse (formClass Q hQ) = ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) := by
  rw [formClass_mk Q hQ ⟨n, w⟩ (by rwa [presentedForm_eq_weightedSumSquares_coe]),
    localHasse_mk]

/-- The local Hasse invariant is trivial in ranks `0` and `1`. -/
theorem localHasse_eq_one_of_rank_le_one {x : RegularFormClass K} (hx : x.rank ≤ 1) :
    localHasse x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    rw [localHasse_mk]
    refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
    have hij := Fin.lt_def.mp (mem_Ioi.mp hj)
    omega

/-- The zero class has trivial local Hasse invariant. -/
@[simp]
theorem localHasse_zero : localHasse (0 : RegularFormClass K) = 1 :=
  localHasse_eq_one_of_rank_le_one (by simp)

/-- The unit class `⟨1⟩` has trivial local Hasse invariant. -/
@[simp]
theorem localHasse_one : localHasse (1 : RegularFormClass K) = 1 :=
  localHasse_eq_one_of_rank_le_one rank_one.le

/-- A rank-one diagonal form `⟨a⟩` has trivial local Hasse invariant. -/
theorem localHasse_mk_rankOne (a : Kˣ) :
    localHasse (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = 1 :=
  localHasse_eq_one_of_rank_le_one (by rw [rank_mk])

/-- The local Hasse invariant of a binary diagonal form `⟨a, b⟩` is its Hilbert symbol
`(a, b)_K`. -/
@[simp high]
theorem localHasse_mk_binary (a b : Kˣ) :
    localHasse (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) = hilbertSymbol a b := by
  rw [localHasse_mk]
  simp [Fin.prod_univ_succ]

/-- The orthogonal-sum formula on diagonal presentations: the local Hasse invariant of
`⟨a₁, …, aₘ⟩ ⊥ ⟨b₁, …, bₙ⟩` is `s⟨a⟩ · s⟨b⟩ · (∏ aᵢ, ∏ bⱼ)_K`. -/
theorem localHasse_add_mk (p q : RegularFormPresentation K) :
    localHasse (Quotient.mk (regularFormSetoid K) p + Quotient.mk (regularFormSetoid K) q) =
      localHasse (Quotient.mk (regularFormSetoid K) p) *
        localHasse (Quotient.mk (regularFormSetoid K) q) *
        hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) := by
  rw [mk_add_mk, RegularFormPresentation.append_def, localHasse_mk, localHasse_mk,
    localHasse_mk]
  exact prod_prod_Ioi_append_of_mul hilbertSymbol hilbertSymbol_one_left hilbertSymbol_one_right
    (fun a b c => hilbertSymbol_mul_left (Invertible.ne_zero 2) c a b)
    (hilbertSymbol_mul_right (Invertible.ne_zero 2)) p.2 q.2

/-- **The orthogonal-sum formula** `s(q ⊥ r) = s(q) · s(r) · (d(q), d(r))_K`, with the cross
term the Hilbert symbol of the two discriminants. -/
theorem localHasse_add (x y : RegularFormClass K) :
    localHasse (x + y) =
      localHasse x * localHasse y * hilbertSymbolOnSquareClasses (discr x) (discr y) := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      simpa only [discr_mk, hilbertSymbolOnSquareClasses_squareClass] using localHasse_add_mk p q

/-- The scaling formula on diagonal presentations: scaling `⟨a₁, …, aₙ⟩` by a unit `λ`
multiplies its local Hasse invariant by `(λ, -1)_K^{n(n-1)/2} · (λ, ∏ aᵢ)_K^{n-1}`. -/
theorem localHasse_mk_scale (a : Kˣ) (p : RegularFormPresentation K) :
    localHasse (Quotient.mk (regularFormSetoid K) ⟨p.1, fun i => a * p.2 i⟩) =
      localHasse (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 * hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  rw [localHasse_mk, localHasse_mk]
  exact prod_prod_Ioi_scale (s := -1) hilbertSymbol
    (hilbertSymbol_mul_right (Invertible.ne_zero 2)) hilbertSymbol_comm a
    (hilbertSymbol_self a) p.2

/-- The scaling formula for multiplication of a diagonal presentation by the rank-one class
`⟨λ⟩`. -/
theorem localHasse_mk_rankOne_mul_mk (a : Kˣ) (p : RegularFormPresentation K) :
    localHasse (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ *
      Quotient.mk (regularFormSetoid K) p) =
      localHasse (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 * hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  rw [mk_mul_mk, RegularFormPresentation.rankOne_tmul, localHasse_mk_scale]

/-- **The scaling formula** `s(λ • q) = s(q) · (λ, -1)_K^{n(n-1)/2} · (λ, d(q))_K^{n-1}` for a
class `q` of rank `n`, where `λ • q` is the product with the rank-one class `⟨λ⟩`. -/
theorem localHasse_mk_rankOne_mul (a : Kˣ) (x : RegularFormClass K) :
    localHasse (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
      localHasse x * hilbertSymbol a (-1) ^ (rank x).choose 2 *
        hilbertSymbolOnSquareClasses (squareClass a) (discr x) ^ (rank x - 1) := by
  induction x using Quotient.inductionOn with
  | h p =>
    simpa only [rank_mk, discr_mk, hilbertSymbolOnSquareClasses_squareClass] using
      localHasse_mk_rankOne_mul_mk a p

end RegularFormClass
end TauCeti
