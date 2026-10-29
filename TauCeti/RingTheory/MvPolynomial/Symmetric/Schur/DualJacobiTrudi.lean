/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.BetaNumbers
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.LinearAlgebra.Matrix.Determinant.Jacobi

/-!
# The dual Jacobi--Trudi identity

The Jacobi--Trudi identity `TauCeti.diagramSchurPoly_eq_det_hsymmInt` expresses the Schur
polynomial `s_μ` as a determinant of complete homogeneous symmetric polynomials.  Its dual
(transpose) form expresses the same polynomial as a determinant of elementary symmetric
polynomials:

`s_μ = det (e_{μᵀᵢ - i + j})_{0 ≤ i, j < c}`

for every `c` at least the number of columns of `μ`, in any number of variables and over any
commutative ring, where `μᵀ` is the transpose of `μ`.  The indices `μᵀᵢ - i + j` are integers and
`e_m = 0` for `m < 0`; this is `TauCeti.esymmInt`.  The statement is
`TauCeti.diagramSchurPoly_eq_det_esymmInt` for Young diagrams in the alphabet `Fin N`, and
`TauCeti.schurPoly_eq_det_esymmInt` for partitions in an arbitrary finite alphabet.

## The proof

The Toeplitz matrices `H = (h_{j - i})` and `E = ((-1)^{j - i} e_{j - i})` of
`TauCeti.hsymmToeplitz` and `TauCeti.esymmToeplitz` are inverse to each other and both have
determinant `1`, so `E` is the adjugate of `H` (`TauCeti.adjugate_hsymmToeplitz`).  Jacobi's
complementary minor identity `Matrix.det_mul_det_submatrix_adjugate`, applied to `H` with the
initial segment of `Fin (r + c)` as row set and the beta-set of `μ` as column set, expresses a
minor of `E` in terms of the corresponding minor of `H`.  The latter is `s_μ` by the primal
Jacobi--Trudi identity.  The complement of the beta-set of `μ` is the set of the `c` numbers
`r + p - μᵀ_p`, and after reindexing the complementary minor of `E` is the transpose
Jacobi--Trudi matrix, up to two diagonal sign matrices.  Their product with Jacobi's sign
`(-1)^{∑ I + ∑ J}` is `1` because that exponent is congruent to `2 |μ| + r (r - 1)` modulo `2`.

## Main results

* `TauCeti.diagramSchurPoly_eq_det_esymmInt`: **the dual Jacobi--Trudi identity** for the Schur
  polynomial of a Young diagram.
* `TauCeti.schurPoly_eq_det_esymmInt`: the dual Jacobi--Trudi identity for the Schur polynomial
  of a partition.
* `TauCeti.adjugate_hsymmToeplitz`: the adjugate of `TauCeti.hsymmToeplitz` is
  `TauCeti.esymmToeplitz`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, formula (3.5).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.16.1.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

/-! ### The beta-set and its complement in `Fin (r + c)` -/

section FinSets

/-- The `i`-th element of the beta-set of `μ` with `r` rows, as an element of `Fin (r + c)`. -/
private def betaFun {r c : ℕ} (μ : YoungDiagram) (hc : μ.rowLen 0 ≤ c) (i : Fin r) :
    Fin (r + c) :=
  ⟨μ.betaNumber r i, μ.betaNumber_lt_add hc i.isLt⟩

@[simp]
private lemma betaFun_val {r c : ℕ} (μ : YoungDiagram) (hc : μ.rowLen 0 ≤ c) (i : Fin r) :
    ((betaFun μ hc i : Fin (r + c)) : ℕ) = μ.betaNumber r i := rfl

private lemma betaFun_injective {r c : ℕ} (μ : YoungDiagram) (hc : μ.rowLen 0 ≤ c) :
    Function.Injective (betaFun (r := r) (c := c) μ hc) := by
  intro i j h
  exact (μ.strictAnti_betaNumber r).injective
    (by simpa only [betaFun_val] using congrArg Fin.val h)

/-- The `p`-th element of the complementary beta-set of `μ` with `r` rows. -/
private def complBetaFun {r c : ℕ} (μ : YoungDiagram) (_hr : μ.colLen 0 ≤ r) (p : Fin c) :
    Fin (r + c) :=
  ⟨μ.complBetaNumber r p, μ.complBetaNumber_lt p.isLt⟩

@[simp]
private lemma complBetaFun_val {r c : ℕ} (μ : YoungDiagram) (hr : μ.colLen 0 ≤ r) (p : Fin c) :
    ((complBetaFun μ hr p : Fin (r + c)) : ℕ) = μ.complBetaNumber r p := rfl

private lemma complBetaFun_injective {r c : ℕ} (μ : YoungDiagram) (hr : μ.colLen 0 ≤ r) :
    Function.Injective (complBetaFun (r := r) (c := c) μ hr) := by
  intro p q h
  exact (μ.strictMono_complBetaNumber hr).injective
    (by simpa only [complBetaFun_val] using congrArg Fin.val h)

private lemma complBetaFun_strictMono {r c : ℕ} (μ : YoungDiagram) (hr : μ.colLen 0 ≤ r) :
    StrictMono (complBetaFun (r := r) (c := c) μ hr) := by
  intro p q hpq
  simp only [Fin.lt_def, complBetaFun_val]
  exact μ.strictMono_complBetaNumber hr hpq

/-- The beta-set of `μ` with `r` rows, as a finset of `Fin (r + c)`. -/
private def betaSetFin {r c : ℕ} (μ : YoungDiagram) (hc : μ.rowLen 0 ≤ c) :
    Finset (Fin (r + c)) :=
  univ.image (betaFun μ hc)

/-- The complementary beta-set of `μ` with `r` rows, as a finset of `Fin (r + c)`. -/
private def complBetaSetFin {r c : ℕ} (μ : YoungDiagram) (hr : μ.colLen 0 ≤ r) :
    Finset (Fin (r + c)) :=
  univ.image (complBetaFun μ hr)

private def initialSet (r c : ℕ) : Finset (Fin (r + c)) :=
  univ.image (Fin.castAdd c)

private def terminalSet (r c : ℕ) : Finset (Fin (r + c)) :=
  univ.image (Fin.natAdd r)

private lemma mem_betaSetFin {r c : ℕ} {μ : YoungDiagram} {hc : μ.rowLen 0 ≤ c}
    {x : Fin (r + c)} :
    x ∈ betaSetFin (r := r) (c := c) μ hc ↔ ∃ i : Fin r, betaFun μ hc i = x := by
  rw [betaSetFin, mem_image]
  exact ⟨fun ⟨a, _, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, mem_univ a, ha⟩⟩

private lemma mem_complBetaSetFin {r c : ℕ} {μ : YoungDiagram} {hr : μ.colLen 0 ≤ r}
    {x : Fin (r + c)} :
    x ∈ complBetaSetFin (r := r) (c := c) μ hr ↔ ∃ p : Fin c, complBetaFun μ hr p = x := by
  rw [complBetaSetFin, mem_image]
  exact ⟨fun ⟨a, _, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, mem_univ a, ha⟩⟩

private lemma mem_initialSet {r c : ℕ} {x : Fin (r + c)} :
    x ∈ initialSet r c ↔ (x : ℕ) < r := by
  rw [initialSet, mem_image]
  constructor
  · rintro ⟨q, -, hq⟩
    have h : (q : ℕ) = (x : ℕ) := by simpa only [Fin.val_castAdd] using congrArg Fin.val hq
    omega
  · intro hx
    exact ⟨⟨x, hx⟩, mem_univ _, Fin.ext rfl⟩

private lemma mem_terminalSet {r c : ℕ} {x : Fin (r + c)} :
    x ∈ terminalSet r c ↔ r ≤ (x : ℕ) := by
  rw [terminalSet, mem_image]
  constructor
  · rintro ⟨q, -, hq⟩
    have h : r + (q : ℕ) = (x : ℕ) := by simpa only [Fin.val_natAdd] using congrArg Fin.val hq
    omega
  · intro hx
    refine ⟨⟨(x : ℕ) - r, by omega⟩, mem_univ _, Fin.ext ?_⟩
    simp only [Fin.val_natAdd]
    omega

private lemma card_betaSetFin {r c : ℕ} {μ : YoungDiagram} {hc : μ.rowLen 0 ≤ c} :
    #(betaSetFin (r := r) (c := c) μ hc) = r := by
  rw [betaSetFin, card_image_of_injective _ (betaFun_injective μ hc), card_univ,
    Fintype.card_fin]

private lemma card_complBetaSetFin {r c : ℕ} {μ : YoungDiagram} {hr : μ.colLen 0 ≤ r} :
    #(complBetaSetFin (r := r) (c := c) μ hr) = c := by
  rw [complBetaSetFin, card_image_of_injective _ (complBetaFun_injective μ hr), card_univ,
    Fintype.card_fin]

private lemma card_initialSet {r c : ℕ} : #(initialSet r c) = r := by
  rw [initialSet, card_image_of_injective _ (Fin.castAdd_injective r c), card_univ,
    Fintype.card_fin]

private lemma disjoint_betaSetFin_complBetaSetFin {r c : ℕ} {μ : YoungDiagram}
    (hc : μ.rowLen 0 ≤ c) (hr : μ.colLen 0 ≤ r) :
    Disjoint (betaSetFin (r := r) (c := c) μ hc) (complBetaSetFin (r := r) (c := c) μ hr) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_betaSetFin] at hx
  rw [mem_complBetaSetFin] at hx'
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨p, hp⟩ := hx'
  have hi := i.isLt
  have hp' := p.isLt
  have hval : μ.complBetaNumber r p = μ.betaNumber r i := by
    simpa only [complBetaFun_val, betaFun_val] using congrArg Fin.val hp
  have hle : μ.transpose.rowLen p ≤ r + p := by
    rw [μ.rowLen_transpose]
    exact ((μ.colLen_anti 0 (p : ℕ) (Nat.zero_le p)).trans hr).trans (Nat.le_add_right r (p : ℕ))
  simp only [YoungDiagram.complBetaNumber_def, YoungDiagram.betaNumber_def] at hval
  exact μ.rowLen_add_colLen_ne i p (by omega)

private lemma union_betaSetFin_complBetaSetFin {r c : ℕ} {μ : YoungDiagram}
    (hc : μ.rowLen 0 ≤ c) (hr : μ.colLen 0 ≤ r) :
    betaSetFin (r := r) (c := c) μ hc ∪ complBetaSetFin (r := r) (c := c) μ hr = univ := by
  refine eq_of_subset_of_card_le (fun x _ => mem_univ x) ?_
  rw [card_union_of_disjoint (disjoint_betaSetFin_complBetaSetFin hc hr), card_betaSetFin,
    card_complBetaSetFin, card_univ, Fintype.card_fin]

private lemma compl_betaSetFin {r c : ℕ} {μ : YoungDiagram} (hc : μ.rowLen 0 ≤ c)
    (hr : μ.colLen 0 ≤ r) :
    (betaSetFin (r := r) (c := c) μ hc)ᶜ = complBetaSetFin (r := r) (c := c) μ hr := by
  rw [compl_eq_univ_sdiff, ← union_betaSetFin_complBetaSetFin hc hr, union_sdiff_left,
    Finset.sdiff_eq_self_iff_disjoint, disjoint_comm]
  exact disjoint_betaSetFin_complBetaSetFin hc hr

private lemma initialSet_compl {r c : ℕ} : (initialSet r c)ᶜ = terminalSet r c := by
  ext x
  rw [mem_compl, mem_initialSet, mem_terminalSet]
  omega

private lemma initialSet_orderEmb_apply {r c : ℕ} (p : Fin r) :
    (initialSet r c).orderEmbOfFin card_initialSet p = Fin.castAdd c p := by
  have h : (fun p : Fin r => Fin.castAdd c p) =
      (initialSet r c).orderEmbOfFin card_initialSet := by
    refine orderEmbOfFin_unique _ (fun p => ?_) (Fin.strictMono_castAdd c)
    rw [mem_initialSet]
    exact p.isLt
  rw [← h]

private lemma betaSetFin_orderEmb_apply {r c : ℕ} {μ : YoungDiagram} {hc : μ.rowLen 0 ≤ c}
    (q : Fin r) :
    (betaSetFin (r := r) (c := c) μ hc).orderEmbOfFin (card_betaSetFin) q =
      ⟨μ.betaNumber r (r - 1 - (q : ℕ)),
        μ.betaNumber_lt_add hc (by have := q.isLt; omega)⟩ := by
  have h : (fun q : Fin r =>
      (⟨μ.betaNumber r (r - 1 - (q : ℕ)),
        μ.betaNumber_lt_add hc (by have := q.isLt; omega)⟩ : Fin (r + c))) =
      (betaSetFin μ hc).orderEmbOfFin (card_betaSetFin) := by
    refine orderEmbOfFin_unique _ (fun q => ?_) (fun q q' hlt => ?_)
    · rw [mem_betaSetFin]
      exact ⟨⟨r - 1 - (q : ℕ), by have := q.isLt; omega⟩, rfl⟩
    · have h1 : (⟨r - 1 - (q' : ℕ), by have := q'.isLt; omega⟩ : Fin r) <
          ⟨r - 1 - (q : ℕ), by have := q.isLt; omega⟩ := by
        simp only [Fin.lt_def]
        omega
      exact μ.strictAnti_betaNumber r h1
  rw [← h]

private lemma initialSet_orderEmb_fun {r c : ℕ} :
    ⇑((initialSet r c).orderEmbOfFin card_initialSet) = Fin.castAdd c :=
  funext initialSet_orderEmb_apply

private lemma betaSetFin_orderEmb_fun {r c : ℕ} {μ : YoungDiagram} {hc : μ.rowLen 0 ≤ c} :
    ⇑((betaSetFin (r := r) (c := c) μ hc).orderEmbOfFin card_betaSetFin) =
      fun q : Fin r =>
        (⟨μ.betaNumber r (r - 1 - (q : ℕ)),
          μ.betaNumber_lt_add hc (by have := q.isLt; omega)⟩ : Fin (r + c)) :=
  funext (betaSetFin_orderEmb_apply (hc := hc))

/-- `orderEmbOfFin` for the complementary beta-set, stated with an arbitrary cardinality proof. -/
private lemma orderEmbOfFin_complBetaFun {r c : ℕ} {μ : YoungDiagram} {hr : μ.colLen 0 ≤ r}
    {k : ℕ} {h : #(complBetaSetFin (r := r) (c := c) μ hr) = k} (hk : k = c) :
    ⇑((complBetaSetFin μ hr).orderEmbOfFin h) = (complBetaFun μ hr) ∘ ⇑(finCongr hk) := by
  refine (orderEmbOfFin_unique h (fun x => ?_) ?_).symm
  · rw [Function.comp_apply, mem_complBetaSetFin]
    exact ⟨_, rfl⟩
  · exact (complBetaFun_strictMono μ hr).comp (Fin.cast_strictMono hk)

/-- `orderEmbOfFin` for the terminal segment, stated with an arbitrary cardinality proof. -/
private lemma orderEmbOfFin_terminalFun {r c : ℕ} {k : ℕ} {h : #(terminalSet r c) = k}
    (hk : k = c) :
    ⇑((terminalSet r c).orderEmbOfFin h) = (Fin.natAdd r) ∘ ⇑(finCongr hk) := by
  refine (orderEmbOfFin_unique h (fun x => ?_) ?_).symm
  · rw [Function.comp_apply, mem_terminalSet]
    exact Nat.le_add_right r _
  · exact (Fin.strictMono_natAdd r).comp (Fin.cast_strictMono hk)

end FinSets

/-! ### The sign of an integer in the polynomial ring -/

section Sign

variable {N : ℕ}

/-- The sign `(-1) ^ n` of a natural number, as an element of the polynomial ring. -/
private lemma negOnePowCast_natCast (n : ℕ) :
    negOnePowCast (MvPolynomial (Fin N) R) (n : ℤ) = (-1) ^ n := by
  rw [negOnePowCast_eq_intCast, Int.cast_negOnePow_natCast]

/-- The `.toNat` in the definition of `esymmToeplitz` only changes the sign, and the sign can be
read off from the parity of the integer index. -/
private lemma neg_one_pow_toNat_mul_esymmInt (m : ℤ) :
    (-1 : MvPolynomial (Fin N) R) ^ m.toNat * esymmInt (Fin N) R m =
      negOnePowCast (MvPolynomial (Fin N) R) m * esymmInt (Fin N) R m := by
  rcases le_or_gt 0 m with hm | hm
  · have hcast : ((m.toNat : ℕ) : ℤ) = ((m.natAbs : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hm, Int.natAbs_of_nonneg hm]
    have h : m.toNat = m.natAbs := Nat.cast_injective hcast
    rw [h, negOnePowCast_eq_intCast, Int.coe_negOnePow]
  · rw [esymmInt_of_neg hm, mul_zero, mul_zero]

end Sign

/-! ### The adjugate of the Toeplitz matrix of `h` -/

section MatrixLayer

open scoped Matrix

variable {N : ℕ}

/-- The adjugate of the Toeplitz matrix of complete homogeneous polynomials is the signed
Toeplitz matrix of elementary symmetric polynomials. -/
theorem adjugate_hsymmToeplitz (n : ℕ) :
    Matrix.adjugate (hsymmToeplitz (Fin N) R n) = esymmToeplitz (Fin N) R n := by
  have h1 : Matrix.adjugate (hsymmToeplitz (Fin N) R n) * hsymmToeplitz (Fin N) R n = 1 := by
    rw [Matrix.adjugate_mul, det_hsymmToeplitz, one_smul]
  calc Matrix.adjugate (hsymmToeplitz (Fin N) R n)
      = Matrix.adjugate (hsymmToeplitz (Fin N) R n) * 1 := (mul_one _).symm
    _ = Matrix.adjugate (hsymmToeplitz (Fin N) R n) *
          (hsymmToeplitz (Fin N) R n * esymmToeplitz (Fin N) R n) := by
        rw [hsymmToeplitz_mul_esymmToeplitz]
    _ = (Matrix.adjugate (hsymmToeplitz (Fin N) R n) * hsymmToeplitz (Fin N) R n) *
          esymmToeplitz (Fin N) R n := by rw [Matrix.mul_assoc]
    _ = esymmToeplitz (Fin N) R n := by rw [h1, one_mul]

/-- The entry of the complementary minor of the adjugate, written in terms of the conjugate row
lengths. -/
private lemma esymmToeplitz_apply_complBeta {μ : YoungDiagram} {r c : ℕ}
    (hr : μ.colLen 0 ≤ r) (p q : Fin c) :
    (esymmToeplitz (Fin N) R (r + c)) (complBetaFun μ hr p) (Fin.natAdd r q) =
      negOnePowCast (MvPolynomial (Fin N) R) ((μ.transpose.rowLen p : ℤ) - (p : ℕ))
        * esymmInt (Fin N) R ((μ.transpose.rowLen p : ℤ) - (p : ℕ) + (q : ℕ))
        * negOnePowCast (MvPolynomial (Fin N) R) ((q : ℕ) : ℤ) := by
  rw [esymmToeplitz_apply]
  have hcq : ((Fin.natAdd r q : Fin (r + c)) : ℤ) = (r : ℤ) + (q : ℤ) := by
    simp
  have hle : μ.transpose.rowLen p ≤ r + p := by
    rw [μ.rowLen_transpose]
    exact (μ.colLen_anti 0 (p : ℕ) (Nat.zero_le p)).trans
      (hr.trans (Nat.le_add_right r (p : ℕ)))
  have hcp : ((complBetaFun μ hr p : Fin (r + c)) : ℤ)
      = (r : ℤ) + (p : ℤ) - (μ.transpose.rowLen p : ℤ) := by
    simp only [complBetaFun_val, YoungDiagram.complBetaNumber_def]
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcq, hcp]
  have hm : ((r : ℤ) + (q : ℤ)) - ((r : ℤ) + (p : ℤ) - (μ.transpose.rowLen p : ℤ))
      = (μ.transpose.rowLen p : ℤ) - (p : ℤ) + (q : ℤ) := by ring
  rw [hm, neg_one_pow_toNat_mul_esymmInt]
  rw [show (μ.transpose.rowLen p : ℤ) - (p : ℤ) + (q : ℤ)
      = ((μ.transpose.rowLen p : ℤ) - (p : ℤ)) + (q : ℤ) by ring, negOnePowCast_add]
  ring

private lemma esymmToeplitz_submatrix_complBeta {μ : YoungDiagram} {r c : ℕ}
    (hr : μ.colLen 0 ≤ r) :
    (esymmToeplitz (Fin N) R (r + c)).submatrix (complBetaFun μ hr) (Fin.natAdd r) =
      Matrix.diagonal (fun p : Fin c => negOnePowCast (MvPolynomial (Fin N) R)
            ((μ.transpose.rowLen p : ℤ) - (p : ℕ)))
        * (Matrix.of fun p q : Fin c => esymmInt (Fin N) R
            ((μ.transpose.rowLen p : ℤ) - (p : ℕ) + (q : ℕ)))
        * Matrix.diagonal (fun q : Fin c =>
            negOnePowCast (MvPolynomial (Fin N) R) ((q : ℕ) : ℤ)) := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc, Matrix.submatrix_apply,
    esymmToeplitz_apply_complBeta hr, Matrix.of_apply, mul_assoc]

/-- The minor of the Toeplitz matrix of `h` on the initial segment and the beta-set is the
Jacobi--Trudi determinant. -/
private lemma hsymmToeplitz_minor {μ : YoungDiagram} {r c : ℕ} (hr : μ.colLen 0 ≤ r)
    (hc : μ.rowLen 0 ≤ c) :
    ((hsymmToeplitz (Fin N) R (r + c)).submatrix (Fin.castAdd c)
        (fun q : Fin r => ⟨μ.betaNumber r (r - 1 - (q : ℕ)),
          μ.betaNumber_lt_add hc (by have := q.isLt; omega)⟩)).det
      = diagramSchurPoly N R μ := by
  rw [diagramSchurPoly_eq_det_hsymmInt N μ hr]
  have hL' : (hsymmToeplitz (Fin N) R (r + c)).submatrix (Fin.castAdd c)
        (fun q : Fin r => ⟨μ.betaNumber r (r - 1 - (q : ℕ)),
          μ.betaNumber_lt_add hc (by have := q.isLt; omega)⟩) =
      Matrix.of (fun i j : Fin r =>
        hsymmInt (Fin N) R ((μ.betaNumber r (r - 1 - (j : ℕ)) : ℤ) - (i : ℕ))) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hsymmToeplitz_apply, Fin.val_castAdd]
  have hrev : Matrix.of (fun i j : Fin r =>
      hsymmInt (Fin N) R ((μ.betaNumber r (r - 1 - (j : ℕ)) : ℤ) - (i : ℕ))) =
      (Matrix.of fun i j : Fin r =>
        hsymmInt (Fin N) R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ)))ᵀ.submatrix
        (Fin.revPerm) (Fin.revPerm) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.revPerm_apply]
    have hidx : ((μ.betaNumber r (r - 1 - (j : ℕ)) : ℕ) : ℤ) - (i : ℤ) =
        ((μ.rowLen ((j.rev : Fin r) : ℕ) : ℕ) : ℤ) - (((j.rev : Fin r) : ℕ) : ℤ) +
          (((i.rev : Fin r) : ℕ) : ℤ) := by
      have hjr : ((j.rev : Fin r) : ℕ) = r - 1 - (j : ℕ) := by rw [Fin.val_rev]; omega
      have hir : ((i.rev : Fin r) : ℕ) = r - 1 - (i : ℕ) := by rw [Fin.val_rev]; omega
      have hcast : ((μ.betaNumber r (r - 1 - (j : ℕ)) : ℕ) : ℤ) =
          (μ.rowLen (r - 1 - (j : ℕ)) : ℤ) + (j : ℤ) := by
        have h1 : r - 1 - (r - 1 - (j : ℕ)) = (j : ℕ) := by omega
        simp only [YoungDiagram.betaNumber_def, Nat.cast_add, h1]
      have hrow : ((μ.rowLen ((j.rev : Fin r) : ℕ) : ℕ) : ℤ) =
          (μ.rowLen (r - 1 - (j : ℕ)) : ℤ) := by rw [hjr]
      have hcj : (((j.rev : Fin r) : ℕ) : ℤ) = (r : ℤ) - 1 - (j : ℤ) := by
        rw [hjr, Nat.cast_sub (by have := j.isLt; omega),
          Nat.cast_sub (by have := j.isLt; omega)]
        push_cast
        ring
      have hci : (((i.rev : Fin r) : ℕ) : ℤ) = (r : ℤ) - 1 - (i : ℤ) := by
        rw [hir, Nat.cast_sub (by have := i.isLt; omega),
          Nat.cast_sub (by have := i.isLt; omega)]
        push_cast
        ring
      rw [hcast, hrow, hcj, hci]
      ring
    rw [hidx]
  rw [hL', hrev, Matrix.det_submatrix_equiv_self (Fin.revPerm (n := r)), Matrix.det_transpose]

/-- The dual Jacobi--Trudi determinant does not depend on the ambient size. -/
private lemma diagramSchurPoly_eq_det_esymmInt_aux {μ : YoungDiagram} {r c : ℕ}
    (hr : μ.colLen 0 ≤ r) (hc : μ.rowLen 0 ≤ c) :
    diagramSchurPoly N R μ =
      (Matrix.of fun i j : Fin c =>
        esymmInt (Fin N) R ((μ.transpose.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  set M : Matrix (Fin c) (Fin c) (MvPolynomial (Fin N) R) :=
    Matrix.of fun i j : Fin c =>
      esymmInt (Fin N) R ((μ.transpose.rowLen i : ℤ) - (i : ℕ) + (j : ℕ)) with hM
  set X : ℤ := ∑ p : Fin c, ((μ.transpose.rowLen p : ℤ) - (p : ℕ)) with hX
  set Y : ℤ := ∑ q : Fin c, ((q : ℕ) : ℤ) with hY
  set E : ℕ := ∑ i ∈ initialSet (r := r) (c := c), (i : ℕ) +
    ∑ j ∈ betaSetFin (r := r) (c := c) μ hc, (j : ℕ) with hE
  set eps : MvPolynomial (Fin N) R := negOnePowCast (MvPolynomial (Fin N) R) (E : ℤ) with heps
  set P : MvPolynomial (Fin N) R :=
    ∏ p : Fin c, negOnePowCast (MvPolynomial (Fin N) R) ((μ.transpose.rowLen p : ℤ) - (p : ℕ))
    with hP
  set Q : MvPolynomial (Fin N) R :=
    ∏ q : Fin c, negOnePowCast (MvPolynomial (Fin N) R) ((q : ℕ) : ℤ) with hQ
  -- Jacobi's complementary minor identity, with the initial segment as row set and the beta-set
  -- of `μ` as column set.
  have hjac := Matrix.det_mul_det_submatrix_adjugate (A := hsymmToeplitz (Fin N) R (r + c))
    (I := initialSet (r := r) (c := c)) (J := betaSetFin (r := r) (c := c) μ hc) (k := r)
    card_initialSet card_betaSetFin
  simp only [Nat.add_sub_cancel_left] at hjac
  rw [det_hsymmToeplitz, one_mul, one_pow, adjugate_hsymmToeplitz] at hjac
  simp only [initialSet_compl, compl_betaSetFin hc hr] at hjac
  simp only [initialSet_orderEmb_fun, betaSetFin_orderEmb_fun (hc := hc)] at hjac
  -- The complementary minor is indexed by `Fin (r + c - r)`; reindex it by `Fin c`.
  have hcast_eq : r + c - r = c := Nat.add_sub_cancel_left r c
  simp only [orderEmbOfFin_complBetaFun (hr := hr) hcast_eq,
    orderEmbOfFin_terminalFun (r := r) (c := c) hcast_eq] at hjac
  have hLdet : ((esymmToeplitz (Fin N) R (r + c)).submatrix (complBetaFun μ hr)
        (Fin.natAdd r)).det = P * M.det * Q := by
    rw [esymmToeplitz_submatrix_complBeta hr, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, Matrix.det_diagonal, ← hM, ← hP, ← hQ]
  have hsum_mu : (∑ p : Fin c, (μ.transpose.rowLen p : ℤ)) = (μ.card : ℤ) := by
    have hc' : μ.transpose.colLen 0 ≤ c := by simpa using hc
    rw [← Nat.cast_sum, Fin.sum_univ_eq_sum_range,
      ← YoungDiagram.card_eq_sum_range_rowLen μ.transpose hc', YoungDiagram.card_transpose]
  have hXY : X + Y = (μ.card : ℤ) := by
    rw [hX, hY, ← Finset.sum_add_distrib]
    have hterm : ∀ p : Fin c,
        ((μ.transpose.rowLen p : ℤ) - (p : ℕ)) + ((p : ℕ) : ℤ) = (μ.transpose.rowLen p : ℤ) := by
      intro p
      ring
    simp only [hterm]
    exact hsum_mu
  have hsum_I : ((∑ i ∈ initialSet (r := r) (c := c), (i : ℕ)) : ℤ) = ∑ i : Fin r, (i : ℤ) := by
    rw [initialSet, Finset.sum_image (Fin.castAdd_injective r c).injOn]
    simp
  have hsum_J : ((∑ j ∈ betaSetFin (r := r) (c := c) μ hc, (j : ℕ)) : ℤ) =
      ∑ i : Fin r, (μ.betaNumber r i : ℤ) := by
    rw [betaSetFin, Finset.sum_image (betaFun_injective μ hc).injOn]
    simp
  have hbeta : (∑ i : Fin r, (μ.betaNumber r i : ℤ)) =
      (μ.card : ℤ) + ∑ i : Fin r, (((r - 1 - (i : ℕ) : ℕ)) : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) (μ.sum_betaNumber (r := r) hr)
    simp only [Nat.cast_add, Nat.cast_sum] at h
    simpa [YoungDiagram.betaNumber_def] using h
  have hstair : (∑ i : Fin r, (i : ℤ)) +
      (∑ i : Fin r, (((r - 1 - (i : ℕ) : ℕ)) : ℤ)) = ((r * (r - 1) : ℕ) : ℤ) := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ i : Fin r,
        ((i : ℤ) + (((r - 1 - (i : ℕ) : ℕ)) : ℤ)) = ((r - 1 : ℕ) : ℤ) := by
      intro i
      have hi : (i : ℕ) ≤ r - 1 := by have := i.isLt; omega
      rw [Nat.cast_sub hi]
      ring
    simp only [hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Nat.cast_mul]
  have hE2 : (E : ℤ) = (μ.card : ℤ) + ((r * (r - 1) : ℕ) : ℤ) := by
    rw [hE, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, hsum_I, hsum_J, hbeta]
    linarith [hstair]
  -- The product of the two diagonal sign matrices with Jacobi's sign `(-1) ^ E` is `1`: the
  -- exponent `∑ I + ∑ J` is `2 * μ.card + r * (r - 1)`, which is even.
  have hsign : P * Q * eps = 1 := by
    rw [hP, hQ, ← negOnePowCast_sum, ← negOnePowCast_sum, heps]
    have hXYE : X + Y + (E : ℤ) = 2 * (μ.card : ℤ) + ((r * (r - 1) : ℕ) : ℤ) := by
      rw [hXY, hE2]
      ring
    rw [← negOnePowCast_add, ← negOnePowCast_add, hXYE, negOnePowCast_add,
      negOnePowCast_two_mul, one_mul, negOnePowCast_natCast,
      (Nat.even_mul_pred_self r).neg_one_pow]
  have hmain : P * M.det * Q = eps * diagramSchurPoly N R μ := by
    rw [← hLdet, ← Matrix.det_submatrix_equiv_self (finCongr hcast_eq),
      Matrix.submatrix_submatrix, hjac, hsymmToeplitz_minor hr hc, mul_one,
      ← negOnePowCast_natCast]
  have hsign' : P * (Q * eps) = 1 := by
    rw [← mul_assoc]
    exact hsign
  have heps2 : eps * eps = 1 := by
    simp [heps]
  -- Cancel the sign matrices, which multiply to `1`.
  have hMd : M.det = diagramSchurPoly N R μ := by
    calc M.det = 1 * M.det := (one_mul _).symm
      _ = (P * (Q * eps)) * M.det := by rw [hsign']
      _ = eps * (P * M.det * Q) := by ring
      _ = eps * (eps * diagramSchurPoly N R μ) := by rw [hmain]
      _ = diagramSchurPoly N R μ := by
          rw [← mul_assoc, heps2, one_mul]
  exact hMd.symm

/-- **The dual Jacobi--Trudi identity.**  The Schur polynomial of a Young diagram `μ` in the
alphabet `Fin N` is the determinant `det (e_{μᵀᵢ - i + j})_{0 ≤ i, j < c}` of elementary
symmetric polynomials, for every `c` at least the number of columns of `μ`.  The index
`μᵀᵢ - i + j` is an integer, and `e_m = 0` for `m < 0` (`TauCeti.esymmInt`).

There is no condition relating `N` to `μ`: when `μ` has more than `N` rows, both sides
vanish. -/
theorem diagramSchurPoly_eq_det_esymmInt (N : ℕ) (μ : YoungDiagram) {c : ℕ}
    (hc : μ.rowLen 0 ≤ c) :
    diagramSchurPoly N R μ =
      (Matrix.of fun i j : Fin c =>
        esymmInt (Fin N) R ((μ.transpose.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det :=
  diagramSchurPoly_eq_det_esymmInt_aux (r := μ.colLen 0) le_rfl hc

/-- **The dual Jacobi--Trudi identity for partitions.**  In a finite alphabet `σ`, the Schur
polynomial of a partition `μ` is `det (e_{μᵀᵢ - i + j})_{0 ≤ i, j < c}` for every `c` at least
the number of columns of `μ`, where `μᵀ` is the conjugate partition and `e_m = 0` for `m < 0`. -/
theorem schurPoly_eq_det_esymmInt {σ : Type*} [Fintype σ] {n : ℕ}
    (μ : n.Partition) {c : ℕ} (hc : (YoungDiagram.ofPartition μ).rowLen 0 ≤ c) :
    schurPoly σ R μ =
      (Matrix.of fun i j : Fin c =>
        esymmInt σ R (((YoungDiagram.ofPartition μ).transpose.rowLen i : ℤ) - (i : ℕ) +
          (j : ℕ))).det := by
  rw [schurPoly_eq_rename, diagramSchurPoly_eq_det_esymmInt _ _ hc, AlgHom.map_det]
  congr 1
  ext i j : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact rename_esymmInt _ _

end MatrixLayer

end TauCeti
