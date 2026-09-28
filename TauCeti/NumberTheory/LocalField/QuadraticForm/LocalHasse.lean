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
import TauCeti.NumberTheory.LocalField.SquareClasses

/-!
# The local Hasse invariant in odd residue characteristic

For a regular diagonal form `⟨a₁, …, aₙ⟩` over a nonarchimedean local field with odd
residue characteristic, its local Hasse invariant is the sign
`∏_{i<j} (aᵢ, aⱼ)ₖ`. Witt's chain theorem makes this independent of the diagonalization:
the Hilbert symbol is symmetric, multiplicative, and constant on isometric binary forms.

The orthogonal-sum formula has a cross term given by the Hilbert symbol of the two
discriminants. This is the convention of Serre's `ε` and Lam's `s`; O'Meara's product
over `i ≤ j` uses a different convention.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3.
-/

public section

open Finset QuadraticMap ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [Invertible (2 : K)] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace RegularFormClass

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

private theorem hilbertSymbol_mul_mul (h2 : IsUnit (2 : 𝒪[K])) (a b c : Kˣ) :
    hilbertSymbol (a * b) (a * c) =
      hilbertSymbol b c * hilbertSymbol a (-1) * hilbertSymbol a b * hilbertSymbol a c := by
  rw [hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2,
    hilbertSymbol_mul_right h2, hilbertSymbol_self, hilbertSymbol_comm b a]
  ac_rfl

private theorem localHasseProd_scale (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ)
    {n : ℕ} (w : Fin n → Kˣ) :
    (∏ i, ∏ j ∈ Ioi i, hilbertSymbol (a * w i) (a * w j)) =
      (∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j)) *
        hilbertSymbol a (-1) ^ n.choose 2 *
        hilbertSymbol a (∏ i, w i) ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let w₀ := Fin.init w
    let b := w (Fin.last n)
    have hw : w = Fin.snoc w₀ b := (Fin.snoc_init_self w).symm
    rw [hw]
    have hs (i : Fin (n + 1)) :
        a * Fin.snoc (α := fun _ => Kˣ) w₀ b i =
          Fin.snoc (α := fun _ => Kˣ) (fun j => a * w₀ j) (a * b) i := by
      rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl <;> simp
    simp_rw [hs]
    let h₁ : Kˣ →* ℤˣ := {
      toFun := hilbertSymbol a
      map_one' := hilbertSymbol_one_right a
      map_mul' := hilbertSymbol_mul_right h2 a }
    have hprod : (∏ i, hilbertSymbol a (w₀ i)) = hilbertSymbol a (∏ i, w₀ i) :=
      (map_prod h₁ w₀ Finset.univ).symm
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    rw [prod_prod_Ioi_snoc hilbertSymbol (fun j => a * w₀ j) (a * b),
      prod_prod_Ioi_snoc hilbertSymbol w₀ b, ih w₀, Fin.prod_snoc, Nat.add_sub_cancel]
    simp_rw [hilbertSymbol_mul_mul h2]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hprod, hilbertSymbol_mul_right h2, mul_pow, hchoose, pow_add]
    cases n with
    | zero => simp
    | succ n =>
      rw [Nat.add_sub_cancel, pow_succ (hilbertSymbol a (∏ i, w₀ i)) n]
      ac_nf
      rw [mul_left_comm (hilbertSymbol a (-1) ^ (n + 1))]

/-- The product of pairwise Hilbert symbols on a regular-form class over a local field
of odd residue characteristic. It is independent of the diagonal presentation. -/
noncomputable def localHasseOfOdd (h2 : IsUnit (2 : 𝒪[K])) :
    RegularFormClass K → ℤˣ := by
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
  exact liftDiagonal_mk _ localHasseProd_eq_of_permutationStep
    (localHasseProd_eq_of_binaryStep h2)
    (fun a b _ => localHasseProd_rankOne a b) p

/-- The local Hasse invariant of a regular form is read from any diagonalization. -/
theorem localHasseOfOdd_formClass (h2 : IsUnit (2 : 𝒪[K]))
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) {n : ℕ}
    (w : Fin n → Kˣ) (h : Q.Equivalent (weightedSumSquares K fun i => (w i : K))) :
    localHasseOfOdd h2 (formClass Q hQ) =
      ∏ i, ∏ j ∈ Ioi i, hilbertSymbol (w i) (w j) := by
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
    localHasseOfOdd h2 (hyperbolicClass K) = 1 := by
  rw [hyperbolicClass_def, localHasseOfOdd_mk_binary, hilbertSymbol_one_left]

/-- The Hasse invariant of an orthogonal sum of diagonal presentations. The cross term
is the Hilbert symbol of their coefficient products. -/
theorem localHasseOfOdd_add_mk (h2 : IsUnit (2 : 𝒪[K]))
    (p q : RegularFormPresentation K) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p +
      Quotient.mk (regularFormSetoid K) q) =
      localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) *
        localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) q) *
        hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) := by
  let h₁ (a : Kˣ) : Kˣ →* ℤˣ := {
    toFun := hilbertSymbol a
    map_one' := hilbertSymbol_one_right a
    map_mul' := hilbertSymbol_mul_right h2 a }
  let h₂ (b : Kˣ) : Kˣ →* ℤˣ := {
    toFun := fun a => hilbertSymbol a b
    map_one' := hilbertSymbol_one_left b
    map_mul' := fun a c => hilbertSymbol_mul_left h2 b a c }
  have happend : p.append q = ⟨p.1 + q.1, Fin.append p.2 q.2⟩ := by
    let hfst := RegularFormPresentation.fst_append p q
    have hw : (p.append q).2 ∘ Fin.cast hfst.symm = Fin.append p.2 q.2 := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro k
        simpa only [Function.comp_apply, Fin.append_left] using
          RegularFormPresentation.append_apply_castAdd p q k
      · intro k
        simpa only [Function.comp_apply, Fin.append_right] using
          RegularFormPresentation.append_apply_natAdd p q k
    apply RegularFormPresentation.ext hfst
    intro i
    let j := Fin.cast hfst i
    have hi : i = Fin.cast hfst.symm j := Fin.ext rfl
    rw [hi]
    exact congrFun hw j
  rw [mk_add_mk, happend, localHasseOfOdd_mk, localHasseOfOdd_mk, localHasseOfOdd_mk,
    prod_prod_Ioi_append]
  congr 1
  calc
    (∏ i, ∏ j, hilbertSymbol (p.2 i) (q.2 j)) =
        ∏ i, hilbertSymbol (p.2 i) (∏ j, q.2 j) := by
          apply Finset.prod_congr rfl
          intro i _
          exact (map_prod (h₁ (p.2 i)) q.2 Finset.univ).symm
    _ = hilbertSymbol (∏ i, p.2 i) (∏ j, q.2 j) :=
      (map_prod (h₂ (∏ j, q.2 j)) p.2 Finset.univ).symm

/-- Scaling the coefficients of a diagonal presentation changes the local Hasse invariant
by a correction for each coefficient pair and a correction involving the discriminant. -/
theorem localHasseOfOdd_mk_scale (h2 : IsUnit (2 : 𝒪[K])) (a : Kˣ)
    (p : RegularFormPresentation K) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K)
      ⟨p.1, fun i => a * p.2 i⟩) =
      localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 *
        hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  rw [localHasseOfOdd_mk, localHasseOfOdd_mk]
  exact localHasseProd_scale h2 a p.2

/-- Scaling by a rank-one class is coefficientwise scaling of a diagonal presentation. -/
theorem localHasseOfOdd_mk_rankOne_mul_mk (h2 : IsUnit (2 : 𝒪[K]))
    (a : Kˣ) (p : RegularFormPresentation K) :
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ *
      Quotient.mk (regularFormSetoid K) p) =
      localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) p) *
        hilbertSymbol a (-1) ^ p.1.choose 2 *
        hilbertSymbol a (∏ i, p.2 i) ^ (p.1 - 1) := by
  let r : RegularFormPresentation K := ⟨1, fun _ => a⟩
  have hrank : (r.tmul p).1 = p.1 := by simp [r]
  have hscale : r.tmul p = ⟨p.1, fun i => a * p.2 i⟩ := by
    refine RegularFormPresentation.ext (q := ⟨p.1, fun i => a * p.2 i⟩) hrank ?_
    intro i
    let j := Fin.cast hrank i
    have happly := RegularFormPresentation.tmul_apply r p (0 : Fin r.1) j
    have hi : Fin.cast (RegularFormPresentation.fst_tmul r p).symm
        (finProdFinEquiv (0, j)) = i := by
      apply Fin.ext
      simp [r, j, finProdFinEquiv]
    rw [hi] at happly
    simpa [r, j] using happly
  rw [mk_mul_mk, hscale, localHasseOfOdd_mk_scale]

/-- Orthogonal sum multiplies the two local Hasse invariants and adds the Hilbert
symbol of their discriminants as a cross term. -/
theorem localHasseOfOdd_add (h2 : IsUnit (2 : 𝒪[K])) (x y : RegularFormClass K) :
    localHasseOfOdd h2 (x + y) = localHasseOfOdd h2 x * localHasseOfOdd h2 y *
      hilbertSymbolOnSquareClasses (discr x) (discr y) := by
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
    localHasseOfOdd h2 (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
      localHasseOfOdd h2 x * hilbertSymbol a (-1) ^ (rank x).choose 2 *
        hilbertSymbolOnSquareClasses (squareClass a) (discr x) ^ (rank x - 1) := by
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
