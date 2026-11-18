/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Combinatorics.Brauer.Generator
public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Crossing
public import TauCeti.LinearAlgebra.Matrix.Kronecker.Power
public import TauCeti.Logic.Equiv.Fin.Basic

-- Non-public: `Equiv.Perm.mclosure_swap_castSucc_succ` generates permutations from adjacent
-- transpositions, `BrauerDiagram.capCup_induction_on` reduces the loop rule to permutations and
-- cap-cup diagrams, `Associativity` and `WeightedAssociativity` reassociate diagram stacks and
-- their loop counts, and `TauCeti.LinearAlgebra.SymplecticGroup` supplies the entrywise identities
-- for `Matrix.J`.
import Mathlib.GroupTheory.Perm.Sign
import TauCeti.Combinatorics.Brauer.Associativity
import TauCeti.Combinatorics.Brauer.Generation
import TauCeti.Combinatorics.Brauer.WeightedAssociativity
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The symplectic Brauer action matrices

A Brauer diagram `D` on `k` strands acts on the `k`-th tensor power of the standard symplectic
module `V = (ι ⊕ ι) → R` equipped with the alternating form `Matrix.J ι R`. This file builds the
matrix of that operator in the monomial basis directly on the diagram basis, without using a
generator-and-relations presentation of the Brauer algebra.

Read the `2 * k` boundary points of `D` in counterclockwise order via `TauCeti.finSumFinRevEquiv`:
`0, …, k - 1` along the bottom from left to right, then `k, …, 2k - 1` along the top from right to
left. In this linear order `D` becomes a perfect matching `M` of `Fin (k + k)` with a Pfaffian
crossing sign `M.crossingSign` (`±1`) and a skew-symmetric pair-weight product `M.weight` built
from `Matrix.J`, defining `TauCeti.BrauerDiagram.symplecticBoundaryMatrix`. Multiplying on the
right by the Kronecker power `(Matrix.J ι R).kroneckerPower (Fin k)` dualizes the input slots and
yields `TauCeti.BrauerDiagram.symplecticActionMatrix`.

Using the local sign calculus of `TauCeti/Combinatorics/Enumerative/PerfectMatching/Crossing.lean`,
left multiplication on the boundary matrix by a signed adjacent transposition composes on the top
with that transposition diagram, and left multiplication by the cap-cup matrix on strands `0` and
`1` composes on the top with `capCup 0 1` while extracting the loop factor `-(2 * |ι|)` when
`{0, 1}` is already a cup of `D` and reconnecting the top pair otherwise. Conjugating to arbitrary
distinct pairs and applying `TauCeti.BrauerDiagram.capCup_induction_on` yields the full loop rule
`M(D₁) * M(D₂) = (-(2 * |ι|)) ^ c • M(D₁ ∘ D₂)`
(`TauCeti.BrauerDiagram.symplecticActionMatrix_mul`).

In addition, every matrix `A` satisfying `A * J * Aᵀ = J` leaves the boundary matrix invariant
under congruence by its Kronecker power
(`TauCeti.BrauerDiagram.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose`). Taken at
`A = J`, together with order reversal of the counterclockwise boundary under `D.flip`, this shows
that transposing or conjugate-transposing the action matrix of `D` gives the action matrix of
`D.flip`.

## Main definitions

* `TauCeti.BrauerDiagram.symplecticBoundaryMatrix`: the Pfaffian-signed boundary matrix of a Brauer
  diagram with pair weights given by `Matrix.J`.
* `TauCeti.BrauerDiagram.symplecticActionMatrix`: the matrix of a Brauer diagram acting on the
  `k`-th tensor power of `(ι ⊕ ι) → R`.

## Main results

* `TauCeti.BrauerDiagram.symplecticActionMatrix_permToBrauer_one`: the identity diagram acts by the
  identity matrix.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_permToBrauer`: permutation diagrams act by signed
  permutation matrices.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_capCup`: cap-cup diagrams on distinct strands act
  by the single-arc matrices.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_mul`: **the loop rule for the matrices**,
  `M(D₁) * M(D₂) = (-(2 * |ι|)) ^ c • M(D₁ ∘ D₂)` with `c` the number of closed middle loops.
* `TauCeti.BrauerDiagram.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose`: congruence
  invariance of the boundary matrix under any matrix satisfying `A * J * Aᵀ = J`.
* `TauCeti.BrauerDiagram.transpose_symplecticActionMatrix` and
  `TauCeti.BrauerDiagram.conjTranspose_symplecticActionMatrix`: transposing or conjugate-transposing
  the action matrix of a diagram gives the action matrix of the reflected diagram.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped Matrix

namespace TauCeti.BrauerDiagram

universe u

variable (R : Type u) [CommRing R] (ι : Type*) [DecidableEq ι] {k : ℕ}

/-! ### The boundary matrix and the action matrix -/

/-- **The symplectic boundary matrix of a Brauer diagram.** Numbering the `2 * k` boundary points
counterclockwise by `TauCeti.finSumFinRevEquiv` (bottom left-to-right, then top right-to-left),
the `(v, u)` entry is the crossing sign of the resulting perfect matching times the product of
`Matrix.J ι R` evaluated on the labels `Sum.elim u v` at the two endpoints of each arc in
increasing counterclockwise order. -/
def symplecticBoundaryMatrix (D : BrauerDiagram k) :
    Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R :=
  Matrix.of fun v u =>
    (((PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).crossingSign : ℤ) : R) *
      (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).weight fun x y =>
        Matrix.J ι R
          (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm x))
          (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm y))

/-- Entrywise formula for `TauCeti.BrauerDiagram.symplecticBoundaryMatrix`. -/
@[simp]
theorem symplecticBoundaryMatrix_apply (D : BrauerDiagram k) (v u : Fin k → ι ⊕ ι) :
    D.symplecticBoundaryMatrix R ι v u =
      (((PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).crossingSign : ℤ) : R) *
        (PerfectMatching.congr (finSumFinRevEquiv k k (k + k) rfl) D).weight fun x y =>
          Matrix.J ι R
            (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm x))
            (Sum.elim u v ((finSumFinRevEquiv k k (k + k) rfl).symm y)) :=
  (rfl)

/-- **The symplectic action matrix of a Brauer diagram** acting on the `k`-th tensor power of
`(ι ⊕ ι) → R`, obtained from `TauCeti.BrauerDiagram.symplecticBoundaryMatrix` by dualizing the
input slots through the Kronecker power of `Matrix.J`. -/
def symplecticActionMatrix [Fintype ι] (D : BrauerDiagram k) :
    Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R :=
  D.symplecticBoundaryMatrix R ι * (Matrix.J ι R).kroneckerPower (Fin k)

/-- The action matrix is the boundary matrix multiplied on the right by the Kronecker power of
`Matrix.J`. -/
theorem symplecticActionMatrix_def [Fintype ι] (D : BrauerDiagram k) :
    D.symplecticActionMatrix R ι =
      D.symplecticBoundaryMatrix R ι * (Matrix.J ι R).kroneckerPower (Fin k) :=
  (rfl)

/-! ### The identity diagram -/

/-- The boundary matrix of the identity diagram pairs each input label with the matching output
label through `Matrix.J`. -/
private theorem symplecticBoundaryMatrix_permToBrauer_one_apply (v u : Fin k → ι ⊕ ι) :
    (permToBrauer 1).symplecticBoundaryMatrix R ι v u =
      ∏ i : Fin k, Matrix.J ι R (u i) (v i) := by
  let φ := finSumFinRevEquiv k k (k + k) rfl
  have hval_inl (i : Fin k) :
      (PerfectMatching.congr φ (permToBrauer 1)).val (φ (Sum.inl i)) = φ (Sum.inr i) := by
    simp [Equiv.Perm.one_def]
  have hval_inr (j : Fin k) :
      (PerfectMatching.congr φ (permToBrauer 1)).val (φ (Sum.inr j)) = φ (Sum.inl j) := by
    simp [Equiv.Perm.one_def]
  have hnc : (PerfectMatching.congr φ (permToBrauer 1)).val.IsNoncrossingMatching := by
    rw [Equiv.Perm.isNoncrossingMatching_iff]
    intro a b hab hba hma
    obtain ⟨x, rfl⟩ := φ.surjective a
    obtain ⟨y, rfl⟩ := φ.surjective b
    rcases x with i | i
    · rcases y with j | j
      · rw [hval_inl i, hval_inl j] at hma
        have hij : i < j := (finSumFinRevEquiv_inl_lt_inl_iff ..).mp hab
        have hji : j < i := (finSumFinRevEquiv_inr_lt_inr_iff ..).mp hma
        exact lt_asymm hij hji
      · rw [hval_inl i, hval_inr j] at hma
        exact not_finSumFinRevEquiv_inr_lt_inl k k (k + k) rfl j i hma
    · rw [hval_inr i] at hba
      exact not_lt_of_gt (lt_trans hab hba) (finSumFinRevEquiv_inl_lt_inr k k (k + k) rfl i i)
  rw [symplecticBoundaryMatrix_apply, PerfectMatching.crossingSign_of_isNoncrossingMatching hnc]
  simp only [Units.val_one, Int.cast_one, one_mul, PerfectMatching.weight_def]
  rw [← Fintype.prod_equiv φ _ _ fun _ => rfl, Fintype.prod_sum_type]
  have htop : ∏ j : Fin k,
      (if φ (Sum.inr j) < (PerfectMatching.congr φ (permToBrauer 1)).val (φ (Sum.inr j)) then
        Matrix.J ι R (Sum.elim u v (φ.symm (φ (Sum.inr j))))
          (Sum.elim u v (φ.symm ((PerfectMatching.congr φ (permToBrauer 1)).val (φ (Sum.inr j)))))
      else 1) = 1 :=
    Finset.prod_eq_one fun j _ => by
      rw [hval_inr j, ite_eq_right (not_finSumFinRevEquiv_inr_lt_inl k k (k + k) rfl j j)]
  rw [htop, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hval_inl i, ite_eq_left (finSumFinRevEquiv_inl_lt_inr k k (k + k) rfl i i),
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

/-- **The identity diagram has the identity matrix.** -/
@[simp]
theorem symplecticActionMatrix_permToBrauer_one [Fintype ι] :
    (permToBrauer 1).symplecticActionMatrix R ι =
      (1 : Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R) := by
  ext v u
  rw [symplecticActionMatrix_def, Matrix.mul_apply, Matrix.one_apply]
  simp only [symplecticBoundaryMatrix_permToBrauer_one_apply, Matrix.kroneckerPower_apply,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => Matrix.J ι R x (v i) * Matrix.J ι R x (u i))]
  simp only [Matrix.sum_J_mul_J_eq_ite, Fintype.prod_boole, ← funext_iff]

/-! ### Left multiplication by permutation diagrams -/

/-- The matrix of the sign-twisted permutation action of `σ : Equiv.Perm (Fin k)` in the monomial
basis. -/
private def signedPermMatrix (σ : Equiv.Perm (Fin k)) :
    Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R :=
  Matrix.of fun v u => if v = u ∘ σ.symm then ((Equiv.Perm.sign σ : ℤ) : R) else 0

private theorem signedPermMatrix_one :
    signedPermMatrix R ι (1 : Equiv.Perm (Fin k)) = 1 := by
  ext v u
  simp [signedPermMatrix, Matrix.one_apply, Equiv.Perm.one_def]

private theorem signedPermMatrix_mul [Fintype ι] (σ τ : Equiv.Perm (Fin k)) :
    signedPermMatrix R ι σ * signedPermMatrix R ι τ = signedPermMatrix R ι (σ * τ) := by
  ext v u
  rw [Matrix.mul_apply]
  simp only [signedPermMatrix, Matrix.of_apply, mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (u ∘ τ.symm)]
  have hcomp : (u ∘ τ.symm) ∘ σ.symm = u ∘ (σ * τ).symm := by
    funext i
    simp only [Function.comp_apply]
    rw [← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def, mul_inv_rev,
      Equiv.Perm.mul_apply]
  simp only [Finset.mem_univ, ite_true, hcomp, map_mul, Units.val_mul, Int.cast_mul]

private theorem signedPermMatrix_mul_apply [Fintype ι] (σ : Equiv.Perm (Fin k))
    (M : Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R) (v u : Fin k → ι ⊕ ι) :
    (signedPermMatrix R ι σ * M) v u = ((Equiv.Perm.sign σ : ℤ) : R) * M (v ∘ σ) u := by
  rw [Matrix.mul_apply]
  have heq (w : Fin k → ι ⊕ ι) : (v = w ∘ σ.symm) ↔ w = v ∘ σ := by
    constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  simp only [signedPermMatrix, Matrix.of_apply, heq, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Left multiplication of the boundary matrix by a signed adjacent transposition composes on the
top with that transposition diagram. -/
private theorem signedPermMatrix_swap_castSucc_mul_symplecticBoundaryMatrix [Fintype ι]
    {m : ℕ} (i : Fin m) (D : BrauerDiagram (m + 1)) :
    signedPermMatrix R ι (Equiv.swap i.castSucc i.succ) * D.symplecticBoundaryMatrix R ι =
      (composeDiagram (permToBrauer (Equiv.swap i.castSucc i.succ)) D).symplecticBoundaryMatrix
        R ι := by
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i.castSucc i.succ
  let φ := finSumFinRevEquiv (m + 1) (m + 1) ((m + 1) + (m + 1)) rfl
  set a : Fin ((m + 1) + (m + 1)) := φ (Sum.inr i.succ)
  set b : Fin ((m + 1) + (m + 1)) := φ (Sum.inr i.castSucc)
  set s : Equiv.Perm (Fin ((m + 1) + (m + 1))) := Equiv.swap a b
  have hab : a < b := (finSumFinRevEquiv_inr_lt_inr_iff ..).mpr Fin.castSucc_lt_succ
  have hadj : ∀ x : Fin ((m + 1) + (m + 1)), a < x → b ≤ x := by
    intro x hx
    have ha : (a : ℕ) = (m + 1) + (m - (i.val + 1)) := by simp [a, φ]
    have hb : (b : ℕ) = (m + 1) + (m - i.val) := by simp [b, φ]
    have hi : i.val < m := i.isLt
    change (b : ℕ) ≤ (x : ℕ)
    change (a : ℕ) < (x : ℕ) at hx
    omega
  have hφσ : ∀ x : Fin (m + 1) ⊕ Fin (m + 1),
      φ (Equiv.Perm.sumCongr 1 σ x) = s (φ x) := by
    intro x
    rcases x with j | j
    · simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.coe_one, id_eq, s]
      symm
      exact Equiv.swap_apply_of_ne_of_ne (fun h => by simpa using φ.injective h)
        (fun h => by simpa using φ.injective h)
    · simp only [Equiv.Perm.sumCongr_apply, Sum.map_inr]
      rcases eq_or_ne j i.castSucc with rfl | hj1
      · simp [σ, s, a, b]
      rcases eq_or_ne j i.succ with rfl | hj2
      · simp [σ, s, a, b]
      · rw [Equiv.swap_apply_of_ne_of_ne hj1 hj2]
        symm
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hj2 (Sum.inr.inj (φ.injective h)))
          (fun h => hj1 (Sum.inr.inj (φ.injective h)))
  have hcongr : PerfectMatching.congr φ (composeDiagram (permToBrauer σ) D) =
      PerfectMatching.congr s (PerfectMatching.congr φ D) := by
    refine PerfectMatching.ext fun z => ?_
    obtain ⟨y, rfl⟩ := φ.surjective z
    rw [composeDiagram_permToBrauer_left, relabel_def, PerfectMatching.congr_val_apply,
      PerfectMatching.congr_val_apply, PerfectMatching.congr_val_apply,
      PerfectMatching.congr_val_apply, Equiv.symm_apply_apply]
    have hsymm : (Equiv.Perm.sumCongr 1 σ).symm y = Equiv.Perm.sumCongr 1 σ y := by
      rw [← Equiv.Perm.inv_def, Equiv.Perm.sumCongr_inv, inv_one, Equiv.swap_inv]
    have hs_symm : s.symm (φ y) = φ (Equiv.Perm.sumCongr 1 σ y) := by
      rw [Equiv.symm_swap, hφσ]
    rw [hs_symm, Equiv.symm_apply_apply, hsymm, hφσ]
  have hsign : ((Equiv.Perm.sign σ : ℤ) : R) = -1 := by
    rw [Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
    simp
  ext v u
  rw [signedPermMatrix_mul_apply, hsign, neg_one_mul, symplecticBoundaryMatrix_apply,
    symplecticBoundaryMatrix_apply, hcongr]
  have hlabel (x : Fin ((m + 1) + (m + 1))) :
      Sum.elim u v (φ.symm (s x)) = Sum.elim u (v ∘ σ) (φ.symm x) := by
    obtain ⟨y, rfl⟩ := φ.surjective x
    rw [← hφσ y, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases y with j | j <;> simp
  set M := PerfectMatching.congr φ D
  set w : Fin ((m + 1) + (m + 1)) → Fin ((m + 1) + (m + 1)) → R :=
    fun x y => Matrix.J ι R (Sum.elim u v (φ.symm x)) (Sum.elim u v (φ.symm y))
  have hw_swap : (fun x y => Matrix.J ι R (Sum.elim u (v ∘ σ) (φ.symm x))
      (Sum.elim u (v ∘ σ) (φ.symm y))) = fun x y => w (s x) (s y) := by
    funext x y
    simp only [w, hlabel]
  rw [hw_swap]
  by_cases hM : M.val a = b
  · rw [PerfectMatching.congr_swap_of_apply_eq M hM,
      PerfectMatching.weight_swap_of_apply_eq M hM (w := w)
        (fun _ _ => Matrix.J_apply_swap ι R _ _)]
    ring
  · rw [PerfectMatching.crossingSign_congr_swap_of_ne M hab hadj hM,
      PerfectMatching.weight_congr_swap_of_ne M hab hadj hM w]
    simp [s]

/-- Left multiplication of the boundary matrix by any signed permutation matrix composes on the
top with that permutation diagram. -/
private theorem signedPermMatrix_mul_symplecticBoundaryMatrix [Fintype ι]
    (σ : Equiv.Perm (Fin k)) (D : BrauerDiagram k) :
    signedPermMatrix R ι σ * D.symplecticBoundaryMatrix R ι =
      (composeDiagram (permToBrauer σ) D).symplecticBoundaryMatrix R ι := by
  cases k with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst hσ
    rw [signedPermMatrix_one, Matrix.one_mul, composeDiagram_permToBrauer_one_left]
  | succ m =>
    have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin m =>
        Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hmem using Submonoid.closure_induction generalizing D with
    | mem τ hτ =>
      rcases hτ with ⟨i, rfl⟩
      exact signedPermMatrix_swap_castSucc_mul_symplecticBoundaryMatrix R ι i D
    | one =>
      rw [signedPermMatrix_one, Matrix.one_mul, composeDiagram_permToBrauer_one_left]
    | mul τ₁ τ₂ _ _ ih₁ ih₂ =>
      rw [← signedPermMatrix_mul, Matrix.mul_assoc, ih₂ D, ih₁,
        ← composeDiagram_assoc, composeDiagram_permToBrauer]

/-- Left multiplication of the action matrix by any signed permutation matrix composes on the top
with that permutation diagram. -/
private theorem signedPermMatrix_mul_symplecticActionMatrix [Fintype ι]
    (σ : Equiv.Perm (Fin k)) (D : BrauerDiagram k) :
    signedPermMatrix R ι σ * D.symplecticActionMatrix R ι =
      (composeDiagram (permToBrauer σ) D).symplecticActionMatrix R ι := by
  rw [symplecticActionMatrix_def, symplecticActionMatrix_def, ← Matrix.mul_assoc,
    signedPermMatrix_mul_symplecticBoundaryMatrix]

/-- **The action matrix of a permutation diagram** is the signed permutation matrix: entry `(v, u)`
is `sign σ` when `v = u ∘ σ.symm`, and `0` otherwise. -/
theorem symplecticActionMatrix_permToBrauer [Fintype ι] (σ : Equiv.Perm (Fin k))
    (v u : Fin k → ι ⊕ ι) :
    (permToBrauer σ).symplecticActionMatrix R ι v u =
      if v = u ∘ σ.symm then ((Equiv.Perm.sign σ : ℤ) : R) else 0 := by
  have h := signedPermMatrix_mul_symplecticActionMatrix R ι σ (permToBrauer 1)
  rw [symplecticActionMatrix_permToBrauer_one, Matrix.mul_one,
    composeDiagram_permToBrauer_one_right] at h
  exact congrFun (congrFun h.symm v) u

/-- Left multiplication by the action matrix of a permutation diagram composes on the top. -/
private theorem symplecticActionMatrix_permToBrauer_mul [Fintype ι]
    (σ : Equiv.Perm (Fin k)) (D : BrauerDiagram k) :
    (permToBrauer σ).symplecticActionMatrix R ι * D.symplecticActionMatrix R ι =
      (composeDiagram (permToBrauer σ) D).symplecticActionMatrix R ι := by
  have h : (permToBrauer σ).symplecticActionMatrix R ι = signedPermMatrix R ι σ := by
    ext v u
    exact symplecticActionMatrix_permToBrauer R ι σ v u
  rw [h, signedPermMatrix_mul_symplecticActionMatrix]

/-! ### Stacking a cap-cup diagram on top -/

section CapCupDiagram

variable {a b : Fin k}

/-- Off the two top points `{a, b}` and their partners in `D`, stacking `capCup a b` above `D`
preserves every arc of `D`. -/
private theorem composeDiagram_capCup_val_of_ne {D : BrauerDiagram k}
    {x : Fin k ⊕ Fin k} (hxa : x ≠ Sum.inr a) (hxb : x ≠ Sum.inr b)
    (hDxa : D.val x ≠ Sum.inr a) (hDxb : D.val x ≠ Sum.inr b) :
    (composeDiagram (capCup a b) D).val x = D.val x := by
  rcases x with i | j <;> rcases hy : D.val _ with i' | j'
  · exact composeDiagram_val_inl_eq_inl_of_cap_lower _ _ hy
  · rw [hy] at hDxa hDxb
    exact composeDiagram_val_inl_eq_inr_of_through _ _ hy
      (capCup_val_inl_of_ne (by simpa using hDxa) (by simpa using hDxb))
  · exact composeDiagram_val_inr_eq_inl_of_through _ _
      (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
  · rw [hy] at hDxa hDxb
    exact composeDiagram_val_inr_eq_inr_of_cup_lower _ _
      (capCup_val_inr_of_ne (by simpa using hxa) (by simpa using hxb)) hy
      (capCup_val_inl_of_ne (by simpa using hDxa) (by simpa using hDxb))

/-- If `D` already cups `{a, b}`, stacking `capCup a b` above `D` leaves `D` unchanged. -/
private theorem composeDiagram_capCup_of_apply_eq {D : BrauerDiagram k} (hab : a ≠ b)
    (hcup : D.val (Sum.inr a) = Sum.inr b) :
    composeDiagram (capCup a b) D = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hxa : x = Sum.inr a
  · subst hxa
    rw [hcup]
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab)
  by_cases hxb : x = Sum.inr b
  · subst hxb
    rw [D.apply_eq_of_apply_eq hcup]
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab)
  obtain ⟨hDxa, hDxb⟩ := (D.apply_ne_and_ne_iff hcup x).mpr ⟨hxa, hxb⟩
  exact composeDiagram_capCup_val_of_ne hxa hxb hDxa hDxb

/-- If `D` already cups `{a, b}`, stacking `capCup a b` above `D` closes up exactly one middle
loop. -/
private theorem middleLoopCount_capCup_of_apply_eq {D : BrauerDiagram k} (hab : a ≠ b)
    (hcup : D.val (Sum.inr a) = Sum.inr b) :
    middleLoopCount (capCup a b) D = 1 := by
  rw [middleLoopCount_eq_ncard_image]
  have hset : {m : Fin k | OnMiddleLoop (capCup a b) D m} = {a, b} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hm
      exact (isCap_capCup_inl_iff hab).mp ((isMiddleVertex_def ..).mp hm.isMiddleVertex).1
    · rintro (rfl | rfl)
      · exact onMiddleLoop_of_val_eq (capCup_val_inl_left hab) hcup
      · exact onMiddleLoop_of_val_eq (capCup_val_inl_right hab) (D.apply_eq_of_apply_eq hcup)
  have hq : Quot.mk (MiddleAdj (capCup a b) D) a = Quot.mk (MiddleAdj (capCup a b) D) b :=
    Quot.sound ((middleAdj_def ..).mpr (Or.inl (capCup_val_inl_left hab)))
  rw [hset, Set.image_pair, hq, Set.pair_eq_singleton, Set.ncard_singleton]

/-- If `D` does not cup `{a, b}`, stacking `capCup a b` above `D` reconnects the two top points
`Sum.inr a` and `Sum.inr b`. -/
private theorem composeDiagram_capCup_of_apply_ne {D : BrauerDiagram k} (hab : a ≠ b)
    (hcup : D.val (Sum.inr a) ≠ Sum.inr b) :
    composeDiagram (capCup a b) D = D.reconnect (Sum.inr a) (Sum.inr b) := by
  have hba' : (Sum.inr b : Fin k ⊕ Fin k) ≠ Sum.inr a := by simpa using hab.symm
  have hba_ne : D.val (Sum.inr b) ≠ Sum.inr a := fun h => hcup (D.apply_eq_of_apply_eq h)
  -- The strand starting at `D (inr a)` reaches the middle state `Sum.inl a`, crosses the cap
  -- of `capCup a b` to `Sum.inr b`, and exits at `D (inr b)`.
  have hval_u : (composeDiagram (capCup a b) D).val (D.val (Sum.inr a)) = D.val (Sum.inr b) := by
    have hstart : ∃ s, stackStart (capCup a b) D (D.val (Sum.inr a)) = Sum.inr s ∧
        Relation.ReflTransGen (fun u v => stackStep (capCup a b) D u = Sum.inr v) s
          (Sum.inl a) := by
      rcases hu : D.val (Sum.inr a) with i | c
      · refine ⟨Sum.inl a, ?_, .refl⟩
        rw [stackStart_inl, ← hu, D.apply_apply, Sum.elim_inr]
      · have hca : c ≠ a := fun h => D.apply_ne (Sum.inr a) (by rw [hu, h])
        have hcb : c ≠ b := fun h => hcup (by rw [hu, h])
        refine ⟨Sum.inr c, ?_, .single ?_⟩
        · rw [stackStart_inr, capCup_val_inr_of_ne hca hcb, Sum.elim_inl]
        · rw [stackStep_inr, ← hu, D.apply_apply, Sum.elim_inr]
    have hend : ∃ t, Relation.ReflTransGen (fun u v => stackStep (capCup a b) D u = Sum.inr v)
          (Sum.inr b) t ∧ stackStep (capCup a b) D t = Sum.inl (D.val (Sum.inr b)) := by
      rcases hv : D.val (Sum.inr b) with j | d
      · refine ⟨Sum.inr b, .refl, ?_⟩
        rw [stackStep_inr, hv, Sum.elim_inl]
      · have hda : d ≠ a := fun h => hba_ne (by rw [hv, h])
        have hdb : d ≠ b := fun h => D.apply_ne (Sum.inr b) (by rw [hv, h])
        refine ⟨Sum.inl d, .single ?_, ?_⟩
        · rw [stackStep_inr, hv, Sum.elim_inr]
        · rw [stackStep_inl, capCup_val_inl_of_ne hda hdb, Sum.elim_inr]
    obtain ⟨s, hs, hpath₁⟩ := hstart
    obtain ⟨t, hpath₂, ht⟩ := hend
    have hmid : stackStep (capCup a b) D (Sum.inl a) = Sum.inr (Sum.inr b) := by
      rw [stackStep_inl, capCup_val_inl_left hab, Sum.elim_inl]
    exact (composeDiagram_val_eq_iff _ _).mpr
      (Or.inr ⟨s, t, hs, (hpath₁.tail hmid).trans hpath₂, ht⟩)
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hxa : x = Sum.inr a
  · subst hxa
    rw [PerfectMatching.reconnect_val_self hba']
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab)
  by_cases hxb : x = Sum.inr b
  · subst hxb
    rw [PerfectMatching.reconnect_val_right hba']
    exact composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab)
  by_cases hxu : x = D.val (Sum.inr a)
  · subst hxu
    rw [PerfectMatching.reconnect_val_val_self hba', hval_u]
  by_cases hxv : x = D.val (Sum.inr b)
  · subst hxv
    rw [PerfectMatching.reconnect_val_val_right hba',
      (composeDiagram (capCup a b) D).apply_eq_of_apply_eq hval_u]
  rw [PerfectMatching.reconnect_val_of_ne hxa hxb hxu hxv]
  have hDxa : D.val x ≠ Sum.inr a := fun h => hxu (D.apply_eq_of_apply_eq h).symm
  have hDxb : D.val x ≠ Sum.inr b := fun h => hxv (D.apply_eq_of_apply_eq h).symm
  exact composeDiagram_capCup_val_of_ne hxa hxb hDxa hDxb

/-- If `D` does not cup `{a, b}`, stacking `capCup a b` above `D` closes up no middle loop. -/
private theorem middleLoopCount_capCup_of_apply_ne {D : BrauerDiagram k} (hab : a ≠ b)
    (hcup : D.val (Sum.inr a) ≠ Sum.inr b) :
    middleLoopCount (capCup a b) D = 0 := by
  refine middleLoopCount_eq_zero_iff.mpr fun m hm => ?_
  have ha : OnMiddleLoop (capCup a b) D a := by
    rcases (isCap_capCup_inl_iff hab).mp ((isMiddleVertex_def ..).mp hm.isMiddleVertex).1 with
      rfl | rfl
    · exact hm
    · exact hm.reflTransGen (.single ((middleAdj_def ..).mpr (Or.inl (capCup_val_inl_right hab))))
  obtain ⟨c, hc⟩ :=
    Sum.isRight_iff.mp ((isCup_def D _).mp ((isMiddleVertex_def ..).mp ha.isMiddleVertex).2).2
  have hca : c ≠ a := fun h => D.apply_ne (Sum.inr a) (by rw [hc, h])
  have hcb : c ≠ b := fun h => hcup (by rw [hc, h])
  exact not_onMiddleLoop_of_isThrough_left ((isThrough_capCup_inl_iff hab).mpr ⟨hca, hcb⟩)
    (ha.reflTransGen (.single ((middleAdj_def ..).mpr (Or.inr hc))))

end CapCupDiagram

/-! ### Left multiplication by cap-cup diagrams -/

/-- The matrix of the single-arc generator `TauCeti.symplecticCupCapAt` in the monomial basis. -/
private def capCupMatrix (a b : Fin k) :
    Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R :=
  Matrix.of fun v u =>
    if ∀ t, t ≠ a → t ≠ b → v t = u t then
      -(Matrix.J ι R (u a) (u b) * Matrix.J ι R (v a) (v b))
    else 0

/-- Conjugating `capCupMatrix a b` by a signed permutation matrix renames its pair of strands. -/
private theorem signedPermMatrix_mul_capCupMatrix_mul_inv [Fintype ι]
    (σ : Equiv.Perm (Fin k)) (a b : Fin k) :
    signedPermMatrix R ι σ * capCupMatrix R ι a b * signedPermMatrix R ι σ⁻¹ =
      capCupMatrix R ι (σ a) (σ b) := by
  ext v u
  rw [Matrix.mul_assoc, signedPermMatrix_mul_apply, Matrix.mul_apply]
  have heq (w : Fin k → ι ⊕ ι) : (w = u ∘ σ) ↔ w = u ∘ (σ⁻¹).symm := by
    rw [← Equiv.Perm.inv_def, inv_inv]
  simp only [signedPermMatrix, Matrix.of_apply, ← heq, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [← mul_assoc, mul_comm (((Equiv.Perm.sign σ : ℤ) : R)), mul_assoc, ← Int.cast_mul,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Int.cast_one, mul_one]
  simp only [capCupMatrix, Matrix.of_apply, Function.comp_apply]
  have hcond : (∀ t, t ≠ a → t ≠ b → v (σ t) = u (σ t)) ↔
      (∀ t, t ≠ σ a → t ≠ σ b → v t = u t) := by
    refine ⟨fun h t hta htb => ?_, fun h t hta htb => h (σ t) (σ.injective.ne hta)
      (σ.injective.ne htb)⟩
    simpa using h (σ.symm t) (fun e => hta (by simpa using congrArg σ e))
      (fun e => htb (by simpa using congrArg σ e))
  simp only [hcond]

/-- Left multiplication by `capCupMatrix 0 1` on a matrix `M` sums over the two labels at strands
`0` and `1` with all other strands fixed. -/
private theorem capCupMatrix_zero_one_mul_apply [Fintype ι] {m : ℕ}
    (M : Matrix (Fin (m + 2) → ι ⊕ ι) (Fin (m + 2) → ι ⊕ ι) R)
    (v u : Fin (m + 2) → ι ⊕ ι) :
    (capCupMatrix R ι (0 : Fin (m + 2)) 1 * M) v u =
      ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        -(Matrix.J ι R x y * Matrix.J ι R (v 0) (v 1)) *
          M (Function.update (Function.update v 0 x) 1 y) u := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
  rw [Matrix.mul_apply]
  simp only [capCupMatrix, Matrix.of_apply, ite_mul, zero_mul, ← Finset.sum_filter]
  let f : (ι ⊕ ι) × (ι ⊕ ι) → (Fin (m + 2) → ι ⊕ ι) :=
    fun p => Function.update (Function.update v 0 p.1) 1 p.2
  have hfilt : Finset.univ.filter (fun w : Fin (m + 2) → ι ⊕ ι =>
      ∀ t, t ≠ 0 → t ≠ 1 → v t = w t) = Finset.univ.image f := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun hw => ⟨(w 0, w 1), funext fun t => ?_⟩, ?_⟩
    · rcases eq_or_ne t 1 with rfl | ht1
      · simp [f]
      rcases eq_or_ne t 0 with rfl | ht0
      · simp [f, h01]
      · simp [f, ht0, ht1, hw t ht0 ht1]
    · rintro ⟨⟨x, y⟩, rfl⟩ t ht0 ht1
      simp [f, ht0, ht1]
  have hinj : Set.InjOn f (Finset.univ : Finset ((ι ⊕ ι) × (ι ⊕ ι))) := by
    intro p _ q _ hpq
    have h0 := congrFun hpq 0
    have h1 := congrFun hpq 1
    simp only [f, Function.update_self, Function.update_of_ne h01] at h0 h1
    exact Prod.ext h0 h1
  rw [hfilt, Finset.sum_image hinj, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp [f, h01]

/-- **The cap-cup contraction on strands `0` and `1`** acting on the boundary matrix: if `D` already
cups `{0, 1}` it extracts the symplectic loop value `-(2 * |ι|)` and leaves `D` unchanged;
otherwise it reconnects the two largest boundary points and the Pfaffian sign change matches the
contraction sign of `Matrix.J`. -/
private theorem capCupMatrix_zero_one_mul_symplecticBoundaryMatrix [Fintype ι] {m : ℕ}
    (D : BrauerDiagram (m + 2)) :
    capCupMatrix R ι (0 : Fin (m + 2)) 1 * D.symplecticBoundaryMatrix R ι =
      (-(2 * (Fintype.card ι : R))) ^ middleLoopCount (capCup (0 : Fin (m + 2)) 1) D •
        (composeDiagram (capCup 0 1) D).symplecticBoundaryMatrix R ι := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
  let φ := finSumFinRevEquiv (m + 2) (m + 2) ((m + 2) + (m + 2)) rfl
  set p : Fin ((m + 2) + (m + 2)) := φ (Sum.inr 1)
  set q : Fin ((m + 2) + (m + 2)) := φ (Sum.inr 0)
  have hpq : p < q := (finSumFinRevEquiv_inr_lt_inr_iff ..).mpr (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
  have hp_top : ∀ z : Fin ((m + 2) + (m + 2)), z ≠ q → z ≤ p := by
    intro z hz
    have hpv : (p : ℕ) = (m + 2) + m := by simp [p, φ]
    have hzv : (z : ℕ) ≠ (q : ℕ) := fun h => hz (Fin.ext h)
    have hlt : (z : ℕ) < (m + 2) + (m + 2) := z.isLt
    change (z : ℕ) ≤ (p : ℕ)
    omega
  set M := PerfectMatching.congr φ D
  ext v u
  rw [capCupMatrix_zero_one_mul_apply, Matrix.smul_apply, smul_eq_mul]
  let ℓ : Fin ((m + 2) + (m + 2)) → ι ⊕ ι := fun z => Sum.elim u v (φ.symm z)
  let ℓ' : ι ⊕ ι → ι ⊕ ι → Fin ((m + 2) + (m + 2)) → ι ⊕ ι := fun x y z =>
    Sum.elim u (Function.update (Function.update v 0 x) 1 y) (φ.symm z)
  have hℓ'_p (x y : ι ⊕ ι) : ℓ' x y p = y := by
    simp only [ℓ', p, Equiv.symm_apply_apply, Sum.elim_inr, Function.update_self]
  have hℓ'_q (x y : ι ⊕ ι) : ℓ' x y q = x := by
    simp only [ℓ', q, Equiv.symm_apply_apply, Sum.elim_inr, Function.update_of_ne h01,
      Function.update_self]
  have hℓ'_off (x y : ι ⊕ ι) {z : Fin ((m + 2) + (m + 2))} (hzp : z ≠ p) (hzq : z ≠ q) :
      ℓ' x y z = ℓ z := by
    obtain ⟨w, rfl⟩ := φ.surjective z
    simp only [ℓ', ℓ, Equiv.symm_apply_apply]
    rcases w with i | j
    · rfl
    · have hj1 : j ≠ 1 := fun h => hzp (by simp [p, h])
      have hj0 : j ≠ 0 := fun h => hzq (by simp [q, h])
      simp [hj0, hj1]
  have hℓ_p : ℓ p = v 1 := by simp only [ℓ, p, Equiv.symm_apply_apply, Sum.elim_inr]
  have hℓ_q : ℓ q = v 0 := by simp only [ℓ, q, Equiv.symm_apply_apply, Sum.elim_inr]
  by_cases hcup : D.val (Sum.inr 0) = Sum.inr 1
  · -- Case 1: `{0, 1}` is already a cup of `D`, closing up one loop with factor `-(2 * |ι|)`.
    rw [composeDiagram_capCup_of_apply_eq h01 hcup, middleLoopCount_capCup_of_apply_eq h01 hcup,
      pow_one, symplecticBoundaryMatrix_apply]
    have hMpq : M.val p = q := by
      simp [M, p, q, D.apply_eq_of_apply_eq hcup]
    have hterm (x y : ι ⊕ ι) :
        D.symplecticBoundaryMatrix R ι (Function.update (Function.update v 0 x) 1 y) u =
          ((M.crossingSign : ℤ) : R) * (Matrix.J ι R y x *
            (M.restrict hMpq).weight fun a b => Matrix.J ι R (ℓ a.1) (ℓ b.1)) := by
      rw [symplecticBoundaryMatrix_apply,
        PerfectMatching.weight_eq_min_max_mul_weight_restrict M hMpq,
        min_eq_left hpq.le, max_eq_right hpq.le]
      congr 1
      change Matrix.J ι R (ℓ' x y p) (ℓ' x y q) *
          (M.restrict hMpq).weight (fun a b => Matrix.J ι R (ℓ' x y a.1) (ℓ' x y b.1)) = _
      rw [hℓ'_p, hℓ'_q]
      congr 1
      exact PerfectMatching.weight_congr _ fun a _ => by
        rw [hℓ'_off x y a.2.1 a.2.2, hℓ'_off x y ((M.restrict hMpq).val a).2.1
          ((M.restrict hMpq).val a).2.2]
    have hrhs : M.weight (fun a b => Matrix.J ι R (ℓ a) (ℓ b)) =
        Matrix.J ι R (v 1) (v 0) *
          (M.restrict hMpq).weight fun a b => Matrix.J ι R (ℓ a.1) (ℓ b.1) := by
      rw [PerfectMatching.weight_eq_min_max_mul_weight_restrict M hMpq,
        min_eq_left hpq.le, max_eq_right hpq.le, hℓ_p, hℓ_q]
    simp_rw [hterm]
    change _ = -(2 * (Fintype.card ι : R)) *
        (((M.crossingSign : ℤ) : R) * M.weight fun a b => Matrix.J ι R (ℓ a) (ℓ b))
    rw [hrhs]
    have hcoeff (x y : ι ⊕ ι) :
        -(Matrix.J ι R x y * Matrix.J ι R (v 0) (v 1)) *
          (((M.crossingSign : ℤ) : R) * (Matrix.J ι R y x *
            (M.restrict hMpq).weight fun a b => Matrix.J ι R (ℓ a.1) (ℓ b.1))) =
        -(Matrix.J ι R x y * Matrix.J ι R x y) *
          (((M.crossingSign : ℤ) : R) * (Matrix.J ι R (v 1) (v 0) *
            (M.restrict hMpq).weight fun a b => Matrix.J ι R (ℓ a.1) (ℓ b.1))) := by
      rw [Matrix.J_apply_swap ι R x y, Matrix.J_apply_swap ι R (v 0) (v 1)]
      ring
    simp_rw [hcoeff, ← Finset.sum_mul, Finset.sum_neg_distrib, Matrix.sum_sum_J_mul_J]
  · -- Case 2: `{0, 1}` is not a cup of `D`; reconnect `{p, q}` and contract over `(x, y)`.
    have hcup' : D.val (Sum.inr 1) ≠ Sum.inr 0 := fun h => hcup (D.apply_eq_of_apply_eq h)
    rw [← capCup_comm (0 : Fin (m + 2)) 1, composeDiagram_capCup_of_apply_ne h01.symm hcup',
      middleLoopCount_capCup_of_apply_ne h01.symm hcup', pow_zero, one_mul,
      symplecticBoundaryMatrix_apply]
    have hMpq : M.val p ≠ q := by
      intro h
      rw [PerfectMatching.congr_val_apply, Equiv.symm_apply_apply] at h
      exact hcup' (φ.injective h)
    have hreconn : PerfectMatching.congr φ (D.reconnect (Sum.inr 1) (Sum.inr 0)) =
        M.reconnect p q := by
      have h10 : (Sum.inr (0 : Fin (m + 2)) : Fin (m + 2) ⊕ Fin (m + 2)) ≠ Sum.inr 1 :=
        fun h => h01 (Sum.inr.inj h)
      have hMp : M.val p = φ (D.val (Sum.inr 1)) := by
        simp [M, p]
      have hMq : M.val q = φ (D.val (Sum.inr 0)) := by
        simp [M, q]
      refine PerfectMatching.ext fun z => ?_
      obtain ⟨y, rfl⟩ := φ.surjective z
      rw [PerfectMatching.congr_val_apply, Equiv.symm_apply_apply]
      rcases eq_or_ne y (Sum.inr 1) with rfl | hy1
      · rw [PerfectMatching.reconnect_val_self h10, PerfectMatching.reconnect_val_self hpq.ne']
      rcases eq_or_ne y (Sum.inr 0) with rfl | hy0
      · rw [PerfectMatching.reconnect_val_right h10, PerfectMatching.reconnect_val_right hpq.ne']
      rcases eq_or_ne y (D.val (Sum.inr 1)) with rfl | hyu
      · rw [PerfectMatching.reconnect_val_val_self h10, ← hMp,
          PerfectMatching.reconnect_val_val_self hpq.ne', hMq]
      rcases eq_or_ne y (D.val (Sum.inr 0)) with rfl | hyw
      · rw [PerfectMatching.reconnect_val_val_right h10, ← hMq,
          PerfectMatching.reconnect_val_val_right hpq.ne', hMp]
      · rw [PerfectMatching.reconnect_val_of_ne hy1 hy0 hyu hyw,
          PerfectMatching.reconnect_val_of_ne (φ.injective.ne hy1) (φ.injective.ne hy0)
            (by rw [hMp]; exact φ.injective.ne hyu) (by rw [hMq]; exact φ.injective.ne hyw),
          PerfectMatching.congr_val_apply, Equiv.symm_apply_apply]
    set u₀ := M.val p
    set w₀ := M.val q
    have hu₀_lt : u₀ < p := lt_of_le_of_ne (hp_top u₀ hMpq) (M.apply_ne p)
    have hw₀_lt : w₀ < p :=
      lt_of_le_of_ne (hp_top w₀ (M.apply_ne q)) (fun h => hMpq (M.apply_eq_of_apply_eq h))
    have huw : u₀ ≠ w₀ := M.val.injective.ne hpq.ne
    set S : Finset (Fin ((m + 2) + (m + 2))) := {p, q, u₀, w₀}
    -- Split `M.weight` and `(M.reconnect p q).weight` along `S = {p, q, u₀, w₀}` and `Sᶜ`.
    have hS_prod (g : Fin ((m + 2) + (m + 2)) → R) :
        ∏ z ∈ S, g z = g p * (g q * (g u₀ * g w₀)) := by
      have hp_mem : p ∉ ({q, u₀, w₀} : Finset _) := by simp [hpq.ne, hu₀_lt.ne', hw₀_lt.ne']
      have hq_mem : q ∉ ({u₀, w₀} : Finset _) := by
        simp [(lt_trans hu₀_lt hpq).ne', (lt_trans hw₀_lt hpq).ne']
      rw [Finset.prod_insert hp_mem, Finset.prod_insert hq_mem, Finset.prod_pair huw]
    have hM_weight (f : Fin ((m + 2) + (m + 2)) → Fin ((m + 2) + (m + 2)) → R) :
        M.weight f = f u₀ p * f w₀ q *
          ∏ z ∈ Sᶜ, (if z < M.val z then f z (M.val z) else 1) := by
      rw [PerfectMatching.weight_def, ← Finset.prod_mul_prod_compl S, hS_prod]
      have hMu₀ : M.val u₀ = p := M.apply_apply p
      have hMw₀ : M.val w₀ = q := M.apply_apply q
      have hnp : ¬p < M.val p := not_lt_of_gt hu₀_lt
      have hnq : ¬q < M.val q := not_lt_of_gt (lt_trans hw₀_lt hpq)
      simp only [hMu₀, hMw₀, hu₀_lt, lt_trans hw₀_lt hpq, hnp, hnq, ite_true, ite_false, one_mul]
    have hM'_weight (f : Fin ((m + 2) + (m + 2)) → Fin ((m + 2) + (m + 2)) → R) :
        (M.reconnect p q).weight f = f p q * f (min u₀ w₀) (max u₀ w₀) *
          ∏ z ∈ Sᶜ, (if z < M.val z then f z (M.val z) else 1) := by
      rw [PerfectMatching.weight_def, ← Finset.prod_mul_prod_compl S, hS_prod]
      have hcompl : ∏ z ∈ Sᶜ, (if z < (M.reconnect p q).val z then
            f z ((M.reconnect p q).val z) else 1) =
          ∏ z ∈ Sᶜ, (if z < M.val z then f z (M.val z) else 1) := by
        refine Finset.prod_congr rfl fun z hz => ?_
        have hzS : z ≠ p ∧ z ≠ q ∧ z ≠ u₀ ∧ z ≠ w₀ := by
          simpa [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] using hz
        rw [PerfectMatching.reconnect_val_of_ne hzS.1 hzS.2.1 hzS.2.2.1 hzS.2.2.2]
      have hru₀ : (M.reconnect p q).val u₀ = w₀ :=
        PerfectMatching.reconnect_val_val_self hpq.ne'
      have hrw₀ : (M.reconnect p q).val w₀ = u₀ :=
        PerfectMatching.reconnect_val_val_right hpq.ne'
      rw [hcompl, PerfectMatching.reconnect_val_self hpq.ne',
        PerfectMatching.reconnect_val_right hpq.ne', hru₀, hrw₀,
        ite_eq_left hpq, ite_eq_right (not_lt_of_gt hpq), one_mul]
      rcases lt_or_gt_of_ne huw with hlt | hgt
      · simp [hlt, not_lt_of_gt hlt, min_eq_left hlt.le, max_eq_right hlt.le]
      · simp [hgt, not_lt_of_gt hgt, min_eq_right hgt.le, max_eq_left hgt.le]
    set rest : R := ∏ z ∈ Sᶜ, (if z < M.val z then Matrix.J ι R (ℓ z) (ℓ (M.val z)) else 1)
    have hrest_eq (x y : ι ⊕ ι) :
        ∏ z ∈ Sᶜ, (if z < M.val z then Matrix.J ι R (ℓ' x y z) (ℓ' x y (M.val z)) else 1) =
          rest := by
      refine Finset.prod_congr rfl fun z hz => ?_
      have hzS : z ≠ p ∧ z ≠ q ∧ z ≠ u₀ ∧ z ≠ w₀ := by
        simpa [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] using hz
      have hMzp : M.val z ≠ p := fun h => hzS.2.2.1 (M.apply_eq_of_apply_eq h).symm
      have hMzq : M.val z ≠ q := fun h => hzS.2.2.2 (M.apply_eq_of_apply_eq h).symm
      rw [hℓ'_off x y hzS.1 hzS.2.1, hℓ'_off x y hMzp hMzq]
    have hterm (x y : ι ⊕ ι) :
        D.symplecticBoundaryMatrix R ι (Function.update (Function.update v 0 x) 1 y) u =
          ((M.crossingSign : ℤ) : R) * (Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x * rest) := by
      rw [symplecticBoundaryMatrix_apply]
      change ((M.crossingSign : ℤ) : R) * M.weight (fun a b => Matrix.J ι R (ℓ' x y a) (ℓ' x y b)) =
        _
      rw [hM_weight, hrest_eq, hℓ'_p, hℓ'_q,
        hℓ'_off x y hu₀_lt.ne (lt_trans hu₀_lt hpq).ne,
        hℓ'_off x y hw₀_lt.ne (lt_trans hw₀_lt hpq).ne]
    simp_rw [hterm]
    -- Contract `(x, y)`: `∑ x y, J x y * J (ℓ u₀) y * J (ℓ w₀) x = -J (ℓ u₀) (ℓ w₀)`.
    have hcontract :
        ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
          Matrix.J ι R x y * Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x =
        -Matrix.J ι R (ℓ u₀) (ℓ w₀) := by
      rw [Finset.sum_comm]
      have hinner (y : ι ⊕ ι) :
          ∑ x : ι ⊕ ι, Matrix.J ι R x y * Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x =
            if ℓ w₀ = y then -Matrix.J ι R (ℓ u₀) y else 0 := by
        have hstep (x : ι ⊕ ι) :
            Matrix.J ι R x y * Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x =
              -(Matrix.J ι R x (ℓ w₀) * Matrix.J ι R x y) * Matrix.J ι R (ℓ u₀) y := by
          rw [Matrix.J_apply_swap ι R x (ℓ w₀)]
          ring
        simp_rw [hstep, ← Finset.sum_mul, Finset.sum_neg_distrib, Matrix.sum_J_mul_J_eq_ite]
        split_ifs <;> simp
      simp_rw [hinner, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hstep_lhs (x y : ι ⊕ ι) :
        -(Matrix.J ι R x y * Matrix.J ι R (v 0) (v 1)) *
          (((M.crossingSign : ℤ) : R) * (Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x * rest)) =
        (Matrix.J ι R x y * Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x) *
          (((M.crossingSign : ℤ) : R) * (Matrix.J ι R (v 1) (v 0) * rest)) := by
      rw [Matrix.J_apply_swap ι R (v 0) (v 1)]
      ring
    have hfactor :
        ∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
            -(Matrix.J ι R x y * Matrix.J ι R (v 0) (v 1)) *
              (((M.crossingSign : ℤ) : R) *
                (Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x * rest)) =
          (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
            Matrix.J ι R x y * Matrix.J ι R (ℓ u₀) y * Matrix.J ι R (ℓ w₀) x) *
          (((M.crossingSign : ℤ) : R) * (Matrix.J ι R (v 1) (v 0) * rest)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => hstep_lhs x y
    rw [hfactor, hcontract]
    -- Match with the reconnected boundary matrix via `crossingSign_reconnect_top`.
    change _ = (((PerfectMatching.congr φ (D.reconnect (Sum.inr 1) (Sum.inr 0))).crossingSign :
        ℤ) : R) *
      (PerfectMatching.congr φ (D.reconnect (Sum.inr 1) (Sum.inr 0))).weight
        (fun a b => Matrix.J ι R (ℓ a) (ℓ b))
    rw [hreconn, PerfectMatching.crossingSign_reconnect_top M hpq hp_top hMpq, hM'_weight,
      hℓ_p, hℓ_q]
    rcases lt_or_gt_of_ne huw with hlt | hgt
    · have hlt' : M.val p < M.val q := hlt
      simp only [hlt', ite_true, Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul,
        Int.cast_neg, Int.cast_one, min_eq_left hlt.le, max_eq_right hlt.le]
      ring
    · have hgt' : ¬M.val p < M.val q := not_lt_of_gt hgt
      simp only [hgt', ite_false, one_mul, min_eq_right hgt.le, max_eq_left hgt.le]
      rw [Matrix.J_apply_swap ι R (ℓ w₀) (ℓ u₀)]
      ring

/-- Left multiplication of the boundary matrix by `capCupMatrix a b` for any `a ≠ b` composes on
the top with `capCup a b` and extracts the symplectic loop factor. -/
private theorem capCupMatrix_mul_symplecticBoundaryMatrix [Fintype ι] {a b : Fin k}
    (hab : a ≠ b) (D : BrauerDiagram k) :
    capCupMatrix R ι a b * D.symplecticBoundaryMatrix R ι =
      (-(2 * (Fintype.card ι : R))) ^ middleLoopCount (capCup a b) D •
        (composeDiagram (capCup a b) D).symplecticBoundaryMatrix R ι := by
  have hk : 2 ≤ k := by
    have ha := a.isLt
    have hb := b.isLt
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![(0 : Fin (m + 2)), 1] ![a, b]
    (Matrix.injective_pair_iff_ne.mpr h01) (Matrix.injective_pair_iff_ne.mpr hab)
  obtain ⟨rfl, rfl⟩ : σ 0 = a ∧ σ 1 = b := ⟨hσ 0, hσ 1⟩
  have hloop :
      middleLoopCount (capCup (σ 0) (σ 1)) D =
        middleLoopCount (capCup 0 1) (composeDiagram (permToBrauer σ⁻¹) D) := by
    have hiff : D.val (Sum.inr (σ 0)) = Sum.inr (σ 1) ↔
        (composeDiagram (permToBrauer σ⁻¹) D).val (Sum.inr 0) = Sum.inr 1 := by
      rw [composeDiagram_permToBrauer_left, relabel_val_inr]
      have hinv : (σ⁻¹).symm 0 = σ 0 := by rw [← Equiv.Perm.inv_def, inv_inv]
      rw [hinv]
      rcases D.val (Sum.inr (σ 0)) with i | j
      · simp
      · simp [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    by_cases h : D.val (Sum.inr (σ 0)) = Sum.inr (σ 1)
    · rw [middleLoopCount_capCup_of_apply_eq hab h,
        middleLoopCount_capCup_of_apply_eq h01 (hiff.mp h)]
    · rw [middleLoopCount_capCup_of_apply_ne hab h,
        middleLoopCount_capCup_of_apply_ne h01 (mt hiff.mpr h)]
  calc
    capCupMatrix R ι (σ 0) (σ 1) * D.symplecticBoundaryMatrix R ι
        = signedPermMatrix R ι σ * capCupMatrix R ι 0 1 * signedPermMatrix R ι σ⁻¹ *
            D.symplecticBoundaryMatrix R ι := by
          rw [signedPermMatrix_mul_capCupMatrix_mul_inv]
    _ = signedPermMatrix R ι σ * (capCupMatrix R ι 0 1 *
          (signedPermMatrix R ι σ⁻¹ * D.symplecticBoundaryMatrix R ι)) := by
          simp only [Matrix.mul_assoc]
    _ = signedPermMatrix R ι σ * (capCupMatrix R ι 0 1 *
          (composeDiagram (permToBrauer σ⁻¹) D).symplecticBoundaryMatrix R ι) := by
          rw [signedPermMatrix_mul_symplecticBoundaryMatrix]
    _ = (-(2 * (Fintype.card ι : R))) ^
          middleLoopCount (capCup 0 1) (composeDiagram (permToBrauer σ⁻¹) D) •
            (signedPermMatrix R ι σ *
              (composeDiagram (capCup 0 1)
                (composeDiagram (permToBrauer σ⁻¹) D)).symplecticBoundaryMatrix R ι) := by
          rw [capCupMatrix_zero_one_mul_symplecticBoundaryMatrix, Matrix.mul_smul]
    _ = (-(2 * (Fintype.card ι : R))) ^ middleLoopCount (capCup (σ 0) (σ 1)) D •
          (composeDiagram (capCup (σ 0) (σ 1)) D).symplecticBoundaryMatrix R ι := by
          rw [signedPermMatrix_mul_symplecticBoundaryMatrix, ← hloop,
            ← composeDiagram_assoc (capCup 0 1), ← composeDiagram_assoc (permToBrauer σ),
            composeDiagram_permToBrauer_conj_capCup]

/-- Left multiplication of the action matrix by `capCupMatrix a b` composes on the top with
`capCup a b` and extracts the symplectic loop factor. -/
private theorem capCupMatrix_mul_symplecticActionMatrix [Fintype ι] {a b : Fin k}
    (hab : a ≠ b) (D : BrauerDiagram k) :
    capCupMatrix R ι a b * D.symplecticActionMatrix R ι =
      (-(2 * (Fintype.card ι : R))) ^ middleLoopCount (capCup a b) D •
        (composeDiagram (capCup a b) D).symplecticActionMatrix R ι := by
  rw [symplecticActionMatrix_def, symplecticActionMatrix_def, ← Matrix.mul_assoc,
    capCupMatrix_mul_symplecticBoundaryMatrix R ι hab, Matrix.smul_mul]

/-- **The action matrix of a cap-cup diagram** on two distinct strands `a ≠ b`: entry `(v, u)` is
`-(J (u a) (u b) * J (v a) (v b))` when `v` agrees with `u` off `{a, b}`, and `0` otherwise. -/
theorem symplecticActionMatrix_capCup [Fintype ι] {a b : Fin k} (hab : a ≠ b)
    (v u : Fin k → ι ⊕ ι) :
    (capCup a b).symplecticActionMatrix R ι v u =
      if ∀ t, t ≠ a → t ≠ b → v t = u t then
        -(Matrix.J ι R (u a) (u b) * Matrix.J ι R (v a) (v b))
      else 0 := by
  have h := capCupMatrix_mul_symplecticActionMatrix R ι hab (permToBrauer 1)
  rw [symplecticActionMatrix_permToBrauer_one, Matrix.mul_one, middleLoopCount_permToBrauer_right,
    pow_zero, one_smul, composeDiagram_permToBrauer_one_right] at h
  exact congrFun (congrFun h.symm v) u

/-- Left multiplication by the action matrix of a cap-cup diagram obeys the loop rule. -/
private theorem symplecticActionMatrix_capCup_mul [Fintype ι] {a b : Fin k}
    (hab : a ≠ b) (D : BrauerDiagram k) :
    (capCup a b).symplecticActionMatrix R ι * D.symplecticActionMatrix R ι =
      (-(2 * (Fintype.card ι : R))) ^ middleLoopCount (capCup a b) D •
        (composeDiagram (capCup a b) D).symplecticActionMatrix R ι := by
  have h : (capCup a b).symplecticActionMatrix R ι = capCupMatrix R ι a b := by
    ext v u
    exact symplecticActionMatrix_capCup R ι hab v u
  rw [h, capCupMatrix_mul_symplecticActionMatrix R ι hab]

/-! ### The loop rule -/

/-- **The loop rule for the symplectic action matrices.** Multiplying the action matrices of `D₁`
and `D₂` gives the action matrix of the composite `TauCeti.composeDiagram D₁ D₂`, scaled by
`-(2 * |ι|)` raised to the number of closed middle loops. -/
theorem symplecticActionMatrix_mul [Fintype ι] (D₁ D₂ : BrauerDiagram k) :
    D₁.symplecticActionMatrix R ι * D₂.symplecticActionMatrix R ι =
      (-(2 * (Fintype.card ι : R))) ^ middleLoopCount D₁ D₂ •
        (composeDiagram D₁ D₂).symplecticActionMatrix R ι := by
  induction D₁ using BrauerDiagram.capCup_induction_on with
  | permToBrauer σ =>
    rw [middleLoopCount_permToBrauer_left, pow_zero, one_smul,
      symplecticActionMatrix_permToBrauer_mul]
  | capCup_compose a b X hab hloop ih =>
    have hX : (composeDiagram (capCup a b) X).symplecticActionMatrix R ι =
        (capCup a b).symplecticActionMatrix R ι * X.symplecticActionMatrix R ι := by
      rw [symplecticActionMatrix_capCup_mul R ι hab, hloop, pow_zero, one_smul]
    rw [hX, Matrix.mul_assoc, ih, Matrix.mul_smul, symplecticActionMatrix_capCup_mul R ι hab,
      smul_smul, ← pow_add, composeDiagram_assoc]
    have hcount := middleLoopCount_add_middleLoopCount_composeDiagram (capCup a b) X D₂
    rw [hloop, zero_add] at hcount
    rw [hcount, add_comm]

/-! ### Congruence invariance and transposition -/

/-- For a perfect matching on a finite linear order, a product over all points splits into a
product of pairs over the smaller endpoints of its arcs. -/
private theorem prod_eq_prod_lt {α : Type*} [Fintype α] [LinearOrder α] (M : PerfectMatching α)
    (g : α → R) :
    ∏ x : α, g x = ∏ x : {x : α // x < M.val x}, g x.1 * g (M.val x.1) := by
  let s : Finset α := Finset.univ.filter fun x => x < M.val x
  rw [← Finset.prod_mul_prod_compl s]
  have hcompl : ∏ x ∈ sᶜ, g x = ∏ x ∈ s, g (M.val x) := by
    refine Finset.prod_bij (fun x _ => M.val x) (fun x hx => ?_)
      (fun x₁ _ x₂ _ h => M.val.injective h) (fun y hy => ?_) (fun x _ => by rw [M.apply_apply])
    · simp only [s, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx ⊢
      rw [M.apply_apply]
      exact lt_of_le_of_ne hx (M.apply_ne x)
    · refine ⟨M.val y, ?_, M.apply_apply y⟩
      simp only [s, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hy ⊢
      rw [M.apply_apply]
      exact le_of_lt hy
  rw [hcompl, ← Finset.prod_mul_distrib,
    Finset.prod_subtype (p := fun x => x < M.val x) s (fun x => by simp [s])]

/-- **Congruence invariance of the symplectic boundary matrix.** If `A * J * Aᵀ = J`, then
congruating the boundary matrix of `D` by the Kronecker power of `A` leaves it unchanged. -/
theorem kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose [Fintype ι]
    (D : BrauerDiagram k) {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R}
    (hA : A * Matrix.J ι R * Aᵀ = Matrix.J ι R) :
    A.kroneckerPower (Fin k) * D.symplecticBoundaryMatrix R ι * (A.kroneckerPower (Fin k))ᵀ =
      D.symplecticBoundaryMatrix R ι := by
  let φ := finSumFinRevEquiv k k (k + k) rfl
  set M := PerfectMatching.congr φ D
  ext v u
  let ℓ : Fin (k + k) → ι ⊕ ι := fun x => Sum.elim u v (φ.symm x)
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.kroneckerPower_apply,
    symplecticBoundaryMatrix_apply, Finset.sum_mul]
  -- Pull out `M.crossingSign` and reindex `(w₂, w₁)` as a labelling `m : Fin (k + k) → ι ⊕ ι`.
  have hterm (w₂ w₁ : Fin k → ι ⊕ ι) :
      (∏ i : Fin k, A (v i) (w₁ i)) *
          (((M.crossingSign : ℤ) : R) * M.weight fun x y =>
            Matrix.J ι R (Sum.elim w₂ w₁ (φ.symm x)) (Sum.elim w₂ w₁ (φ.symm y))) *
        ∏ j : Fin k, A (u j) (w₂ j) =
      ((M.crossingSign : ℤ) : R) *
        ((∏ x : Fin (k + k), A (ℓ x) (Sum.elim w₂ w₁ (φ.symm x))) *
          M.weight fun x y =>
            Matrix.J ι R (Sum.elim w₂ w₁ (φ.symm x)) (Sum.elim w₂ w₁ (φ.symm y))) := by
    have hprod : ∏ x : Fin (k + k), A (ℓ x) (Sum.elim w₂ w₁ (φ.symm x)) =
        (∏ j : Fin k, A (u j) (w₂ j)) * ∏ i : Fin k, A (v i) (w₁ i) := by
      rw [← Fintype.prod_equiv φ _ _ fun _ => rfl, Fintype.prod_sum_type]
      simp only [ℓ, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    rw [hprod]
    ring
  change (∑ w₂ : Fin k → ι ⊕ ι, ∑ w₁ : Fin k → ι ⊕ ι,
      (∏ i : Fin k, A (v i) (w₁ i)) *
          (((M.crossingSign : ℤ) : R) * M.weight fun x y =>
            Matrix.J ι R (Sum.elim w₂ w₁ (φ.symm x)) (Sum.elim w₂ w₁ (φ.symm y))) *
        ∏ j : Fin k, A (u j) (w₂ j)) =
    ((M.crossingSign : ℤ) : R) * M.weight (fun x y => Matrix.J ι R (ℓ x) (ℓ y))
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  let e₁ : (Fin (k + k) → ι ⊕ ι) ≃ (Fin k → ι ⊕ ι) × (Fin k → ι ⊕ ι) :=
    (Equiv.arrowCongr φ (Equiv.refl (ι ⊕ ι))).symm.trans
      (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) (ι ⊕ ι))
  have he₁ (p : (Fin k → ι ⊕ ι) × (Fin k → ι ⊕ ι)) (x : Fin (k + k)) :
      e₁.symm p x = Sum.elim p.1 p.2 (φ.symm x) := by
    simp only [e₁, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_apply,
      Function.comp_apply, Equiv.coe_refl, id_eq]
    cases φ.symm x <;> rfl
  rw [← Fintype.sum_prod_type (f := fun p : (Fin k → ι ⊕ ι) × (Fin k → ι ⊕ ι) =>
    (∏ x : Fin (k + k), A (ℓ x) (Sum.elim p.1 p.2 (φ.symm x))) *
      M.weight fun x y => Matrix.J ι R (Sum.elim p.1 p.2 (φ.symm x))
        (Sum.elim p.1 p.2 (φ.symm y)))]
  have hsum₁ :
      ∑ p : (Fin k → ι ⊕ ι) × (Fin k → ι ⊕ ι),
          (∏ x : Fin (k + k), A (ℓ x) (Sum.elim p.1 p.2 (φ.symm x))) *
            M.weight (fun x y => Matrix.J ι R (Sum.elim p.1 p.2 (φ.symm x))
              (Sum.elim p.1 p.2 (φ.symm y))) =
        ∑ m : Fin (k + k) → ι ⊕ ι,
          (∏ x : Fin (k + k), A (ℓ x) (m x)) *
            M.weight (fun x y => Matrix.J ι R (m x) (m y)) := by
    symm
    refine Fintype.sum_equiv e₁ _ _ fun m => ?_
    have hm : ∀ x, Sum.elim (e₁ m).1 (e₁ m).2 (φ.symm x) = m x := fun x => by
      rw [← he₁ (e₁ m) x, Equiv.symm_apply_apply]
    simp_rw [hm]
  rw [hsum₁]
  -- Factor the sum over `m : Fin (k + k) → ι ⊕ ι` arc by arc into a product over `{x // x < M x}`.
  let L := {x : Fin (k + k) // x < M.val x}
  let e₂ : (Fin (k + k) → ι ⊕ ι) ≃ (L → (ι ⊕ ι) × (ι ⊕ ι)) :=
    { toFun := fun m x => (m x.1, m (M.val x.1))
      invFun := fun f y =>
        if hy : y < M.val y then (f ⟨y, hy⟩).1
        else (f ⟨M.val y, by
          rw [M.apply_apply]
          exact lt_of_le_of_ne (not_lt.mp hy) (M.apply_ne y)⟩).2
      left_inv := fun m => funext fun y => by
        by_cases hy : y < M.val y
        · simp [hy]
        · simp [hy, M.apply_apply]
      right_inv := fun f => funext fun x => by
        have hlt : x.1 < M.val x.1 := x.2
        have hgt : ¬M.val x.1 < M.val (M.val x.1) := by
          rw [M.apply_apply]
          exact not_lt_of_gt hlt
        ext
        · simp [hlt]
        · dsimp
          rw [dite_eq_right hgt]
          simp [M.apply_apply] }
  have hweight (w : Fin (k + k) → Fin (k + k) → R) :
      M.weight w = ∏ x : L, w x.1 (M.val x.1) := by
    rw [PerfectMatching.weight_def, ← Finset.prod_filter,
      Finset.prod_subtype (p := fun x => x < M.val x) (Finset.univ.filter fun x => x < M.val x)
        (fun x => by simp)]
  have hsummand (m : Fin (k + k) → ι ⊕ ι) :
      (∏ x : Fin (k + k), A (ℓ x) (m x)) * M.weight (fun x y => Matrix.J ι R (m x) (m y)) =
        ∏ x : L, A (ℓ x.1) (e₂ m x).1 * A (ℓ (M.val x.1)) (e₂ m x).2 *
          Matrix.J ι R (e₂ m x).1 (e₂ m x).2 := by
    rw [prod_eq_prod_lt R M, hweight, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [hsummand]
  rw [Fintype.sum_equiv e₂ _
      (fun f => ∏ x : L, A (ℓ x.1) (f x).1 * A (ℓ (M.val x.1)) (f x).2 *
        Matrix.J ι R (f x).1 (f x).2)
      (fun _ => rfl),
    ← Fintype.prod_sum (fun (x : L) (p : (ι ⊕ ι) × (ι ⊕ ι)) =>
      A (ℓ x.1) p.1 * A (ℓ (M.val x.1)) p.2 * Matrix.J ι R p.1 p.2),
    hweight]
  refine Finset.prod_congr rfl fun x _ => ?_
  have hentry := congrFun (congrFun hA (ℓ x.1)) (ℓ (M.val x.1))
  rw [← hentry, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Transposing the boundary matrix reflects the diagram up to the sign `(-1) ^ k`. -/
private theorem transpose_symplecticBoundaryMatrix (D : BrauerDiagram k) :
    (D.symplecticBoundaryMatrix R ι)ᵀ =
      (-1 : R) ^ k • D.flip.symplecticBoundaryMatrix R ι := by
  let φ := finSumFinRevEquiv k k (k + k) rfl
  have hrev (x : Fin (k + k)) : φ.symm (Fin.revPerm x) = (φ.symm x).swap := by
    apply φ.injective
    rw [Equiv.apply_symm_apply, finSumFinRevEquiv_swap rfl, Equiv.apply_symm_apply]
    rfl
  have hflip : PerfectMatching.congr φ D.flip =
      PerfectMatching.congr Fin.revPerm (PerfectMatching.congr φ D) := by
    refine PerfectMatching.ext fun x => ?_
    rw [PerfectMatching.congr_val_apply, PerfectMatching.congr_val_apply,
      PerfectMatching.congr_val_apply, BrauerDiagram.flip_val, finSumFinRevEquiv_swap rfl]
    have hsymm : Fin.revPerm.symm x = Fin.revPerm x := rfl
    rw [hsymm, hrev x]
    rfl
  ext v u
  rw [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    symplecticBoundaryMatrix_apply, symplecticBoundaryMatrix_apply, hflip,
    PerfectMatching.crossingSign_congr_revPerm,
    PerfectMatching.weight_congr_strictAnti_of_skew _ Fin.revPerm
      (fun _ _ h => Fin.rev_lt_rev.mpr h) (fun _ _ => Matrix.J_apply_swap ι R _ _)]
  have hcard : Fintype.card (Fin (k + k)) / 2 = k := by
    rw [Fintype.card_fin]
    omega
  have hw : (fun x y => Matrix.J ι R (Sum.elim u v (φ.symm (Fin.revPerm x)))
        (Sum.elim u v (φ.symm (Fin.revPerm y)))) =
      (fun x y => Matrix.J ι R (Sum.elim v u (φ.symm x)) (Sum.elim v u (φ.symm y))) := by
    funext x y
    rw [hrev x, hrev y]
    cases φ.symm x <;> cases φ.symm y <;> rfl
  have hsign : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [hcard, hw]
  calc
    (((PerfectMatching.congr φ D).crossingSign : ℤ) : R) *
        (PerfectMatching.congr φ D).weight (fun x y =>
          Matrix.J ι R (Sum.elim v u (φ.symm x)) (Sum.elim v u (φ.symm y)))
        = ((-1 : R) ^ k * (-1 : R) ^ k) *
            ((((PerfectMatching.congr φ D).crossingSign : ℤ) : R) *
              (PerfectMatching.congr φ D).weight (fun x y =>
                Matrix.J ι R (Sum.elim v u (φ.symm x)) (Sum.elim v u (φ.symm y)))) := by
          rw [hsign, one_mul]
    _ = (-1 : R) ^ k *
          ((((PerfectMatching.congr φ D).crossingSign : ℤ) : R) *
            ((-1 : R) ^ k * (PerfectMatching.congr φ D).weight (fun x y =>
              Matrix.J ι R (Sum.elim v u (φ.symm x)) (Sum.elim v u (φ.symm y))))) := by
          ring

/-- **Reflecting a diagram transposes its symplectic action matrix.** -/
@[simp]
theorem transpose_symplecticActionMatrix [Fintype ι] (D : BrauerDiagram k) :
    (D.symplecticActionMatrix R ι)ᵀ = D.flip.symplecticActionMatrix R ι := by
  set K := (Matrix.J ι R).kroneckerPower (Fin k)
  have hKT : Kᵀ = (-1 : R) ^ k • K := by
    ext v u
    simp only [K, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.kroneckerPower_apply]
    have hentry (i : Fin k) : Matrix.J ι R (u i) (v i) = (-1 : R) * Matrix.J ι R (v i) (u i) := by
      rw [Matrix.J_apply_swap ι R (v i) (u i), neg_one_mul]
    simp_rw [hentry, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hJ : Matrix.J ι R * Matrix.J ι R * (Matrix.J ι R)ᵀ = Matrix.J ι R := by
    rw [Matrix.J_squared, Matrix.J_transpose, neg_one_mul, neg_neg]
  have hJTJ : (Matrix.J ι R)ᵀ * Matrix.J ι R = 1 := by
    rw [Matrix.J_transpose]
    exact Matrix.neg_J_mul_J ι R
  have hcomm : K * D.flip.symplecticBoundaryMatrix R ι =
      D.flip.symplecticBoundaryMatrix R ι * K := by
    have hconj := kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose R ι D.flip hJ
    calc
      K * D.flip.symplecticBoundaryMatrix R ι
          = K * D.flip.symplecticBoundaryMatrix R ι * (Kᵀ * K) := by
            rw [Matrix.transpose_kroneckerPower_mul_self hJTJ, Matrix.mul_one]
      _ = (K * D.flip.symplecticBoundaryMatrix R ι * Kᵀ) * K := by
            simp only [Matrix.mul_assoc]
      _ = D.flip.symplecticBoundaryMatrix R ι * K := by
            rw [hconj]
  have hsign : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [symplecticActionMatrix_def, symplecticActionMatrix_def, Matrix.transpose_mul, hKT,
    transpose_symplecticBoundaryMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsign,
    one_smul, hcomm]

/-- **Conjugate-transposing a symplectic action matrix reflects the diagram**: every entry is an
integer expression built from the crossing sign and the entries of `Matrix.J`, so `star` fixes it
and the conjugate transpose equals the transpose. -/
@[simp]
theorem conjTranspose_symplecticActionMatrix [Fintype ι] [StarRing R] (D : BrauerDiagram k) :
    (D.symplecticActionMatrix R ι)ᴴ = D.flip.symplecticActionMatrix R ι := by
  have hstarJ (x y : ι ⊕ ι) : star (Matrix.J ι R x y) = Matrix.J ι R x y := by
    rw [← Matrix.map_J ι (Int.castRingHom R), Matrix.map_apply, eq_intCast, star_intCast]
  have hstar_bdry (v u : Fin k → ι ⊕ ι) :
      star (D.symplecticBoundaryMatrix R ι v u) = D.symplecticBoundaryMatrix R ι v u := by
    rw [symplecticBoundaryMatrix_apply, star_mul', star_intCast, ← starRingEnd_apply,
      PerfectMatching.map_weight]
    simp only [starRingEnd_apply, hstarJ]
  rw [← transpose_symplecticActionMatrix]
  ext v u
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, symplecticActionMatrix_def,
    Matrix.mul_apply, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [star_mul', hstar_bdry, Matrix.kroneckerPower_apply, ← starRingEnd_apply, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [starRingEnd_apply]
  exact hstarJ _ _

end TauCeti.BrauerDiagram
