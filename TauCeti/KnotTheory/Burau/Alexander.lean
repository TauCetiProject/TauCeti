/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Alexander
public import TauCeti.KnotTheory.Burau.Basic
public import TauCeti.KnotTheory.Markov
public import TauCeti.LinearAlgebra.Matrix.CornerMinor

/-!
# The Alexander polynomial of a braid closure, from the Burau representation

Closing a braid on `n` strands, by joining the `i`-th endpoint at the top to the `i`-th endpoint
at the bottom, presents an oriented link. This file attaches a Laurent-polynomial-valued invariant
to that presentation, read off the unreduced Burau representation:
`TauCeti.MarkovBraid.burauAlexander` is the determinant of `burau b - 1` with its last row and its
last column deleted.

That *corner minor* is the right quantity because of the two invariant vectors of the Burau
representation. The all-ones column vector is fixed and the geometric row vector
`(1, t, …, t ^ (n - 1))` is fixed, so `burau b - 1` is annihilated by the first on the right and
by the second on the left; a matrix with two such annihilators has a corner minor unchanged by
conjugation by anything fixing them (`Matrix.det_submatrix_castSucc_conj`), and that is precisely
Markov's conjugation move. The other Markov move, adding a strand and crossing it once with the
previous one, multiplies the corner minor by `-t` when the new crossing is positive and by `-1`
when it is negative. Both factors are units, so the corner minor is constant along Markov
equivalence up to a unit of the coefficient ring: `TauCeti.MarkovEquiv.associated_burauAlexander`.
By Markov's theorem (not formalized here) that makes it an invariant of the closure as an oriented
link, defined up to a unit; over `ℤ[T;T⁻¹]` at `t = T` the units are `± T ^ k`, which is the
classical indeterminacy of the Alexander polynomial.

The unreduced representation is used rather than the reduced one exactly because of that
transformation law: the two stabilizations must change the invariant by a unit, and here they do.

Two computations keep the invariant honest. The braid `σ₀ ^ 3` on two strands, whose closure is
the right-handed trefoil, has invariant `-t (t ^ 2 - t + 1)`; over `ℤ[T;T⁻¹]` this is associated
to `T - 1 + T⁻¹`, the value that the Seifert-matrix route of `TauCeti/KnotTheory/Alexander.lean`
produces from `TauCeti.KnotTheory.trefoilSeifertMatrix`, so the two routes to the Alexander
polynomial agree on the trefoil. Over `ℤ` at `t = -1` the same braid has invariant `3` while the
trivial one-strand braid has invariant `1`, and `3` and `1` are not associated in `ℤ`; hence the
two are not Markov equivalent. Their closures both have one component, so this is a separation
that `TauCeti.MarkovBraid.componentCount` cannot make.

Everything is stated over an arbitrary commutative ring `R` and an arbitrary unit `t : Rˣ`, as in
`TauCeti/KnotTheory/Burau/Basic.lean`; the knot-theoretic case is `R = ℤ[T;T⁻¹]` and `t = T`.

## Main definitions

* `TauCeti.MarkovBraid.burauAlexander`: the corner minor of `burau b - 1`.

## Main results

* `TauCeti.KnotTheory.submatrix_burau_strandIncl` and
  `TauCeti.KnotTheory.burau_strandIncl_mulVec_single`: the Burau matrix of a braid with an extra
  uncrossed strand is the old matrix in the old strands, and fixes the new strand.
* `TauCeti.KnotTheory.burau_sub_one_mulVec_one` and
  `TauCeti.KnotTheory.geom_vecMul_burau_sub_one`: the two vectors annihilating `burau b - 1`,
  and `TauCeti.KnotTheory.det_burau_sub_one`, its vanishing determinant.
* `TauCeti.MarkovBraid.burauAlexander_conj`,
  `TauCeti.MarkovBraid.burauAlexander_stabilize` and
  `TauCeti.MarkovBraid.burauAlexander_stabilizeInv`: the effect of each Markov move.
* `TauCeti.MarkovEquiv.associated_burauAlexander`: Markov-equivalent braids have associated
  invariants.
* `TauCeti.MarkovBraid.burauAlexander_sigma_pow_three`: the trefoil value `-t (t ^ 2 - t + 1)`.
* `TauCeti.KnotTheory.associated_burauAlexander_alexander_trefoilSeifertMatrix`: on the trefoil
  this agrees, up to a unit of `ℤ[T;T⁻¹]`, with the Alexander polynomial of a Seifert matrix.
* `TauCeti.not_markovEquiv_sigma_pow_three_one`: the trefoil braid is not Markov equivalent to
  the trivial one-strand braid.

## References

* W. Burau, *Über Zopfgruppen und gleichsinnig verdrillte Verkettungen*, Abh. Math. Semin. Univ.
  Hambg. 11 (1935), 179-186.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Theorem 3.11 (the Alexander polynomial of a braid closure from the Burau matrix).
* C. Kassel, V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 3.3.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1, 6
  and 16.
-/

public section

open Matrix

namespace TauCeti

open KnotTheory

variable {R : Type*} [CommRing R] {n : ℕ}

namespace KnotTheory

/-! ### The Burau matrix of a braid with an extra uncrossed strand -/

private theorem burauCol_castSucc (t : R) (i : Fin n) (u : Fin (n + 1)) :
    burauCol (n := n + 2) t i.castSucc u.castSucc = burauCol (n := n + 1) t i u := by
  rw [burauCol_apply, burauCol_apply]
  simp only [Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc, Fin.val_castSucc]

private theorem burauRow_castSucc (i : Fin n) (u : Fin (n + 1)) :
    burauRow R (n := n + 2) i.castSucc u.castSucc = burauRow R (n := n + 1) i u := by
  rw [burauRow_apply, burauRow_apply]
  simp only [Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc, Fin.val_castSucc]

private theorem burau_strandIncl_aux (t : Rˣ) (b : BraidGroup (n + 1)) :
    ((burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R) *ᵥ
        Pi.single (Fin.last (n + 1)) 1 = Pi.single (Fin.last (n + 1)) 1) ∧
      (burau (n + 2) t (BraidGroup.strandIncl b) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix Fin.castSucc Fin.castSucc =
        (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  induction b using BraidGroup.sigma_induction_on with
  | sigma i =>
    rw [BraidGroup.strandIncl_sigma, burau_sigma, burau_sigma, coe_burauGL, coe_burauGL]
    refine ⟨?_, ?_⟩
    · rw [burauMatrix_mulVec, burauRow_dotProduct]
      have h₁ : (Pi.single (Fin.last (n + 1)) 1 : Fin (n + 2) → R)
          (BraidGroup.strand (n := n + 2) i.castSucc) = 0 := by
        refine Pi.single_eq_of_ne ?_ 1
        simp only [Ne, Fin.ext_iff, BraidGroup.val_strand, Fin.val_last, Fin.val_castSucc]
        omega
      have h₂ : (Pi.single (Fin.last (n + 1)) 1 : Fin (n + 2) → R)
          (BraidGroup.strandSucc (n := n + 2) i.castSucc) = 0 := by
        refine Pi.single_eq_of_ne ?_ 1
        simp only [Ne, Fin.ext_iff, BraidGroup.val_strandSucc, Fin.val_last, Fin.val_castSucc]
        omega
      rw [h₁, h₂, sub_self, zero_smul, sub_zero]
    · ext u v
      rw [Matrix.submatrix_apply, burauMatrix_apply, burauMatrix_apply, burauCol_castSucc,
        burauRow_castSucc]
      simp [Fin.castSucc_inj]
  | one =>
    rw [map_one, map_one, map_one, Units.val_one, Units.val_one]
    refine ⟨Matrix.one_mulVec _, ?_⟩
    ext u v
    rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castSucc_inj]
  | mul b b' hb hb' =>
    rw [map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, hb'.1, hb.1]
    · rw [Matrix.submatrix_mul_of_mulVec_single _ _ hb.1, hb.2, hb'.2, ← Units.val_mul,
        ← map_mul]
  | inv b hb =>
    have hunit : ((burau (n + 2) t (BraidGroup.strandIncl b))⁻¹ : GL (Fin (n + 2)) R) *
        (burau (n + 2) t (BraidGroup.strandIncl b)) = 1 := inv_mul_cancel _
    have hmat : ((burau (n + 2) t (BraidGroup.strandIncl b⁻¹) : GL (Fin (n + 2)) R) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) R) *
        (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R) = 1 := by
      rw [map_inv, map_inv, ← Units.val_mul, hunit, Units.val_one]
    have hcol : (burau (n + 2) t (BraidGroup.strandIncl b⁻¹) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) R) *ᵥ Pi.single (Fin.last (n + 1)) 1 =
        Pi.single (Fin.last (n + 1)) 1 := by
      conv_lhs => rw [← hb.1]
      rw [Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]
    refine ⟨hcol, ?_⟩
    have hprod := congrArg (fun X : Matrix (Fin (n + 2)) (Fin (n + 2)) R =>
      X.submatrix Fin.castSucc Fin.castSucc) hmat
    simp only [Matrix.submatrix_mul_of_mulVec_single _ _ hcol, hb.2] at hprod
    have hone : ((1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R)).submatrix
        Fin.castSucc Fin.castSucc = 1 := by
      ext u v
      rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
      simp [Fin.castSucc_inj]
    rw [hone] at hprod
    have hbinv : (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        (burau (n + 1) t b⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 := by
      rw [map_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (burau (n + 2) t (BraidGroup.strandIncl b⁻¹) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix Fin.castSucc Fin.castSucc
        = _ * ((burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
            (burau (n + 1) t b⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) := by
          rw [hbinv, Matrix.mul_one]
      _ = (burau (n + 1) t b⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
          rw [← Matrix.mul_assoc, hprod, Matrix.one_mul]

/-- **The Burau matrix of a braid with an uncrossed strand added.** Deleting the new strand's row
and column recovers the Burau matrix of the original braid. -/
theorem submatrix_burau_strandIncl (t : Rˣ) (b : BraidGroup (n + 1)) :
    (burau (n + 2) t (BraidGroup.strandIncl b) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix Fin.castSucc Fin.castSucc =
      (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
  (burau_strandIncl_aux t b).2

/-- The new strand of `TauCeti.BraidGroup.strandIncl b` is fixed by the Burau matrix: the last
column is the last standard basis vector. -/
theorem burau_strandIncl_mulVec_single (t : Rˣ) (b : BraidGroup (n + 1)) :
    (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R) *ᵥ
        Pi.single (Fin.last (n + 1)) 1 = Pi.single (Fin.last (n + 1)) 1 :=
  (burau_strandIncl_aux t b).1

/-! ### The elementary Burau matrix of the last crossing -/

private theorem burauCol_last_castSucc (t : R) (c : Fin (n + 1)) :
    burauCol (n := n + 2) t (Fin.last n) c.castSucc = if c = Fin.last n then t else 0 := by
  have hc := c.isLt
  have h1 : (c.castSucc = BraidGroup.strand (n := n + 2) (Fin.last n)) ↔ c = Fin.last n := by
    simp only [Fin.ext_iff, BraidGroup.val_strand, Fin.val_castSucc, Fin.val_last]
  have h2 : ¬ c.castSucc = BraidGroup.strandSucc (n := n + 2) (Fin.last n) := by
    simp only [Fin.ext_iff, BraidGroup.val_strandSucc, Fin.val_castSucc, Fin.val_last]
    omega
  simp only [burauCol_apply, h1, h2, ite_false, sub_zero]

private theorem burauRow_last_castSucc (c : Fin (n + 1)) :
    burauRow R (n := n + 2) (Fin.last n) c.castSucc = if c = Fin.last n then 1 else 0 := by
  have hc := c.isLt
  have h1 : (c.castSucc = BraidGroup.strand (n := n + 2) (Fin.last n)) ↔ c = Fin.last n := by
    simp only [Fin.ext_iff, BraidGroup.val_strand, Fin.val_castSucc, Fin.val_last]
  have h2 : ¬ c.castSucc = BraidGroup.strandSucc (n := n + 2) (Fin.last n) := by
    simp only [Fin.ext_iff, BraidGroup.val_strandSucc, Fin.val_castSucc, Fin.val_last]
    omega
  simp only [burauRow_apply, h1, h2, ite_false, sub_zero]

/-! ### The two vectors annihilating `burau b - 1` -/

/-- The all-ones column vector is annihilated by `burau b - 1`. -/
theorem burau_sub_one_mulVec_one (t : Rˣ) (b : BraidGroup n) :
    ((burau n t b : Matrix (Fin n) (Fin n) R) - 1) *ᵥ (1 : Fin n → R) = 0 := by
  rw [Matrix.sub_mulVec, burau_mulVec_one, Matrix.one_mulVec, sub_self]

/-- The geometric row vector `(1, t, …, t ^ (n - 1))` annihilates `burau b - 1`. -/
theorem geom_vecMul_burau_sub_one (t : Rˣ) (b : BraidGroup n) :
    (fun k : Fin n => (t : R) ^ (k : ℕ)) ᵥ* ((burau n t b : Matrix (Fin n) (Fin n) R) - 1) = 0 := by
  rw [Matrix.vecMul_sub, vecMul_burau_geom, Matrix.vecMul_one, sub_self]

/-- **The matrix `burau b - 1` is singular.** Its determinant vanishes because the all-ones vector
is in its kernel. -/
theorem det_burau_sub_one (t : Rˣ) (b : BraidGroup (n + 1)) :
    ((burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1).det = 0 :=
  Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (burau_sub_one_mulVec_one t b)
    (i := 0) (by simp)

/-! ### Adding a strand and crossing it once -/

/-- The Burau matrix of a stabilised braid, with its last row and column deleted. The elementary
matrix of the new crossing enters only through the scalar `k`, which is `t` for the positive
crossing and `1` for the negative one. -/
private theorem submatrix_burau_strandIncl_mul (t : Rˣ) (b : BraidGroup (n + 1)) (k : R)
    (S : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hS : ∀ c v : Fin (n + 1), S c.castSucc v.castSucc =
      (if c = v then 1 else 0) -
        k * (if c = Fin.last n then 1 else 0) * (if v = Fin.last n then 1 else 0)) :
    (((burau (n + 2) t (BraidGroup.strandIncl b) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) R) * S) - 1).submatrix Fin.castSucc Fin.castSucc =
      ((burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1).updateCol (Fin.last n)
        (fun u => (1 - k) * (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
          u (Fin.last n) - (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) u) := by
  have hPb : ∀ x y : Fin (n + 1),
      (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
          x.castSucc y.castSucc =
        (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) x y := fun x y =>
    congrFun (congrFun (submatrix_burau_strandIncl t b) x) y
  have hcol : (burau (n + 2) t (BraidGroup.strandIncl b) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) R).col (Fin.last (n + 1)) =
      Pi.single (Fin.last (n + 1)) 1 := by
    rw [← Matrix.mulVec_single_one]
    exact burau_strandIncl_mulVec_single t b
  have hentry : ∀ i : Fin (n + 2),
      (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R) i
          (Fin.last (n + 1)) = (Pi.single (Fin.last (n + 1)) 1 : Fin (n + 2) → R) i :=
    fun i => congrFun hcol i
  have hlast : ∀ x : Fin (n + 1),
      (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
        x.castSucc (Fin.last (n + 1)) = 0 := fun x => by
    rw [hentry, Pi.single_eq_of_ne (Fin.castSucc_lt_last x).ne]
  ext u v
  have hsum : ∑ c : Fin (n + 1),
      (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) u c *
        ((if c = v then (1 : R) else 0) - k * (if c = Fin.last n then 1 else 0) *
          (if v = Fin.last n then 1 else 0)) =
      (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) u v -
        k * (if v = Fin.last n then 1 else 0) *
          (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) u (Fin.last n) := by
    have hexp : ∀ c : Fin (n + 1),
        (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) u c *
          ((if c = v then (1 : R) else 0) - k * (if c = Fin.last n then 1 else 0) *
            (if v = Fin.last n then 1 else 0)) =
        (if c = v then (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) u c else 0) -
          (if c = Fin.last n then k * (if v = Fin.last n then 1 else 0) *
            (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) u c else 0) := by
      intro c
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun c _ => hexp c, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ v, Finset.sum_ite_eq' Finset.univ (Fin.last n)]
    simp
  rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hlast,
    zero_mul, add_zero]
  simp only [hPb, hS, Matrix.one_apply, Fin.castSucc_inj]
  rw [hsum]
  rcases eq_or_ne v (Fin.last n) with rfl | hv
  · rw [Matrix.updateCol_self]
    simp only [Pi.single_apply, ite_true]
    ring
  · rw [Matrix.updateCol_ne hv, Matrix.sub_apply, Matrix.one_apply]
    simp only [hv, ite_false, mul_zero, zero_mul, sub_zero]

/-! ### The two-strand braids -/

private theorem burauMatrix_two (t : R) : burauMatrix (n := 2) t 0 = !![1 - t, t; 1, 0] := by
  have h0 : BraidGroup.strand (n := 2) 0 = 0 := by
    simp [Fin.ext_iff]
  have h1 : BraidGroup.strandSucc (n := 2) 0 = 1 := by
    simp [Fin.ext_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burauMatrix_apply, burauCol_apply, burauRow_apply, h0, h1]

private theorem burauMatrix_two_pow_three_apply (t : R) :
    (burauMatrix (n := 2) t 0 ^ 3) 0 0 = (1 - t) * (1 + t ^ 2) := by
  rw [pow_succ, pow_succ, pow_one, burauMatrix_two]
  simp only [Matrix.mul_fin_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

end KnotTheory

namespace MarkovBraid

/-- **The Alexander polynomial of the closure of a braid**, computed from the unreduced Burau
representation: the determinant of `burau b - 1` with its last row and last column deleted.

The value depends on the braid, not only on its closure, but only up to a unit of `R`;
`TauCeti.MarkovEquiv.associated_burauAlexander` is the precise statement. Over `R = ℤ[T;T⁻¹]` at
`t = T` the units are `± T ^ k`, which is the classical indeterminacy of the Alexander polynomial,
and `TauCeti.KnotTheory.associated_burauAlexander_alexander_trefoilSeifertMatrix` checks the
normalisation against the Seifert-matrix route on the trefoil. -/
def burauAlexander (β : MarkovBraid) (t : Rˣ) : R :=
  (((burau (β.predStrands + 1) t β.braid :
      Matrix (Fin (β.predStrands + 1)) (Fin (β.predStrands + 1)) R) - 1).submatrix
    Fin.castSucc Fin.castSucc).det

/-- The Burau–Alexander invariant is the corner minor of `burau β.braid - 1`. -/
theorem burauAlexander_def (β : MarkovBraid) (t : Rˣ) :
    burauAlexander (R := R) β t =
      (((burau (β.predStrands + 1) t β.braid :
          Matrix (Fin (β.predStrands + 1)) (Fin (β.predStrands + 1)) R) - 1).submatrix
        Fin.castSucc Fin.castSucc).det :=
  (rfl)

/-- On one strand there is nothing to delete: the corner minor of a `1 × 1` matrix is the empty
determinant. Informally, the closure of the trivial one-strand braid is the unknot. -/
@[simp]
theorem burauAlexander_one_strand (t : Rˣ) (b : BraidGroup 1) :
    burauAlexander (R := R) ⟨0, b⟩ t = 1 :=
  by rw [burauAlexander_def, Matrix.det_fin_zero]

/-- **Markov move I leaves the invariant unchanged.** Passing from `b` to `c * b * c⁻¹` conjugates
`burau b - 1` by `burau c`, which fixes both of the vectors annihilating it, so
`Matrix.det_submatrix_castSucc_conj` applies. -/
theorem burauAlexander_conj (t : Rˣ) (b c : BraidGroup (n + 1)) :
    burauAlexander (R := R) ⟨n, c * b * c⁻¹⟩ t = burauAlexander (R := R) ⟨n, b⟩ t := by
  have hinv : (burau (n + 1) t c : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
      (burau (n + 1) t c⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = 1 := by
    rw [map_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hnonsing : (burau (n + 1) t c : Matrix (Fin (n + 1)) (Fin (n + 1)) R)⁻¹ =
      (burau (n + 1) t c⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
    Matrix.inv_eq_right_inv hinv
  have hconj : (burau (n + 1) t (c * b * c⁻¹) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1 =
      (burau (n + 1) t c : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
        ((burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *
        (burau (n + 1) t c : Matrix (Fin (n + 1)) (Fin (n + 1)) R)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hnonsing, hinv, map_mul, map_mul,
      Units.val_mul, Units.val_mul]
  rw [burauAlexander_def, burauAlexander_def, hconj]
  exact Matrix.det_submatrix_castSucc_conj _ _ (burau_sub_one_mulVec_one t b)
    (geom_vecMul_burau_sub_one t b) (burau_mulVec_one t c) (vecMul_burau_geom t c)
    (Matrix.isUnit_iff_isUnit_det _ |>.mp (burau (n + 1) t c).isUnit) (by simp)
    (by simpa using t.isUnit.pow n)

/-- **Markov move II, positive stabilization, multiplies the invariant by `-t`.** -/
theorem burauAlexander_stabilize (t : Rˣ) (b : BraidGroup (n + 1)) :
    burauAlexander (R := R) ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ t =
      -(t : R) * burauAlexander (R := R) ⟨n, b⟩ t := by
  have hS : ∀ c v : Fin (n + 1),
      burauMatrix (n := n + 2) (t : R) (Fin.last n) c.castSucc v.castSucc =
        (if c = v then 1 else 0) - (t : R) * (if c = Fin.last n then 1 else 0) *
          (if v = Fin.last n then 1 else 0) := by
    intro c v
    rw [burauMatrix_apply, burauCol_last_castSucc, burauRow_last_castSucc]
    simp only [Fin.castSucc_inj]
    split_ifs <;> ring
  have hmul : (burau (n + 2) t (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) R) =
      (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R) *
        burauMatrix (t : R) (Fin.last n) := by
    rw [map_mul, Units.val_mul, burau_sigma, coe_burauGL]
  rw [burauAlexander_def, burauAlexander_def, hmul,
    submatrix_burau_strandIncl_mul t b (t : R) _ hS,
    Matrix.det_updateCol_last_smul_col_sub_single_of_det_sub_one_eq_zero _
      (det_burau_sub_one t b) (1 - (t : R))]
  ring

/-- **Markov move II, negative stabilization, multiplies the invariant by `-1`.** -/
theorem burauAlexander_stabilizeInv (t : Rˣ) (b : BraidGroup (n + 1)) :
    burauAlexander (R := R)
        ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ t =
      -burauAlexander (R := R) ⟨n, b⟩ t := by
  have hS : ∀ c v : Fin (n + 1),
      (burauMatrix (n := n + 2) (t : R) (Fin.last n))⁻¹ c.castSucc v.castSucc =
        (if c = v then 1 else 0) - (1 : R) * (if c = Fin.last n then 1 else 0) *
          (if v = Fin.last n then 1 else 0) := by
    intro c v
    rw [inv_burauMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      burauCol_last_castSucc, burauRow_last_castSucc, Matrix.one_apply]
    simp only [Fin.castSucc_inj, smul_eq_mul]
    split_ifs <;> simp [Units.inv_mul]
  have hmul : (burau (n + 2) t (BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹) :
      Matrix (Fin (n + 2)) (Fin (n + 2)) R) =
      (burau (n + 2) t (BraidGroup.strandIncl b) : Matrix (Fin (n + 2)) (Fin (n + 2)) R) *
        (burauMatrix (t : R) (Fin.last n))⁻¹ := by
    rw [map_mul, Units.val_mul, map_inv, Matrix.coe_units_inv, burau_sigma, coe_burauGL]
  rw [burauAlexander_def, burauAlexander_def, hmul,
    submatrix_burau_strandIncl_mul t b (1 : R) _ hS,
    Matrix.det_updateCol_last_smul_col_sub_single_of_det_sub_one_eq_zero _
      (det_burau_sub_one t b) (1 - (1 : R))]
  ring

/-- **The Burau-Alexander polynomial of the closure of the three-fold crossing on two strands**,
whose closure is the right-handed trefoil. Over `ℤ[T;T⁻¹]` at `t = T` this is `-T ^ 2` times the
Conway-normalised Alexander polynomial `T - 1 + T⁻¹` of the trefoil. -/
theorem burauAlexander_sigma_pow_three (t : Rˣ) :
    burauAlexander (R := R) ⟨1, BraidGroup.sigma 0 ^ 3⟩ t =
      -(t : R) * ((t : R) ^ 2 - (t : R) + 1) := by
  have hm : (burau 2 t (BraidGroup.sigma 0 ^ 3) : Matrix (Fin 2) (Fin 2) R) =
      burauMatrix (t : R) 0 ^ 3 := by
    rw [map_pow, burau_sigma, Units.val_pow_eq_pow_val, coe_burauGL]
  rw [burauAlexander_def, hm, Matrix.det_fin_one, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.one_apply]
  have hcast : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := rfl
  rw [hcast, burauMatrix_two_pow_three_apply]
  simp only [ite_true]
  ring

/-- On the integers at `t = -1` the invariant of the trefoil braid is `3`, matching the
determinant `3` of the trefoil. -/
theorem burauAlexander_sigma_pow_three_neg_one :
    burauAlexander (R := ℤ) ⟨1, BraidGroup.sigma 0 ^ 3⟩ (-1) = 3 := by
  rw [burauAlexander_sigma_pow_three]
  norm_num

end MarkovBraid

/-- A single Markov move changes the Burau-Alexander invariant only by a unit. -/
theorem IsMarkovMove.associated_burauAlexander {β γ : MarkovBraid} (h : IsMarkovMove β γ)
    (t : Rˣ) : Associated (β.burauAlexander t) (γ.burauAlexander t) := by
  induction h with
  | conj b c => rw [MarkovBraid.burauAlexander_conj]
  | stabilize b =>
    refine Associated.symm ⟨-t, ?_⟩
    rw [MarkovBraid.burauAlexander_stabilize, Units.val_neg]
    ring
  | stabilizeInv b =>
    refine Associated.symm ⟨-1, ?_⟩
    rw [MarkovBraid.burauAlexander_stabilizeInv, Units.val_neg, Units.val_one]
    ring

/-- **The Burau-Alexander polynomial is a Markov invariant, up to a unit.** By Markov's theorem
this says that it is an invariant of the oriented link obtained by closing the braid; over
`ℤ[T;T⁻¹]` the units are `± T ^ k`, which is exactly the classical indeterminacy of the Alexander
polynomial. -/
theorem MarkovEquiv.associated_burauAlexander {β γ : MarkovBraid} (h : MarkovEquiv β γ) (t : Rˣ) :
    Associated (β.burauAlexander t) (γ.burauAlexander t) :=
  h.induction (fun hmove => hmove.associated_burauAlexander t) (fun _ => Associated.refl _)
    (fun _ ih => ih.symm) (fun _ _ ih ih' => ih.trans ih')

/-- **The trefoil braid is not Markov equivalent to the trivial one-strand braid.** Both closures
have one component, so `TauCeti.MarkovEquiv.componentCount_eq` cannot separate them; the
Burau-Alexander invariant can, taking the values `3` and `1` over `ℤ` at `t = -1`, which are not
associated. Informally, the trefoil is not the unknot. -/
theorem not_markovEquiv_sigma_pow_three_one :
    ¬ MarkovEquiv ⟨1, BraidGroup.sigma 0 ^ 3⟩ ⟨0, 1⟩ := fun h => by
  have hassoc := h.associated_burauAlexander (R := ℤ) (-1)
  rw [MarkovBraid.burauAlexander_sigma_pow_three_neg_one,
    MarkovBraid.burauAlexander_one_strand] at hassoc
  have h3 : (3 : ℤ) = 1 ∨ (3 : ℤ) = -1 := Int.isUnit_iff.mp (associated_one_iff_isUnit.mp hassoc)
  omega

namespace KnotTheory

open LaurentPolynomial

/-- **The Burau route and the Seifert-matrix route to the Alexander polynomial agree on the
trefoil.** The braid `σ₀ ^ 3` closes to the right-handed trefoil, and
`TauCeti.KnotTheory.trefoilSeifertMatrix` is a Seifert matrix of that knot; the two invariants
agree up to the unit `-T ^ (-2)` of `ℤ[T;T⁻¹]`, which is the exact indeterminacy that
`TauCeti.MarkovEquiv.associated_burauAlexander` allows. -/
theorem associated_burauAlexander_alexander_trefoilSeifertMatrix :
    Associated (MarkovBraid.burauAlexander (R := ℤ[T;T⁻¹]) ⟨1, BraidGroup.sigma 0 ^ 3⟩
      (isUnit_T 1).unit) (alexander trefoilSeifertMatrix) := by
  have hTT : (T (-1) : ℤ[T;T⁻¹]) * T 1 = 1 := by
    have hnegadd : (-1 : ℤ) + 1 = 0 := by norm_num
    rw [← T_add, hnegadd, T_zero]
  have hsq : (T (-1) : ℤ[T;T⁻¹]) * (T 1) ^ 2 = T 1 := by
    rw [sq, ← mul_assoc, hTT, one_mul]
  have hmul : (T 1 : ℤ[T;T⁻¹]) * T (-2) = T (-1) := by
    have hadd : (1 : ℤ) + -2 = -1 := by norm_num
    rw [← T_add, hadd]
  refine ⟨-(isUnit_T (R := ℤ) (-2)).unit, ?_⟩
  rw [MarkovBraid.burauAlexander_sigma_pow_three, IsUnit.unit_spec, Units.val_neg,
    IsUnit.unit_spec, alexander_trefoilSeifertMatrix]
  calc -(T 1 : ℤ[T;T⁻¹]) * ((T 1) ^ 2 - T 1 + 1) * -T (-2)
      = (T 1 * T (-2)) * ((T 1) ^ 2 - T 1 + 1) := by ring
    _ = T (-1) * ((T 1) ^ 2 - T 1 + 1) := by rw [hmul]
    _ = T 1 - 1 + T (-1) := by
        rw [mul_add, mul_sub, hsq, hTT, mul_one]

end KnotTheory

end TauCeti
