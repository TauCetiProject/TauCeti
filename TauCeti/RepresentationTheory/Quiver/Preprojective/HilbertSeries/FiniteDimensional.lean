/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.ZigzagCartan

/-!
# Hilbert series of finite-dimensional preprojective algebras

Let `Q` be a finite quiver with at least one vertex, `Π = Π_k(Q)` its preprojective algebra over a
field `k`, `H` its matrix Hilbert series (`TauCeti.preprojectiveHilbertSeries`) and `A` the
arrow-count matrix of the doubled quiver, `A_{v,w} = #(w ⟶ v)`. Write `M = (1 + X²) I - X A`, a
matrix of formal power series which is invertible because its constant term is `I`. When `Π` is
finite-dimensional, its graded corners `e_j Π_n e_i` vanish in all large degrees, so the entries of
`H` are polynomials. This file proves that then

* `M H ≠ I`, so the Koszul complex of some vertex module is not exact at its left end: some nonzero
  `y ∈ e_v Π` is killed by the reverse `b*` of every arrow `b` of the doubled quiver into `v`;
* the inverse `M⁻¹` has a negative coefficient.

Both statements rest on one observation: when `Q` is nonempty, no matrix `N` whose entries are
polynomials satisfies `M N = I`. Indeed the coefficient matrices of such an `N` satisfy
`N_{n+2} = A N_{n+1} - N_n`, so if they vanish from some degree on, then they vanish in every degree
by descending induction, against `N_0 = I`. For the second statement, the Koszul defect formula
gives `M H = I + D` where `D` has nonnegative coefficients
(`TauCeti.coeff_one_le_coeff_mul_preprojectiveHilbertSeries`). If every coefficient of `M⁻¹` were
nonnegative, then `H = M⁻¹ + M⁻¹ D` would bound `M⁻¹` coefficientwise, so `M⁻¹` would be a matrix
of polynomials.

For a finite simple graph `G` without isolated vertices, `M` is the zigzag graded Cartan matrix
`C_G(q) = (1 + q²) I + q A_G` at `q = -X`
(`TauCeti.zigzagGradedCartanMatrix_map_aeval_neg_X_eq_submatrix`). Hence `C_G(-X)⁻¹` has a negative
coefficient as soon as the preprojective algebra of one orientation of `G` is finite-dimensional,
which is the case for every finite simply-laced Dynkin diagram
(`TauCeti.finiteDimensional_preprojectiveAlgebra_of_isSimplyLaced`). This is the numerical
obstruction to the Koszulity of the zigzag algebras of these graphs: the inverse of the graded
Cartan matrix of a Koszul algebra at `q = -X` is the matrix Hilbert series of its Koszul dual, so it
has nonnegative coefficients. It contrasts with the graphs containing a cycle, for which
`H = C_G(-X)⁻¹` (`TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.NonTree`).

## Main results

* `TauCeti.exists_forall_le_preprojectiveCorner_eq_bot`: the graded corners of a finite-dimensional
  preprojective algebra vanish in all large degrees.
* `TauCeti.mul_preprojectiveHilbertSeries_ne_one`: for a finite-dimensional preprojective algebra of
  a nonempty quiver, `M H ≠ I`.
* `TauCeti.exists_ne_zero_forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero`: the Koszul complex of
  some vertex module is not exact at its left end.
* `TauCeti.exists_coeff_inv_lt_zero_of_finiteDimensional`: `M⁻¹` has a negative coefficient.
* `TauCeti.exists_coeff_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_lt_zero`: **`C_G(-X)⁻¹` has a
  negative coefficient** when the preprojective algebra of an orientation of `G` is
  finite-dimensional.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the Koszul complex and the Hilbert series.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  J. Amer. Math. Soc. 9 (1996), Lemma 2.11.1, for the Hilbert series of a Koszul algebra and its
  dual.
* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), for the preprojective algebras of Dynkin quivers as almost
  Koszul algebras.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra PowerSeries

universe u v w

/-- **No polynomial matrix is a right inverse of `(1 + X²) I - X A`** over a nonempty index type. If
`((1 + X²) I - X A) N = I` for a matrix `A` of natural numbers, and the coefficients of every entry
of `N` vanish from degree `d` on, then the index type is empty. -/
private theorem isEmpty_of_mul_eq_one_of_coeff_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℕ) {N : Matrix ι ι ℤ⟦X⟧}
    (hN : (((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix ι ι ℤ⟦X⟧) -
      (X : ℤ⟦X⟧) • Matrix.of fun v w => (A v w : ℤ⟦X⟧)) * N = 1)
    {d : ℕ} (hd : ∀ n, d ≤ n → ∀ i j, coeff n (N i j) = 0) : IsEmpty ι := by
  have happly (i j : ι) : ((((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix ι ι ℤ⟦X⟧) -
      (X : ℤ⟦X⟧) • Matrix.of fun v w => (A v w : ℤ⟦X⟧)) * N) i j =
        ((1 : ℤ⟦X⟧) + X ^ 2) * N i j - X * ∑ l, (A i l : ℤ⟦X⟧) * N l j := by
    rw [sub_mul]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.of_apply]
  -- The coefficients of `N` satisfy `N_{n+2} = A N_{n+1} - N_n`.
  have hrec (n : ℕ) (i j : ι) : coeff (n + 2) (N i j) + coeff n (N i j) =
      ∑ l, (A i l : ℤ) * coeff (n + 1) (N l j) := by
    have h := congrArg (fun P => coeff (n + 2) (P i j)) hN
    simp only [happly, Matrix.one_apply] at h
    have h0 : coeff (n + 2) (if i = j then (1 : ℤ⟦X⟧) else 0) = 0 := by
      split_ifs <;> simp [coeff_one]
    rw [h0, map_sub, add_mul, one_mul, map_add, coeff_X_pow_mul',
      ite_eq_left (by omega : 2 ≤ n + 2), Nat.add_sub_cancel, coeff_succ_X_mul, map_sum,
      sub_eq_zero] at h
    simpa only [coeff_natCast_mul] using h
  -- Descending induction from degree `d` kills every coefficient.
  have hzero : ∀ t n, d ≤ n + t → ∀ i j, coeff n (N i j) = 0 := by
    intro t
    induction t with
    | zero => exact fun n hn => hd n hn
    | succ t ih =>
      intro n hn i j
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h := hrec n i j
      simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add] at h
      exact h
  -- But the constant term of `N` is the identity matrix.
  refine ⟨fun i => ?_⟩
  have h := congrArg (fun P => constantCoeff (P i i)) hN
  simp only [happly, Matrix.one_apply_eq, map_sub, map_mul, map_add, map_one, map_pow,
    constantCoeff_X, zero_pow two_ne_zero, add_zero, one_mul, zero_mul, sub_zero] at h
  rw [← coeff_zero_eq_constantCoeff_apply, hzero d 0 (by omega)] at h
  exact zero_ne_one h

section Quiver

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The graded corners of a finite-dimensional preprojective algebra vanish in large degrees**:
there is a degree `d` with `e_j Π_n e_i = 0` for all `n ≥ d` and all vertices `i` and `j`. -/
theorem exists_forall_le_preprojectiveCorner_eq_bot
    [FiniteDimensional k (preprojectiveAlgebra k Q)] :
    ∃ d, ∀ n, d ≤ n → ∀ i j : Symmetrify Q, preprojectiveCorner k Q n i j = ⊥ := by
  obtain ⟨d, hd⟩ := (WellFoundedGT.finite_ne_bot_of_iSupIndep
    (isInternal_preprojectiveGrade k Q).submodule_iSupIndep).bddAbove
  refine ⟨d + 1, fun n hn i j => eq_bot_iff.2 ?_⟩
  rw [preprojectiveCorner_eq_cornerSubmodule_inf_preprojectiveGrade]
  refine inf_le_right.trans (le_of_eq ?_)
  by_contra h
  exact absurd (hd h) (by omega)

/-- The entries of the matrix Hilbert series of a finite-dimensional preprojective algebra are
polynomials. -/
private theorem exists_forall_le_coeff_preprojectiveHilbertSeries_eq_zero
    [FiniteDimensional k (preprojectiveAlgebra k Q)] :
    ∃ d, ∀ n, d ≤ n → ∀ j i, coeff n (preprojectiveHilbertSeries k Q j i) = 0 := by
  obtain ⟨d, hd⟩ := exists_forall_le_preprojectiveCorner_eq_bot k Q
  exact ⟨d, fun n hn j i => by
    rw [coeff_preprojectiveHilbertSeries, hd n hn, finrank_bot, Nat.cast_zero]⟩

variable [DecidableEq Q] [Nonempty Q]

/-- **The Hilbert series identity fails for a finite-dimensional preprojective algebra.** If `Q`
has a vertex, `A_{v,w} = #(w ⟶ v)` is the arrow-count matrix of the doubled quiver and `Π` is
finite-dimensional, then its matrix Hilbert series `H` satisfies `((1 + X²) I - X A) H ≠ I`. -/
theorem mul_preprojectiveHilbertSeries_ne_one [FiniteDimensional k (preprojectiveAlgebra k Q)] :
    (((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧)) *
        preprojectiveHilbertSeries k Q ≠ 1 := fun h => by
  obtain ⟨d, hd⟩ := exists_forall_le_coeff_preprojectiveHilbertSeries_eq_zero k Q
  exact not_isEmpty_of_nonempty Q (isEmpty_of_mul_eq_one_of_coeff_eq_zero _ h hd)

omit [DecidableEq Q] in
/-- **The Koszul complex of a finite-dimensional preprojective algebra is not exact at its left
end.** If `Q` has a vertex and `Π` is finite-dimensional, then at some vertex `v` there is a nonzero
`y ∈ e_v Π` killed by the reverse `b*` of every arrow `b` of the doubled quiver into `v`: the
left-hand map `y ↦ (ε_b b* y)_b` of the Koszul complex of the vertex module `S_v` is not
injective. -/
theorem exists_ne_zero_forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero
    [FiniteDimensional k (preprojectiveAlgebra k Q)] :
    ∃ (v : Q) (y : preprojectiveAlgebra k Q),
      preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y ∧
        (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
          preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) ∧ y ≠ 0 := by
  classical
  by_contra! h
  exact mul_preprojectiveHilbertSeries_ne_one k Q
    ((mul_preprojectiveHilbertSeries_eq_one_iff k Q).2 h)

/-- **The inverse of `(1 + X²) I - X A` has a negative coefficient** when `Q` has a vertex and its
preprojective algebra is finite-dimensional, for `A_{v,w} = #(w ⟶ v)` the arrow-count matrix of the
doubled quiver. The inverse is taken in the ring of matrices of formal power series over `ℤ`. -/
theorem exists_coeff_inv_lt_zero_of_finiteDimensional
    [FiniteDimensional k (preprojectiveAlgebra k Q)] :
    ∃ n v i, coeff n ((((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧))⁻¹ v i) < 0 := by
  set M : Matrix Q Q ℤ⟦X⟧ := ((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
    (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
      (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧) with hM
  set H : Matrix Q Q ℤ⟦X⟧ := preprojectiveHilbertSeries k Q
  by_contra! hpos
  -- `M` is invertible, since its constant term is the identity matrix.
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det]
    convert isUnit_one
    rw [RingHom.mapMatrix_apply, ← Matrix.det_one (n := Q) (R := ℤ)]
    congr 1
    ext v w
    simp [hM, Matrix.one_apply, apply_ite]
  -- Write `M H = I + D`; the Koszul defect `D` has nonnegative coefficients.
  have hD (n : ℕ) (l i : Q) : 0 ≤ coeff n ((M * H - 1) l i) := by
    rw [Matrix.sub_apply, map_sub, sub_nonneg]
    exact coeff_one_le_coeff_mul_preprojectiveHilbertSeries k Q n l i
  -- Hence `H = M⁻¹ + M⁻¹ D` bounds `M⁻¹` coefficientwise.
  have hle (n : ℕ) (v i : Q) : coeff n (M⁻¹ v i) ≤ coeff n (H v i) := by
    have hH : H = M⁻¹ + M⁻¹ * (M * H - 1) := by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdet, Matrix.mul_one,
        add_sub_cancel]
    rw [hH, Matrix.add_apply, map_add, le_add_iff_nonneg_right, Matrix.mul_apply, map_sum]
    refine Finset.sum_nonneg fun l _ => ?_
    rw [coeff_mul]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hpos _ _ _) (hD _ _ _)
  -- So `M⁻¹` is a polynomial right inverse of `M`, which is impossible.
  obtain ⟨d, hd⟩ := exists_forall_le_coeff_preprojectiveHilbertSeries_eq_zero k Q
  have hN (n : ℕ) (hn : d ≤ n) (v i : Q) : coeff n (M⁻¹ v i) = 0 :=
    le_antisymm ((hle n v i).trans (hd n hn v i).le) (hpos n v i)
  exact not_isEmpty_of_nonempty Q
    (isEmpty_of_mul_eq_one_of_coeff_eq_zero _ (Matrix.mul_nonsing_inv M hdet) hN)

end Quiver

section Graph

open DoubledQuiver

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [Nonempty V]

/-- **The inverse zigzag Cartan matrix at `q = -X` has a negative coefficient** for a graph with a
finite-dimensional preprojective algebra. Let `G` be a nonempty finite simple graph without isolated
vertices, and let the preprojective algebra of some orientation `o` of `G` be finite-dimensional.
Then the inverse of the zigzag graded Cartan matrix `C_G(q) = (1 + q²) I + q A_G` evaluated at
`q = -X`, taken in the ring of matrices of formal power series over `ℤ`, has a negative
coefficient. -/
theorem exists_coeff_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_lt_zero
    (hns : ∀ i : V, ∃ j, G.Adj i j) (o : Orientation G)
    [FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o))] :
    ∃ n v w, coeff n (((zigzagGradedCartanMatrix k G).map
      (Polynomial.aeval (-X : ℤ⟦X⟧)))⁻¹ v w) < 0 := by
  classical
  have : Nonempty (OrientedQuiver G o) := (OrientedQuiver.vertexEquiv G o).symm.nonempty
  obtain ⟨n, v, i, h⟩ := exists_coeff_inv_lt_zero_of_finiteDimensional k (OrientedQuiver G o)
  rw [zigzagGradedCartanMatrix_map_aeval_neg_X_eq_submatrix k o hns, Matrix.inv_submatrix_equiv]
  refine ⟨n, (OrientedQuiver.vertexEquiv G o).symm v, (OrientedQuiver.vertexEquiv G o).symm i, ?_⟩
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using h

end Graph

end TauCeti
