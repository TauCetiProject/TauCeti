/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Binary
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass
public import TauCeti.RingTheory.Henselian.BinaryForm

/-!
# Unimodular diagonal forms over Henselian local rings

Over a Henselian local ring with finite residue field and with two invertible, diagonal forms
with unit coefficients are classified by their rank and their determinant modulo unit squares.
In positive rank, every such form is isometric to the form with all coefficients equal to one
except for the last, which is the product of the original coefficients.

The binary representation normal form supplies the elementary integral changes of basis: every
binary unit form represents one, so `⟨a, b⟩` is isometric to `⟨1, a * b⟩`. Iterating these changes
uses the existing diagonal-chain API. In particular, the equivalences are over the coefficient ring,
rather than merely over its fraction field.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open QuadraticMap

namespace TauCeti

variable {R : Type*} [CommRing R] [HenselianLocalRing R]
  [Finite (IsLocalRing.ResidueField R)]

/-- A binary form with unit coefficients over a finite-residue Henselian local ring with two
invertible is isometric, integrally, to `⟨1, a * b⟩`. -/
theorem equivalent_binary_one_mul_of_isUnit_two (h2 : IsUnit (2 : R)) (a b : Rˣ) :
    (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(1 : R), (a * b : Rˣ)]) := by
  obtain ⟨x, y, hxy⟩ := exists_mul_sq_add_mul_sq_eq_of_isUnit h2 a.isUnit b.isUnit isUnit_one
  have h : (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![((1 : Rˣ) : R), (a : R) * (b : R) * (1 : Rˣ)]) :=
    ⟨(isometryEquivBinaryNormalForm (a : R) (b : R) x y 1 hxy).symm⟩
  simpa only [Units.val_one, mul_one, Units.val_mul] using h

/-- The elementary binary changes of basis reduce a positive-rank unit diagonal form to ones
followed by its determinant. -/
private theorem diagonalChain_snoc_prod_of_isUnit_two (h2 : IsUnit (2 : R)) {n : ℕ}
    (w : Fin (n + 1) → Rˣ) :
    DiagonalChain w (Fin.snoc (fun _ : Fin n ↦ 1) (∏ i, w i)) := by
  induction n with
  | zero =>
      convert DiagonalChain.refl w using 1
      ext i
      fin_cases i
      simp [Fin.snoc]
  | succ n ih =>
      let v : Fin (n + 1) → Rˣ := Fin.cons (w 0 * w 1) (fun i ↦ w i.succ.succ)
      have hs : BinaryStep w (Fin.cons 1 v) := by
        refine BinaryStep.of_pair 0 1 (by simp) ?_ ?_
        · intro k hk0 hk1
          revert hk0 hk1
          refine Fin.cases (by simp) (fun j ↦ ?_) k
          refine Fin.cases (by simp) (fun j _ _ ↦ by simp [v]) j
        · simpa [v] using equivalent_binary_one_mul_of_isUnit_two h2 (w 0) (w 1)
      have hp : (∏ i, v i) = ∏ i, w i := by
        simp [v, Fin.prod_univ_succ, mul_assoc]
      refine (DiagonalChain.binary hs).trans ?_
      convert (ih v).cons 1 using 1
      rw [Fin.cons_snoc_eq_snoc_cons, hp]
      congr 1
      ext i
      refine Fin.cases (by simp) (fun j ↦ by simp) i

/-- A positive-rank unit diagonal form over a finite-residue Henselian local ring with two
invertible is isometric to ones followed by its determinant. -/
theorem equivalent_weightedSumSquares_snoc_prod_of_isUnit_two (h2 : IsUnit (2 : R)) {n : ℕ}
    (w : Fin (n + 1) → Rˣ) :
    (weightedSumSquares R w).Equivalent
      (weightedSumSquares R (Fin.snoc (fun _ : Fin n ↦ (1 : Rˣ)) (∏ i, w i))) := by
  simpa only [weightedSumSquares_units] using
    (diagonalChain_snoc_prod_of_isUnit_two h2 w).equivalent

/-- Two unit diagonal forms of the same rank over a finite-residue Henselian local ring with
two invertible are isometric exactly when their determinants agree modulo unit squares. -/
theorem equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
    (h2 : IsUnit (2 : R)) {n : ℕ} (w v : Fin n → Rˣ) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R v) ↔
      IsSquare ((∏ i, w i) * ∏ i, v i) := by
  let := h2.invertible
  refine ⟨isSquare_prod_mul_prod_of_equivalent, fun h ↦ ?_⟩
  cases n with
  | zero =>
      have hv : w = v := Subsingleton.elim _ _
      rw [hv]
  | succ n =>
      refine (equivalent_weightedSumSquares_snoc_prod_of_isUnit_two h2 w).trans
        ((equivalent_weightedSumSquares_of_isSquare_div ?_).trans
          (equivalent_weightedSumSquares_snoc_prod_of_isUnit_two h2 v).symm)
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [div_eq_mul_inv, pow_two, mul_assoc] using h.div (IsSquare.sq (∏ i, v i))
      · simp

private theorem equivalent_weightedSumSquares_subtype_of_isSquare_prod_mul_prod
    (h2 : IsUnit (2 : R)) {ι S : Type*} [Fintype ι] [DecidableEq S]
    (k : ι → S) (u v : ι → Rˣ) (m : S)
    (hm : IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i)) :
    (weightedSumSquares R fun i : {i : ι // k i = m} ↦ (u i.1 : R)).Equivalent
      (weightedSumSquares R fun i : {i : ι // k i = m} ↦ (v i.1 : R)) := by
  classical
  let ef := (Fintype.equivFin {i : ι // k i = m}).symm
  have heq := (equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two h2
    (fun j ↦ u (ef j).1) (fun j ↦ v (ef j).1)).mpr <| by
      rw [ef.prod_comp (fun x : {i : ι // k i = m} ↦ u x.1),
        ef.prod_comp (fun x : {i : ι // k i = m} ↦ v x.1),
        ← Finset.prod_subtype {i | k i = m} (by simp) u,
        ← Finset.prod_subtype {i | k i = m} (by simp) v]
      exact hm
  rw [weightedSumSquares_units, weightedSumSquares_units] at heq
  exact (equivalent_weightedSumSquares_comp (fun i : {i : ι // k i = m} ↦ (u i.1 : R)) ef).trans
    (heq.trans
      (equivalent_weightedSumSquares_comp (fun i : {i : ι // k i = m} ↦ (v i.1 : R)) ef).symm)

/-- Over a finite-residue Henselian local ring with two invertible, two diagonal forms with weights
`(u i : R) * c (k i)` and `(v i : R) * c (k i)` are isometric whenever at every level `m` the unit
products `∏_{k i = m} u i` and `∏_{k i = m} v i` differ by a square. -/
theorem equivalent_weightedSumSquares_mul_of_forall_isSquare_prod_mul_prod
    (h2 : IsUnit (2 : R)) {ι S : Type*} [Fintype ι] [DecidableEq S]
    (k : ι → S) (c : S → R) (u v : ι → Rˣ)
    (h : ∀ m, IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i)) :
    (weightedSumSquares R fun i ↦ (u i : R) * c (k i)).Equivalent
      (weightedSumSquares R fun i ↦ (v i : R) * c (k i)) := by
  classical
  let e := fun m ↦
    (equivalent_weightedSumSquares_subtype_of_isSquare_prod_mul_prod h2 k u v m (h m)).some
  let T : Finset S := Finset.univ.image k
  let σ : (Σ m : T, {i : ι // k i = m.1}) ≃ ι :=
    { toFun := fun p ↦ p.2.1
      invFun := fun i ↦ ⟨⟨k i, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩, ⟨i, rfl⟩⟩
      left_inv := fun ⟨⟨_, _⟩, ⟨_, hi⟩⟩ ↦ by cases hi; rfl
      right_inv := fun _ ↦ rfl }
  let C : (ι → R) ≃ₗ[R] (∀ m : T, {i : ι // k i = m.1} → R) :=
    (LinearEquiv.funCongrLeft R R σ).trans (LinearEquiv.piCurry R fun (_ : T) _ ↦ R)
  have heval (w : ι → Rˣ) (g : ∀ m : T, {i : ι // k i = m.1} → R) :
      weightedSumSquares R (fun i ↦ (w i : R) * c (k i)) (C.symm g) =
        ∑ m : T,
          c m.1 * weightedSumSquares R (fun i : {i : ι // k i = m.1} ↦ (w i.1 : R)) (g m) := by
    rw [weightedSumSquares_apply, ← σ.sum_comp, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [weightedSumSquares_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hval : C.symm g (σ ⟨m, i⟩) = g m i := by
      simp [C, LinearEquiv.piCurry_symm_apply]
      rfl
    have hσ : σ ⟨m, i⟩ = i.1 := rfl
    rw [hval, hσ, i.2]
    simp only [smul_eq_mul]
    ring
  refine ⟨{
    toLinearEquiv :=
      C.trans ((LinearEquiv.piCongrRight fun m : T ↦ (e m.1).toLinearEquiv).trans C.symm)
    map_app' := fun x ↦ ?_ }⟩
  -- Unfold the composite `LinearEquiv.trans` action on `x` so `heval` matches the outer `C.symm`.
  change weightedSumSquares R (fun i ↦ (v i : R) * c (k i))
      (C.symm (LinearEquiv.piCongrRight (fun m : T ↦ (e m.1).toLinearEquiv) (C x))) = _
  rw [heval v]
  have hstep :
      (∑ m : T, c m.1 * weightedSumSquares R (fun i : {i : ι // k i = m.1} ↦ (v i.1 : R))
          (LinearEquiv.piCongrRight (fun m : T ↦ (e m.1).toLinearEquiv) (C x) m)) =
        ∑ m : T, c m.1 * weightedSumSquares R (fun i : {i : ι // k i = m.1} ↦ (u i.1 : R))
          (C x m) :=
    Finset.sum_congr rfl fun m _ ↦ congrArg (c m.1 * ·) ((e m.1).map_app (C x m))
  rw [hstep, ← heval u (C x), C.symm_apply_apply]

end TauCeti
