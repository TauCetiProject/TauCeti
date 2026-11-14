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

/-- Two unit diagonal forms on the same finite index type over a finite-residue Henselian local
ring with two invertible are isometric exactly when their determinants agree modulo unit squares. -/
theorem equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
    (h2 : IsUnit (2 : R)) {ι : Type*} [Fintype ι] (w v : ι → Rˣ) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R v) ↔
      IsSquare ((∏ i, w i) * ∏ i, v i) := by
  let := h2.invertible
  refine ⟨isSquare_prod_mul_prod_of_equivalent, fun h ↦ ?_⟩
  rcases eq_or_ne (Fintype.card ι) 0 with hc | hc
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    rw [Subsingleton.elim w v]
  · obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
    let α : Fin (n + 1) ≃ ι := (Fintype.equivFinOfCardEq hn).symm
    have hcomp (u : ι → Rˣ) :
        (weightedSumSquares R u).Equivalent (weightedSumSquares R (u ∘ α)) := by
      rw [weightedSumSquares_units, weightedSumSquares_units]
      exact equivalent_weightedSumSquares_comp (fun i ↦ (u i : R)) α
    have hfin : IsSquare ((∏ j, (w ∘ α) j) * ∏ j, (v ∘ α) j) := by
      rwa [Function.comp_def, Equiv.prod_comp α w, Function.comp_def, Equiv.prod_comp α v]
    refine (hcomp w).trans <|
      (equivalent_weightedSumSquares_snoc_prod_of_isUnit_two h2 (w ∘ α)).trans
        ((equivalent_weightedSumSquares_of_isSquare_div ?_).trans
          ((equivalent_weightedSumSquares_snoc_prod_of_isUnit_two h2 (v ∘ α)).symm.trans
            (hcomp v).symm))
    intro i
    refine Fin.lastCases ?_ (fun _ ↦ by simp) i
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using hfin.div (IsSquare.sq (∏ j, (v ∘ α) j))

/-- Over a finite-residue Henselian local ring with two invertible, two diagonal forms
`∑ᵢ uᵢ s(kᵢ) xᵢ²` and `∑ᵢ vᵢ s(kᵢ) xᵢ²` sharing a scale profile `k : ι → α` are isometric over `R`
whenever the unit products `∏_{kᵢ = m} uᵢ` and `∏_{kᵢ = m} vᵢ` agree modulo unit squares on every
fiber `m : α`. -/
theorem equivalent_weightedSumSquares_mul_of_forall_fiber
    (h2 : IsUnit (2 : R)) {ι α : Type*} [Fintype ι] [DecidableEq α]
    (k : ι → α) (s : α → R) (u v : ι → Rˣ)
    (hfiber : ∀ m : α, IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v i)) :
    (weightedSumSquares R fun i ↦ (u i : R) * s (k i)).Equivalent
      (weightedSumSquares R fun i ↦ (v i : R) * s (k i)) := by
  classical
  let S : Finset α := Finset.univ.image k
  let κ : ι → S := fun i ↦ ⟨k i, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩
  let σ : (Σ m : S, {i : ι // κ i = m}) ≃ ι := Equiv.sigmaFiberEquiv κ
  have hstep (m : S) : (weightedSumSquares R fun i : {i : ι // κ i = m} ↦ u i.1).Equivalent
      (weightedSumSquares R fun i : {i : ι // κ i = m} ↦ v i.1) := by
    refine (equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two h2 _ _).mpr ?_
    have hsub (w : ι → Rˣ) : ∏ i : {i : ι // κ i = m}, w i.1 = ∏ i with k i = m.1, w i :=
      (Finset.prod_subtype {i : ι | k i = m.1} (fun i ↦ by simp [κ, Subtype.ext_iff]) w).symm
    rw [hsub u, hsub v]
    exact hfiber m.1
  let f := fun m : S ↦ Classical.choice (hstep m)
  let curry := LinearEquiv.piCurry R fun (m : S) (_ : {i : ι // κ i = m}) ↦ R
  let σEquiv : (ι → R) ≃ₗ[R] ((Σ m : S, {i : ι // κ i = m}) → R) :=
    LinearEquiv.funCongrLeft R R σ
  let E : (ι → R) ≃ₗ[R] (ι → R) :=
    σEquiv.trans (curry.trans ((LinearEquiv.piCongrRight fun m ↦ (f m).toLinearEquiv).trans
      (curry.symm.trans σEquiv.symm)))
  refine ⟨{ toLinearEquiv := E, map_app' := fun x ↦ ?_ }⟩
  simp only [weightedSumSquares_apply, smul_eq_mul]
  rw [← Equiv.sum_comp σ, ← Equiv.sum_comp σ, Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hf := (f m).map_app (fun j ↦ x (σ ⟨m, j⟩))
  simp only [weightedSumSquares_units, weightedSumSquares_apply, smul_eq_mul] at hf
  have hE (i : {i : ι // κ i = m}) : E x (σ ⟨m, i⟩) = f m (fun j ↦ x (σ ⟨m, j⟩)) i := by
    simp only [E, σEquiv, curry, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_symm,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, LinearEquiv.piCurry_apply,
      LinearEquiv.piCurry_symm_apply, Equiv.symm_apply_apply]
    rfl
  calc ∑ i : {i : ι // κ i = m},
          ((v (σ ⟨m, i⟩) : R) * s (k (σ ⟨m, i⟩))) * (E x (σ ⟨m, i⟩) * E x (σ ⟨m, i⟩))
      = s m.1 * ∑ i : {i : ι // κ i = m},
          (v i.1 : R) * (f m (fun j ↦ x (σ ⟨m, j⟩)) i * f m (fun j ↦ x (σ ⟨m, j⟩)) i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hE i]
        simp only [σ, Equiv.sigmaFiberEquiv_apply]
        rw [show k i.1 = m.1 from congrArg Subtype.val i.2]
        ring
    _ = s m.1 * ∑ i : {i : ι // κ i = m}, (u i.1 : R) * (x (σ ⟨m, i⟩) * x (σ ⟨m, i⟩)) := by
        rw [hf]
    _ = ∑ i : {i : ι // κ i = m},
          ((u (σ ⟨m, i⟩) : R) * s (k (σ ⟨m, i⟩))) * (x (σ ⟨m, i⟩) * x (σ ⟨m, i⟩)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [σ, Equiv.sigmaFiberEquiv_apply]
        rw [show k i.1 = m.1 from congrArg Subtype.val i.2]
        ring

end TauCeti
