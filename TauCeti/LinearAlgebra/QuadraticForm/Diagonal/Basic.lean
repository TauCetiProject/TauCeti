/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Determinant

/-!
# Diagonal quadratic forms

This file provides general infrastructure for diagonal quadratic forms expressed as weighted sums
of squares.

## Main results

* `TauCeti.equivalent_weightedSumSquares_comp`: reindexing the coefficients preserves equivalence.
* `TauCeti.equivalent_weightedSumSquares_of_pair`: a binary equivalence extends across fixed
  coordinates.
* `QuadraticMap.associated_weightedSumSquares`, `QuadraticForm.toMatrix'_weightedSumSquares`, and
  `QuadraticForm.discr'_weightedSumSquares`: over a ring in which two is invertible, the associated
  bilinear form of a diagonal form is the weighted dot product, its Gram matrix in the standard
  basis is the diagonal matrix of the weights, and its discriminant is their product.
* `QuadraticMap.weightedSumSquares_units`: unit weights may be replaced by the scalars they name.
* `QuadraticMap.not_anisotropic_weightedSumSquares_of_ternary_eq_zero`: a ternary solution with
  a nonzero third coordinate gives a nonzero isotropic vector in a diagonal form.
* `TauCeti.isSquare_prod_mul_prod_of_equivalent`: isometric diagonal forms with unit weights have
  weight products differing by a square.
-/

public section

namespace TauCeti

universe u v w

open QuadraticMap

section PairExtension

variable {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {w w' : ι → R} {i j : ι}

private def replacePair (f : (Fin 2 → R) → (Fin 2 → R)) (i j : ι)
    (x : ι → R) (k : ι) : R :=
  if k = i then f ![x i, x j] 0 else if k = j then f ![x i, x j] 1 else x k

omit [CommSemiring R] [Fintype ι] in
private theorem replacePair_apply_left (f : (Fin 2 → R) → (Fin 2 → R))
    (i j : ι) (x : ι → R) : replacePair f i j x i = f ![x i, x j] 0 := by
  simp [replacePair]

omit [CommSemiring R] [Fintype ι] in
private theorem replacePair_apply_right (f : (Fin 2 → R) → (Fin 2 → R))
    (hij : i ≠ j) (x : ι → R) : replacePair f i j x j = f ![x i, x j] 1 := by
  simp [replacePair, hij.symm]

omit [CommSemiring R] [Fintype ι] in
private theorem replacePair_comp (f g : (Fin 2 → R) → (Fin 2 → R))
    (hfg : Function.LeftInverse f g) (hij : i ≠ j) (x : ι → R) :
    replacePair f i j (replacePair g i j x) = x := by
  have finTwo_eta (v : Fin 2 → R) : ![v 0, v 1] = v := FinVec.etaExpand_eq v
  funext k
  by_cases hki : k = i
  · subst k
    simp only [replacePair_apply_left,
      replacePair_apply_right (f := g) (i := i) (j := j) hij]
    rw [finTwo_eta, hfg]
    rfl
  by_cases hkj : k = j
  · subst k
    simp only [replacePair_apply_right (f := f) (i := i) (j := j) hij,
      replacePair_apply_left, replacePair_apply_right (f := g) (i := i) (j := j) hij]
    rw [finTwo_eta, hfg]
    rfl
  · simp [replacePair, hki, hkj]

private def pairLinearEquiv (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j])) :
    (ι → R) ≃ₗ[R] (ι → R) where
  toFun := replacePair e i j
  invFun := replacePair e.symm i j
  left_inv := replacePair_comp e.symm e e.symm_apply_apply hij
  right_inv := replacePair_comp e e.symm e.apply_symm_apply hij
  map_add' x y := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_add e ![x i, x j] ![y i, y j]) 0
    by_cases hkj : k = j
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_add e ![x i, x j] ![y i, y j]) 1
    · simp [replacePair, hki, hkj]
  map_smul' a x := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_smul e a ![x i, x j]) 0
    by_cases hkj : k = j
    · subst k
      simpa [replacePair, hij, hij.symm] using
        congrFun (map_smul e a ![x i, x j]) 1
    · simp [replacePair, hki, hkj]

private def pairIsometryEquiv (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k = w' k) :
    (weightedSumSquares R w).IsometryEquiv (weightedSumSquares R w') where
  toLinearEquiv := pairLinearEquiv hij e
  map_app' x := by
    simp only [weightedSumSquares_apply]
    have sum_pair_add_rest (f : ι → R) :
        ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
      rw [← Finset.add_sum_erase _ f (Finset.mem_univ i),
        ← Finset.add_sum_erase _ f
          (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]
    rw [sum_pair_add_rest, sum_pair_add_rest]
    simp only [pairLinearEquiv]
    have hpair := e.map_app ![x i, x j]
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul] at hpair
    rw [replacePair_apply_left, replacePair_apply_right (f := e) (i := i) (j := j) hij x]
    simp only [smul_eq_mul]
    rw [hpair]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [replacePair, hki, hkj, hrest k hki hkj]

omit [DecidableEq ι] in
/-- Replacing two distinct coefficients by an equivalent binary form, while fixing all other
coefficients, produces an equivalent diagonal form. -/
theorem equivalent_weightedSumSquares_of_pair (hij : i ≠ j)
    (hpair : (weightedSumSquares R ![w i, w j]).Equivalent
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k = w' k) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R w') := by
  classical
  obtain ⟨e⟩ := hpair
  exact ⟨pairIsometryEquiv hij e hrest⟩

end PairExtension

variable {R : Type u} [CommSemiring R] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

/-- Reindexing the coefficients of a diagonal form does not change its equivalence class. -/
theorem equivalent_weightedSumSquares_comp (w : ι → R) (σ : κ ≃ ι) :
    (QuadraticMap.weightedSumSquares R w).Equivalent
      (QuadraticMap.weightedSumSquares R (w ∘ σ)) := by
  refine ⟨{
    toLinearEquiv := LinearEquiv.funCongrLeft R R σ
    map_app' := fun x => ?_ }⟩
  simp only [QuadraticMap.weightedSumSquares_apply, Function.comp_apply, smul_eq_mul]
  simpa using (Equiv.sum_comp σ.symm (fun i => w (σ i) * (x (σ i) * x (σ i)))).symm

/-- A diagonal form with unit weights is the diagonal form with the underlying scalar weights. -/
theorem _root_.QuadraticMap.weightedSumSquares_units (w : ι → Rˣ) :
    QuadraticMap.weightedSumSquares R w
      = QuadraticMap.weightedSumSquares R fun i => ((w i : R)) := by
  ext x
  simp [QuadraticMap.weightedSumSquares_apply, Units.smul_def]

/-- Evaluate a diagonal form on a linear combination of three distinct coordinate vectors. -/
theorem _root_.QuadraticMap.weightedSumSquares_three_single
    {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → R)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x y z : R) :
    QuadraticMap.weightedSumSquares R a
      (Pi.single i x + Pi.single j y + Pi.single k z) =
      a i * x ^ 2 + a j * y ^ 2 + a k * z ^ 2 := by
  classical
  rw [QuadraticMap.weightedSumSquares_apply,
    ← Finset.sum_subset (Finset.subset_univ {i, j, k})]
  · simp [Finset.sum_insert, hij, hik, hjk, smul_eq_mul, pow_two, add_assoc]
  · intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    simp [hl.1, hl.2.1, hl.2.2]

/-- A ternary solution with a nonzero third coordinate gives a nonzero isotropic vector in a
diagonal quadratic form. -/
theorem _root_.QuadraticMap.not_anisotropic_weightedSumSquares_of_ternary_eq_zero
    {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] (a : ι → R)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x y z : R} (hz : z ≠ 0)
    (h : a i * x ^ 2 + a j * y ^ 2 + a k * z ^ 2 = 0) :
    ¬ (QuadraticMap.weightedSumSquares R a).Anisotropic := by
  classical
  let f : ι → R := Pi.single i x + Pi.single j y + Pi.single k z
  intro hanis
  have hf : f = 0 := hanis f <| by
    simpa [f, weightedSumSquares_three_single a hij hik hjk x y z] using h
  have hz0 : z = 0 := by simpa [f, hik.symm, hjk.symm] using congrFun hf k
  exact hz hz0

section Discriminant

variable {R : Type u} [CommRing R] [Invertible (2 : R)]
variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

/-- The bilinear form associated with a diagonal quadratic form pairs the coordinates
diagonally: it is the weighted dot product. -/
@[simp]
theorem _root_.QuadraticMap.associated_weightedSumSquares (w : ι → R) (x y : ι → R) :
    QuadraticMap.associated (R := R) (QuadraticMap.weightedSumSquares R w) x y =
      ∑ i, w i * (x i * y i) := by
  have h2 : (2 : R) * (QuadraticMap.associated (R := R) (QuadraticMap.weightedSumSquares R w) x) y
      = (2 : R) * ∑ i, w i * (x i * y i) := by
    have h := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated R
      (QuadraticMap.weightedSumSquares (S := R) R w))
    simp only [LinearMap.smul_apply, nsmul_eq_mul] at h
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Nat.cast_ofNat] at h
    rw [h]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, Pi.add_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h := congrArg (fun r : R => ⅟(2 : R) * r) h2
  simpa only [← mul_assoc, invOf_mul_self, one_mul] using h

/-- The matrix of a diagonal quadratic form in the standard basis is the diagonal matrix of its
weights. -/
@[simp]
theorem _root_.QuadraticForm.toMatrix'_weightedSumSquares [DecidableEq ι] (w : ι → R) :
    QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares R w) = Matrix.diagonal w := by
  ext i j
  rw [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
    QuadraticMap.associated_weightedSumSquares]
  simp only [Matrix.diagonal_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The discriminant of a diagonal quadratic form is the product of its weights. -/
@[simp]
theorem _root_.QuadraticForm.discr'_weightedSumSquares [DecidableEq ι] (w : ι → R) :
    QuadraticForm.discr' (QuadraticMap.weightedSumSquares R w) = ∏ i, w i := by
  rw [QuadraticForm.discr', QuadraticForm.toMatrix'_weightedSumSquares, Matrix.det_diagonal]

/-- **Isometric diagonal forms with unit weights have weight products differing by a square.** An
isometry of the coordinate spaces changes the Gram matrix of a diagonal form by a congruence, so
it changes its determinant — the product of the weights — by the square of the determinant of that
isometry. -/
theorem isSquare_prod_mul_prod_of_equivalent {w : ι → Rˣ} {v : κ → Rˣ}
    (h : (QuadraticMap.weightedSumSquares R w).Equivalent
      (QuadraticMap.weightedSumSquares R v)) :
    IsSquare ((∏ i, w i) * ∏ i, v i) := by
  classical
  by_cases hR : Nontrivial R
  swap
  · have _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact ⟨1, Subsingleton.elim _ _⟩
  let _ : Nontrivial R := hR
  obtain ⟨f⟩ := h
  let e : ι ≃ κ := Fintype.equivOfCardEq <| by
    simpa only [Module.finrank_fintype_fun_eq_card] using f.toLinearEquiv.finrank_eq
  have hreindex : (QuadraticMap.weightedSumSquares R v).Equivalent
      (QuadraticMap.weightedSumSquares R (v ∘ e)) := by
    rw [QuadraticMap.weightedSumSquares_units, QuadraticMap.weightedSumSquares_units]
    exact equivalent_weightedSumSquares_comp (fun i => ((v i : R))) e
  have h' : (QuadraticMap.weightedSumSquares R w).Equivalent
      (QuadraticMap.weightedSumSquares R (v ∘ e)) :=
    QuadraticMap.Equivalent.trans ⟨f⟩ hreindex
  obtain ⟨f⟩ := h'
  obtain ⟨g, hg⟩ : ∃ g : (ι → R) ≃ₗ[R] (ι → R),
      QuadraticMap.weightedSumSquares R w
        = (QuadraticMap.weightedSumSquares R (v ∘ e)).comp g.toLinearMap :=
    ⟨f.toLinearEquiv, by ext x; exact (f.map_app' x).symm⟩
  have hdet : (∏ i, ((w i : R))) =
      ((LinearEquiv.det g : Rˣ) : R) * ((LinearEquiv.det g : Rˣ) : R) *
        ∏ i, (((v ∘ e) i : R)) := by
    rw [← QuadraticForm.discr'_weightedSumSquares fun i => ((w i : R)),
      ← QuadraticForm.discr'_weightedSumSquares fun i => (((v ∘ e) i : R)),
      ← QuadraticMap.weightedSumSquares_units, ← QuadraticMap.weightedSumSquares_units, hg,
      QuadraticForm.discr'_comp, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  refine ⟨LinearEquiv.det g * ∏ i, (v ∘ e) i, Units.ext ?_⟩
  push_cast
  have he : (∏ i, (((v ∘ e) i : R))) = ∏ i, ((v i : R)) :=
    Equiv.prod_comp e fun i => ((v i : R))
  rw [hdet, he]
  ring

end Discriminant

end TauCeti
