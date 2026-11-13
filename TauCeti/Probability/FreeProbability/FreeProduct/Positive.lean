/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.FreeProduct.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Probability.FreeProbability.Orthogonality
import TauCeti.LinearAlgebra.Matrix.PosSemidef
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Positivity of the free-product expectation

The free-product expectation of normalized positive complex-linear functionals is positive
on algebraic squares. Its algebraic GNS representation therefore realizes the free factors
with their prescribed joint star distributions. No norm, faithfulness, trace, or boundedness
assumption is made on the factors or on the resulting representation.

The proof uses the orthogonality of distinct reduced words. On each word summand the Gram
matrix is the entrywise product of the factor GNS Gram matrices, hence is positive semidefinite
by the Schur product theorem.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 7.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §1.5.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct
open LinearAlgebra.FreeProduct

namespace TauCeti

variable {I : Type*} [DecidableEq I] {A : I → Type*}
  [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)] [∀ i, StarRing (A i)]
  [∀ i, StarModule ℂ (A i)]

private theorem pure_pairing
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)
    (w v : ReducedWord I)
    (m : ∀ k, WordTensorFactor (fun i ↦ (φ i).toLinearMap) w k)
    (n : ∀ k, WordTensorFactor (fun i ↦ (φ i).toLinearMap) v k) :
    freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ
      (star (wordMul (fun i ↦ (φ i).toLinearMap) w (PiTensorProduct.tprod ℂ m)) *
        wordMul (fun i ↦ (φ i).toLinearMap) v (PiTensorProduct.tprod ℂ n)) =
    if h : w = v then ∏ k, φ w.toList[k] (star (m k).1 * ((h.symm ▸ n) k).1) else 0 := by
  let W : List (I × LinearAlgebra.FreeProduct ℂ A) :=
    List.ofFn fun k ↦ (w.toList[k], ι ℂ A w.toList[k] (m k))
  let V : List (I × LinearAlgebra.FreeProduct ℂ A) :=
    List.ofFn fun k ↦ (v.toList[k], ι ℂ A v.toList[k] (n k))
  have hW : W.map Prod.fst = w.toList := by simp [W, List.map_ofFn, Function.comp_def]
  have hV : V.map Prod.fst = v.toList := by simp [V, List.map_ofFn, Function.comp_def]
  have hfree : IsFreelyIndependent (freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ)
      (fun i ↦ (ιStar ℂ A i).range.toSubalgebra) :=
    by simpa only [StarAlgHom.range, ιStar_toAlgHom] using
      isFreelyIndependent_freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ
  have h := hfree.apply_star_prod_mul_prod
    (freeProductExpectation_one _ hφ)
    (freeProductExpectation_star _ hφ fun i a ↦ (φ i).map_star a) W V
    (hW ▸ w.isChain) (hV ▸ v.isChain)
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; exact ⟨(m k).1, ιStar_apply ℂ A _ _⟩)
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; exact ⟨(n k).1, ιStar_apply ℂ A _ _⟩)
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
        simp)
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
        simp)
  have hWM : W.map Prod.snd = List.ofFn (fun k ↦ ι ℂ A w.toList[k] (m k)) := by
    simp [W, List.map_ofFn, Function.comp_def]
  have hVM : V.map Prod.snd = List.ofFn (fun k ↦ ι ℂ A v.toList[k] (n k)) := by
    simp [V, List.map_ofFn, Function.comp_def]
  rw [wordMul_tprod, wordMul_tprod, ← hWM, ← hVM, h, hW, hV]
  by_cases hwv : w = v
  · subst v
    simp only [dite_true, ↓reduceIte]
    have hz : List.zipWith
        (fun x y : I × LinearAlgebra.FreeProduct ℂ A ↦
          freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ (star x.2 * y.2)) W V =
        List.ofFn (fun k ↦ φ w.toList[k] (star (m k).1 * (n k).1)) := by
      apply List.ext_getElem
      · simp [W, V]
      · intro j hj hk
        simp [W, V, List.getElem_zipWith, star_ι, ← map_mul, freeProductExpectation_ι]
    rw [hz, List.prod_ofFn]
  · have hne : w.toList ≠ v.toList := fun h ↦ hwv (ReducedWord.ext h)
    simp [hwv, hne]

/-- Distinct reduced-word summands are orthogonal for the free-product expectation of positive
normalized factor functionals. -/
private theorem freeProductExpectation_star_wordMul_mul_wordMul_eq_zero
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)
    {w v : ReducedWord I} (hwv : w ≠ v)
    (x : WordTensor (fun i ↦ (φ i).toLinearMap) w)
    (y : WordTensor (fun i ↦ (φ i).toLinearMap) v) :
    freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ
      (star (wordMul (fun i ↦ (φ i).toLinearMap) w x) *
        wordMul (fun i ↦ (φ i).toLinearMap) v y) = 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s n =>
      simp only [map_smul, star_smul, smul_mul_assoc, mul_smul_comm, pure_pairing,
        dite_eq_right hwv, smul_zero]
    | add y z hy hz => simp only [map_add, mul_add, hy, hz, add_zero]
  | add x z hx hz => simp only [map_add, star_add, add_mul, hx, hz, add_zero]

private theorem word_square_nonneg
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)
    (w : ReducedWord I) (x : WordTensor (fun i ↦ (φ i).toLinearMap) w) :
    0 ≤ freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ
      (star (wordMul (fun i ↦ (φ i).toLinearMap) w x) *
        wordMul (fun i ↦ (φ i).toLinearMap) w x) := by
  classical
  have hxspan : x ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ)) := by
    rw [PiTensorProduct.span_tprod_eq_top]
    trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hxspan
  have hx : x = ∑ m : c.support, c m • PiTensorProduct.tprod ℂ m.1 := by
    rw [← hc, Finsupp.sum]
    exact (Finset.sum_attach _ _).symm
  rw [hx]
  have hK : Matrix.PosSemidef (fun m n : c.support ↦
      ∏ k, φ w.toList[k] (star (m.1 k).1 * (n.1 k).1)) := by
    apply posSemidef_schur_finset_prod
    intro k _
    have heq : (fun m n : c.support ↦ φ w.toList[k] (star (m.1 k).1 * (n.1 k).1)) =
        Matrix.gram ℂ (fun m : c.support ↦ (φ w.toList[k]).classMap (m.1 k).1) := by
      ext m n
      simp only [Matrix.gram_apply, StarPositiveFunctional.inner_classMap]
    rw [heq]
    exact Matrix.posSemidef_gram ℂ _
  have h := (posSemidef_iff_finite_sum.mp hK).2 (fun m : c.support ↦ m) (fun m ↦ c m)
  rw [Finset.sum_comm] at h
  simpa only [map_sum, star_sum, Finset.sum_mul, Finset.mul_sum, map_smul,
    star_smul, smul_mul_assoc, mul_smul_comm, pure_pairing, dite_true,
    smul_eq_mul, mul_assoc, mul_comm (c _)] using h

private theorem expectation_square_nonneg
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)
    (x : LinearAlgebra.FreeProduct ℂ A) :
    0 ≤ freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ (star x * x) := by
  classical
  let z := equivReducedWords (fun i ↦ (φ i).toLinearMap) hφ x
  have hx : x = ∑ w ∈ z.support,
      wordMul (fun i ↦ (φ i).toLinearMap) w (z w) := by
    calc
      x = (equivReducedWords (fun i ↦ (φ i).toLinearMap) hφ).symm z :=
        ((equivReducedWords _ hφ).symm_apply_apply x).symm
      _ = (equivReducedWords (fun i ↦ (φ i).toLinearMap) hφ).symm
          (∑ w ∈ z.support, DirectSum.of _ w (z w)) := by
        rw [DirectSum.sum_support_of]
      _ = _ := by
        simp only [map_sum, ← DirectSum.lof_eq_of ℂ, equivReducedWords_symm_apply,
          reducedWordsToFreeProduct_lof]
  rw [hx]
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_nonneg
  intro w hw
  rw [Finset.sum_eq_single w]
  · exact word_square_nonneg φ hφ w (z w)
  · intro v _ hvw
    exact freeProductExpectation_star_wordMul_mul_wordMul_eq_zero φ hφ hvw _ _
  · exact fun h ↦ (h hw).elim

/-- The canonical free-product expectation is positive on algebraic squares whenever each
normalized factor functional is positive on algebraic squares. No norm or trace is required. -/
theorem freeProductExpectation_star_mul_self_nonneg
    (φ : ∀ i, A i →ₗ[ℂ] ℂ) (hφ : ∀ i, φ i 1 = 1)
    (hpos : ∀ i a, 0 ≤ φ i (star a * a)) (x : LinearAlgebra.FreeProduct ℂ A) :
    0 ≤ freeProductExpectation φ hφ (star x * x) :=
  expectation_square_nonneg (fun i ↦ ⟨φ i, hpos i⟩) hφ x

/-- The positive functional on the algebraic free product extending the normalized positive
factor functionals. Its algebraic GNS representation realizes their free joint distribution. -/
def freeProductPositiveFunctional
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1) :
    StarPositiveFunctional (LinearAlgebra.FreeProduct ℂ A) where
  toLinearMap := freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ
  square_nonneg := freeProductExpectation_star_mul_self_nonneg _ hφ
    (fun i ↦ (φ i).square_nonneg)

@[simp]
theorem freeProductPositiveFunctional_toLinearMap
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1) :
    (freeProductPositiveFunctional φ hφ).toLinearMap =
      freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ := (rfl)

theorem freeProductPositiveFunctional_apply
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1)
    (x : LinearAlgebra.FreeProduct ℂ A) :
    freeProductPositiveFunctional φ hφ x =
      freeProductExpectation (fun i ↦ (φ i).toLinearMap) hφ x := (rfl)

@[simp]
theorem freeProductPositiveFunctional_one
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1) :
    freeProductPositiveFunctional φ hφ 1 = 1 := by
  rw [freeProductPositiveFunctional_apply, freeProductExpectation_one]

@[simp]
theorem freeProductPositiveFunctional_ι
    (φ : ∀ i, StarPositiveFunctional (A i)) (hφ : ∀ i, φ i 1 = 1) (i : I) (a : A i) :
    freeProductPositiveFunctional φ hφ (ι ℂ A i a) = φ i a := by
  rw [freeProductPositiveFunctional_apply, freeProductExpectation_ι,
    StarPositiveFunctional.toLinearMap_apply]

end TauCeti
