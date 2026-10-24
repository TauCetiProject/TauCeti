/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Basic

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# Arakelov height bounds for linear maps and matrix products

The Euclidean local factors in `arakelovMulHeight` make linear algebra estimates possible with
constant one. At an infinite place this is the submultiplicativity of the Frobenius norm, while
at a finite place it is the ultrametric inequality. Combining the local estimates gives bounds
for matrix products and, by viewing a vector as a one-column matrix, for linear maps.

These bounds contrast with the corresponding sup-height estimate: at archimedean places the
sup norm of a matrix product incurs a factor equal to the size of the contracted index.

## Main results

* `Matrix.arakelovMulHeight_mul_le`: the Arakelov height of a matrix product is at most the
  product of the heights of the factors.
* `TauCeti.arakelovMulHeight_linearMap_apply_le`: the one-column specialization for a linear
  map applied to a vector.
* `Matrix.arakelovLogHeight_mul_le` and
  `TauCeti.arakelovLogHeight_linearMap_apply_le`: their logarithmic forms.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1 and §6.3.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, §5.6.
-/

public noncomputable section

open scoped BigOperators Matrix.Norms.Frobenius
open NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

private theorem arakelov_infinite_mul_le {m n p : Type*} [Finite m] [Fintype n]
    [Finite p] (w : InfinitePlace K) (A : Matrix m n K) (B : Matrix n p K) :
    ((@Finset.univ (m × p) (Fintype.ofFinite _)).sum
      (fun q ↦ ‖w.embedding ((A * B) q.1 q.2)‖ ^ 2)) ^ ((w.mult : ℝ) / 2) ≤
      ((@Finset.univ (m × n) (Fintype.ofFinite _)).sum
        (fun q ↦ ‖w.embedding (A q.1 q.2)‖ ^ 2)) ^ ((w.mult : ℝ) / 2) *
        ((@Finset.univ (n × p) (Fintype.ofFinite _)).sum
          (fun q ↦ ‖w.embedding (B q.1 q.2)‖ ^ 2)) ^ ((w.mult : ℝ) / 2) := by
  let _ := Fintype.ofFinite m
  let _ := Fintype.ofFinite p
  let fmp : Fintype (m × p) := inferInstance
  let fmn : Fintype (m × n) := inferInstance
  let fnp : Fintype (n × p) := inferInstance
  have hmp : Fintype.ofFinite (m × p) = fmp := Subsingleton.elim _ _
  have hmn : Fintype.ofFinite (m × n) = fmn := Subsingleton.elim _ _
  have hnp : Fintype.ofFinite (n × p) = fnp := Subsingleton.elim _ _
  rw [hmp, hmn, hnp]
  let A' : Matrix m n ℂ := A.map w.embedding
  let B' : Matrix n p ℂ := B.map w.embedding
  have hmap : (A * B).map w.embedding = A' * B' := by
    ext i j
    simp [A', B', Matrix.mul_apply]
  have hnorm := Matrix.frobenius_norm_mul A' B'
  dsimp [A', B'] at hnorm
  rw [← hmap, Matrix.frobenius_norm_def, Matrix.frobenius_norm_def,
    Matrix.frobenius_norm_def] at hnorm
  simp only [Matrix.map_apply, Real.rpow_two, ← Finset.sum_product'] at hnorm
  have hnonneg : 0 ≤
      (∑ q : m × p, ‖w.embedding ((A * B) q.1 q.2)‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    positivity
  have hpow := Real.rpow_le_rpow hnonneg hnorm (Nat.cast_nonneg w.mult)
  calc
    (∑ q : m × p, ‖w.embedding ((A * B) q.1 q.2)‖ ^ 2) ^ ((w.mult : ℝ) / 2) =
        ((∑ q : m × p, ‖w.embedding ((A * B) q.1 q.2)‖ ^ 2) ^ ((1 : ℝ) / 2)) ^
          (w.mult : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      ring
    _ ≤ (((∑ q : m × n, ‖w.embedding (A q.1 q.2)‖ ^ 2) ^ ((1 : ℝ) / 2)) *
        ((∑ q : n × p, ‖w.embedding (B q.1 q.2)‖ ^ 2) ^ ((1 : ℝ) / 2))) ^
          (w.mult : ℝ) := hpow
    _ = (∑ q : m × n, ‖w.embedding (A q.1 q.2)‖ ^ 2) ^ ((w.mult : ℝ) / 2) *
        (∑ q : n × p, ‖w.embedding (B q.1 q.2)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1 <;> rw [← Real.rpow_mul (by positivity)] <;> congr 1 <;> ring

private theorem arakelov_finite_mul_le {m n p : Type*} [Finite m] [Fintype n]
    [Finite p] [Nonempty n] (v : FinitePlace K) (A : Matrix m n K) (B : Matrix n p K) :
    (⨆ q : m × p, v ((A * B) q.1 q.2)) ≤
      (⨆ q : m × n, v (A q.1 q.2)) * (⨆ q : n × p, v (B q.1 q.2)) := by
  rcases isEmpty_or_nonempty (m × p) with hmp | hmp
  · simp only [iSup_of_empty', Real.sSup_empty]
    exact mul_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _)
      (Real.iSup_nonneg_of_nonnegHomClass v _)
  refine ciSup_le fun q ↦ ?_
  calc
    v ((A * B) q.1 q.2) = v (∑ j, A q.1 j * B j q.2) := by rw [Matrix.mul_apply]
    _ ≤ ⨆ j, v (A q.1 j * B j q.2) := by
      refine (IsNonarchimedean.apply_sum_le_sup (FinitePlace.add_le v)
        (Finset.univ_nonempty : (Finset.univ : Finset n).Nonempty)).trans ?_
      exact Finset.sup'_le _ _ fun j _ ↦ Finite.le_ciSup_of_le j le_rfl
    _ ≤ (⨆ q : m × n, v (A q.1 q.2)) * (⨆ q : n × p, v (B q.1 q.2)) := by
      refine ciSup_le fun j ↦ ?_
      rw [map_mul]
      exact mul_le_mul
        (Finite.le_ciSup_of_le (q.1, j) le_rfl)
        (Finite.le_ciSup_of_le (j, q.2) le_rfl) (v.val.nonneg _)
        (Real.iSup_nonneg_of_nonnegHomClass v _)

end TauCeti

namespace Matrix

open TauCeti

variable {K : Type*} [Field K] [NumberField K] {m n p : Type*} [Finite m] [Fintype n] [Finite p]

/-- The relative Arakelov height of the entries of a matrix product is at most the product of
the relative Arakelov heights of the entries of its factors. This estimate has constant one,
including when an index type is empty. -/
theorem arakelovMulHeight_mul_le (A : Matrix m n K) (B : Matrix n p K) :
    TauCeti.arakelovMulHeight (fun q : m × p ↦ (A * B) q.1 q.2) ≤
      TauCeti.arakelovMulHeight (fun q : m × n ↦ A q.1 q.2) *
        TauCeti.arakelovMulHeight (fun q : n × p ↦ B q.1 q.2) := by
  classical
  let _ := Fintype.ofFinite m
  let _ := Fintype.ofFinite p
  set a : m × n → K := fun q ↦ A q.1 q.2
  set b : n × p → K := fun q ↦ B q.1 q.2
  set c : m × p → K := fun q ↦ (A * B) q.1 q.2
  suffices arakelovMulHeight c ≤ arakelovMulHeight a * arakelovMulHeight b by
    simpa only [a, b, c] using this
  have hbase : 1 ≤ arakelovMulHeight a * arakelovMulHeight b :=
    one_le_mul_of_one_le_of_one_le (one_le_arakelovMulHeight a) (one_le_arakelovMulHeight b)
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, arakelovMulHeight_zero]
    exact hbase
  have hn : Nonempty n := by
    by_contra hn
    let _ := not_nonempty_iff.mp hn
    apply hc
    ext q
    simp [c, Matrix.mul_apply]
  have ha : a ≠ 0 := by
    intro ha
    apply hc
    ext q
    simp only [c, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    have hAj := congrFun ha (q.1, j)
    simp only [a, Pi.zero_apply] at hAj
    simp [hAj]
  have hb : b ≠ 0 := by
    intro hb
    apply hc
    ext q
    simp only [c, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    have hBj := congrFun hb (j, q.2)
    simp only [b, Pi.zero_apply] at hBj
    simp [hBj]
  rw [arakelovMulHeight_eq hc, arakelovMulHeight_eq ha, arakelovMulHeight_eq hb,
    mul_mul_mul_comm]
  apply mul_le_mul
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦
      TauCeti.arakelov_infinite_mul_le w A B
  · rw [← finprod_mul_distrib (NumberField.FinitePlace.hasFiniteMulSupport_iSup ha)
      (NumberField.FinitePlace.hasFiniteMulSupport_iSup hb)]
    exact finprod_le_finprod₀ (NumberField.FinitePlace.hasFiniteMulSupport_iSup hc)
      (fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass _ _)
      ((NumberField.FinitePlace.hasFiniteMulSupport_iSup ha).mul
        (NumberField.FinitePlace.hasFiniteMulSupport_iSup hb))
      fun v ↦ TauCeti.arakelov_finite_mul_le v A B
  · exact finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass _ _
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ ↦ by positivity)
      (Finset.prod_nonneg fun _ _ ↦ by positivity)

/-- Logarithmic form of `Matrix.arakelovMulHeight_mul_le`. -/
theorem arakelovLogHeight_mul_le (A : Matrix m n K) (B : Matrix n p K) :
    TauCeti.arakelovLogHeight (fun q : m × p ↦ (A * B) q.1 q.2) ≤
      TauCeti.arakelovLogHeight (fun q : m × n ↦ A q.1 q.2) +
        TauCeti.arakelovLogHeight (fun q : n × p ↦ B q.1 q.2) := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight, ← Real.log_mul
    (arakelovMulHeight_ne_zero _) (arakelovMulHeight_ne_zero _)]
  exact Real.log_le_log (arakelovMulHeight_pos _) (arakelovMulHeight_mul_le A B)

end Matrix

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- Applying a matrix to a vector does not increase relative Arakelov height by more than the
height of the matrix. Unlike the analogous sup-height bound, no cardinality factor and no
nonemptiness hypothesis are needed. -/
theorem arakelovMulHeight_linearMap_apply_le {m n : Type*} [Finite m] [Fintype n]
    (A : m × n → K) (x : n → K) :
    arakelovMulHeight (fun i ↦ ∑ j, A (i, j) * x j) ≤
      arakelovMulHeight A * arakelovMulHeight x := by
  let M : Matrix m n K := fun i j ↦ A (i, j)
  let X : Matrix n Unit K := fun i _ ↦ x i
  have h := Matrix.arakelovMulHeight_mul_le M X
  let eOut : m ≃ m × Unit := (Equiv.prodUnique m Unit).symm
  let eX : n ≃ n × Unit := (Equiv.prodUnique n Unit).symm
  have hentry (i : m) : (M * X) i Unit.unit = ∑ j, A (i, j) * x j := by
    rw [Matrix.mul_apply]
  have hOut :
      arakelovMulHeight (fun i ↦ ∑ j, A (i, j) * x j) =
        arakelovMulHeight (fun q : m × Unit ↦ (M * X) q.1 q.2) := by
    have heq : (fun i ↦ ∑ j, A (i, j) * x j) =
        (fun q : m × Unit ↦ (M * X) q.1 q.2) ∘ eOut := by
      funext i
      simpa [eOut] using (hentry i).symm
    rw [heq]
    exact arakelovMulHeight_comp_equiv eOut _
  have hA :
      arakelovMulHeight A = arakelovMulHeight (fun q : m × n ↦ M q.1 q.2) := by
    simp [M]
  have hX :
      arakelovMulHeight x = arakelovMulHeight (fun q : n × Unit ↦ X q.1 q.2) := by
    have heq : x = (fun q : n × Unit ↦ X q.1 q.2) ∘ eX := by
      funext i
      simp [X, eX]
    rw [heq]
    exact arakelovMulHeight_comp_equiv eX _
  rw [← hOut, ← hA, ← hX] at h
  exact h

/-- Logarithmic form of `TauCeti.arakelovMulHeight_linearMap_apply_le`. -/
theorem arakelovLogHeight_linearMap_apply_le {m n : Type*} [Finite m] [Fintype n]
    (A : m × n → K) (x : n → K) :
    arakelovLogHeight (fun i ↦ ∑ j, A (i, j) * x j) ≤
      arakelovLogHeight A + arakelovLogHeight x := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight, ← Real.log_mul
    (arakelovMulHeight_ne_zero _) (arakelovMulHeight_ne_zero _)]
  exact Real.log_le_log (arakelovMulHeight_pos _)
    (arakelovMulHeight_linearMap_apply_le A x)

end TauCeti
