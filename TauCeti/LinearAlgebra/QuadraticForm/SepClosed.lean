/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Quadratic forms over a separably closed field

This file proves that a finite-dimensional nondegenerate quadratic form over a separably closed
field of characteristic different from two is equivalent to a sum of squares, so that such forms
are classified up to equivalence by their dimension. It also characterizes representation by
the dimension inequality and proves isotropy in dimension at least two.

## Main results

* `QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed`: a nondegenerate quadratic form is
  equivalent to the standard sum of squares.
* `QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed`: nondegenerate quadratic forms on spaces
  of the same dimension are equivalent.
* `QuadraticForm.equivalent_iff_finrank_eq_of_isSepClosed`: nondegenerate quadratic forms are
  equivalent exactly when their dimensions agree.
* `QuadraticForm.equivalent_weightedSumSquares_one_iff_finrank_eq`: a nondegenerate form is
  equivalent to the standard sum of squares on `Fin n` exactly when its dimension is `n`.
* `QuadraticForm.isRepresentedBy_iff_finrank_le_of_isSepClosed`: representation of nondegenerate
  quadratic forms is characterized by the inequality of their dimensions.
* `QuadraticForm.not_anisotropic_of_isSepClosed`: every form in dimension at least two is isotropic.

## References

* Mathlib's `QuadraticForm.isometryEquivSumSquaresUnits` and
  `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` supply the normalization argument
  adapted here from algebraically closed to separably closed fields.
-/

public section

open QuadraticMap

namespace QuadraticForm

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [IsSepClosed K]

private noncomputable def isometryEquivSumSquaresUnits [NeZero (2 : K)] (w : ι → Kˣ) :
    IsometryEquiv (weightedSumSquares K fun i ↦ (w i : K))
      (weightedSumSquares K (1 : ι → K)) := by
  classical
  refine isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ Units.mk0 (IsSepClosed.isSquare (w i : K)).choose ?_) ?_
  · rw [← mul_self_eq_zero.ne, ← (IsSepClosed.isSquare (w i : K)).choose_spec]
    exact (w i).ne_zero
  · intro i
    simp [pow_two, ← (IsSepClosed.isSquare (w i : K)).choose_spec]

/-- A finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is equivalent to the standard sum of squares. -/
theorem equivalent_weightedSumSquares_of_isSepClosed [Invertible (2 : K)] {M : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

/-- Nondegenerate quadratic forms over a separably closed field of characteristic different from
two, on possibly different finite-dimensional spaces, are equivalent when their dimensions
agree. -/
theorem equivalent_of_finrank_eq_of_isSepClosed [Invertible (2 : K)] {M N : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (Q : QuadraticForm K M) (R : QuadraticForm K N) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (h : Module.finrank K M = Module.finrank K N) : Q.Equivalent R := by
  have hQ' := Q.equivalent_weightedSumSquares_of_isSepClosed
    (nondegenerate_associated_iff.mpr hQ).1
  rw [h] at hQ'
  exact hQ'.trans (R.equivalent_weightedSumSquares_of_isSepClosed
    (nondegenerate_associated_iff.mpr hR).1).symm

/-- Two regular quadratic forms over a separably closed field are equivalent precisely when
their dimensions agree. -/
@[simp] theorem equivalent_iff_finrank_eq_of_isSepClosed
    {K W₁ W₂ : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank K W₁ = Module.finrank K W₂ := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · exact QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed Q R hQ hR

/-- Over a separably closed field a regular quadratic form is isometric to the standard sum
of squares on `Fin n` exactly when its space has dimension `n`. -/
@[simp]
theorem equivalent_weightedSumSquares_one_iff_finrank_eq
    {K W : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : Q.Nondegenerate) (n : ℕ) :
    Q.Equivalent (weightedSumSquares K (1 : Fin n → K)) ↔ Module.finrank K W = n := by
  constructor
  · rintro ⟨e⟩
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  · rintro rfl
    exact Q.equivalent_weightedSumSquares_of_isSepClosed
      (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1

/-- A regular quadratic form over a separably closed field is represented by another regular
form exactly when the dimension of its space is no larger. -/
@[simp]
theorem isRepresentedBy_iff_finrank_le_of_isSepClosed
    {K W₁ W₂ : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsRepresentedBy R ↔ Module.finrank K W₁ ≤ Module.finrank K W₂ := by
  constructor
  · rw [QuadraticMap.isRepresentedBy_iff]
    rintro ⟨f, hf, -⟩
    exact LinearMap.finrank_le_finrank_of_injective hf
  · intro h
    let S : QuadraticForm K (Fin (Module.finrank K W₂ - Module.finrank K W₁) → K) :=
      weightedSumSquares K
        (1 : Fin (Module.finrank K W₂ - Module.finrank K W₁) → K)
    have hS : S.Nondegenerate := nondegenerate_weightedSumSquares fun _ ↦ isRegular_one
    have hprod : (Q.prod S).Nondegenerate := hQ.prod hS
    have hrank : Module.finrank K
          (W₁ × (Fin (Module.finrank K W₂ - Module.finrank K W₁) → K)) =
        Module.finrank K W₂ := by
      simp only [Module.finrank_prod, Module.finrank_fin_fun]
      omega
    obtain ⟨e⟩ := QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed
      (Q.prod S) R hprod hR hrank
    rw [QuadraticMap.isRepresentedBy_iff]
    exact ⟨(e.toIsometry.comp (QuadraticMap.Isometry.inl Q S)).toLinearMap,
      e.injective.comp LinearMap.inl_injective, fun x ↦ by simp⟩

/-- A form over a separably closed field of characteristic not two has a nonzero isotropic
vector when its space has dimension at least two. -/
theorem not_anisotropic_of_isSepClosed
    {K W : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (Q : QuadraticForm K W)
    (h : 2 ≤ Module.finrank K W) : ¬ Q.Anisotropic := by
  classical
  intro hQ
  have he := Q.equivalent_weightedSumSquares_of_isSepClosed
    (QuadraticMap.separatingLeft_of_anisotropic Q hQ)
  have hstandard := he.anisotropic_iff.mp hQ
  obtain ⟨i, hi⟩ := IsSepClosed.isSquare (-1 : K)
  let i₀ : Fin (Module.finrank K W) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank K W) := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁]
  -- The two coordinate values contribute `1` and `-1` to the sum of squares.
  have hzero := hstandard (Pi.single i₀ 1 + Pi.single i₁ i) (by
    simp [weightedSumSquares_apply, Pi.single_apply, mul_add, add_mul, hne, hne.symm,
      Finset.sum_add_distrib, Finset.sum_ite_eq', ← hi])
  have : (1 : K) = 0 := by simpa [hne] using congrFun hzero i₀
  exact one_ne_zero this

end QuadraticForm
