/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Bounded-degree polynomial functions on Euclidean space

`TauCeti.polynomialsDegLE ι m` is the subspace of real functions on `EuclideanSpace ℝ ι`
represented by multivariate polynomials of total degree at most `m`. Evaluation is injective,
so this space is linearly equivalent to the corresponding formal polynomial space and has
dimension `(m + Fintype.card ι).choose (Fintype.card ι)`.

These are functions on the whole Euclidean space, before restriction to a domain or passage
to almost-everywhere classes. In particular, degree zero means exactly the constant functions,
also when the coordinate type is empty.

Evaluating a real multilinear map on the diagonal gives a polynomial function of degree at most
the number of its arguments (`MultilinearMap.apply_const_mem_polynomialsDegLE`); this covers
the homogeneous terms of a power series.

The construction uses Mathlib's `MvPolynomial.evalₗ` and `MvPolynomial.funext`, and the formal
dimension formula `TauCeti.finrank_restrictTotalDegree`.
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial

variable (ι : Type*)

/-- Evaluate a real multivariate polynomial on Euclidean coordinates, linearly in the
polynomial. -/
def polynomialEvalₗ : MvPolynomial ι ℝ →ₗ[ℝ] (EuclideanSpace ℝ ι → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (EuclideanSpace.equiv ι ℝ)).comp (MvPolynomial.evalₗ ℝ ι)

@[simp]
theorem polynomialEvalₗ_apply (p : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    polynomialEvalₗ ι p x = eval (fun i ↦ x i) p :=
  (rfl)

/-- Evaluation on the whole Euclidean space determines a formal polynomial uniquely. -/
theorem polynomialEvalₗ_injective : Function.Injective (polynomialEvalₗ ι) := by
  intro p q h
  apply MvPolynomial.funext
  intro x
  have hx := congrFun h ((EuclideanSpace.equiv ι ℝ).symm x)
  simpa only [polynomialEvalₗ_apply, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply] using hx

/-- The subspace of real polynomial functions of total degree at most `m`. -/
def polynomialsDegLE (m : ℕ) : Submodule ℝ (EuclideanSpace ℝ ι → ℝ) :=
  (restrictTotalDegree ι ℝ m).map (polynomialEvalₗ ι)

/-- The polynomial function space is the image of formal bounded-degree polynomials. -/
theorem polynomialsDegLE_def (m : ℕ) :
    polynomialsDegLE ι m = (restrictTotalDegree ι ℝ m).map (polynomialEvalₗ ι) :=
  (rfl)

/-- Membership is precisely representability by a polynomial of bounded total degree. -/
theorem mem_polynomialsDegLE_iff {m : ℕ} {f : EuclideanSpace ℝ ι → ℝ} :
    f ∈ polynomialsDegLE ι m ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ m ∧ polynomialEvalₗ ι p = f := by
  simp only [polynomialsDegLE_def, Submodule.mem_map, mem_restrictTotalDegree]

/-- Evaluating a formal polynomial belongs to the function space exactly at its degree
and above. -/
@[simp]
theorem polynomialEvalₗ_mem_polynomialsDegLE_iff (m : ℕ) (p : MvPolynomial ι ℝ) :
    polynomialEvalₗ ι p ∈ polynomialsDegLE ι m ↔ p.totalDegree ≤ m := by
  rw [mem_polynomialsDegLE_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    exact polynomialEvalₗ_injective ι h ▸ hq
  · exact fun hp ↦ ⟨p, hp, rfl⟩

/-- Increasing the total-degree bound enlarges the polynomial function space. -/
theorem polynomialsDegLE_mono : Monotone (polynomialsDegLE ι) :=
  fun _ _ h ↦ Submodule.map_mono (restrictTotalDegree_mono ι ℝ h)

/-- Formal bounded-degree polynomials and the functions they represent are linearly
equivalent. -/
def restrictTotalDegreeEquivPolynomialsDegLE (m : ℕ) :
    restrictTotalDegree ι ℝ m ≃ₗ[ℝ] polynomialsDegLE ι m :=
  Submodule.equivMapOfInjective (polynomialEvalₗ ι) (polynomialEvalₗ_injective ι) _

@[simp]
theorem coe_restrictTotalDegreeEquivPolynomialsDegLE (m : ℕ) (p : restrictTotalDegree ι ℝ m) :
    (restrictTotalDegreeEquivPolynomialsDegLE ι m p : EuclideanSpace ℝ ι → ℝ) =
      polynomialEvalₗ ι p :=
  (rfl)

@[simp]
theorem polynomialEvalₗ_restrictTotalDegreeEquivPolynomialsDegLE_symm (m : ℕ)
    (f : polynomialsDegLE ι m) :
    polynomialEvalₗ ι ((restrictTotalDegreeEquivPolynomialsDegLE ι m).symm f) = f :=
  Submodule.map_equivMapOfInjective_symm_apply _ _ _ _

@[simp]
theorem polynomialEvalₗ_C (c : ℝ) :
    polynomialEvalₗ ι (C c) = fun _ ↦ c := by
  ext x
  simp

@[simp]
theorem polynomialEvalₗ_X (i : ι) :
    polynomialEvalₗ ι (X i) = fun x ↦ x i := by
  ext x
  simp

/-- Every constant function belongs to every nonnegative degree bound. -/
@[simp]
theorem const_mem_polynomialsDegLE (m : ℕ) (c : ℝ) :
    (fun _ : EuclideanSpace ℝ ι ↦ c) ∈ polynomialsDegLE ι m := by
  rw [← polynomialEvalₗ_C ι c, polynomialEvalₗ_mem_polynomialsDegLE_iff]
  simp

/-- A coordinate function belongs exactly when the degree bound is positive. -/
@[simp]
theorem coordinate_mem_polynomialsDegLE_iff (m : ℕ) (i : ι) :
    (fun x : EuclideanSpace ℝ ι ↦ x i) ∈ polynomialsDegLE ι m ↔ 1 ≤ m := by
  rw [← polynomialEvalₗ_X ι i, polynomialEvalₗ_mem_polynomialsDegLE_iff, totalDegree_X]

/-- Degree-zero polynomial functions are exactly the constant functions. -/
theorem mem_polynomialsDegLE_zero_iff {f : EuclideanSpace ℝ ι → ℝ} :
    f ∈ polynomialsDegLE ι 0 ↔ ∃ c : ℝ, f = fun _ ↦ c := by
  constructor
  · rintro hf
    obtain ⟨p, hp, rfl⟩ := (mem_polynomialsDegLE_iff ι).1 hf
    have hpC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp)
    refine ⟨p.coeff 0, ?_⟩
    rw [hpC]
    ext x
    simp
  · rintro ⟨c, rfl⟩
    exact const_mem_polynomialsDegLE ι 0 c

/-- Evaluating a real multilinear map on the diagonal gives a polynomial function whose degree is
at most the number of arguments. -/
theorem _root_.MultilinearMap.apply_const_mem_polynomialsDegLE [Finite ι] {κ : Type*}
    [Fintype κ] (m : (Π _ : κ, EuclideanSpace ℝ ι) →ₘₗ[ℝ] ℝ) :
    (fun x ↦ m fun _ ↦ x) ∈ polynomialsDegLE ι (Fintype.card κ) := by
  classical
  have := Fintype.ofFinite ι
  set b := EuclideanSpace.basisFun ι ℝ
  refine (mem_polynomialsDegLE_iff ι).2
    ⟨∑ σ : κ → ι, C (m fun j ↦ b (σ j)) * ∏ j, X (σ j), ?_, ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    simp [totalDegree_X]
  · ext x
    -- Expand `x = ∑ᵢ xᵢ eᵢ` in every argument by multilinearity.
    conv_rhs => rw [← b.sum_repr x, m.map_sum]
    simp [m.map_smul_univ, b, mul_comm]

/-- Bounded-degree polynomial functions form a finite-dimensional space. -/
instance [Finite ι] (m : ℕ) : FiniteDimensional ℝ (polynomialsDegLE ι m) :=
  inferInstanceAs (Module.Finite ℝ ((restrictTotalDegree ι ℝ m).map (polynomialEvalₗ ι)))

/-- The dimension of polynomial functions of total degree at most `m` is the number of
monomials of that degree or less. -/
@[simp]
theorem finrank_polynomialsDegLE [Fintype ι] (m : ℕ) :
    Module.finrank ℝ (polynomialsDegLE ι m) =
      (m + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← (restrictTotalDegreeEquivPolynomialsDegLE ι m).finrank_eq,
    finrank_restrictTotalDegree]

end TauCeti
