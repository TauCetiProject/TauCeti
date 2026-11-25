/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.FrobeniusFixedPoints
public import TauCeti.RingTheory.PowerSeries.Matrix.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Lang's theorem over formal power series

Let `k` be an algebraically closed field of characteristic `p > 0`, let `q = p ^ f` with `f > 0`,
and let `σ` be the `q`-power Frobenius of `k`, acting on `k⟦X⟧` coefficientwise. This file proves
that every invertible matrix `A` over `k⟦X⟧` is `B σ(B)⁻¹` for an invertible matrix `B` over
`k⟦X⟧`, where `σ` acts entrywise: `A σ(B) = B`.

In module terms: a free `k⟦X⟧`-module of finite rank with a `σ`-semilinear map whose matrix in
some basis is invertible has a basis of fixed vectors, the columns of `B` in that basis. With `X`
playing the uniformizer `π` of `k((π))`, a Frobenius module over `k((π))` with a lattice that the
Frobenius maps onto itself is therefore a direct sum of copies of the unit object: unit-root
Frobenius modules are trivial. This is the slope-zero input of the equal-characteristic
Dieudonné–Manin classification.

The proof solves `A σ(B) = B` coefficient by coefficient. Writing `A = ∑ Aᵢ Xⁱ` and
`B = ∑ Bⱼ Xʲ`, the equation in degree `m` reads `∑_{i + j = m} Aᵢ σ(Bⱼ) = Bₘ`. In degree `0` it is
`A₀ σ(B₀) = B₀` over `k`, which Lang's theorem for `GLₙ(k)`,
`Matrix.exists_isUnit_mul_map_iterateFrobenius_eq`, solves with `B₀` invertible. In degree
`m + 1` the substitution `Bₘ₊₁ = B₀ Y` turns it into `B₀ (σ(Y) - Y) = -∑_{j ≤ m} Aₘ₊₁₋ⱼ σ(Bⱼ)`,
that is, into one Artin–Schreier equation `y ^ q - y = c` for each entry of `Y`, solvable since
`k` is algebraically closed.

## Main results

* `PowerSeries.exists_isUnit_mul_map_iterateFrobenius_eq`: every invertible matrix `A` over
  `k⟦X⟧` has an invertible `B` over `k⟦X⟧` with `A σ(B) = B`.

## References

* N. M. Katz, *p-adic properties of modular schemes and modular forms*, in *Modular functions of
  one variable III*, Lecture Notes in Math. 350, Springer, 1973, §4.1, for fixed vectors of
  unit-root Frobenius modules.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §4.5, for the
  Dieudonné–Manin classification over a coefficient field with algebraically closed residue
  field.
-/

public section

namespace PowerSeries

open Finset Matrix

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n]

/-- A solution of `x ^ q - x = c`, when one exists. -/
private noncomputable def artinSchreierRoot (q : ℕ) (c : k) : k :=
  open Classical in if h : ∃ x : k, x ^ q - x = c then h.choose else 0

private theorem artinSchreierRoot_spec [IsAlgClosed k] (p : ℕ) [CharP k p] {q : ℕ} (hpq : p ∣ q)
    (hq : 2 ≤ q) (c : k) : artinSchreierRoot q c ^ q - artinSchreierRoot q c = c := by
  obtain ⟨x, hx⟩ :=
    IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' p q 1 (-1) (-c) hpq hq (by simp)
  have h : ∃ x : k, x ^ q - x = c := ⟨x, by linear_combination hx⟩
  rw [artinSchreierRoot, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

section Recursion

variable (p f : ℕ) [ExpChar k p]

/-- The coefficient matrices of a solution of `A σ(B) = B` with constant term `B₀`, by the
recursion `Bₘ₊₁ = B₀ Y`, where `Y` solves `σ(Y) - Y = -B₀⁻¹ ∑_{i ≤ m} Aᵢ₊₁ σ(Bₘ₋ᵢ)` entrywise. -/
private noncomputable def langCoeff (A : Matrix n n k⟦X⟧) (B₀ : Matrix n n k) :
    ℕ → Matrix n n k
  | 0 => B₀
  | m + 1 => B₀ * (-(B₀⁻¹ * ∑ i : Fin (m + 1),
      A.map (coeff (i + 1)) * (langCoeff A B₀ (m - i)).map (iterateFrobenius k p f))).map
        (artinSchreierRoot (p ^ f))

variable {p f}

/-- If `A₀ σ(B₀) = B₀` with `B₀` invertible, the recursion `langCoeff` solves the equation
`∑_{i + j = m + 1} Aᵢ σ(Bⱼ) = Bₘ₊₁` in every positive degree `m + 1`. -/
private theorem langCoeff_succ [IsAlgClosed k] [CharP k p] (hf : f ≠ 0) (hq : 1 < p ^ f)
    {A : Matrix n n k⟦X⟧} {B₀ : Matrix n n k}
    (hAB₀ : A.map constantCoeff * B₀.map (iterateFrobenius k p f) = B₀)
    (hdet : IsUnit B₀.det) (m : ℕ) :
    A.map constantCoeff * (langCoeff p f A B₀ (m + 1)).map (iterateFrobenius k p f) +
      ∑ x ∈ antidiagonal m,
        A.map (coeff (x.1 + 1)) * (langCoeff p f A B₀ x.2).map (iterateFrobenius k p f) =
      langCoeff p f A B₀ (m + 1) := by
  set σ := iterateFrobenius k p f
  -- the terms of degree `m + 1` other than `A₀ σ(Bₘ₊₁)`
  set S := ∑ i : Fin (m + 1),
    A.map (coeff (i + 1)) * (langCoeff p f A B₀ (m - i)).map σ with hS_def
  have hS : ∑ x ∈ antidiagonal m,
      A.map (coeff (x.1 + 1)) * (langCoeff p f A B₀ x.2).map σ = S := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ A.map (coeff (a + 1)) * (langCoeff p f A B₀ b).map σ),
      hS_def, Fin.sum_univ_eq_sum_range (fun i ↦ A.map (coeff (i + 1)) *
        (langCoeff p f A B₀ (m - i)).map σ)]
  set Y := (-(B₀⁻¹ * S)).map (artinSchreierRoot (p ^ f)) with hY_def
  have hY : Y.map σ = Y - B₀⁻¹ * S := by
    ext i j
    simp only [hY_def, Matrix.map_apply, Matrix.sub_apply, Matrix.neg_apply]
    rw [show σ _ = _ ^ p ^ f from iterateFrobenius_def p f _]
    linear_combination artinSchreierRoot_spec p (dvd_pow_self p hf) hq (-((B₀⁻¹ * S) i j))
  have hlang : langCoeff p f A B₀ (m + 1) = B₀ * Y := by rw [langCoeff]
  rw [hS, hlang]
  -- `A₀ σ(B₀ Y) + S = B₀ σ(Y) + S = B₀ (Y - B₀⁻¹ S) + S = B₀ Y`
  calc A.map constantCoeff * (B₀ * Y).map σ + S = B₀ * Y.map σ + S := by
        rw [Matrix.map_mul, ← Matrix.mul_assoc, hAB₀]
    _ = B₀ * (Y - B₀⁻¹ * S) + S := by rw [hY]
    _ = B₀ * Y := by simp [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet]

end Recursion

variable {p f : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- **Lang's theorem over `k⟦X⟧`.** Over an algebraically closed field `k` of characteristic `p`,
let `σ x = x ^ p ^ f` with `f ≠ 0` be the Frobenius, acting on `k⟦X⟧` coefficientwise and on
matrices entrywise. Then every invertible matrix `A` over `k⟦X⟧` is `B σ(B)⁻¹` for an invertible
matrix `B` over `k⟦X⟧`: `A σ(B) = B`. -/
theorem exists_isUnit_mul_map_iterateFrobenius_eq (hf : f ≠ 0) {A : Matrix n n k⟦X⟧}
    (hA : IsUnit A) :
    ∃ B : Matrix n n k⟦X⟧, IsUnit B ∧ A * B.map (map (iterateFrobenius k p f)) = B := by
  set σ := iterateFrobenius k p f
  have hq : 1 < p ^ f := Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt
  -- the constant term `B₀`, from Lang's theorem over `k`
  obtain ⟨B₀, hB₀, hAB₀⟩ := Matrix.exists_isUnit_mul_map_iterateFrobenius_eq hf
    (hA.map (constantCoeff (R := k)).mapMatrix)
  rw [RingHom.mapMatrix_apply] at hAB₀
  have hdet : IsUnit B₀.det := (Matrix.isUnit_iff_isUnit_det B₀).1 hB₀
  set B : Matrix n n k⟦X⟧ := of fun i j ↦ mk fun m ↦ langCoeff p f A B₀ m i j
  have hB (m : ℕ) : B.map (coeff m) = langCoeff p f A B₀ m := by
    ext i j
    simp [B]
  have hB0 : B.map constantCoeff = B₀ := by
    rw [← coeff_zero_eq_constantCoeff, hB 0, langCoeff]
  refine ⟨B, ?_, matrix_ext fun m ↦ ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
      RingHom.mapMatrix_apply, hB0]
    exact hdet
  have hσB (j : ℕ) : (B.map (map σ)).map (coeff j) = (langCoeff p f A B₀ j).map σ := by
    rw [← hB]
    ext
    simp
  rw [map_coeff_matrix_mul]
  simp only [hσB]
  rcases m with _ | m
  · rw [Finset.Nat.antidiagonal_zero, sum_singleton, hB 0, coeff_zero_eq_constantCoeff]
    simpa only [langCoeff] using hAB₀
  · rw [Finset.Nat.sum_antidiagonal_succ, hB, coeff_zero_eq_constantCoeff]
    exact langCoeff_succ hf hq hAB₀ hdet m

end PowerSeries
