/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Polynomials in two variables

For `φ : MvPolynomial (Fin 2) R` the monomial with exponent `s : Fin 2 →₀ ℕ` is
`X₀ ^ s 0 * X₁ ^ s 1`, of degree `s 0 + s 1`.  This file records the evaluation of `φ` at a pair
`(a, b)` as a sum over these monomials, and the description of the total degree of `φ` as the
largest `s 0 + s 1` over its support.  These are the forms in which a plane curve equation
`φ(x, y) = 0` of degree `n` is manipulated term by term.

## Main results

* `MvPolynomial.aeval_fin_two_eq_sum`: `φ(a, b) = ∑ₛ cₛ a ^ s 0 b ^ s 1`.
* `MvPolynomial.add_le_totalDegree_of_mem_support`: every monomial of `φ` has degree at most the
  total degree of `φ`.
* `MvPolynomial.exists_mem_support_add_eq_totalDegree`: a nonzero `φ` has a monomial of degree
  exactly its total degree.
* `MvPolynomial.exists_sum_coeff_mul_pow_ne_zero`: over a field with more than `deg φ` elements,
  the leading form `φ_n` of `φ` satisfies `φ_n(c, 1) ≠ 0` for some `c`.
* `MvPolynomial.natDegree_minpoly_le_totalDegree`: if `φ(u + c y, y) = 0` with `u ∈ K` and
  `φ_n(c, 1) ≠ 0`, then `y` has degree at most `deg φ` over `K`.
-/

public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- A polynomial in two variables evaluated at `(a, b)` is the sum of its terms
`c_s a ^ s 0 b ^ s 1`. -/
theorem aeval_fin_two_eq_sum {A : Type*} [CommSemiring A] [Algebra R A]
    (φ : MvPolynomial (Fin 2) R) (a b : A) :
    aeval ![a, b] φ = ∑ s ∈ φ.support, algebraMap R A (φ.coeff s) * (a ^ s 0 * b ^ s 1) := by
  rw [aeval_def, eval₂_eq']
  simp [Fin.prod_univ_two]

/-- Every monomial of a polynomial in two variables has degree at most its total degree. -/
theorem add_le_totalDegree_of_mem_support {φ : MvPolynomial (Fin 2) R} {s : Fin 2 →₀ ℕ}
    (hs : s ∈ φ.support) : s 0 + s 1 ≤ φ.totalDegree := by
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using le_totalDegree hs

/-- A nonzero polynomial in two variables has a monomial whose degree is its total degree. -/
theorem exists_mem_support_add_eq_totalDegree {φ : MvPolynomial (Fin 2) R} (hφ : φ ≠ 0) :
    ∃ s ∈ φ.support, s 0 + s 1 = φ.totalDegree := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup φ.support
    (Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hφ)) fun s ↦ s.sum fun _ e ↦ e
  exact ⟨s, hs, by simpa [totalDegree, Finsupp.sum_fintype, Fin.sum_univ_two] using hsup.symm⟩

section Field

variable {k : Type*} [Field k]

open scoped Polynomial

/-- Over a field with more than `n` elements, the leading form `φ_n` of a nonzero polynomial `φ`
of total degree `n` satisfies `φ_n(c, 1) ≠ 0` for some `c`. -/
theorem exists_sum_coeff_mul_pow_ne_zero {φ : MvPolynomial (Fin 2) k} (hφ : φ ≠ 0)
    (hcard : (φ.totalDegree : ℕ∞) < ENat.card k) :
    ∃ c : k, ∑ s ∈ φ.support with s 0 + s 1 = φ.totalDegree, φ.coeff s * c ^ s 0 ≠ 0 := by
  classical
  set n := φ.totalDegree
  -- The dehomogenized leading form `φ_n(X, 1)`.
  let g : k[X] := ∑ s ∈ φ.support with s 0 + s 1 = n, Polynomial.C (φ.coeff s) * Polynomial.X ^ s 0
  have hdeg : g.natDegree ≤ n := Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := (Finset.mem_filter.1 hs).2; omega)
  -- A monomial `s₀` of top degree contributes the coefficient of `X ^ s₀ 0` alone.
  obtain ⟨s₀, hs₀, hs₀n⟩ := exists_mem_support_add_eq_totalDegree hφ
  have hs₀S : s₀ ∈ φ.support.filter fun s ↦ s 0 + s 1 = n := Finset.mem_filter.2 ⟨hs₀, hs₀n⟩
  have hg : g ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.coeff · (s₀ 0)) h0
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single s₀ (fun s hs hne ↦ ite_eq_right_iff.mpr fun h ↦ (hne ?_).elim)
      (fun h ↦ (h hs₀S).elim)] at this
    · simp only [↓reduceIte] at this
      exact (MvPolynomial.mem_support_iff.mp hs₀) this
    · have h1 := (Finset.mem_filter.1 hs).2
      have h2 := (Finset.mem_filter.1 hs₀S).2
      ext i
      fin_cases i <;> simp <;> omega
  obtain ⟨c, hc⟩ := g.exists_eval_ne_zero_of_natDegree_lt_card hg
    (lt_of_le_of_lt (Nat.cast_le.mpr hdeg) (Cardinal.natCast_lt_toENat.mp hcard))
  exact ⟨c, by simpa [g, Polynomial.eval_finsetSum] using hc⟩

/-- If `φ(u + c y, y) = 0` with `u ∈ K` and the leading form of `φ` does not vanish at `(c, 1)`,
then `y` has degree at most `deg φ` over `K`: it is a root of `φ(u + c Y, Y)`, whose coefficient of
`Y ^ n` is `φ_n(c, 1)`. -/
theorem natDegree_minpoly_le_totalDegree {K F : Type*} [Field K] [Field F] [Algebra k K]
    [Algebra K F] [Algebra k F] [IsScalarTower k K F] {φ : MvPolynomial (Fin 2) k} {u : K} {y : F}
    {c : k} (hφ : aeval ![algebraMap K F u + algebraMap k F c * y, y] φ = 0)
    (hc : ∑ s ∈ φ.support with s 0 + s 1 = φ.totalDegree, φ.coeff s * c ^ s 0 ≠ 0) :
    (minpoly K y).natDegree ≤ φ.totalDegree := by
  classical
  set n := φ.totalDegree
  let L : K[X] := Polynomial.C (algebraMap k K c) * Polynomial.X +
    Polynomial.C u
  let ψ : K[X] := ∑ s ∈ φ.support,
    Polynomial.C (algebraMap k K (φ.coeff s)) * (L ^ s 0 * Polynomial.X ^ s 1)
  have hL : L.natDegree ≤ 1 := Polynomial.natDegree_linear_le
  have hterm : ∀ s : Fin 2 →₀ ℕ, (L ^ s 0 * Polynomial.X ^ s 1).natDegree ≤ s 0 + s 1 :=
    fun s ↦ Polynomial.natDegree_mul_le.trans (add_le_add
      ((Polynomial.natDegree_pow_le_of_le _ hL).trans (by rw [mul_one]))
      (Polynomial.natDegree_X_pow_le _))
  have hψdeg : ψ.natDegree ≤ n := Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦
    (Polynomial.natDegree_C_mul_le _ _).trans
      ((hterm s).trans (add_le_totalDegree_of_mem_support hs))
  have hcoeff : ψ.coeff n =
      algebraMap k K (∑ s ∈ φ.support with s 0 + s 1 = n, φ.coeff s * c ^ s 0) := by
    rw [Polynomial.finsetSum_coeff, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Polynomial.coeff_C_mul]
    split_ifs with hsn
    · have hpow := Polynomial.coeff_pow_of_natDegree_le (m := s 0) hL
      rw [mul_one] at hpow
      rw [← hsn, Polynomial.coeff_mul_X_pow, hpow]
      simp [L]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hterm s).trans_lt
        (lt_of_le_of_ne (add_le_totalDegree_of_mem_support hs) hsn)), mul_zero]
  have hψ0 : ψ ≠ 0 := fun h ↦ hc <| (algebraMap k K).injective <| by
    rw [← hcoeff, h, Polynomial.coeff_zero, map_zero]
  have hψy : Polynomial.aeval y ψ = 0 := by
    rw [← hφ, aeval_fin_two_eq_sum]
    simp [ψ, L, ← IsScalarTower.algebraMap_apply, add_comm]
  exact (Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero _ y hψ0 hψy)).trans hψdeg

end Field

end MvPolynomial
