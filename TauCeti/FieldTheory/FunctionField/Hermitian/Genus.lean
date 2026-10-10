/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hermitian.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.FunctionField.Radical.Genus
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.FunctionField.Divisor.RatFunc
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.FieldTheory.FunctionField.Different.Radical
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# The genus of a Hermitian function field

For Hermitian coordinates `y ^ q + y = x ^ (q + 1)`, with `q > 1` and `q = 0` in the
constant field, the exact constant field is `K` and the genus is `q(q - 1)/2`.
The projection to `y` is a tame radical extension of degree `q + 1`. Its radicand
`T ^ q + T` is squarefree, and its zeros and its pole at infinity are totally ramified.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 6.4 and Proposition 3.7.3.
-/

public section

open Polynomial
open TauCeti.AlgebraicGeometry
open scoped IntermediateField

namespace TauCeti.IsHermitianCoordinates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {q : ℕ} {x y : F} (h : IsHermitianCoordinates K q x y)
include h

omit h in
private theorem radicand_degree (hq : 1 < q) : (X ^ q + X : K[X]).natDegree = q := by
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using hq

omit h in
private theorem radicand_squarefree (hchar : (q : K) = 0) : Squarefree (X ^ q + X : K[X]) := by
  simpa using
    (separable_C_mul_X_pow_add_C_mul_X_add_C (1 : K) 1 0 hchar isUnit_one).squarefree

omit h in
private noncomputable def radicandUnit (hchar : (q : K) = 0) : (RatFunc K)ˣ :=
  Units.mk0 (algebraMap K[X] (RatFunc K) (X ^ q + X))
    (RatFunc.algebraMap_ne_zero (radicand_squarefree hchar).ne_zero)

omit h in
private theorem radicandUnit_val (hchar : (q : K) = 0) :
    (radicandUnit hchar : RatFunc K) = algebraMap K[X] (RatFunc K) (X ^ q + X) := rfl

section RationalBase

variable (hq : 1 < q)

private theorem rational_adjoin_eq_top :
    let := ratFuncAlgebraOfTranscendental h.transcendental_y
    (RatFunc K)⟮x⟯ = ⊤ := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  let := isScalarTower_ratFuncAlgebraOfTranscendental h.transcendental_y
  have htop := IntermediateField.adjoin_eq_top_of_adjoin_eq_top
    (E := RatFunc K) K h.adjoin_eq_top
  apply top_le_iff.mp
  rw [← htop, IntermediateField.adjoin_le_iff]
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact IntermediateField.mem_adjoin_simple_self _ _
  · have hz' : z = y := Set.mem_singleton_iff.mp hz
    subst z
    simpa using (IntermediateField.algebraMap_mem (RatFunc K)⟮x⟯ RatFunc.X)

private theorem rational_equation :
    let := ratFuncAlgebraOfTranscendental h.transcendental_y
    x ^ (q + 1) = algebraMap (RatFunc K) F
      (algebraMap K[X] (RatFunc K) (X ^ q + X)) := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  simpa [map_add, map_pow, RatFunc.algebraMap_X] using h.equation.symm

private theorem rational_finrank (hq : 1 < q) :
    let := ratFuncAlgebraOfTranscendental h.transcendental_y
    Module.finrank (RatFunc K) F = q + 1 := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  refine (Place.infty K).valuation.finrank_eq_of_pow_eq_of_gcd_ord_eq_one
    h.rational_adjoin_eq_top h.rational_equation (by omega) ?_
  rw [Valuation.ord_def, ← Place.ord_def, Place.ord_infty, RatFunc.intDegree_polynomial,
    radicand_degree hq]
  rw [Int.gcd_neg, Int.gcd_natCast_natCast]
  simp

private theorem rational_finiteDimensional (hq : 1 < q) :
    let := ratFuncAlgebraOfTranscendental h.transcendental_y
    FiniteDimensional (RatFunc K) F := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  exact Module.finite_of_finrank_pos (by rw [h.rational_finrank hq]; omega)

private theorem rational_separable (hchar : (q : K) = 0) :
    let := ratFuncAlgebraOfTranscendental h.transcendental_y
    Algebra.IsSeparable (RatFunc K) F := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  let a := algebraMap K[X] (RatFunc K) (X ^ q + X)
  have ha : a ≠ 0 := RatFunc.algebraMap_ne_zero (radicand_squarefree hchar).ne_zero
  have hn : ((q + 1 : ℕ) : RatFunc K) ≠ 0 := by
    have hc := congrArg (algebraMap K (RatFunc K)) hchar
    simp only [map_natCast, map_zero] at hc
    simp [Nat.cast_add, hc]
  have he : aeval x (X ^ (q + 1) - C a) = 0 := by
    simpa [a] using sub_eq_zero.mpr h.rational_equation
  have hs : IsSeparable (RatFunc K) x :=
    (separable_X_pow_sub_C a hn ha).of_dvd (minpoly.dvd _ _ he)
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hs
  rw [h.rational_adjoin_eq_top] at this
  exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv

/-- A Hermitian equation with `q = 0` in `K` acquires no new constants. -/
theorem isIntegrallyClosedIn (hq : 1 < q) (hchar : (q : K) = 0) : IsIntegrallyClosedIn K F := by
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  let := isScalarTower_ratFuncAlgebraOfTranscendental h.transcendental_y
  let := h.rational_finiteDimensional hq
  let := h.rational_separable hchar
  obtain ⟨P, hP⟩ := Place.restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc K)
    (h.isFunctionField hq) (Place.infty K)
  replace hP : P.restrict K (RatFunc K) = Place.infty K := hP
  refine isIntegrallyClosedIn_of_isTotallyRamified (F := RatFunc K) inferInstance (P' := P) ?_
  rw [Place.isTotallyRamified_iff, h.rational_finrank hq,
    Place.ramificationIdx_eq_of_pow_eq K (RatFunc K) h.rational_adjoin_eq_top
      h.rational_equation (by simp [hchar])
      (RatFunc.algebraMap_ne_zero (radicand_squarefree hchar).ne_zero), hP,
    Place.ord_infty, RatFunc.intDegree_polynomial, radicand_degree hq]
  rw [Int.gcd_neg, Int.gcd_natCast_natCast]
  simp

end RationalBase

omit h in
private theorem radicand_ord (hchar : (q : K) = 0)
    (P : Place K (RatFunc K)) (hP : P ≠ Place.infty K) :
    P.ord (algebraMap K[X] (RatFunc K) (X ^ q + X)) = 0 ∨
      P.ord (algebraMap K[X] (RatFunc K) (X ^ q + X)) = 1 := by
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨r, hr, rfl⟩
  · exact (hP rfl).elim
  · rw [Place.ord_adicOfIrreducible_algebraMap_of_squarefree hr (radicand_squarefree hchar)]
    split_ifs <;> simp

omit h in
private theorem radicand_branch_sum [DecidableEq (Place K (RatFunc K))]
    (hq : 1 < q) (hchar : (q : K) = 0) :
    let z := radicandUnit hchar
    let Z := Divisor.zeros (IsFunctionField.ratFunc K) z
    ∑ P ∈ insert (Place.infty K) Z.support,
      ((q + 1 : ℕ) - (Int.gcd (q + 1) (P.ord (z : RatFunc K))) : ℤ) * P.degree =
      (q : ℤ) * (q + 1) := by
  classical
  dsimp only
  let z := radicandUnit hchar
  let Z := Divisor.zeros (IsFunctionField.ratFunc K) z
  have hinf : (Place.infty K).ord (z : RatFunc K) = -(q : ℤ) := by
    rw [radicandUnit_val, Place.ord_infty, RatFunc.intDegree_polynomial, radicand_degree hq]
  have hnot : Place.infty K ∉ Z.support := by
    rw [Divisor.mem_support_zeros_iff, hinf]
    omega
  have hord (P : Place K (RatFunc K)) (hP : P ∈ Z.support) : P.ord (z : RatFunc K) = 1 := by
    have hpos := (Divisor.mem_support_zeros_iff (IsFunctionField.ratFunc K)).mp hP
    have hne : P ≠ Place.infty K := fun he ↦ hnot (he ▸ hP)
    have hh : P.ord (z : RatFunc K) = 0 ∨ P.ord (z : RatFunc K) = 1 :=
      radicand_ord hchar P hne
    exact hh.resolve_left (by omega)
  have hdeg : Divisor.degree Z = q := by
    simpa only [Z, z, radicandUnit, radicand_degree hq] using
      Divisor.degree_zeros_algebraMap (radicand_squarefree hchar).ne_zero
  -- Squarefreeness makes each zero order one, so this is the unweighted zero-place sum.
  have hsum : ∑ P ∈ Z.support, (P.degree : ℤ) = q := by
    rw [Divisor.degree_apply, Finsupp.sum] at hdeg
    convert hdeg using 1
    apply Finset.sum_congr rfl
    intro P hP
    rw [← WeilDivisor.coeff, Divisor.coeff_zeros, hord P hP]
    simp
  -- Infinity contributes q; the finite zeros contribute q times their total degree q.
  have hcop : Int.gcd ((q : ℤ) + 1) q = 1 := by
    have hh : Int.gcd (q + 1 : ℕ) (q : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      simp
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  rw [Finset.sum_insert hnot, hinf, Int.gcd_neg, hcop, Place.degree_infty]
  simp only [Nat.cast_one, mul_one]
  have hfinite : (∑ P ∈ Z.support,
      ((q + 1 : ℕ) - Int.gcd (q + 1) (P.ord (z : RatFunc K)) : ℤ) * P.degree) =
      q * (q : ℤ) := by
    calc
      _ = ∑ P ∈ Z.support, (q : ℤ) * P.degree := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [hord P hP]
        simp
      _ = q * (q : ℤ) := by rw [← Finset.mul_sum, hsum]
  rw [hfinite]
  push_cast
  ring

/-- **The Hermitian genus formula**: `2g = q(q - 1)` when `q > 1` and `q = 0` in `K`. -/
theorem two_mul_genus_eq (hq : 1 < q) (hchar : (q : K) = 0) :
    2 * genus K F = q * (q - 1) := by
  classical
  let := ratFuncAlgebraOfTranscendental h.transcendental_y
  let := isScalarTower_ratFuncAlgebraOfTranscendental h.transcendental_y
  let := h.rational_finiteDimensional hq
  let := h.rational_separable hchar
  let z := radicandUnit hchar
  let Z := Divisor.zeros (IsFunctionField.ratFunc K) z
  let S := insert (Place.infty K) Z.support
  have hS (P : Place K (RatFunc K)) (hP : P ∉ S) : (q + 1 : ℤ) ∣ P.ord (z : RatFunc K) := by
    have hne : P ≠ Place.infty K := fun he ↦ hP (by simp [S, he])
    have hnpos : ¬ 0 < P.ord (z : RatFunc K) := by
      intro hh
      exact hP (Finset.mem_insert_of_mem ((Divisor.mem_support_zeros_iff _).mpr hh))
    have hh : P.ord (z : RatFunc K) = 0 ∨ P.ord (z : RatFunc K) = 1 :=
      radicand_ord hchar P hne
    have hz := hh.resolve_right (by omega)
    rw [hz]
    exact dvd_zero _
  have hg := genus_formula_of_pow_eq (k' := K) (F' := F) (IsFunctionField.ratFunc K)
    h.rational_adjoin_eq_top h.rational_equation (by simp [hchar])
    (RatFunc.algebraMap_ne_zero (radicand_squarefree hchar).ne_zero) S hS
    (h.isFunctionField hq) inferInstance (h.isIntegrallyClosedIn hq hchar) (h.rational_finrank hq)
  rw [Module.finrank_self, genus_ratFunc] at hg
  have hsum : ∑ P ∈ S,
      ((q + 1 : ℕ) - Int.gcd (q + 1) (P.ord
        (algebraMap K[X] (RatFunc K) (X ^ q + X))) : ℤ) * P.degree =
      (q : ℤ) * (q + 1) := radicand_branch_sum hq hchar
  simp only [Nat.cast_add, Nat.cast_one] at hg hsum
  rw [hsum] at hg
  have hq1 : 1 ≤ q := by omega
  have hg' : (2 * genus K F : ℤ) = (q : ℤ) * (q - 1 : ℕ) := by
    push_cast at hg ⊢
    rw [Nat.cast_sub hq1]
    norm_num at hg ⊢
    nlinarith
  exact_mod_cast hg'

/-- A Hermitian function field with parameter at least three has genus at least two. -/
theorem two_le_genus (hq : 3 ≤ q) (hchar : (q : K) = 0) : 2 ≤ genus K F := by
  have hg := h.two_mul_genus_eq (by omega) hchar
  have hq1 := Nat.sub_add_cancel (by omega : 1 ≤ q)
  nlinarith

end TauCeti.IsHermitianCoordinates
