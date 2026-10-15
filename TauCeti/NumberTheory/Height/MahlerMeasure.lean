/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.MahlerMeasure
public import TauCeti.FieldTheory.Minpoly.Primitive

import Mathlib.Analysis.Complex.IsIntegral

/-!
# The Mahler measure of an algebraic number

For an element `x` of a field of characteristic zero, the Mahler measure `M(x)` is the Mahler
measure of its primitive minimal polynomial `F_x ∈ ℤ[X]`, mapped to `ℂ[X]`. For algebraic `x` of
degree `d` with conjugates `x⁽¹⁾, …, x⁽ᵈ⁾ ∈ ℂ` this is
`M(x) = a₀ ∏ᵢ max(1, |x⁽ⁱ⁾|)`: the positive integer leading coefficient `a₀` of `F_x` times the
product of `max(1, |x⁽ⁱ⁾|)` over the conjugates. Keeping the leading coefficient gives
`M(p/q) = max(|p|, q)` for a rational number in lowest terms. For transcendental `x` the value is
`1`.

The definition needs no complex embedding of the ambient field: only the polynomial `F_x` is
mapped to `ℂ`. Consequently `M(x)` is constant on conjugacy classes and invariant under field
embeddings. Together with the naive and absolute heights, the Mahler measure is one of the
classical size functions on algebraic numbers used in Liouville- and Roth-type approximation
estimates and in Northcott finiteness.

## Main definitions

* `TauCeti.mahlerMeasure x`: the Mahler measure of `x`.

## Main results

* `TauCeti.mahlerMeasure_eq_leadingCoeff_mul_prod`: `M(x) = a₀ ∏ max(1, |z|)` over the complex
  roots `z` of `minpoly ℚ x`, counted with multiplicity.
* `TauCeti.leadingCoeff_le_mahlerMeasure`, `TauCeti.one_le_mahlerMeasure`: `1 ≤ a₀ ≤ M(x)`.
* `TauCeti.mahlerMeasure_ratCast`: `M(p/q) = max(|p|, q)`, the multiplicative height of `p/q`.
* `TauCeti.mahlerMeasure_map`, `TauCeti.mahlerMeasure_eq_of_minpoly_eq`: invariance under field
  embeddings and conjugation.
* `TauCeti.mahlerMeasure_eq_one_iff`: Kronecker's theorem, for algebraic `x`, `M(x) = 1` exactly
  when `x` is zero or a root of unity.
* `TauCeti.finite_setOf_mahlerMeasure_le`: Northcott's theorem for the Mahler measure; in every
  field of characteristic zero there are only finitely many algebraic elements of bounded degree
  and bounded Mahler measure.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, §6.1 and Theorem 6.1.
* C. Smyth, *The Mahler measure of algebraic numbers: a survey* (2008), §1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F] {F' : Type*} [Field F'] [CharZero F']

/-- The *Mahler measure* `M(x)` of `x`: the Mahler measure of its primitive minimal polynomial
`F_x`, mapped to `ℂ[X]`. For algebraic `x` this is `a₀ ∏ max(1, |x⁽ⁱ⁾|)` over the complex
conjugates of `x` (`mahlerMeasure_eq_leadingCoeff_mul_prod`); for transcendental `x` it is `1`. -/
noncomputable def mahlerMeasure (x : F) : ℝ :=
  (primitiveMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ)

/-- The Mahler measure of `x` is the Mahler measure of `F_x` mapped to `ℂ[X]`. -/
theorem mahlerMeasure_def (x : F) :
    mahlerMeasure x = ((primitiveMinpoly x).map (Int.castRingHom ℂ)).mahlerMeasure :=
  (rfl)

/-- The Mahler measure depends only on `minpoly ℚ x`: conjugates, possibly lying in different
fields, have equal Mahler measure. -/
theorem mahlerMeasure_eq_of_minpoly_eq {x : F} {y : F'} (h : minpoly ℚ x = minpoly ℚ y) :
    mahlerMeasure x = mahlerMeasure y := by
  rw [mahlerMeasure_def, mahlerMeasure_def, primitiveMinpoly_eq_of_minpoly_eq h]

/-- Field embeddings preserve the Mahler measure. -/
@[simp]
theorem mahlerMeasure_map (f : F →+* F') (x : F) : mahlerMeasure (f x) = mahlerMeasure x := by
  rw [mahlerMeasure_def, mahlerMeasure_def, primitiveMinpoly_map]

/-- Transcendental elements have Mahler measure `1`. -/
@[simp]
theorem mahlerMeasure_of_not_isAlgebraic {x : F} (hx : ¬IsAlgebraic ℚ x) :
    mahlerMeasure x = 1 := by
  rw [mahlerMeasure_def, primitiveMinpoly_of_not_isAlgebraic hx, Polynomial.map_one,
    Polynomial.mahlerMeasure_one]

/-- For algebraic `x`, the image of `F_x` in `ℂ[X]` is `a₀` times the image of `minpoly ℚ x`. -/
private lemma map_primitiveMinpoly_complex {x : F} (hx : IsAlgebraic ℚ x) :
    (primitiveMinpoly x).map (Int.castRingHom ℂ) =
      C ((primitiveMinpoly x).leadingCoeff : ℂ) * (minpoly ℚ x).map (algebraMap ℚ ℂ) := by
  have hcomp : Int.castRingHom ℂ = (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) :=
    RingHom.ext_int _ _
  rw [hcomp, ← Polynomial.map_map, map_primitiveMinpoly hx]
  simp

/-- The Mahler measure of `x` is `a₀ ∏ max(1, |z|)`, the product running over the complex roots
`z` of `minpoly ℚ x` counted with multiplicity, where `a₀` is the leading coefficient of `F_x`.
For transcendental `x` both sides are `1`. -/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod (x : F) :
    mahlerMeasure x = (primitiveMinpoly x).leadingCoeff *
      (((minpoly ℚ x).aroots ℂ).map fun z ↦ max 1 ‖z‖).prod := by
  by_cases hx : IsAlgebraic ℚ x
  · have hmon : ((minpoly ℚ x).map (algebraMap ℚ ℂ)).Monic :=
      (minpoly.monic (isAlgebraic_iff_isIntegral.mp hx)).map _
    -- `M(C a₀ * p) = |a₀| M(p)`, and `M(p)` is the product over the roots for monic `p`.
    rw [mahlerMeasure_def, map_primitiveMinpoly_complex hx, mahlerMeasure_mul, mahlerMeasure_const,
      Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hmon.leadingCoeff]
    simp [aroots_def, (leadingCoeff_primitiveMinpoly_pos x).le]
  · rw [mahlerMeasure_of_not_isAlgebraic hx, primitiveMinpoly_of_not_isAlgebraic hx,
      minpoly.eq_zero (isAlgebraic_iff_isIntegral.not.mp hx)]
    simp

/-- The leading coefficient `a₀` of `F_x` is at most the Mahler measure of `x`. -/
theorem leadingCoeff_le_mahlerMeasure (x : F) :
    ((primitiveMinpoly x).leadingCoeff : ℝ) ≤ mahlerMeasure x := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod]
  refine le_mul_of_one_le_right (by exact_mod_cast (leadingCoeff_primitiveMinpoly_pos x).le) ?_
  exact Polynomial.one_le_prod_max_one_norm_roots _

/-- The Mahler measure of every element is at least `1`. -/
theorem one_le_mahlerMeasure (x : F) : 1 ≤ mahlerMeasure x :=
  mahlerMeasure_def x ▸ one_le_mahlerMeasure_of_ne_zero (primitiveMinpoly_ne_zero x)

/-- The Mahler measure of a rational number `q` is the maximum of the absolute value of its
numerator and its denominator, independently of the field containing `q`. -/
@[simp]
theorem mahlerMeasure_ratCast (q : ℚ) :
    mahlerMeasure (q : F) = max (q.num.natAbs : ℝ) q.den := by
  have hden : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
  have hmap : (C (q.den : ℤ) * X - C q.num).map (Int.castRingHom ℂ) =
      C (q.den : ℂ) * X + C (-(q.num : ℂ)) := by simp [sub_eq_add_neg]
  rw [mahlerMeasure_def, primitiveMinpoly_ratCast, hmap,
    Polynomial.mahlerMeasure_C_mul_X_add_C hden]
  simp [max_comm]

/-- On rational numbers the Mahler measure is the multiplicative Weil height. -/
theorem mahlerMeasure_ratCast_eq_mulHeight₁ (q : ℚ) :
    mahlerMeasure (q : F) = Height.mulHeight₁ q := by
  rw [mahlerMeasure_ratCast, Rat.mulHeight₁_eq_max, Nat.cast_max]

/-- The Mahler measure of `0` is `1`. -/
@[simp]
theorem mahlerMeasure_zero : mahlerMeasure (0 : F) = 1 := by
  simpa using mahlerMeasure_ratCast (F := F) 0

/-- The Mahler measure of `1` is `1`. -/
@[simp]
theorem mahlerMeasure_one : mahlerMeasure (1 : F) = 1 := by
  simpa using mahlerMeasure_ratCast (F := F) 1

/-- **Kronecker's theorem.** An algebraic element has Mahler measure `1` exactly when it is zero
or a root of unity. -/
theorem mahlerMeasure_eq_one_iff {x : F} (hx : IsAlgebraic ℚ x) :
    mahlerMeasure x = 1 ↔ x = 0 ∨ ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  have hirr := irreducible_primitiveMinpoly hx
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [mahlerMeasure_def] at h
    by_cases hX : X ∣ primitiveMinpoly x
    · -- `F_x` is then an associate of `X`, so `x` is a root of `X`.
      left
      simpa using (primitiveMinpoly_dvd_iff hx).mp (irreducible_X.dvd_symm hirr hX)
    · -- Otherwise some cyclotomic polynomial divides `F_x`; by irreducibility `F_x` divides it
      -- back, so `x` is a primitive root of unity.
      right
      have hdeg : (primitiveMinpoly x).degree ≠ 0 := by
        rw [degree_eq_natDegree (primitiveMinpoly_ne_zero x), natDegree_primitiveMinpoly]
        exact_mod_cast (minpoly.natDegree_pos (isAlgebraic_iff_isIntegral.mp hx)).ne'
      obtain ⟨n, hn, hdvd⟩ := cyclotomic_dvd_of_mahlerMeasure_eq_one h hX hdeg
      have hroot := (primitiveMinpoly_dvd_iff hx).mp
        ((cyclotomic.irreducible hn).dvd_symm hirr hdvd)
      have hprim : IsPrimitiveRoot x n := (isRoot_cyclotomic_iff_charZero hn).mp
        (by simpa [aeval_def, eval₂_eq_eval_map] using hroot)
      exact ⟨n, hn, hprim.pow_eq_one⟩
  · rintro (rfl | ⟨n, hn, hxn⟩)
    · exact mahlerMeasure_zero
    · obtain ⟨m, hm, hprim⟩ := IsPrimitiveRoot.exists_pos hxn hn.ne'
      rw [mahlerMeasure_def, primitiveMinpoly_eq_minpoly_int (hprim.isIntegral hm),
        ← cyclotomic_eq_minpoly hprim hm, ← algebraMap_int_eq]
      exact cyclotomic_mahlerMeasure_eq_one m

/-- **Northcott's theorem for the Mahler measure.** In a field of characteristic zero, there are
only finitely many algebraic elements of degree at most `d` and Mahler measure at most `B`. -/
theorem finite_setOf_mahlerMeasure_le (d : ℕ) (B : ℝ) :
    {z : F | IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ mahlerMeasure z ≤ B}.Finite := by
  classical
  refine ((finite_mahlerMeasure_le d B.toNNReal).biUnion
    fun p _ ↦ (p.aroots F).toFinset.finite_toSet).subset ?_
  rintro z ⟨hz, hd, hB⟩
  refine Set.mem_biUnion (x := primitiveMinpoly z)
    ⟨by rwa [natDegree_primitiveMinpoly], (mahlerMeasure_def z ▸ hB).trans B.le_coe_toNNReal⟩ ?_
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_aroots]
  exact ⟨primitiveMinpoly_ne_zero z, aeval_primitiveMinpoly hz⟩

/-! ### Examples -/

/- `M(1/2) = 2`. -/
example : mahlerMeasure (((1 : ℚ) / 2 : ℚ) : ℝ) = 2 := by
  rw [mahlerMeasure_ratCast]
  norm_num

/- The Mahler measure keeps the leading coefficient: `M(1/2) = 2`, whereas the norm of `1/2`
is `1/2`. -/
example : mahlerMeasure (((1 : ℚ) / 2 : ℚ) : ℝ) ≠ |Algebra.norm ℚ ((1 : ℚ) / 2)| := by
  rw [mahlerMeasure_ratCast, Algebra.norm_self]
  norm_num

/- The root of unity `i` has Mahler measure `1`. -/
example : mahlerMeasure Complex.I = 1 :=
  (mahlerMeasure_eq_one_iff (Complex.isIntegral_I ℚ).isAlgebraic).mpr
    (Or.inr ⟨4, by norm_num, Complex.I_pow_four⟩)

end TauCeti
