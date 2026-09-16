/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.Algebra.Quaternion.Split
public import TauCeti.Algebra.Quaternion.SymbolEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The splitting criterion for quaternion algebras

Over a field `K` in which `2` is invertible, a quaternion algebra `ℍ[K,a,b]` with `a, b ∈ Kˣ` is
either a division algebra or isomorphic to the matrix algebra `M₂(K)`, and which case occurs is
decided by quadratic forms. This file proves the classical criterion: the following are equivalent.

1. `ℍ[K,a,b]` splits, that is `ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K`;
2. `b` is a norm from the quadratic algebra `K[√a] = QuadraticAlgebra K a 0`;
3. `b = x² - a y²` for some `x, y ∈ K`;
4. the ternary form `⟨1, -a, -b⟩` is isotropic;
5. the norm form `⟨1, -a, -b, ab⟩` of `ℍ[K,a,b]` is isotropic.

No hypothesis that `a` is a nonsquare is needed: when `a` is a square the form `x² - a y²` is
universal and all five conditions hold.

The arguments are elementary. A quaternion is invertible exactly when its norm is
(`QuaternionAlgebra.anisotropic_normForm_iff`), so `ℍ[K,a,b]` is a division algebra exactly
when its norm form is anisotropic; since `M₂(K)` has nonzero non-invertible elements, a split
algebra has an isotropic norm form. An isotropic vector `t + u i + v j + w k` of the norm form gives
`t² - a u² = b (v² - a w²)`, and dividing in `K[√a]` exhibits `b` as a norm. Conversely, if
`b = N(z)` then `TauCeti.QuaternionAlgebra.normMulEquiv` identifies `ℍ[K,a,b]` with `ℍ[K,a,1]`,
which is split by `TauCeti.QuaternionAlgebra.oneEquivMatrix`.

## Main results

* `TauCeti.exists_eq_sq_sub_mul_sq_of_isSquare`: `x² - a y²` is universal when `a` is a square
  unit.
* `TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_tfae`: the splitting criterion.
* `TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_forall_isUnit` and
  `TauCeti.QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix`: `ℍ[K,a,b]` is split
  exactly when it is not a division algebra.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, Theorems 2.7 and
  4.2 (Lam writes `⟨⟨a,b⟩⟩` for the norm form and `(a,b)` for the algebra).
* J.-P. Serre, *A Course in Arithmetic* (1973), Chapter III, Proposition 1.
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), Proposition 1.1.7
  and Corollary 1.1.9.
-/

public section

open QuadraticMap

open scoped Quaternion

namespace TauCeti

section Universal

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- **The norm form of a split quadratic algebra is universal.** If `a` is the square of a unit,
then every `b` is of the form `x² - a y²`: explicitly `x = (b + 1) / 2` and `y = (b - 1) / (2 s)`
for `a = s²`. -/
theorem exists_eq_sq_sub_mul_sq_of_isSquare {a : R} (ha : IsSquare a) (ha' : IsUnit a) (b : R) :
    ∃ x y : R, b = x ^ 2 - a * y ^ 2 := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨s, rfl⟩ := isUnit_mul_self_iff.mp ha'
  refine ⟨⅟(2 : R) * (b + 1), ⅟(2 : R) * (b - 1) * ((s⁻¹ : Rˣ) : R), ?_⟩
  linear_combination (-b * (2 * ⅟(2 : R) + 1)) * invOf_mul_self (2 : R) +
    (⅟(2 : R) ^ 2 * (b - 1) ^ 2 * (s * (s⁻¹ : Rˣ) + 1)) * s.mul_inv

end Universal

namespace QuaternionAlgebra

variable {K : Type*} [Field K]

/-- Over a field, `p² - a q²` vanishes only at `p = q = 0` when `a` is not a square. -/
private theorem eq_zero_of_sq_sub_mul_sq_eq_zero {a p q : K} (ha : ¬IsSquare a)
    (h : p ^ 2 - a * q ^ 2 = 0) : p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · subst hq
    exact ⟨by simpa using h, rfl⟩
  · exact (ha ⟨p / q, by field_simp; linear_combination -h⟩).elim

variable [Invertible (2 : K)]

/-- An isotropic norm form of `ℍ[K,a,b]` exhibits `b` in the form `x² - a y²`. -/
private theorem exists_eq_sq_sub_mul_sq_of_not_anisotropic_normForm {a b : K} (ha : a ≠ 0)
    (h : ¬(_root_.QuaternionAlgebra.normForm a 0 b).Anisotropic) :
    ∃ x y : K, b = x ^ 2 - a * y ^ 2 := by
  by_cases hsq : IsSquare a
  · exact exists_eq_sq_sub_mul_sq_of_isSquare hsq ha.isUnit b
  simp only [Anisotropic, not_forall] at h
  obtain ⟨q, hq, hq0⟩ := h
  rw [_root_.QuaternionAlgebra.normForm_apply_coordinates] at hq
  -- `t² - a u² = b (v² - a w²)`, and `v² - a w²` is nonzero since `a` is not a square.
  have hn : q.imJ ^ 2 - a * q.imK ^ 2 ≠ 0 := by
    intro hn
    obtain ⟨hv, hw⟩ := eq_zero_of_sq_sub_mul_sq_eq_zero hsq hn
    obtain ⟨ht, hu⟩ := eq_zero_of_sq_sub_mul_sq_eq_zero (p := q.re) (q := q.imI) hsq
      (by rw [hv, hw] at hq; linear_combination hq)
    exact hq0 (_root_.QuaternionAlgebra.ext ht hu hv hw)
  refine ⟨(q.re * q.imJ - a * q.imI * q.imK) / (q.imJ ^ 2 - a * q.imK ^ 2),
    (q.imI * q.imJ - q.re * q.imK) / (q.imJ ^ 2 - a * q.imK ^ 2), ?_⟩
  field_simp
  linear_combination (-(q.imJ ^ 2 - a * q.imK ^ 2)) * hq

/-- An isotropic ternary form `⟨1, -a, -b⟩` exhibits `b` in the form `x² - a y²`. -/
private theorem exists_eq_sq_sub_mul_sq_of_not_anisotropic {a b : K} (ha : a ≠ 0)
    (h : ¬(weightedSumSquares K ![1, -a, -b]).Anisotropic) :
    ∃ x y : K, b = x ^ 2 - a * y ^ 2 := by
  by_cases hsq : IsSquare a
  · exact exists_eq_sq_sub_mul_sq_of_isSquare hsq ha.isUnit b
  simp only [Anisotropic, not_forall] at h
  obtain ⟨v, hv, hv0⟩ := h
  simp only [weightedSumSquares_apply, smul_eq_mul, Fin.sum_univ_three, Matrix.cons_val_zero,
    one_mul, Matrix.cons_val_one, neg_mul, Matrix.cons_val] at hv
  by_cases h2 : v 2 = 0
  · obtain ⟨h0, h1⟩ := eq_zero_of_sq_sub_mul_sq_eq_zero (p := v 0) (q := v 1) hsq
      (by rw [h2] at hv; linear_combination hv)
    exact (hv0 (by ext i; fin_cases i <;> simp [h0, h1, h2])).elim
  · refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
    field_simp
    linear_combination -hv

variable (a b : Kˣ)

/-- **The splitting criterion for quaternion algebras** (Lam III.2.7 and III.4.2, Serre III.1,
Gille-Szamuely 1.1.9). For units `a` and `b` of a field in which `2` is invertible, the following
are equivalent:
1. `ℍ[K,a,b]` is isomorphic to `M₂(K)`;
2. `b` is a norm from `K[√a] = QuadraticAlgebra K a 0`;
3. `b = x² - a y²` for some `x, y ∈ K`;
4. the ternary form `⟨1, -a, -b⟩` is isotropic;
5. the norm form of `ℍ[K,a,b]`, that is `⟨1, -a, -b, ab⟩`, is isotropic. -/
theorem nonempty_algEquiv_matrix_tfae :
    [Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K),
      ∃ z : QuadraticAlgebra K (a : K) 0, z.norm = b,
      ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2,
      ¬(weightedSumSquares K ![1, -(a : K), -(b : K)]).Anisotropic,
      ¬(_root_.QuaternionAlgebra.normForm (a : K) 0 (b : K)).Anisotropic].TFAE := by
  tfae_have 1 → 5 := by
    rintro ⟨f⟩ h
    rw [_root_.QuaternionAlgebra.anisotropic_normForm_iff] at h
    have hs : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K) ≠ 0 := fun h => by
      simpa using congrFun₂ h 0 0
    have hx := (h (f.symm (Matrix.single 0 0 1)) (by simpa using hs)).map f
    simp [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two] at hx
  tfae_have 5 → 3 := exists_eq_sq_sub_mul_sq_of_not_anisotropic_normForm a.ne_zero
  tfae_have 3 → 2 := fun ⟨x, y, h⟩ => ⟨⟨x, y⟩, by
    rw [QuadraticAlgebra.norm_def, h]; ring⟩
  tfae_have 2 → 1 := by
    rintro ⟨z, hz⟩
    have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ b.isUnit)
    have hb : (b : K) = (hu.unit : QuadraticAlgebra K (a : K) 0).norm * (1 : Kˣ) := by
      simp [hz]
    rw [hb]
    exact ⟨((normMulEquiv _ _ hu.unit).trans
      (_root_.QuaternionAlgebra.swapEquiv (a : K) ((1 : Kˣ) : K))).trans (oneEquivMatrix a)⟩
  tfae_have 3 → 4 := by
    rintro ⟨x, y, h⟩ hQ
    have := hQ ![x, y, 1] (by
      simp [weightedSumSquares_apply, Fin.sum_univ_three, h]
      ring)
    simpa using congrFun this 2
  tfae_have 4 → 3 := exists_eq_sq_sub_mul_sq_of_not_anisotropic a.ne_zero
  tfae_finish

/-- `ℍ[K,a,b]` is split exactly when `b` is a norm from `K[√a]`. -/
theorem nonempty_algEquiv_matrix_iff_exists_norm_eq :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔
      ∃ z : QuadraticAlgebra K (a : K) 0, z.norm = b :=
  (nonempty_algEquiv_matrix_tfae a b).out 1 2

/-- `ℍ[K,a,b]` is split exactly when `b = x² - a y²` is solvable. -/
theorem nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔
      ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 :=
  (nonempty_algEquiv_matrix_tfae a b).out 1 3

/-- `ℍ[K,a,b]` is split exactly when `⟨1, -a, -b⟩` is isotropic. -/
theorem nonempty_algEquiv_matrix_iff_not_anisotropic_weightedSumSquares :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔
      ¬(weightedSumSquares K ![1, -(a : K), -(b : K)]).Anisotropic :=
  (nonempty_algEquiv_matrix_tfae a b).out 1 4

/-- `ℍ[K,a,b]` is split exactly when its norm form is isotropic. -/
theorem nonempty_algEquiv_matrix_iff_not_anisotropic_normForm :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔
      ¬(_root_.QuaternionAlgebra.normForm (a : K) 0 (b : K)).Anisotropic :=
  (nonempty_algEquiv_matrix_tfae a b).out 1 5

/-- **Split or division** (Lam III.2.7). `ℍ[K,a,b]` is split exactly when it is not a division
algebra. -/
theorem nonempty_algEquiv_matrix_iff_not_forall_isUnit :
    Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔
      ¬∀ x : ℍ[K,(a : K),(b : K)], x ≠ 0 → IsUnit x := by
  rw [nonempty_algEquiv_matrix_iff_not_anisotropic_normForm,
    _root_.QuaternionAlgebra.anisotropic_normForm_iff]

/-- **Split or division.** Every quaternion algebra `ℍ[K,a,b]` is a division algebra or is
isomorphic to `M₂(K)`. -/
theorem forall_isUnit_or_nonempty_algEquiv_matrix :
    (∀ x : ℍ[K,(a : K),(b : K)], x ≠ 0 → IsUnit x) ∨
      Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :=
  or_iff_not_imp_left.mpr (nonempty_algEquiv_matrix_iff_not_forall_isUnit a b).mpr

end QuaternionAlgebra

end TauCeti
