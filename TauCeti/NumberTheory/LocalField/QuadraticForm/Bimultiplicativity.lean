/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.NormalizedValuation

import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.DirectIndex
import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass
import TauCeti.NumberTheory.LocalField.Squares

/-!
# The index theorem for quadratic norms, and bimultiplicativity of the local Hilbert symbol

Let `K` be a nonarchimedean local field with `2 ≠ 0`, in any residue characteristic. The norms
from `K(√a)`, that is the subgroup `N` of `Kˣ` consisting of the `b` of the form `x² - a y²` with
`x, y ∈ K`, form a subgroup of index two in `Kˣ` for every nonsquare radicand `a`.

Every nonsquare `a ∈ Kˣ` has a finite integer quadratic defect exponent `δ(a) = d ∈ ℤ`. Depending
on the parity of `d`, the index `(Kˣ : N) = 2` comes directly from the base-field arithmetic of
`TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.DirectIndex`: when `d` is even, `a` lies in the
unramified class and `N` consists of the elements of even normalized valuation
(`TauCeti.quadraticNormSubgroup_index_eq_two_of_even_defectExponent`); when `d` is odd, `N` attains
every normalized valuation while its valuation-one elements meet half the unit square classes via
the uniformizer and Eisenstein norm families
(`TauCeti.quadraticNormSubgroup_index_eq_two_of_odd_defectExponent`).

The sign indicator of an index-two subgroup is a character, so the local Hilbert symbol is
bimultiplicative in both arguments. The same index theorem gives nondegeneracy, and there that step
is purely group-theoretic: the sign indicator of a proper subgroup of index two is onto, so it takes
the value `-1` off the subgroup. The field-level statement is
`TauCeti.exists_hilbertSymbol_eq_neg_one_of_index_eq_two`, which asks only that the norm subgroup of
`a` have index two.

Nondegeneracy has two consequences for prescribing values of the symbol. Two distinct nontrivial
characters `(·, a)_K` and `(·, b)_K` of the group `Kˣ/(Kˣ)²` of exponent two take every pair of
values. And the norm group of `K(√a)` contains a nonsquare for every `a`: among a uniformizer, the
unramified unit and their product, three nonsquares, the symbols with `a` multiply to `1`.

The diagonal entry `(a, a)_K = (a, -1)_K` needs no arithmetic input and is stated for an arbitrary
field in `TauCeti.NumberTheory.HilbertSymbol.NormSubgroup`, as
`TauCeti.hilbertSymbol_self`.

## Main results

* `TauCeti.quadraticNormSubgroup_index_eq_two_of_not_isSquare`,
  `TauCeti.quadraticNormSubgroup_index_eq_two_iff_not_isSquare`, and
  `TauCeti.quadraticNormSubgroup_eq_top_iff_isSquare`: the norm index of every nonsquare radicand
  and the two-sided characterizations of index `2` and `⊤`.
* `TauCeti.hilbertSymbol_mul_right` and `TauCeti.hilbertSymbol_mul_left`: the Hilbert symbol is
  bilinear in both arguments.
* `TauCeti.exists_hilbertSymbol_eq_neg_one`,
  `TauCeti.forall_hilbertSymbol_eq_one_iff_isSquare_left`, and
  `TauCeti.forall_hilbertSymbol_eq_one_iff_isSquare_right`: nondegeneracy and triviality of both
  radicals modulo squares.
* `TauCeti.exists_hilbertSymbol_eq_and_hilbertSymbol_eq`: for nonsquares `a`, `b` with `ab` a
  nonsquare, the characters `(·, a)_K` and `(·, b)_K` take every pair of values.
* `TauCeti.exists_not_isSquare_hilbertSymbol_eq_one`: the norm group of `K(√a)` contains a
  nonsquare, for every `a`.
* `TauCeti.uncurry_hilbertSymbol_surjective`: the Hilbert symbol takes both values `±1`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter VI, §2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 2.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The norm index of a nonsquare radicand.** If `2 ≠ 0` in `K`, the norms from `K(√a)` form
a subgroup of index two in `Kˣ` for every `a` that is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_of_not_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : ¬IsSquare a) : (quadraticNormSubgroup (a : K)).index = 2 := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
  rcases Int.even_or_odd d with hev | hodd
  · exact quadraticNormSubgroup_index_eq_two_of_even_defectExponent h2 hd.symm hev
  · exact quadraticNormSubgroup_index_eq_two_of_odd_defectExponent h2 hd.symm hodd

/-- Over a nonarchimedean local field with `2 ≠ 0`, `quadraticNormSubgroup (a : K)` is all of `Kˣ`
if and only if `a` is a square. -/
theorem quadraticNormSubgroup_eq_top_iff_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    quadraticNormSubgroup (a : K) = ⊤ ↔ IsSquare a := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  refine ⟨fun htop ↦ ?_, fun ha ↦ eq_top_iff.mpr fun b _ ↦
    (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mp
      (hilbertSymbol_eq_one_of_isSquare_left ha b)⟩
  by_contra ha
  have hidx := quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha
  rw [htop, Subgroup.index_top] at hidx
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, `quadraticNormSubgroup (a : K)` has index two
in `Kˣ` if and only if `a` is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_iff_not_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).index = 2 ↔ ¬IsSquare a := by
  refine ⟨fun hidx ha ↦ ?_, quadraticNormSubgroup_index_eq_two_of_not_isSquare h2⟩
  rw [(quadraticNormSubgroup_eq_top_iff_isSquare h2).mpr ha, Subgroup.index_top] at hidx
  omega

/-- **Bimultiplicativity of the local Hilbert symbol in the second argument.** If `2 ≠ 0` in `K`,
then `(a, bc)_K = (a, b)_K (a, c)_K` for every `a`, `b` and `c`. -/
@[simp]
theorem hilbertSymbol_mul_right (h2 : (2 : K) ≠ 0) (a b c : Kˣ) :
    hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  by_cases ha : IsSquare a
  · simp [hilbertSymbol_eq_one_of_isSquare_left ha]
  · exact (hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two a).mpr
      (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha ▸ dvd_rfl) b c

/-- **Bimultiplicativity of the local Hilbert symbol in the first argument.** If `2 ≠ 0` in `K`,
then `(bc, a)_K = (b, a)_K (c, a)_K` for every `a`, `b` and `c`. -/
@[simp]
theorem hilbertSymbol_mul_left (h2 : (2 : K) ≠ 0) (a b c : Kˣ) :
    hilbertSymbol (b * c) a = hilbertSymbol b a * hilbertSymbol c a := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  -- the first-argument law is the second-argument law read through the symmetry of the symbol
  simp only [hilbertSymbol_comm _ a, hilbertSymbol_mul_right h2]

/-- The Hilbert symbol is multiplicative on integer powers of its second argument. -/
@[simp]
theorem hilbertSymbol_zpow_right (h2 : (2 : K) ≠ 0)
    (a b : Kˣ) (n : ℤ) :
    hilbertSymbol a (b ^ n) = hilbertSymbol a b ^ n := by
  let f : Kˣ →* ℤˣ :=
    { toFun := hilbertSymbol a
      map_one' := hilbertSymbol_one_right a
      map_mul' := hilbertSymbol_mul_right h2 a }
  exact map_zpow f b n

/-- The Hilbert symbol is multiplicative on integer powers of its first argument. -/
@[simp]
theorem hilbertSymbol_zpow_left (h2 : (2 : K) ≠ 0)
    (a b : Kˣ) (n : ℤ) :
    hilbertSymbol (a ^ n) b = hilbertSymbol a b ^ n := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rw [hilbertSymbol_comm, hilbertSymbol_zpow_right h2, hilbertSymbol_comm]

/-- The Hilbert symbol is multiplicative on natural-number powers of its first argument. -/
@[simp]
theorem hilbertSymbol_pow_left (h2 : (2 : K) ≠ 0)
    (a b : Kˣ) (n : ℕ) :
    hilbertSymbol (a ^ n) b = hilbertSymbol a b ^ n := by
  simpa only [zpow_natCast] using hilbertSymbol_zpow_left h2 a b n

/-- **Nondegeneracy of the local Hilbert symbol.** If `2 ≠ 0` in `K`, then for every nonsquare `a`
there is a `b ∈ Kˣ` with `(a, b)_K = -1`. It is the field-level consequence
`TauCeti.exists_hilbertSymbol_eq_neg_one_of_index_eq_two` of the norm index theorem. -/
theorem exists_hilbertSymbol_eq_neg_one (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : ¬IsSquare a) :
    ∃ b : Kˣ, hilbertSymbol a b = -1 :=
  exists_hilbertSymbol_eq_neg_one_of_index_eq_two a
    (quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 ha)

/-- **Left radical of the local Hilbert symbol.** Over a nonarchimedean local field with `2 ≠ 0`,
`(a, b)_K = 1` for every `b ∈ Kˣ` if and only if `a` is a square. -/
theorem forall_hilbertSymbol_eq_one_iff_isSquare_left (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (∀ b : Kˣ, hilbertSymbol a b = 1) ↔ IsSquare a := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  refine ⟨fun h ↦ ?_, fun ha b ↦ hilbertSymbol_eq_one_of_isSquare_left ha b⟩
  by_contra ha
  obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one h2 ha
  exact (by decide : (1 : ℤˣ) ≠ -1) ((h b).symm.trans hb)

/-- **Right radical of the local Hilbert symbol.** Over a nonarchimedean local field with `2 ≠ 0`,
`(a, b)_K = 1` for every `a ∈ Kˣ` if and only if `b` is a square. -/
theorem forall_hilbertSymbol_eq_one_iff_isSquare_right (h2 : (2 : K) ≠ 0) {b : Kˣ} :
    (∀ a : Kˣ, hilbertSymbol a b = 1) ↔ IsSquare b := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  simpa only [hilbertSymbol_comm _ b] using
    forall_hilbertSymbol_eq_one_iff_isSquare_left h2 (a := b)

/-! ### Prescribing values of the Hilbert symbol -/

/-- If `2 ≠ 0` in `K`, then for a nonsquare `a` and any `b` with `ab` a nonsquare, some `y ∈ Kˣ`
has `(y, a)_K = -1` and `(y, b)_K = 1`: the character `(·, a)_K` is nontrivial and differs from
`(·, b)_K`. -/
private theorem exists_hilbertSymbol_eq_neg_one_and_eq_one (h2 : (2 : K) ≠ 0) {a b : Kˣ}
    (ha : ¬IsSquare a) (hab : ¬IsSquare (a * b)) :
    ∃ y : Kˣ, hilbertSymbol y a = -1 ∧ hilbertSymbol y b = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨x₁, hx₁⟩ := exists_hilbertSymbol_eq_neg_one h2 ha
  obtain ⟨x₃, hx₃⟩ := exists_hilbertSymbol_eq_neg_one h2 hab
  rw [hilbertSymbol_comm] at hx₁ hx₃
  rw [hilbertSymbol_mul_right h2] at hx₃
  rcases Int.units_eq_one_or (hilbertSymbol x₁ b) with h₁ | h₁
  · exact ⟨x₁, hx₁, h₁⟩
  rcases Int.units_eq_one_or (hilbertSymbol x₃ a) with h₃ | h₃
  · rw [h₃, one_mul] at hx₃
    exact ⟨x₁ * x₃, by rw [hilbertSymbol_mul_left h2, hx₁, h₃, mul_one],
      by rw [hilbertSymbol_mul_left h2, h₁, hx₃]; decide⟩
  · rw [h₃, neg_one_mul, neg_inj] at hx₃
    exact ⟨x₃, h₃, hx₃⟩

/-- **Two distinct nontrivial characters take every pair of values.** If `2 ≠ 0` in `K`, then for
nonsquares `a`, `b` with `ab` a nonsquare, every pair of signs `(s, t)` is `((x, a)_K, (x, b)_K)`
for some `x ∈ Kˣ`. -/
theorem exists_hilbertSymbol_eq_and_hilbertSymbol_eq (h2 : (2 : K) ≠ 0) {a b : Kˣ}
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) (hab : ¬IsSquare (a * b)) (s t : ℤˣ) :
    ∃ x : Kˣ, hilbertSymbol x a = s ∧ hilbertSymbol x b = t := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨y, hya, hyb⟩ := exists_hilbertSymbol_eq_neg_one_and_eq_one h2 ha hab
  obtain ⟨z, hzb, hza⟩ := exists_hilbertSymbol_eq_neg_one_and_eq_one h2 hb (mul_comm a b ▸ hab)
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · exact ⟨1, hilbertSymbol_one_left a, hilbertSymbol_one_left b⟩
  · exact ⟨z, hza, hzb⟩
  · exact ⟨y, hya, hyb⟩
  · exact ⟨y * z, by rw [hilbertSymbol_mul_left h2, hya, hza, mul_one],
      by rw [hilbertSymbol_mul_left h2, hyb, hzb, one_mul]⟩

/-- **The norm group of `K(√a)` contains a nonsquare.** If `2 ≠ 0` in `K`, then for every `a ∈ Kˣ`
there is a nonsquare `b` with `(b, a)_K = 1`: among a uniformizer `π`, the unramified unit `Δ` and
their product, three nonsquares, the symbols with `a` multiply to `1`, so one of them is `1`. -/
theorem exists_not_isSquare_hilbertSymbol_eq_one (h2 : (2 : K) ≠ 0) (a : Kˣ) :
    ∃ b : Kˣ, ¬IsSquare b ∧ hilbertSymbol b a = 1 := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  obtain ⟨Δ, hΔ, hΔv, -, -⟩ := exists_unramified_class h2
  by_cases hπa : hilbertSymbol π a = 1
  · exact ⟨π, not_isSquare_of_isUniformizer hπ, hπa⟩
  by_cases hΔa : hilbertSymbol Δ a = 1
  · exact ⟨Δ, hΔ, hΔa⟩
  refine ⟨π * Δ,
    not_isSquare_mul_of_isUniformizer_of_even_toAdd_normalizedValuation hπ (hΔv ▸ Even.zero), ?_⟩
  rw [hilbertSymbol_mul_left h2, Int.units_ne_iff_eq_neg.mp hπa, Int.units_ne_iff_eq_neg.mp hΔa]
  decide

/-- **The local Hilbert symbol takes both values.** Every sign `±1` is `(a, b)_K` for some
`a, b ∈ Kˣ`; when `2 ≠ 0` in `K`, in particular some quaternion algebra `ℍ[K,a,b]` is a
division algebra. -/
theorem uncurry_hilbertSymbol_surjective :
    Function.Surjective (Function.uncurry (hilbertSymbol (K := K))) := by
  intro s
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨(1, 1), hilbertSymbol_one_right 1⟩
  · obtain ⟨π, hπ⟩ := exists_isUniformizer K
    by_cases h2 : (2 : K) = 0
    · -- in characteristic two, `π = x ^ 2 - y ^ 2 = (x + y) ^ 2` would be a square
      refine ⟨(1, π), (hilbertSymbol_eq_neg_one_iff _ _).mpr ?_⟩
      rintro ⟨x, y, h⟩
      simp only [Units.val_one, one_mul] at h
      exact not_isSquare_of_isUniformizer hπ
        (Units.isSquare_coe_iff.mp ⟨x + y, by linear_combination h + (-x * y - y ^ 2) * h2⟩)
    · have : Invertible (2 : K) := invertibleOfNonzero h2
      obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one h2 (not_isSquare_of_isUniformizer hπ)
      exact ⟨(π, b), hb⟩

end TauCeti
