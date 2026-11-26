/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.NumberTheory.Quaternion.Order.Basic
public import TauCeti.RingTheory.IntegralOrder.Maximal
-- `round` on `ℚ`, used only in proofs.
import Mathlib.Data.Rat.Floor

/-!
# The Hurwitz order

The **Hurwitz order** of Hamilton's rational quaternions `ℍ[ℚ,-1,-1]` is
`O_H = ℤ ω + ℤ i + ℤ j + ℤ k` with `ω = (1 + i + j + k) / 2`, the quaternions whose four
coordinates are either all integers or all in `1/2 + ℤ`. It contains the Lipschitz order
`ℤ⟨i, j⟩ = ℤ + ℤ i + ℤ j + ℤ k` (`TauCeti.QuaternionAlgebra.standardOrder ℤ (-1) 0 (-1)`) with
index `2`, and it is the unique order properly containing it: if `α = t + x i + y j + z k` lies in
an order containing `i` and `j`, the reduced traces of `α`, `α i`, `α j`, `α k` are the integers
`2t, -2x, -2y, -2z`, and the reduced norm `t² + x² + y² + z²` is an integer too, which forces
`2t, 2x, 2y, 2z` to have the same parity. Consequently the Hurwitz order is a maximal `ℤ`-order,
while the Lipschitz order is not.

Unlike the Lipschitz order, the Hurwitz order is norm-Euclidean: every rational quaternion lies
within reduced norm `1/2` of `O_H`, because the half-integral points fill the holes of the
integral lattice `ℤ⁴`. Hence division with remainder holds in `O_H`, the input to the
principality of its one-sided ideals and to the computation of its class number.

## Main definitions

* `TauCeti.QuaternionAlgebra.hurwitzOrder`: the Hurwitz order `O_H` of `ℍ[ℚ,-1,-1]`.

## Main results

* `TauCeti.QuaternionAlgebra.mem_hurwitzOrder_iff`: a quaternion lies in `O_H` exactly when its
  coordinates are all integers or all in `1/2 + ℤ`.
* `TauCeti.QuaternionAlgebra.toSubmodule_hurwitzOrder`: `O_H` is the `ℤ`-span of `ω, i, j, k`.
* `TauCeti.QuaternionAlgebra.hurwitzOrder_le_iff` and
  `TauCeti.QuaternionAlgebra.adjoin_eq_hurwitzOrder`: `O_H = ℤ⟨i, j, ω⟩`.
* `TauCeti.QuaternionAlgebra.isOrder_hurwitzOrder`: `O_H` is a `ℤ`-order.
* `TauCeti.QuaternionAlgebra.standardOrder_lt_hurwitzOrder` and
  `TauCeti.QuaternionAlgebra.relIndex_standardOrder_hurwitzOrder`: the Lipschitz order is a
  subgroup of index `2` of `O_H`.
* `TauCeti.QuaternionAlgebra.le_hurwitzOrder_of_standardOrder_le`: every order containing the
  Lipschitz order lies in `O_H`.
* `TauCeti.QuaternionAlgebra.eq_hurwitzOrder_of_standardOrder_lt`: `O_H` is the only order properly
  containing the Lipschitz order.
* `TauCeti.QuaternionAlgebra.isMaximalOrder_hurwitzOrder`: `O_H` is a maximal `ℤ`-order, and
  `TauCeti.QuaternionAlgebra.not_isMaximalOrder_standardOrder`: the Lipschitz order is not.
* `TauCeti.QuaternionAlgebra.exists_mem_hurwitzOrder_normForm_sub_le_half`: every quaternion
  `γ` has some `μ ∈ O_H` with `nrd (γ - μ) ≤ 1/2`.
* `TauCeti.QuaternionAlgebra.exists_mem_hurwitzOrder_eq_mul_add_normForm_lt`: `O_H` is right
  norm-Euclidean.

## References

* J. Voight, *Quaternion algebras*, Graduate Texts in Mathematics 288 (2021), Section 11.1, in
  particular Lemma 11.1.2, and Section 11.3, Lemma 11.3.1 and Proposition 11.3.2.
* A. Hurwitz, *Vorlesungen über die Zahlentheorie der Quaternionen*, Springer (1919).
-/

public section

open Submodule TauCeti.IntegralOrder QuaternionAlgebra

open scoped Quaternion

namespace TauCeti.QuaternionAlgebra

/-- The **Hurwitz order** `O_H = ℤ ω + ℤ i + ℤ j + ℤ k` of `ℍ[ℚ,-1,-1]`, where
`ω = (1 + i + j + k) / 2`: the quaternions `a ω + b i + c j + d k` with `a, b, c, d ∈ ℤ`. Its
elements are the quaternions whose coordinates are all integers or all in `1/2 + ℤ`
(`TauCeti.QuaternionAlgebra.mem_hurwitzOrder_iff`). -/
def hurwitzOrder : Subalgebra ℤ ℍ[ℚ,-1,-1] where
  carrier := {x | ∃ a b c d : ℤ, x = ⟨a / 2, a / 2 + b, a / 2 + c, a / 2 + d⟩}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨e, f, g, h, rfl⟩
    refine ⟨-a * e - a * (f + g + h) - e * (b + c + d) - 2 * (b * f + c * g + d * h),
      a * e + a * (f + h) + e * (b + c) + c * h - d * g + b * f + c * g + d * h,
      a * e + a * (f + g) + e * (c + d) - b * h + d * f + b * f + c * g + d * h,
      a * e + a * (g + h) + e * (b + d) + b * g - c * f + b * f + c * g + d * h, ?_⟩
    ext <;> simp <;> ring
  add_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨e, f, g, h, rfl⟩
    exact ⟨a + e, b + f, c + g, d + h, by ext <;> simp <;> ring⟩
  algebraMap_mem' n := ⟨2 * n, -n, -n, -n, by ext <;> simp⟩

/-- Membership in the Hurwitz order, in the coordinates `a ω + b i + c j + d k` with respect to
`ω = (1 + i + j + k) / 2, i, j, k`. -/
theorem mem_hurwitzOrder_iff_exists {x : ℍ[ℚ,-1,-1]} :
    x ∈ hurwitzOrder ↔ ∃ a b c d : ℤ, x = ⟨a / 2, a / 2 + b, a / 2 + c, a / 2 + d⟩ :=
  Iff.rfl

/-- **The Hurwitz order in coordinates.** A quaternion lies in the Hurwitz order exactly when its
four coordinates are either all integers or all in `1/2 + ℤ`. -/
theorem mem_hurwitzOrder_iff {x : ℍ[ℚ,-1,-1]} :
    x ∈ hurwitzOrder ↔ (∃ a b c d : ℤ, x = ⟨a, b, c, d⟩) ∨
      ∃ a b c d : ℤ, x = ⟨a + 1 / 2, b + 1 / 2, c + 1 / 2, d + 1 / 2⟩ := by
  rw [mem_hurwitzOrder_iff_exists]
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' a
    · exact .inl ⟨m, m + b, m + c, m + d, by ext <;> push_cast <;> ring⟩
    · exact .inr ⟨m, m + b, m + c, m + d, by ext <;> push_cast <;> ring⟩
  · rintro (⟨a, b, c, d, rfl⟩ | ⟨a, b, c, d, rfl⟩)
    · exact ⟨2 * a, b - a, c - a, d - a, by ext <;> push_cast <;> ring⟩
    · exact ⟨2 * a + 1, b - a, c - a, d - a, by ext <;> push_cast <;> ring⟩

/-- The Hurwitz quaternion `ω = (1 + i + j + k) / 2` lies in the Hurwitz order. -/
theorem half_mem_hurwitzOrder : (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ[ℚ,-1,-1]) ∈ hurwitzOrder :=
  ⟨1, 0, 0, 0, by ext <;> simp⟩

/-- The quaternion `i` lies in the Hurwitz order. -/
theorem i_mem_hurwitzOrder : (⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1]) ∈ hurwitzOrder :=
  ⟨0, 1, 0, 0, by ext <;> simp⟩

/-- The quaternion `j` lies in the Hurwitz order. -/
theorem j_mem_hurwitzOrder : (⟨0, 0, 1, 0⟩ : ℍ[ℚ,-1,-1]) ∈ hurwitzOrder :=
  ⟨0, 0, 1, 0, by ext <;> simp⟩

/-- The Hurwitz order `O_H` is the `ℤ`-span of `ω = (1 + i + j + k) / 2, i, j, k`. -/
theorem toSubmodule_hurwitzOrder :
    Subalgebra.toSubmodule hurwitzOrder = span ℤ (Set.range ![(⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ :
      ℍ[ℚ,-1,-1]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]) := by
  ext x
  rw [Subalgebra.mem_toSubmodule, mem_hurwitzOrder_iff_exists, mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨![a, b, c, d], by ext <;> simp [Fin.sum_univ_four] <;> ring⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v 0, v 1, v 2, v 3, by ext <;> simp [Fin.sum_univ_four] <;> ring⟩

/-- The Hurwitz order lies in a `ℤ`-subalgebra `Λ` of `ℍ[ℚ,-1,-1]` exactly when `i`, `j` and
`ω = (1 + i + j + k) / 2` do. -/
theorem hurwitzOrder_le_iff {Λ : Subalgebra ℤ ℍ[ℚ,-1,-1]} :
    hurwitzOrder ≤ Λ ↔
      ⟨0, 1, 0, 0⟩ ∈ Λ ∧ ⟨0, 0, 1, 0⟩ ∈ Λ ∧ ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ ∈ Λ := by
  refine ⟨fun h => ⟨h i_mem_hurwitzOrder, h j_mem_hurwitzOrder, h half_mem_hurwitzOrder⟩, ?_⟩
  rintro ⟨hi, hj, hω⟩ x hx
  rw [← Subalgebra.mem_toSubmodule, toSubmodule_hurwitzOrder] at hx
  -- `k = i * j`, so all four spanning vectors lie in `Λ`
  have hk : (⟨0, 0, 0, 1⟩ : ℍ[ℚ,-1,-1]) ∈ Λ := by
    convert Λ.mul_mem hi hj using 1
    ext <;> simp
  refine (span_le (p := Subalgebra.toSubmodule Λ)).2 (Set.range_subset_iff.2 fun n => ?_) hx
  fin_cases n
  exacts [hω, hi, hj, hk]

/-- The Hurwitz order is the `ℤ`-subalgebra `ℤ⟨i, j, ω⟩` generated by `i`, `j` and
`ω = (1 + i + j + k) / 2`. -/
theorem adjoin_eq_hurwitzOrder :
    Algebra.adjoin ℤ {(⟨0, 1, 0, 0⟩ : ℍ[ℚ,-1,-1]), ⟨0, 0, 1, 0⟩, ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩} =
      hurwitzOrder := by
  refine le_antisymm ?_ (hurwitzOrder_le_iff.2 ⟨?_, ?_, ?_⟩)
  · rw [Algebra.adjoin_le_iff, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨i_mem_hurwitzOrder, j_mem_hurwitzOrder, half_mem_hurwitzOrder⟩
  all_goals exact Algebra.subset_adjoin (by simp)

/-- The **Lipschitz order** `ℤ⟨i, j⟩` lies in the Hurwitz order. -/
theorem standardOrder_le_hurwitzOrder :
    standardOrder ℤ (-1 : ℚ) 0 (-1) ≤ hurwitzOrder :=
  standardOrder_le_iff.2 ⟨i_mem_hurwitzOrder, j_mem_hurwitzOrder⟩

/-- A quaternion lies in the Lipschitz order `ℤ⟨i, j⟩` of `ℍ[ℚ,-1,-1]` exactly when its four
coordinates are integers. -/
private theorem mem_lipschitz_iff {x : ℍ[ℚ,-1,-1]} :
    x ∈ standardOrder ℤ (-1 : ℚ) 0 (-1) ↔ ∃ a b c d : ℤ, x = ⟨a, b, c, d⟩ := by
  rw [mem_standardOrder_iff ⟨-1, by simp⟩ ⟨0, by simp⟩ ⟨-1, by simp⟩]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨a, b, c, d, by ext <;> simp [← ha, ← hb, ← hc, ← hd]⟩
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩, ⟨d, by simp⟩⟩

/-- The Hurwitz quaternion `ω = (1 + i + j + k) / 2` does not lie in the Lipschitz order. -/
private theorem half_notMem_lipschitz :
    (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ[ℚ,-1,-1]) ∉ standardOrder ℤ (-1 : ℚ) 0 (-1) := by
  rintro h
  obtain ⟨a, _, _, _, heq⟩ := mem_lipschitz_iff.1 h
  have hden := congrArg (fun x : ℍ[ℚ,-1,-1] => x.re.den) heq
  simp at hden

/-- The Lipschitz order `ℤ⟨i, j⟩` is properly contained in the Hurwitz order. -/
theorem standardOrder_lt_hurwitzOrder :
    standardOrder ℤ (-1 : ℚ) 0 (-1) < hurwitzOrder :=
  IsConcreteLE.lt_iff_le_and_exists.2
    ⟨standardOrder_le_hurwitzOrder, _, half_mem_hurwitzOrder, half_notMem_lipschitz⟩

/-- **The Lipschitz order has index `2` in the Hurwitz order**: every Hurwitz quaternion lies in
`ℤ⟨i, j⟩` or differs from an element of it by `ω = (1 + i + j + k) / 2`. -/
theorem relIndex_standardOrder_hurwitzOrder :
    (Subalgebra.toSubmodule (standardOrder ℤ (-1 : ℚ) 0 (-1))).toAddSubgroup.relIndex
      (Subalgebra.toSubmodule hurwitzOrder).toAddSubgroup = 2 := by
  refine AddSubgroup.relIndex_eq_two_iff_exists_notMem_and.2
    ⟨_, half_mem_hurwitzOrder, half_notMem_lipschitz, fun x hx => ?_⟩
  simp only [Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule, mem_lipschitz_iff] at hx ⊢
  rcases mem_hurwitzOrder_iff.1 hx with ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · exact .inr ⟨a, b, c, d, rfl⟩
  · exact .inl ⟨a + 1, b + 1, c + 1, d + 1, by ext <;> simp <;> ring⟩

/-- **The Hurwitz order is a `ℤ`-order** in `ℍ[ℚ,-1,-1]`. -/
theorem isOrder_hurwitzOrder : IsOrder ℚ hurwitzOrder := by
  have : Module.Finite ℤ hurwitzOrder :=
    Module.Finite.iff_fg.2 (toSubmodule_hurwitzOrder ▸ fg_span (Set.finite_range _))
  exact (isOrder_standardOrder ⟨-1, by simp⟩ ⟨0, by simp⟩ ⟨-1, by simp⟩).of_le
    standardOrder_le_hurwitzOrder

/-- If the squares of four integers sum to a multiple of `4`, the four integers have the same
parity. -/
private theorem exists_eq_add_two_mul_of_sum_sq {A B C D n : ℤ}
    (h : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 * n) :
    ∃ b c d : ℤ, B = A + 2 * b ∧ C = A + 2 * c ∧ D = A + 2 * d := by
  -- `X ^ 2 ≡ X (mod 2)` and `X ^ 2 ≡ 0, 1 (mod 4)`, so `X ^ 2 % 4 = X % 2`
  have hsq (X : ℤ) : X ^ 2 % 4 = X % 2 := by
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' X <;> ring_nf <;> omega
  have := hsq A
  have := hsq B
  have := hsq C
  have := hsq D
  exact ⟨(B - A) / 2, (C - A) / 2, (D - A) / 2, by omega, by omega, by omega⟩

/-- **Every order containing the Lipschitz order lies in the Hurwitz order.** If `α` lies in a
`ℤ`-order `Λ` containing `ℤ⟨i, j⟩`, the reduced traces of `α`, `α i`, `α j` and `α k` show that the
coordinates of `2 α` are integers, and the integrality of the reduced norm of `α` forces them to
have the same parity. -/
theorem le_hurwitzOrder_of_standardOrder_le {Λ : Subalgebra ℤ ℍ[ℚ,-1,-1]} (hΛ : IsOrder ℚ Λ)
    (hle : standardOrder ℤ (-1 : ℚ) 0 (-1) ≤ Λ) : Λ ≤ hurwitzOrder := by
  intro x hx
  have hi := hle i_mem_standardOrder
  have hj := hle j_mem_standardOrder
  -- the reduced traces of `x`, `x i`, `x j`, `x k` are `2 t, -2 x₁, -2 x₂, -2 x₃`
  obtain ⟨A, hA⟩ := hΛ.two_mul_re_add_mul_imI_mem_range hx
  obtain ⟨B, hB⟩ := hΛ.two_mul_re_add_mul_imI_mem_range (Λ.mul_mem hx hi)
  obtain ⟨C, hC⟩ := hΛ.two_mul_re_add_mul_imI_mem_range (Λ.mul_mem hx hj)
  obtain ⟨D, hD⟩ := hΛ.two_mul_re_add_mul_imI_mem_range (Λ.mul_mem hx (Λ.mul_mem hi hj))
  obtain ⟨n, hn⟩ := hΛ.normForm_mem_range hx
  simp only [eq_intCast] at hA hB hC hD hn
  simp only [QuaternionAlgebra.re_mul, zero_mul, add_zero, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] at hA hB hC hD
  rw [normForm_apply_coordinates] at hn
  have hsum : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 4 * n := by
    have : (A : ℚ) ^ 2 + (B : ℚ) ^ 2 + (C : ℚ) ^ 2 + (D : ℚ) ^ 2 = 4 * n := by
      rw [hA, hB, hC, hD, hn]
      ring
    exact_mod_cast this
  obtain ⟨b, c, d, rfl, rfl, rfl⟩ := exists_eq_add_two_mul_of_sum_sq hsum
  refine ⟨A, -b - A, -c - A, -d - A, ?_⟩
  ext <;> push_cast at hB hC hD ⊢ <;> linarith

/-- **The Hurwitz order is the unique order properly containing the Lipschitz order.** -/
theorem eq_hurwitzOrder_of_standardOrder_lt {Λ : Subalgebra ℤ ℍ[ℚ,-1,-1]} (hΛ : IsOrder ℚ Λ)
    (hlt : standardOrder ℤ (-1 : ℚ) 0 (-1) < Λ) : Λ = hurwitzOrder := by
  refine le_antisymm (le_hurwitzOrder_of_standardOrder_le hΛ hlt.le) ?_
  obtain ⟨x, hxΛ, hxL⟩ := IsConcreteLE.exists_of_lt hlt
  -- `x` has half-integral coordinates, so `ω` differs from `x` by a Lipschitz quaternion
  rcases mem_hurwitzOrder_iff.1 (le_hurwitzOrder_of_standardOrder_le hΛ hlt.le hxΛ) with
    ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · exact absurd (mem_lipschitz_iff.2 ⟨a, b, c, d, rfl⟩) hxL
  have hy := hlt.le (mem_lipschitz_iff.2 ⟨a, b, c, d, rfl⟩)
  have hω : (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ[ℚ,-1,-1]) ∈ Λ := by
    convert Λ.sub_mem hxΛ hy using 1
    ext <;> simp
  exact hurwitzOrder_le_iff.2 ⟨hlt.le i_mem_standardOrder, hlt.le j_mem_standardOrder, hω⟩

/-- **The Hurwitz order is a maximal order.** Every order containing `O_H` properly contains the
Lipschitz order, so it is `O_H`. -/
theorem isMaximalOrder_hurwitzOrder : IsMaximalOrder ℚ hurwitzOrder :=
  ⟨isOrder_hurwitzOrder, fun _ hΛ hle =>
    (eq_hurwitzOrder_of_standardOrder_lt hΛ (standardOrder_lt_hurwitzOrder.trans_le hle)).le⟩

/-- **The Lipschitz order is not maximal**: it is properly contained in the Hurwitz order. -/
theorem not_isMaximalOrder_standardOrder :
    ¬IsMaximalOrder ℚ (standardOrder ℤ (-1 : ℚ) 0 (-1)) := fun h =>
  standardOrder_lt_hurwitzOrder.not_ge (h.2 isOrder_hurwitzOrder standardOrder_lt_hurwitzOrder.le)

/-! ### The Euclidean property -/

/-- For a rational `t` with `|t| ≤ 1/2`, the half-integer `e + 1/2 = ± 1/2` of the sign of `t`
satisfies `t² + (t - (e + 1/2))² ≤ 1/4`. -/
private theorem exists_sq_add_sq_sub_le {t : ℚ} (ht : |t| ≤ 1 / 2) :
    ∃ e : ℤ, t ^ 2 + (t - (e + 1 / 2)) ^ 2 ≤ 1 / 4 := by
  obtain ⟨ht₁, ht₂⟩ := abs_le.1 ht
  by_cases h : 0 ≤ t
  · exact ⟨0, by push_cast; nlinarith⟩
  · exact ⟨-1, by push_cast; nlinarith⟩

/-- **Every quaternion lies within reduced norm `1/2` of the Hurwitz order.** Rounding the
coordinates of `γ` gives a Lipschitz quaternion `n` with `γ - n` in the cube `[-1/2, 1/2]⁴`, and the
reduced norms of `γ - n` and of `γ - n - h`, for the half-integral `h = (± 1 ± i ± j ± k) / 2` whose
signs match those of the coordinates of `γ - n`, add up to at most `1`. -/
theorem exists_mem_hurwitzOrder_normForm_sub_le_half (γ : ℍ[ℚ,-1,-1]) :
    ∃ μ ∈ hurwitzOrder, normForm (-1 : ℚ) 0 (-1) (γ - μ) ≤ 1 / 2 := by
  set n : ℍ[ℚ,-1,-1] := ⟨round γ.re, round γ.imI, round γ.imJ, round γ.imK⟩
  have hn : n ∈ hurwitzOrder := mem_hurwitzOrder_iff.2 (.inl ⟨_, _, _, _, rfl⟩)
  obtain ⟨e₀, h₀⟩ := exists_sq_add_sq_sub_le (abs_sub_round γ.re)
  obtain ⟨e₁, h₁⟩ := exists_sq_add_sq_sub_le (abs_sub_round γ.imI)
  obtain ⟨e₂, h₂⟩ := exists_sq_add_sq_sub_le (abs_sub_round γ.imJ)
  obtain ⟨e₃, h₃⟩ := exists_sq_add_sq_sub_le (abs_sub_round γ.imK)
  have hh : n + ⟨e₀ + 1 / 2, e₁ + 1 / 2, e₂ + 1 / 2, e₃ + 1 / 2⟩ ∈ hurwitzOrder :=
    add_mem hn (mem_hurwitzOrder_iff.2 (.inr ⟨_, _, _, _, rfl⟩))
  by_contra! hlt
  have hn' := hlt n hn
  have hh' := hlt _ hh
  simp only [normForm_apply_coordinates, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub,
    QuaternionAlgebra.imJ_sub, QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_add,
    QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add, n] at hn' hh'
  linarith

/-- **The Hurwitz order is right norm-Euclidean.** For `α, β ∈ O_H` with `β ≠ 0` there are
`μ, ρ ∈ O_H` with `α = β μ + ρ` and `nrd ρ < nrd β`. -/
theorem exists_mem_hurwitzOrder_eq_mul_add_normForm_lt {α β : ℍ[ℚ,-1,-1]}
    (hα : α ∈ hurwitzOrder) (hβ : β ∈ hurwitzOrder) (hβ₀ : β ≠ 0) :
    ∃ μ ∈ hurwitzOrder, ∃ ρ ∈ hurwitzOrder, α = β * μ + ρ ∧
      normForm (-1 : ℚ) 0 (-1) ρ < normForm (-1 : ℚ) 0 (-1) β := by
  have hpos : 0 < normForm (-1 : ℚ) 0 (-1) β :=
    posDef_normForm_of_neg (by norm_num) (by norm_num) β hβ₀
  -- `γ = β⁻¹ α = nrd(β)⁻¹ (star β) α` satisfies `β γ = α`
  set γ := (normForm (-1 : ℚ) 0 (-1) β)⁻¹ • (star β * α)
  have hγ : β * γ = α := by
    rw [mul_smul_comm, ← mul_assoc, mul_star_eq_coe, ← normForm_apply, coe_mul_eq_smul, smul_smul,
      inv_mul_cancel₀ hpos.ne', one_smul]
  obtain ⟨μ, hμ, hle⟩ := exists_mem_hurwitzOrder_normForm_sub_le_half γ
  refine ⟨μ, hμ, α - β * μ, sub_mem hα (mul_mem hβ hμ), (add_sub_cancel _ _).symm, ?_⟩
  rw [← hγ, ← mul_sub, normForm_mul]
  nlinarith

end TauCeti.QuaternionAlgebra
