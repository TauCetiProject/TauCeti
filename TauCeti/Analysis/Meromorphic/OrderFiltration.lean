/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Germ
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# The order filtration of meromorphic germs

The germs at `a` of order at least `n` form a vector space `orderGE a n`, for every integer
`n`, including negative integers (which allow poles). Multiplication by a power of the local
coordinate shifts this filtration. These are the local spaces underlying divisor sheaves;
increasing a pole bound by one compares consecutive steps of this filtration.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1 and 16.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.meromorphicGerms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {a : 𝕜}

/-- The order of a meromorphic germ, with order `⊤` for the zero germ. -/
def order (φ : meromorphicGerms 𝕜 a) : WithTop ℤ :=
  Germ.liftOn φ.1 (fun f ↦ meromorphicOrderAt f a) fun _ _ h ↦ meromorphicOrderAt_congr h

@[simp]
theorem order_mk (f : 𝕜 → 𝕜) (hf : MeromorphicAt f a) :
    order (mk f hf) = meromorphicOrderAt f a := by
  rw [order, coe_mk]
  rfl

@[simp]
theorem order_zero : order (0 : meromorphicGerms 𝕜 a) = ⊤ := by
  classical
  rw [← mk_zero, order_mk, meromorphicOrderAt_const]
  simp

/-- Only the zero germ has infinite order. -/
@[simp]
theorem order_eq_top_iff (φ : meromorphicGerms 𝕜 a) : order φ = ⊤ ↔ φ = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  rw [order_mk, meromorphicOrderAt_eq_top_iff, ← mk_zero, mk_eq_mk_iff]
  rfl

/-- Orders of products add. -/
theorem order_mul (φ ψ : meromorphicGerms 𝕜 a) : order (φ * ψ) = order φ + order ψ := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  obtain ⟨g, hg, rfl⟩ := exists_mk ψ
  rw [← mk_mul, order_mk, order_mk, order_mk, meromorphicOrderAt_mul hf hg]

/-- Addition cannot decrease order below the smaller of the two orders. -/
theorem min_order_le_order_add (φ ψ : meromorphicGerms 𝕜 a) :
    min (order φ) (order ψ) ≤ order (φ + ψ) := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  obtain ⟨g, hg, rfl⟩ := exists_mk ψ
  rw [← mk_add, order_mk, order_mk, order_mk]
  exact meromorphicOrderAt_add hf hg

/-- Multiplication by a nonzero scalar preserves order. -/
theorem order_smul_of_ne_zero {c : 𝕜} (hc : c ≠ 0) (φ : meromorphicGerms 𝕜 a) :
    order (c • φ) = order φ := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  rw [← mk_smul, order_mk, order_mk, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]

/-- The vector space of meromorphic germs of order at least `n`. -/
def orderGE (a : 𝕜) (n : ℤ) : Submodule 𝕜 (meromorphicGerms 𝕜 a) where
  carrier := {φ | (n : WithTop ℤ) ≤ order φ}
  zero_mem' := by simp
  add_mem' hφ hψ := (le_min hφ hψ).trans (min_order_le_order_add _ _)
  smul_mem' c φ hφ := by
    by_cases hc : c = 0
    · simp [hc]
    · simpa only [Set.mem_ofPred_eq, order_smul_of_ne_zero hc] using hφ

@[simp]
theorem mem_orderGE (φ : meromorphicGerms 𝕜 a) (n : ℤ) :
    φ ∈ orderGE a n ↔ (n : WithTop ℤ) ≤ order φ := Iff.rfl

/-- Increasing the required order decreases the space of germs. -/
theorem orderGE_antitone (a : 𝕜) : Antitone (orderGE a : ℤ → Submodule 𝕜 _) :=
  fun _ _ h _ hφ ↦ le_trans (WithTop.coe_le_coe.mpr h) hφ

/-- The quotient of two order bounds, with the denominator viewed in the numerator.
For `n ≤ m` it consists of the coefficients of orders `n, …, m - 1`. -/
abbrev OrderWindow (a : 𝕜) (n m : ℤ) :=
  orderGE a n ⧸ (orderGE a m).comap (orderGE a n).subtype

/-- The coordinate vanishes to order exactly one. -/
@[simp]
theorem order_coordinate (a : 𝕜) : order (coordinate a) = 1 := by
  rw [order, coe_coordinate]
  exact meromorphicOrderAt_id_sub_const

/-- The coordinate has nonzero punctured germ. -/
theorem coordinate_ne_zero (a : 𝕜) : coordinate a ≠ 0 := by
  intro h
  have ho := congrArg order h
  rw [order_coordinate, order_zero] at ho
  exact WithTop.coe_ne_top ho

/-- Integer powers of the coordinate have their indicated order, also for poles. -/
@[simp]
theorem order_coordinate_zpow (a : 𝕜) (n : ℤ) : order (coordinate a ^ n) = n := by
  have hm : MeromorphicAt (fun z : 𝕜 ↦ (z - a) ^ n) a :=
    ((MeromorphicAt.id a).sub (.const a a)).zpow n
  have heq : coordinate a ^ n = mk (fun z : 𝕜 ↦ (z - a) ^ n) hm := by
    apply Subtype.ext
    rw [coe_zpow, coe_coordinate, coe_mk]
    exact (Germ.coe_pow (fun z : 𝕜 ↦ z - a) n).symm
  rw [heq, order_mk]
  exact meromorphicOrderAt_zpow_id_sub_const

/-- Multiplying by a coordinate power shifts the order bound by that integer. -/
theorem coordinate_zpow_mul_mem_orderGE_iff (φ : meromorphicGerms 𝕜 a) (m n : ℤ) :
    coordinate a ^ m * φ ∈ orderGE a (m + n) ↔ φ ∈ orderGE a n := by
  rw [mem_orderGE, order_mul, order_coordinate_zpow, mem_orderGE]
  cases h : order φ with
  | top => simp
  | coe j => simp only [← WithTop.coe_add, WithTop.coe_le_coe, add_le_add_iff_left]

/-- A scalar multiple of a coordinate monomial, as a germ of order at least `n`. -/
def monomial (a : 𝕜) (n : ℤ) (c : 𝕜) : orderGE a n :=
  ⟨c • coordinate a ^ n, by
    by_cases hc : c = 0
    · simp [hc]
    · simp [mem_orderGE, order_smul_of_ne_zero hc]⟩

@[simp]
theorem coe_monomial (n : ℤ) (c : 𝕜) :
    (monomial a n c : meromorphicGerms 𝕜 a) = c • coordinate a ^ n := (rfl)

end TauCeti.meromorphicGerms
