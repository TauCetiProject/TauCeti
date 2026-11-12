/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.QuadraticOrder.Product
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Explicit lattices over the split product order

The lattice `sℤ × 0 + ℤ(c, 1)` is a module over the actual congruence product order.
When `s`, `c`, and `d` are jointly coprime, multiplication of the modules with coefficients
`c` and `d` gives the module with coefficient `c * d`.
Equality is exactly congruence of the coefficients modulo `s`, and coprime coefficients
give invertible modules.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (order-module conventions).
-/

public section

namespace TauCeti.QuadraticOrder

/-- The module spanned over the integers by `(s, 0)` and `(c, 1)`, over the actual
split congruence product order. -/
def splitModule (s c : ℤ) : Submodule (productSubalgebra s) (ℤ × ℤ) where
  carrier := {z | s ∣ z.1 - c * z.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h := hx.add hy
    have heq : (x + y).1 - c * (x + y).2 =
        (x.1 - c * x.2) + (y.1 - c * y.2) := by
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    simpa only [Set.mem_ofPred_eq, heq] using h
  smul_mem' := by
    intro r z hz
    have hr := (mem_productSubalgebra s (r : ℤ × ℤ)).mp r.property
    have h := (hz.mul_left (r : ℤ × ℤ).1).add (hr.mul_left (c * z.2))
    have heq : (r : ℤ × ℤ).1 * z.1 - c * ((r : ℤ × ℤ).2 * z.2) =
        (r : ℤ × ℤ).1 * (z.1 - c * z.2) +
          c * z.2 * ((r : ℤ × ℤ).1 - (r : ℤ × ℤ).2) := by ring
    simpa only [Set.mem_ofPred_eq, Algebra.smul_def, Subalgebra.algebraMap_apply,
      Prod.fst_mul, Prod.snd_mul, heq] using h

/-- Split-module membership is its defining congruence. -/
@[simp] theorem mem_splitModule (s c : ℤ) (z : ℤ × ℤ) :
    z ∈ splitModule s c ↔ s ∣ z.1 - c * z.2 := by
  rfl

/-- The first lattice generator belongs to the module. -/
theorem first_mem_splitModule (s c : ℤ) : (s, 0) ∈ splitModule s c := by
  simp

/-- The second lattice generator belongs to the module. -/
theorem second_mem_splitModule (s c : ℤ) : (c, 1) ∈ splitModule s c := by
  simp

/-- Every module element has integral coordinates in the two displayed generators. -/
theorem mem_splitModule_iff_exists (s c : ℤ) (z : ℤ × ℤ) :
    z ∈ splitModule s c ↔ ∃ x y : ℤ, z = (s * x + c * y, y) := by
  rw [mem_splitModule]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, z.2, ?_⟩
    ext
    · linear_combination hx
    · rfl
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, by ring⟩

/-- Two actual split-order modules are equal exactly when their coefficients are congruent. -/
@[simp] theorem splitModule_eq_iff_dvd_sub (s c d : ℤ) :
    splitModule s c = splitModule s d ↔ s ∣ c - d := by
  constructor
  · intro h
    have hm := second_mem_splitModule s c
    rw [h, mem_splitModule, mul_one] at hm
    exact hm
  · intro h
    ext z
    rw [mem_splitModule, mem_splitModule]
    constructor
    · intro hz
      convert hz.add (h.mul_right z.2) using 1
      ring
    · intro hz
      convert hz.sub (h.mul_right z.2) using 1
      ring

/-- The module with coefficient one is the unit module, the actual product order itself. -/
@[simp] theorem splitModule_one (s : ℤ) : splitModule s 1 = 1 := by
  ext z
  rw [mem_splitModule, Submodule.mem_one]
  simp only [one_mul]
  constructor
  · intro hz
    exact ⟨⟨z, (mem_productSubalgebra s z).mpr hz⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    exact (mem_productSubalgebra s (r : ℤ × ℤ)).mp r.property

/-- Joint coprimality of the modulus and both coefficients makes multiplication of the actual
product-order modules multiply their congruence coefficients. -/
@[simp] theorem splitModule_mul (s c d : ℤ) (hcd : IsCoprime s (Int.gcd c d)) :
    splitModule s c * splitModule s d = splitModule s (c * d) := by
  apply le_antisymm
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨a, b, rfl⟩ := (mem_splitModule_iff_exists s c x).mp hx
    obtain ⟨u, v, rfl⟩ := (mem_splitModule_iff_exists s d y).mp hy
    apply (mem_splitModule _ _ _).mpr
    refine ⟨s * a * u + a * d * v + c * b * u, ?_⟩
    simp only [Prod.fst_mul, Prod.snd_mul]
    ring
  · intro z hz
    obtain ⟨x, y, rfl⟩ := (mem_splitModule_iff_exists s (c * d) z).mp hz
    have hfirst : (s, 0) ∈ splitModule s c * splitModule s d := by
      -- Bézout combines the generators with first coordinates s², sc, and sd.
      obtain ⟨u, v, huv⟩ := hcd
      rw [Int.gcd_eq_gcd_ab] at huv
      have hss := Submodule.mul_mem_mul (first_mem_splitModule s c)
        (first_mem_splitModule s d)
      have hcs := Submodule.mul_mem_mul (second_mem_splitModule s c)
        (first_mem_splitModule s d)
      have hsd := Submodule.mul_mem_mul (first_mem_splitModule s c)
        (second_mem_splitModule s d)
      let M := (splitModule s c * splitModule s d).restrictScalars ℤ
      have h := M.add_mem
        (M.add_mem (M.smul_mem u hss) (M.smul_mem (v * Int.gcdA c d) hcs))
        (M.smul_mem (v * Int.gcdB c d) hsd)
      have heq : u • (((s, 0) : ℤ × ℤ) * (s, 0)) +
          (v * Int.gcdA c d) • (((c, 1) : ℤ × ℤ) * (s, 0)) +
          (v * Int.gcdB c d) • (((s, 0) : ℤ × ℤ) * (d, 1)) = (s, 0) := by
        simp only [Prod.mk_mul_mk, Prod.smul_mk, Prod.mk_add_mk]
        ext
        · simp only [Int.zsmul_eq_mul]
          linear_combination s * huv
        · simp
      rw [heq] at h
      exact h
    have hsecond : (c * d, 1) ∈ splitModule s c * splitModule s d := by
      simpa only [Prod.mk_mul_mk, one_mul] using
        Submodule.mul_mem_mul (second_mem_splitModule s c) (second_mem_splitModule s d)
    have h := ((splitModule s c * splitModule s d).restrictScalars ℤ).add_mem
      (((splitModule s c * splitModule s d).restrictScalars ℤ).smul_mem x hfirst)
      (((splitModule s c * splitModule s d).restrictScalars ℤ).smul_mem y hsecond)
    have heq : x • (s, 0) + y • (c * d, 1) = (s * x + c * d * y, y) := by
      ext <;> simp [mul_comm]
    rw [heq] at h
    exact h

/-- Coprime coefficients give invertible modules over the actual split order. -/
theorem isUnit_splitModule (s c : ℤ) (hc : IsCoprime s c) :
    IsUnit (splitModule s c) := by
  obtain ⟨u, v, huv⟩ := hc
  have hcv : s ∣ c * v - 1 := by
    refine ⟨-u, ?_⟩
    linear_combination huv
  have hcoprime : IsCoprime s c := ⟨u, v, huv⟩
  have hmul := splitModule_mul s c v
    (hcoprime.of_isCoprime_of_dvd_right (Int.gcd_dvd_left _ _))
  rw [(splitModule_eq_iff_dvd_sub s (c * v) 1).mpr hcv, splitModule_one] at hmul
  exact IsUnit.of_mul_eq_one (splitModule s v) hmul

end TauCeti.QuadraticOrder
