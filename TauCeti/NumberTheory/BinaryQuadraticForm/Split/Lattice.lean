/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Classes
public import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Explicit lattices over the split product order

The lattice `sℤ × 0 + ℤ(c, 1)` is a module over the actual congruence product order.
Its product norm is the triangular form `sxy + cy²`. When `c` is coprime to `s`,
multiplication of these modules multiplies `c` modulo `s`, giving the split composition
calculation without a number-field ideal-class carrier.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (order-module conventions).
-/

public section

namespace TauCeti.BinaryQuadraticForm

/-- The module spanned over the integers by `(s, 0)` and `(c, 1)`, over the actual
split congruence product order. -/
def splitModule (s c : ℤ) : Submodule (QuadraticOrder.productSubalgebra s) (ℤ × ℤ) where
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
    have hr := (QuadraticOrder.mem_productSubalgebra s (r : ℤ × ℤ)).mp r.property
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

/-- Congruent coefficients give the same actual split-order module. -/
theorem splitModule_eq_of_dvd_sub (s c d : ℤ) (h : s ∣ c - d) :
    splitModule s c = splitModule s d := by
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
    exact ⟨⟨z, (QuadraticOrder.mem_productSubalgebra s z).mpr hz⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    exact (QuadraticOrder.mem_productSubalgebra s (r : ℤ × ℤ)).mp r.property

/-- Multiplication of actual product-order modules multiplies their congruence coefficients. -/
theorem splitModule_mul (s c d : ℤ) (hc : IsCoprime s c) :
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
      obtain ⟨u, v, huv⟩ := hc
      have hss := Submodule.mul_mem_mul (first_mem_splitModule s c)
        (first_mem_splitModule s d)
      have hcs := Submodule.mul_mem_mul (second_mem_splitModule s c)
        (first_mem_splitModule s d)
      have h := ((splitModule s c * splitModule s d).restrictScalars ℤ).add_mem
        (((splitModule s c * splitModule s d).restrictScalars ℤ).smul_mem u hss)
        (((splitModule s c * splitModule s d).restrictScalars ℤ).smul_mem v hcs)
      have heq : u • (((s, 0) : ℤ × ℤ) * (s, 0)) +
          v • (((c, 1) : ℤ × ℤ) * (s, 0)) = (s, 0) := by
        ext
        · simp only [Prod.fst_add, Prod.fst_mul, zsmul_eq_mul]
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

/-- Primitive triangular forms give invertible modules over the actual split order. -/
theorem isUnit_splitModule (s c : ℤ) (hc : IsCoprime s c) :
    IsUnit (splitModule s c) := by
  obtain ⟨u, v, huv⟩ := hc
  have hcv : s ∣ c * v - 1 := by
    refine ⟨-u, ?_⟩
    linear_combination huv
  have hmul := splitModule_mul s c v ⟨u, v, huv⟩
  rw [splitModule_eq_of_dvd_sub s (c * v) 1 hcv, splitModule_one] at hmul
  exact IsUnit.of_mul_eq_one (splitModule s v) hmul

end TauCeti.BinaryQuadraticForm
