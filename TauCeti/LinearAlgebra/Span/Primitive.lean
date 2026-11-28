/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import TauCeti.Algebra.GCDMonoid.Finset

/-!
# Primitive integer vectors in `ℤ`-spans

On a finite index type, integer tuples satisfying the cross-product equations
`m j * v i = m i * v j` for a tuple `m : ι → ℕ` with a nonzero coordinate form the `ℤ`-span of
the primitive vector `i ↦ m i / gcd(m)` (`TauCeti.forall_natCast_mul_eq_iff_mem_span_div_gcd`).
-/

public section

namespace TauCeti

/-- For natural numbers `m : ι → ℕ` on a finite index type with at least one nonzero entry, the
cross-product equations `(m j : ℤ) * v i = (m i : ℤ) * v j` hold for all `i, j` if and only if
`v` lies in the `ℤ`-span of the primitive vector `i ↦ m i / gcd(m)`. -/
theorem forall_natCast_mul_eq_iff_mem_span_div_gcd {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∃ i, m i ≠ 0) (v : ι → ℤ) :
    (∀ i j, (m j : ℤ) * v i = (m i : ℤ) * v j) ↔
      v ∈ Submodule.span ℤ {fun i ↦ ((m i / Finset.univ.gcd m : ℕ) : ℤ)} := by
  set d : ℕ := Finset.univ.gcd m
  have hd_dvd (i : ι) : d ∣ m i := Finset.gcd_dvd (Finset.mem_univ i)
  obtain ⟨i₀, hi₀⟩ := hm
  have hd_ne : d ≠ 0 := ne_zero_of_dvd_ne_zero hi₀ (hd_dvd i₀)
  have hd_ne_int : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd_ne
  have hmul_div (i : ι) : (d : ℤ) * ((m i / d : ℕ) : ℤ) = (m i : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (hd_dvd i)
  constructor
  · intro hv
    have hgcd1 : Finset.univ.gcd (fun j : ι ↦ m j / d) = 1 :=
      Finset.gcd_div_eq_one (Finset.mem_univ i₀) hi₀
    obtain ⟨c, hc⟩ := Finset.gcd_eq_one_iff_exists_sum_natCast_mul_eq_one.mp hgcd1
    refine Submodule.mem_span_singleton.mpr ⟨∑ j : ι, v j * c j, funext fun i ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ hd_ne_int
    calc
      (d : ℤ) * ((∑ j : ι, v j * c j) * ((m i / d : ℕ) : ℤ))
          = (m i : ℤ) * ∑ j : ι, v j * c j := by
            rw [mul_comm (∑ j : ι, _), ← mul_assoc, hmul_div i]
      _ = ∑ j : ι, ((m i : ℤ) * v j) * c j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j : ι, ((m j : ℤ) * v i) * c j :=
            Finset.sum_congr rfl fun j _ ↦ by rw [hv i j]
      _ = (d : ℤ) * ((∑ j : ι, ((m j / d : ℕ) : ℤ) * c j) * v i) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by rw [← hmul_div j]; ring
      _ = (d : ℤ) * v i := by rw [hc, one_mul]
  · intro hv i j
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    apply mul_left_cancel₀ hd_ne_int
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (d : ℤ) * ((m j : ℤ) * (c * ((m i / d : ℕ) : ℤ)))
          = (m j : ℤ) * c * ((d : ℤ) * ((m i / d : ℕ) : ℤ)) := by ring
      _ = (m j : ℤ) * c * (m i : ℤ) := by rw [hmul_div i]
      _ = (m i : ℤ) * c * ((d : ℤ) * ((m j / d : ℕ) : ℤ)) := by
            rw [hmul_div j]; ring
      _ = (d : ℤ) * ((m i : ℤ) * (c * ((m j / d : ℕ) : ℤ))) := by ring

end TauCeti
