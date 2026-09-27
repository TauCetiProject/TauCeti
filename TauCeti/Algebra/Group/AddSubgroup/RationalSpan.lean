/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Rat
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational spans of integer subgroups

An element of the rational span of a subgroup of integer-valued functions lies in that subgroup
after multiplication by some positive integer. This denominator-clearing result is used to pass
from rational spans back to integer lattices.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- An element of the rational span of a subgroup `P` of `ι → ℤ` becomes an element of `P` after
multiplication by some positive integer. -/
theorem AddSubgroup.exists_nat_mul_eq_intCast_of_mem_span {P : AddSubgroup (ι → ℤ)}
    {x : ι → ℚ} (hx : x ∈ Submodule.span ℚ ((fun p : ι → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' P)) :
    ∃ N : ℕ, 0 < N ∧ ∃ p ∈ P, ∀ i, (p i : ℚ) = N * x i := by
  let s : Set (ι → ℚ) := (fun p : ι → ℤ => ((↑) : ℤ → ℚ) ∘ p) '' P
  obtain ⟨t, ht⟩ :=
    multiple_mem_span_of_mem_localization_span (Submonoid.pos ℤ) ℚ s x hx
  have hspan : ∀ y ∈ Submodule.span ℤ s, ∃ p ∈ P, ∀ i, (p i : ℚ) = y i := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨p, hp, fun _ => rfl⟩
    | zero => exact ⟨0, zero_mem P, fun i => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, hp, hpy⟩ := hy
      obtain ⟨q, hq, hqz⟩ := hz
      exact ⟨p + q, add_mem hp hq, fun i => by simp [hpy i, hqz i]⟩
    | smul n y _ hy =>
      obtain ⟨p, hp, hpy⟩ := hy
      exact ⟨n • p, zsmul_mem hp n, fun i => by simp [hpy i]⟩
  obtain ⟨p, hp, hpx⟩ := hspan (t • x) ht
  have htn : (t.val.toNat : ℤ) = t.val := Int.toNat_of_nonneg t.prop.le
  have hN : 0 < t.val.toNat := by
    have htpos : (0 : ℤ) < t.val := t.prop
    rw [← htn] at htpos
    exact_mod_cast htpos
  have hcast : (t.val.toNat : ℚ) = (t.val : ℚ) := by exact_mod_cast htn
  refine ⟨t.val.toNat, hN, p, hp, fun i => ?_⟩
  simpa [Submonoid.smul_def, Pi.smul_apply, smul_eq_mul, hcast] using hpx i

end TauCeti
