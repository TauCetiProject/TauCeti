/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Leading-term congruences modulo powers of a maximal ideal

Let `P` be a maximal ideal and `π ∈ P`. A congruence `a y ≡ π ^ n (mod P ^ (n + 1))` records the
leading term of `y` up to the factor `a`. This file shows that such leading terms multiply and can
be renormalised through a relation `x y = u z` in which `u` is a unit modulo `P`. This is the
inductive step in computing the leading terms of Gauss sums (Stickelberger's congruence).

## Main results

* `Ideal.IsMaximal.mul_sub_pow_succ_mem_of_mul_eq_mul`: if `x ≡ π (mod P ^ 2)`,
  `a y ≡ π ^ n (mod P ^ (n + 1))` and `x y = u z` with `u ≡ c (mod P)`, then
  `a' z ≡ π ^ (n + 1) (mod P ^ (n + 2))` for every `a' ∉ P` with `a' ≡ a c (mod P)`.
-/

public section

namespace Ideal.IsMaximal

variable {R : Type*} [CommRing R] {P : Ideal R} [P.IsMaximal]

/-- Leading terms modulo powers of a maximal ideal `P`: if `x ≡ π (mod P ^ 2)` with `π ∈ P`,
`a y ≡ π ^ n (mod P ^ (n + 1))` and `x y = u z` with `u ≡ c (mod P)`, then
`a' z ≡ π ^ (n + 1) (mod P ^ (n + 2))` for every `a' ∉ P` with `a' ≡ a c (mod P)`. -/
theorem mul_sub_pow_succ_mem_of_mul_eq_mul {π x y z u c a a' : R} {n : ℕ} (hπ : π ∈ P)
    (hx : x - π ∈ P ^ 2) (hy : a * y - π ^ n ∈ P ^ (n + 1)) (hxyz : x * y = u * z)
    (hu : u - c ∈ P) (ha' : a' - a * c ∈ P) (ha'P : a' ∉ P) :
    a' * z - π ^ (n + 1) ∈ P ^ (n + 1 + 1) := by
  have hcP : a * c ∉ P := fun hc ↦ ha'P (by simpa using Ideal.add_mem _ ha' hc)
  have haP : a ∉ P := fun ha ↦ hcP (Ideal.mul_mem_right _ _ ha)
  have huP : u ∉ P := fun hu' ↦ hcP (Ideal.mul_mem_left _ _ (by simpa using Ideal.sub_mem _ hu' hu))
  have hπn : π ^ n ∈ P ^ n := Ideal.pow_mem_pow hπ n
  have hxP : x ∈ P := by
    simpa using Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hx) hπ
  have hyn : y ∈ P ^ n := (Ideal.IsMaximal.mul_mem_pow P (by
    simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) hy) hπn)).resolve_left haP
  have hz : z ∈ P ^ (n + 1) := (Ideal.IsMaximal.mul_mem_pow P (by
    rw [← hxyz, pow_succ']; exact Ideal.mul_mem_mul hxP hyn)).resolve_left huP
  have key : a' * z - π ^ (n + 1) =
      (a' - a * u) * z + ((a * y - π ^ n) * x + π ^ n * (x - π)) := by
    linear_combination (-a) * hxyz
  rw [key]
  refine Ideal.add_mem _ ?_ (Ideal.add_mem _ ?_ ?_)
  · have : a' - a * u ∈ P := by
      simpa [mul_sub] using Ideal.sub_mem _ ha' (Ideal.mul_mem_left _ a hu)
    rw [pow_succ']
    exact Ideal.mul_mem_mul this hz
  · rw [pow_succ]
    exact Ideal.mul_mem_mul hy hxP
  · rw [add_assoc, pow_add]
    exact Ideal.mul_mem_mul hπn hx

end Ideal.IsMaximal
