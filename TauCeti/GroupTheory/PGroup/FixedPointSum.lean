/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.GroupTheory.PGroup

/-!
# Sums of invariant functions over a `p`-group set in characteristic `p`

Let a `p`-group `P` act on a finite set `α`, and let `f : α → k` be constant on the `P`-orbits,
with `k` of characteristic `p`. Then the sum of `f` over `α` equals its sum over the fixed points
`α^P` (`IsPGroup.sum_eq_sum_fixedPoints`): an orbit that is not a fixed point has `p`-power size
`p^n` with `n ≥ 1`, so it contributes `p^n • f(a) = 0`. This is the weighted form of
`IsPGroup.card_modEq_card_fixedPoints`, which is the case `f = 1`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.5, p. 243, where the argument
  proves that the Brauer homomorphism is multiplicative.
-/

public section

namespace IsPGroup

open MulAction

variable {P α k : Type*} [Group P] [MulAction P α] [Fintype α] [NonAssocSemiring k]
  {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Sums over a `p`-group set in characteristic `p`.** If a `p`-group `P` acts on a finite set
`α` and `f : α → k` is `P`-invariant, with `k` of characteristic `p`, the sum of `f` over `α`
equals its sum over the fixed points of `P`. -/
theorem sum_eq_sum_fixedPoints (hP : IsPGroup p P) [DecidablePred (· ∈ fixedPoints P α)]
    (f : α → k) (hf : ∀ (g : P) (a : α), f (g • a) = f a) :
    ∑ a, f a = ∑ a with a ∈ fixedPoints P α, f a := by
  classical
  let π : α → orbitRel.Quotient P α := Quotient.mk (orbitRel P α)
  rw [← Finset.sum_fiberwise Finset.univ π f, Finset.sum_filter,
    ← Finset.sum_fiberwise Finset.univ π]
  refine Finset.sum_congr rfl fun ω _ => ?_
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective ω
  have hfib : ∀ a ∈ Finset.univ.filter (π · = π b), f a = f b := fun a ha => by
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (Quotient.exact (Finset.mem_filter.1 ha).2)
    exact hf g b
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  have hcard : (Finset.univ.filter (π · = π b)).card = Nat.card (orbit P b) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      simp [π, Quotient.eq, orbitRel_apply])
  have hone : ∀ a : α, a ∈ fixedPoints P α ↔ Nat.card (orbit P a) = 1 := fun a => by
    rw [Nat.card_eq_fintype_card, mem_fixedPoints_iff_card_orbit_eq_one]
  rw [hcard]
  by_cases hb : b ∈ fixedPoints P α
  · have hfix : ∀ a ∈ Finset.univ.filter (π · = π b),
        (if a ∈ fixedPoints P α then f a else 0) = f b := fun a ha => by
      obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (Quotient.exact (Finset.mem_filter.1 ha).2)
      rw [hb g, ite_eq_left hb]
    rw [Finset.sum_congr rfl hfix, Finset.sum_const, hcard, (hone b).1 hb]
  · have hnfix : ∀ a ∈ Finset.univ.filter (π · = π b),
        (if a ∈ fixedPoints P α then f a else 0) = 0 := fun a ha => by
      obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (Quotient.exact (Finset.mem_filter.1 ha).2)
      split_ifs with hgb
      · rw [hone, orbit_smul, ← hone] at hgb
        exact absurd hgb hb
      · rfl
    rw [Finset.sum_congr rfl hnfix, Finset.sum_const_zero]
    obtain ⟨n, hn⟩ := hP.card_orbit b
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hb ((hone b).2 (by rw [hn, pow_zero]))
    rw [hn, nsmul_eq_mul, (CharP.cast_eq_zero_iff k p _).2 (dvd_pow_self p hn0), zero_mul]

end IsPGroup
