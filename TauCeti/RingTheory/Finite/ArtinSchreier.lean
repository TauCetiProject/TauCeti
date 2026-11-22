/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.RingTheory.LocalRing.Basic

import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# The Artin–Schreier map `t ↦ t² + t` on a finite ring

On a finite nontrivial ring, the map `t ↦ t² + t` is not surjective: it sends both `0` and
`-1` to zero. This supplies residue-field witnesses for local square and norm arguments.

On a finite commutative local ring of characteristic two the map is additive with kernel
`{0, 1}`, so its range has index two: the sum of two elements outside the range lies in the range.
Over the residue field, this makes the unramified quadratic class of a dyadic local field unique.

On a finite field `k` of characteristic two the range is exactly the kernel of the absolute trace
`Algebra.trace (ZMod 2) k`: the trace is invariant under the Frobenius, so it kills every
`t² + t`, and its kernel also has index two. This is the finite-field case of Artin–Schreier
theory (the additive Hilbert theorem 90 for `k / ZMod 2`); it decides when a binary quadratic form
`a x² + x y + b y²` over `k` is isotropic.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, 2nd ed., Encyclopedia of Mathematics and its
  Applications 20, Cambridge University Press (1997), Theorem 2.25.
-/

public section

namespace TauCeti

/-- The map `t ↦ t² + t` has a value outside its range on every finite nontrivial ring. -/
theorem exists_not_mem_range_sq_add_self (R : Type*) [Ring R] [Finite R] [Nontrivial R] :
    ∃ a : R, a ∉ Set.range (fun t : R => t ^ 2 + t) := by
  by_contra! h
  have hsurj : Function.Surjective (fun t : R => t ^ 2 + t) := fun a => h a
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  exact one_ne_zero (neg_eq_zero.mp (hinj (a₁ := (-1 : R)) (a₂ := 0) (by simp [pow_two])))

/-- On a finite commutative local ring of characteristic two, the Artin–Schreier map
`frobenius R 2 + id` has range of index two. -/
theorem index_range_frobenius_two_add_id (R : Type*) [CommRing R] [IsLocalRing R] [Finite R]
    [CharP R 2] :
    ((frobenius R 2).toAddMonoidHom + AddMonoidHom.id R).range.index = 2 := by
  rw [AddSubgroup.index_range]
  have hker : (((frobenius R 2).toAddMonoidHom + AddMonoidHom.id R).ker : Set R) =
      {0, 1} := by
    ext t
    simp [frobenius_def]
  rw [← SetLike.coe_sort_coe, hker, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]

/-- On a finite commutative local ring of characteristic two, the sum of two elements outside
the range of `t ↦ t² + t` lies in the range. -/
theorem add_mem_range_sq_add_self {R : Type*} [CommRing R] [IsLocalRing R] [Finite R]
    [CharP R 2] {a b : R} (ha : a ∉ Set.range (fun t : R => t ^ 2 + t))
    (hb : b ∉ Set.range (fun t : R => t ^ 2 + t)) :
    a + b ∈ Set.range (fun t : R => t ^ 2 + t) := by
  have h := AddSubgroup.add_mem_iff_of_index_two (index_range_frobenius_two_add_id R)
    (a := a) (b := b)
  simpa [AddMonoidHom.mem_range, frobenius_def, ← Set.mem_range, ha, hb] using h

/-- **Artin–Schreier over a finite field of characteristic two.** For `s` in a finite field `k`
of characteristic two, the equation `t ^ 2 + t = s` has a solution in `k` if and only if the
absolute trace of `s` to `ZMod 2` vanishes. -/
theorem exists_sq_add_self_eq_iff_trace_eq_zero {k : Type*} [Field k] [Finite k]
    [Algebra (ZMod 2) k] {s : k} :
    (∃ t : k, t ^ 2 + t = s) ↔ Algebra.trace (ZMod 2) k s = 0 := by
  have : CharP k 2 := (Algebra.charP_iff (ZMod 2) k 2).mp (ZMod.charP 2)
  set φ := (frobenius k 2).toAddMonoidHom + AddMonoidHom.id k
  have hφ (t : k) : φ t = t ^ 2 + t := by simp [φ, frobenius_def]
  let T := (Algebra.trace (ZMod 2) k).toAddMonoidHom
  have hT (x : k) : T x = Algebra.trace (ZMod 2) k x := rfl
  -- The trace kills `t ^ 2 + t`, because it is invariant under the Frobenius.
  have hle : φ.range ≤ T.ker := by
    rintro _ ⟨t, rfl⟩
    have hfr := Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquiv (ZMod 2) k 2) t
    rw [FiniteField.frobeniusAlgEquiv_apply, ZMod.card] at hfr
    rw [AddMonoidHom.mem_ker, hφ, hT, map_add, hfr, CharTwo.add_self_eq_zero]
  -- The trace is onto `ZMod 2`, so its kernel has index two, like the range of `φ`.
  have hTindex : T.ker.index = 2 := by
    obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := by
      by_contra! h
      exact Algebra.trace_ne_zero (ZMod 2) k (LinearMap.ext h)
    have htop : T.range = ⊤ := by
      refine eq_top_iff.mpr fun y _ ↦ ?_
      rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) y with rfl | rfl
      · exact T.range.zero_mem
      · rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) (T x) with h | h
        · exact absurd h hx
        · exact ⟨x, h⟩
    rw [AddSubgroup.index_ker, htop, AddSubgroup.card_top, Nat.card_zmod]
  have heq : φ.range = T.ker := by
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    have h₁ := φ.range.card_mul_index
    have h₂ := T.ker.card_mul_index
    rw [index_range_frobenius_two_add_id] at h₁
    rw [hTindex] at h₂
    omega
  rw [← hT, ← AddMonoidHom.mem_ker, ← heq, AddMonoidHom.mem_range]
  simp only [hφ]

end TauCeti
