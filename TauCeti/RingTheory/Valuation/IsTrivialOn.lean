/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations trivial on a base ring

A valuation trivial on a base ring stays trivial on that base when restricted along a map of
algebras over it. The restriction changes where the valuation is evaluated but not what it does to
constants, because an algebra map fixes them.

A valuation trivial on a base ring also sees the base as scalars of size one, so a family of
elements with pairwise distinct nonzero valuations is linearly independent over the base: in a
linear combination with a nonzero coefficient, the summand of largest valuation dominates and the
combination cannot vanish.

## Main results

* `Valuation.IsTrivialOn.comap`: **restriction preserves triviality on the base**, for a valuation
  on any algebra restricted along any algebra map over that base.
* `Valuation.linearIndependent_of_injective`: **elements of pairwise distinct nonzero valuations
  are linearly independent** over a base ring on which the valuation is trivial.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], for valuations, their restriction along a ring map,
  and triviality on a base ring.
-/

public section

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Restricting a valuation along an algebra map preserves triviality on the base.** An algebra
map fixes the base, so the restricted valuation takes the same values on constants. -/
instance IsTrivialOn.comap {A B C : Type*} [CommSemiring A] [Ring B] [Ring C] [Algebra A B]
    [Algebra A C] (v : Valuation C Γ₀) (f : B →ₐ[A] C) [v.IsTrivialOn A] :
    (v.comap f.toRingHom).IsTrivialOn A where
  eq_one a ha := by simpa using Valuation.IsTrivialOn.eq_one (v := v) a ha

/-- **Elements of pairwise distinct nonzero valuations are linearly independent** over a base ring
on which the valuation is trivial. A nontrivial linear combination has, among its summands with
nonzero coefficient, a unique one of largest valuation, and that summand dictates the valuation of
the sum, which is therefore nonzero. -/
theorem linearIndependent_of_injective {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    (v : Valuation B Γ₀) [v.IsTrivialOn A] {ι : Type*} {f : ι → B} (hf : ∀ i, v (f i) ≠ 0)
    (hinj : Function.Injective (v ∘ f)) : LinearIndependent A f := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  -- Restrict to the summands with nonzero coefficient; they have the same sum.
  set t := s.filter fun i ↦ g i ≠ 0 with ht
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  have hsum' : ∑ i ∈ t, g i • f i = 0 := by
    rw [← hsum, ht]
    exact Finset.sum_filter_of_ne fun i _ h hg ↦ h (by rw [hg, zero_smul])
  -- Each remaining summand has the valuation of the vector it scales.
  have hval : ∀ i ∈ t, v (g i • f i) = v (f i) := fun i hi ↦ by
    rw [Algebra.smul_def, v.map_mul, IsTrivialOn.eq_one (v := v) _ (Finset.mem_filter.mp hi).2,
      one_mul]
  -- The summand of largest valuation is unique, so it dictates the valuation of the sum.
  obtain ⟨j, hjt, hmax⟩ := t.exists_max_image (fun i ↦ v (f i)) ⟨i, hit⟩
  have hlt : ∀ i ∈ t \ {j}, v (g i • f i) < v (g j • f j) := fun i hi ↦ by
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    rw [hval i hi.1, hval j hjt]
    exact lt_of_le_of_ne (hmax i hi.1) fun h ↦ hi.2 (hinj h)
  have h := v.map_sum_eq_of_lt hjt hlt
  rw [hsum', v.map_zero, hval j hjt] at h
  exact hf j h.symm

end Valuation

end
