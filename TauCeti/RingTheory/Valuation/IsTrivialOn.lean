/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.LinearIndependent

/-!
# Valuations trivial on a base ring

A valuation trivial on a base ring stays trivial on that base when restricted along a map of
algebras over it. The restriction changes where the valuation is evaluated but not what it does to
constants, because an algebra map fixes them.

A valuation trivial on a base ring also sees the base as scalars of size one, so a family of
elements with pairwise distinct nonzero valuations is linearly independent over the base, by
`Valuation.linearIndependent_of_map_smul_ne`.

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
on which the valuation is trivial. Such a valuation gives each nonzero multiple `a • f i` the
valuation of `f i`, so this is the case of `Valuation.linearIndependent_of_map_smul_ne` with
trivial scalars. -/
theorem linearIndependent_of_injective {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    (v : Valuation B Γ₀) [v.IsTrivialOn A] {ι : Type*} {f : ι → B} (hf : ∀ i, v (f i) ≠ 0)
    (hinj : Function.Injective (v ∘ f)) : LinearIndependent A f := by
  have hval : ∀ i (a : A), a ≠ 0 → v (a • f i) = v (f i) := fun i a ha ↦ by
    rw [Algebra.smul_def, v.map_mul, IsTrivialOn.eq_one (v := v) a ha, one_mul]
  refine v.linearIndependent_of_map_smul_ne (fun i a ha ↦ by rw [hval i a ha]; exact hf i)
    fun i j hij a b ha hb ↦ ?_
  rw [hval i a ha, hval j b hb]
  exact fun h ↦ hij (hinj h)

end Valuation

end
