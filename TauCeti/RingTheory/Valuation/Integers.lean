/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Rings of integers: domains and perfection

A ring of integers `O` for a valuation `v` on a domain `R` (in the sense of `Valuation.Integers`)
embeds into `R`, so it is a domain.

If `O` is a ring of integers for a valuation `v` on a ring `R` (in the sense of
`Valuation.Integers`) and `R` is perfect, then so is `O`: a `p`-th root of an integral element is
integral, since `v y ^ p ≤ 1` forces `v y ≤ 1`. For instance the ring of integers `𝒪_F` of a
perfect valued field `F` of characteristic `p` is perfect, as is needed to form the Witt vectors
`W(𝒪_F)` with their Teichmüller expansions.

A domain is the ring of integers of its trivial valuation, so constructions taking a ring of
integers, such as the Gauss valuations on Witt vectors, apply to a perfect field with its trivial
valuation.

## Main results

* `Valuation.Integers.isDomain`: the ring of integers of a domain is a domain.
* `Valuation.Integers.perfectRing`: the ring of integers of a perfect ring is perfect.
* `Valuation.integers_one`: a domain is the ring of integers of its trivial valuation.
-/

public section

namespace Valuation.Integers

variable {R Γ₀ O : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
  [CommRing O] [Algebra O R]

/-- **The ring of integers of a domain is a domain**, as it embeds into it. -/
theorem isDomain [IsDomain R] (hv : v.Integers O) : IsDomain O :=
  Function.Injective.isDomain _ hv.hom_inj

/-- **The ring of integers of a perfect ring is perfect.** If `O` is a ring of integers for a
valuation on a ring `R` that is perfect for the exponent `p`, then `O` is perfect for `p`. -/
theorem perfectRing (hv : v.Integers O) (p : ℕ) [PerfectRing R p] : PerfectRing O p := by
  rcases eq_or_ne p 0 with rfl | hp
  · -- For `p = 0` the map `x ↦ x ^ 0` is constant, so `R`, and hence `O`, is trivial.
    have : Subsingleton R := subsingleton_of_zero_eq_one <|
      (PerfectRing.bijective_frobenius (R := R) (p := 0)).1 (by simp only [pow_zero])
    have : Subsingleton O := hv.hom_inj.subsingleton
    exact ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨x, Subsingleton.elim _ _⟩⟩⟩
  refine ⟨⟨fun x y hxy ↦ hv.hom_inj ?_, fun x ↦ ?_⟩⟩
  · refine (PerfectRing.bijective_frobenius (R := R) (p := p)).1 ?_
    simpa only [map_pow] using congrArg (algebraMap O R) hxy
  · obtain ⟨y, hy⟩ : ∃ y : R, y ^ p = algebraMap O R x :=
      (PerfectRing.bijective_frobenius (R := R) (p := p)).2 _
    have hyv : v y ≤ 1 := by
      rw [← pow_le_one_iff hp, ← map_pow, hy]
      exact hv.map_le_one x
    obtain ⟨z, rfl⟩ := hv.exists_of_le_one hyv
    exact ⟨z, hv.hom_inj (by simpa only [map_pow] using hy)⟩

end Valuation.Integers

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] [Nontrivial R]
  [NoZeroDivisors R] [DecidablePred fun x : R ↦ x = 0]

/-- **A domain is the ring of integers of its trivial valuation**, which is at most `1`
everywhere. -/
theorem integers_one : (1 : Valuation R Γ₀).Integers R :=
  ⟨Function.injective_id, one_apply_le_one, fun r _ ↦ ⟨r, rfl⟩⟩

end Valuation
