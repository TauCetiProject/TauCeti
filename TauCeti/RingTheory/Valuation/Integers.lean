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

A ring is its own ring of integers for any valuation that is at most `1` everywhere, for instance
a domain for its trivial valuation. So constructions taking a ring of integers, such as the Gauss
valuations on Witt vectors, apply to a perfect field with its trivial valuation.

## Main results

* `Valuation.Integers.isDomain`: the ring of integers of a domain is a domain.
* `Valuation.Integers.perfectRing`: the ring of integers of a perfect ring is perfect.
* `Valuation.integers_self_iff`: a ring is the ring of integers of a valuation on it iff the
  valuation is at most `1` everywhere.
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
  have hR := PerfectRing.bijective_frobenius (R := R) (p := p)
  refine ⟨⟨fun x y hxy ↦ hv.hom_inj <| hR.1 ?_, fun x ↦ ?_⟩⟩
  · simpa only [map_pow] using congrArg (algebraMap O R) hxy
  obtain ⟨y, hy⟩ : ∃ y, y ^ p = algebraMap O R x := hR.2 _
  have hyv : v y ≤ 1 := by
    rcases eq_or_ne p 0 with rfl | hp
    · -- For `p = 0` the injectivity of `x ↦ x ^ 0` forces `y = 1`.
      rw [hR.1 (show y ^ 0 = 1 ^ 0 by simp only [pow_zero]), map_one]
    · rw [← pow_le_one_iff hp, ← map_pow, hy]
      exact hv.map_le_one x
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hyv
  exact ⟨z, hv.hom_inj (by simpa only [map_pow] using hy)⟩

end Valuation.Integers

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}

/-- **A ring is the ring of integers of a valuation on it exactly when the valuation is at most
`1` everywhere.** For instance a domain is the ring of integers of its trivial valuation
(`Valuation.one_apply_le_one`). -/
theorem integers_self_iff : v.Integers R ↔ ∀ x, v x ≤ 1 :=
  ⟨fun hv ↦ hv.map_le_one, fun h ↦ ⟨Function.injective_id, h, fun r _ ↦ ⟨r, rfl⟩⟩⟩

end Valuation
