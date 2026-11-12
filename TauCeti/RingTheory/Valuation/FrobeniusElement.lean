/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Maps raising residues to the `q`-th power

Let `v` be a valuation on a field `L` and `q` a natural number. A map `τ : L → L` with
`v (τ x - x ^ q) < 1` for every `x` in the valuation ring acts on the residue field of `v` as the
`q`-power map: it preserves the valuation ring, and the residue of `τ x` is the `q`-th power of
the residue of `x`. When `τ` is a ring endomorphism and `q ≠ 0`, it also keeps elements outside
the valuation ring outside it, since it sends `x⁻¹` into the maximal ideal. A Frobenius element
of a Galois group at a place with finite residue field is the standard example.

## Main results

* `Valuation.exists_le_one_and_residue_eq_pow`: such a map preserves the valuation ring and raises
  residues to the `q`-th power.
* `Valuation.one_lt_map_of_one_lt`: such a ring endomorphism keeps a pole a pole.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.
-/

public section

open IsLocalRing

namespace Valuation

variable {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
  {q : ℕ}

/-- **A map raising residues to the `q`-th power preserves the valuation ring.** If
`v (τ x - x ^ q) < 1` for every `x` in the valuation ring of `v`, then `τ z` is integral for
integral `z`, and the residue of `τ z` is the `q`-th power of the residue of `z`. -/
theorem exists_le_one_and_residue_eq_pow {τ : L → L} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ q) < 1)
    {z : L} (hz : v z ≤ 1) :
    ∃ hτz : v (τ z) ≤ 1,
      residue v.valuationSubring ⟨τ z, (v.mem_valuationSubring_iff _).mpr hτz⟩ =
        residue v.valuationSubring ⟨z, (v.mem_valuationSubring_iff z).mpr hz⟩ ^ q := by
  have hzq : v (z ^ q) ≤ 1 := by
    rw [map_pow]
    exact pow_le_one' hz _
  have hτz : v (τ z) ≤ 1 := by
    rw [← sub_add_cancel (τ z) (z ^ q)]
    exact v.map_add_le (hτ z hz).le hzq
  refine ⟨hτz, ?_⟩
  rw [← _root_.map_pow, ← sub_eq_zero, ← _root_.map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_iff]
  exact hτ z hz

/-- **A ring endomorphism raising residues to a positive power keeps a pole a pole.** If
`v (τ x - x ^ q) < 1` for every `x` in the valuation ring of `v`, with `q ≠ 0`, then `1 < v x`
implies `1 < v (τ x)`, since `τ` sends `x⁻¹` into the maximal ideal. -/
theorem one_lt_map_of_one_lt {R : Type*} [FunLike R L L] [RingHomClass R L L] (hq : q ≠ 0)
    {τ : R} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ q) < 1) {x : L} (hx : 1 < v x) :
    1 < v (τ x) := by
  have hinv : v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hx
  have h' : v (τ x⁻¹) < 1 := by
    rw [← sub_add_cancel (τ x⁻¹) (x⁻¹ ^ q)]
    refine v.map_add_lt (hτ _ hinv.le) ?_
    rw [map_pow]
    exact pow_lt_one₀ zero_le hinv hq
  have hx0 : τ x ≠ 0 := (map_ne_zero τ).mpr (v.ne_zero_iff.mp (zero_lt_one.trans hx).ne')
  rwa [map_inv₀, map_inv₀, inv_lt_one₀ (v.pos_iff.mpr hx0)] at h'

end Valuation
