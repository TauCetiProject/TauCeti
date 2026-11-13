/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LyndonLength.FreeGroup
import TauCeti.GroupTheory.FreeGroup.BigPowers

/-!
# Separated elements for a Lyndon length function

Let `l` be a Lyndon length function on a group `G`. The Gromov product `c((uᵐ)⁻¹, vⁿ)` measures
the cancellation in the product `uᵐ vⁿ`. Two elements `u`, `v` are *separated* when this
cancellation does not depend on `m` and `n` once they are large: there is `r` such that for all
`m, n ≥ r` the cancellation in `uᵐ vⁿ` is the cancellation in `uʳ vʳ`. Myasnikov, Remeslennikov
and Serbin introduce this notion for groups of infinite words; any two elements of a free group
that do not commute are separated for the word length.

The paper states the definition through the cyclic decompositions `u = c⁻¹ ∘ u₁ ∘ c`,
`v = d⁻¹ ∘ v₁ ∘ d`, asking for cancellation less than `max (|c|, |d|)` around `uʳ vʳ`. Read
literally, no two cyclically reduced elements would be separated; its proofs use the definition
as the stabilization of the cancellation, which is the form given here.

## Main definitions

* `TauCeti.LyndonLength.IsSeparated`: separated pairs of elements.

## Main results

* `TauCeti.LyndonLength.isSeparated_iff_map_mul`: separation in terms of lengths of products.
* `TauCeti.LyndonLength.not_isSeparated_inv`: for a free Lyndon length function, a nontrivial
  element is not separated from its inverse.
* `TauCeti.LyndonLength.isSeparated_freeGroupNorm`: non-commuting elements of a free group are
  separated.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, Definition 6.2 and Lemma 6.5.
-/

public section

namespace TauCeti.LyndonLength

variable {G Λ : Type*} [Group G] [AddCommGroup Λ] [LinearOrder Λ]

/-- Two elements `u`, `v` are *separated* for a Lyndon length function when the cancellation in
`uᵐ vⁿ`, measured by the Gromov product `c((uᵐ)⁻¹, vⁿ)`, is the same for all large `m` and `n`. -/
def IsSeparated (l : LyndonLength G Λ) (u v : G) : Prop :=
  ∃ r : ℕ, ∀ m n : ℕ, r ≤ m → r ≤ n →
    l.gromovProduct (u ^ m)⁻¹ (v ^ n) = l.gromovProduct (u ^ r)⁻¹ (v ^ r)

/-- The defining property of separated elements. -/
theorem isSeparated_iff {l : LyndonLength G Λ} {u v : G} : l.IsSeparated u v ↔
    ∃ r : ℕ, ∀ m n : ℕ, r ≤ m → r ≤ n →
      l.gromovProduct (u ^ m)⁻¹ (v ^ n) = l.gromovProduct (u ^ r)⁻¹ (v ^ r) := Iff.rfl

/-- In terms of lengths: `u`, `v` are separated when
`l (uᵐ vⁿ) + l (uʳ) + l (vʳ) = l (uʳ vʳ) + l (uᵐ) + l (vⁿ)` for all large `m`, `n`. -/
theorem isSeparated_iff_map_mul [IsOrderedAddMonoid Λ] {l : LyndonLength G Λ} {u v : G} :
    l.IsSeparated u v ↔ ∃ r : ℕ, ∀ m n : ℕ, r ≤ m → r ≤ n →
      l (u ^ m * v ^ n) + l (u ^ r) + l (v ^ r) =
        l (u ^ r * v ^ r) + l (u ^ m) + l (v ^ n) := by
  refine exists_congr fun r => forall₄_congr fun m n _ _ => ?_
  simp only [gromovProduct_eq_gromovProduct_iff, map_inv_eq_map, inv_inv]
  grind

/-- For a free Lyndon length function, a nontrivial element is not separated from its inverse. -/
theorem not_isSeparated_inv [IsOrderedAddMonoid Λ] {l : LyndonLength G Λ} (hl : l.IsFree) {u : G}
    (hu : u ≠ 1) : ¬l.IsSeparated u u⁻¹ := by
  rintro ⟨r, hr⟩
  -- At `m = n`, the cancellation in `uᵐ u⁻ᵐ` is `l (uᵐ)`, which would be constant for `m ≥ r`.
  have hconst (m : ℕ) (hm : r ≤ m) : l (u ^ m) = l (u ^ r) := by
    simpa using hr m m hm hm
  -- If `uʳ = 1` then `l u = l (uʳ⁺¹) = l (uʳ) = 0`; otherwise `l (u²ʳ) > l (uʳ)` by (L5).
  rcases eq_or_ne (u ^ r) 1 with h1 | h1
  · exact hu (hl.eq_one_of_map_eq_zero (by simpa [h1, pow_succ] using hconst (r + 1) r.le_succ))
  · exact (hl.lt_map_sq _ h1).ne' (by rw [← pow_mul, hconst _ (Nat.le_mul_of_pos_right r two_pos)])

/-- Two elements of a free group that do not commute are separated for the word length. -/
theorem isSeparated_freeGroupNorm {α : Type*} [DecidableEq α] {u v : FreeGroup α}
    (h : ¬Commute u v) : (freeGroupNorm α).IsSeparated u v := by
  -- The reduced words of `u⁻ᵐ` and `vⁿ` begin with prefixes of the rays of `u⁻¹` and `v`, and
  -- these rays differ in their first `L` letters.
  set L := u.norm * v.norm
  have hL : (u⁻¹ ^ L).toWord.take L ≠ (v ^ L).toWord.take L := fun heq =>
    h (Commute.inv_left_iff.1
      (FreeGroup.commute_of_take_toWord_pow_eq (by rw [FreeGroup.norm_inv_eq]) heq))
  have key (m n : ℕ) (hm : L ≤ m) (hn : L ≤ n) :
      List.commonPrefixLength (u⁻¹ ^ m).toWord (v ^ n).toWord =
        List.commonPrefixLength ((u⁻¹ ^ L).toWord.take L) ((v ^ L).toWord.take L) := by
    rw [← FreeGroup.take_toWord_pow_of_le u⁻¹ hm, ← FreeGroup.take_toWord_pow_of_le v hn] at hL ⊢
    rw [List.commonPrefixLength_take_left, List.commonPrefixLength_take_right, ← min_assoc,
      min_self, min_eq_right]
    by_contra! hlt
    exact hL (List.le_commonPrefixLength_iff.1 hlt.le).2.2
  refine ⟨L, fun m n hm hn => ?_⟩
  rw [← inv_pow, ← inv_pow, gromovProduct_freeGroupNorm, gromovProduct_freeGroupNorm, key m n hm hn,
    key L L le_rfl le_rfl]

end TauCeti.LyndonLength
