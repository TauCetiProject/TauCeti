/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Separated elements for a Lyndon length function

Let `l` be a Lyndon length function on a group `G`. The Gromov product `c((uᵐ)⁻¹, vⁿ)` measures
the cancellation in the product `uᵐ vⁿ`. Two elements `u`, `v` are *separated* when this
cancellation does not depend on `m` and `n` once they are large: there is `r` such that for all
`m, n ≥ r` the cancellation in `uᵐ vⁿ` is the cancellation in `uʳ vʳ`. Myasnikov, Remeslennikov
and Serbin introduce this notion for groups of infinite words; any two elements of a free group
that do not commute are separated for the word length
(`TauCeti.LyndonLength.isSeparated_freeGroupNorm_of_not_commute`).

The paper states the definition through the cyclic decompositions `u = c⁻¹ ∘ u₁ ∘ c`,
`v = d⁻¹ ∘ v₁ ∘ d`, asking for cancellation less than `max (|c|, |d|)` around `uʳ vʳ`. Read
literally, no two cyclically reduced elements would be separated; its proofs use the definition
as the stabilization of the cancellation, which is the form given here.

## Main definitions

* `TauCeti.LyndonLength.IsSeparated`: separated pairs of elements.

## Main results

* `TauCeti.LyndonLength.isSeparated_iff_map_mul`: separation in terms of lengths of products.
* `TauCeti.LyndonLength.isSeparated_comap_iff`: separation for the restriction of a length
  function along a homomorphism.
* `TauCeti.LyndonLength.isSeparated_inv_inv_iff`, `TauCeti.LyndonLength.IsSeparated.pow_left`,
  `TauCeti.LyndonLength.IsSeparated.pow_right`: separation under inverses and powers.
* `TauCeti.LyndonLength.IsFree.not_isSeparated_inv_right`: for a free Lyndon length function, a
  nontrivial element is not separated from its inverse.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, Definition 6.2.
-/

public section

namespace TauCeti.LyndonLength

variable {G H Λ : Type*} [Group G] [Group H] [AddCommGroup Λ] [LinearOrder Λ]

/-- Two elements `u`, `v` are *separated* for a Lyndon length function when the cancellation in
`uᵐ vⁿ`, measured by the Gromov product `c((uᵐ)⁻¹, vⁿ)`, is the same for all large `m` and `n`. -/
def IsSeparated (l : LyndonLength G Λ) (u v : G) : Prop :=
  ∃ r : ℕ, ∀ m n : ℕ, r ≤ m → r ≤ n →
    l.gromovProduct (u ^ m)⁻¹ (v ^ n) = l.gromovProduct (u ^ r)⁻¹ (v ^ r)

/-- The defining property of separated elements. -/
theorem isSeparated_iff {l : LyndonLength G Λ} {u v : G} : l.IsSeparated u v ↔
    ∃ r : ℕ, ∀ m n : ℕ, r ≤ m → r ≤ n →
      l.gromovProduct (u ^ m)⁻¹ (v ^ n) = l.gromovProduct (u ^ r)⁻¹ (v ^ r) := Iff.rfl

variable [IsOrderedAddMonoid Λ]

/-- For the zero length function, any two elements are separated. -/
@[simp]
theorem isSeparated_zero (u v : G) : (0 : LyndonLength G Λ).IsSeparated u v :=
  ⟨0, fun _ _ _ _ => by rw [gromovProduct_eq_gromovProduct_iff]; simp⟩

/-- In terms of lengths: `u`, `v` are separated when
`l (uᵐ vⁿ) + l (uʳ) + l (vʳ) = l (uʳ vʳ) + l (uᵐ) + l (vⁿ)` for all large `m`, `n`. -/
theorem isSeparated_iff_map_mul {l : LyndonLength G Λ} {u v : G} :
    l.IsSeparated u v ↔ ∃ r : ℕ, ∀ m n : ℕ, r ≤ m → r ≤ n →
      l (u ^ m * v ^ n) + l (u ^ r) + l (v ^ r) =
        l (u ^ r * v ^ r) + l (u ^ m) + l (v ^ n) := by
  refine exists_congr fun r => forall₄_congr fun m n _ _ => ?_
  simp only [gromovProduct_eq_gromovProduct_iff, map_inv_eq_map, inv_inv]
  grind

/-- The identity is separated from every element. -/
@[simp]
theorem isSeparated_one_left (l : LyndonLength G Λ) (v : G) : l.IsSeparated 1 v :=
  ⟨0, fun _ _ _ _ => by simp⟩

/-- Every element is separated from the identity. -/
@[simp]
theorem isSeparated_one_right (l : LyndonLength G Λ) (u : G) : l.IsSeparated u 1 :=
  ⟨0, fun _ _ _ _ => by simp⟩

/-- Separation for the restriction of a length function along a homomorphism `φ` is separation
of the images under `φ`. -/
@[simp]
theorem isSeparated_comap_iff {l : LyndonLength G Λ} {φ : H →* G} {u v : H} :
    (l.comap φ).IsSeparated u v ↔ l.IsSeparated (φ u) (φ v) := by
  simp [isSeparated_iff]

/-- `u⁻¹` and `v⁻¹` are separated exactly when `v` and `u` are. -/
@[simp]
theorem isSeparated_inv_inv_iff {l : LyndonLength G Λ} {u v : G} :
    l.IsSeparated u⁻¹ v⁻¹ ↔ l.IsSeparated v u := by
  simp only [isSeparated_iff, inv_pow, inv_inv]
  refine exists_congr fun r => ⟨fun h m n hm hn => ?_, fun h m n hm hn => ?_⟩ <;>
    rw [gromovProduct_comm, h n m hn hm, gromovProduct_comm]

/-- If `u` and `v` are separated, then so are `v⁻¹` and `u⁻¹`. -/
theorem IsSeparated.inv_inv {l : LyndonLength G Λ} {u v : G} (h : l.IsSeparated u v) :
    l.IsSeparated v⁻¹ u⁻¹ :=
  isSeparated_inv_inv_iff.2 h

/-- If `u` and `v` are separated, then so are `uᵏ` and `v`. -/
theorem IsSeparated.pow_left {l : LyndonLength G Λ} {u v : G} (h : l.IsSeparated u v) (k : ℕ) :
    l.IsSeparated (u ^ k) v := by
  obtain _ | k := k
  · simp
  obtain ⟨r, hr⟩ := h
  refine ⟨r, fun m n hm hn => ?_⟩
  rw [← pow_mul, ← pow_mul, hr _ n (hm.trans (Nat.le_mul_of_pos_left m k.succ_pos)) hn,
    hr _ r (Nat.le_mul_of_pos_left r k.succ_pos) le_rfl]

/-- If `u` and `v` are separated, then so are `u` and `vᵏ`. -/
theorem IsSeparated.pow_right {l : LyndonLength G Λ} {u v : G} (h : l.IsSeparated u v) (k : ℕ) :
    l.IsSeparated u (v ^ k) := by
  simpa using (h.inv_inv.pow_left k).inv_inv

/-- For a free Lyndon length function, a nontrivial element is not separated from its inverse. -/
theorem IsFree.not_isSeparated_inv_right {l : LyndonLength G Λ} (hl : l.IsFree) {u : G}
    (hu : u ≠ 1) : ¬l.IsSeparated u u⁻¹ := by
  rintro ⟨r, hr⟩
  -- At `m = n`, the cancellation in `uᵐ u⁻ᵐ` is `l (uᵐ)`, which would be constant for `m ≥ r`.
  have hconst (m : ℕ) (hm : r ≤ m) : l (u ^ m) = l (u ^ r) := by
    simpa using hr m m hm hm
  -- If `uʳ = 1` then `l u = l (uʳ⁺¹) = l (uʳ) = 0`; otherwise `l (u²ʳ) > l (uʳ)` by (L5).
  rcases eq_or_ne (u ^ r) 1 with h1 | h1
  · exact hu (hl.eq_one_of_map_eq_zero (by simpa [h1, pow_succ] using hconst (r + 1) r.le_succ))
  · exact (hl.lt_map_sq _ h1).ne' (by rw [← pow_mul, hconst _ (Nat.le_mul_of_pos_right r two_pos)])

/-- For a free Lyndon length function, the inverse of a nontrivial element is not separated from
the element. -/
theorem IsFree.not_isSeparated_inv_left {l : LyndonLength G Λ} (hl : l.IsFree) {u : G}
    (hu : u ≠ 1) : ¬l.IsSeparated u⁻¹ u := by
  simpa using hl.not_isSeparated_inv_right (inv_ne_one.2 hu)

end TauCeti.LyndonLength
