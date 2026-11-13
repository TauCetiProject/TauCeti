/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.PositiveDegrees.Map

/-!
# Positive multiples of a positive degree

For positive degree data `δ` on an allowed monoid `P` and a positive integer `c`, the multiple
`c δ` is again positive degree data on `P`, and the degrees of `c δ` exceed `k` exactly when
those of `δ` exceed `⌊k / c⌋`.

Consequently the identity change of degree from `δ` to `c δ` (`PositiveDegreeMap.changeDegree`)
has cutoff modulus at most `⌊k / c⌋`, and the reverse change has cutoff modulus at most `c k`.
Both bounds are equalities as soon as `δ` takes the value one on `P`.

Adapted from `Mei/Algebra/PositiveDegrees/Scale.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, released under Apache 2.0.
-/

public section

namespace TauCeti

variable {N : Type*} [AddCommMonoid N]

namespace PositiveDegrees

variable (d : PositiveDegrees N) (c : ℕ) [NeZero c]

/-- The positive degree data `c δ` on the same allowed monoid, for a positive integer `c`. -/
def scale : PositiveDegrees N where
  monoid := d.monoid
  degree := (AddMonoidHom.mulLeft (c : ℤ)).comp d.degree
  degree_pos hn hne :=
    mul_pos (by exact_mod_cast NeZero.pos c) (d.degree_pos hn hne)
  finite_le k := (d.finite_le k).subset fun n ⟨hn, hk⟩ =>
    ⟨hn, (le_mul_of_one_le_left (d.degree_nonneg hn)
      (by exact_mod_cast NeZero.one_le)).trans hk⟩

/-- Scaling keeps the allowed monoid. -/
@[simp]
theorem scale_monoid : (d.scale c).monoid = d.monoid := (rfl)

/-- The scaled degree is the multiple `c δ`. -/
@[simp]
theorem scale_degree (n : N) : (d.scale c).degree n = c * d.degree n := (rfl)

/-- Scaling by one is the identity. -/
@[simp]
theorem scale_one : d.scale 1 = d :=
  PositiveDegrees.ext (d.scale_monoid 1) (AddMonoidHom.ext fun n => by simp)

/-- The degree `c δ` exceeds `k` exactly when `δ` exceeds `⌊k / c⌋`. -/
theorem lt_scale_degree_iff {k : ℕ} {n : N} :
    (k : ℤ) < (d.scale c).degree n ↔ ((k / c : ℕ) : ℤ) < d.degree n := by
  rw [scale_degree, Int.natCast_div, Int.ediv_lt_iff_lt_mul (by exact_mod_cast NeZero.pos c),
    mul_comm]

end PositiveDegrees

namespace PositiveDegreeMap

variable (d : PositiveDegrees N) (c : ℕ) [NeZero c]

/-- Changing from `δ` to `c δ` needs source cutoff at most `⌊k / c⌋` at target order `k`. -/
theorem changeDegree_self_scale_modulus_le (k : ℕ) :
    (changeDegree d (d.scale c) (d.scale_monoid c).symm).modulus k ≤ k / c :=
  (changeDegree_modulus_le_iff _ _ _ _ _).mpr fun _ _ hk =>
    not_lt.mp fun h => (not_lt.mpr hk) ((d.lt_scale_degree_iff c).mpr h)

/-- Changing from `c δ` back to `δ` needs source cutoff at most `c k` at target order `k`. -/
theorem changeDegree_scale_self_modulus_le (k : ℕ) :
    (changeDegree (d.scale c) d (d.scale_monoid c)).modulus k ≤ c * k :=
  (changeDegree_modulus_le_iff _ _ _ _ _).mpr fun _ _ hk => by
    rw [PositiveDegrees.scale_degree, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hk (Int.natCast_nonneg c)

variable {d}

/-- If `δ` takes the value one on the allowed monoid, the change from `δ` to `c δ` has
modulus exactly `⌊k / c⌋`. -/
theorem changeDegree_self_scale_modulus {n : N} (hn : n ∈ d.monoid) (h1 : d.degree n = 1)
    (k : ℕ) : (changeDegree d (d.scale c) (d.scale_monoid c).symm).modulus k = k / c := by
  have hdeg (m : ℕ) : d.degree (m • n) = m := by simp [h1]
  refine le_antisymm (changeDegree_self_scale_modulus_le d c k) ?_
  have h := (changeDegree d (d.scale c) (d.scale_monoid c).symm).degree_le k
    (d.monoid.nsmul_mem hn (k / c)) (by
      rw [changeDegree_apply, PositiveDegrees.scale_degree, hdeg]
      exact_mod_cast Nat.mul_div_le k c)
  rw [hdeg] at h
  exact_mod_cast h

/-- If `δ` takes the value one on the allowed monoid, the change from `c δ` back to `δ` has
modulus exactly `c k`. -/
theorem changeDegree_scale_self_modulus {n : N} (hn : n ∈ d.monoid) (h1 : d.degree n = 1)
    (k : ℕ) : (changeDegree (d.scale c) d (d.scale_monoid c)).modulus k = c * k := by
  have hdeg (m : ℕ) : d.degree (m • n) = m := by simp [h1]
  refine le_antisymm (changeDegree_scale_self_modulus_le d c k) ?_
  have h := (changeDegree (d.scale c) d (d.scale_monoid c)).degree_le k
    (d.monoid.nsmul_mem hn k) (by rw [changeDegree_apply, hdeg])
  rw [PositiveDegrees.scale_degree, hdeg] at h
  exact_mod_cast h

end PositiveDegreeMap

end TauCeti
