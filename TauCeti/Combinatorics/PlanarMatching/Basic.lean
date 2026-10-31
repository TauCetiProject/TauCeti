/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ChordDiagram
import TauCeti.Data.Fin.Basic

/-!
# Planar matchings

A **planar matching** on `k` boundary points is a perfect matching of `Fin k` whose arcs do not
interleave: there are no `a < b < σ a < σ b`. Placing the points `0, …, k - 1` in order around a
circle, these are exactly the matchings whose arcs can be drawn disjointly inside the disc. They
are the matching part of the morphisms of the Temperley–Lieb diagram category, where a diagram
`n → m` has its `n + m` boundary points numbered counterclockwise around a rectangle.

The type `TauCeti.PlanarMatching k` is the subtype of `TauCeti.PerfectMatching (Fin k)` cut out by
`Equiv.Perm.IsNoncrossingMatching`, so that the perfect matching API (finiteness, decidability,
transport, arc restriction) applies unchanged and the forgetful map to perfect matchings is the
subtype inclusion. The same objects appear as the noncrossing partitions all of whose blocks are
pairs (`Finpartition.IsPairing`, in `TauCeti/Combinatorics/NoncrossingPartition/Catalan.lean`);
the involution encoding used here is the one in which diagrams are glued and composed.
The noncrossing condition depends only on the cyclic order of the boundary
points (`Function.Involutive.isNoncrossingMatching_permCongr_finRotate_iff`), and is preserved
by reversing that order (`Function.Involutive.isNoncrossingMatching_permCongr_revPerm_iff`).
This file packages these facts as the rotation and the reflection of planar matchings, two
permutations of `PlanarMatching k` satisfying the dihedral relations, and proves the innermost cup
lemma: on at least one boundary point, some arc joins two consecutive points.

## Main definitions

* `TauCeti.PlanarMatching k`: the planar matchings of `Fin k`.
* `TauCeti.PlanarMatching.rotate k`: rotating every arc one step around the circle,
  `{a, b} ↦ {a + 1, b + 1}` modulo `k`.
* `TauCeti.PlanarMatching.reflect k`: reflecting every arc in the order reversal `Fin.rev`.

## Main results

* `TauCeti.PlanarMatching.exists_val_apply_eq_val_add_one`: the innermost cup lemma.
* `TauCeti.PlanarMatching.rotate_pow_self`: `rotate k ^ k = 1`.
* `TauCeti.PlanarMatching.reflect_mul_self`: `reflect k * reflect k = 1`.
* `TauCeti.PlanarMatching.reflect_mul_rotate_mul_reflect`: the dihedral relation
  `reflect k * rotate k * reflect k = (rotate k)⁻¹`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

open Equiv

namespace TauCeti

/-- A **planar matching** on `k` boundary points: a perfect matching of `Fin k`, that is, a
fixed-point-free involution `σ`, whose arcs `{a, σ a}` do not interleave in the linear order of
`Fin k`. It is a subtype of `TauCeti.PerfectMatching (Fin k)`, so that the finiteness and
decidability instances of perfect matchings carry over unchanged. -/
abbrev PlanarMatching (k : ℕ) : Type :=
  {D : PerfectMatching (Fin k) // D.val.IsNoncrossingMatching}

namespace PlanarMatching

variable {k : ℕ}

/-- Two planar matchings are equal when they match every point with the same partner. -/
@[ext]
theorem ext {x y : PlanarMatching k} (h : ∀ a, x.1.val a = y.1.val a) : x = y :=
  Subtype.ext <| Subtype.ext <| Equiv.ext h

/-- There is no planar matching of an odd number of points. -/
theorem isEmpty_of_not_even (hk : ¬ Even k) : IsEmpty (PlanarMatching k) :=
  have := isEmpty_perfectMatching_of_not_even (α := Fin k) (by simpa using hk)
  inferInstance

/-- **The innermost cup lemma.** A planar matching of at least one point joins some point `a` to
the next point `a + 1`. Equivalently, its diagram has an arc enclosing no other boundary point. -/
theorem exists_val_apply_eq_val_add_one (x : PlanarMatching k) (hk : k ≠ 0) :
    ∃ a : Fin k, (x.1.val a : ℕ) = a + 1 := by
  have h1 : x.1.val ≠ 1 := fun h => x.1.apply_ne ⟨0, Nat.pos_of_ne_zero hk⟩ (by simp [h])
  obtain ⟨a, ha, hin⟩ := x.2.exists_forall_apply_eq_self x.1.prop.involutive h1
  refine ⟨a, le_antisymm ?_ (Fin.lt_def.mp ha)⟩
  -- A point strictly inside the innermost arc would be a fixed point of the matching.
  by_contra! h
  have hlt : (a : ℕ) + 1 < k := h.trans (x.1.val a).isLt
  exact x.1.apply_ne ⟨a + 1, hlt⟩ <| hin _ (Fin.lt_def.mpr (Nat.lt_succ_self _))
    (Fin.lt_def.mpr h)

/-! ### Rotation -/

/-- **Rotation of planar matchings**: every arc `{a, b}` moves one step around the boundary
circle, to `{finRotate k a, finRotate k b}`, that is `{a + 1, b + 1}` modulo `k`. The result is
again planar because noninterleaving depends only on the cyclic order. -/
def rotate (k : ℕ) : Perm (PlanarMatching k) :=
  (PerfectMatching.congr (finRotate k)).subtypeEquiv fun D => by
    rw [PerfectMatching.congr_val,
      D.prop.involutive.isNoncrossingMatching_permCongr_finRotate_iff]

/-- The perfect matching underlying a rotated planar matching is the transport of the original
one along `finRotate k`. -/
@[simp]
theorem coe_rotate_apply (x : PlanarMatching k) :
    (rotate k x : PerfectMatching (Fin k)) = PerfectMatching.congr (finRotate k) x := (rfl)

/-- The perfect matching underlying the inverse rotation of a planar matching is the transport of
the original one along the inverse of `finRotate k`. -/
@[simp]
theorem coe_rotate_symm_apply (x : PlanarMatching k) :
    ((rotate k).symm x : PerfectMatching (Fin k)) =
      PerfectMatching.congr (finRotate k).symm x := by
  apply (PerfectMatching.congr (finRotate k)).injective
  rw [← coe_rotate_apply, Equiv.apply_symm_apply]
  simp

/-- Rotation moves the arc `{a, x a}` to `{finRotate k a, finRotate k (x a)}`. -/
theorem rotate_apply_val_apply (x : PlanarMatching k) (a : Fin k) :
    (rotate k x).1.val (finRotate k a) = finRotate k (x.1.val a) := by
  rw [coe_rotate_apply, PerfectMatching.congr_val_apply_apply]

/-- The perfect matching underlying the `j`-fold rotation of a planar matching is its transport
along `finRotate k ^ j`. -/
theorem coe_rotate_pow_apply (j : ℕ) (x : PlanarMatching k) :
    ((rotate k ^ j) x : PerfectMatching (Fin k)) =
      PerfectMatching.congr (finRotate k ^ j : Perm (Fin k)) x := by
  induction j with
  | zero => exact (PerfectMatching.congr_refl _).symm
  | succ j ih => simp [pow_succ', ih, Perm.mul_def]

/-- Rotating `k` times around a circle of `k` boundary points is the identity. -/
@[simp]
theorem rotate_pow_self (k : ℕ) : rotate k ^ k = 1 := by
  have hr : (finRotate k ^ k : Perm (Fin k)) = 1 := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simpa [orderOf_finRotate hk] using pow_orderOf_eq_one (finRotate k)
  refine Equiv.ext fun x => Subtype.ext ?_
  rw [coe_rotate_pow_apply, hr, Perm.one_apply]
  exact PerfectMatching.congr_refl _

/-! ### Reflection -/

/-- **Reflection of planar matchings**: every arc `{a, b}` is reflected in the order reversal of
`Fin k`, to `{Fin.rev a, Fin.rev b}`. The result is again planar because reversing the order
preserves noninterleaving. -/
def reflect (k : ℕ) : Perm (PlanarMatching k) :=
  (PerfectMatching.congr Fin.revPerm).subtypeEquiv fun D => by
    rw [PerfectMatching.congr_val,
      D.prop.involutive.isNoncrossingMatching_permCongr_revPerm_iff]

/-- The perfect matching underlying a reflected planar matching is the transport of the original
one along `Fin.revPerm`. -/
@[simp]
theorem coe_reflect_apply (x : PlanarMatching k) :
    (reflect k x : PerfectMatching (Fin k)) = PerfectMatching.congr Fin.revPerm x := (rfl)

/-- Reflection moves the arc `{a, x a}` to `{Fin.rev a, Fin.rev (x a)}`. -/
theorem reflect_apply_val_apply (x : PlanarMatching k) (a : Fin k) :
    (reflect k x).1.val (Fin.rev a) = Fin.rev (x.1.val a) :=
  PerfectMatching.congr_val_apply_apply Fin.revPerm x.1 a

/-- Reflection is an involution. -/
@[simp]
theorem reflect_reflect (x : PlanarMatching k) : reflect k (reflect k x) = x := by
  ext a
  simp

/-- Reflection is its own inverse. -/
@[simp]
theorem reflect_symm (k : ℕ) : (reflect k).symm = reflect k :=
  Equiv.ext fun x => (Equiv.symm_apply_eq _).mpr (reflect_reflect x).symm

/-- Reflecting twice is the identity permutation of the planar matchings. -/
theorem reflect_mul_self (k : ℕ) : reflect k * reflect k = 1 :=
  Equiv.ext reflect_reflect

/-- **The dihedral relation**: conjugating the rotation by the reflection reverses it. -/
theorem reflect_mul_rotate_mul_reflect (k : ℕ) :
    reflect k * rotate k * reflect k = (rotate k)⁻¹ := by
  have hrev : (Fin.revPerm.trans ((finRotate k).trans Fin.revPerm) : Perm (Fin k)) =
      (finRotate k).symm := Equiv.ext fun i => by
    have := i.neZero
    simp
  refine Equiv.ext fun x => Subtype.ext ?_
  simp [Perm.inv_def, Equiv.trans_assoc, hrev]

end PlanarMatching

/-- The nested matching `{0, 3}, {1, 2}` of four points is planar, while the crossing matching
`{0, 2}, {1, 3}` is a perfect matching that is not. -/
example :
    (∃ x : PlanarMatching 4,
        x.1.val = (Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2 : Perm (Fin 4))) ∧
      ∃ D : PerfectMatching (Fin 4),
        D.val = (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3 : Perm (Fin 4)) ∧
          ¬ D.val.IsNoncrossingMatching :=
  ⟨⟨⟨⟨_, by decide⟩, by decide⟩, rfl⟩, ⟨⟨_, by decide⟩, rfl, by decide⟩⟩

/-- There are five planar matchings of six points, the Catalan number `catalan 3`. -/
example : Fintype.card (PlanarMatching 6) = 5 := by decide

/-- Rotating the nested matching `{0, 3}, {1, 2}` of four points gives the matching
`{1, 0}, {2, 3}` of consecutive points. -/
example (x : PlanarMatching 4) (hx : x.1.val = swap 0 3 * swap 1 2) :
    (PlanarMatching.rotate 4 x).1.val = swap 0 1 * swap 2 3 := by
  rw [PlanarMatching.coe_rotate_apply, PerfectMatching.congr_val, hx]
  decide

end TauCeti
