/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import TauCeti.Combinatorics.Network.WeightedDistance

/-!
# Weighted distances on small arrow families

Take three vertices `s = 0`, `a = 1` and `t = 2`, with one arrow `s → t` of weight `5` and arrows
`s → a` and `a → t` of weight `2` each. The distance from `s` to `t` is `4`, attained by the walk
through `a`; the distance from `t` to `s` is `⊤`, since no arrow leaves `t`; and the distance from
`s` to `s` is `0`.

Take one vertex with one loop. When the loop has weight `-1`, the walks from the vertex to itself
have the weights `-n` for `n : ℕ`, so no value is the distance from the vertex to itself. When the
loop has a nonnegative weight, such as `0` or `1`, the distance from the vertex to itself is `0`.
-/

public section

namespace TauCeti.Examples.WeightedDistance

/-- The arrow relation on three vertices: arrows `0 → 1`, `0 → 2` and `1 → 2`. -/
abbrev Arrow (x y : Fin 3) : Prop :=
  x = 0 ∧ y ≠ 0 ∨ x = 1 ∧ y = 2

/-- At most one arrow for each ordered pair of vertices, as given by `Arrow`. -/
abbrev Hom (x y : Fin 3) : Type :=
  PLift (Arrow x y)

/-- Weight `5` on the arrow `0 → 2` and weight `2` on the other two arrows. -/
def weight : Assignment Hom ℤ :=
  fun x y _ ↦ if x = 0 ∧ y = 2 then 5 else 2

/-- The walk `0 → 1 → 2`. -/
def viaOne : ArrowWalk Hom 0 2 :=
  ((ArrowWalk.nil 0).cons (x := 1) ⟨by decide⟩).cons (x := 2) ⟨by decide⟩

/-- The walk `0 → 1 → 2` has weight `4`. -/
theorem walkWeight_viaOne : walkWeight weight viaOne = 4 := by
  rw [viaOne, walkWeight_cons, walkWeight_cons, walkWeight_nil]
  decide

/-- Every walk from `0` to `v` weighs at least `0`, `2` or `4`, for `v = 0`, `1` or `2`. -/
theorem le_walkWeight {v : Fin 3} (p : ArrowWalk Hom 0 v) :
    ![0, 2, 4] v ≤ walkWeight weight p := by
  induction p with
  | nil => simp
  | @cons x y p e ih =>
    have key : ∀ x y : Fin 3, Arrow x y →
        ![(0 : ℤ), 2, 4] y ≤ ![0, 2, 4] x + if x = 0 ∧ y = 2 then 5 else 2 := by
      decide
    rw [walkWeight_cons]
    have := key x y e.down
    simp only [weight] at *
    linarith

/-- Every walk from `2` stays at `2`. -/
theorem eq_two_of_arrowWalk {v : Fin 3} (p : ArrowWalk Hom 2 v) : v = 2 := by
  induction p with
  | nil => rfl
  | @cons x y p e ih =>
    subst ih
    rcases e.down with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

example : IsDist weight 0 2 4 :=
  isDist_coe_iff.2 ⟨viaOne, isShortest_def.2 fun q ↦ by
    simpa [walkWeight_viaOne] using le_walkWeight q, walkWeight_viaOne⟩

example : IsDist weight 2 0 ⊤ :=
  isDist_top_iff.2 ⟨fun p ↦ absurd (eq_two_of_arrowWalk p) (by decide)⟩

example : IsDist weight 0 0 0 := by
  have h : IsShortest weight (ArrowWalk.nil 0) := isShortest_def.2 fun q ↦ by
    simpa [walkWeight_nil] using le_walkWeight q
  simpa [walkWeight_nil] using h.isDist

/-- One vertex with one loop. -/
abbrev Loop (_ _ : Unit) : Type :=
  Unit

/-- With a loop of weight `-1`, no value is the distance from the vertex to itself. -/
example : ¬∃ x, IsDist (fun _ _ _ ↦ (-1 : ℤ) : Assignment Loop ℤ) () () x := by
  rintro ⟨x, hx⟩
  induction x using WithTop.recTopCoe with
  | top => exact (isDist_top_iff.1 hx).false (ArrowWalk.nil ())
  | coe a =>
    obtain ⟨p, hp, -⟩ := isDist_coe_iff.1 hx
    have h := hp.walkWeight_nonneg (@Quiver.Path.start_mem_vertices Unit ⟨Loop⟩ _ _ p)
      ((ArrowWalk.nil ()).cons (x := ()) ())
    rw [walkWeight_cons, walkWeight_nil] at h
    norm_num at h

/-- With a loop of nonnegative weight, the distance from the vertex to itself is `0`. -/
example (c : ℤ) (hc : 0 ≤ c) : IsDist (fun _ _ _ ↦ c : Assignment Loop ℤ) () () 0 := by
  have h : IsShortest (fun _ _ _ ↦ c : Assignment Loop ℤ) (ArrowWalk.nil ()) :=
      isShortest_def.2 fun q ↦ by
    rw [walkWeight_nil, walkWeight_eq_sum_arrows]
    refine List.sum_nonneg fun x hx ↦ ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hc
  have hd := h.isDist
  rwa [walkWeight_nil, WithTop.coe_zero] at hd

end TauCeti.Examples.WeightedDistance
