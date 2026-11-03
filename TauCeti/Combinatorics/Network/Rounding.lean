/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Hoffman
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Rounding assignments with integer excess

On a finite arrow family, an assignment with integer excess at every vertex admits an integer
assignment with the same excess, rounding each arrow either down or up. Any integer lower and
upper bounds respected by the original assignment are preserved. The results apply to signed
assignments, circulations, and ordinary flows of integer value; loops and parallel arrows are
retained.

The proof applies Hoffman's feasibility criterion over the integers to the floor and ceiling
bounds. Casting the cut inequalities into the original coefficient ring verifies feasibility
using the original assignment.

## References

* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3 and Exercises 2.4–2.6.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {R : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)]
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

namespace Assignment

/-- An assignment with integer excess can be rounded to integer arrow values without changing
its excess, rounding each arrow between its floor and ceiling. -/
theorem exists_int_rounding (f : Assignment Q R) (b : V → ℤ)
    (hb : ∀ v, excessAt f v = (b v : R)) :
    ∃ g : Assignment Q ℤ, excessAt g = b ∧
      ∀ ⦃x y⦄ (e : Q x y), ⌊f e⌋ ≤ g e ∧ g e ≤ ⌈f e⌉ := by
  classical
  let lo : Assignment Q ℤ := f.map Int.floor
  let hi : Assignment Q ℤ := f.map Int.ceil
  have hlo : lo ≤ hi := fun _ _ e ↦ Int.floor_le_ceil (f e)
  let F : ExcessFlow (lo.map (Int.castAddHom R)) (hi.map (Int.castAddHom R))
      (fun v ↦ (b v : R)) :=
    ⟨f, ⟨fun _ _ e ↦ Int.floor_le (f e), fun _ _ e ↦ Int.le_ceil (f e)⟩, funext hb⟩
  have hbalance : ∑ v, b v = 0 := by
    have h := F.sum_eq_zero
    exact_mod_cast h
  have hcuts (S : Finset V) :
      (∑ v ∈ S, b v) + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S := by
    have h := F.sum_add_arrowSum_le S
    rw [← map_arrowSum (Int.castAddHom R), ← map_arrowSum (Int.castAddHom R)] at h
    simp only [Int.coe_castAddHom] at h
    exact_mod_cast h
  obtain ⟨g⟩ := (ExcessFlow.nonempty_iff hlo).2 ⟨hbalance, hcuts⟩
  exact ⟨g.val, g.property.2, fun _ _ e ↦ ⟨g.mem_Icc.1 _ _ e, g.mem_Icc.2 _ _ e⟩⟩

/-- Integer rounding preserves any integer arrow bounds respected by the original assignment,
as well as its prescribed integer excess and the floor/ceiling bounds on every arrow. -/
theorem exists_int_rounding_of_mem_Icc (f : Assignment Q R) {lo hi : Assignment Q ℤ}
    (hf : f ∈ Set.Icc (lo.map (Int.castAddHom R)) (hi.map (Int.castAddHom R)))
    (b : V → ℤ) (hb : ∀ v, excessAt f v = (b v : R)) :
    ∃ g : ExcessFlow lo hi b,
      ∀ ⦃x y⦄ (e : Q x y), ⌊f e⌋ ≤ g.val e ∧ g.val e ≤ ⌈f e⌉ := by
  obtain ⟨g, hg, hround⟩ := f.exists_int_rounding b hb
  refine ⟨⟨g, ⟨?_, ?_⟩, hg⟩, hround⟩
  · exact fun _ _ e ↦ (Int.le_floor.2 (hf.1 _ _ e)).trans (hround e).1
  · exact fun _ _ e ↦ (hround e).2.trans (Int.ceil_le.2 (hf.2 _ _ e))

end Assignment

/-- A signed circulation admits an integer circulation between the floor and ceiling of each
original arrow value. No sign restriction is imposed on the circulation. -/
theorem IsCirculation.exists_int_rounding {f : Assignment Q R} (hf : IsCirculation f) :
    ∃ g : Assignment Q ℤ, IsCirculation g ∧
      ∀ ⦃x y⦄ (e : Q x y), ⌊f e⌋ ≤ g e ∧ g e ≤ ⌈f e⌉ := by
  obtain ⟨g, hg, hround⟩ := f.exists_int_rounding 0 (by simpa using (isCirculation_iff f).1 hf)
  exact ⟨g, (isCirculation_iff g).2 (fun v ↦ congrFun hg v), hround⟩

namespace BoundedFlow

/-- A bounded terminal assignment with integer bounds and integer value admits an integer
assignment of the same value, with every arrow rounded between its floor and ceiling. -/
theorem exists_int_rounding {lo hi : Assignment Q ℤ} {s t : V}
    (f : BoundedFlow (lo.map (Int.castAddHom R)) (hi.map (Int.castAddHom R)) s t)
    (q : ℤ) (hq : f.val = (q : R)) :
    ∃ g : BoundedFlow lo hi s t, g.val = q ∧
      ∀ ⦃x y⦄ (e : Q x y), ⌊f.toFun e⌋ ≤ g.toFun e ∧ g.toFun e ≤ ⌈f.toFun e⌉ := by
  classical
  let b : V → ℤ := fun v ↦ if v = t then q else if v = s then -q else 0
  have hb (v : V) : excessAt f.toFun v = (b v : R) := by
    by_cases ht : v = t
    · subst v
      simpa [b] using f.val_def.symm.trans hq
    · by_cases hs : v = s
      · subst v
        simpa [b, ht] using
          f.excessAt_source.trans (congrArg Neg.neg hq)
      · simpa [b, ht, hs] using f.conserve v hs ht
  obtain ⟨g, hround⟩ := f.toFun.exists_int_rounding_of_mem_Icc f.mem_Icc b hb
  let g' : BoundedFlow lo hi s t :=
    ⟨g.val, g.mem_Icc, fun v hs ht ↦ by simp [g.excessAt_eq, b, ht, hs]⟩
  exact ⟨g', by simp [g', val_def, g.excessAt_eq, b], hround⟩

end BoundedFlow

namespace Flow

/-- An ordinary flow of integer value under integer capacities admits an integer flow of the
same value, rounding each arrow between its floor and ceiling. -/
theorem exists_int_rounding {cap : Assignment Q ℤ} {s t : V}
    (f : Flow (cap.map (Int.castAddHom R)) s t) (q : ℤ) (hq : f.val = (q : R)) :
    ∃ g : Flow cap s t, g.val = q ∧
      ∀ ⦃x y⦄ (e : Q x y), ⌊f.toFun e⌋ ≤ g.toFun e ∧ g.toFun e ≤ ⌈f.toFun e⌉ := by
  let F : BoundedFlow ((0 : Assignment Q ℤ).map (Int.castAddHom R))
      (cap.map (Int.castAddHom R)) s t :=
    ⟨f.toFun, by simpa only [Assignment.map_zero] using f.mem_Icc, f.conserve⟩
  have hF : F.val = (q : R) := F.val_def.trans (f.val_def.symm.trans hq)
  obtain ⟨g, hg, hround⟩ := F.exists_int_rounding q hF
  have hq0 : 0 ≤ q := by
    have h := f.val_nonneg
    rw [hq] at h
    exact_mod_cast h
  exact ⟨⟨g, by simpa only [← BoundedFlow.val_def, hg] using hq0⟩, hg, hround⟩

end Flow

/-! ### Fractional circulation examples -/

-- Both directions of a two-vertex cycle carry one half, and each vertex also has a
-- negative half-unit loop. Rounding preserves zero excess and the signed integer bounds.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Unit
    let f : Assignment Q ℚ := fun x y _ ↦ if x = y then -(1 / 2) else 1 / 2
    ∃ g : ExcessFlow (Q := Q) (-1) 1 0,
      ∀ ⦃x y⦄ (e : Q x y), ⌊@f x y e⌋ ≤ @g.val x y e ∧ @g.val x y e ≤ ⌈@f x y e⌉ := by
  intro Q f
  apply f.exists_int_rounding_of_mem_Icc
  · constructor <;> intro x y e <;> cases x <;> cases y <;> norm_num [f]
  · intro v
    cases v <;> norm_num [excessAt_def, f, Fintype.sum_bool]

-- A real half-unit circulation on two parallel arrows in each direction, including loops,
-- rounds each arrow to zero or one while preserving conservation.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Fin 2
    ∃ g : Assignment Q ℤ, IsCirculation g ∧
      ∀ ⦃x y⦄ (e : Q x y), 0 ≤ @g x y e ∧ @g x y e ≤ 1 := by
  intro Q
  let f : Assignment Q ℝ := fun _ _ _ ↦ 1 / 2
  have hf : IsCirculation f := by
    apply (isCirculation_iff f).2
    intro v
    simp [excessAt_def, f, Q]
  obtain ⟨g, hg, hround⟩ := hf.exists_int_rounding
  refine ⟨g, hg, fun x y e ↦ ?_⟩
  have h := hround (x := x) (y := y) e
  norm_num [f] at h
  exact h

-- Two parallel half-unit source-to-sink arrows have value one. Integer rounding keeps the
-- value and capacity constraints, so exactly one of those arrows carries the unit afterwards.
example :
    let Q : Bool → Bool → Type := fun _ _ ↦ Fin 2
    let f : Assignment Q ℚ := fun x y _ ↦ if x = false ∧ y = true then 1 / 2 else 0
    ∃ g : Flow (Q := Q) 1 false true, g.val = 1 ∧
      ∀ ⦃x y⦄ (e : Q x y),
        ⌊@f x y e⌋ ≤ @g.toFun x y e ∧ @g.toFun x y e ≤ ⌈@f x y e⌉ := by
  intro Q f
  let F : Flow ((1 : Assignment Q ℤ).map (Int.castAddHom ℚ)) false true :=
    { toFun := f
      mem_Icc := by
        constructor <;> intro x y e <;> cases x <;> cases y <;> norm_num [f]
      conserve := by
        intro v hs ht
        cases v <;> contradiction
      excessAt_sink_nonneg := by norm_num [excessAt_def, f, Q, Fintype.sum_bool] }
  apply F.exists_int_rounding 1
  norm_num [BoundedFlow.val_def, F, excessAt_def, f, Q, Fintype.sum_bool]

end TauCeti
