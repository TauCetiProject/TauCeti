/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.BasicSeq
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.FinCases

/-!
# Bounded-twist families of solutions of a commutator equation

Let `a`, `b` be elements of a group `G` and write `[x, y] = x⁻¹ y⁻¹ x y` (Mathlib's
`⁅x⁻¹, y⁻¹⁆`). The equation `[x, y] = [a, b]` over `G`
(`TauCeti.GroupAlgGeom.Quadratic.oneCommutatorEquation`) is a standard orientable quadratic
equation of genus one, and its basic sequence of automorphisms in the sense of [IFT], §7.1,
consists of the three Nielsen moves

`γ₁ : y ↦ x y`, `γ₂ : x ↦ y x`, `γ₃ : y ↦ x y`,

each of which fixes the commutator `[x, y]`. By [IFT], Lemma 41, the power `γᵢ ^ p` multiplies the
moved variable on the left by the `p`-th power of the other one. Applying the powers
`γ₁ ^ p₁, γ₂ ^ p₂, γ₃ ^ p₃, γ₁ ^ p₄, γ₂ ^ p₅, γ₃ ^ p₆` of two periods of the basic sequence to the
solution `(a, b)` therefore produces, for every tuple of exponents `p`, a solution of
`[x, y] = [a, b]`: these are the solutions `φ_{2K,p} β` of [IFT], Theorem 10, for `K = 3` and
`β = (a, b)` (`twistPoint_orientableCoeff_one_zero_ofFn`).

This file records the six moves as a finite system of equations. Starting from
`(A₀, B₀) = (a, b)`, the `i`-th move multiplies one entry of the pair `(Aᵢ₋₁, Bᵢ₋₁)` on the left
by an element `tᵢ` commuting with the other entry, the *pivot* of the move; the moves change the
entries `y, x, y, y, x, y` in this order. The *bounded-twist system* in the variables `x`, `y`
and `t₁, …, t₆` consists of the six equations saying that `tᵢ` commutes with the pivot of the
`i`-th move, and of the equations `x = A₆`, `y = B₆`. Every solution of this system solves
`[x, y] = [a, b]`, and every member of the twist family extends to a solution of the system, with
`tᵢ` the corresponding power of the pivot.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.boundedTwistStages a b t`: the seven pairs `(Aᵢ, Bᵢ)` obtained from
  `(a, b)` by the six left multiplications by `t₁, …, t₆`.
* `TauCeti.GroupAlgGeom.Lift.boundedTwistPivot a b t i`: the entry left unchanged by the `i`-th
  move.
* `TauCeti.GroupAlgGeom.Lift.boundedTwistTuple a b p`: the multipliers `tᵢ` that are the
  `pᵢ`-th powers of the pivots.
* `TauCeti.GroupAlgGeom.Lift.boundedTwistPoint a b p`: the member of the twist family with
  exponents `p`.
* `TauCeti.GroupAlgGeom.Lift.boundedTwistSystem a b`: the bounded-twist system.

## Main results

* `TauCeti.GroupAlgGeom.Lift.commutatorElement_boundedTwistStages`: multipliers commuting with
  the pivots preserve the commutator of the pair.
* `TauCeti.GroupAlgGeom.Lift.mem_V_boundedTwistSystem`: the solutions of the bounded-twist
  system.
* `TauCeti.GroupAlgGeom.Lift.comp_inl_mem_V_oneCommutatorEquation`: a solution of the
  bounded-twist system restricts to a solution of `[x, y] = [a, b]`.
* `TauCeti.GroupAlgGeom.Lift.boundedTwistPoint_mem_V`: the twist family consists of solutions
  of `[x, y] = [a, b]`.
* `TauCeti.GroupAlgGeom.Lift.twistPoint_orientableCoeff_one_zero_ofFn`,
  `TauCeti.GroupAlgGeom.Lift.twistPoint_orientable_one_ofFn`: the twist family consists of the
  points `φ_{6,p} β` of the basic sequence of `[x, y] = [a, b]`.
* `TauCeti.GroupAlgGeom.Lift.boundedTwist_family_solvable`: the bounded-twist system is solvable
  at every member of the twist family.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1 (the basic sequence of automorphisms, Lemma 41 and Notation 42) and §7.2,
  Theorem 10.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Lift

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-! ### The six twist moves in a group -/

section Stages

variable (a b : H) (t : Fin 6 → H)

/-- The seven pairs `(A₀, B₀) = (a, b)`, `(A₁, B₁)`, …, `(A₆, B₆)` obtained from `(a, b)` by six
moves, the `i`-th of which multiplies one entry of the pair on the left by `tᵢ`. The moves change
the second, first, second, second, first and second entry, in this order. -/
def boundedTwistStages : Fin 7 → H × H :=
  ![(a, b), (a, t 0 * b), (t 1 * a, t 0 * b), (t 1 * a, t 2 * (t 0 * b)),
    (t 1 * a, t 3 * (t 2 * (t 0 * b))), (t 4 * (t 1 * a), t 3 * (t 2 * (t 0 * b))),
    (t 4 * (t 1 * a), t 5 * (t 3 * (t 2 * (t 0 * b))))]

/-- The pivot of the `i`-th of the six twist moves: the entry of the pair `(Aᵢ₋₁, Bᵢ₋₁)` that the
move leaves unchanged. -/
def boundedTwistPivot (i : Fin 6) : H :=
  if i = 1 ∨ i = 4 then (boundedTwistStages a b t i.castSucc).2
  else (boundedTwistStages a b t i.castSucc).1

/-- The pivot of a twist move is the second entry of the current pair at the two moves changing
the first entry, and the first entry otherwise. -/
theorem boundedTwistPivot_def (i : Fin 6) :
    boundedTwistPivot a b t i = if i = 1 ∨ i = 4 then (boundedTwistStages a b t i.castSucc).2
      else (boundedTwistStages a b t i.castSucc).1 := (rfl)

/-- The twist moves start at the pair `(a, b)`. -/
@[simp]
theorem boundedTwistStages_zero : boundedTwistStages a b t 0 = (a, b) := (rfl)

/-- The `i`-th twist move multiplies the entry other than its pivot on the left by `tᵢ`. -/
theorem boundedTwistStages_succ (i : Fin 6) :
    boundedTwistStages a b t i.succ =
      if i = 1 ∨ i = 4 then
        (t i * (boundedTwistStages a b t i.castSucc).1, (boundedTwistStages a b t i.castSucc).2)
      else
        ((boundedTwistStages a b t i.castSucc).1,
          t i * (boundedTwistStages a b t i.castSucc).2) := by
  fin_cases i <;> rfl

/-- The pair reached after all six twist moves. -/
theorem boundedTwistStages_last :
    boundedTwistStages a b t 6 = (t 4 * (t 1 * a), t 5 * (t 3 * (t 2 * (t 0 * b)))) := (rfl)

variable {a b t}

/-- The pivot of the `i`-th twist move depends only on the multipliers of the earlier moves. -/
theorem boundedTwistPivot_congr {t' : Fin 6 → H} {i : Fin 6} (h : ∀ j < i, t j = t' j) :
    boundedTwistPivot a b t i = boundedTwistPivot a b t' i := by
  fin_cases i <;> simp [boundedTwistPivot_def, boundedTwistStages, h]

/-- A group homomorphism maps the stages of the twist moves to the stages of the images. -/
theorem map_boundedTwistStages (f : H →* K) (i : Fin 7) :
    Prod.map f f (boundedTwistStages a b t i) = boundedTwistStages (f a) (f b) (f ∘ t) i := by
  fin_cases i <;> simp [boundedTwistStages]

/-- A group homomorphism maps the pivots of the twist moves to the pivots of the images. -/
theorem map_boundedTwistPivot (f : H →* K) (i : Fin 6) :
    f (boundedTwistPivot a b t i) = boundedTwistPivot (f a) (f b) (f ∘ t) i := by
  simp only [boundedTwistPivot_def, ← map_boundedTwistStages f]
  split_ifs <;> rfl

/-- Twist moves whose multipliers commute with their pivots preserve the commutator
`[A, B] = A⁻¹ B⁻¹ A B` of the pair. -/
theorem commutatorElement_boundedTwistStages
    (h : ∀ i, Commute (t i) (boundedTwistPivot a b t i)) (i : Fin 7) :
    ⁅(boundedTwistStages a b t i).1⁻¹, (boundedTwistStages a b t i).2⁻¹⁆ = ⁅a⁻¹, b⁻¹⁆ := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hi := h i
    rw [boundedTwistPivot_def] at hi
    rw [boundedTwistStages_succ, ← ih]
    split_ifs at hi ⊢
    · simp [commutatorElement_def, mul_assoc, hi.inv_inv.left_comm]
    · simp [commutatorElement_def, mul_assoc, hi.inv_left.left_comm]

end Stages

/-! ### The twist family -/

section Family

variable (a b : H) (p : Fin 6 → ℕ)

/-- The multipliers of the six twist moves with exponents `p`: the `i`-th multiplier is the
`pᵢ`-th power of the pivot of the `i`-th move. -/
def boundedTwistTuple : Fin 6 → H :=
  let t₀ := a ^ p 0
  let t₁ := (t₀ * b) ^ p 1
  let t₂ := (t₁ * a) ^ p 2
  let t₃ := (t₁ * a) ^ p 3
  let t₄ := (t₃ * (t₂ * (t₀ * b))) ^ p 4
  let t₅ := (t₄ * (t₁ * a)) ^ p 5
  ![t₀, t₁, t₂, t₃, t₄, t₅]

/-- Each multiplier of the twist moves with exponents `p` is the corresponding power of its
pivot. -/
theorem boundedTwistTuple_apply (i : Fin 6) :
    boundedTwistTuple a b p i = boundedTwistPivot a b (boundedTwistTuple a b p) i ^ p i := by
  fin_cases i <;> rfl

/-- The multipliers of the twist moves with exponents `p` are determined by being the powers of
their pivots. -/
theorem eq_boundedTwistTuple_iff {t : Fin 6 → H} :
    t = boundedTwistTuple a b p ↔ ∀ i, t i = boundedTwistPivot a b t i ^ p i := by
  refine ⟨fun h i => h ▸ boundedTwistTuple_apply a b p i, fun h => ?_⟩
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih => rw [h i, boundedTwistTuple_apply, boundedTwistPivot_congr ih]

/-- The member of the twist family of `(a, b)` with exponents `p`: the pair reached from `(a, b)`
by the six twist moves whose multipliers are the powers of the pivots with exponents `p`. -/
def boundedTwistPoint : Fin 2 → H :=
  ![(boundedTwistStages a b (boundedTwistTuple a b p) 6).1,
    (boundedTwistStages a b (boundedTwistTuple a b p) 6).2]

/-- The first entry of a member of the twist family. -/
@[simp]
theorem boundedTwistPoint_apply_zero :
    boundedTwistPoint a b p 0 = (boundedTwistStages a b (boundedTwistTuple a b p) 6).1 := (rfl)

/-- The second entry of a member of the twist family. -/
@[simp]
theorem boundedTwistPoint_apply_one :
    boundedTwistPoint a b p 1 = (boundedTwistStages a b (boundedTwistTuple a b p) 6).2 := (rfl)

/-- With all exponents zero the multipliers of the twist moves are trivial. -/
@[simp]
theorem boundedTwistTuple_zero : boundedTwistTuple a b 0 = 1 := by
  funext i
  fin_cases i <;> simp [boundedTwistTuple]

/-- With all exponents zero the twist moves do not change the pair `(a, b)`. -/
@[simp]
theorem boundedTwistPoint_zero : boundedTwistPoint a b 0 = ![a, b] := by
  simp [boundedTwistPoint, boundedTwistStages_last]

variable {a b} in
/-- A group homomorphism maps the multipliers of the twist moves of `(a, b)` to those of the
image pair. -/
theorem map_boundedTwistTuple (f : H →* K) (i : Fin 6) :
    f (boundedTwistTuple a b p i) = boundedTwistTuple (f a) (f b) p i := by
  fin_cases i <;> simp [boundedTwistTuple]

variable {a b} in
/-- A group homomorphism maps the twist family of `(a, b)` to the twist family of the image
pair. -/
theorem map_boundedTwistPoint (f : H →* K) :
    f ∘ boundedTwistPoint a b p = boundedTwistPoint (f a) (f b) p := by
  have ht : f ∘ boundedTwistTuple a b p = boundedTwistTuple (f a) (f b) p :=
    funext (map_boundedTwistTuple p f)
  funext i
  fin_cases i <;> simp [← ht, ← map_boundedTwistStages]

/-- The multipliers of the twist family commute with their pivots. -/
theorem commute_boundedTwistTuple (i : Fin 6) :
    Commute (boundedTwistTuple a b p i) (boundedTwistPivot a b (boundedTwistTuple a b p) i) := by
  rw [boundedTwistTuple_apply]
  exact Commute.pow_self _ _

/-- The members of the twist family of `(a, b)` have the commutator of `(a, b)`. -/
theorem commutatorElement_boundedTwistPoint :
    ⁅(boundedTwistPoint a b p 0)⁻¹, (boundedTwistPoint a b p 1)⁻¹⁆ = ⁅a⁻¹, b⁻¹⁆ :=
  commutatorElement_boundedTwistStages (commute_boundedTwistTuple a b p) 6

end Family

/-! ### The twist family as the points `φ_{6,p} β` -/

section TwistPoint

open Quadratic.Standard

variable (ι : G →* H) (v : Fin 2 → H) (p : Fin 6 → ℕ)

/-- For the basic sequence `(y ↦ x y, x ↦ y x, y ↦ x y)` of a genus-one equation in the variables
`x = 0`, `y = 1` without coefficient atoms, the point `φ_{6,p} v` is the member of the twist
family of `(v x, v y)` with exponents `p`. -/
private theorem wordMap_phi_basicWordSeq_ofFn {z : Fin 0 → Fin 2}
    (inj : (Sum.elim (Sum.elim ![(0 : Fin 2)] ![1]) z).Injective) (c : Fin 0 → G) :
    wordMap ι (fun x => phi (basicWordSeq inj c) (List.ofFn p) (inr (.of x))) v =
      boundedTwistPoint (v 0) (v 1) p := by
  have hY (k : ℕ) := basicY_pow_inr_of (G := G) inj 0 k
  have hX (k : ℕ) := basicX_pow_inr_of (G := G) inj 0 k
  have hY' (k : ℕ) := basicY_pow_inr_of_of_ne (G := G) inj 0 (v := 0) (by simp) k
  have hX' (k : ℕ) := basicX_pow_inr_of_of_ne (G := G) inj 0 (v := 1) (by simp) k
  simp only [Matrix.cons_val_fin_one] at hY hX hY' hX'
  funext i
  fin_cases i <;>
    simp [basicWordSeq_def, phi_def, List.ofFn_succ, List.zipIdx, hY, hX, hY', hX',
      boundedTwistPoint, boundedTwistStages, boundedTwistTuple]

/-- For the equation `[x, y] = 1`, whose basic sequence has `K = 3` terms, the point `φ_{2K,p} v`
is the member of the twist family of `(v x, v y)` with exponents `p`. -/
theorem twistPoint_orientable_one_ofFn (inj : (Sum.elim ![(0 : Fin 2)] ![1]).Injective) :
    twistPoint ι (orientable 1 one_pos ![0] ![1] inj) (isOrientable_orientable one_pos inj) v
      (List.ofFn p) = boundedTwistPoint (v 0) (v 1) p := by
  rw [twistPoint_def, basicSeq_orientable, wordMap_phi_basicWordSeq_ofFn]

/-- For the equation `[x, y] d = 1`, whose basic sequence has `K = 3` terms, the point `φ_{2K,p} v`
is the member of the twist family of `(v x, v y)` with exponents `p`. For `d = [a, b]⁻¹` this is
the equation `[x, y] = [a, b]`, a standard equation when `a` and `b` do not commute. -/
theorem twistPoint_orientableCoeff_one_zero_ofFn {z : Fin 0 → Fin 2} {c : Fin 0 → G} {d : G}
    (inj : (Sum.elim (Sum.elim ![(0 : Fin 2)] ![1]) z).Injective) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) :
    twistPoint ι (orientableCoeff 1 0 one_pos ![0] ![1] z inj c hc d hd)
        (isOrientable_orientableCoeff one_pos inj hc hd) v (List.ofFn p) =
      boundedTwistPoint (v 0) (v 1) p := by
  rw [twistPoint_def, basicSeq_orientableCoeff_of_eq_zero _ _ _ _ rfl,
    wordMap_phi_basicWordSeq_ofFn]

end TwistPoint

/-! ### The bounded-twist system -/

section System

variable (a b : G)

/-- The bounded-twist system over `G` in the variables `x`, `y` and `t₁, …, t₆`: the multiplier
`tᵢ` of the `i`-th twist move commutes with the pivot of that move, and `(x, y)` is the pair
reached from `(a, b)` by the six moves. -/
def boundedTwistSystem : Set (GX G (Fin 2 ⊕ Fin 6)) :=
  let t : Fin 6 → GX G (Fin 2 ⊕ Fin 6) := fun i => inr (FreeGroup.of (.inr i))
  (Set.range fun i => ⁅t i, boundedTwistPivot (inl a) (inl b) t i⁆) ∪
    {inr (FreeGroup.of (.inl 0)) * (boundedTwistStages (inl a) (inl b) t 6).1⁻¹,
      inr (FreeGroup.of (.inl 1)) * (boundedTwistStages (inl a) (inl b) t 6).2⁻¹}

/-- The bounded-twist system is finite. -/
theorem finite_boundedTwistSystem : (boundedTwistSystem a b).Finite :=
  (Set.finite_range _).union (Set.toFinite _)

variable {a b} {ι : G →* H}

/-- The solutions of the bounded-twist system: the multipliers commute with the pivots of the
twist moves of `(a, b)`, and `(x, y)` is the pair reached by the six moves. -/
theorem mem_V_boundedTwistSystem {v : Fin 2 ⊕ Fin 6 → H} :
    v ∈ V ι (boundedTwistSystem a b) ↔
      (∀ i, Commute (v (.inr i)) (boundedTwistPivot (ι a) (ι b) (v ∘ .inr) i)) ∧
        (v (.inl 0), v (.inl 1)) = boundedTwistStages (ι a) (ι b) (v ∘ .inr) 6 := by
  have ht : (eval ι v ∘ fun i => inr (FreeGroup.of (Sum.inr i))) = v ∘ Sum.inr :=
    funext fun i => eval_inr_of ι v _
  have hs := map_boundedTwistStages (a := inl a) (b := inl b)
    (t := fun i => inr (FreeGroup.of (Sum.inr i))) (eval ι v) 6
  rw [ht, eval_inl, eval_inl] at hs
  simp only [boundedTwistSystem, V_union, Set.mem_inter_iff]
  refine and_congr ?_ ?_
  · simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, map_boundedTwistPivot, ht]
  · simp [mul_inv_eq_one, ← hs, Prod.ext_iff]

/-- Every solution of the bounded-twist system restricts to a solution of `[x, y] = [a, b]`. -/
theorem comp_inl_mem_V_oneCommutatorEquation {v : Fin 2 ⊕ Fin 6 → H}
    (hv : v ∈ V ι (boundedTwistSystem a b)) :
    v ∘ .inl ∈ V ι {Quadratic.oneCommutatorEquation a b} := by
  rw [mem_V_boundedTwistSystem] at hv
  rw [Quadratic.mem_V_oneCommutatorEquation]
  have h := commutatorElement_boundedTwistStages (t := v ∘ Sum.inr) hv.1 6
  rwa [← hv.2] at h

variable (ι) (p : Fin 6 → ℕ)

/-- The members of the twist family of `(a, b)` are solutions of `[x, y] = [a, b]`. -/
theorem boundedTwistPoint_mem_V :
    boundedTwistPoint (ι a) (ι b) p ∈ V ι {Quadratic.oneCommutatorEquation a b} :=
  Quadratic.mem_V_oneCommutatorEquation.2 (commutatorElement_boundedTwistPoint _ _ p)

/-- The bounded-twist system is solvable at every member of the twist family of `(a, b)`, the
multipliers being the powers of the pivots. -/
theorem boundedTwist_family_solvable :
    Sum.elim (boundedTwistPoint (ι a) (ι b) p) (boundedTwistTuple (ι a) (ι b) p) ∈
      V ι (boundedTwistSystem a b) := by
  rw [mem_V_boundedTwistSystem]
  exact ⟨fun i => by simpa using commute_boundedTwistTuple (ι a) (ι b) p i, by simp⟩

end System

end TauCeti.GroupAlgGeom.Lift
