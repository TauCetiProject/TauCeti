/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Hoffman
public import TauCeti.Combinatorics.Network.Reorient

/-!
# Bounded circulations with signed bounds

Take two vertices `false` and `true`, with one arrow for each ordered pair, including a loop at
each vertex. The arrow `false → true` has bounds `[-1, 2]`, crossing zero; the arrow
`true → false` has the two negative bounds `[-3, -1]`; and each loop has the equal negative bounds
`[-2, -2]`. These examples exercise feasibility, lower-bound subtraction, reversal, residual
capacities and shifts by a feasible reference on this one network.

* **Feasibility.** Conservation forces equal values on the two arrows between the vertices, and
  `-1` is the only value both of their bound intervals allow. So the assignment `circulation`,
  with value `-1` on both of these arrows and `-2` on both loops, is the unique feasible
  circulation (`eq_circulation`). No feasible circulation vanishes on any arrow: the flow forced
  by the bounds cannot be cancelled. Hoffman's cut inequalities hold, while raising the lower
  bound of `false → true` to `0` makes `{true}` a strict Hoffman cut.
* **Lower-bound subtraction.** The lower bounds have excess `2` at `true` and `-2` at `false`, so
  subtracting them turns the circulation problem into a prescribed-excess problem for the
  capacities `3`, `2`, `0`, `0`, with supply two at `true` and demand two at `false`. The forced
  circulation becomes two units on `true → false`.
* **Reversal.** Reversing the arrows whose upper bound is negative, namely `true → false` and both
  loops, negates their values and bounds: they become an arrow `false → true` with bounds
  `[1, 3]` and loops with bounds `[2, 2]`. The forced circulation becomes `-1`, `1`, `2`, `2`, and
  the reoriented circulation problem again has exactly one solution.
* **Residual capacities.** At the forced circulation, the forward copy of `false → true` has
  residual capacity `3`, the reverse copy of `true → false` has residual capacity `2`, and every
  other residual arrow, including the four residual copies of the loops, has capacity zero. Both
  residual arrows of positive capacity run from `false` to `true`, so the only feasible residual
  circulation is zero. Updating by two units on the forward copy of `false → true` gives a
  feasible assignment `reference` with supply two at `false` and demand two at `true`.
* **Feasible references.** Shifting by `reference` identifies its prescribed-excess problem with
  a circulation problem. The reference itself becomes the zero circulation, and the other
  solution `other`, with value `0` on `false → true` and `-2` on `true → false`, becomes the
  nonzero circulation with value `-1` on both arrows between the vertices.

Positive excess denotes demand and negative excess denotes supply throughout.
-/

public section

namespace TauCeti.Examples.SignedBounds

open Finset

/-! ## The network -/

/-- One arrow for each ordered pair of the two vertices, including a loop at each vertex. -/
abbrev Hom : Bool → Bool → Type := fun _ _ ↦ Unit

/-- Lower bounds: `-1` on `false → true`, `-3` on `true → false`, and `-2` on both loops. -/
def lower : Assignment Hom ℤ
  | false, true, _ => -1
  | true, false, _ => -3
  | false, false, _ => -2
  | true, true, _ => -2

/-- Upper bounds: `2` on `false → true`, `-1` on `true → false`, and `-2` on both loops. -/
def upper : Assignment Hom ℤ
  | false, true, _ => 2
  | true, false, _ => -1
  | false, false, _ => -2
  | true, true, _ => -2

@[simp] theorem lower_false_true (e : Hom false true) : lower e = -1 := (rfl)
@[simp] theorem lower_true_false (e : Hom true false) : lower e = -3 := (rfl)
@[simp] theorem lower_false_false (e : Hom false false) : lower e = -2 := (rfl)
@[simp] theorem lower_true_true (e : Hom true true) : lower e = -2 := (rfl)
@[simp] theorem upper_false_true (e : Hom false true) : upper e = 2 := (rfl)
@[simp] theorem upper_true_false (e : Hom true false) : upper e = -1 := (rfl)
@[simp] theorem upper_false_false (e : Hom false false) : upper e = -2 := (rfl)
@[simp] theorem upper_true_true (e : Hom true true) : upper e = -2 := (rfl)

/-- Every lower bound is at most the corresponding upper bound. -/
theorem lower_le_upper : lower ≤ upper := by
  intro x y e
  cases x <;> cases y <;> simp

/-- On this network the excess at `true` is the value on `false → true` minus the value on
`true → false`; the loop contributes to both sums and cancels. -/
private theorem excessAt_true {K : Type*} [AddCommGroup K] (f : Assignment Hom K) :
    excessAt f true = f (x := false) (y := true) () - f (x := true) (y := false) () := by
  simp only [excessAt_def, Fintype.sum_bool, Fintype.univ_punit, sum_singleton]
  abel

/-- On this network the excess at `false` is the value on `true → false` minus the value on
`false → true`. -/
private theorem excessAt_false {K : Type*} [AddCommGroup K] (f : Assignment Hom K) :
    excessAt f false = f (x := true) (y := false) () - f (x := false) (y := true) () := by
  simp only [excessAt_def, Fintype.sum_bool, Fintype.univ_punit, sum_singleton]
  abel

/-! ## The forced circulation -/

/-- The forced circulation: `-1` on both arrows between the vertices and `-2` on both loops. -/
def circulation : Assignment Hom ℤ
  | false, true, _ => -1
  | true, false, _ => -1
  | false, false, _ => -2
  | true, true, _ => -2

@[simp] theorem circulation_false_true (e : Hom false true) : circulation e = -1 := (rfl)
@[simp] theorem circulation_true_false (e : Hom true false) : circulation e = -1 := (rfl)
@[simp] theorem circulation_false_false (e : Hom false false) : circulation e = -2 := (rfl)
@[simp] theorem circulation_true_true (e : Hom true true) : circulation e = -2 := (rfl)

theorem circulation_mem_Icc : circulation ∈ Set.Icc lower upper := by
  constructor <;> intro x y e <;> cases x <;> cases y <;> simp

theorem isCirculation_circulation : IsCirculation circulation := by
  rw [isCirculation_iff]
  intro v
  cases v
  · simp [excessAt_false]
  · simp [excessAt_true]

/-- **The forced circulation is the only one.** Every feasible circulation equals
`circulation`. -/
theorem eq_circulation {f : Assignment Hom ℤ} (hf : f ∈ Set.Icc lower upper)
    (hc : IsCirculation f) : f = circulation := by
  -- Conservation at `true` forces equal values on the two arrows between the vertices; the
  -- lower bound of `false → true` and the upper bound of `true → false` then pin both to `-1`.
  have hex : f (x := false) (y := true) PUnit.unit = f (x := true) (y := false) PUnit.unit :=
    sub_eq_zero.1 (excessAt_true f ▸ (isCirculation_iff f).1 hc true)
  have hft : -1 ≤ f (x := false) (y := true) PUnit.unit := hf.1 false true PUnit.unit
  have htf : f (x := true) (y := false) PUnit.unit ≤ -1 := hf.2 true false PUnit.unit
  funext x y e
  cases e
  have hlo := hf.1 x y PUnit.unit
  have hup := hf.2 x y PUnit.unit
  cases x <;> cases y <;> simp at hlo hup ⊢ <;> omega

/-- The flow forced by the bounds cannot be cancelled: no feasible circulation vanishes on any
arrow. -/
theorem ne_zero_of_mem_Icc_of_isCirculation {f : Assignment Hom ℤ}
    (hf : f ∈ Set.Icc lower upper) (hc : IsCirculation f) {x y : Bool} (e : Hom x y) :
    f e ≠ 0 := by
  rw [eq_circulation hf hc]
  cases x <;> cases y <;> simp

/-- The forced circulation, as an assignment within the bounds with zero prescribed excess. -/
def circulationFlow : ExcessFlow lower upper 0 :=
  ⟨circulation, circulation_mem_Icc, funext ((isCirculation_iff _).1 isCirculation_circulation)⟩

@[simp]
theorem circulationFlow_val : circulationFlow.val = circulation :=
  (rfl)

/-- Every feasible assignment with zero prescribed excess is the forced circulation. -/
theorem eq_circulationFlow (f : ExcessFlow lower upper 0) : f = circulationFlow :=
  Subtype.ext (eq_circulation f.mem_Icc ((isCirculation_iff _).2 fun v ↦ f.excessAt_eq v))

instance : Subsingleton (ExcessFlow lower upper 0) :=
  ⟨fun f g ↦ (eq_circulationFlow f).trans (eq_circulationFlow g).symm⟩

-- Hoffman's cut inequalities hold, since a feasible circulation exists.
example : ∀ S : Finset Bool, arrowSum lower Sᶜ S ≤ arrowSum upper S Sᶜ :=
  (exists_isCirculation_iff lower_le_upper).1
    ⟨circulation, circulation_mem_Icc, isCirculation_circulation⟩

/-- The lower bounds with the lower bound of `false → true` raised from `-1` to `0`. -/
def raisedLower : Assignment Hom ℤ
  | false, true, _ => 0
  | true, false, _ => -3
  | false, false, _ => -2
  | true, true, _ => -2

-- Raising that lower bound to `0` makes `{true}` a strict Hoffman cut: at least `0` must enter
-- `true`, but at most `-1` can leave it.
example : ¬∃ f : Assignment Hom ℤ, f ∈ Set.Icc raisedLower upper ∧ IsCirculation f := by
  have hlo : raisedLower ≤ upper := by
    intro x y e
    cases x <;> cases y <;> simp [raisedLower]
  refine (not_exists_isCirculation_iff hlo).2 ⟨{true}, ?_⟩
  rw [show ({true} : Finset Bool)ᶜ = {false} by decide]
  simp [arrowSum_def, raisedLower]

/-! ## Lower-bound subtraction -/

/-- The lower bounds carry two units of excess into `true`. -/
@[simp]
theorem excessAt_lower_true : excessAt lower true = 2 := by
  simp [excessAt_true]

/-- The lower bounds carry two units of excess out of `false`. -/
@[simp]
theorem excessAt_lower_false : excessAt lower false = -2 := by
  simp [excessAt_false]

-- Subtracting the lower bounds produces nonzero prescribed excess, with supply two at `true` and
-- demand two at `false`, although the original problem is a circulation problem.
example : (0 : Bool → ℤ) - excessAt lower ≠ 0 := fun h ↦ by
  simpa using congrFun h true

-- After subtracting the lower bounds, the forced circulation sends two units along
-- `true → false`, which now has capacity `2`, and nothing along `false → true`, which now has
-- capacity `3`.
example :
    (ExcessFlow.shiftLowerEquiv lower upper 0 circulationFlow).val (x := true) (y := false) () =
        2 ∧
      (upper - lower) (x := true) (y := false) () = 2 ∧
      (ExcessFlow.shiftLowerEquiv lower upper 0 circulationFlow).val (x := false) (y := true) () =
        0 ∧
      (upper - lower) (x := false) (y := true) () = 3 := by
  simp

/-! ## Reversal -/

/-- Select the arrows with negative upper bound for reversal: `true → false` and both loops. -/
def reversed : ∀ ⦃x y : Bool⦄, Hom x y → Bool :=
  fun _ _ e ↦ decide (upper e < 0)

/-- Every reversed arrow has a positive lower bound after reversal, so both of its bounds are
positive. -/
theorem reorientLower_flip_pos {x y : Bool} (e : Hom x y) (h : reversed e) :
    0 < reorientLower reversed lower upper (ReorientedHom.flip reversed e h) := by
  simpa [reversed] using h

-- The reversed arrow `true → false` becomes an arrow `false → true` with bounds `[1, 3]`, and the
-- forced circulation has value `1` on it.
example :
    reorientLower reversed lower upper
        (ReorientedHom.flip reversed (x := true) (y := false) () (by decide)) = 1 ∧
      reorientUpper reversed lower upper
        (ReorientedHom.flip reversed (x := true) (y := false) () (by decide)) = 3 ∧
      (ExcessFlow.reorientEquiv reversed lower upper 0 circulationFlow).val
        (ReorientedHom.flip reversed (x := true) (y := false) () (by decide)) = 1 := by
  simp

-- The reversed loop at `false` has bounds `[2, 2]` and carries `2`, while the arrow
-- `false → true` keeps its bounds `[-1, 2]` and its value `-1`.
example :
    reorientLower reversed lower upper
        (ReorientedHom.flip reversed (x := false) (y := false) () (by decide)) = 2 ∧
      (ExcessFlow.reorientEquiv reversed lower upper 0 circulationFlow).val
        (ReorientedHom.flip reversed (x := false) (y := false) () (by decide)) = 2 ∧
      reorientLower reversed lower upper
        (ReorientedHom.keep reversed (x := false) (y := true) () (by decide)) = -1 ∧
      (ExcessFlow.reorientEquiv reversed lower upper 0 circulationFlow).val
        (ReorientedHom.keep reversed (x := false) (y := true) () (by decide)) = -1 := by
  simp

-- The reoriented circulation problem again has exactly one solution.
example :
    Nonempty
        (ExcessFlow (reorientLower reversed lower upper) (reorientUpper reversed lower upper) 0) ∧
      Subsingleton
        (ExcessFlow (reorientLower reversed lower upper) (reorientUpper reversed lower upper) 0) :=
  ⟨⟨ExcessFlow.reorientEquiv reversed lower upper 0 circulationFlow⟩,
    (ExcessFlow.reorientEquiv reversed lower upper 0).symm.subsingleton⟩

/-! ## Residual capacities -/

-- The residual capacities at the forced circulation: `3` forward along `false → true`, `2` back
-- along `true → false`, zero on the other two copies of these arrows, and zero on both residual
-- copies of each loop.
example :
    residualCapacity lower upper circulation (Sum.inl () : ResidualHom Hom false true) = 3 ∧
      residualCapacity lower upper circulation (Sum.inr () : ResidualHom Hom false true) = 2 ∧
      residualCapacity lower upper circulation (Sum.inl () : ResidualHom Hom true false) = 0 ∧
      residualCapacity lower upper circulation (Sum.inr () : ResidualHom Hom true false) = 0 ∧
      residualCapacity lower upper circulation (Sum.inl () : ResidualHom Hom false false) = 0 ∧
      residualCapacity lower upper circulation (Sum.inr () : ResidualHom Hom false false) = 0 ∧
      residualCapacity lower upper circulation (Sum.inl () : ResidualHom Hom true true) = 0 ∧
      residualCapacity lower upper circulation (Sum.inr () : ResidualHom Hom true true) = 0 := by
  simp

/-- Every residual arrow of positive capacity at the forced circulation runs from `false` to
`true`. -/
theorem eq_false_and_eq_true_of_residualCapacity_pos {v w : Bool} (a : ResidualHom Hom v w)
    (ha : 0 < residualCapacity lower upper circulation a) : v = false ∧ w = true := by
  rcases a with ⟨⟩ | ⟨⟩ <;> cases v <;> cases w <;> simp_all

/-- The only feasible residual circulation at the forced circulation is zero: no residual cycle
can adjust it. -/
theorem eq_zero_of_mem_Icc_residualCapacity {r : Assignment (ResidualHom Hom) ℤ}
    (hr : r ∈ Set.Icc 0 (residualCapacity lower upper circulation)) (hc : IsCirculation r) :
    r = 0 := by
  -- A residual arrow not from `false` to `true` has capacity at most zero, so it carries zero.
  have hzero {v w : Bool} (a : ResidualHom Hom v w) (h : ¬(v = false ∧ w = true)) : r a = 0 :=
    le_antisymm ((hr.2 v w a).trans
      (not_lt.1 (mt (eq_false_and_eq_true_of_residualCapacity_pos a) h))) (hr.1 v w a)
  -- Conservation at `true` then says the two residual arrows from `false` to `true` carry zero
  -- in total, and both carry nonnegative values.
  have hex : r (x := false) (y := true) (Sum.inl PUnit.unit) +
      r (x := false) (y := true) (Sum.inr PUnit.unit) = 0 := by
    simpa [excessAt_def, Fintype.sum_sum_type, hzero] using (isCirculation_iff r).1 hc true
  have hinl : 0 ≤ r (x := false) (y := true) (Sum.inl PUnit.unit) := hr.1 false true _
  have hinr : 0 ≤ r (x := false) (y := true) (Sum.inr PUnit.unit) := hr.1 false true _
  funext v w a
  cases v <;> cases w
  case false.true => rcases a with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp only [Pi.zero_apply] <;> omega
  all_goals exact hzero a (by simp)

/-! ## A feasible reference -/

/-- Supply two at `false` and demand two at `true`. -/
def demand : Bool → ℤ
  | false => -2
  | true => 2

@[simp] theorem demand_false : demand false = -2 := (rfl)
@[simp] theorem demand_true : demand true = 2 := (rfl)

/-- Two units on the forward residual copy of `false → true`, and zero on every other residual
arrow. -/
noncomputable def push : Assignment (ResidualHom Hom) ℤ :=
  Assignment.single (Sum.inl () : ResidualHom Hom false true) 2

@[simp]
theorem push_inl_false_true (e : Hom false true) : push (Sum.inl e : ResidualHom Hom _ _) = 2 :=
  Assignment.single_apply_self _ _

@[simp]
theorem push_inl_true_false (e : Hom true false) : push (Sum.inl e : ResidualHom Hom _ _) = 0 :=
  Assignment.single_apply_of_ne _ _ (by simp)

@[simp]
theorem push_inl_false_false (e : Hom false false) : push (Sum.inl e : ResidualHom Hom _ _) = 0 :=
  Assignment.single_apply_of_ne _ _ (by simp)

@[simp]
theorem push_inl_true_true (e : Hom true true) : push (Sum.inl e : ResidualHom Hom _ _) = 0 :=
  Assignment.single_apply_of_ne _ _ (by simp)

/-- `push` vanishes on every reverse residual arrow. -/
@[simp]
theorem push_inr {v w : Bool} (e : Hom w v) : push (Sum.inr e : ResidualHom Hom v w) = 0 :=
  Assignment.single_apply_of_ne _ _ (by simp)

theorem push_mem_Icc : push ∈ Set.Icc 0 (residualCapacity lower upper circulation) := by
  constructor <;> intro x y a <;> rcases a with ⟨⟩ | ⟨⟩ <;> cases x <;> cases y <;> simp

/-- The residual update of the forced circulation by `push`: `1` on `false → true`, `-1` on
`true → false` and `-2` on both loops. -/
noncomputable def reference : ExcessFlow lower upper demand :=
  ⟨residualUpdate circulation push, residualUpdate_mem_Icc push_mem_Icc, by
    funext v
    rw [excessAt_residualUpdate, (isCirculation_iff _).1 isCirculation_circulation v, push,
      excessAt_single]
    cases v <;> simp⟩

@[simp]
theorem reference_val : reference.val = residualUpdate circulation push :=
  (rfl)

-- The reference sends one unit along `false → true`.
example : reference.val (x := false) (y := true) () = 1 := by
  simp

/-- A second solution of the same prescribed-excess problem: `0` on `false → true`, `-2` on
`true → false` and `-2` on both loops. -/
def other : Assignment Hom ℤ
  | false, true, _ => 0
  | true, false, _ => -2
  | false, false, _ => -2
  | true, true, _ => -2

/-- The second solution, as a feasible assignment with excess `demand`. -/
def otherFlow : ExcessFlow lower upper demand :=
  ⟨other, by constructor <;> intro x y e <;> cases x <;> cases y <;> simp [other], by
    funext v
    cases v
    · simp [excessAt_false, other]
    · simp [excessAt_true, other]⟩

@[simp]
theorem otherFlow_val : otherFlow.val = other :=
  (rfl)

-- Shifting by the feasible reference turns the problem with excess `demand` into a circulation
-- problem. The reference becomes the zero circulation.
example : (ExcessFlow.circulationEquiv reference reference).val = 0 := by
  simp

-- The second solution becomes a nonzero circulation, with `-1` on both arrows between the
-- vertices and `0` on both loops.
example :
    (ExcessFlow.circulationEquiv reference otherFlow).val (x := false) (y := true) () = -1 ∧
      (ExcessFlow.circulationEquiv reference otherFlow).val (x := true) (y := false) () = -1 ∧
      (ExcessFlow.circulationEquiv reference otherFlow).val (x := false) (y := false) () = 0 ∧
      (ExcessFlow.circulationEquiv reference otherFlow).val (x := true) (y := true) () = 0 := by
  simp [other]

end TauCeti.Examples.SignedBounds
