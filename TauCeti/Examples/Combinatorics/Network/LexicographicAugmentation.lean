/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import TauCeti.Combinatorics.Network.ShortestAugmentation
import Mathlib.Tactic.FinCases

/-!
# Full-bottleneck augmentation need not terminate

On four vertices `s = 0`, `a = 1`, `b = 2`, `t = 3`, give the four outer arrows
`s → a`, `s → b`, `a → t`, `b → t` capacity `(1, 0)` in lexicographically ordered
`ℤ × ℤ`, and give `a → b` capacity `(0, 1)`.

Alternately augment along `s → a → b → t` and `s → b → a → t`, using the reverse
residual copy of `a → b` in the latter path. Every full bottleneck is `(0, 1)`.
The flow after `n` steps has value `(0, n)`, and after `2m` steps every outer arrow
carries `(0, m)` and the middle arrow carries zero. Thus full-bottleneck augmentation
can continue forever on a finite network. Shortest augmentation instead uses the two
length-two paths and reaches value `(2, 0)`, certified by the cut `{s}`.

The example illustrates the distinction between arbitrary and shortest-path augmentation
in Ford and Fulkerson's method; see Schrijver, *Combinatorial Optimization*, Chapter 10.
-/

namespace TauCeti.Examples.LexicographicAugmentation

/-- The five arrows of the example, with no additional zero-capacity arrows. -/
inductive Hom : Fin 4 → Fin 4 → Type
  | sa : Hom 0 1
  | sb : Hom 0 2
  | at : Hom 1 3
  | bt : Hom 2 3
  | ab : Hom 1 2
  deriving DecidableEq

instance {x y} : Subsingleton (Hom x y) := ⟨by
  intro a b
  cases a <;> cases b <;> rfl⟩

noncomputable instance {x y} : Fintype (Hom x y) := Fintype.ofFinite _

private abbrev K := ℤ ×ₗ ℤ

private def big : K := toLex (1, 0)
private def small : K := toLex (0, 1)

/-- Outer capacities are `(1, 0)`; the middle capacity is `(0, 1)`. -/
def capacity : Assignment Hom K
  | _, _, .ab => small
  | _, _, .sa | _, _, .sb | _, _, .at | _, _, .bt => big

private theorem capacity_nonneg : 0 ≤ capacity := by
  intro x y e
  cases e <;> simp [capacity, big, small, ← toLex_zero, Prod.Lex.toLex_le_toLex]

private noncomputable def assignment (n : ℕ) : Assignment Hom K :=
  Assignment.single Hom.sa (toLex (0, (((n + 1) / 2 : ℕ) : ℤ))) +
  Assignment.single Hom.sb (toLex (0, ((n / 2 : ℕ) : ℤ))) +
  Assignment.single Hom.at (toLex (0, ((n / 2 : ℕ) : ℤ))) +
  Assignment.single Hom.bt (toLex (0, (((n + 1) / 2 : ℕ) : ℤ))) +
  Assignment.single Hom.ab (toLex (0, ((n % 2 : ℕ) : ℤ)))

@[simp] private theorem assignment_apply (n : ℕ) {x y : Fin 4} (e : Hom x y) :
    assignment n e = match e with
      | .sa | .bt => toLex (0, (((n + 1) / 2 : ℕ) : ℤ))
      | .sb | .at => toLex (0, ((n / 2 : ℕ) : ℤ))
      | .ab => toLex (0, ((n % 2 : ℕ) : ℤ)) := by
  cases e <;> simp [assignment, Assignment.single_apply]

@[simp] private theorem assignment_excessAt (n : ℕ) (v : Fin 4) :
    excessAt (assignment n) v =
      toLex (0, if v = 0 then -(n : ℤ) else if v = 3 then (n : ℤ) else 0) := by
  fin_cases v <;>
    simp [assignment, excessAt_add, ← toLex_add, ← toLex_sub, ← toLex_zero,
      Prod.ext_iff] <;> omega

private theorem assignment_feasible (n : ℕ) : assignment n ∈ Set.Icc 0 capacity := by
  constructor <;> intro x y e <;> cases e <;>
    simp [capacity, big, small, ← toLex_zero, Prod.Lex.toLex_le_toLex] <;> omega

/-- The assignment after `n` alternating augmentations, bundled as a feasible flow. -/
noncomputable def flow (n : ℕ) : Flow capacity 0 3 where
  toFun := assignment n
  mem_Icc := assignment_feasible n
  conserve v hv₀ hv₃ := by
    simp [hv₀, hv₃, ← toLex_zero]
  excessAt_sink_nonneg := by
    simp [← toLex_zero, Prod.Lex.toLex_le_toLex]

@[simp] private theorem flow_toFun (n : ℕ) : (flow n).toFun = assignment n := rfl

/-- The value after `n` augmentations is infinitesimal compared with `(1, 0)`. -/
theorem flow_val (n : ℕ) : (flow n).val = toLex (0, (n : ℤ)) := by
  simp [BoundedFlow.val_def]

/-- After an even number of steps all four outer arrows carry `(0, m)` and the middle is zero. -/
theorem flow_even (m : ℕ) :
    (flow (2 * m)).toFun Hom.sa = toLex (0, (m : ℤ)) ∧
    (flow (2 * m)).toFun Hom.sb = toLex (0, (m : ℤ)) ∧
    (flow (2 * m)).toFun Hom.at = toLex (0, (m : ℤ)) ∧
    (flow (2 * m)).toFun Hom.bt = toLex (0, (m : ℤ)) ∧
    (flow (2 * m)).toFun Hom.ab = 0 := by
  simp [← toLex_zero, Prod.ext_iff]
  omega

private def forwardPath : ArrowWalk (ResidualHom Hom) 0 3 :=
  (((ArrowWalk.nil (Q := ResidualHom Hom) 0).cons (Sum.inl Hom.sa)).cons
    (Sum.inl Hom.ab)).cons (Sum.inl Hom.bt)

private def backwardPath : ArrowWalk (ResidualHom Hom) 0 3 :=
  (((ArrowWalk.nil (Q := ResidualHom Hom) 0).cons (Sum.inl Hom.sb)).cons
    (Sum.inr Hom.ab)).cons (Sum.inl Hom.at)

private def alternatingPath (n : ℕ) : ArrowWalk (ResidualHom Hom) 0 3 :=
  if n % 2 = 0 then forwardPath else backwardPath

private theorem alternatingPath_isPath (n : ℕ) : (alternatingPath n).IsPath := by
  unfold alternatingPath
  split <;> simp [ArrowWalk.isPath_def, forwardPath, backwardPath, Quiver.Path.vertices_cons]

private theorem alternatingPath_ne_nil (n : ℕ) : (alternatingPath n).arrows ≠ [] :=
  (alternatingPath n).arrows_ne_nil (by decide)

private theorem alternatingPath_capacity (n : ℕ) :
    (∀ a ∈ (alternatingPath n).arrows,
      small ≤ residualCapacity 0 capacity (flow n).toFun a.2.2) ∧
    (∃ a ∈ (alternatingPath n).arrows,
      residualCapacity 0 capacity (flow n).toFun a.2.2 = small) := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;>
    simp [alternatingPath, hn, forwardPath, backwardPath,
      capacity, small, big, ← toLex_sub,
      ← toLex_zero, Prod.Lex.toLex_le_toLex]

/-- Every chosen augmenting path has full bottleneck `(0, 1)`. -/
theorem alternatingPath_bottleneck (n : ℕ) :
    (alternatingPath n).bottleneck (residualCapacity 0 capacity (flow n).toFun)
      (alternatingPath_ne_nil n) = small := by
  apply le_antisymm
  · obtain ⟨a, ha, he⟩ := (alternatingPath_capacity n).2
    exact he ▸ ArrowWalk.bottleneck_le ha
  · exact ArrowWalk.le_bottleneck_iff.2 (alternatingPath_capacity n).1

private theorem alternatingPath_update (n : ℕ) :
    residualUpdate (flow n).toFun (walkAssignment (alternatingPath n) small) =
      (flow (n + 1)).toFun := by
  funext x y e
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;> cases e <;>
    simp [residualUpdate_apply, alternatingPath, hn, forwardPath, backwardPath,
      Assignment.single_apply, small, ← toLex_add, ← toLex_sub,
      ← toLex_zero, Prod.ext_iff] <;> omega

/-- Each successor is a genuine full-bottleneck augmentation of the preceding flow. -/
theorem flow_augmentsTo (n : ℕ) : (flow n).AugmentsTo (flow (n + 1)) := by
  apply Flow.augmentsTo_iff.2
  refine ⟨alternatingPath n, (alternatingPath_isPath n).nodup_arrows,
    alternatingPath_ne_nil n, ?_, ?_⟩
  · intro a ha
    exact lt_of_lt_of_le (by decide : 0 < small) ((alternatingPath_capacity n).1 a ha)
  · apply Flow.ext
    rw [Flow.augmentBottleneck_toFun, alternatingPath_bottleneck, alternatingPath_update]

/-- The initial assignment is zero. -/
theorem flow_zero : flow 0 = Flow.zero capacity_nonneg := by
  apply Flow.ext
  funext x y e
  cases e <;> simp [← toLex_zero]

/-- There is an infinite chain of full-bottleneck augmentations starting at zero. -/
theorem not_acc_flow_zero : ¬ Acc (fun g f : Flow capacity 0 3 ↦ f.AugmentsTo g) (flow 0) :=
  not_acc_iff_exists_descending_chain.2 ⟨flow, rfl, flow_augmentsTo⟩

private def shortPath (b : Bool) : ArrowWalk (ResidualHom Hom) 0 3 :=
  if b then
    ((ArrowWalk.nil (Q := ResidualHom Hom) 0).cons (Sum.inl Hom.sb)).cons (Sum.inl Hom.bt)
  else
    ((ArrowWalk.nil (Q := ResidualHom Hom) 0).cons (Sum.inl Hom.sa)).cons (Sum.inl Hom.at)

private noncomputable def fastAssignment (i : Fin 3) : Assignment Hom K :=
  Assignment.single Hom.sa (if i = 0 then 0 else big) +
  Assignment.single Hom.at (if i = 0 then 0 else big) +
  Assignment.single Hom.sb (if i = 2 then big else 0) +
  Assignment.single Hom.bt (if i = 2 then big else 0)

@[simp] private theorem fastAssignment_apply (i : Fin 3) {x y : Fin 4} (e : Hom x y) :
    fastAssignment i e = match e with
      | .sa | .at => if i = 0 then 0 else big
      | .sb | .bt => if i = 2 then big else 0
      | .ab => 0 := by
  cases e <;> simp [fastAssignment, Assignment.single_apply]

@[simp] private theorem fastAssignment_excessAt (i : Fin 3) (v : Fin 4) :
    excessAt (fastAssignment i) v =
      if v = 0 then -((if i = 0 then 0 else big) + (if i = 2 then big else 0))
      else if v = 3 then (if i = 0 then 0 else big) + (if i = 2 then big else 0)
      else 0 := by
  fin_cases v <;> simp [fastAssignment, excessAt_add, add_comm]

/-- The three states of the two-step shortest augmentation. -/
noncomputable def fastFlow (i : Fin 3) : Flow capacity 0 3 where
  toFun := fastAssignment i
  mem_Icc := by
    constructor <;> intro x y e <;> cases e <;> fin_cases i <;>
      simp [capacity, big, small, ← toLex_zero, Prod.Lex.toLex_le_toLex]
  conserve v hv₀ hv₃ := by
    simp [hv₀, hv₃]
  excessAt_sink_nonneg := by
    fin_cases i <;> simp [big, ← toLex_add, ← toLex_zero, Prod.Lex.toLex_le_toLex]

@[simp] private theorem fastFlow_toFun (i : Fin 3) :
    (fastFlow i).toFun = fastAssignment i := rfl

private theorem shortPath_capacity (b : Bool) :
    ∀ a ∈ (shortPath b).arrows,
      residualCapacity 0 capacity (fastFlow (if b then 1 else 0)).toFun a.2.2 = big := by
  cases b <;> simp [shortPath, capacity, big, ← toLex_sub, ← toLex_zero]

private theorem shortPath_bottleneck (b : Bool) :
    (shortPath b).bottleneck
      (residualCapacity 0 capacity (fastFlow (if b then 1 else 0)).toFun)
      ((shortPath b).arrows_ne_nil (by decide)) = big :=
  ArrowWalk.bottleneck_mem (A := {big}) (shortPath_capacity b)

private theorem two_le_positiveEDist (c : Assignment (ResidualHom Hom) K) :
    2 ≤ positiveEDist c 0 3 := by
  let rank : Fin 4 → ℕ∞ := fun v ↦ if v = 0 then 0 else if v = 3 then 2 else 1
  have hr := le_positiveEDist (c := c) (s := 0) (φ := rank) (by simp [rank])
    (fun x y e _ ↦ by
      rcases e with e | e <;> cases e <;>
        simp only [rank, Fin.reduceEq, ↓reduceIte] <;> decide) 3
  simpa [rank] using hr

/-- Both steps use a shortest positive-residual path and its full bottleneck `(1, 0)`. -/
theorem fastFlow_shortestAugmentationStep (b : Bool) :
    (fastFlow (if b then 1 else 0)).toBoundedFlow.ShortestAugmentationStep
      (fastFlow (if b then 2 else 1)).toBoundedFlow := by
  apply BoundedFlow.shortestAugmentationStep_def.2
  refine ⟨shortPath b, (shortPath b).arrows_ne_nil (by decide), ?_, ?_, ?_⟩
  · intro a ha
    rw [shortPath_capacity b a ha]
    decide
  · have hlen : (shortPath b).length = 2 := by cases b <;> rfl
    rw [hlen]
    refine le_antisymm (two_le_positiveEDist _) ?_
    simpa only [hlen] using positiveEDist_le_length
      (c := residualCapacity 0 capacity (fastFlow (if b then 1 else 0)).toFun)
      (shortPath b) (fun a ha ↦ by rw [shortPath_capacity b a ha]; decide)
  · rw [shortPath_bottleneck]
    funext x y e
    cases b <;> cases e <;>
      simp [shortPath, residualUpdate_apply, Assignment.single_apply, big,
        ← toLex_add, ← toLex_sub, ← toLex_zero]

/-- Shortest augmentation starts at the same zero flow as the infinite chain. -/
theorem fastFlow_zero : fastFlow 0 = flow 0 := by
  rw [flow_zero]
  apply Flow.ext
  funext x y e
  cases e <;> simp

/-- Two shortest augmentations reach value `(2, 0)`. -/
theorem fastFlow_two_val : (fastFlow 2).val = toLex (2, 0) := by
  simp [BoundedFlow.val_def, big, ← toLex_add]

/-- After two shortest augmentations the flow value equals the capacity of the source cut `{0}`. -/
theorem fastFlow_two_val_eq_cut : (fastFlow 2).val = arrowSum capacity {0} {0}ᶜ := by
  have h := (fastFlow 2).toBoundedFlow.val_eq_cutBound_iff (S := {0}) (by simp) (by simp)
  simp only [cutBound_zero_left] at h
  apply h.2
  intro v hv w _ e
  obtain rfl : v = 0 := Finset.mem_singleton.1 hv
  rcases e with e | e <;> cases e <;>
    simp [capacity]

/-- The source cut certifies that the value `(2, 0)` reached after two steps is maximum. -/
theorem fastFlow_two_isMaximum : (fastFlow 2).IsMaximum := by
  apply ((Flow.tfae_isMaximum (by decide : (0 : Fin 4) ≠ 3) (fastFlow 2)).out 3 1).1
  exact ⟨{0}, by simp, by simp, fastFlow_two_val_eq_cut⟩

/-- The five-arrow network with outer capacities `(1, 0)` and middle capacity `(0, 1)`
admits an infinite chain from zero with simple augmenting paths of full bottleneck `(0, 1)`
and values `(0, n)`. After `2m` steps every outer arrow carries `(0, m)` and the middle
arrow is zero. Two shortest augmentations from the same zero flow instead reach a maximum
of value `(2, 0)`, certified by the source cut `{0}`. -/
public theorem exists_infinite_augmentation_and_shortest_termination :
    ∃ (Q : Fin 4 → Fin 4 → Type) (inst : ∀ x y, Fintype (Q x y)),
      letI := inst
      ∃ (sa : Q 0 1) (sb : Q 0 2) (a_t : Q 1 3) (b_t : Q 2 3) (ab : Q 1 2)
        (cap : Assignment Q (ℤ ×ₗ ℤ)) (f : ℕ → Flow cap 0 3),
        (∀ x y (e : Q x y), HEq e sa ∨ HEq e sb ∨ HEq e a_t ∨ HEq e b_t ∨ HEq e ab) ∧
        cap sa = toLex (1, 0) ∧ cap sb = toLex (1, 0) ∧
        cap a_t = toLex (1, 0) ∧ cap b_t = toLex (1, 0) ∧ cap ab = toLex (0, 1) ∧
        0 ≤ cap ∧ (f 0).toFun = 0 ∧
        (∀ n, (f n).AugmentsTo (f (n + 1)) ∧ (f n).val = toLex (0, (n : ℤ))) ∧
        (∀ m, (f (2 * m)).toFun sa = toLex (0, (m : ℤ)) ∧
          (f (2 * m)).toFun sb = toLex (0, (m : ℤ)) ∧
          (f (2 * m)).toFun a_t = toLex (0, (m : ℤ)) ∧
          (f (2 * m)).toFun b_t = toLex (0, (m : ℤ)) ∧ (f (2 * m)).toFun ab = 0) ∧
        (∀ n, ∃ p : ArrowWalk (ResidualHom Q) 0 3, p.IsPath ∧
          ∃ hn : p.arrows ≠ [],
            p.bottleneck (residualCapacity 0 cap (f n).toFun) hn = toLex (0, 1) ∧
            residualUpdate (f n).toFun (walkAssignment p (toLex (0, 1))) =
              (f (n + 1)).toFun) ∧
        ¬ Acc (fun g f : Flow cap 0 3 ↦ f.AugmentsTo g) (f 0) ∧
        ∃ g : Fin 3 → Flow cap 0 3, g 0 = f 0 ∧
          (∀ b : Bool, (g (if b then 1 else 0)).toBoundedFlow.ShortestAugmentationStep
            (g (if b then 2 else 1)).toBoundedFlow) ∧
          (g 2).val = toLex (2, 0) ∧ (g 2).IsMaximum ∧
          (g 2).val = arrowSum cap {0} {0}ᶜ := by
  refine ⟨Hom, inferInstance, Hom.sa, Hom.sb, Hom.at, Hom.bt, Hom.ab, capacity, flow,
    ?_, rfl, rfl, rfl, rfl, rfl, capacity_nonneg, ?_,
    fun n ↦ ⟨flow_augmentsTo n, flow_val n⟩, flow_even, ?_, not_acc_flow_zero,
    fastFlow, fastFlow_zero, fastFlow_shortestAugmentationStep, fastFlow_two_val,
    fastFlow_two_isMaximum, fastFlow_two_val_eq_cut⟩
  · intro x y e
    cases e <;> simp
  · simp [flow_zero]
  · intro n
    exact ⟨alternatingPath n, alternatingPath_isPath n, alternatingPath_ne_nil n,
      alternatingPath_bottleneck n, alternatingPath_update n⟩

end TauCeti.Examples.LexicographicAugmentation
