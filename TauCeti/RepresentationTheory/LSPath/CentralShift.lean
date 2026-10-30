/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Reparametrization
public import TauCeti.RepresentationTheory.LSPath.RootOperator
import TauCeti.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Adding a linear path to a timed presentation

For a timed presentation `p`, `shiftTimed χ p` adds `d • χ` to each segment of duration `d`.
On its time interval this represents `t ↦ evalTimed p t + t • χ`. Durations are unchanged,
shifts compose additively, and a linear form annihilating `χ` sees exactly the same heights,
including the minimum height. In a weight space this applies to every simple coroot when `χ`
is a central weight.

This operation is on **timed presentations**, not on `PLPath` reparametrization classes.
`not_exists_shiftTimed_on_paths` gives a two-dimensional rational counterexample: two timings
of the same straight path acquire different images after adding the same linear path.
Consequently, central transport of LS paths must first select their distinguished
representatives; shifting an arbitrary representative is not well-defined.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1 (parametrized paths and their reparametrizations).
-/

public section

namespace TauCeti.PLPath

section Algebra

variable {𝕜 V : Type*} [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]

/-- Add the linear path of velocity `χ` to a timed presentation: each segment of duration `d`
is translated by `d • χ`. No centrality condition is needed to define this operation. -/
def shiftTimed (χ : V) (p : List (𝕜 × V)) : List (𝕜 × V) :=
  p.map fun x ↦ (x.1, x.2 + x.1 • χ)

@[simp]
theorem shiftTimed_nil (χ : V) : shiftTimed χ ([] : List (𝕜 × V)) = [] := (rfl)

@[simp]
theorem shiftTimed_cons (χ v : V) (d : 𝕜) (p : List (𝕜 × V)) :
    shiftTimed χ ((d, v) :: p) = (d, v + d • χ) :: shiftTimed χ p := (rfl)

@[simp]
theorem shiftTimed_append (χ : V) (p q : List (𝕜 × V)) :
    shiftTimed χ (p ++ q) = shiftTimed χ p ++ shiftTimed χ q :=
  List.map_append

@[simp]
theorem map_fst_shiftTimed (χ : V) (p : List (𝕜 × V)) :
    (shiftTimed χ p).map Prod.fst = p.map Prod.fst := by
  simp [shiftTimed, List.map_map, Function.comp_def]

@[simp]
theorem duration_shiftTimed (χ : V) (p : List (𝕜 × V)) :
    duration (shiftTimed χ p) = duration p := by
  simp [duration_def]

/-- Shifting preserves exactly the positive-duration condition. -/
@[simp]
theorem isTimed_shiftTimed_iff [LT 𝕜] (χ : V) {p : List (𝕜 × V)} :
    IsTimed (shiftTimed χ p) ↔ IsTimed p := by
  simp only [isTimed_iff, shiftTimed, List.forall_mem_map]

@[simp]
theorem shiftTimed_zero (p : List (𝕜 × V)) : shiftTimed (0 : V) p = p := by
  simp [shiftTimed]

/-- Adding two linear paths successively adds their velocities. -/
@[simp]
theorem shiftTimed_shiftTimed (χ ψ : V) (p : List (𝕜 × V)) :
    shiftTimed ψ (shiftTimed χ p) = shiftTimed (χ + ψ) p := by
  simp [shiftTimed, List.map_map, Function.comp_def, smul_add, add_assoc]

/-- The endpoint changes by the total duration times the added velocity. -/
theorem sum_map_snd_shiftTimed (χ : V) (p : List (𝕜 × V)) :
    ((shiftTimed χ p).map Prod.snd).sum = (p.map Prod.snd).sum + duration p • χ := by
  induction p with
  | nil => simp
  | cons x p ih =>
    rcases x with ⟨d, v⟩
    simp only [shiftTimed_cons, List.map_cons, List.sum_cons, ih, duration_cons, add_smul]
    ac_rfl

end Algebra

section OrderedField

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {p : List (𝕜 × V)}

/-- Evaluation of the shifted presentation, including its constant extensions outside the
presentation's time interval. -/
theorem evalTimed_shiftTimed (hp : IsTimed p) (χ : V) (t : 𝕜) :
    evalTimed (shiftTimed χ p) t =
      evalTimed p t + max 0 (min t (duration p)) • χ := by
  induction p generalizing t with
  | nil => simp
  | cons x p ih =>
    rcases x with ⟨d, v⟩
    obtain ⟨hd, hp⟩ := isTimed_cons.mp hp
    simp only [shiftTimed_cons, evalTimed_cons, ih hp, duration_cons,
      TauCeti.max_zero_min_add hd.le (duration_nonneg hp.nonneg), smul_add, smul_smul,
      div_mul_cancel₀ _ hd.ne', add_smul]
    module

/-- Within the presentation's time interval the added path is precisely `t • χ`. -/
theorem evalTimed_shiftTimed_of_mem_Icc (hp : IsTimed p) (χ : V) {t : 𝕜}
    (ht : t ∈ Set.Icc 0 (duration p)) :
    evalTimed (shiftTimed χ p) t = evalTimed p t + t • χ := by
  rw [evalTimed_shiftTimed hp, min_eq_left ht.2, max_eq_right ht.1]

omit [IsStrictOrderedRing 𝕜] in
/-- A linear form annihilating the added velocity has unchanged running height. -/
@[simp]
theorem apply_evalTimed_shiftTimed {f : Module.Dual 𝕜 V} {χ : V}
    (hχ : f χ = 0) (t : 𝕜) :
    f (evalTimed (shiftTimed χ p) t) = f (evalTimed p t) := by
  induction p generalizing t with
  | nil => simp
  | cons x p ih =>
    rcases x with ⟨d, v⟩
    simp [evalTimed_cons, map_add, hχ, ih]

/-- A linear form annihilating the added velocity has unchanged minimum height. -/
theorem minHeight_ofSegments_shiftTimed {f : Module.Dual 𝕜 V} {χ : V} (hχ : f χ = 0)
    (p : List (𝕜 × V)) :
    (ofSegments 𝕜 ((shiftTimed χ p).map Prod.snd)).minHeight f =
      (ofSegments 𝕜 (p.map Prod.snd)).minHeight f := by
  simp only [minHeight_ofSegments]
  induction p with
  | nil => rfl
  | cons x p ih =>
    rcases x with ⟨d, v⟩
    simp [listMinHeight_cons, ih, hχ]

/-- The endpoint of the shifted path is the old endpoint plus the total linear displacement. -/
theorem endpoint_ofSegments_shiftTimed (χ : V) (p : List (𝕜 × V)) :
    (ofSegments 𝕜 ((shiftTimed χ p).map Prod.snd)).endpoint =
      (ofSegments 𝕜 (p.map Prod.snd)).endpoint + duration p • χ := by
  simp only [endpoint_ofSegments, sum_map_snd_shiftTimed]

end OrderedField

/-! ### A central shift cannot be made on arbitrary reparametrization classes -/

section Counterexample

-- Coordinates are the GL₂ weight space. The simple coroot is `(x, y) ↦ x - y`, so the
-- determinant weight `(1, 1)` is central. We keep the presentations local to this calculation.
private def straightTiming : List (ℚ × (ℚ × ℚ)) := [(1, (1, 0))]

private def bentTiming : List (ℚ × (ℚ × ℚ)) :=
  [(1 / 2, (1 / 4, 0)), (1 / 2, (3 / 4, 0))]

private theorem isTimed_straightTiming : IsTimed straightTiming := by
  norm_num [straightTiming]

private theorem isTimed_bentTiming : IsTimed bentTiming := by
  norm_num [bentTiming]

private theorem same_path_timings :
    ofSegments ℚ (straightTiming.map Prod.snd) =
      ofSegments ℚ (bentTiming.map Prod.snd) := by
  simp only [straightTiming, bentTiming, List.map_cons, List.map_nil]
  have h := straight_smul_mul_straight_smul (𝕜 := ℚ)
    (show (0 : ℚ) ≤ 1 / 4 by norm_num) (show (0 : ℚ) ≤ 3 / 4 by norm_num) ((1, 0) : ℚ × ℚ)
  norm_num [smul_eq_mul, Prod.smul_mk] at h
  simpa only [ofSegments_cons, ofSegments_nil, mul_one] using h.symm

private theorem shifted_timings_ne :
    ofSegments ℚ ((shiftTimed (1, 1) straightTiming).map Prod.snd) ≠
      ofSegments ℚ ((shiftTimed (1, 1) bentTiming).map Prod.snd) := by
  intro h
  -- The first shifted path lies on x = 2y. The second has vertex (3/4, 1/2),
  -- where x - 2y = -1/4, so their minimum heights for this form differ.
  let f : Module.Dual ℚ (ℚ × ℚ) :=
    (LinearMap.fst ℚ ℚ ℚ) - (2 : ℚ) • LinearMap.snd ℚ ℚ ℚ
  have hm := congrArg (fun q : PLPath ℚ (ℚ × ℚ) ↦ q.minHeight f) h
  norm_num [straightTiming, bentTiming, minHeight_ofSegments, listMinHeight_cons,
    listMinHeight_nil, f, shiftTimed, Prod.smul_mk, smul_eq_mul] at hm

/-- There is no operation on all unparametrized rational planar paths that adds the linear
central path of velocity `(1, 1)` on every duration-one timed representative. The witnesses are
two timings of `t ↦ (t, 0)`, with the second traversing one quarter of the segment in the first
half of the time. -/
theorem not_exists_shiftTimed_on_paths :
    ¬ ∃ F : PLPath ℚ (ℚ × ℚ) → PLPath ℚ (ℚ × ℚ),
      ∀ p : List (ℚ × (ℚ × ℚ)), IsTimed p → duration p = 1 →
        F (ofSegments ℚ (p.map Prod.snd)) =
          ofSegments ℚ ((shiftTimed (1, 1) p).map Prod.snd) := by
  rintro ⟨F, hF⟩
  apply shifted_timings_ne
  rw [← hF straightTiming isTimed_straightTiming (by norm_num [straightTiming]),
    ← hF bentTiming isTimed_bentTiming (by norm_num [bentTiming]), same_path_timings]

end Counterexample

end TauCeti.PLPath
