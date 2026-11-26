/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Module.Torsion.Field

/-!
# Butcher tableaux and the stage equations of Runge–Kutta methods

A Runge–Kutta method with `s` stages for the differential equation `y' = f(t, y)` is given by its
Butcher tableau `(A, b, c)`, with `A` an `s × s` real matrix and `b`, `c` real vectors. One step
of size `h` from `(t, y)` first solves the stage equations

  `k i = f (t + c i * h) (y + h • ∑ j, A i j • k j)`, for every stage `i`,

for the stage vector `k : Fin s → E`, and then moves to `y + h • ∑ i, b i • k i`. The method is a
one-step method with increment function `(t, y, h) ↦ ∑ i, b i • k i`.

The stage equations are a fixed-point problem, which need not have a solution, nor a unique one.
The increment function is defined with the stage vector when it exists and is unique, and with
the junk value `0` otherwise. For an explicit tableau, one whose matrix `A` is strictly lower
triangular, the stage equations are solved stage by stage, so their solution always exists and
is unique, with no hypothesis on `f`.

## Main declarations

* `TauCeti.ButcherTableau s`: a Butcher tableau with `s` stages.
* `TauCeti.ButcherTableau.IsExplicit`: the matrix `A` is strictly lower triangular.
* `TauCeti.ButcherTableau.stageMap`: the map whose fixed points solve the stage equations.
* `TauCeti.ButcherTableau.IsStage`: `k` solves the stage equations.
* `TauCeti.ButcherTableau.stages`: the unique solution of the stage equations, or `0`.
* `TauCeti.ButcherTableau.increment`: the increment function `∑ i, b i • stages i`.

## Main results

* `TauCeti.ButcherTableau.existsUnique_isStage_of_isExplicit`: an explicit tableau has exactly
  one stage vector, for every field, point and step.
* `TauCeti.ButcherTableau.isStage_iff_of_isExplicit`: for an explicit tableau the stage equations
  only involve earlier stages.
* `TauCeti.ButcherTableau.stages_eq_stageMap_iterate`: for an explicit tableau with `s` stages the
  stage vector is the `s`-th iterate of `stageMap` from any starting vector.
* `TauCeti.ButcherTableau.isStage_zero_right_iff` and
  `TauCeti.ButcherTableau.increment_zero_right`: at step `0` the unique stage vector is constant,
  equal to `f t y`, and the increment is `(∑ i, b i) • f t y`.
* `TauCeti.ButcherTableau.forall_increment_zero_right_eq_iff`: the method is consistent with `f`
  exactly when `∑ i, b i = 1` or `f = 0`.
* `TauCeti.ButcherTableau.continuous_increment_of_isExplicit`: for an explicit tableau and a
  jointly continuous field the increment function is jointly continuous.

## References

* J. C. Butcher, *Runge–Kutta methods*, Scholarpedia **2**(9):3147, 2007, section
  Runge-Kutta methods.
* J. M. Sanz-Serna, *Symplectic Runge–Kutta schemes for adjoint equations, automatic
  differentiation, optimal control and more*, arXiv:1503.04021, 2015, (2.4)–(2.6).
* D. Mirzaei, *Lecture notes: numerical solution of ODEs*, arXiv:2412.19959, 2024,
  Definition 2.13.
-/

public section

open Function

namespace TauCeti

/-- A **Butcher tableau** with `s` stages: the Runge–Kutta matrix `A`, the weights `b` and the
nodes `c`. -/
@[ext]
structure ButcherTableau (s : ℕ) where
  /-- The Runge–Kutta matrix. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- The weights. -/
  b : Fin s → ℝ
  /-- The nodes. -/
  c : Fin s → ℝ

namespace ButcherTableau

variable {s : ℕ} (T : ButcherTableau s)
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A tableau is **explicit** when its matrix `A` is strictly lower triangular: `A i j = 0`
whenever `i ≤ j`. -/
def IsExplicit : Prop := ∀ i j, i ≤ j → T.A i j = 0

variable {T} in
theorem isExplicit_iff : T.IsExplicit ↔ ∀ i j, i ≤ j → T.A i j = 0 := Iff.rfl

/-- The **stage map** of the tableau for the field `f` at time `t`, point `y` and step `h`: it
sends `k` to `i ↦ f (t + c i * h) (y + h • ∑ j, A i j • k j)`. Its fixed points are the solutions
of the stage equations. -/
def stageMap (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) (k : Fin s → E) : Fin s → E :=
  fun i ↦ f (t + T.c i * h) (y + h • ∑ j, T.A i j • k j)

@[simp]
theorem stageMap_apply (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) (k : Fin s → E) (i : Fin s) :
    T.stageMap f t y h k i = f (t + T.c i * h) (y + h • ∑ j, T.A i j • k j) := (rfl)

/-- `k` is a **stage vector**: it solves the stage equations
`k i = f (t + c i * h) (y + h • ∑ j, A i j • k j)` for every stage `i`. -/
def IsStage (f : ℝ → E → E) (t : ℝ) (y : E) (h : ℝ) (k : Fin s → E) : Prop :=
  ∀ i, k i = f (t + T.c i * h) (y + h • ∑ j, T.A i j • k j)

variable {T} {f : ℝ → E → E} {t : ℝ} {y : E} {h : ℝ} {k : Fin s → E}

theorem isStage_iff :
    T.IsStage f t y h k ↔ ∀ i, k i = f (t + T.c i * h) (y + h • ∑ j, T.A i j • k j) := Iff.rfl

/-- The stage vectors are the fixed points of the stage map. -/
theorem isStage_iff_isFixedPt : T.IsStage f t y h k ↔ IsFixedPt (T.stageMap f t y h) k := by
  rw [isStage_iff, IsFixedPt, funext_iff]
  exact forall_congr' fun _ ↦ eq_comm

variable (T f t y h) in
/-- The **stage vector** of the tableau for the field `f` at time `t`, point `y` and step `h`:
the solution of the stage equations if there is exactly one, and `0` otherwise. -/
noncomputable def stages : Fin s → E := by
  classical exact if hk : ∃! k, T.IsStage f t y h k then hk.choose else 0

/-- If the stage equations have exactly one solution, `stages` is a solution. -/
theorem isStage_stages (hk : ∃! k, T.IsStage f t y h k) : T.IsStage f t y h (T.stages f t y h) := by
  rw [stages, dite_eq_left_of_eq_true (eq_true hk)]
  exact hk.choose_spec.1

/-- A stage vector is equal to `stages` as soon as it is the only stage vector. -/
theorem stages_eq_of_isStage (hk : T.IsStage f t y h k)
    (huniq : ∀ k', T.IsStage f t y h k' → k' = k) : T.stages f t y h = k :=
  huniq _ (isStage_stages ⟨k, hk, huniq⟩)

/-- If the stage equations do not have exactly one solution, `stages` takes the junk value `0`.
-/
theorem stages_of_not_existsUnique (hk : ¬∃! k, T.IsStage f t y h k) : T.stages f t y h = 0 := by
  rw [stages, dite_eq_right_of_eq_false (eq_false hk)]

variable (T f t y h) in
/-- The **increment function** `∑ i, b i • k i` of the Runge–Kutta method of the tableau, where
`k` is the stage vector `stages`. One step of the method from `(t, y)` with step `h` leads to
`y + h • T.increment f t y h`. -/
noncomputable def increment : E := ∑ i, T.b i • T.stages f t y h i

variable (T f t y h) in
theorem increment_def : T.increment f t y h = ∑ i, T.b i • T.stages f t y h i := (rfl)

/-! ### Explicit tableaux -/

/-- For an explicit tableau only the earlier stages enter row `i` of the stage equations. -/
theorem IsExplicit.sum_eq_sum_Iio (hT : T.IsExplicit) (i : Fin s) (v : Fin s → E) :
    ∑ j, T.A i j • v j = ∑ j ∈ Finset.Iio i, T.A i j • v j := by
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_).symm
  rw [hT i j (not_lt.mp (by simpa using hj)), zero_smul]

/-- For an explicit tableau the stage equations are solved stage by stage:
`k i = f (t + c i * h) (y + h • ∑ j < i, A i j • k j)`. -/
theorem isStage_iff_of_isExplicit (hT : T.IsExplicit) :
    T.IsStage f t y h k ↔
      ∀ i, k i = f (t + T.c i * h) (y + h • ∑ j ∈ Finset.Iio i, T.A i j • k j) := by
  simp only [isStage_iff, hT.sum_eq_sum_Iio]

/-- For an explicit tableau, the `m`-th iterate of the stage map from two starting vectors agrees
on the first `m` stages. -/
private theorem IsExplicit.stageMap_iterate_apply_eq (hT : T.IsExplicit) (m : ℕ)
    (k k' : Fin s → E) (j : Fin s) (hj : (j : ℕ) < m) :
    (T.stageMap f t y h)^[m] k j = (T.stageMap f t y h)^[m] k' j := by
  induction m generalizing j with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    simp only [iterate_succ_apply', stageMap_apply, hT.sum_eq_sum_Iio]
    refine congrArg (fun v ↦ f _ (y + h • v)) (Finset.sum_congr rfl fun l hl ↦ ?_)
    rw [ih l (lt_of_lt_of_le (Fin.lt_def.mp (Finset.mem_Iio.mp hl)) (Nat.lt_succ_iff.mp hj))]

/-- For an explicit tableau with `s` stages, the `s`-th iterate of the stage map does not depend
on the starting vector. -/
theorem IsExplicit.stageMap_iterate_eq (hT : T.IsExplicit) (k k' : Fin s → E) :
    (T.stageMap f t y h)^[s] k = (T.stageMap f t y h)^[s] k' :=
  funext fun j ↦ hT.stageMap_iterate_apply_eq s k k' j j.isLt

/-- For an explicit tableau with `s` stages, the `s`-th iterate of the stage map from any starting
vector solves the stage equations. -/
theorem IsExplicit.isStage_stageMap_iterate (hT : T.IsExplicit) (k₀ : Fin s → E) :
    T.IsStage f t y h ((T.stageMap f t y h)^[s] k₀) := by
  rw [isStage_iff_isFixedPt, IsFixedPt, ← iterate_succ_apply' (T.stageMap f t y h),
    iterate_succ_apply]
  exact hT.stageMap_iterate_eq _ _

/-- For an explicit tableau with `s` stages, every stage vector is the `s`-th iterate of the stage
map from any starting vector. -/
theorem IsExplicit.eq_stageMap_iterate_of_isStage (hT : T.IsExplicit) (hk : T.IsStage f t y h k)
    (k₀ : Fin s → E) : k = (T.stageMap f t y h)^[s] k₀ :=
  ((isStage_iff_isFixedPt.mp hk).iterate s).symm.trans (hT.stageMap_iterate_eq k k₀)

/-- **Explicit tableaux have unique stage vectors.** For an explicit tableau the stage equations
have exactly one solution, for every field `f`, time `t`, point `y` and step `h`. -/
theorem existsUnique_isStage_of_isExplicit (hT : T.IsExplicit) (f : ℝ → E → E) (t : ℝ) (y : E)
    (h : ℝ) : ∃! k, T.IsStage f t y h k :=
  ⟨_, hT.isStage_stageMap_iterate 0, fun _ hk ↦ hT.eq_stageMap_iterate_of_isStage hk 0⟩

/-- For an explicit tableau with `s` stages, `stages` is the `s`-th iterate of the stage map from
any starting vector. -/
theorem stages_eq_stageMap_iterate (hT : T.IsExplicit) (k₀ : Fin s → E) :
    T.stages f t y h = (T.stageMap f t y h)^[s] k₀ :=
  stages_eq_of_isStage (hT.isStage_stageMap_iterate k₀) fun _ hk ↦
    hT.eq_stageMap_iterate_of_isStage hk k₀

/-- For an explicit tableau, `stages` solves the stage equations. -/
theorem IsExplicit.isStage_stages (hT : T.IsExplicit) : T.IsStage f t y h (T.stages f t y h) :=
  ButcherTableau.isStage_stages (existsUnique_isStage_of_isExplicit hT f t y h)

/-- For an explicit tableau, the stage vector is computed stage by stage:
`stages i = f (t + c i * h) (y + h • ∑ j < i, A i j • stages j)`. -/
theorem stages_apply_of_isExplicit (hT : T.IsExplicit) (i : Fin s) :
    T.stages f t y h i =
      f (t + T.c i * h) (y + h • ∑ j ∈ Finset.Iio i, T.A i j • T.stages f t y h j) :=
  (isStage_iff_of_isExplicit hT).mp hT.isStage_stages i

/-! ### The step `0` -/

/-- At step `0` the only stage vector is the constant vector `f t y`. -/
@[simp]
theorem isStage_zero_right_iff : T.IsStage f t y 0 k ↔ k = fun _ ↦ f t y := by
  simp [isStage_iff, funext_iff]

variable (T) in
/-- At step `0` every tableau has exactly one stage vector. -/
theorem existsUnique_isStage_zero_right (f : ℝ → E → E) (t : ℝ) (y : E) :
    ∃! k, T.IsStage f t y 0 k :=
  ⟨_, isStage_zero_right_iff.mpr rfl, fun _ ↦ isStage_zero_right_iff.mp⟩

variable (T) in
/-- At step `0` every stage is `f t y`, for every tableau. -/
@[simp]
theorem stages_zero_right (f : ℝ → E → E) (t : ℝ) (y : E) :
    T.stages f t y 0 = fun _ ↦ f t y :=
  stages_eq_of_isStage (isStage_zero_right_iff.mpr rfl) fun _ ↦ isStage_zero_right_iff.mp

variable (T) in
/-- At step `0` the increment function is `(∑ i, b i) • f t y`. -/
@[simp]
theorem increment_zero_right (f : ℝ → E → E) (t : ℝ) (y : E) :
    T.increment f t y 0 = (∑ i, T.b i) • f t y := by
  simp [increment_def, Finset.sum_smul]

/-- **Consistency.** The increment function of the Runge–Kutta method agrees with `f` at step `0`
exactly when the weights sum to `1` or `f = 0`. -/
theorem forall_increment_zero_right_eq_iff :
    (∀ t y, T.increment f t y 0 = f t y) ↔ ∑ i, T.b i = 1 ∨ f = 0 := by
  simp only [increment_zero_right]
  refine ⟨fun H ↦ or_iff_not_imp_left.mpr fun hb ↦ funext₂ fun t y ↦ ?_, ?_⟩
  · have : (∑ i, T.b i - 1) • f t y = 0 := by rw [sub_smul, one_smul, H, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hb)
  · rintro (hb | rfl) t y
    · rw [hb, one_smul]
    · simp

/-! ### Continuity -/

section Continuity

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

variable (T) in
/-- If `f` is jointly continuous and `K` depends continuously on `(t, y, h)`, then so does the
image of `K` under the stage map. -/
theorem continuous_stageMap (hf : Continuous (uncurry f)) {K : ℝ × E × ℝ → Fin s → E}
    (hK : Continuous K) : Continuous fun q : ℝ × E × ℝ ↦ T.stageMap f q.1 q.2.1 q.2.2 (K q) := by
  refine continuous_pi fun i ↦ ?_
  simp only [stageMap_apply]
  refine hf.comp (f := fun q : ℝ × E × ℝ ↦ (q.1 + T.c i * q.2.2,
    q.2.1 + q.2.2 • ∑ j, T.A i j • K q j)) ?_
  fun_prop

variable (T) in
/-- For an explicit tableau and a jointly continuous field the stage vector depends continuously
on time, point and step. -/
theorem continuous_stages_of_isExplicit (hT : T.IsExplicit) (hf : Continuous (uncurry f)) :
    Continuous fun q : ℝ × E × ℝ ↦ T.stages f q.1 q.2.1 q.2.2 := by
  have key : ∀ m : ℕ, Continuous fun q : ℝ × E × ℝ ↦ (T.stageMap f q.1 q.2.1 q.2.2)^[m] 0 := by
    intro m
    induction m with
    | zero => exact continuous_const
    | succ m ih =>
      simp only [iterate_succ_apply']
      exact T.continuous_stageMap hf ih
  simpa only [stages_eq_stageMap_iterate hT 0] using key s

variable (T) in
/-- For an explicit tableau and a jointly continuous field the increment function is jointly
continuous in time, point and step. -/
theorem continuous_increment_of_isExplicit (hT : T.IsExplicit) (hf : Continuous (uncurry f)) :
    Continuous fun q : ℝ × E × ℝ ↦ T.increment f q.1 q.2.1 q.2.2 := by
  have hk := T.continuous_stages_of_isExplicit hT hf
  simp only [increment_def]
  fun_prop

end Continuity

end ButcherTableau

end TauCeti
