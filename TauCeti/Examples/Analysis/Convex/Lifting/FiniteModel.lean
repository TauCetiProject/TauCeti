/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.FiniteModel.Normalization
public import TauCeti.Analysis.Convex.Lifting.FiniteModel.Separable
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Examples of finite mixed-integer models and their exact lifts

Small real examples for `TauCeti.ConvexLifting.FiniteModel`, its coordinate maps
`TauCeti.ConvexLifting.project`, `TauCeti.ConvexLifting.height` and
`TauCeti.ConvexLifting.insertHeight`, and the two exact reformulations
`TauCeti.ConvexLifting.FiniteModel.normalizedLift` and
`TauCeti.ConvexLifting.FiniteModel.separableLift`.

* Coordinates: splitting the continuous block `(3, 7)` of a point with one original and one
  appended coordinate gives the projection `(3)` and the height `(7)`, and inserting `(7)` into
  `(3)` reconstructs `(3, 7)`. The affine argument `x + z + 2` is `1` at `(x, z) = (-1, 0)`, and
  `-1` without the offset; the objective `2 x - 3 z` is `-2` there.
* The running model `mixedSquareModel`: a continuous `x ∈ [-1, 1]`, an integer `z ∈ {0, 1}`, the
  residual `(x + z) ^ 2 - 1 ≤ 0` and the objective `x + z`. The point `(0, 1/2)` lies in the
  continuous relaxation, with objective `1/2`, but is not mixed feasible.
* Normalization `mixedSquareNormalized c` replaces `x + z` by a continuous argument `u` with
  `u = x + z + c`. For `c = 0` both added affine rows vanish at `(x, z, u) = (-1, 0, -1)`. For
  `c = 2` the rows take the values `2` and `-2` at `(-1, 0, 1)`, equal to their right sides, and
  this point is feasible for `c = 2` but not for `c = -2`. The argument `u = 1/2` of the feasible
  point `(1/2, 0)` is not integral, so it must be a continuous coordinate.
* Separable lifting `mixedSquareSeparable` of the normalized model adds a height `v` with
  `u ^ 2 - 1 ≤ v ≤ 0`; the added coordinates carry zero objective coefficients. At `u = 1/2` the
  height `v = -3/4` is feasible.
* All three models attain the minimum `-1` at the lifts of `(-1, 0)`.
* A negative weight breaks separable projection: for the residual `-x` written as `-1` times the
  component `x`, the lift admits `(x, y) = (-1, 0)`, whose projection violates `-x ≤ 0`.
-/

public section

open Set

namespace TauCeti.ConvexLifting

open FiniteModel

/-! ### Coordinates, affine arguments and objectives -/

/-- With one original and one appended continuous coordinate and an empty integer block,
projecting the continuous coordinates `(3, 7)` keeps `(3)`. -/
theorem project_three_seven : project ((![3, 7], ![]) : Point (1 + 1) 0) = (![3], ![]) := by
  ext i
  · fin_cases i
    simp
  · exact i.elim0

/-- With one original and one appended continuous coordinate, the height of `(3, 7)` is `(7)`. -/
theorem height_three_seven : height ((![3, 7], ![]) : Point (1 + 1) 0) = ![7] := by
  ext j
  fin_cases j
  simp

/-- Inserting the height `(7)` into the point `(3)` with empty integer block gives `(3, 7)`. -/
theorem insertHeight_three_seven :
    insertHeight ((![3], ![]) : Point 1 0) ![7] = ((![3, 7], ![]) : Point (1 + 1) 0) := by
  rw [← insertHeight_project_height ((![3, 7], ![]) : Point (1 + 1) 0), project_three_seven,
    height_three_seven]

/-- The affine argument `x + z + 2` equals `1` at `(x, z) = (-1, 0)`. -/
theorem affineArgument_one_one_two :
    affineArgument ![1] ![1] 2 ((![-1], ![0]) : Point 1 1) = 1 := by
  norm_num [affineArgument_apply]

/-- Without the offset, the affine argument `x + z` equals `-1` at `(x, z) = (-1, 0)`. -/
theorem affineArgument_one_one_zero :
    affineArgument ![1] ![1] 0 ((![-1], ![0]) : Point 1 1) = -1 := by
  norm_num [affineArgument_apply]

namespace FiniteModel

/-- The objective with coefficients `c1 = (2)` and `c2 = (-3)` equals `-2` at `(x, z) = (-1, 0)`.
-/
theorem objective_two_neg_three {l r : ℕ} (d : FiniteModel 1 1 l r) (hc1 : d.c1 = ![2])
    (hc2 : d.c2 = ![-3]) : d.objective (![-1], ![0]) = -2 := by
  norm_num [objective_apply, hc1, hc2]

end FiniteModel

/-! ### The running mixed model -/

/-- The mixed model with a continuous coordinate `x`, an integer coordinate `z`, the affine rows
`x ≤ 1` and `-x ≤ 1`, the bounds `0 ≤ z ≤ 1`, the nonlinear residual `(x + z) ^ 2 - 1 ≤ 0` and the
objective `x + z`. -/
def mixedSquareModel : FiniteModel 1 1 1 2 where
  g _ p := (p.1 0 + p.2 0) ^ 2 - 1
  A := ![![1], ![-1]]
  B := 0
  rhs := 1
  c1 := 1
  c2 := 1
  lo := 0
  hi := 1

/-- The objective of `mixedSquareModel` is `x + z`. -/
theorem mixedSquareModel_objective (p : Point 1 1) :
    mixedSquareModel.objective p = p.1 0 + p.2 0 := by
  simp [objective_apply, mixedSquareModel]

/-- Membership in the continuous relaxation of `mixedSquareModel`. -/
theorem mem_mixedSquareModel_relaxationOn_iff (p : Point 1 1) :
    p ∈ mixedSquareModel.relaxationOn univ ↔
      (p.1 0 + p.2 0) ^ 2 ≤ 1 ∧ p.1 0 ≤ 1 ∧ -p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  simp only [mem_relaxationOn_iff, mem_univ, true_and, Fin.forall_fin_one, Fin.forall_fin_two,
    Fin.sum_univ_one, mixedSquareModel]
  norm_num [and_assoc]

/-- Membership in the mixed feasible set of `mixedSquareModel`. -/
theorem mem_mixedSquareModel_feasibleOn_iff (p : Point 1 1) :
    p ∈ mixedSquareModel.feasibleOn univ ↔
      (p.1 0 + p.2 0) ^ 2 ≤ 1 ∧ p.1 0 ≤ 1 ∧ -p.1 0 ≤ 1 ∧ (p.2 0 = 0 ∨ p.2 0 = 1) := by
  have hint : (∃ y : Fin 1 → ℤ, (∀ j, mixedSquareModel.lo j ≤ (y j : ℝ) ∧
      (y j : ℝ) ≤ mixedSquareModel.hi j) ∧ p.2 = fun j => (y j : ℝ)) ↔
      p.2 0 = 0 ∨ p.2 0 = 1 := by
    constructor
    · rintro ⟨y, hy, hp⟩
      obtain ⟨h0, h1⟩ := hy 0
      simp only [mixedSquareModel, Pi.zero_apply, Pi.one_apply] at h0 h1
      have h0' : (0 : ℤ) ≤ y 0 := by exact_mod_cast h0
      have h1' : y 0 ≤ 1 := by exact_mod_cast h1
      rw [hp]
      rcases (by omega : y 0 = 0 ∨ y 0 = 1) with h | h <;> simp [h]
    · rintro (h | h)
      · exact ⟨0, by simp [mixedSquareModel], funext fun j => by fin_cases j; simp [h]⟩
      · exact ⟨1, by simp [mixedSquareModel], funext fun j => by fin_cases j; simp [h]⟩
  rw [mem_feasibleOn_iff, hint]
  simp only [mem_univ, true_and, Fin.forall_fin_one, Fin.forall_fin_two, Fin.sum_univ_one,
    mixedSquareModel]
  norm_num [and_assoc]

/-- The point `(0, 1/2)` lies in the continuous relaxation of `mixedSquareModel`, since
`(0 + 1/2) ^ 2 = 1/4 ≤ 1` and the bounds hold. -/
theorem mem_mixedSquareModel_relaxationOn_zero_half :
    ((![0], ![1 / 2]) : Point 1 1) ∈ mixedSquareModel.relaxationOn univ := by
  rw [mem_mixedSquareModel_relaxationOn_iff]
  norm_num

/-- The point `(0, 1/2)` is not mixed feasible for `mixedSquareModel`, since `1/2` is not an
integer. -/
theorem notMem_mixedSquareModel_feasibleOn_zero_half :
    ((![0], ![1 / 2]) : Point 1 1) ∉ mixedSquareModel.feasibleOn univ := by
  rw [mem_mixedSquareModel_feasibleOn_iff]
  norm_num

/-- The relaxed objective of `mixedSquareModel` at `(0, 1/2)` is `1/2`. -/
theorem mixedSquareModel_objective_zero_half :
    mixedSquareModel.objective (![0], ![1 / 2]) = 1 / 2 := by
  norm_num [mixedSquareModel_objective]

/-- `mixedSquareModel` attains its mixed minimum `-1` at `(x, z) = (-1, 0)`. -/
theorem isMinOn_mixedSquareModel :
    ((![-1], ![0]) : Point 1 1) ∈ mixedSquareModel.feasibleOn univ ∧
      IsMinOn mixedSquareModel.objective (mixedSquareModel.feasibleOn univ) (![-1], ![0]) ∧
      mixedSquareModel.objective (![-1], ![0]) = -1 := by
  refine ⟨by rw [mem_mixedSquareModel_feasibleOn_iff]; norm_num, isMinOn_iff.2 fun p hp => ?_,
    by norm_num [mixedSquareModel_objective]⟩
  have hsq := ((mem_mixedSquareModel_feasibleOn_iff p).1 hp).1
  rw [mixedSquareModel_objective, mixedSquareModel_objective]
  norm_num
  nlinarith

/-! ### Affine-argument normalization -/

/-- The residual of `mixedSquareModel` is `(u - c) ^ 2 - 1` at the affine argument
`u = x + z + c`. -/
private theorem mixedSquareModel_g_eq (c : ℝ) (i : Fin 1) (p : Point 1 1) :
    mixedSquareModel.g i p = ∑ j, (1 : Fin 1 → Fin 1 → ℝ) i j *
      (fun _ u => (u - c) ^ 2 - 1 : Fin 1 → ℝ → ℝ) j
        (affineArgument ((1 : Fin 1 → Fin 1 → ℝ) j) ((1 : Fin 1 → Fin 1 → ℝ) j) c p) := by
  simp [mixedSquareModel, affineArgument_apply]

/-- The normalization of `mixedSquareModel` by a continuous argument `u = x + z + c`, with the
residual rewritten as `(u - c) ^ 2 - 1`. -/
def mixedSquareNormalized (c : ℝ) : FiniteModel (1 + 1) 1 1 (2 + (1 + 1)) :=
  mixedSquareModel.normalizedLift 1 1 (fun _ => c) (fun _ u => (u - c) ^ 2 - 1) 1

/-- A point is feasible for `mixedSquareNormalized c` exactly when its projection is feasible for
`mixedSquareModel` and its argument coordinate is `x + z + c`. -/
theorem mem_mixedSquareNormalized_feasibleOn_iff (c : ℝ) (z : Point (1 + 1) 1) :
    z ∈ (mixedSquareNormalized c).feasibleOn univ ↔
      project z ∈ mixedSquareModel.feasibleOn univ ∧
        height z 0 = (project z).1 0 + (project z).2 0 + c := by
  have h := mem_normalizedLift_feasibleOn_iff mixedSquareModel univ 1 1 (fun _ => c)
    (fun _ u => (u - c) ^ 2 - 1) 1 (mixedSquareModel_g_eq c) z
  rw [preimage_univ, Fin.forall_fin_one, affineArgument_apply] at h
  rw [mixedSquareNormalized, h]
  simp

/-- At `(x, z, u) = (-1, 0, -1)` the added row `-x - z + u` of `mixedSquareNormalized 0`
vanishes. -/
theorem mixedSquareNormalized_row_upper :
    (∑ i, (mixedSquareNormalized 0).A (((0 : Fin 1).castAdd 1).natAdd 2) i *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![-1]).1 i) +
      ∑ s, (mixedSquareNormalized 0).B (((0 : Fin 1).castAdd 1).natAdd 2) s *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![-1]).2 s = 0 := by
  rw [mixedSquareNormalized, normalizedLift_row_upper]
  -- `height_apply` would expose the index `Fin.natAdd 1 0`, which `simp` evaluates to the literal
  -- `1` before `insertHeight_fst_natAdd` applies; `height_insertHeight` evaluates it directly.
  simp [-height_apply]

/-- At `(x, z, u) = (-1, 0, -1)` the added row `x + z - u` of `mixedSquareNormalized 0`
vanishes. -/
theorem mixedSquareNormalized_row_lower :
    (∑ i, (mixedSquareNormalized 0).A (((0 : Fin 1).addNat 1).natAdd 2) i *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![-1]).1 i) +
      ∑ s, (mixedSquareNormalized 0).B (((0 : Fin 1).addNat 1).natAdd 2) s *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![-1]).2 s = 0 := by
  rw [mixedSquareNormalized, normalizedLift_row_lower]
  simp [-height_apply]

/-- At `(x, z, u) = (-1, 0, -1)` the residual `u ^ 2 - 1` of `mixedSquareNormalized 0` vanishes.
-/
theorem mixedSquareNormalized_g :
    (mixedSquareNormalized 0).g 0 (insertHeight ((![-1], ![0]) : Point 1 1) ![-1]) = 0 := by
  rw [mixedSquareNormalized, normalizedLift_g]
  norm_num [-height_apply]

/-- The objective of `mixedSquareNormalized c` is `x + z`, ignoring the argument coordinate. -/
theorem mixedSquareNormalized_objective (c : ℝ) (z : Point (1 + 1) 1) :
    (mixedSquareNormalized c).objective z = (project z).1 0 + (project z).2 0 := by
  rw [mixedSquareNormalized, normalizedLift_objective, Function.comp_apply,
    mixedSquareModel_objective]

/-- With offset `2` the added rows `-x - z + u` and `x + z - u` take the values `2` and `-2` at
`(x, z, u) = (-1, 0, 1)`, equal to their right sides. -/
theorem mixedSquareNormalized_two_rows :
    (∑ i, (mixedSquareNormalized 2).A (((0 : Fin 1).castAdd 1).natAdd 2) i *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![1]).1 i) +
      ∑ s, (mixedSquareNormalized 2).B (((0 : Fin 1).castAdd 1).natAdd 2) s *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![1]).2 s = 2 ∧
    (mixedSquareNormalized 2).rhs (((0 : Fin 1).castAdd 1).natAdd 2) = 2 ∧
    (∑ i, (mixedSquareNormalized 2).A (((0 : Fin 1).addNat 1).natAdd 2) i *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![1]).1 i) +
      ∑ s, (mixedSquareNormalized 2).B (((0 : Fin 1).addNat 1).natAdd 2) s *
        (insertHeight ((![-1], ![0]) : Point 1 1) ![1]).2 s = -2 ∧
    (mixedSquareNormalized 2).rhs (((0 : Fin 1).addNat 1).natAdd 2) = -2 := by
  rw [mixedSquareNormalized, normalizedLift_row_upper, normalizedLift_rhs_upper,
    normalizedLift_row_lower, normalizedLift_rhs_lower]
  norm_num [-height_apply]

/-- With offset `2` the point `(x, z, u) = (-1, 0, 1)` is feasible: `u = x + z + 2`. -/
theorem mem_mixedSquareNormalized_two_feasibleOn :
    insertHeight ((![-1], ![0]) : Point 1 1) ![1] ∈ (mixedSquareNormalized 2).feasibleOn univ := by
  rw [mem_mixedSquareNormalized_feasibleOn_iff, project_insertHeight,
    mem_mixedSquareModel_feasibleOn_iff]
  norm_num [-height_apply]

/-- With offset `-2` the point `(x, z, u) = (-1, 0, 1)` is infeasible, so the sign of the offset
matters. -/
theorem notMem_mixedSquareNormalized_neg_two_feasibleOn :
    insertHeight ((![-1], ![0]) : Point 1 1) ![1] ∉
      (mixedSquareNormalized (-2)).feasibleOn univ := by
  rw [mem_mixedSquareNormalized_feasibleOn_iff]
  norm_num [-height_apply]

/-- The mixed feasible point `(x, z) = (1/2, 0)` lifts with the non-integral argument
`u = 1/2`, which is therefore a continuous coordinate. -/
theorem mem_mixedSquareNormalized_feasibleOn_half :
    insertHeight ((![1 / 2], ![0]) : Point 1 1) ![1 / 2] ∈
      (mixedSquareNormalized 0).feasibleOn univ := by
  rw [mem_mixedSquareNormalized_feasibleOn_iff, project_insertHeight,
    mem_mixedSquareModel_feasibleOn_iff]
  norm_num [-height_apply]

/-- `mixedSquareNormalized 0` attains its mixed minimum `-1` at `(x, z, u) = (-1, 0, -1)`, the
lift of the minimiser of `mixedSquareModel`. -/
theorem isMinOn_mixedSquareNormalized :
    insertHeight ((![-1], ![0]) : Point 1 1) ![-1] ∈ (mixedSquareNormalized 0).feasibleOn univ ∧
      IsMinOn (mixedSquareNormalized 0).objective ((mixedSquareNormalized 0).feasibleOn univ)
        (insertHeight (![-1], ![0]) ![-1]) ∧
      (mixedSquareNormalized 0).objective (insertHeight (![-1], ![0]) ![-1]) = -1 := by
  obtain ⟨hp, hmin, -⟩ := isMinOn_mixedSquareModel
  have hz : insertHeight ((![-1], ![0]) : Point 1 1) ![-1] ∈
      (mixedSquareNormalized 0).feasibleOn univ := by
    rw [mem_mixedSquareNormalized_feasibleOn_iff, project_insertHeight]
    norm_num [hp, -height_apply]
  have key := (normalization_minimum_iff mixedSquareModel univ 1 1 (fun _ => 0)
    (fun _ u => (u - 0) ^ 2 - 1) 1 (mixedSquareModel_g_eq 0)
    (insertHeight (![-1], ![0]) ![-1])).2
  rw [preimage_univ, project_insertHeight] at key
  refine ⟨hz, (key ⟨hz, hp, hmin⟩).2, ?_⟩
  rw [mixedSquareNormalized_objective, project_insertHeight]
  norm_num

/-! ### Separable-height lifting -/

/-- The residual of `mixedSquareNormalized 0` is the single component `u ^ 2 - 1` with weight
one. -/
private theorem mixedSquareNormalized_g_eq (i : Fin 1) (z : Point (1 + 1) 1) :
    (mixedSquareNormalized 0).g i z = ∑ j, (1 : Fin 1 → Fin 1 → ℝ) i j *
      (fun _ z => height z 0 ^ 2 - 1 : Fin 1 → Point (1 + 1) 1 → ℝ) j z := by
  rw [mixedSquareNormalized, normalizedLift_g]
  simp

/-- The separable-height lift of `mixedSquareNormalized 0`, adding a continuous height `v` with
`u ^ 2 - 1 ≤ v` and the budget row `v ≤ 0`. -/
def mixedSquareSeparable : FiniteModel (1 + 1 + 1) 1 1 (2 + (1 + 1) + 1) :=
  (mixedSquareNormalized 0).separableLift (fun _ z => height z 0 ^ 2 - 1) 1

/-- Inserting the component value `v = u ^ 2 - 1` lifts a feasible point of
`mixedSquareNormalized 0` to `mixedSquareSeparable`. -/
theorem insertHeight_mem_mixedSquareSeparable_feasibleOn {z : Point (1 + 1) 1}
    (hz : z ∈ (mixedSquareNormalized 0).feasibleOn univ) {v : ℝ} (hv : v = height z 0 ^ 2 - 1) :
    insertHeight z ![v] ∈ mixedSquareSeparable.feasibleOn univ := by
  have key := insertHeight_component_mem_separableLift_feasibleOn (mixedSquareNormalized 0) univ
    (fun _ z => height z 0 ^ 2 - 1) 1 mixedSquareNormalized_g_eq hz
  have hv' : ![v] = fun _ => height z 0 ^ 2 - 1 := funext fun j => by fin_cases j; simp [hv]
  rw [preimage_univ, ← hv'] at key
  exact key

/-- The objective of `mixedSquareSeparable` is `x + z`: the added argument and height
coordinates have zero objective coefficients. -/
theorem mixedSquareSeparable_objective (w : Point (1 + 1 + 1) 1) :
    mixedSquareSeparable.objective w = mixedSquareModel.objective (project (project w)) := by
  rw [mixedSquareSeparable, separableLift_objective, Function.comp_apply,
    mixedSquareNormalized_objective, mixedSquareModel_objective]

/-- At `(x, z, u) = (1/2, 0, 1/2)` the component residual is `u ^ 2 - 1 = -3/4`, and the stored
height `v = -3/4` is feasible for `mixedSquareSeparable`: it satisfies the budget `v ≤ 0`. -/
theorem mem_mixedSquareSeparable_feasibleOn_half :
    insertHeight (insertHeight ((![1 / 2], ![0]) : Point 1 1) ![1 / 2]) ![-3 / 4] ∈
      mixedSquareSeparable.feasibleOn univ :=
  insertHeight_mem_mixedSquareSeparable_feasibleOn mem_mixedSquareNormalized_feasibleOn_half
    (by norm_num [-height_apply])

/-- `mixedSquareSeparable` attains its mixed minimum `-1` at `(x, z, u, v) = (-1, 0, -1, 0)`, the
lift of the minimiser of `mixedSquareModel`. -/
theorem isMinOn_mixedSquareSeparable :
    insertHeight (insertHeight ((![-1], ![0]) : Point 1 1) ![-1]) ![0] ∈
        mixedSquareSeparable.feasibleOn univ ∧
      IsMinOn mixedSquareSeparable.objective (mixedSquareSeparable.feasibleOn univ)
        (insertHeight (insertHeight (![-1], ![0]) ![-1]) ![0]) ∧
      mixedSquareSeparable.objective (insertHeight (insertHeight (![-1], ![0]) ![-1]) ![0]) =
        -1 := by
  obtain ⟨hz, hmin, hval⟩ := isMinOn_mixedSquareNormalized
  have hw := insertHeight_mem_mixedSquareSeparable_feasibleOn hz (v := 0)
    (by norm_num [-height_apply])
  have key := (separable_minimum_iff (mixedSquareNormalized 0) univ
    (fun _ z => height z 0 ^ 2 - 1) 1 (fun _ _ => zero_le_one) mixedSquareNormalized_g_eq
    (insertHeight (insertHeight (![-1], ![0]) ![-1]) ![0])).2
  rw [preimage_univ, project_insertHeight] at key
  refine ⟨hw, (key ⟨hw, hz, hmin⟩).2, ?_⟩
  rw [mixedSquareSeparable, separableLift_objective, Function.comp_apply, project_insertHeight,
    hval]

/-! ### Negative weights -/

/-- A model with one continuous coordinate `x`, no integer coordinates, no affine rows and the
residual `-x ≤ 0`, which is `-1` times the component `x`. -/
def negativeWeightModel : FiniteModel 1 0 1 0 where
  g _ p := -p.1 0
  A := 0
  B := 0
  rhs := 0
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

/-- The residual of `negativeWeightModel` decomposes as `-1` times the component `x`. -/
theorem negativeWeightModel_g_eq (i : Fin 1) (p : Point 1 0) :
    negativeWeightModel.g i p = ∑ j, (-1 : Fin 1 → Fin 1 → ℝ) i j *
      (fun _ p => p.1 0 : Fin 1 → Point 1 0 → ℝ) j p := by
  simp [negativeWeightModel]

/-- With the negative weight `-1`, the separable lift of `negativeWeightModel` admits
`(x, y) = (-1, 0)`: it satisfies `x ≤ y` and `-y ≤ 0`. -/
theorem mem_negativeWeightModel_separableLift_feasibleOn :
    insertHeight ((![-1], ![]) : Point 1 0) ![0] ∈
      (negativeWeightModel.separableLift (fun (_ : Fin 1) p => p.1 0) (-1)).feasibleOn univ := by
  rw [mem_feasibleOn_iff, separableLift_nonlinear_rows_iff, separableLift_affine_rows_iff]
  simp [negativeWeightModel, -height_apply, funext_iff]

/-- The point `x = -1` violates the residual `-x ≤ 0` of `negativeWeightModel`. -/
theorem notMem_negativeWeightModel_feasibleOn :
    ((![-1], ![]) : Point 1 0) ∉ negativeWeightModel.feasibleOn univ := by
  simp [negativeWeightModel]

/-- With a negative weight, separable lifting is not exact: the nonnegativity hypothesis of
`TauCeti.ConvexLifting.FiniteModel.separable_projection` cannot be dropped, although
`negativeWeightModel` satisfies its decomposition hypothesis. -/
theorem image_project_negativeWeightModel_separableLift_ne :
    project '' (negativeWeightModel.separableLift (fun (_ : Fin 1) p => p.1 0) (-1)).feasibleOn
        (project ⁻¹' univ) ≠ negativeWeightModel.feasibleOn univ := by
  rw [preimage_univ]
  intro h
  have hmem := mem_negativeWeightModel_separableLift_feasibleOn
  exact notMem_negativeWeightModel_feasibleOn (h ▸ ⟨_, hmem, project_insertHeight _ _⟩)

end TauCeti.ConvexLifting
