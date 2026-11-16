/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.CompositionLift
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Examples of exact composition lifts

Small real examples for `TauCeti.CompositionLift.originalSet` and
`TauCeti.CompositionLift.liftedSet`, showing which hypotheses of the exact projection theorem
`TauCeti.CompositionLift.fst_image_liftedSet` matter.

* For `g x = |x|`, `h = id` and budget zero the original set is `{0}`; no differentiability of
  `g` is involved.
* For `g x = x ^ 2` and the decreasing outer function `h y = 1 - y`, the pair `(0, 1)` lies in the
  lift although `0` is not originally feasible, so the projection identity needs `h` monotone.
* On `[-1, 1]` with `g x = x ^ 2`, `h = id` and budget one, minimising `-x` attains `-1` on both
  sets. Restricting heights to `y ≤ 1/4`, so that `g` no longer maps `D` into the height domain,
  moves the attained minimum of the lift to `-1/2`: the height domain must contain the graph.
* On the open interval `(0, 1)` with trivial constraints, the objective `x` attains no minimum on
  either set, so transferring attainment does not create it.
-/

public section

open Set

namespace TauCeti.CompositionLift

/-- With `g = |·|`, `h = id` and budget zero, only `0` is originally feasible. -/
theorem originalSet_abs_id_zero : originalSet univ (fun x : ℝ => |x|) id 0 = {0} := by
  ext x
  simp

/-- The graph point `(0, 0)` lies in the lift of `|x| ≤ 0`. -/
theorem zero_mem_liftedSet_abs_id_zero :
    ((0 : ℝ), (0 : ℝ)) ∈ liftedSet univ univ (fun x : ℝ => |x|) id 0 := by
  simp

/-- For the decreasing outer function `h y = 1 - y`, the pair `(0, 1)` lies in the lift of
`1 - x ^ 2 ≤ 0`. -/
theorem mk_zero_one_mem_liftedSet_sq_one_sub :
    ((0 : ℝ), (1 : ℝ)) ∈ liftedSet univ univ (fun x : ℝ => x ^ 2) (fun y => 1 - y) 0 := by
  norm_num

/-- For the decreasing outer function `h y = 1 - y`, the point `0` violates `1 - x ^ 2 ≤ 0`. -/
theorem zero_notMem_originalSet_sq_one_sub :
    (0 : ℝ) ∉ originalSet univ (fun x : ℝ => x ^ 2) (fun y => 1 - y) 0 := by
  norm_num

/-- Without monotonicity of the outer function the projection of the lift can be strictly larger
than the original set. -/
theorem fst_image_liftedSet_sq_one_sub_ne :
    Prod.fst '' liftedSet univ univ (fun x : ℝ => x ^ 2) (fun y => 1 - y) 0 ≠
      originalSet univ (fun x : ℝ => x ^ 2) (fun y => 1 - y) 0 := fun h =>
  zero_notMem_originalSet_sq_one_sub
    (h ▸ ⟨((0 : ℝ), (1 : ℝ)), mk_zero_one_mem_liftedSet_sq_one_sub, rfl⟩)

/-- On `[-1, 1]`, the objective `-x` attains its minimum `-1` subject to `x ^ 2 ≤ 1` at `x = 1`. -/
theorem isMinOn_neg_originalSet_Icc_sq :
    IsMinOn (fun x : ℝ => -x) (originalSet (Icc (-1) 1) (fun x : ℝ => x ^ 2) id 1) 1 :=
  isMinOn_iff.2 fun _ hx => neg_le_neg (mem_originalSet.1 hx).1.2

/-- The same minimum is attained on the lift at the graph point `(1, 1)`. -/
theorem isMinOn_neg_liftedSet_Icc_sq :
    IsMinOn ((fun x : ℝ => -x) ∘ Prod.fst)
      (liftedSet (Icc (-1) 1) univ (fun x : ℝ => x ^ 2) id 1) ((1 : ℝ), (1 : ℝ)) :=
  (isMinOn_comp_fst_liftedSet_iff (mapsTo_univ _ _) (monotone_id.monotoneOn _) _ _).2
    isMinOn_neg_originalSet_Icc_sq

/-- Restricting the heights to `y ≤ 1/4` gives a lift whose attained minimum of `-x` is `-1/2`,
at `(1/2, 1/4)`. Here `x ↦ x ^ 2` does not map `[-1, 1]` into the height domain. -/
theorem isMinOn_neg_liftedSet_Icc_sq_Iic :
    IsMinOn ((fun x : ℝ => -x) ∘ Prod.fst)
      (liftedSet (Icc (-1) 1) (Iic (1 / 4)) (fun x : ℝ => x ^ 2) id 1)
      ((1 / 2 : ℝ), (1 / 4 : ℝ)) := by
  refine isMinOn_iff.2 fun p hp => ?_
  obtain ⟨-, hy, hxy, -⟩ := mem_liftedSet.1 hp
  have : p.1 ^ 2 ≤ 1 / 4 := hxy.trans hy
  simp only [Function.comp_apply, neg_le_neg_iff]
  nlinarith [sq_nonneg (p.1 - 1 / 2)]

/-- With heights restricted to `y ≤ 1/4`, the point `1` no longer lifts. -/
theorem one_notMem_fst_image_liftedSet_Icc_sq_Iic :
    (1 : ℝ) ∉ Prod.fst '' liftedSet (Icc (-1) 1) (Iic (1 / 4)) (fun x : ℝ => x ^ 2) id 1 := by
  rintro ⟨p, hp, hp1⟩
  obtain ⟨-, hy, hxy, -⟩ := mem_liftedSet.1 hp
  have : p.1 ^ 2 ≤ 1 / 4 := hxy.trans hy
  rw [hp1] at this
  norm_num at this

/-- On the open interval `(0, 1)` with trivial constraints, the objective `x` attains no minimum
on the original set. -/
theorem not_exists_isMinOn_originalSet_Ioo :
    ¬∃ x ∈ originalSet (Ioo (0 : ℝ) 1) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0,
      IsMinOn id (originalSet (Ioo (0 : ℝ) 1) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0) x := by
  rintro ⟨x, hx, hmin⟩
  obtain ⟨⟨hx0, hx1⟩, -⟩ := mem_originalSet.1 hx
  have hx' : x / 2 ∈ originalSet (Ioo (0 : ℝ) 1) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 :=
    mem_originalSet.2 ⟨⟨by linarith, by linarith⟩, le_rfl⟩
  have := isMinOn_iff.1 hmin _ hx'
  simp only [id] at this
  linarith

/-- Hence the lift of the same problem attains no minimum either. -/
theorem not_exists_isMinOn_liftedSet_Ioo :
    ¬∃ p ∈ liftedSet (Ioo (0 : ℝ) 1) univ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0,
      IsMinOn (id ∘ Prod.fst)
        (liftedSet (Ioo (0 : ℝ) 1) univ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0) p := by
  rw [exists_isMinOn_liftedSet_iff (mapsTo_univ _ _) monotoneOn_const]
  exact not_exists_isMinOn_originalSet_Ioo

end TauCeti.CompositionLift
