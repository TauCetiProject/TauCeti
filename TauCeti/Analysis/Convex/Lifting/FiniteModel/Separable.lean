/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.Basic
public import TauCeti.Analysis.Convex.Lifting.FiniteModel.Basic
import TauCeti.Order.Filter.Extr

/-!
# Separable-height lifting of finite mixed-integer models

When the nonlinear residuals of a `FiniteModel` decompose as nonnegatively weighted sums of
component functions,

    d.g i x = ∑ j, weight i j * component j x,    0 ≤ weight i j,

introducing one free continuous height coordinate `y_j` per component with nonlinear constraints
`component j (project z) - height z j ≤ 0` and added affine budget rows
`∑ j, weight i j * height z j ≤ 0` yields `FiniteModel.separableLift`. The original affine rows,
integer-block bounds, and linear objective are retained, with zero objective coefficients on the
appended height coordinates.

Under `pointEquiv n m q : Point (n + q) m ≃ Point n m × (Fin q → ℝ)`, the lifted mixed-integer and
relaxed feasible sets are preimages of `liftedSet` with inner map `fun x j => component j x`,
outer map `fun y i => ∑ j, weight i j * y j` (coordinatewise-monotone when `0 ≤ weight i j`), and
budget `0 : Fin l → ℝ` (`FiniteModel.separableLift_feasibleWith_eq_preimage_liftedSet`,
`FiniteModel.feasibleWith_eq_originalSet`). This directly instantiates `projection_eq` to yield
exact projection (`FiniteModel.separable_projection`,
`FiniteModel.separable_relaxation_projection`), from which feasible-minimum equivalence
(`FiniteModel.separable_minimum_iff`, `FiniteModel.separable_relaxation_minimum_iff`) and
attainment equivalence (`FiniteModel.separable_attainment_iff`,
`FiniteModel.separable_relaxation_attainment_iff`) follow immediately.

## Main definitions

* `TauCeti.ConvexLifting.FiniteModel.separableLift` — the finite model with `q` appended free
  continuous height variables, `q` component-epigraph residuals, and `r + l` affine rows.

## Main statements

* `TauCeti.ConvexLifting.FiniteModel.separableLift_affine_rows_iff` — equivalence of the lifted
  affine rows with the original affine rows plus the weighted height budget rows.
* `TauCeti.ConvexLifting.FiniteModel.feasibleWith_eq_originalSet` and
  `TauCeti.ConvexLifting.FiniteModel.separableLift_feasibleWith_eq_preimage_liftedSet` —
  identification of `d.feasibleWith D P` with `originalSet` and of
  `(d.separableLift component weight).feasibleWith (project ⁻¹' D) P` with the `pointEquiv`
  preimage of `liftedSet`.
* `TauCeti.ConvexLifting.FiniteModel.separable_projection` and
  `TauCeti.ConvexLifting.FiniteModel.separable_relaxation_projection` — exact projection for
  mixed-integer feasibility and the continuous relaxation under nonnegative weights.
* `TauCeti.ConvexLifting.FiniteModel.separable_minimum_iff` and
  `TauCeti.ConvexLifting.FiniteModel.separable_attainment_iff` — transfer of feasible minima and
  attainment for the mixed-integer problem, together with their continuous-relaxation
  counterparts.

## References

* H. Hijazi, P. Bonami and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (4 October 2013),
  §3.1, p. 4 (generalized algebraically from unweighted sums to nonnegative weights).
-/

public section

open Set

namespace TauCeti.ConvexLifting.FiniteModel

variable {n m l r q : ℕ}

/-- Lift a `FiniteModel` by appending `q` free continuous height coordinates `y_j` with component
epigraph residuals `component j (project z) - y_j ≤ 0` and weighted affine budget rows
`∑ j, weight i j * y_j ≤ 0`. The original nonlinear residuals `d.g` are not carried over; they are
discarded and replaced by the `q` component-epigraph residuals, so the lifted model matches `d`
only when `d.g` satisfies the assumed separable decomposition `hg` (with nonnegative weights `hw`).
Original affine rows, integer-block bounds, and the linear objective are retained, with zero
objective coefficients on the appended height coordinates. -/
def separableLift (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    FiniteModel (n + q) m q (r + l) where
  g := fun j z => component j (project z) - height z j
  A := Fin.append (fun i => Fin.append (d.A i) 0) (fun i => Fin.append 0 (weight i))
  B := Fin.append d.B 0
  rhs := Fin.append d.rhs 0
  c1 := Fin.append d.c1 0
  c2 := d.c2
  lo := d.lo
  hi := d.hi

/-- Continuous-block objective coefficients of `separableLift`. -/
@[simp]
theorem separableLift_c1 (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).c1 = Fin.append d.c1 0 := (rfl)

/-- Integer-block objective coefficients of `separableLift`. -/
@[simp]
theorem separableLift_c2 (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).c2 = d.c2 := (rfl)

/-- The objective of `separableLift` is the pullback of `d.objective` along `project`. -/
@[simp]
theorem separableLift_objective (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).objective = d.objective ∘ project :=
  objective_eq_comp_project (separableLift_c1 d component weight)
    (separableLift_c2 d component weight)

/-- Nonlinear residual evaluation of `separableLift`. -/
@[simp]
theorem separableLift_g (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (j : Fin q)
    (z : Point (n + q) m) :
    (d.separableLift component weight).g j z = component j (project z) - height z j := (rfl)

/-- Lower bounds on the integer block are unchanged by `separableLift`. -/
@[simp]
theorem separableLift_lo (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).lo = d.lo := (rfl)

/-- Upper bounds on the integer block are unchanged by `separableLift`. -/
@[simp]
theorem separableLift_hi (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).hi = d.hi := (rfl)

/-- Right-hand side of a retained original affine row in `separableLift`. -/
@[simp]
theorem separableLift_rhs_orig (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (k : Fin r) :
    (d.separableLift component weight).rhs (k.castAdd l) = d.rhs k := by
  simp [separableLift]

/-- Right-hand side of an added weighted budget row in `separableLift`. -/
@[simp]
theorem separableLift_rhs_budget (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (i : Fin l) :
    (d.separableLift component weight).rhs (i.natAdd r) = 0 := by
  simp [separableLift]

/-- Evaluation of a retained original affine row in `separableLift`. -/
theorem separableLift_row_orig (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (k : Fin r)
    (z : Point (n + q) m) :
    (∑ i, (d.separableLift component weight).A (k.castAdd l) i * z.1 i) +
        (∑ s, (d.separableLift component weight).B (k.castAdd l) s * z.2 s) =
      (∑ i, d.A k i * (project z).1 i) + ∑ s, d.B k s * (project z).2 s := by
  simp [separableLift, sum_append_zero_right_mul_fst]

/-- Evaluation of an added weighted height budget row in `separableLift`. -/
theorem separableLift_row_budget (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (i : Fin l)
    (z : Point (n + q) m) :
    (∑ a, (d.separableLift component weight).A (i.natAdd r) a * z.1 a) +
        (∑ s, (d.separableLift component weight).B (i.natAdd r) s * z.2 s) =
      ∑ j, weight i j * height z j := by
  simp [separableLift, sum_append_zero_left_mul_fst]

/-- With no components, every added budget row of `separableLift` reads `0 ≤ 0`. -/
theorem separableLift_row_budget_fin_zero (d : FiniteModel n m l r)
    (component : Fin 0 → Point n m → ℝ) (weight : Fin l → Fin 0 → ℝ) (i : Fin l)
    (z : Point (n + 0) m) :
    (∑ a, (d.separableLift component weight).A (i.natAdd r) a * z.1 a) +
        (∑ s, (d.separableLift component weight).B (i.natAdd r) s * z.2 s) = 0 ∧
      (d.separableLift component weight).rhs (i.natAdd r) = 0 := by
  rw [separableLift_row_budget, separableLift_rhs_budget]
  simp

/-- The affine rows of `separableLift` consist precisely of the original affine rows on
`project z` together with the weighted height budget inequalities
`∑ j, weight i j * height z j ≤ 0`. -/
theorem separableLift_affine_rows_iff (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (∀ k, (∑ i, (d.separableLift component weight).A k i * z.1 i) +
        (∑ s, (d.separableLift component weight).B k s * z.2 s) ≤
          (d.separableLift component weight).rhs k) ↔
      (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ s, d.B k s * (project z).2 s) ≤ d.rhs k) ∧
        ∀ i, (∑ j, weight i j * height z j) ≤ 0 := by
  rw [Fin.forall_fin_add]
  simp only [separableLift_row_orig, separableLift_row_budget, separableLift_rhs_orig,
    separableLift_rhs_budget]

/-- The component-height residuals `component j (project z) - height z j ≤ 0` are equivalent to
`component j (project z) ≤ height z j`. -/
theorem separableLift_nonlinear_rows_iff (d : FiniteModel n m l r)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (∀ j, (d.separableLift component weight).g j z ≤ 0) ↔
      ∀ j, component j (project z) ≤ height z j :=
  forall_congr' fun _ => sub_nonpos

/-- With no components, a residual decomposed as a weighted sum of components vanishes. -/
theorem g_eq_zero_of_eq_sum_fin_zero {d : FiniteModel n m l r}
    {component : Fin 0 → Point n m → ℝ} {weight : Fin l → Fin 0 → ℝ}
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) (i : Fin l) (x : Point n m) :
    d.g i x = 0 := by
  simp [hg]

/-- Under the separable decomposition `hg`, the parameterized feasible set `d.feasibleWith D P`
coincides with `originalSet` on base domain `d.affineFeasibleWith D P`, with inner map
`fun x j => component j x`, outer map `fun y i => ∑ j, weight i j * y j`, and budget `0`. -/
theorem feasibleWith_eq_originalSet (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    d.feasibleWith D P =
      originalSet (d.affineFeasibleWith D P) (fun x j => component j x)
        (fun y i => ∑ j, weight i j * y j) 0 := by
  ext x
  simp only [mem_feasibleWith_iff, mem_originalSet_iff, mem_affineFeasibleWith_iff, Pi.le_def,
    Pi.zero_apply, hg]
  tauto

/-- Under `pointEquiv n m q`, the lifted parameterized feasible set of `d.separableLift` equals
the preimage of `liftedSet` on base domain `d.affineFeasibleWith D P` and unrestricted height
domain `univ`, with inner map `fun x j => component j x`, outer map
`fun y i => ∑ j, weight i j * y j`, and budget `0`. -/
theorem separableLift_feasibleWith_eq_preimage_liftedSet (d : FiniteModel n m l r)
    (D : Set (Point n m)) (P : (Fin m → ℝ) → Prop)
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.separableLift component weight).feasibleWith (project ⁻¹' D) P =
      pointEquiv n m q ⁻¹'
        liftedSet (d.affineFeasibleWith D P) univ (fun x j => component j x)
          (fun y i => ∑ j, weight i j * y j) 0 := by
  ext z
  simp only [mem_feasibleWith_iff, mem_preimage, separableLift_nonlinear_rows_iff,
    separableLift_affine_rows_iff, mem_liftedSet_iff, pointEquiv_apply,
    mem_affineFeasibleWith_iff, mem_univ, true_and, Pi.le_def, Pi.zero_apply, project_snd]
  tauto

/-- Inserting the actual component values lifts any `feasibleWith D P` point of `d` into
`separableLift`, without needing nonnegativity of `weight`. -/
theorem insertHeight_component_mem_separableLift_feasibleWith (d : FiniteModel n m l r)
    (D : Set (Point n m)) {P : (Fin m → ℝ) → Prop}
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x)
    {x : Point n m} (hx : x ∈ d.feasibleWith D P) :
    insertHeight x (fun j => component j x) ∈
      (d.separableLift component weight).feasibleWith (project ⁻¹' D) P := by
  rw [separableLift_feasibleWith_eq_preimage_liftedSet]
  rw [feasibleWith_eq_originalSet d D P component weight hg] at hx
  simpa only [mem_preimage, pointEquiv_apply, project_insertHeight, height_insertHeight] using
    graph_mem_liftedSet (mapsTo_univ _ _) hx

/-- Inserting the actual component values lifts any `feasibleOn D` point of `d` into
`separableLift`, without needing nonnegativity of `weight`. -/
theorem insertHeight_component_mem_separableLift_feasibleOn (d : FiniteModel n m l r)
    (D : Set (Point n m)) (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x)
    {x : Point n m} (hx : x ∈ d.feasibleOn D) :
    insertHeight x (fun j => component j x) ∈
      (d.separableLift component weight).feasibleOn (project ⁻¹' D) := by
  simp only [feasibleOn_eq_feasibleWith, separableLift_lo, separableLift_hi] at hx ⊢
  exact insertHeight_component_mem_separableLift_feasibleWith d D component weight hg hx

/-- Exact projection for separable-height lifting under nonnegative weights and any integer-block
predicate `P`. -/
theorem separable_feasibleWith_projection (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).feasibleWith (project ⁻¹' D) P =
      d.feasibleWith D P := by
  rw [separableLift_feasibleWith_eq_preimage_liftedSet,
    feasibleWith_eq_originalSet d D P component weight hg,
    ← fst_comp_pointEquiv (n := n) (m := m) (q := q), image_comp, Equiv.image_preimage]
  exact projection_eq (mapsTo_univ _ _) fun _ _ _ _ hle i =>
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hw i j)

/-- **Exact mixed-integer projection for separable-height lifting.** Under nonnegative weights
and the separable decomposition `hg`, projecting `(d.separableLift component weight).feasibleOn`
recovers `d.feasibleOn D`. -/
theorem separable_projection (d : FiniteModel n m l r) (D : Set (Point n m))
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).feasibleOn (project ⁻¹' D) =
      d.feasibleOn D := by
  simp only [feasibleOn_eq_feasibleWith, separableLift_lo, separableLift_hi]
  exact separable_feasibleWith_projection d D _ component weight hw hg

/-- **Exact continuous-relaxation projection for separable-height lifting.** -/
theorem separable_relaxation_projection (d : FiniteModel n m l r) (D : Set (Point n m))
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    project '' (d.separableLift component weight).relaxationOn (project ⁻¹' D) =
      d.relaxationOn D := by
  simp only [relaxationOn_eq_feasibleWith, separableLift_lo, separableLift_hi]
  exact separable_feasibleWith_projection d D _ component weight hw hg

/-- **Feasible minimum equivalence for separable-height lifting (mixed-integer problem).** -/
theorem separable_minimum_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    (z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ∧
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z) ↔
      z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D) ∧
        project z ∈ d.feasibleOn D ∧ IsMinOn d.objective (d.feasibleOn D) (project z) := by
  rw [separableLift_objective, ← separable_projection d D component weight hw hg,
    mem_and_isMinOn_comp_iff]

/-- **Attainment equivalence for separable-height lifting (mixed-integer problem).** -/
theorem separable_attainment_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    (∃ z ∈ (d.separableLift component weight).feasibleOn (project ⁻¹' D),
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).feasibleOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.feasibleOn D, IsMinOn d.objective (d.feasibleOn D) x := by
  rw [separableLift_objective, ← separable_projection d D component weight hw hg,
    exists_mem_image_isMinOn_iff]

/-- **Feasible minimum equivalence for separable-height lifting (continuous relaxation).** -/
theorem separable_relaxation_minimum_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) (z : Point (n + q) m) :
    (z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ∧
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).relaxationOn (project ⁻¹' D)) z) ↔
      z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D) ∧
        project z ∈ d.relaxationOn D ∧ IsMinOn d.objective (d.relaxationOn D) (project z) := by
  rw [separableLift_objective, ← separable_relaxation_projection d D component weight hw hg,
    mem_and_isMinOn_comp_iff]

/-- **Attainment equivalence for separable-height lifting (continuous relaxation).** -/
theorem separable_relaxation_attainment_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (component : Fin q → Point n m → ℝ) (weight : Fin l → Fin q → ℝ)
    (hw : ∀ i j, 0 ≤ weight i j)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * component j x) :
    (∃ z ∈ (d.separableLift component weight).relaxationOn (project ⁻¹' D),
      IsMinOn (d.separableLift component weight).objective
        ((d.separableLift component weight).relaxationOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.relaxationOn D, IsMinOn d.objective (d.relaxationOn D) x := by
  rw [separableLift_objective, ← separable_relaxation_projection d D component weight hw hg,
    exists_mem_image_isMinOn_iff]

end TauCeti.ConvexLifting.FiniteModel
