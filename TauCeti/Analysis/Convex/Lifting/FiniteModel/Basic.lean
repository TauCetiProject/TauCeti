/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Finite mixed-integer nonlinear models and coordinate lifting

This file defines the finite mixed-integer nonlinear optimization data (`FiniteModel`) used to
formulate exact affine-argument normalizations and separable-height lifts. Points `Point n m`
consist of an `n`-dimensional real continuous block paired with an `m`-dimensional real block on
which integrality can be imposed. A `FiniteModel n m l r` stores `l` nonlinear residual functions
bounded above by zero, `r` affine inequality rows, linear objective coefficients on both blocks,
and finite real lower and upper bounds on the integer block.

Enlarging the continuous block from `n` to `n + q` is managed by `project` (forgetting the
appended coordinates while retaining the integer block), `height` (reading the appended
coordinates), and `insertHeight` (appending a height vector to an original point), packaged
together as the equivalence `pointEquiv`. Affine expressions `affineArgument` evaluate linear
combinations of both coordinate blocks plus an offset, and support exact Fréchet derivative
transport when univariate component derivatives are supplied at the evaluated argument.

## Main definitions

* `TauCeti.ConvexLifting.Point` — `(Fin n → ℝ) × (Fin m → ℝ)`.
* `TauCeti.ConvexLifting.FiniteModel` — nonlinear residuals, affine rows, linear objective, and
  integer-block bounds.
* `TauCeti.ConvexLifting.project`, `TauCeti.ConvexLifting.height`,
  `TauCeti.ConvexLifting.insertHeight`, and `TauCeti.ConvexLifting.pointEquiv` — coordinate
  projection, height extraction, insertion, and splitting equivalence for `Point (n + q) m`.
* `TauCeti.ConvexLifting.affineArgument` and `TauCeti.ConvexLifting.affineArgumentCLM` — affine
  expressions on `Point n m` and their linear parts.
* `TauCeti.ConvexLifting.FiniteModel.objective`, `TauCeti.ConvexLifting.FiniteModel.feasibleOn`,
  and `TauCeti.ConvexLifting.FiniteModel.relaxationOn` — linear objective, mixed-integer feasible
  set, and continuous relaxation.

## References

* H. Hijazi, P. Bonami and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (4 October 2013),
  pp. 1–2.
-/

public section

open Set

namespace TauCeti.ConvexLifting

/-- Continuous coordinates in `Fin n → ℝ` paired with real coordinates in `Fin m → ℝ` on which
integrality can be imposed. -/
abbrev Point (n m : ℕ) := (Fin n → ℝ) × (Fin m → ℝ)

/-- Data of a finite mixed-integer nonlinear model with `n` continuous variables, `m`
integer-constrained variables, `l` nonlinear residual inequalities `g i x ≤ 0`, and `r` affine
inequality rows. -/
@[ext]
structure FiniteModel (n m l r : ℕ) where
  /-- Nonlinear residual functions bounded above by `0`. -/
  g : Fin l → Point n m → ℝ
  /-- Continuous-block coefficients of the affine inequality rows. -/
  A : Fin r → Fin n → ℝ
  /-- Integer-block coefficients of the affine inequality rows. -/
  B : Fin r → Fin m → ℝ
  /-- Right-hand sides of the affine inequality rows. -/
  rhs : Fin r → ℝ
  /-- Linear objective coefficients on the continuous block. -/
  c1 : Fin n → ℝ
  /-- Linear objective coefficients on the integer block. -/
  c2 : Fin m → ℝ
  /-- Lower bounds on the integer-block coordinates. -/
  lo : Fin m → ℝ
  /-- Upper bounds on the integer-block coordinates. -/
  hi : Fin m → ℝ

section Coordinates

variable {n m q : ℕ}

/-- Forget the `q` appended continuous coordinates and retain the original continuous and integer
blocks. -/
def project (z : Point (n + q) m) : Point n m :=
  (fun i => z.1 (i.castAdd q), z.2)

/-- Read the `q` appended continuous argument or height coordinates. -/
def height (z : Point (n + q) m) : Fin q → ℝ :=
  fun j => z.1 (j.natAdd n)

/-- Append a `q`-dimensional height or argument vector to the continuous block of `x`. -/
def insertHeight (x : Point n m) (y : Fin q → ℝ) : Point (n + q) m :=
  (Fin.append x.1 y, x.2)

/-- Continuous coordinates of `project z`. -/
@[simp]
theorem project_fst (z : Point (n + q) m) (i : Fin n) :
    (project z).1 i = z.1 (i.castAdd q) := (rfl)

/-- Integer-block coordinates of `project z`. -/
@[simp]
theorem project_snd (z : Point (n + q) m) : (project z).2 = z.2 := (rfl)

/-- Coordinate evaluation of `height z`. -/
@[simp]
theorem height_apply (z : Point (n + q) m) (j : Fin q) :
    height z j = z.1 (j.natAdd n) := (rfl)

/-- Original continuous coordinates of `insertHeight x y`. -/
@[simp]
theorem insertHeight_fst_castAdd (x : Point n m) (y : Fin q → ℝ) (i : Fin n) :
    (insertHeight x y).1 (i.castAdd q) = x.1 i := by
  simp [insertHeight]

/-- Appended continuous coordinates of `insertHeight x y`. -/
@[simp]
theorem insertHeight_fst_natAdd (x : Point n m) (y : Fin q → ℝ) (j : Fin q) :
    (insertHeight x y).1 (j.natAdd n) = y j := by
  simp [insertHeight]

/-- Integer-block coordinates of `insertHeight x y`. -/
@[simp]
theorem insertHeight_snd (x : Point n m) (y : Fin q → ℝ) :
    (insertHeight x y).2 = x.2 := (rfl)

/-- Projecting after height insertion recovers the original point. -/
@[simp]
theorem project_insertHeight (x : Point n m) (y : Fin q → ℝ) :
    project (insertHeight x y) = x := by
  ext i
  · exact insertHeight_fst_castAdd x y i
  · rfl

/-- Reading the height after height insertion recovers the inserted vector. -/
@[simp]
theorem height_insertHeight (x : Point n m) (y : Fin q → ℝ) :
    height (insertHeight x y) = y := by
  ext j
  exact insertHeight_fst_natAdd x y j

/-- Reconstructing an enlarged point from its projection and height recovers the point. -/
@[simp]
theorem insertHeight_project_height (z : Point (n + q) m) :
    insertHeight (project z) (height z) = z := by
  ext i
  · exact congrFun (Fin.append_castAdd_natAdd (f := z.1)) i
  · rfl

/-- With `q = 0` appended coordinates, projection is the identity. -/
@[simp]
theorem project_zero (z : Point (n + 0) m) : project z = z := by
  ext i
  · simp [project]
  · rfl

/-- With `q = 0` appended coordinates, height insertion adds no coordinates. -/
@[simp]
theorem insertHeight_zero (x : Point n m) (y : Fin 0 → ℝ) : insertHeight x y = x := by
  rw [← project_zero (insertHeight x y), project_insertHeight]

/-- The splitting equivalence `Point (n + q) m ≃ Point n m × (Fin q → ℝ)` given by `project` and
`height`. -/
def pointEquiv (n m q : ℕ) : Point (n + q) m ≃ Point n m × (Fin q → ℝ) where
  toFun z := (project z, height z)
  invFun p := insertHeight p.1 p.2
  left_inv := insertHeight_project_height
  right_inv p := Prod.ext (project_insertHeight p.1 p.2) (height_insertHeight p.1 p.2)

/-- Forward evaluation of `pointEquiv`. -/
@[simp]
theorem pointEquiv_apply (z : Point (n + q) m) :
    pointEquiv n m q z = (project z, height z) := (rfl)

/-- Inverse evaluation of `pointEquiv`. -/
@[simp]
theorem pointEquiv_symm_apply (p : Point n m × (Fin q → ℝ)) :
    (pointEquiv n m q).symm p = insertHeight p.1 p.2 := (rfl)

/-- Composing `pointEquiv` with `Prod.fst` gives `project`. -/
@[simp]
theorem fst_comp_pointEquiv : Prod.fst ∘ pointEquiv n m q = project := (rfl)

/-- Splitting a continuous-block inner product with appended coefficients into its original and
height parts. -/
theorem sum_append_mul_fst (a : Fin n → ℝ) (c : Fin q → ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.append a c i * z.1 i) =
      (∑ i : Fin n, a i * (project z).1 i) + ∑ j : Fin q, c j * height z j := by
  rw [Fin.sum_univ_add]
  simp [project, height]

/-- A continuous-block linear form extended by zero on the appended coordinates depends only on
`project z`. -/
theorem sum_append_zero_right_mul_fst (a : Fin n → ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.append a 0 i * z.1 i) = ∑ i : Fin n, a i * (project z).1 i := by
  rw [sum_append_mul_fst]
  simp

/-- A continuous-block linear form vanishing on the original coordinates depends only on
`height z`. -/
theorem sum_append_zero_left_mul_fst (c : Fin q → ℝ) (z : Point (n + q) m) :
    (∑ i : Fin (n + q), Fin.append 0 c i * z.1 i) = ∑ j : Fin q, c j * height z j := by
  rw [sum_append_mul_fst]
  simp

end Coordinates

section AffineArgument

variable {n m : ℕ}

/-- An affine expression `(∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset` on `Point n m`. -/
def affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) : ℝ :=
  (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset

/-- Explicit evaluation of `affineArgument`. -/
@[simp]
theorem affineArgument_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) :
    affineArgument a b offset x = (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset := (rfl)

/-- The continuous linear part of `affineArgument a b offset`. -/
noncomputable def affineArgumentCLM (a : Fin n → ℝ) (b : Fin m → ℝ) : Point n m →L[ℝ] ℝ :=
  (∑ i : Fin n, a i • (ContinuousLinearMap.proj (R := ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin m → ℝ))) +
    ∑ j : Fin m, b j • (ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin m → ℝ))

/-- Pointwise evaluation of `affineArgumentCLM`. -/
@[simp]
theorem affineArgumentCLM_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (v : Point n m) :
    affineArgumentCLM a b v = (∑ i, a i * v.1 i) + ∑ j, b j * v.2 j := by
  simp [affineArgumentCLM, smul_eq_mul]

/-- The Fréchet derivative of `affineArgument a b offset` at every point `x` is
`affineArgumentCLM a b`. -/
theorem hasFDerivAt_affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ)
    (x : Point n m) :
    HasFDerivAt (affineArgument a b offset) (affineArgumentCLM a b) x := by
  have hEq : affineArgument a b offset = fun y => affineArgumentCLM a b y + offset := by
    ext y
    simp
  rw [hEq]
  exact (affineArgumentCLM a b).hasFDerivAt.add_const offset

/-- Transporting a univariate derivative `HasDerivAt φ φ'` at `affineArgument a b offset x` to a
Fréchet derivative of `y ↦ φ (affineArgument a b offset y)` at `x`. -/
theorem hasFDerivAt_comp_affineArgument {φ : ℝ → ℝ} {φ' : ℝ}
    (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) {x : Point n m}
    (hφ : HasDerivAt φ φ' (affineArgument a b offset x)) :
    HasFDerivAt (fun y => φ (affineArgument a b offset y)) (φ' • affineArgumentCLM a b) x :=
  hφ.comp_hasFDerivAt x (hasFDerivAt_affineArgument a b offset x)

/-- Transporting supplied univariate component derivatives at each evaluated affine argument to a
Fréchet derivative of the weighted sum `y ↦ ∑ j, weight j * phi j (affineArgument ...)`. -/
theorem hasFDerivAt_sum_mul_comp_affineArgument {q : ℕ}
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (phi' : Fin q → ℝ) (weight : Fin q → ℝ) {x : Point n m}
    (hphi : ∀ j, HasDerivAt (phi j) (phi' j) (affineArgument (a j) (b j) (offset j) x)) :
    HasFDerivAt
      (fun y => ∑ j, weight j * phi j (affineArgument (a j) (b j) (offset j) y))
      (∑ j, (weight j * phi' j) • affineArgumentCLM (a j) (b j)) x := by
  refine HasFDerivAt.fun_sum fun j _ => ?_
  simpa only [mul_smul] using
    (hasFDerivAt_comp_affineArgument (a j) (b j) (offset j) (hphi j)).const_mul (weight j)

end AffineArgument

namespace FiniteModel

variable {n m l r q : ℕ}

/-- The linear objective `(∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j` in the two coordinate
blocks. -/
def objective (d : FiniteModel n m l r) (x : Point n m) : ℝ :=
  (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j

/-- Explicit evaluation of `FiniteModel.objective`. -/
theorem objective_apply (d : FiniteModel n m l r) (x : Point n m) :
    d.objective x = (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j := (rfl)

/-- With zero continuous and integer coordinates, the objective is identically zero. -/
@[simp]
theorem objective_zero_dim (d : FiniteModel 0 0 l r) (x : Point 0 0) :
    d.objective x = 0 := by
  simp [objective_apply]

/-- Extending `d.c1` by zero on appended continuous coordinates pulls `d.objective` back along
`project`. -/
theorem objective_eq_comp_project {l' r' : ℕ} {d : FiniteModel n m l r}
    {d' : FiniteModel (n + q) m l' r'}
    (hc1 : d'.c1 = Fin.append d.c1 0) (hc2 : d'.c2 = d.c2) (z : Point (n + q) m) :
    d'.objective z = d.objective (project z) := by
  simp only [objective_apply, hc1, hc2, project_snd]
  rw [sum_append_zero_right_mul_fst]

/-- The mixed-integer feasible set on domain `D`: points `x ∈ D` satisfying every nonlinear
residual `d.g j x ≤ 0`, every affine row, and boundedness and integrality of `x.2`. -/
def feasibleOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
      x.2 = fun j => (y j : ℝ)}

/-- The continuous relaxation on domain `D`: the same domain, nonlinear residuals, affine rows, and
coordinate bounds on `x.2`, without requiring `x.2` to be integral. -/
def relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
    (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
    ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j}

/-- Membership in `FiniteModel.feasibleOn`. -/
@[simp]
theorem mem_feasibleOn_iff (d : FiniteModel n m l r) (D : Set (Point n m)) (x : Point n m) :
    x ∈ d.feasibleOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          x.2 = fun j => (y j : ℝ) :=
  (Iff.rfl)

/-- Membership in `FiniteModel.relaxationOn`. -/
@[simp]
theorem mem_relaxationOn_iff (d : FiniteModel n m l r) (D : Set (Point n m)) (x : Point n m) :
    x ∈ d.relaxationOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j :=
  (Iff.rfl)

/-- Every point of `d.feasibleOn D` lies in `D`. -/
theorem feasibleOn_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ D :=
  fun _ hx => hx.1

/-- Every point of `d.relaxationOn D` lies in `D`. -/
theorem relaxationOn_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.relaxationOn D ⊆ D :=
  fun _ hx => hx.1

/-- Mixed-integer feasibility is contained in the continuous relaxation. -/
theorem feasibleOn_subset_relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ d.relaxationOn D := by
  rintro x ⟨hxD, hg, hA, y, hbd, hx2⟩
  refine ⟨hxD, hg, hA, fun j => ?_⟩
  simpa only [hx2] using hbd j

/-- With `m = 0` integer-block coordinates, mixed-integer feasibility coincides with the
continuous relaxation. -/
theorem feasibleOn_eq_relaxationOn_of_zero (d : FiniteModel n 0 l r) (D : Set (Point n 0)) :
    d.feasibleOn D = d.relaxationOn D := by
  refine Subset.antisymm (d.feasibleOn_subset_relaxationOn D) ?_
  rintro x ⟨hxD, hg, hA, _⟩
  exact ⟨hxD, hg, hA, Fin.elim0, fun j => j.elim0, funext fun j => j.elim0⟩

end FiniteModel

end TauCeti.ConvexLifting
