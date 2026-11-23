/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Logic.Equiv.Fin.Basic
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
together as the equivalence `pointEquiv` built from `Fin.appendEquiv`. Affine expressions
`affineArgument` evaluate linear combinations of both coordinate blocks plus an offset, and support
exact Fréchet derivative transport when univariate component derivatives are supplied at the
evaluated argument.

## Main definitions

* `TauCeti.ConvexLifting.Point` — `(Fin n → ℝ) × (Fin m → ℝ)`.
* `TauCeti.ConvexLifting.FiniteModel` — nonlinear residuals, affine rows, linear objective, and
  integer-block bounds.
* `TauCeti.ConvexLifting.project`, `TauCeti.ConvexLifting.height`,
  `TauCeti.ConvexLifting.insertHeight`, and `TauCeti.ConvexLifting.pointEquiv` — coordinate
  projection, height extraction, insertion, and splitting equivalence for `Point (n + q) m`.
* `TauCeti.ConvexLifting.affineArgument` and `TauCeti.ConvexLifting.affineArgumentCLM` — affine
  expressions on `Point n m` and their linear parts.
* `TauCeti.ConvexLifting.FiniteModel.objective`,
  `TauCeti.ConvexLifting.FiniteModel.affineFeasibleWith`,
  `TauCeti.ConvexLifting.FiniteModel.feasibleWith`,
  `TauCeti.ConvexLifting.FiniteModel.feasibleOn`, and
  `TauCeti.ConvexLifting.FiniteModel.relaxationOn` — linear objective, parameterized affine and
  nonlinear feasible-set constructors, mixed-integer feasible set, and continuous relaxation.

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
  ext i <;> simp

/-- Reading the height after height insertion recovers the inserted vector. -/
@[simp]
theorem height_insertHeight (x : Point n m) (y : Fin q → ℝ) :
    height (insertHeight x y) = y := by
  ext j
  simp

/-- Reconstructing an enlarged point from its projection and height recovers the point. -/
@[simp]
theorem insertHeight_project_height (z : Point (n + q) m) :
    insertHeight (project z) (height z) = z := by
  unfold insertHeight project height
  exact Prod.ext (Fin.append_castAdd_natAdd (f := z.1)) rfl

/-- The splitting equivalence `Point (n + q) m ≃ Point n m × (Fin q → ℝ)` built from
`Fin.appendEquiv`, separating `project z` from the `q` appended coordinates `height z`. -/
def pointEquiv (n m q : ℕ) : Point (n + q) m ≃ Point n m × (Fin q → ℝ) :=
  (((Fin.appendEquiv n q).symm.prodCongr (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)).trans <|
    ((Equiv.refl _).prodCongr (Equiv.prodComm _ _)).trans (Equiv.prodAssoc _ _ _).symm

/-- Forward evaluation of `pointEquiv`. -/
@[simp]
theorem pointEquiv_apply (z : Point (n + q) m) :
    pointEquiv n m q z = (project z, height z) := by
  ext i <;> simp [pointEquiv]

/-- Inverse evaluation of `pointEquiv`. -/
@[simp]
theorem pointEquiv_symm_apply (p : Point n m × (Fin q → ℝ)) :
    (pointEquiv n m q).symm p = insertHeight p.1 p.2 := by
  ext i <;> simp [pointEquiv, insertHeight]

/-- Composing `pointEquiv` with `Prod.fst` gives `project`. -/
@[simp]
theorem fst_comp_pointEquiv : Prod.fst ∘ pointEquiv n m q = project :=
  funext fun z => congrArg Prod.fst (pointEquiv_apply z)

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

/-- The continuous linear part of `affineArgument a b offset`. -/
def affineArgumentCLM (a : Fin n → ℝ) (b : Fin m → ℝ) : Point n m →L[ℝ] ℝ :=
  (∑ i : Fin n, a i • (ContinuousLinearMap.proj (R := ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin m → ℝ))) +
    ∑ j : Fin m, b j • (ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin m → ℝ))

/-- Pointwise evaluation of `affineArgumentCLM`. -/
@[simp]
theorem affineArgumentCLM_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (v : Point n m) :
    affineArgumentCLM a b v = (∑ i, a i * v.1 i) + ∑ j, b j * v.2 j := by
  simp [affineArgumentCLM, smul_eq_mul]

/-- Extending the continuous-block coefficients of `affineArgumentCLM` by zero on appended
coordinates pulls the linear form back along `project`. -/
@[simp]
theorem coe_affineArgumentCLM_append_zero {q : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    ⇑(affineArgumentCLM (Fin.append a (0 : Fin q → ℝ)) b) =
      ⇑(affineArgumentCLM a b) ∘ project := by
  ext z
  simp only [Function.comp_apply, affineArgumentCLM_apply, sum_append_zero_right_mul_fst,
    project_snd]

/-- An affine expression `(∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset` on `Point n m`,
defined via its continuous linear part `affineArgumentCLM a b`. -/
def affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ)
    (x : Point n m) : ℝ :=
  affineArgumentCLM a b x + offset

/-- Explicit evaluation of `affineArgument`. -/
@[simp]
theorem affineArgument_apply (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ) (x : Point n m) :
    affineArgument a b offset x = (∑ i, a i * x.1 i) + (∑ j, b j * x.2 j) + offset := by
  simp only [affineArgument, affineArgumentCLM_apply]

/-- The Fréchet derivative of `affineArgument a b offset` at every point `x` is
`affineArgumentCLM a b`. -/
theorem hasFDerivAt_affineArgument (a : Fin n → ℝ) (b : Fin m → ℝ) (offset : ℝ)
    (x : Point n m) :
    HasFDerivAt (affineArgument a b offset) (affineArgumentCLM a b) x :=
  (affineArgumentCLM a b).hasFDerivAt.add_const offset

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
blocks, given by `affineArgumentCLM d.c1 d.c2`. -/
def objective (d : FiniteModel n m l r) : Point n m → ℝ :=
  ⇑(affineArgumentCLM d.c1 d.c2)

/-- `FiniteModel.objective` is the underlying function of `affineArgumentCLM d.c1 d.c2`. -/
theorem objective_eq_affineArgumentCLM (d : FiniteModel n m l r) :
    d.objective = ⇑(affineArgumentCLM d.c1 d.c2) := (rfl)

/-- Explicit evaluation of `FiniteModel.objective`. -/
theorem objective_apply (d : FiniteModel n m l r) (x : Point n m) :
    d.objective x = (∑ i, d.c1 i * x.1 i) + ∑ j, d.c2 j * x.2 j := by
  rw [objective_eq_affineArgumentCLM, affineArgumentCLM_apply]

/-- With zero continuous and integer coordinates, the objective is identically zero. -/
@[simp]
theorem objective_zero_dim (d : FiniteModel 0 0 l r) (x : Point 0 0) :
    d.objective x = 0 := by
  simp [objective_apply]

/-- Extending `d.c1` by zero on appended continuous coordinates pulls `d.objective` back along
`project`. -/
theorem objective_eq_comp_project {l' r' : ℕ} {d : FiniteModel n m l r}
    {d' : FiniteModel (n + q) m l' r'}
    (hc1 : d'.c1 = Fin.append d.c1 0) (hc2 : d'.c2 = d.c2) :
    d'.objective = d.objective ∘ project := by
  rw [objective_eq_affineArgumentCLM, objective_eq_affineArgumentCLM, hc1, hc2,
    coe_affineArgumentCLM_append_zero]

/-- Points `x ∈ D` satisfying all affine inequality rows of `d` together with a predicate `P` on
the integer-block coordinates `x.2`, excluding the nonlinear residuals `d.g`. -/
def affineFeasibleWith (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) : Set (Point n m) :=
  {x | x ∈ D ∧ (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧ P x.2}

/-- Membership in `FiniteModel.affineFeasibleWith`. -/
@[simp]
theorem mem_affineFeasibleWith_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) (x : Point n m) :
    x ∈ d.affineFeasibleWith D P ↔
      x ∈ D ∧ (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧ P x.2 :=
  (Iff.rfl)

/-- Points `x ∈ D` satisfying all nonlinear residuals `d.g j x ≤ 0`, all affine inequality rows of
`d`, and a predicate `P` on the integer-block coordinates `x.2`. Both `feasibleOn` and
`relaxationOn` are instances of `feasibleWith`. -/
def feasibleWith (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) : Set (Point n m) :=
  {x ∈ d.affineFeasibleWith D P | ∀ j, d.g j x ≤ 0}

/-- Membership in `FiniteModel.feasibleWith`. -/
@[simp]
theorem mem_feasibleWith_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) (x : Point n m) :
    x ∈ d.feasibleWith D P ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧ P x.2 :=
  ⟨fun ⟨⟨hxD, hA, hP⟩, hg⟩ => ⟨hxD, hg, hA, hP⟩,
    fun ⟨hxD, hg, hA, hP⟩ => ⟨⟨hxD, hA, hP⟩, hg⟩⟩

/-- Every point of `d.feasibleWith D P` lies in `D`. -/
theorem feasibleWith_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m))
    (P : (Fin m → ℝ) → Prop) : d.feasibleWith D P ⊆ D :=
  fun _ hx => hx.1.1

/-- Monotonicity of `d.feasibleWith D` in the integer-block predicate. -/
theorem feasibleWith_mono (d : FiniteModel n m l r) (D : Set (Point n m))
    {P Q : (Fin m → ℝ) → Prop} (hPQ : ∀ v, P v → Q v) :
    d.feasibleWith D P ⊆ d.feasibleWith D Q :=
  fun _ ⟨⟨hxD, hA, hP⟩, hg⟩ => ⟨⟨hxD, hA, hPQ _ hP⟩, hg⟩

/-- The mixed-integer feasible set on domain `D`: points `x ∈ D` satisfying every nonlinear
residual `d.g j x ≤ 0`, every affine row, and boundedness and integrality of `x.2`. -/
def feasibleOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  d.feasibleWith D fun v =>
    ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
      v = fun j => (y j : ℝ)

/-- The continuous relaxation on domain `D`: the same domain, nonlinear residuals, affine rows, and
coordinate bounds on `x.2`, without requiring `x.2` to be integral. -/
def relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) : Set (Point n m) :=
  d.feasibleWith D fun v => ∀ j, d.lo j ≤ v j ∧ v j ≤ d.hi j

/-- `feasibleOn` expressed as an instance of `feasibleWith`. -/
theorem feasibleOn_eq_feasibleWith (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D = d.feasibleWith D fun v =>
      ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
        v = fun j => (y j : ℝ) :=
  (rfl)

/-- `relaxationOn` expressed as an instance of `feasibleWith`. -/
theorem relaxationOn_eq_feasibleWith (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.relaxationOn D = d.feasibleWith D fun v => ∀ j, d.lo j ≤ v j ∧ v j ≤ d.hi j :=
  (rfl)

/-- Membership in `FiniteModel.feasibleOn`. -/
@[simp]
theorem mem_feasibleOn_iff (d : FiniteModel n m l r) (D : Set (Point n m)) (x : Point n m) :
    x ∈ d.feasibleOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∃ y : Fin m → ℤ, (∀ j, d.lo j ≤ (y j : ℝ) ∧ (y j : ℝ) ≤ d.hi j) ∧
          x.2 = fun j => (y j : ℝ) :=
  d.mem_feasibleWith_iff D _ x

/-- Membership in `FiniteModel.relaxationOn`. -/
@[simp]
theorem mem_relaxationOn_iff (d : FiniteModel n m l r) (D : Set (Point n m)) (x : Point n m) :
    x ∈ d.relaxationOn D ↔
      x ∈ D ∧ (∀ j, d.g j x ≤ 0) ∧
        (∀ k, (∑ i, d.A k i * x.1 i) + (∑ j, d.B k j * x.2 j) ≤ d.rhs k) ∧
        ∀ j, d.lo j ≤ x.2 j ∧ x.2 j ≤ d.hi j :=
  d.mem_feasibleWith_iff D _ x

/-- Every point of `d.feasibleOn D` lies in `D`. -/
theorem feasibleOn_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ D :=
  d.feasibleWith_subset_domain D _

/-- Every point of `d.relaxationOn D` lies in `D`. -/
theorem relaxationOn_subset_domain (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.relaxationOn D ⊆ D :=
  d.feasibleWith_subset_domain D _

/-- Mixed-integer feasibility is contained in the continuous relaxation. -/
theorem feasibleOn_subset_relaxationOn (d : FiniteModel n m l r) (D : Set (Point n m)) :
    d.feasibleOn D ⊆ d.relaxationOn D :=
  d.feasibleWith_mono D fun _ ⟨y, hbd, hv⟩ j => by simpa only [hv] using hbd j

/-- With `m = 0` integer-block coordinates, mixed-integer feasibility coincides with the
continuous relaxation. -/
theorem feasibleOn_eq_relaxationOn_of_zero (d : FiniteModel n 0 l r) (D : Set (Point n 0)) :
    d.feasibleOn D = d.relaxationOn D :=
  Subset.antisymm (d.feasibleOn_subset_relaxationOn D) <|
    d.feasibleWith_mono D fun _ _ => ⟨Fin.elim0, fun j => j.elim0, funext fun j => j.elim0⟩

end FiniteModel

end TauCeti.ConvexLifting
