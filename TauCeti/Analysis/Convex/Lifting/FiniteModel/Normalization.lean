/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.FiniteModel.Basic
public import Mathlib.Order.Filter.Extr
import TauCeti.Order.Filter.Extr
import Mathlib.Tactic.Linarith

/-!
# Affine-argument normalization of finite mixed-integer models

When the nonlinear residuals of a `FiniteModel` decompose as weighted sums of univariate functions
evaluated at affine expressions,

    d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x),

appending one continuous argument variable `u_j` per affine expression together with the pair of
opposite affine inequalities imposing `u_j = affineArgument (a j) (b j) (offset j) x` yields the
normalized model `FiniteModel.normalizedLift`. The original affine rows, integer-block bounds, and
linear objective are preserved with zero objective coefficients on the added continuous block.

Because normalization performs exact equality substitution, it requires no sign assumption on
`weight`, no convexity, and no smoothness. It preserves mixed-integer feasibility
(`FiniteModel.normalization_projection`), the continuous relaxation
(`FiniteModel.normalization_relaxation_projection`), feasible minimizers
(`FiniteModel.normalization_minimum_iff`, `FiniteModel.normalization_relaxation_minimum_iff`), and
existence of attained minima (`FiniteModel.normalization_attainment_iff`,
`FiniteModel.normalization_relaxation_attainment_iff`).

## Main definitions

* `TauCeti.ConvexLifting.FiniteModel.normalizedLift` — the normalized finite model with `q`
  appended continuous argument coordinates and `q + q` opposite affine equality rows.

## Main statements

* `TauCeti.ConvexLifting.FiniteModel.normalizedLift_affine_rows_iff` — equivalence of the lifted
  affine rows with the original affine rows plus `height z j = affineArgument ... (project z)`.
* `TauCeti.ConvexLifting.FiniteModel.normalization_projection` and
  `TauCeti.ConvexLifting.FiniteModel.normalization_relaxation_projection` — exact projection for
  mixed-integer feasibility and the continuous relaxation.
* `TauCeti.ConvexLifting.FiniteModel.normalization_minimum_iff` and
  `TauCeti.ConvexLifting.FiniteModel.normalization_attainment_iff` — transfer of feasible minima
  and attainment for the mixed-integer problem, together with their continuous-relaxation
  counterparts.

## References

* H. Hijazi, P. Bonami and A. Ouorou, *An Outer-Inner Approximation for Separable Mixed-Integer
  Nonlinear Programs*, INFORMS Journal on Computing, Articles in Advance (4 October 2013),
  §3 opening, p. 4.
-/

public section

open Set

namespace TauCeti.ConvexLifting.FiniteModel

variable {n m l r q : ℕ}

/-- Normalize affine arguments of a `FiniteModel` by appending `q` continuous coordinates `u_j`
and imposing `u_j = affineArgument (a j) (b j) (offset j) (project z)` via two opposite affine
inequalities per coordinate. The original affine rows, integer-block bounds, and objective are
retained, with zero objective coefficients on the added coordinates. -/
def normalizedLift (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    FiniteModel (n + q) m l (r + (q + q)) where
  g := fun i z => ∑ j, weight i j * phi j (height z j)
  A := Fin.append (fun i => Fin.append (d.A i) 0)
    (Fin.append (fun j => Fin.append (-a j) (Pi.single j 1))
      (fun j => Fin.append (a j) (Pi.single j (-1))))
  B := Fin.append d.B (Fin.append (fun j => -b j) b)
  rhs := Fin.append d.rhs (Fin.append offset (-offset))
  c1 := Fin.append d.c1 0
  c2 := d.c2
  lo := d.lo
  hi := d.hi

/-- Continuous-block objective coefficients of `normalizedLift`. -/
@[simp]
theorem normalizedLift_c1 (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).c1 = Fin.append d.c1 0 := (rfl)

/-- Integer-block objective coefficients of `normalizedLift`. -/
@[simp]
theorem normalizedLift_c2 (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).c2 = d.c2 := (rfl)

/-- The normalized model evaluates the original linear objective on `project z`. -/
@[simp]
theorem normalizedLift_objective (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (d.normalizedLift a b offset phi weight).objective z = d.objective (project z) :=
  objective_eq_comp_project (normalizedLift_c1 d a b offset phi weight)
    (normalizedLift_c2 d a b offset phi weight) z

/-- Nonlinear residual evaluation of `normalizedLift`. -/
@[simp]
theorem normalizedLift_g (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (i : Fin l) (z : Point (n + q) m) :
    (d.normalizedLift a b offset phi weight).g i z = ∑ j, weight i j * phi j (height z j) :=
  (rfl)

/-- Lower bounds on the integer block are unchanged by `normalizedLift`. -/
@[simp]
theorem normalizedLift_lo (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).lo = d.lo := (rfl)

/-- Upper bounds on the integer block are unchanged by `normalizedLift`. -/
@[simp]
theorem normalizedLift_hi (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) :
    (d.normalizedLift a b offset phi weight).hi = d.hi := (rfl)

/-- Right-hand side of a retained original affine row in `normalizedLift`. -/
@[simp]
theorem normalizedLift_rhs_orig (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (k : Fin r) :
    (d.normalizedLift a b offset phi weight).rhs (k.castAdd (q + q)) = d.rhs k := by
  simp [normalizedLift]

/-- Right-hand side of an upper argument-equality row in `normalizedLift`. -/
@[simp]
theorem normalizedLift_rhs_upper (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (j : Fin q) :
    (d.normalizedLift a b offset phi weight).rhs ((j.castAdd q).natAdd r) = offset j := by
  simp [normalizedLift]

/-- Right-hand side of a lower argument-equality row in `normalizedLift`. -/
theorem normalizedLift_rhs_lower (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (j : Fin q) :
    (d.normalizedLift a b offset phi weight).rhs ((j.natAdd q).natAdd r) = -offset j := by
  simp only [normalizedLift, Fin.append_right, Pi.neg_apply]

/-- Evaluation of a retained original affine row in `normalizedLift`. -/
theorem normalizedLift_row_orig (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (k : Fin r) (z : Point (n + q) m) :
    (∑ i, (d.normalizedLift a b offset phi weight).A (k.castAdd (q + q)) i * z.1 i) +
        (∑ s, (d.normalizedLift a b offset phi weight).B (k.castAdd (q + q)) s * z.2 s) =
      (∑ i, d.A k i * (project z).1 i) + ∑ s, d.B k s * (project z).2 s := by
  simp [normalizedLift, sum_append_zero_right_mul_fst]

/-- Evaluation of an added upper argument-equality affine row in `normalizedLift`. -/
theorem normalizedLift_row_upper (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (j : Fin q) (z : Point (n + q) m) :
    (∑ i, (d.normalizedLift a b offset phi weight).A ((j.castAdd q).natAdd r) i * z.1 i) +
        (∑ s, (d.normalizedLift a b offset phi weight).B ((j.castAdd q).natAdd r) s * z.2 s) =
      height z j - (∑ i, a j i * (project z).1 i) - ∑ s, b j s * (project z).2 s := by
  simp only [normalizedLift, Fin.append_right, Fin.append_left]
  simp [sum_append_mul_fst, Finset.sum_neg_distrib, Pi.single_apply]
  ring

/-- Evaluation of an added lower argument-equality affine row in `normalizedLift`. -/
theorem normalizedLift_row_lower (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (j : Fin q) (z : Point (n + q) m) :
    (∑ i, (d.normalizedLift a b offset phi weight).A ((j.natAdd q).natAdd r) i * z.1 i) +
        (∑ s, (d.normalizedLift a b offset phi weight).B ((j.natAdd q).natAdd r) s * z.2 s) =
      (∑ i, a j i * (project z).1 i) + (∑ s, b j s * (project z).2 s) - height z j := by
  simp only [normalizedLift, Fin.append_right]
  simp [sum_append_mul_fst, Pi.single_apply]
  ring

/-- The affine rows of `normalizedLift` consist precisely of the original affine rows on
`project z` together with the argument equalities
`height z j = affineArgument (a j) (b j) (offset j) (project z)`. -/
theorem normalizedLift_affine_rows_iff (d : FiniteModel n m l r)
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ) (z : Point (n + q) m) :
    (∀ k, (∑ i, (d.normalizedLift a b offset phi weight).A k i * z.1 i) +
        (∑ s, (d.normalizedLift a b offset phi weight).B k s * z.2 s) ≤
          (d.normalizedLift a b offset phi weight).rhs k) ↔
      (∀ k, (∑ i, d.A k i * (project z).1 i) + (∑ s, d.B k s * (project z).2 s) ≤ d.rhs k) ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  rw [Fin.forall_fin_add, Fin.forall_fin_add]
  simp only [normalizedLift_row_orig, normalizedLift_row_upper, normalizedLift_row_lower,
    normalizedLift_rhs_orig, normalizedLift_rhs_upper, normalizedLift_rhs_lower, ← forall_and]
  refine and_congr_right fun _ => forall_congr' fun j => ?_
  rw [affineArgument_apply, le_antisymm_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- Mixed-integer feasibility in `normalizedLift` is equivalent to mixed-integer feasibility of
`project z` in `d` together with the argument equalities. -/
theorem mem_normalizedLift_feasibleOn_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ↔
      project z ∈ d.feasibleOn D ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  simp only [mem_feasibleOn_iff, mem_preimage, normalizedLift_g, normalizedLift_lo,
    normalizedLift_hi, normalizedLift_affine_rows_iff, project_snd]
  constructor
  · rintro ⟨hzD, hgn, ⟨hA, heq⟩, hy⟩
    refine ⟨⟨hzD, fun i => ?_, hA, hy⟩, heq⟩
    simpa only [hg i (project z), ← heq] using hgn i
  · rintro ⟨⟨hzD, hgd, hA, hy⟩, heq⟩
    refine ⟨hzD, fun i => ?_, ⟨hA, heq⟩, hy⟩
    simpa only [heq, ← hg i (project z)] using hgd i

/-- Continuous-relaxation feasibility in `normalizedLift` is equivalent to relaxation feasibility
of `project z` in `d` together with the argument equalities. -/
theorem mem_normalizedLift_relaxationOn_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ↔
      project z ∈ d.relaxationOn D ∧
        ∀ j, height z j = affineArgument (a j) (b j) (offset j) (project z) := by
  simp only [mem_relaxationOn_iff, mem_preimage, normalizedLift_g, normalizedLift_lo,
    normalizedLift_hi, normalizedLift_affine_rows_iff, project_snd]
  constructor
  · rintro ⟨hzD, hgn, ⟨hA, heq⟩, hbd⟩
    refine ⟨⟨hzD, fun i => ?_, hA, hbd⟩, heq⟩
    simpa only [hg i (project z), ← heq] using hgn i
  · rintro ⟨⟨hzD, hgd, hA, hbd⟩, heq⟩
    refine ⟨hzD, fun i => ?_, ⟨hA, heq⟩, hbd⟩
    simpa only [heq, ← hg i (project z)] using hgd i

/-- Inserting the evaluated affine arguments lifts a mixed-integer feasible point of `d` into
`normalizedLift`. -/
theorem insertHeight_affineArgument_mem_normalizedLift_feasibleOn (d : FiniteModel n m l r)
    (D : Set (Point n m)) (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    {x : Point n m} (hx : x ∈ d.feasibleOn D) :
    insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x) ∈
      (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) := by
  rw [mem_normalizedLift_feasibleOn_iff d D a b offset phi weight hg]
  simp [hx]

/-- Inserting the evaluated affine arguments lifts a relaxed feasible point of `d` into
`normalizedLift`. -/
theorem insertHeight_affineArgument_mem_normalizedLift_relaxationOn (d : FiniteModel n m l r)
    (D : Set (Point n m)) (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    {x : Point n m} (hx : x ∈ d.relaxationOn D) :
    insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x) ∈
      (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) := by
  rw [mem_normalizedLift_relaxationOn_iff d D a b offset phi weight hg]
  simp [hx]

/-- **Exact mixed-integer projection for affine-argument normalization.** Normalization is exact
substitution and requires no sign assumption on `weight`. -/
theorem normalization_projection (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    project '' (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) =
      d.feasibleOn D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((mem_normalizedLift_feasibleOn_iff d D a b offset phi weight hg z).1 hz).1
  · intro hx
    exact ⟨insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      insertHeight_affineArgument_mem_normalizedLift_feasibleOn d D a b offset phi weight hg hx,
      project_insertHeight _ _⟩

/-- **Exact continuous-relaxation projection for affine-argument normalization.** -/
theorem normalization_relaxation_projection (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    project '' (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) =
      d.relaxationOn D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((mem_normalizedLift_relaxationOn_iff d D a b offset phi weight hg z).1 hz).1
  · intro hx
    exact ⟨insertHeight x (fun j => affineArgument (a j) (b j) (offset j) x),
      insertHeight_affineArgument_mem_normalizedLift_relaxationOn d D a b offset phi weight hg hx,
      project_insertHeight _ _⟩

/-- **Feasible minimum equivalence for affine-argument normalization (mixed-integer problem).** -/
theorem normalization_minimum_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    (z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ∧
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z) ↔
      z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D) ∧
        project z ∈ d.feasibleOn D ∧ IsMinOn d.objective (d.feasibleOn D) (project z) := by
  have hobj : (d.normalizedLift a b offset phi weight).objective = d.objective ∘ project :=
    funext (normalizedLift_objective d a b offset phi weight)
  rw [hobj, ← normalization_projection d D a b offset phi weight hg, isMinOn_image_iff]
  exact ⟨fun ⟨hz, hmin⟩ => ⟨hz, mem_image_of_mem project hz, hmin⟩, fun ⟨hz, _, hmin⟩ => ⟨hz, hmin⟩⟩

/-- **Attainment equivalence for affine-argument normalization (mixed-integer problem).** -/
theorem normalization_attainment_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    (∃ z ∈ (d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D),
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).feasibleOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.feasibleOn D, IsMinOn d.objective (d.feasibleOn D) x := by
  have hobj : (d.normalizedLift a b offset phi weight).objective = d.objective ∘ project :=
    funext (normalizedLift_objective d a b offset phi weight)
  rw [hobj, ← normalization_projection d D a b offset phi weight hg, exists_mem_image_isMinOn_iff]

/-- **Feasible minimum equivalence for affine-argument normalization (continuous relaxation).** -/
theorem normalization_relaxation_minimum_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x))
    (z : Point (n + q) m) :
    (z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ∧
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D)) z) ↔
      z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D) ∧
        project z ∈ d.relaxationOn D ∧ IsMinOn d.objective (d.relaxationOn D) (project z) := by
  have hobj : (d.normalizedLift a b offset phi weight).objective = d.objective ∘ project :=
    funext (normalizedLift_objective d a b offset phi weight)
  rw [hobj, ← normalization_relaxation_projection d D a b offset phi weight hg, isMinOn_image_iff]
  exact ⟨fun ⟨hz, hmin⟩ => ⟨hz, mem_image_of_mem project hz, hmin⟩, fun ⟨hz, _, hmin⟩ => ⟨hz, hmin⟩⟩

/-- **Attainment equivalence for affine-argument normalization (continuous relaxation).** -/
theorem normalization_relaxation_attainment_iff (d : FiniteModel n m l r) (D : Set (Point n m))
    (a : Fin q → Fin n → ℝ) (b : Fin q → Fin m → ℝ) (offset : Fin q → ℝ)
    (phi : Fin q → ℝ → ℝ) (weight : Fin l → Fin q → ℝ)
    (hg : ∀ i x, d.g i x = ∑ j, weight i j * phi j (affineArgument (a j) (b j) (offset j) x)) :
    (∃ z ∈ (d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D),
      IsMinOn (d.normalizedLift a b offset phi weight).objective
        ((d.normalizedLift a b offset phi weight).relaxationOn (project ⁻¹' D)) z) ↔
      ∃ x ∈ d.relaxationOn D, IsMinOn d.objective (d.relaxationOn D) x := by
  have hobj : (d.normalizedLift a b offset phi weight).objective = d.objective ∘ project :=
    funext (normalizedLift_objective d a b offset phi weight)
  rw [hobj, ← normalization_relaxation_projection d D a b offset phi weight hg,
    exists_mem_image_isMinOn_iff]

end TauCeti.ConvexLifting.FiniteModel
