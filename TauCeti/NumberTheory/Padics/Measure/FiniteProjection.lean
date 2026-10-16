/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Finite projections of abstract measures

An abstract measure can be pushed to a finite discrete quotient by recording its values on the
fibres.  This file constructs that linear projection, proves its functoriality under refinement,
and identifies measures on a finite discrete space with finitely supported coefficient functions.

The construction follows the finite-coefficient description in Rodrigues Jacinto and Williams,
*An introduction to p-adic L-functions*, Sections 3.2--3.3.
-/

public noncomputable section

open ContinuousMap

variable {X A B R : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace R]

namespace ContinuousMap

variable [Zero R] [One R]

/-- The continuous characteristic function of a fibre of a map to a finite discrete space. -/
def fiberIndicator [DiscreteTopology A] (q : C(X, A)) (a : A) : C(X, R) :=
  by
    classical
    exact (ContinuousMap.equivFnOfDiscrete.symm (Pi.single a 1)).comp q

@[simp]
theorem fiberIndicator_apply [DiscreteTopology A] [DecidableEq A]
    (q : C(X, A)) (a : A) (x : X) :
    q.fiberIndicator (R := R) a x = if q x = a then 1 else 0 := by
  classical
  simp [fiberIndicator, Pi.single_apply]

end ContinuousMap

namespace AbstractMeasure

variable [CommRing R] [IsTopologicalRing R]

/-- The finite projection of a measure records its values on all fibres of `q`. -/
def finiteProjection [Finite A] [DiscreteTopology A] (q : C(X, A)) :
    D(X, R) →ₗ[R] A →₀ R :=
  let coefficients : D(X, R) →ₗ[R] (A → R) :=
    { toFun := fun μ a ↦ μ (fiberIndicator q a)
      map_add' := fun μ ν ↦ by ext a; simp
      map_smul' := fun r μ ↦ by ext a; simp }
  (Finsupp.linearEquivFunOnFinite R R A).symm.toLinearMap.comp coefficients

@[simp]
theorem finiteProjection_apply [Finite A] [DiscreteTopology A] (q : C(X, A))
    (μ : D(X, R)) (a : A) :
    finiteProjection q μ a = μ (fiberIndicator q a) := by
  simp [finiteProjection]

/-- Integration of a function factoring through a finite quotient is the corresponding finite
sum against the projected coefficients. -/
theorem apply_comp_eq_sum_finiteProjection [Fintype A] [DiscreteTopology A]
    (q : C(X, A)) (μ : D(X, R)) (g : A → R) :
    μ ((ContinuousMap.equivFnOfDiscrete.symm g).comp q) =
      ∑ a, g a * finiteProjection q μ a := by
  classical
  have hfun : (ContinuousMap.equivFnOfDiscrete.symm g).comp q =
      ∑ a, g a • fiberIndicator (R := R) q a := by
    ext x
    simp [fiberIndicator, Pi.single_apply]
  rw [hfun, map_sum]
  simp [finiteProjection_apply]

/-- The finite projection of a Dirac measure is the point mass at the image of its support. -/
@[simp]
theorem finiteProjection_dirac [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (x : X) :
    finiteProjection q (dirac R x) = Finsupp.single (q x) 1 := by
  classical
  ext a
  simp only [finiteProjection_apply, dirac_apply, fiberIndicator_apply, Finsupp.single_apply]

/-- Finite projection is functorial when one finite quotient refines another. -/
theorem finiteProjection_comp [Finite A] [Finite B] [DiscreteTopology A] [DiscreteTopology B]
    (q : C(X, A)) (t : C(A, B)) (μ : D(X, R)) :
    finiteProjection (t.comp q) μ = (finiteProjection q μ).mapDomain t := by
  classical
  let _ := Fintype.ofFinite A
  ext b
  rw [finiteProjection_apply, Finsupp.mapDomain_apply]
  let g : A → R := fun a ↦ if t a = b then 1 else 0
  calc
    μ (fiberIndicator (t.comp q) b) =
        μ ((ContinuousMap.equivFnOfDiscrete.symm g).comp q) := by
      congr 1
      ext x
      simp [g, fiberIndicator_apply]
    _ = ∑ a, g a * finiteProjection q μ a :=
      apply_comp_eq_sum_finiteProjection q μ g
    _ = (finiteProjection q μ).sum fun a m ↦ Finsupp.single (t a) m b := by
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : t a = b <;> simp [g, h]

/-- The sum of all finite coefficients is the total mass of the measure. -/
@[simp]
theorem sum_finiteProjection [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (μ : D(X, R)) :
    (finiteProjection q μ).sum (fun _ r ↦ r) = μ 1 := by
  classical
  let _ := Fintype.ofFinite A
  calc
    (finiteProjection q μ).sum (fun _ r ↦ r) =
        ∑ a, finiteProjection q μ a := Finsupp.sum_fintype _ _ (fun _ ↦ rfl)
    _ = ∑ a, (1 : R) * finiteProjection q μ a := by simp
    _ = μ ((ContinuousMap.equivFnOfDiscrete.symm (fun _ : A ↦ (1 : R))).comp q) :=
      (apply_comp_eq_sum_finiteProjection q μ (fun _ ↦ 1)).symm
    _ = μ 1 := congrArg μ (by ext x; simp)

/-- A finitely supported coefficient function on a finite discrete space defines the corresponding
finite linear combination of Dirac measures. -/
def ofFiniteCoefficients :
    (A →₀ R) →ₗ[R] D(A, R) :=
  Finsupp.linearCombination R (dirac R)

@[simp]
theorem ofFiniteCoefficients_single (a : A) (r : R) :
    ofFiniteCoefficients (Finsupp.single a r) = r • dirac R a := by
  simp [ofFiniteCoefficients]

/-- Evaluating the measure associated to finite coefficients pairs the coefficients with the
values of the test function. -/
@[simp]
theorem ofFiniteCoefficients_apply (c : A →₀ R) (f : C(A, R)) :
    ofFiniteCoefficients c f = c.sum fun a r ↦ r * f a := by
  classical
  rw [ofFiniteCoefficients, Finsupp.linearCombination_apply,
    Finsupp.sum_apply'' _ _ _ (by rfl) (by intros; rfl)]
  simp only [_root_.smul_apply, dirac_apply, smul_eq_mul]

/-- Finite projection along the identity recovers the coefficients used to build a measure. -/
@[simp]
theorem finiteProjection_id_ofFiniteCoefficients [Finite A] [DiscreteTopology A] (c : A →₀ R) :
    finiteProjection (.id A) (ofFiniteCoefficients c) = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add a r c _ _ ih => simp [ih]

/-- Reconstructing a measure on a finite discrete space from its identity projection returns the
original measure. -/
@[simp]
theorem ofFiniteCoefficients_finiteProjection_id [Finite A] [DiscreteTopology A] (μ : D(A, R)) :
    ofFiniteCoefficients (finiteProjection (.id A) μ) = μ := by
  classical
  let _ := Fintype.ofFinite A
  ext f
  rw [ofFiniteCoefficients_apply,
    Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
  calc
    ∑ i, finiteProjection (.id A) μ i * f i =
        ∑ i, f i * finiteProjection (.id A) μ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _ = μ ((ContinuousMap.equivFnOfDiscrete.symm f).comp (.id A)) :=
      (apply_comp_eq_sum_finiteProjection (.id A) μ f).symm
    _ = μ f := congrArg μ (by ext x; simp)

example :
    finiteProjection (R := ℤ) (ContinuousMap.const (Fin 2) (0 : Fin 1))
        (2 • dirac ℤ (0 : Fin 2) + 3 • dirac ℤ (1 : Fin 2)) 0 = 5 := by
  simp

example :
    finiteProjection (R := ℤ) (ContinuousMap.const (Fin 1) (0 : Fin 2))
        (dirac ℤ (0 : Fin 1)) 1 = 0 := by
  simp

end AbstractMeasure
