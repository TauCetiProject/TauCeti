/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.LinearAlgebra.Finsupp.Pi

import Mathlib.Topology.Separation.DisjointCover

/-!
# Finite projections of abstract measures

An abstract measure can be pushed to a finite discrete quotient by recording its values on the
fibres.  This file constructs that linear projection, proves its functoriality under refinement,
identifies measures on a finite discrete space with finitely supported coefficient functions, and
proves that binary projections already determine a measure on a profinite space.

The construction follows the finite-coefficient description in Rodrigues Jacinto and Williams,
*An introduction to p-adic L-functions*, Sections 3.2--3.3.
-/

public noncomputable section

open ContinuousMap

variable {X A B R : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

namespace ContinuousMap

variable [TopologicalSpace R] [Zero R] [One R]

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

/-- The fibre indicators of `q` pull back to the fibre indicators of `q ∘ φ`. -/
@[simp]
theorem fiberIndicator_comp [DiscreteTopology A] (q : C(X, A)) (φ : C(B, X)) (a : A) :
    (q.fiberIndicator (R := R) a).comp φ = (q.comp φ).fiberIndicator a := by
  classical
  ext x
  simp

/-- The indicator of an empty fibre vanishes. -/
theorem fiberIndicator_eq_zero_of_notMem_range [DiscreteTopology A] {q : C(X, A)} {a : A}
    (ha : a ∉ Set.range q) : q.fiberIndicator (R := R) a = 0 := by
  classical
  ext x
  have hx : q x ≠ a := fun h ↦ ha ⟨x, h⟩
  simp [fiberIndicator_apply, hx]

end ContinuousMap

namespace AbstractMeasure

section TopologicalRing

variable [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]

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

/-- A fibre of `q` that is empty carries no mass. -/
theorem finiteProjection_apply_of_notMem_range [Finite A] [DiscreteTopology A] {q : C(X, A)}
    (μ : D(X, R)) {a : A} (ha : a ∉ Set.range q) : finiteProjection q μ a = 0 := by
  rw [finiteProjection_apply, fiberIndicator_eq_zero_of_notMem_range ha, map_zero]

/-- The finite projection of a pushforward is the finite projection along the composite. -/
@[simp]
theorem finiteProjection_map [Finite A] [DiscreteTopology A] (φ : C(B, X)) (q : C(X, A))
    (μ : D(B, R)) : finiteProjection q (map φ μ) = finiteProjection (q.comp φ) μ := by
  ext a
  simp

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

/-- Measures on a finite discrete space are equivalent to their coefficient functions. -/
def finiteProjectionEquiv [Finite A] [DiscreteTopology A] :
    D(A, R) ≃ₗ[R] A →₀ R :=
  { finiteProjection (.id A) with
    invFun := ofFiniteCoefficients
    left_inv := ofFiniteCoefficients_finiteProjection_id
    right_inv := finiteProjection_id_ofFiniteCoefficients }

@[simp]
theorem finiteProjectionEquiv_apply [Finite A] [DiscreteTopology A] (μ : D(A, R)) :
    finiteProjectionEquiv μ = finiteProjection (.id A) μ := (rfl)

@[simp]
theorem finiteProjectionEquiv_symm_apply [Finite A] [DiscreteTopology A] (c : A →₀ R) :
    finiteProjectionEquiv.symm c = ofFiniteCoefficients c := (rfl)

section Profinite

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [T2Space R]

/-- A measure on a profinite space is determined by its projections to binary discrete
quotients. -/
theorem finiteProjection_ext (μ ν : D(X, R))
    (h : ∀ q : C(X, Fin 2), finiteProjection q μ = finiteProjection q ν) :
    μ = ν := by
  -- A binary quotient detects each fibre of an arbitrary finite quotient.
  have hfinite (n : ℕ) (q : C(X, Fin n)) : finiteProjection q μ = finiteProjection q ν := by
    classical
    ext a
    let t : C(Fin n, Fin 2) := ContinuousMap.equivFnOfDiscrete.symm
      (fun b ↦ if b = a then 0 else 1)
    have ha : fiberIndicator (R := R) (t.comp q) 0 = fiberIndicator q a := by
      ext x
      simp [t]
    simpa only [finiteProjection_apply, ha] using
      congrArg (fun c : Fin 2 →₀ R ↦ c 0) (h (t.comp q))
  -- The density argument only needs the canonical uniformity of the additive group of `R`.
  let := IsTopologicalAddGroup.rightUniformSpace R
  let S : Set C(X, R) := {f | ∃ (n : ℕ) (q : C(X, Fin n)) (g : Fin n → R),
    f = (ContinuousMap.equivFnOfDiscrete.symm g).comp q}
  have hS : Dense S := by
    intro f
    refine (mem_closure_iff_nhds_basis
      (nhds_basis_uniformity'
        ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact)).mpr
      fun V hV ↦ ?_
    obtain ⟨n, q, g, hq, hfg⟩ :=
      ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal f
        (nhdsSet_diagonal_le_uniformity hV)
    let q' : C(X, Fin n) := ⟨q, hq⟩
    let f' : C(X, R) := (ContinuousMap.equivFnOfDiscrete.symm g).comp q'
    exact ⟨f', ⟨n, q', g, rfl⟩, fun x ↦ hfg x⟩
  have hEqOn : Set.EqOn μ ν S := by
    rintro _ ⟨n, q, g, rfl⟩
    rw [apply_comp_eq_sum_finiteProjection, apply_comp_eq_sum_finiteProjection, hfinite n q]
  apply AbstractMeasure.ext
  intro f
  exact congrFun (Continuous.ext_on hS μ.continuous ν.continuous hEqOn) f

end Profinite

end TopologicalRing

section Normed

variable [NormedCommRing R]

/-- Finite projection is weakly continuous when its coefficients carry the product topology. -/
theorem continuous_finiteProjection [Finite A] [DiscreteTopology A] (q : C(X, A)) :
    @Continuous _ _ (WeakTopology (X := X) (R := R) (E := R)) inferInstance
      (fun μ : D(X, R) ↦ fun a ↦ finiteProjection q μ a) := by
  let : TopologicalSpace D(X, R) := WeakTopology
  have heval : Continuous (fun μ : D(X, R) ↦ fun f : C(X, R) ↦ μ f) :=
    continuous_induced_dom
  exact continuous_pi fun a ↦
    (continuous_apply (fiberIndicator (R := R) q a)).comp heval

end Normed

example :
    finiteProjection (R := ℤ) (ContinuousMap.const (Fin 2) (0 : Fin 1))
        (2 • dirac ℤ (0 : Fin 2) + 3 • dirac ℤ (1 : Fin 2)) 0 = 5 := by
  simp

example :
    finiteProjection (R := ℤ) (ContinuousMap.const (Fin 1) (0 : Fin 2))
        (dirac ℤ (0 : Fin 1)) 1 = 0 := by
  simp

end AbstractMeasure
