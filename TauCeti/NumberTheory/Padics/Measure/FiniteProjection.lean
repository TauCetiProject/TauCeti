/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import TauCeti.Topology.ContinuousMap.FiberIndicator
import TauCeti.NumberTheory.Padics.Measure.Topology.Basic

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
    simp [fiberIndicator_apply]
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
  -- The fibre of `t ∘ q` over `b` is the union of the fibres of `q` over the preimage of `b`.
  have hb : fiberIndicator (R := R) (t.comp q) b =
      (ContinuousMap.equivFnOfDiscrete.symm fun a ↦ if t a = b then 1 else 0).comp q := by
    ext x
    simp [fiberIndicator_apply]
  rw [finiteProjection_apply, hb, apply_comp_eq_sum_finiteProjection, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  simp [Finsupp.single_apply]

/-- The sum of all finite coefficients is the total mass of the measure. -/
@[simp]
theorem sum_finiteProjection [Finite A] [DiscreteTopology A]
    (q : C(X, A)) (μ : D(X, R)) :
    (finiteProjection q μ).sum (fun _ r ↦ r) = μ 1 := by
  classical
  let _ := Fintype.ofFinite A
  -- The constant function `1` factors through `q` as the constant coefficient function `1`.
  have h1 : (ContinuousMap.equivFnOfDiscrete.symm fun _ : A ↦ (1 : R)).comp q = 1 := by
    ext x
    simp
  rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl, ← h1, apply_comp_eq_sum_finiteProjection]
  simp

/-- A finitely supported coefficient function on `A` defines the corresponding finite linear
combination of Dirac measures. -/
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
  -- On a discrete space, `f` is the continuous function attached to its own values.
  have hf : (ContinuousMap.equivFnOfDiscrete.symm f).comp (.id A) = f := by
    ext x
    simp
  rw [ofFiniteCoefficients_apply, Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  conv_rhs => rw [← hf, apply_comp_eq_sum_finiteProjection]
  simp_rw [mul_comm]

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
  classical
  -- Locally constant functions are dense, so it suffices to compare `μ` and `ν` on them.
  have hlc (f : LocallyConstant X R) : μ f = ν f := by
    -- `f` factors through its finite range, which is discrete since `R` is Hausdorff.
    have : Finite (Set.range f) := f.range_finite.to_subtype
    let _ := Fintype.ofFinite (Set.range f)
    let q : C(X, Set.range f) := ⟨fun x ↦ ⟨f x, x, rfl⟩, f.continuous.subtype_mk _⟩
    have hf : (f : C(X, R)) = (ContinuousMap.equivFnOfDiscrete.symm Subtype.val).comp q := by
      ext x
      simp [q]
    -- A binary quotient separates each fibre of `q` from its complement.
    have hq : finiteProjection q μ = finiteProjection q ν := by
      ext a
      let t : C(Set.range f, Fin 2) := ContinuousMap.equivFnOfDiscrete.symm
        (fun b ↦ if b = a then 0 else 1)
      have ha : fiberIndicator (R := R) (t.comp q) 0 = fiberIndicator q a := by
        ext x
        simp [t]
      simpa only [finiteProjection_apply, ha] using
        congrArg (fun c : Fin 2 →₀ R ↦ c 0) (h (t.comp q))
    rw [hf, apply_comp_eq_sum_finiteProjection, apply_comp_eq_sum_finiteProjection, hq]
  ext f
  exact congrFun (LocallyConstant.denseRange_toContinuousMap.equalizer μ.continuous ν.continuous
    (funext hlc)) f

end Profinite

end TopologicalRing

section Normed

variable [NormedCommRing R]

/-- Finite projection is weakly continuous when its coefficients carry the product topology. -/
theorem continuous_finiteProjection [Finite A] [DiscreteTopology A] (q : C(X, A)) :
    @Continuous _ _ (WeakTopology (X := X) (R := R) (E := R)) inferInstance
      (fun μ : D(X, R) ↦ fun a ↦ finiteProjection q μ a) := by
  let : TopologicalSpace D(X, R) := WeakTopology
  exact continuous_pi fun a ↦ continuous_apply_weak (fiberIndicator (R := R) q a)

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
