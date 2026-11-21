/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Local coordinates for polynomial equations

Over a complete nontrivially normed field, a square polynomial map with nonzero Jacobian
is a local homeomorphism. Applying this to the map consisting of the parameter coordinates
and the equations gives local coordinates on a polynomial solution space: projection to the
parameters is open wherever the Jacobian in the remaining variables is invertible.

These statements use the coordinate topology and apply in positive characteristic as well.
They supply the local topological step in constructing charts for smooth algebraic varieties.
The inverse function theorem is Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`.
-/

public section

open MvPolynomial Filter Topology

namespace TauCeti

variable {K σ ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]

/-- A square polynomial map with nonzero Jacobian at `a` agrees with an open partial
homeomorphism whose source contains `a`. No characteristic-zero assumption is needed. -/
theorem exists_openPartialHomeomorph_eval_family [Fintype ι] [DecidableEq ι]
    (p : ι → MvPolynomial ι K) (a : ι → K) (ha : (jacobiMatrixAt p a).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ι → K) (ι → K),
      a ∈ e.source ∧ ∀ x, e x = fun i ↦ eval x (p i) := by
  classical
  let f := fun x : ι → K ↦ fun i ↦ eval x (p i)
  have hbij : Function.Bijective (fderiv K f a) := by
    have hm : IsUnit (jacobiMatrixAt p a) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ha)
    have heq : (fderiv K f a : (ι → K) → (ι → K)) = (jacobiMatrixAt p a).mulVec :=
      congrArg (fun L : (ι → K) →ₗ[K] (ι → K) ↦ ⇑L) (fderiv_eval_family p a)
    rw [heq]
    exact ⟨Matrix.mulVec_injective_of_isUnit hm,
      Matrix.mulVec_surjective_iff_isUnit.mpr hm⟩
  let L := ContinuousLinearEquiv.ofBijective (fderiv K f a)
    (LinearMap.ker_eq_bot.mpr hbij.injective) (LinearMap.range_eq_top.mpr hbij.surjective)
  have hf : HasStrictFDerivAt f (L : (ι → K) →L[K] (ι → K)) a :=
    (analyticOnNhd_eval_family p a (Set.mem_univ a)).hasStrictFDerivAt
  exact ⟨hf.toOpenPartialHomeomorph f, hf.mem_toOpenPartialHomeomorph_source,
    fun _ ↦ rfl⟩

section Parameters

variable [Finite σ] [Fintype ι] [DecidableEq ι]

/-- At a point with invertible variable Jacobian, parameters and equations are local coordinates.
The parameter coordinates are unchanged, and the other coordinates are the equation values. -/
theorem exists_openPartialHomeomorph_parameters (p : ι → MvPolynomial (σ ⊕ ι) K)
    (a : σ ⊕ ι → K) (ha : ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (σ ⊕ ι → K) (σ ⊕ ι → K),
      a ∈ e.source ∧ ∀ x, e x = Sum.elim (fun i ↦ x (Sum.inl i)) (fun i ↦ eval x (p i)) := by
  classical
  let := Fintype.ofFinite σ
  -- The supplemented polynomial map has an identity parameter block and a zero upper-right block.
  have hmatrix : jacobiMatrixAt (Sum.elim (fun i : σ ↦ X (Sum.inl i)) p) a =
      Matrix.fromBlocks 1 0 ((jacobiMatrixAt p a).submatrix id Sum.inl)
        ((jacobiMatrixAt p a).submatrix id Sum.inr) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, pderiv_X, Pi.single_apply, apply_ite, eq_comm]
  have hdet : (jacobiMatrixAt (Sum.elim (fun i : σ ↦ X (Sum.inl i)) p) a).det ≠ 0 := by
    simpa only [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul] using ha
  obtain ⟨e, he, hmap⟩ := exists_openPartialHomeomorph_eval_family
    (Sum.elim (fun i : σ ↦ X (Sum.inl i)) p) a hdet
  refine ⟨e, he, fun x ↦ ?_⟩
  rw [hmap]
  ext i
  cases i <;> simp

/-- Projection to the parameters is open on an open part of a polynomial solution space
where the Jacobian in the other variables is invertible. This applies in particular to
principal open subsets of affine varieties. -/
theorem isOpenMap_polynomial_solution_projection (p : ι → MvPolynomial (σ ⊕ ι) K)
    (v : Set (σ ⊕ ι → K)) (hv : IsOpen v)
    (hp : ∀ a ∈ v, (∀ i, eval a (p i) = 0) →
      ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0) :
    IsOpenMap (fun a : {a : σ ⊕ ι → K // a ∈ v ∧ ∀ i, eval a (p i) = 0} ↦
      fun i ↦ a.val (Sum.inl i)) := by
  intro s hs
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨a, has, rfl⟩
  obtain ⟨e, hae, he⟩ := exists_openPartialHomeomorph_parameters p a.val
    (hp a.val a.property.1 a.property.2)
  let j : (σ → K) → (σ ⊕ ι → K) := fun y ↦ Sum.elim y 0
  have hja : j (fun i ↦ a.val (Sum.inl i)) = e a.val := by
    rw [he]
    ext i
    cases i <;> simp [j, a.property.2]
  have hj : Continuous j := continuous_pi fun i ↦ by
    cases i with
    | inl i => exact continuous_apply i
    | inr i => exact continuous_const
  have ht : ∀ᶠ y in 𝓝 (fun i ↦ a.val (Sum.inl i)), j y ∈ e.target := by
    exact hj.continuousAt.preimage_mem_nhds
      (hja ▸ e.open_target.mem_nhds (e.map_source hae))
  have hg : Tendsto (fun y ↦ e.symm (j y)) (𝓝 (fun i ↦ a.val (Sum.inl i))) (𝓝 a.val) := by
    have hj' := hj.continuousAt.tendsto (x := fun i ↦ a.val (Sum.inl i))
    rw [hja] at hj'
    have h := (e.continuousAt_symm (e.map_source hae)).tendsto.comp hj'
    simpa only [Function.comp_def, e.left_inv hae] using h
  obtain ⟨u, hu, hsu⟩ := isOpen_induced_iff.mp hs
  have hmem : a.val ∈ u := by rwa [← hsu] at has
  have hgu : ∀ᶠ y in 𝓝 (fun i ↦ a.val (Sum.inl i)), e.symm (j y) ∈ u ∩ v :=
    hg ((hu.inter hv).mem_nhds ⟨hmem, a.property.1⟩)
  filter_upwards [ht, hgu] with y hy hgy
  have hright := e.right_inv hy
  have hzero : ∀ i, eval (e.symm (j y)) (p i) = 0 := by
    intro i
    simpa [he, j] using congrArg (fun z ↦ z (Sum.inr i)) hright
  refine ⟨⟨e.symm (j y), hgy.2, hzero⟩, ?_, ?_⟩
  · rw [← hsu]
    exact hgy.1
  · ext i
    simpa [he, j] using congrArg (fun z ↦ z (Sum.inl i)) hright

/-- On the locus of solutions where the variable Jacobian is nonsingular, projection to
the parameter coordinates is open. This formulation requires no global smoothness hypothesis. -/
theorem isOpenMap_polynomial_nonsingular_projection (p : ι → MvPolynomial (σ ⊕ ι) K) :
    IsOpenMap (fun a : {a : σ ⊕ ι → K //
      ((jacobiMatrixAt p a).submatrix id Sum.inr).det ≠ 0 ∧ ∀ i, eval a (p i) = 0} ↦
      fun i ↦ a.val (Sum.inl i)) := by
  have hdet : Continuous (fun a : σ ⊕ ι → K ↦
      ((jacobiMatrixAt p a).submatrix id Sum.inr).det) :=
    Continuous.matrix_det (continuous_pi fun i ↦ continuous_pi fun j ↦ by
      simpa only [Matrix.submatrix_apply, id_eq, jacobiMatrixAt_apply] using
        MvPolynomial.continuous_eval (pderiv (Sum.inr j) (p i)))
  exact isOpenMap_polynomial_solution_projection p _ (isOpen_ne_fun hdet continuous_const)
    (fun _ ha _ ↦ ha)

end Parameters

end TauCeti
