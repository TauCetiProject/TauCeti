/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
import TauCeti.LinearAlgebra.Charpoly.Dual

/-!
# Eigenvalues of points on comodules

A point `g` of a coalgebra `H` with values in a field `Ω` acts on the scalar extension `Ω ⊗ W`
of every comodule `W` (`TauCeti.Comodule.endOfPoint`). This file compares the eigenvalues of
these actions. Matrix-coefficient morphisms `W → H` intertwine the action on `W` with right
translation on the scalar extension of the regular comodule `H`, so every eigenvalue of `g` on
`W` is an eigenvalue of right translation, and, when `W` is finite-dimensional and `Ω` is
algebraically closed, the matrix coefficients of `W` are sums of generalized eigenvectors of
right translation for eigenvalues of `g` on `W`. Over a Hopf algebra the eigenvalues of points are
nonzero, and the eigenvalues of the inverse point, and of the point on the dual comodule, are the
inverses of the eigenvalues of the point on the comodule.

## Main declarations

* `TauCeti.Comodule.hasEigenvalue_endOfPoint_regular`: an eigenvalue of a point on any comodule is
  an eigenvalue of right translation on the coordinate algebra.
* `TauCeti.Comodule.one_tmul_matrixCoefficient_mem_iSup_maxGenEigenspace`: a matrix coefficient
  of a finite-dimensional comodule is a sum of generalized eigenvectors of right translation, for
  eigenvalues of the point on the comodule.
* `TauCeti.Comodule.ne_zero_of_hasEigenvalue_endOfPoint`: eigenvalues of points are nonzero.
* `TauCeti.Comodule.hasEigenvalue_inv_of_hasEigenvalue_endOfPoint_inv`: the inverse of an
  eigenvalue of the inverse point is an eigenvalue of the point.
* `TauCeti.Comodule.hasEigenvalue_inv_of_hasEigenvalue_endOfPoint_dual`: every eigenvalue of a
  point on the dual comodule is the inverse of an eigenvalue on the comodule.
-/

public section

open TensorProduct WithConv

namespace TauCeti.Comodule

section Coalgebra

variable {k H Ω : Type*} [Field k] [Semiring H] [Algebra k H] [Coalgebra k H] [Field Ω]
  [Algebra k Ω]

/-- **Eigenvalues on a comodule are eigenvalues of right translation.** If a point `g` has the
eigenvalue `ν` on a comodule `W`, then right translation by `g` on the scalar extension of the
coordinate algebra has the eigenvalue `ν`: a matrix-coefficient morphism `W → H` carries an
eigenvector to a nonzero eigenvector. -/
theorem hasEigenvalue_endOfPoint_regular {W : Type*} [AddCommGroup W] [Module k W]
    [Comodule k H W] (g : H →ₐ[k] Ω) {ν : Ω}
    (hν : Module.End.HasEigenvalue (endOfPoint W g) ν) :
    Module.End.HasEigenvalue (endOfPoint H g) ν := by
  obtain ⟨x, hx⟩ := hν.exists_hasEigenvector
  -- Some functional of `W` does not vanish on `x` after scalar extension.
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k W, φ.baseChange Ω x ≠ 0 := by
    by_contra! h
    exact hx.2 (TauCeti.Module.Dual.eq_of_baseChange_eq fun φ ↦ by simp [h φ])
  let c := (matrixCoefficientHom (C := H) φ).toLinearMap.baseChange Ω
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := c x) ⟨?_, fun h0 ↦ hφ ?_⟩
  · rw [Module.End.mem_eigenspace_iff, ← LinearMap.comp_apply,
      ← baseChange_comp_endOfPoint, LinearMap.comp_apply, hx.apply_eq_smul, map_smul]
  · have h0' : (matrixCoefficientHom (C := H) φ).toLinearMap.baseChange Ω x = 0 := h0
    rw [← counit_baseChange_matrixCoefficientHom (C := H) Ω φ x, h0', map_zero, map_zero]

/-- **Matrix coefficients are sums of generalized eigenvectors of right translation.** For a
finite-dimensional comodule `W` and a point `g` with values in an algebraically closed field,
each matrix coefficient of `W` lies in the sum of the generalized eigenspaces of right
translation by `g` for eigenvalues in any set `S` containing the eigenvalues of `g` on `W`. -/
theorem one_tmul_matrixCoefficient_mem_iSup_maxGenEigenspace [IsAlgClosed Ω]
    {W : Type*} [AddCommGroup W] [Module k W] [Comodule k H W] [Module.Finite k W]
    (g : H →ₐ[k] Ω) {S : Set Ω}
    (hS : ∀ μ, Module.End.HasEigenvalue (endOfPoint W g) μ → μ ∈ S)
    (φ : Module.Dual k W) (w : W) :
    (1 : Ω) ⊗ₜ[k] matrixCoefficient (C := H) φ w ∈
      ⨆ μ ∈ S, Module.End.maxGenEigenspace (endOfPoint H g) μ := by
  let c := (matrixCoefficientHom (C := H) φ).toLinearMap.baseChange Ω
  have hc : (1 : Ω) ⊗ₜ[k] matrixCoefficient (C := H) φ w = c (1 ⊗ₜ[k] w) := by
    simp [c]
  have hle : ∀ μ, (Module.End.maxGenEigenspace (endOfPoint W g) μ).map c ≤
      ⨆ μ ∈ S, Module.End.maxGenEigenspace (endOfPoint H g) μ := fun μ ↦ by
    by_cases hμ : Module.End.maxGenEigenspace (endOfPoint W g) μ = ⊥
    · simp [hμ]
    · refine le_trans ?_ (le_biSup _ (hS μ (Module.End.HasUnifEigenvalue.lt zero_lt_one hμ)))
      exact Module.End.map_genEigenspace_le c (baseChange_comp_endOfPoint _ g).symm μ ⊤
  have hmap : (⨆ μ, Module.End.maxGenEigenspace (endOfPoint W g) μ).map c ≤
      ⨆ μ ∈ S, Module.End.maxGenEigenspace (endOfPoint H g) μ := by
    rw [Submodule.map_iSup]
    exact iSup_le hle
  rw [hc]
  refine hmap (Submodule.mem_map_of_mem ?_)
  rw [Module.End.iSup_maxGenEigenspace_eq_top]
  exact Submodule.mem_top

end Coalgebra

section Nonzero

variable {k H Ω : Type*} [CommRing k] [Semiring H] [HopfAlgebra k H] [CommRing Ω] [Algebra k Ω]

/-- The eigenvalues of a point on a comodule are nonzero, since the point acts invertibly. -/
theorem ne_zero_of_hasEigenvalue_endOfPoint {V : Type*} [AddCommGroup V] [Module k V]
    [Comodule k H V] (g : WithConv (H →ₐ[k] Ω)) {μ : Ω}
    (hμ : Module.End.HasEigenvalue (endOfPoint V g.ofConv) μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have := congrArg (endOfPoint V (g⁻¹).ofConv) hx.apply_eq_smul
  rw [zero_smul, map_zero, ← LinearMap.comp_apply, endOfPoint_inv_comp,
    LinearMap.id_apply] at this
  exact hx.2 this

end Nonzero

section Inverse

variable {k H Ω : Type*} [CommRing k] [Semiring H] [HopfAlgebra k H] [Field Ω] [Algebra k Ω]

/-- **Eigenvalues of the inverse point.** If the inverse `g⁻¹` of a point has the eigenvalue `ν`
on a comodule, then `g` has the eigenvalue `ν⁻¹`. -/
theorem hasEigenvalue_inv_of_hasEigenvalue_endOfPoint_inv {V : Type*} [AddCommGroup V]
    [Module k V] [Comodule k H V] (g : WithConv (H →ₐ[k] Ω)) {ν : Ω}
    (hν : Module.End.HasEigenvalue (endOfPoint V (g⁻¹).ofConv) ν) :
    Module.End.HasEigenvalue (endOfPoint V g.ofConv) ν⁻¹ := by
  obtain ⟨z, hz⟩ := hν.exists_hasEigenvector
  have hν0 : ν ≠ 0 := ne_zero_of_hasEigenvalue_endOfPoint g⁻¹ hν
  -- Applying `g` to `g⁻¹ z = ν • z` gives `z = ν • g z`.
  have hgz : z = ν • endOfPoint V g.ofConv z := by
    rw [← map_smul, ← hz.apply_eq_smul, ← LinearMap.comp_apply, endOfPoint_comp_inv,
      LinearMap.id_apply]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := z) ⟨?_, hz.2⟩
  rw [Module.End.mem_eigenspace_iff]
  conv_rhs => rw [hgz]
  rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]

end Inverse

section HopfAlgebra

variable {k H Ω : Type*} [Field k] [Semiring H] [HopfAlgebra k H] [Field Ω] [Algebra k Ω]

attribute [local instance] Comodule.dual

/-- **Eigenvalues on the dual comodule are inverse eigenvalues.** If a point `g` has the
eigenvalue `ν` on the dual of a finite-dimensional comodule `V`, then `ν⁻¹` is an eigenvalue of
`g` on `V`. The action on the dual is adjoint to the action of `g⁻¹` on `V`. -/
theorem hasEigenvalue_inv_of_hasEigenvalue_endOfPoint_dual {V : Type*} [AddCommGroup V] [Module k V]
    [Comodule k H V] [Module.Finite k V] (g : WithConv (H →ₐ[k] Ω)) {ν : Ω}
    (hν : Module.End.HasEigenvalue (endOfPoint (Module.Dual k V) g.ofConv) ν) :
    Module.End.HasEigenvalue (endOfPoint V g.ofConv) ν⁻¹ := by
  obtain ⟨ξ, hξ⟩ := hν.exists_hasEigenvector
  set G := endOfPoint V (g⁻¹).ofConv
  set ψ := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := k) (A := Ω) (M := V) ξ
  -- The functional `ψ` is a `ν`-eigenvector of the transpose of `G`, the action of `g⁻¹`.
  have hψ : G.dualMap ψ = ν • ψ := LinearMap.ext fun z ↦ by
    have := baseChangeEvaluation_dual_endOfPoint (R := k) (H := H) (M := V) g ξ z
    rw [hξ.apply_eq_smul, map_smul, LinearMap.smul_apply] at this
    simp only [ψ, TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply, LinearMap.dualMap_apply,
      LinearMap.smul_apply, G, ← this]
  exact hasEigenvalue_inv_of_hasEigenvalue_endOfPoint_inv g <|
    (Module.End.hasEigenvalue_dualMap_iff G ν).mp <| Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hψ, (LinearEquiv.map_ne_zero_iff _).mpr hξ.2⟩

end HopfAlgebra

end TauCeti.Comodule
