/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SymmetricFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Algebra.Spectrum.Pi

/-!
# Agreement of the finite and continuous functional calculi

On a finite-dimensional complex inner product space, the spectral functional calculus of a
symmetric linear map equals Mathlib's continuous functional calculus of the corresponding bounded
operator. The symbol may be any real function: the spectrum is finite, so its restriction is
continuous. This lets explicit spectral sums and the abstract calculus share the same operator,
in particular when comparing square-root constructions.

The comparison uses Mathlib's `Matrix.toEuclideanCLM`,
`LinearIsometryEquiv.conjStarAlgEquiv`, and `StarAlgHom.map_cfc` to transport the diagonal calculus
through an orthonormal eigenbasis.
-/

public section

open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The finite spectral calculus of a symmetric complex operator agrees with the continuous
functional calculus of its bounded-operator presentation. No continuity hypothesis is needed
because the spectrum is finite. -/
theorem cfc_eq (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    (hT.cfc f).toContinuousLinearMap = _root_.cfc f T.toContinuousLinearMap := by
  classical
  -- Select Mathlib's real calculus explicitly on the finite product of complex scalars.
  let : ContinuousFunctionalCalculus ℝ (Fin (Module.finrank ℂ E) → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let b := hT.eigenvectorBasis rfl
  let δ : (Fin (Module.finrank ℂ E) → ℂ) →⋆ₐ[ℂ]
      Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    { (Matrix.diagonalAlgHom ℂ : (Fin (Module.finrank ℂ E) → ℂ) →ₐ[ℂ]
        Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ) with
      map_star' := by intro x; simp [Matrix.star_eq_conjTranspose] }
  let φ := (b.repr.symm.conjStarAlgEquiv.toStarAlgHom.comp
    Matrix.toEuclideanCLM.toStarAlgHom).comp δ
  let eig : Fin (Module.finrank ℂ E) → ℂ := fun i ↦ algebraMap ℝ ℂ (hT.eigenvalues rfl i)
  have hφ (v : Fin (Module.finrank ℂ E) → ℂ) (i : Fin (Module.finrank ℂ E)) :
      φ v (b i) = v i • b i := by
    apply b.repr.injective
    apply WithLp.ofLp_injective
    ext j
    by_cases hij : i = j <;>
      simp [φ, δ, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, hij]
  have heig : φ eig = T.toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    refine b.toBasis.ext fun i ↦ ?_
    simpa [b, eig, RCLike.algebraMap_eq_ofReal] using
      (hφ eig i).trans (hT.apply_eigenvectorBasis rfl i).symm
  have hspec : (spectrum ℝ eig).Finite := by
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    simpa only [eig, CFC.spectrum_algebraMap_eq] using
      (Set.finite_singleton (hT.eigenvalues rfl i))
  have hsa : IsSelfAdjoint eig := by
    ext i
    simp [eig]
  have hmap := φ.map_cfc f eig (hspec.continuousOn f)
    φ.toAlgHom.toLinearMap.continuous_of_finiteDimensional hsa
    (by
      rw [heig]
      exact T.isSelfAdjoint_toContinuousLinearMap_iff.mpr
        (T.isSymmetric_iff_isSelfAdjoint.mp hT))
  rw [heig] at hmap
  rw [← hmap]
  apply ContinuousLinearMap.coe_injective
  refine b.toBasis.ext fun i ↦ ?_
  rw [OrthonormalBasis.coe_toBasis]
  simp only [ContinuousLinearMap.coe_coe]
  rw [hφ]
  rw [cfc_map_pi (S := ℂ) f eig
    (by rw [← Pi.spectrum_eq]; exact hspec.continuousOn f) hsa
    (fun i ↦ IsSelfAdjoint.algebraMap ℂ (.all _))]
  simp only [eig, cfc_algebraMap]
  simp [b, RCLike.algebraMap_eq_ofReal]

end LinearMap.IsSymmetric
