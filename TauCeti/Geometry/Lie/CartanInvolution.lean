/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Exponential.Basic
import TauCeti.Algebra.Lie.CartanInvolution.Conjugacy
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula

/-!
# Conjugacy of Cartan involutions on the Lie algebra of a real Lie group

On `LeftInvariantDerivation I G` of a finite-dimensional real Lie group `G`, any two Cartan
involutions `θ` and `θ'` are conjugate by `Ad (lieExp Z)` for some `Z ∈ θ.cartanP`
(`TauCeti.Lie.exists_conj_cartanInvolution`).

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2, Theorem 6.16.
-/

public section

open LieAlgebra
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Conjugacy of Cartan involutions on a real Lie group**: any two Cartan involutions `θ` and
`θ'` of `LeftInvariantDerivation I G` satisfy `θ' (Ad (lieExp Z) Y) = Ad (lieExp Z) (θ Y)` for
some `Z ∈ θ.cartanP`. -/
theorem exists_conj_cartanInvolution
    {θ θ' : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G}
    (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    ∃ Z ∈ θ.cartanP, ∀ Y,
      θ' (Ad (I := I) (lieExp Z) Y) = Ad (I := I) (lieExp Z) (θ Y) := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  have : CompleteSpace (LeftInvariantDerivation I G) := FiniteDimensional.completeSpace ℝ _
  obtain ⟨Z, hZP, φ, hconj, heig⟩ := hθ.exists_mem_cartanP_conj_eq hθ'
  let A : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
    LinearMap.toContinuousLinearMap (ad ℝ (LeftInvariantDerivation I G) Z)
  have hexp_eq : ∀ Y : LeftInvariantDerivation I G, NormedSpace.exp A Y = φ Y := by
    have hle : ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ (LeftInvariantDerivation I G) Z) μ ≤
        LinearMap.eqLocus (NormedSpace.exp A).toLinearMap φ.toLinearEquiv.toLinearMap := by
      refine iSup_le fun μ v hv ↦ ?_
      have hZv : ⁅Z, v⁆ = μ • v := Module.End.mem_eigenspace_iff.mp hv
      have hAv : A v = μ • v := by simp [A, hZv]
      rw [LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.exp_apply_of_apply_eq_smul A hAv, ← Real.exp_eq_exp_ℝ]
      exact (heig μ v hZv).symm
    rw [hθ.iSup_eigenspace_ad_eq_top hZP, top_le_iff] at hle
    exact fun Y ↦ LinearMap.mem_eqLocus.mp (hle.symm ▸ Submodule.mem_top)
  refine ⟨Z, hZP, fun Y ↦ ?_⟩
  rw [LeftInvariantDerivation.Ad_lieExp_apply, LeftInvariantDerivation.Ad_lieExp_apply,
    hexp_eq Y, hexp_eq (θ Y), hconj Y]

end TauCeti.Lie
