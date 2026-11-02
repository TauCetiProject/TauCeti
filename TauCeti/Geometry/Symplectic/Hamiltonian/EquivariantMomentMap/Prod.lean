/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Equivariant moment maps for diagonal product actions

If a Lie group acts on two manifolds with coadjoint-equivariant moment maps `μ` and `ν`,
then its diagonal action on their product has moment map `(x, y) ↦ μ x + ν y` for the product
two-form. The infinitesimal moment-map identity follows from the existing product construction;
coadjoint equivariance follows from linearity of the coadjoint representation.

Neither connectedness of the group nor nondegeneracy of the forms is needed. In particular,
the construction applies to disconnected group actions as well as to symplectic actions.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, §22 (Hamiltonian actions and products).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M] [IsManifold I₁ ∞ M]
  [MulAction G M] [ContMDiffSMul I I₁ ∞ G M]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold I₂ ∞ N]
  [MulAction G N] [ContMDiffSMul I I₂ ∞ G N]
  {σ : SmoothTwoForm I₁ M} {τ : SmoothTwoForm I₂ N}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- The sum of two coadjoint-equivariant moment maps is a coadjoint-equivariant moment map
for the diagonal action on the product, with its product two-form. -/
theorem prod (hμ : σ.IsEquivariantMomentMap μ) (hν : τ.IsEquivariantMomentMap ν) :
    (σ.prod τ).IsEquivariantMomentMap (fun p ↦ μ p.1 + ν p.2) where
  toIsMomentMap := by
    rw [InfinitesimalAction.fundamental_prod]
    exact hμ.toIsMomentMap.prod hν.toIsMomentMap
  apply_smul g p := by
    simp only [Prod.smul_fst, Prod.smul_snd, hμ.apply_smul, hν.apply_smul, map_add]

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
