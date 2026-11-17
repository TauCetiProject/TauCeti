/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Pulling back group-level moment maps along equivariant maps

Let a Lie group `G` act on `(M, σ)` with a group-level moment map `μ : M → 𝔤*`. If `f : N → M` is
a smooth `G`-equivariant map, then `μ ∘ f` is a group-level moment map for the pulled-back form
`f^* σ` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback`): an equivariant map sends
fundamental vector fields to fundamental vector fields
(`TauCeti.mfderiv_fundamentalVectorField_of_map_smul`), so the infinitesimal moment map condition
pulls back (`TauCeti.SmoothTwoForm.IsMomentMap.mpullback`), and the defect of `μ ∘ f` is the
defect of `μ` along `f` (`TauCeti.momentDefect_comp`). In particular an equivariant
symplectomorphism `f`, for which `f^* σ = τ`, carries group-level moment maps of `(M, σ)` to those
of `(N, τ)`.

## Main results

* `TauCeti.momentDefect_comp`: the defect of `μ ∘ f` at `(g, y)` is the defect of `μ` at
  `(g, f y)`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback`: pullback of a group-level moment map
  along a smooth equivariant map.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  Chapters 11 and 12 (momentum maps and their equivariance).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

section Defect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I 1 G] {M : Type*} [MulAction G M] {μ : M → Module.Dual 𝕜 (GroupLieAlgebra I G)}

/-- **The defect along an equivariant map.** If `f : N → M` is `G`-equivariant, the defect of
`μ ∘ f` at `(g, y)` is the defect of `μ` at `(g, f y)`. -/
theorem momentDefect_comp {N : Type*} [MulAction G N] {f : N → M}
    (hf : ∀ (g : G) (y : N), f (g • y) = g • f y) (g : G) (y : N) :
    momentDefect (μ ∘ f) g y = momentDefect μ g (f y) := by
  simp only [momentDefect_def, Function.comp_apply, hf]

end Defect

namespace SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

-- The tangent adjoint maps only need `C¹` Lie groups; `lieGroupOne` lowers the smoothness.
attribute [local instance] lieGroupOne

namespace IsEquivariantMomentMap

/-- **Pullback of a group-level moment map along an equivariant map.** If `f : N → M` is a smooth
`G`-equivariant map and `μ` is a group-level moment map for `σ`, then `μ ∘ f` is a group-level
moment map for the pullback `f^* σ`. In particular, an equivariant symplectomorphism carries
group-level moment maps to group-level moment maps. -/
theorem mpullback {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [CompleteSpace EN]
    [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N]
    [ChartedSpace HN N] [IsManifold IN ∞ N] [MulAction G N] [ContMDiffSMul I IN ∞ G N]
    (h : σ.IsEquivariantMomentMap μ) {f : N → M} (hf : ContMDiff IN I' ∞ f)
    (hfg : ∀ (g : G) (y : N), f (g • y) = g • f y) :
    IsEquivariantMomentMap (SmoothForm.mpullback f hf σ) (μ ∘ f) where
  toIsMomentMap := h.toIsMomentMap.mpullback hf fun ξ y ↦ by
    simpa only [InfinitesimalAction.fundamental_apply] using
      mfderiv_fundamentalVectorField_of_map_smul (hf.mdifferentiableAt (by simp))
        ((ContMDiffSMul.contMDiff_smul_const (n := 1) y).mdifferentiableAt one_ne_zero) (hfg · y) ξ
  apply_smul g y := by rw [Function.comp_apply, Function.comp_apply, hfg, h.apply_smul]

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
