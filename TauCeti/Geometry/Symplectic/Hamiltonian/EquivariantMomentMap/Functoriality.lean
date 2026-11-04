/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Restriction and transport of group-level moment maps

Group-level moment maps are functorial in both the group and the manifold.

**Restriction along a homomorphism.** Let `G` act on `(M, σ)` with moment map `μ : M → 𝔤*`, and
let a Lie group `K` act on `M` through a homomorphism `φ : K →* G`, that is `k • x = φ k • x`.
If `L : 𝔨 → 𝔤` is the derivative of `φ` at the identity, the fundamental vector field of `ξ ∈ 𝔨`
is that of `L ξ` (`TauCeti.fundamentalVectorField_apply_of_smul_eq`), and `L` intertwines the
coadjoint actions (`TauCeti.Lie.coadjointRepresentation_comp_of_hasMFDerivAt`). Hence the
restricted map `x ↦ μ x ∘ L = L^* (μ x)` is a moment map for the action of `K`
(`TauCeti.SmoothTwoForm.IsMomentMap.comp_monoidHom`), its equivariance defect is the restriction of
that of `μ` (`TauCeti.momentDefect_comp_monoidHom`), and it is coadjoint-equivariant when `μ` is
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`). For a Lie subgroup `K ≤ G` acting
by restriction, `φ` is the inclusion and `L^*` is the dual of the inclusion `𝔨 → 𝔤`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`). Restriction to a closed normal
subgroup is the first step of reduction in stages.

**Pullback along an equivariant map.** If `f : N → M` is a smooth `G`-equivariant map, then
`μ ∘ f` is a group-level moment map for the pulled-back form `f^* σ`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback`); its defect is the defect of `μ` along
`f` (`TauCeti.momentDefect_comp`). In particular an equivariant symplectomorphism `f`, for which
`f^* σ = τ`, carries group-level moment maps of `(M, σ)` to those of `(N, τ)`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.comp_monoidHom`: restriction of a moment map along a
  homomorphism of Lie groups.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_monoidHom`: restriction of a group-level
  moment map along a homomorphism of Lie groups.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.comp_subtype`: restriction of a group-level moment
  map to a Lie subgroup.
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

/-- **The defect of a restricted map.** Let `K` act on `M` through a homomorphism `φ : K →* G`
whose derivative at the identity is `L`. The defect of the restriction `x ↦ μ x ∘ L` at `k` is the
restriction of the defect of `μ` at `φ k`. -/
theorem momentDefect_comp_monoidHom {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK]
    [TopologicalSpace HK] {IK : ModelWithCorners 𝕜 EK HK} {K : Type*} [TopologicalSpace K]
    [ChartedSpace HK K] [Group K] [LieGroup IK 1 K] [MulAction K M] {φ : K →* G}
    {L : GroupLieAlgebra IK K →L[𝕜] GroupLieAlgebra I G}
    (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) (hL : HasMFDerivAt IK I φ 1 L) (k : K) (x : M) :
    momentDefect (fun y ↦ (μ y).comp (L : GroupLieAlgebra IK K →ₗ[𝕜] GroupLieAlgebra I G)) k x =
      (momentDefect μ (φ k) x).comp (L : GroupLieAlgebra IK K →ₗ[𝕜] GroupLieAlgebra I G) := by
  rw [momentDefect_def, momentDefect_def, LinearMap.sub_comp, hsmul,
    Lie.coadjointRepresentation_comp_of_hasMFDerivAt hL]

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
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [CompleteSpace EK]
  [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
  [LieGroup IK (minSmoothness ℝ 3) K]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [MulAction K M] [ContMDiffSMul IK I' ∞ K M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {φ : K →* G} {L : GroupLieAlgebra IK K →L[ℝ] GroupLieAlgebra I G}

-- The tangent adjoint maps only need `C¹` Lie groups; `lieGroupOne` lowers the smoothness.
attribute [local instance] lieGroupOne

/-- **Restriction of a moment map along a homomorphism.** Let `K` act on `M` through a homomorphism
`φ : K →* G` whose derivative at the identity is `L : 𝔨 → 𝔤`. If `μ` is a moment map of the
action of `G`, then `x ↦ μ x ∘ L` is a moment map of the action of `K`. -/
theorem IsMomentMap.comp_monoidHom
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) (hL : HasMFDerivAt IK I φ 1 L) :
    σ.IsMomentMap (InfinitesimalAction.fundamental IK K I' M)
      fun x ↦ (μ x).comp (L : GroupLieAlgebra IK K →ₗ[ℝ] GroupLieAlgebra I G) where
  contMDiff ξ := h.contMDiff (L ξ)
  isHamiltonianVectorField ξ := by
    have hξ : InfinitesimalAction.fundamental IK K I' M ξ =
        InfinitesimalAction.fundamental I G I' M (L ξ) := funext fun x ↦ by
      rw [InfinitesimalAction.fundamental_apply, InfinitesimalAction.fundamental_apply,
        fundamentalVectorField_apply_of_smul_eq (hsmul · x) hL
          ((ContMDiffSMul.contMDiff_smul_const (n := 1) x).mdifferentiableAt one_ne_zero)]
    rw [hξ]
    exact h.isHamiltonianVectorField (L ξ)

namespace IsEquivariantMomentMap

/-- **Restriction of a group-level moment map along a homomorphism.** Let `K` act on `M` through
a homomorphism `φ : K →* G` whose derivative at the identity is `L : 𝔨 → 𝔤`. If `μ` is a
group-level moment map of the action of `G`, then `x ↦ μ x ∘ L` is a group-level moment map of
the action of `K`. -/
theorem comp_monoidHom (h : σ.IsEquivariantMomentMap μ)
    (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) (hL : HasMFDerivAt IK I φ 1 L) :
    σ.IsEquivariantMomentMap
      fun x ↦ (μ x).comp (L : GroupLieAlgebra IK K →ₗ[ℝ] GroupLieAlgebra I G) := by
  have hμ := (isEquivariantMomentMap_iff_momentDefect_eq_zero.1 h).2
  refine isEquivariantMomentMap_iff_momentDefect_eq_zero.2
    ⟨h.toIsMomentMap.comp_monoidHom hsmul hL, fun k x ↦ ?_⟩
  rw [momentDefect_comp_monoidHom hsmul hL, hμ, LinearMap.zero_comp]

/-- **Restriction of a group-level moment map to a Lie subgroup.** If a subgroup `K ≤ G`, with its
own Lie group structure, acts on `M` by restriction and the inclusion `K → G` has derivative
`L : 𝔨 → 𝔤` at the identity, then `x ↦ μ x ∘ L` is a group-level moment map of the action of `K`.
-/
theorem comp_subtype {K : Subgroup G} [ChartedSpace HK K] [LieGroup IK (minSmoothness ℝ 3) K]
    [ContMDiffSMul IK I' ∞ K M] {L : GroupLieAlgebra IK K →L[ℝ] GroupLieAlgebra I G}
    (h : σ.IsEquivariantMomentMap μ) (hL : HasMFDerivAt IK I ((↑) : K → G) 1 L) :
    σ.IsEquivariantMomentMap
      fun x ↦ (μ x).comp (L : GroupLieAlgebra IK K →ₗ[ℝ] GroupLieAlgebra I G) :=
  h.comp_monoidHom (φ := K.subtype) (fun _ _ ↦ rfl) hL

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
