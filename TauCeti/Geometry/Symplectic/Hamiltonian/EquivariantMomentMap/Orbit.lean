/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RegularLevel

/-!
# Isotropic orbits and coisotropic levels of equivariant moment maps

Let `μ : M → 𝔤*` be a group-level moment map of a Lie group action on a manifold with a
nondegenerate two-form `σ`. Its cocycle vanishes identically
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`), so the pointwise results of
`TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level` and the parametrized-level results of
`TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RegularLevel` apply at every point where `μ(x)`
is coadjoint-fixed.

For a Lie group with an abelian Lie algebra, such as a torus, every value is coadjoint-fixed. So
every orbit tangent space is isotropic
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isIsotropic_orbitTangent`), the group has at most
half the dimension of `M` if it acts locally freely at a point where the form is nondegenerate
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.two_mul_finrank_le`), and a parametrization of a
level `μ = c` of the dimension `dim M - dim G`, at whose points the action is locally free, is a
coisotropic map (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCoisotropicMap_of_forall_eq`),
and a Lagrangian map when `2 dim G = dim M`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isLagrangianMap_of_forall_eq`).

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lectures 23 and 27 (the differential of a moment map, and isotropy of torus
  orbits).
* V. Guillemin, S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

/-! ### Group-level moment maps of groups with abelian Lie algebra -/

namespace IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [IsLieAbelian (GroupLieAlgebra I G)]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  (hσ : σ.IsNondegenerate)

include hσ

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

omit [FiniteDimensional ℝ E'] in
/-- **Torus orbits are isotropic.** For a group-level moment map of a Lie group with abelian Lie
algebra, such as a torus, every orbit tangent space is isotropic. -/
theorem isIsotropic_orbitTangent (h : σ.IsEquivariantMomentMap μ) (x : M) :
    (hσ.symplecticFormAt x).IsIsotropic
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) :=
  h.toIsMomentMap.isIsotropic_orbitTangent hσ (h.momentCocycle_eq_zero x)

omit hσ in
/-- **The dimension bound for torus actions.** If a Lie group with abelian Lie algebra, such as a
torus, has a group-level moment map and acts locally freely at a point where the form is
nondegenerate, then it has at most half the dimension of `M`. -/
theorem two_mul_finrank_le (h : σ.IsEquivariantMomentMap μ) {x : M}
    (hσx : (σ.bilinFormAt x).Nondegenerate)
    (hfree : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) :
    2 * finrank ℝ (GroupLieAlgebra I G) ≤ finrank ℝ E' :=
  h.toIsMomentMap.two_mul_finrank_le hσx (h.momentCocycle_eq_zero x) hfree

variable {F H'' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'']
  {J : ModelWithCorners ℝ F H''} {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
  {g : N → M} {c : Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Regular levels of torus moment maps are coisotropic.** For a group-level moment map of a Lie
group with abelian Lie algebra, let `g : N → M` map into a level `μ = c`, with injective
derivatives, from a manifold of dimension `dim M - dim G`. If the action is locally free at every
point of the image, then `g` is a coisotropic map. -/
theorem isCoisotropicMap_of_forall_eq (h : σ.IsEquivariantMomentMap μ) (hg : ∀ p, μ (g p) = c)
    (hfree : ∀ p, (InfinitesimalAction.fundamental I G I' M).isotropy (g p) = ⊥)
    (hinj : ∀ p, Function.Injective (mfderiv J I' g p))
    (hdim : finrank ℝ F + finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E') :
    hσ.IsCoisotropicMap J g :=
  h.toIsMomentMap.isCoisotropicMap_of_forall_eq hσ hg hfree (fun _ ↦ h.momentCocycle_eq_zero _)
    (lieAnnihilator_eq_top ℝ _ c) hinj hdim

/-- **Regular levels of toric moment maps are Lagrangian.** For a group-level moment map of a Lie
group with abelian Lie algebra and half the dimension of `M`, such as the torus of a symplectic
toric manifold, let `g : N → M` map into a level `μ = c`, with injective derivatives, from a
manifold of the dimension of `G`. If the action is locally free at every point of the image, then
`g` is a Lagrangian map. -/
theorem isLagrangianMap_of_forall_eq (h : σ.IsEquivariantMomentMap μ) (hg : ∀ p, μ (g p) = c)
    (hfree : ∀ p, (InfinitesimalAction.fundamental I G I' M).isotropy (g p) = ⊥)
    (hinj : ∀ p, Function.Injective (mfderiv J I' g p))
    (hdimN : finrank ℝ F = finrank ℝ (GroupLieAlgebra I G))
    (hdim : 2 * finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E') : hσ.IsLagrangianMap J g :=
  h.toIsMomentMap.isLagrangianMap_of_forall_eq hσ hg hfree (fun _ ↦ h.momentCocycle_eq_zero _)
    (lieAnnihilator_eq_top ℝ _ c) hinj hdimN hdim

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
