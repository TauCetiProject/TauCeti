/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level

/-!
# Isotropic orbits and coisotropic levels of equivariant moment maps

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a real Lie algebra `𝔤` on
a manifold with a nondegenerate two-form `σ`, so that `⟨dμ_x(v), Z⟩ = σ(Z_M x, v)`. At a point `x`
where the cocycle of `μ` vanishes and `μ(x)` is fixed by the coadjoint action, the orbit tangent
space `𝔤 · x` is isotropic and its symplectic complement `ker dμ_x` is coisotropic
(`TauCeti.SmoothTwoForm.IsMomentMap.isIsotropic_orbitTangent_iff` and
`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropic_ker_differential_iff`). This file draws the
dimensional and manifold-level consequences.

An isotropic subspace has at most half the dimension, so at such a point
`2 dim (𝔤 · x) ≤ dim M` (`TauCeti.SmoothTwoForm.IsMomentMap.two_mul_finrank_orbitTangent_le`). If
moreover the action is locally free at `x` (the isotropy algebra `𝔤_x` is trivial), then
`ker dμ_x` is Lagrangian exactly when `2 dim 𝔤 = dim M`, in which case it is the orbit tangent
space (`TauCeti.SmoothTwoForm.IsMomentMap.isLagrangian_ker_differential_iff` and
`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_eq_orbitTangent`).

On the manifold level, read in a basis `b` of `𝔤`, the components `μ_{b_i}` of `μ` form a family of
functions whose regular points are exactly the points where the action is locally free
(`TauCeti.SmoothTwoForm.IsMomentMap.isRegularPoint_iff_isotropy_eq_bot`), and which pairwise
Poisson-commute wherever the cocycle vanishes and `μ(x)` is coadjoint-fixed
(`TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_zero`). So the results on common levels of
Poisson-commuting functions apply: a parametrization of a level `μ = c` of the dimension
`dim M - dim 𝔤`, at whose points the action is locally free and the cocycle of `μ` vanishes, is
a coisotropic map when `c` is coadjoint-fixed
(`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropicMap_of_forall_eq`), and a Lagrangian map when
moreover `2 dim 𝔤 = dim M`
(`TauCeti.SmoothTwoForm.IsMomentMap.isLagrangianMap_of_forall_eq`).

For a group-level moment map of a Lie group action the cocycle vanishes identically
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`). So for a Lie group with an
abelian Lie algebra, such as a torus, every orbit tangent space is isotropic
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isIsotropic_orbitTangent`), the group has at most
half the dimension of `M` if it acts locally freely somewhere
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.two_mul_finrank_le`), and parametrized regular
levels of the moment map are coisotropic, and Lagrangian when `2 dim G = dim M`.

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

/-- A coadjoint-fixed linear functional vanishes on brackets. -/
private theorem apply_lie_eq_zero_of_lieAnnihilator_eq_top {𝔤 : Type*} [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] {ν : Module.Dual ℝ 𝔤} (hν : lieAnnihilator ℝ 𝔤 ν = ⊤) (Z Z' : 𝔤) :
    ν ⁅Z, Z'⁆ = 0 := by
  have := LinearMap.congr_fun ((lieAnnihilator_eq_top_iff ℝ 𝔤).1 hν Z) Z'
  rwa [Module.Dual.lie_apply, LinearMap.zero_apply, neg_eq_zero] at this

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤} {x : M}

/-! ### Dimensions of isotropic orbits -/

variable (hσ : σ.IsNondegenerate)
include hσ

variable [FiniteDimensional ℝ E]

/-- **The dimension bound for isotropic orbits.** At a point where the cocycle of a moment map
vanishes and `μ(x)` is coadjoint-fixed, the orbit tangent space has at most half the dimension
of `M`. -/
theorem two_mul_finrank_orbitTangent_le (h : σ.IsMomentMap a μ) (hc : σ.momentCocycle a μ x = 0)
    (hμ : lieAnnihilator ℝ 𝔤 (μ x) = ⊤) : 2 * finrank ℝ (a.orbitTangent x) ≤ finrank ℝ E := by
  simpa only [finrank_tangentSpace] using
    ((h.isIsotropic_orbitTangent_iff hσ hc).2 hμ).two_mul_finrank_le

/-- **The Lagrangian criterion for `ker dμ_x`.** If the action is locally free at a point where
the cocycle of a moment map vanishes and `μ(x)` is coadjoint-fixed, then `ker dμ_x` is Lagrangian
exactly when `𝔤` has half the dimension of `M`. -/
theorem isLagrangian_ker_differential_iff (h : σ.IsMomentMap a μ)
    (hc : σ.momentCocycle a μ x = 0) (hμ : lieAnnihilator ℝ 𝔤 (μ x) = ⊤)
    (hfree : a.isotropy x = ⊥) :
    (hσ.symplecticFormAt x).IsLagrangian (LinearMap.ker (h.differential x)) ↔
      2 * finrank ℝ 𝔤 = finrank ℝ E := by
  have hker := h.finrank_ker_differential_add_finrank (hσ.nondegenerate_bilinFormAt x) hfree
  refine ⟨fun hL ↦ ?_, fun hdim ↦
    ((h.isCoisotropic_ker_differential_iff hσ hc).2 hμ).isLagrangian_of_finrank ?_⟩
  · have := hL.two_mul_finrank
    rw [finrank_tangentSpace] at this
    omega
  · rw [finrank_tangentSpace]
    omega

/-- **The Lagrangian kernel is the orbit tangent space.** If the action is locally free at a point
where the cocycle of a moment map vanishes, `μ(x)` is coadjoint-fixed, and `𝔤` has half the
dimension of `M`, then `ker dμ_x = 𝔤 · x`. -/
theorem ker_differential_eq_orbitTangent (h : σ.IsMomentMap a μ)
    (hc : σ.momentCocycle a μ x = 0) (hμ : lieAnnihilator ℝ 𝔤 (μ x) = ⊤)
    (hfree : a.isotropy x = ⊥) (hdim : 2 * finrank ℝ 𝔤 = finrank ℝ E) :
    LinearMap.ker (h.differential x) = a.orbitTangent x := by
  have hL := ((isLagrangian_ker_differential_iff hσ h hc hμ hfree).2 hdim).isIsotropic
  rw [SymplecticForm.isIsotropic_iff_le, SymplecticForm.orthogonal_def,
    hσ.toBilinForm_symplecticFormAt,
    h.orthogonal_ker_differential (hσ.nondegenerate_bilinFormAt x)] at hL
  exact le_antisymm hL ((h.orbitTangent_le_ker_differential_iff hc).2 hμ)

omit hσ

/-! ### Components in a basis and parametrized levels -/

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- The components of a moment map in a basis of `𝔤` form a differentiable map to `ι → ℝ`. -/
private theorem mdifferentiableAt_components (h : σ.IsMomentMap a μ) (b : Basis ι ℝ 𝔤) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ι → ℝ) (fun y i ↦ μ y (b i)) x :=
  mdifferentiableAt_pi_space.2 fun i ↦ h.mdifferentiableAt (b i) x

/-- **Regular points of a moment map.** At a point where the form is nondegenerate, the components
`μ_{b_i}` of a moment map in a basis `b` of `𝔤` have a regular point exactly where the action is
locally free. -/
theorem isRegularPoint_iff_isotropy_eq_bot (h : σ.IsMomentMap a μ) (b : Basis ι ℝ 𝔤) {x : M}
    (hσx : (σ.bilinFormAt x).Nondegenerate) :
    IsRegularPoint I 𝓘(ℝ, ι → ℝ) (fun y i ↦ μ y (b i)) x ↔ a.isotropy x = ⊥ := by
  classical
  have hd := h.mdifferentiableAt_components b x
  -- The derivative of the components is the differential read in the dual basis.
  have heq : ⇑(mfderiv I 𝓘(ℝ, ι → ℝ) (fun y i ↦ μ y (b i)) x) =
      ⇑b.dualBasis.equivFun ∘ ⇑(h.differential x) := by
    funext v i
    have := congrArg (fun L ↦ L v) (mvfderiv_apply hd i)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at this
    rw [Function.comp_apply, Basis.dualBasis_equivFun, h.differential_apply, this,
      mvfderiv_apply_eq_mfderiv_apply]
  rw [isRegularPoint_iff, heq]
  exact (EquivLike.comp_surjective _ b.dualBasis.equivFun).trans (h.differential_surjective_iff hσx)

include hσ

/-- **Components of a moment map Poisson-commute** at a point where the cocycle of the moment map
vanishes and `μ(x)` is coadjoint-fixed, for instance everywhere for an infinitesimally
equivariant moment map of an abelian Lie algebra. -/
theorem poissonBracket_eq_zero (h : σ.IsMomentMap a μ) (hc : σ.momentCocycle a μ x = 0)
    (hμ : lieAnnihilator ℝ 𝔤 (μ x) = ⊤) (Z Z' : 𝔤) :
    σ.poissonBracket (fun y ↦ μ y Z) (fun y ↦ μ y Z') x = 0 := by
  rw [h.poissonBracket_eq_eval₂ hσ, momentCocycle_eq_zero_iff.1 hc,
    apply_lie_eq_zero_of_lieAnnihilator_eq_top hμ]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {g : N → M} {c : Module.Dual ℝ 𝔤}

/-- **Regular levels are coisotropic.** Let `g : N → M` map into the level `μ = c` of a moment map,
with injective derivatives, from a manifold of dimension `dim M - dim 𝔤`. If the action is locally
free and the cocycle of `μ` vanishes at every point of the image, and `c` is coadjoint-fixed,
then `g` is a coisotropic map. -/
theorem isCoisotropicMap_of_forall_eq [FiniteDimensional ℝ 𝔤] (h : σ.IsMomentMap a μ)
    (hg : ∀ p, μ (g p) = c) (hfree : ∀ p, a.isotropy (g p) = ⊥)
    (hc : ∀ p, σ.momentCocycle a μ (g p) = 0) (hcμ : lieAnnihilator ℝ 𝔤 c = ⊤)
    (hinj : ∀ p, Function.Injective (mfderiv J I g p))
    (hdim : finrank ℝ E' + finrank ℝ 𝔤 = finrank ℝ E) : hσ.IsCoisotropicMap J g := by
  let b := Module.finBasis ℝ 𝔤
  refine hσ.isCoisotropicMap_of_forall_eq (F := fun y i ↦ μ y (b i)) (c := fun i ↦ c (b i))
    (fun p ↦ by simp only [hg]) (fun p ↦ (h.isRegularPoint_iff_isotropy_eq_bot b
      (hσ.nondegenerate_bilinFormAt _)).2 (hfree p))
    (fun p i j ↦ poissonBracket_eq_zero hσ h (hc p) (by rwa [hg]) (b i) (b j))
    hinj ?_
  rwa [Fintype.card_fin]

/-- **Regular levels of a moment map of half dimension are Lagrangian.** Let `g : N → M` map into
the level `μ = c` of a moment map, with injective derivatives, where `2 dim 𝔤 = dim M` and
`dim N = dim 𝔤`. If the action is locally free and the cocycle of `μ` vanishes at every point of the
image, and `c` is coadjoint-fixed, then `g` is a Lagrangian map. -/
theorem isLagrangianMap_of_forall_eq [FiniteDimensional ℝ 𝔤] (h : σ.IsMomentMap a μ)
    (hg : ∀ p, μ (g p) = c) (hfree : ∀ p, a.isotropy (g p) = ⊥)
    (hc : ∀ p, σ.momentCocycle a μ (g p) = 0) (hcμ : lieAnnihilator ℝ 𝔤 c = ⊤)
    (hinj : ∀ p, Function.Injective (mfderiv J I g p)) (hdimN : finrank ℝ E' = finrank ℝ 𝔤)
    (hdim : 2 * finrank ℝ 𝔤 = finrank ℝ E) : hσ.IsLagrangianMap J g := by
  let b := Module.finBasis ℝ 𝔤
  refine hσ.isLagrangianMap_of_forall_eq (F := fun y i ↦ μ y (b i)) (c := fun i ↦ c (b i))
    (fun p ↦ by simp only [hg]) (fun p ↦ (h.isRegularPoint_iff_isotropy_eq_bot b
      (hσ.nondegenerate_bilinFormAt _)).2 (hfree p))
    (fun p i j ↦ poissonBracket_eq_zero hσ h (hc p) (by rwa [hg]) (b i) (b j))
    hinj ?_ ?_
  · rwa [Fintype.card_fin]
  · rwa [Fintype.card_fin]

end IsMomentMap

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

/-- **The dimension bound for torus actions.** If a Lie group with abelian Lie algebra, such as a
torus, has a group-level moment map and acts locally freely at some point, then it has at most
half the dimension of `M`. -/
theorem two_mul_finrank_le (h : σ.IsEquivariantMomentMap μ) {x : M}
    (hfree : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) :
    2 * finrank ℝ (GroupLieAlgebra I G) ≤ finrank ℝ E' :=
  h.toIsMomentMap.two_mul_finrank_le (hσ.nondegenerate_bilinFormAt x) (h.momentCocycle_eq_zero x)
    hfree

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
