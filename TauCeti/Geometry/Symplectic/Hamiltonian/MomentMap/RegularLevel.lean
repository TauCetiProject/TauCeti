/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Involutive
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level

/-!
# Regular levels of moment maps

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a real Lie algebra `𝔤` on
a manifold with a two-form `σ`, so that `⟨dμ_x(v), Z⟩ = σ(Z_M x, v)`. Read in a basis `b` of `𝔤`,
the components `μ_{b_i}` of `μ` form a family of functions. At points where the form is
nondegenerate, the regular points of this family are exactly the points where the action is locally
free (`TauCeti.SmoothTwoForm.IsMomentMap.isRegularPoint_iff_isotropy_eq_bot`). For a nondegenerate
form they pairwise Poisson-commute wherever the cocycle of `μ` vanishes and `μ(x)` is
coadjoint-fixed (`TauCeti.SmoothTwoForm.IsMomentMap.poissonBracket_eq_zero`).

So the results on common levels of Poisson-commuting functions apply: for a nondegenerate form, a
parametrization of a level `μ = c` of the dimension `dim M - dim 𝔤`, at whose points the action is
locally free and the cocycle of `μ` vanishes, is a coisotropic map when `c` is coadjoint-fixed
(`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropicMap_of_forall_eq`), and a Lagrangian map when
moreover `2 dim 𝔤 = dim M`
(`TauCeti.SmoothTwoForm.IsMomentMap.isLagrangianMap_of_forall_eq`).

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin, S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤} {x : M}

variable {ι : Type*} [Fintype ι]

/-- The components of a moment map in a basis of `𝔤` form a differentiable map to `ι → ℝ`. -/
private theorem mdifferentiableAt_components (h : σ.IsMomentMap a μ) (b : Basis ι ℝ 𝔤) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ι → ℝ) (fun y i ↦ μ y (b i)) x :=
  mdifferentiableAt_pi_space.2 fun i ↦ h.mdifferentiableAt (b i) x

variable [FiniteDimensional ℝ E]

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

variable (hσ : σ.IsNondegenerate)
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

end SmoothTwoForm

end TauCeti
