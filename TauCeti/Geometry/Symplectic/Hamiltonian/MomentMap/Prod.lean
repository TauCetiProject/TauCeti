/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Manifold.Prod

import TauCeti.Geometry.Manifold.MFDeriv.Graph

/-!
# Moment maps of products

Let `μ₁ : M₁ → 𝔤₁*` and `μ₂ : M₂ → 𝔤₂*` be moment maps of infinitesimal actions `a₁` of `𝔤₁` on
`(M₁, σ₁)` and `a₂` of `𝔤₂` on `(M₂, σ₂)`. The product Lie algebra `𝔤₁ × 𝔤₂` acts on `M₁ × M₂`
componentwise, `(Z₁, Z₂) ↦ (Z₁_{M₁}, Z₂_{M₂})` (`TauCeti.InfinitesimalAction.prodMap`). Its
moment map for the product form `σ₁.prod σ₂ = pr₁^* σ₁ + pr₂^* σ₂` is

`μ(x₁, x₂)(Z₁, Z₂) = μ₁(x₁)(Z₁) + μ₂(x₂)(Z₂)`

(`TauCeti.SmoothTwoForm.IsMomentMap.prodMap`), the functional `μ₁(x₁).coprod μ₂(x₂)` on
`𝔤₁ × 𝔤₂`. Its cocycle is the sum of the cocycles of the factors
(`TauCeti.SmoothTwoForm.momentCocycle_prodMap`; for the diagonal action of a single Lie algebra,
`TauCeti.SmoothTwoForm.momentCocycle_prod`), so it vanishes exactly where both cocycles vanish
(`TauCeti.SmoothTwoForm.momentCocycle_prodMap_eq_zero_iff`). Its differential is componentwise
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_prodMap_apply`), so the tangent spaces `ker dμ`
of its levels are the products of those of the factors
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_prodMap`).

The hypotheses on level data of
`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback` pass to
products. For maps `i_k : Z_k → M_k`, the tangent images of `i₁ × i₂` lie in, or are equal to,
`ker dμ` exactly when those of `i₁` and `i₂` lie in, or are equal to, `ker dμ₁` and `ker dμ₂`
(`TauCeti.SmoothTwoForm.IsMomentMap.range_mfderiv_prodMap_le_ker_differential_prodMap_iff`,
`TauCeti.SmoothTwoForm.IsMomentMap.range_mfderiv_prodMap_eq_ker_differential_prodMap_iff`). For
maps `p_k : Z_k → Q_k` and subspaces `S_k ⊆ 𝔤_k`, the vertical vectors of `p₁ × p₂` are sent by
`d(i₁ × i₂)` into the orbit directions `(S₁ × S₂) · (i₁ × i₂)(z)` exactly when the same holds for
both factors (`TauCeti.InfinitesimalAction.ker_mfderiv_prodMap_le_comap_map_eval_prodMap_iff`,
`TauCeti.InfinitesimalAction.ker_mfderiv_prodMap_eq_comap_map_eval_prodMap_iff`). The reduced
symplectic form of a product of level data is
`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_prodMap_eq_mpullback_prodMap`
in `TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.prodMap`: the moment map of the componentwise action of
  `𝔤₁ × 𝔤₂` on `M₁ × M₂`.
* `TauCeti.SmoothTwoForm.momentCocycle_prodMap`: the cocycle of the product is the sum of the
  cocycles of the factors.
* `TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_prodMap`: `ker dμ = ker dμ₁ × ker dμ₂`.
* `TauCeti.SmoothTwoForm.IsMomentMap.range_mfderiv_prodMap_eq_ker_differential_prodMap_iff` and
  `TauCeti.InfinitesimalAction.ker_mfderiv_prodMap_eq_comap_map_eval_prodMap_iff`: the tangent and
  vertical conditions on level data hold for a product exactly when they hold for both factors.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lectures 22–23 (moment maps of products and reduction).
* J. Marsden, T. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer, 1999,
  Section 11.2 (momentum maps of product actions).
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁]
  [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂]
  [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁] [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
  {EZ₁ HZ₁ Z₁ : Type*} [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
  {J₁ : ModelWithCorners ℝ EZ₁ HZ₁} [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁]
  {EZ₂ HZ₂ Z₂ : Type*} [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
  {J₂ : ModelWithCorners ℝ EZ₂ HZ₂} [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂]
  {i₁ : Z₁ → M₁} {i₂ : Z₂ → M₂}

namespace SmoothTwoForm

/-- **The cocycle of a diagonal action.** The cocycle of the moment map `μ(x) + ν(y)` of the
diagonal action of `𝔤` on `M × N` for the product form is the sum of the cocycles of `μ` at `x` and
of `ν` at `y`. -/
theorem momentCocycle_prod (σ₁ : SmoothTwoForm I₁ M₁) (σ₂ : SmoothTwoForm I₂ M₂)
    (a : InfinitesimalAction 𝔤₁ I₁ M₁) (b : InfinitesimalAction 𝔤₁ I₂ M₂)
    (μ : M₁ → Module.Dual ℝ 𝔤₁) (ν : M₂ → Module.Dual ℝ 𝔤₁) (p : M₁ × M₂) :
    (σ₁.prod σ₂).momentCocycle (a.prod b) (fun q ↦ μ q.1 + ν q.2) p =
      σ₁.momentCocycle a μ p.1 + σ₂.momentCocycle b ν p.2 := by
  refine DFunLike.ext _ _ fun Z ↦ LinearMap.ext fun Z' ↦ ?_
  simp only [momentCocycle_apply, LieModule.Cohomology.add_apply_apply, eval₂_prod,
    InfinitesimalAction.prod_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
    LinearMap.add_apply]
  rw [← map_add]
  congr 1
  ring

/-- **The cocycle of a product.** The cocycle of the moment map `μ₁(x₁).coprod μ₂(x₂)` of the
componentwise action of `𝔤₁ × 𝔤₂` on `M₁ × M₂` is the sum of the cocycles of `μ₁` at `x₁` and of
`μ₂` at `x₂` on the components. -/
theorem momentCocycle_prodMap (σ₁ : SmoothTwoForm I₁ M₁) (σ₂ : SmoothTwoForm I₂ M₂)
    (a₁ : InfinitesimalAction 𝔤₁ I₁ M₁) (a₂ : InfinitesimalAction 𝔤₂ I₂ M₂)
    (μ₁ : M₁ → Module.Dual ℝ 𝔤₁) (μ₂ : M₂ → Module.Dual ℝ 𝔤₂) (p : M₁ × M₂) (Z Z' : 𝔤₁ × 𝔤₂) :
    TrivialLieModule.equiv ℝ (𝔤₁ × 𝔤₂) ℝ
        ((σ₁.prod σ₂).momentCocycle (a₁.prodMap a₂) (fun q ↦ (μ₁ q.1).coprod (μ₂ q.2)) p Z Z') =
      TrivialLieModule.equiv ℝ 𝔤₁ ℝ (σ₁.momentCocycle a₁ μ₁ p.1 Z.1 Z'.1) +
        TrivialLieModule.equiv ℝ 𝔤₂ ℝ (σ₂.momentCocycle a₂ μ₂ p.2 Z.2 Z'.2) := by
  simp only [momentCocycle_apply, LinearEquiv.apply_symm_apply, eval₂_prod,
    InfinitesimalAction.prodMap_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
    LieAlgebra.Prod.bracket_apply, LinearMap.coprod_apply]
  ring

variable {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂}
  {a₁ : InfinitesimalAction 𝔤₁ I₁ M₁} {a₂ : InfinitesimalAction 𝔤₂ I₂ M₂}
  {μ₁ : M₁ → Module.Dual ℝ 𝔤₁} {μ₂ : M₂ → Module.Dual ℝ 𝔤₂}

/-- The cocycle of the moment map `μ₁(x₁).coprod μ₂(x₂)` of the componentwise action vanishes at
`(x₁, x₂)` exactly when the cocycles of `μ₁` at `x₁` and of `μ₂` at `x₂` vanish. -/
@[simp]
theorem momentCocycle_prodMap_eq_zero_iff (p : M₁ × M₂) :
    (σ₁.prod σ₂).momentCocycle (a₁.prodMap a₂) (fun q ↦ (μ₁ q.1).coprod (μ₂ q.2)) p = 0 ↔
      σ₁.momentCocycle a₁ μ₁ p.1 = 0 ∧ σ₂.momentCocycle a₂ μ₂ p.2 = 0 := by
  simp only [momentCocycle_eq_zero_iff, InfinitesimalAction.prodMap_apply, eval₂_prod,
    Manifold.tangentSpaceProdEquiv_prodVectorField, Prod.forall, LieAlgebra.Prod.bracket_apply,
    LinearMap.coprod_apply]
  refine ⟨fun h ↦ ⟨fun Z Z' ↦ ?_, fun Z Z' ↦ ?_⟩, fun h Z₁ Z₂ Z₁' Z₂' ↦ by rw [h.1, h.2]⟩
  · simpa using h Z 0 Z' 0
  · simpa using h 0 Z 0 Z'

namespace IsMomentMap

/-- **Moment maps of products.** If `μ₁` and `μ₂` are moment maps of infinitesimal actions of
`𝔤₁` on `(M₁, σ₁)` and of `𝔤₂` on `(M₂, σ₂)`, then `(x₁, x₂) ↦ μ₁(x₁).coprod μ₂(x₂)`, that is
`(Z₁, Z₂) ↦ μ₁(x₁)(Z₁) + μ₂(x₂)(Z₂)`, is a moment map of the componentwise action of `𝔤₁ × 𝔤₂`
on `M₁ × M₂` for the product form. -/
theorem prodMap (h₁ : σ₁.IsMomentMap a₁ μ₁) (h₂ : σ₂.IsMomentMap a₂ μ₂) :
    (σ₁.prod σ₂).IsMomentMap (a₁.prodMap a₂) fun p ↦ (μ₁ p.1).coprod (μ₂ p.2) := by
  rw [InfinitesimalAction.prodMap_def]
  exact (h₁.comp (LieHom.fst ℝ 𝔤₁ 𝔤₂)).prod (h₂.comp (LieHom.snd ℝ 𝔤₁ 𝔤₂))

/-- The differential of the moment map of a product is componentwise:
`dμ_(x₁, x₂)(v₁, v₂) = (dμ₁)_{x₁}(v₁).coprod (dμ₂)_{x₂}(v₂)`. -/
@[simp]
theorem differential_prodMap_apply (h₁ : σ₁.IsMomentMap a₁ μ₁) (h₂ : σ₂.IsMomentMap a₂ μ₂)
    (p : M₁ × M₂) (v : TangentSpace (I₁.prod I₂) p) :
    (h₁.prodMap h₂).differential p v =
      (h₁.differential p.1 (Manifold.tangentSpaceProdEquiv p v).1).coprod
        (h₂.differential p.2 (Manifold.tangentSpaceProdEquiv p v).2) := by
  refine LinearMap.ext fun Z ↦ ?_
  simp only [differential_apply_eq_eval₂, LinearMap.coprod_apply, eval₂_prod,
    InfinitesimalAction.prodMap_apply, Manifold.tangentSpaceProdEquiv_prodVectorField]

/-- **The tangent spaces of a level of a product.** The kernel of the differential of the moment
map of a product at `(x₁, x₂)` is `ker (dμ₁)_{x₁} × ker (dμ₂)_{x₂}`. -/
theorem ker_differential_prodMap (h₁ : σ₁.IsMomentMap a₁ μ₁) (h₂ : σ₂.IsMomentMap a₂ μ₂)
    (p : M₁ × M₂) :
    LinearMap.ker ((h₁.prodMap h₂).differential p) =
      ((LinearMap.ker (h₁.differential p.1)).prod (LinearMap.ker (h₂.differential p.2))).comap
        (Manifold.tangentSpaceProdEquiv p).toLinearMap := by
  ext v
  rw [LinearMap.mem_ker, differential_prodMap_apply h₁ h₂, Submodule.mem_comap,
    Submodule.mem_prod, LinearMap.mem_ker, LinearMap.mem_ker]
  -- A functional `f.coprod g` on `𝔤₁ × 𝔤₂` vanishes exactly when `f` and `g` do.
  simpa only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearMap.coprodEquiv_apply, Prod.mk_eq_zero] using
    (LinearMap.coprodEquiv ℝ).map_eq_zero_iff (x := (h₁.differential p.1 _, h₂.differential p.2 _))

/-- **Products of maps into levels.** The tangent images of `i₁ × i₂` at `(z₁, z₂)` lie in the
kernel of the differential of the moment map of the product exactly when the tangent images of
`i₁` at `z₁` and of `i₂` at `z₂` lie in the kernels of the differentials of `μ₁` and `μ₂`. -/
theorem range_mfderiv_prodMap_le_ker_differential_prodMap_iff (h₁ : σ₁.IsMomentMap a₁ μ₁)
    (h₂ : σ₂.IsMomentMap a₂ μ₂) {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2) :
    LinearMap.range (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap ≤
        LinearMap.ker ((h₁.prodMap h₂).differential (Prod.map i₁ i₂ z)) ↔
      LinearMap.range (mfderiv J₁ I₁ i₁ z.1).toLinearMap ≤
          LinearMap.ker (h₁.differential (i₁ z.1)) ∧
        LinearMap.range (mfderiv J₂ I₂ i₂ z.2).toLinearMap ≤
          LinearMap.ker (h₂.differential (i₂ z.2)) := by
  rw [← Submodule.comap_map_eq_of_injective
    (Manifold.tangentSpaceProdEquiv (Prod.map i₁ i₂ z)).injective (LinearMap.range _),
    Manifold.map_range_mfderiv_prodMap hi₁ hi₂, ker_differential_prodMap h₁ h₂,
    Submodule.comap_le_comap_iff_of_surjective
    (Manifold.tangentSpaceProdEquiv (Prod.map i₁ i₂ z)).surjective]
  exact ⟨fun h ↦ ⟨by simpa using Submodule.comap_mono (f := LinearMap.inl ℝ _ _) h,
    by simpa using Submodule.comap_mono (f := LinearMap.inr ℝ _ _) h⟩,
    fun h ↦ Submodule.prod_mono h.1 h.2⟩

/-- **The product of levels is a level of the product.** The tangent images of `i₁ × i₂` at
`(z₁, z₂)` are the kernel of the differential of the moment map of the product exactly when the
tangent images of `i₁` at `z₁` and of `i₂` at `z₂` are the kernels of the differentials of `μ₁`
and `μ₂`. -/
theorem range_mfderiv_prodMap_eq_ker_differential_prodMap_iff (h₁ : σ₁.IsMomentMap a₁ μ₁)
    (h₂ : σ₂.IsMomentMap a₂ μ₂) {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2) :
    LinearMap.range (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap =
        LinearMap.ker ((h₁.prodMap h₂).differential (Prod.map i₁ i₂ z)) ↔
      LinearMap.range (mfderiv J₁ I₁ i₁ z.1).toLinearMap =
          LinearMap.ker (h₁.differential (i₁ z.1)) ∧
        LinearMap.range (mfderiv J₂ I₂ i₂ z.2).toLinearMap =
          LinearMap.ker (h₂.differential (i₂ z.2)) := by
  rw [← Submodule.comap_map_eq_of_injective
    (Manifold.tangentSpaceProdEquiv (Prod.map i₁ i₂ z)).injective (LinearMap.range _),
    Manifold.map_range_mfderiv_prodMap hi₁ hi₂, ker_differential_prodMap h₁ h₂,
    (Submodule.comap_injective_of_surjective
    (Manifold.tangentSpaceProdEquiv (Prod.map i₁ i₂ z)).surjective).eq_iff]
  exact ⟨fun h ↦ ⟨by simpa using congrArg (Submodule.comap (LinearMap.inl ℝ _ _)) h,
    by simpa using congrArg (Submodule.comap (LinearMap.inr ℝ _ _)) h⟩,
    fun h ↦ h.1 ▸ h.2 ▸ rfl⟩

end IsMomentMap

end SmoothTwoForm

namespace InfinitesimalAction

variable {EQ₁ HQ₁ Q₁ : Type*} [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [TopologicalSpace HQ₁]
  {JQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
  {EQ₂ HQ₂ Q₂ : Type*} [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [TopologicalSpace HQ₂]
  {JQ₂ : ModelWithCorners ℝ EQ₂ HQ₂} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂]
  {p₁ : Z₁ → Q₁} {p₂ : Z₂ → Q₂}

/-- The tangent vectors at `(z₁, z₂)` sent by `d(i₁ × i₂)` into the image of `S₁ × S₂` under the
orbit map of the componentwise action are, read in the product tangent spaces, the products of
those sent by `di₁` and `di₂` into the images of `S₁` and `S₂`. -/
theorem comap_mfderiv_prodMap_map_eval_prodMap (a₁ : InfinitesimalAction 𝔤₁ I₁ M₁)
    (a₂ : InfinitesimalAction 𝔤₂ I₂ M₂) (S₁ : Submodule ℝ 𝔤₁) (S₂ : Submodule ℝ 𝔤₂)
    {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2) :
    ((S₁.prod S₂).map ((a₁.prodMap a₂).eval (Prod.map i₁ i₂ z))).comap
        (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap =
      (((S₁.map (a₁.eval (i₁ z.1))).comap (mfderiv J₁ I₁ i₁ z.1).toLinearMap).prod
        ((S₂.map (a₂.eval (i₂ z.2))).comap (mfderiv J₂ I₂ i₂ z.2).toLinearMap)).comap
        (Manifold.tangentSpaceProdEquiv z).toLinearMap := by
  rw [map_eval_prodMap, Prod.map_fst, Prod.map_snd, ← Submodule.comap_comp,
    ← LinearMap.prodMap_comap_prod, ← Submodule.comap_comp]
  congr 1
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ := (Manifold.tangentSpaceProdEquiv z).symm.surjective v
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    Manifold.mfderiv_prodMap_apply hi₁ hi₂, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply,
    LinearMap.prodMap_apply]
  -- `Prod.map i₁ i₂ z` is `(i₁ z.1, i₂ z.2)` by definition.
  exact (Manifold.tangentSpaceProdEquiv (Prod.map i₁ i₂ z)).apply_symm_apply _

/-- **Vertical directions of products.** The vertical tangent vectors of `p₁ × p₂` at `(z₁, z₂)`
are sent by `d(i₁ × i₂)` into the orbit directions `(S₁ × S₂) · (i₁ × i₂)(z₁, z₂)` of the
componentwise action exactly when the vertical vectors of `p₁` at `z₁` and of `p₂` at `z₂` are sent
by `di₁` and `di₂` into `S₁ · i₁(z₁)` and `S₂ · i₂(z₂)`. -/
theorem ker_mfderiv_prodMap_le_comap_map_eval_prodMap_iff (a₁ : InfinitesimalAction 𝔤₁ I₁ M₁)
    (a₂ : InfinitesimalAction 𝔤₂ I₂ M₂) (S₁ : Submodule ℝ 𝔤₁) (S₂ : Submodule ℝ 𝔤₂)
    {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1) (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2)
    (hp₁ : MDifferentiableAt J₁ JQ₁ p₁ z.1) (hp₂ : MDifferentiableAt J₂ JQ₂ p₂ z.2) :
    (mfderiv (J₁.prod J₂) (JQ₁.prod JQ₂) (Prod.map p₁ p₂) z).ker ≤
        ((S₁.prod S₂).map ((a₁.prodMap a₂).eval (Prod.map i₁ i₂ z))).comap
          (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap ↔
      (mfderiv J₁ JQ₁ p₁ z.1).ker ≤
          (S₁.map (a₁.eval (i₁ z.1))).comap (mfderiv J₁ I₁ i₁ z.1).toLinearMap ∧
        (mfderiv J₂ JQ₂ p₂ z.2).ker ≤
          (S₂.map (a₂.eval (i₂ z.2))).comap (mfderiv J₂ I₂ i₂ z.2).toLinearMap := by
  rw [Manifold.ker_mfderiv_prodMap hp₁ hp₂,
    comap_mfderiv_prodMap_map_eval_prodMap a₁ a₂ S₁ S₂ hi₁ hi₂,
    Submodule.comap_le_comap_iff_of_surjective (Manifold.tangentSpaceProdEquiv z).surjective]
  exact ⟨fun h ↦ ⟨by simpa using Submodule.comap_mono (f := LinearMap.inl ℝ _ _) h,
    by simpa using Submodule.comap_mono (f := LinearMap.inr ℝ _ _) h⟩,
    fun h ↦ Submodule.prod_mono h.1 h.2⟩

/-- **The vertical directions of a product of reduction data.** The vertical tangent vectors of
`p₁ × p₂` at `(z₁, z₂)` are exactly those sent by `d(i₁ × i₂)` into the orbit directions
`(S₁ × S₂) · (i₁ × i₂)(z₁, z₂)` of the componentwise action exactly when the vertical vectors of
`p₁` at `z₁` and of `p₂` at `z₂` are exactly those sent by `di₁` and `di₂` into `S₁ · i₁(z₁)` and
`S₂ · i₂(z₂)`. -/
theorem ker_mfderiv_prodMap_eq_comap_map_eval_prodMap_iff (a₁ : InfinitesimalAction 𝔤₁ I₁ M₁)
    (a₂ : InfinitesimalAction 𝔤₂ I₂ M₂) (S₁ : Submodule ℝ 𝔤₁) (S₂ : Submodule ℝ 𝔤₂)
    {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1) (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2)
    (hp₁ : MDifferentiableAt J₁ JQ₁ p₁ z.1) (hp₂ : MDifferentiableAt J₂ JQ₂ p₂ z.2) :
    (mfderiv (J₁.prod J₂) (JQ₁.prod JQ₂) (Prod.map p₁ p₂) z).ker =
        ((S₁.prod S₂).map ((a₁.prodMap a₂).eval (Prod.map i₁ i₂ z))).comap
          (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap ↔
      (mfderiv J₁ JQ₁ p₁ z.1).ker =
          (S₁.map (a₁.eval (i₁ z.1))).comap (mfderiv J₁ I₁ i₁ z.1).toLinearMap ∧
        (mfderiv J₂ JQ₂ p₂ z.2).ker =
          (S₂.map (a₂.eval (i₂ z.2))).comap (mfderiv J₂ I₂ i₂ z.2).toLinearMap := by
  rw [Manifold.ker_mfderiv_prodMap hp₁ hp₂,
    comap_mfderiv_prodMap_map_eval_prodMap a₁ a₂ S₁ S₂ hi₁ hi₂,
    (Submodule.comap_injective_of_surjective (Manifold.tangentSpaceProdEquiv z).surjective).eq_iff]
  exact ⟨fun h ↦ ⟨by simpa using congrArg (Submodule.comap (LinearMap.inl ℝ _ _)) h,
    by simpa using congrArg (Submodule.comap (LinearMap.inr ℝ _ _)) h⟩,
    fun h ↦ h.1 ▸ h.2 ▸ rfl⟩

end InfinitesimalAction

end TauCeti
