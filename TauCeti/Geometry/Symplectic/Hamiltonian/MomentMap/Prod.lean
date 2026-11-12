/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm
public import TauCeti.Geometry.Symplectic.Manifold.Prod

import TauCeti.Algebra.Lie.Coadjoint

/-!
# Moment maps and reduction of products

Let `μ₁ : M₁ → 𝔤₁*` and `μ₂ : M₂ → 𝔤₂*` be moment maps of infinitesimal actions `a₁` of `𝔤₁` on
`(M₁, σ₁)` and `a₂` of `𝔤₂` on `(M₂, σ₂)`. The product Lie algebra `𝔤₁ × 𝔤₂` acts on `M₁ × M₂`
componentwise, `(Z₁, Z₂) ↦ (Z₁_{M₁}, Z₂_{M₂})`; this is the diagonal action
`TauCeti.InfinitesimalAction.prod` of the actions `a₁ ∘ pr₁` and `a₂ ∘ pr₂` of `𝔤₁ × 𝔤₂`. Its
moment map for the product form `σ₁.prod σ₂ = pr₁^* σ₁ + pr₂^* σ₂` is

`μ(x₁, x₂)(Z₁, Z₂) = μ₁(x₁)(Z₁) + μ₂(x₂)(Z₂)`

(`TauCeti.SmoothTwoForm.IsMomentMap.prodMap`), the functional `μ₁(x₁).coprod μ₂(x₂)` on
`𝔤₁ × 𝔤₂`. Its differential is componentwise
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_prodMap_apply`), so the tangent spaces
`ker dμ` of its levels are the products of those of the factors
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_prodMap`), and its cocycle vanishes exactly
where both cocycles vanish (`TauCeti.SmoothTwoForm.momentCocycle_prodMap_eq_zero_iff`). The
coadjoint stabilizer of `c₁.coprod c₂` is `(𝔤₁)_{c₁} × (𝔤₂)_{c₂}`
(`Module.Dual.toSubmodule_lieAnnihilator_coprod`).

Consequently **the product of reduction data is reduction data**. Let `i_k : Z_k → M_k` and
`p_k : Z_k → Q_k` be level data for `μ_k` at `c_k` in the sense of
`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`: `i_k`
parametrizes the level `μ_k = c_k` with tangent images `ker dμ_k`, and `p_k` is a surjective
submersion whose vertical vectors are those sent into the stabilizer orbit directions. Then
`i₁ × i₂` parametrizes the level `μ = c₁.coprod c₂` of the product moment map with tangent images
`ker dμ` (`TauCeti.SmoothTwoForm.IsMomentMap.range_mfderiv_prodMap_eq_ker_differential_prodMap`),
and the vertical vectors of `p₁ × p₂` are those sent into the orbit directions of the product
stabilizer (`TauCeti.SmoothTwoForm.IsMomentMap.ker_mfderiv_prodMap_eq_comap_map_eval_prod`).
So the product of the levels has a unique reduced symplectic form on `Q₁ × Q₂`
(`IsMomentMap.existsUnique_isSymplectic_mpullback_prodMap_eq_mpullback_prodMap`). By naturality
of the product form (`TauCeti.SmoothTwoForm.mpullback_prodMap_prod`) it is the product of the
reduced forms of the factors.
For the Marsden–Weinstein–Meyer data of a product of Hamiltonian spaces, these are the level
`μ⁻¹(c₁, c₂) = μ₁⁻¹(c₁) × μ₂⁻¹(c₂)` and its quotient by `G_{c₁} × G_{c₂}`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.prodMap`: the moment map of the componentwise action of
  `𝔤₁ × 𝔤₂` on `M₁ × M₂`.
* `TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_prodMap`: `ker dμ = ker dμ₁ × ker dμ₂`.
* `TauCeti.SmoothTwoForm.momentCocycle_prodMap_eq_zero_iff`: the cocycle of the product
  vanishes exactly where both cocycles vanish.
* `IsMomentMap.existsUnique_isSymplectic_mpullback_prodMap_eq_mpullback_prodMap`:
  the product of the level data of `μ₁` and `μ₂` has a unique reduced symplectic form.

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

namespace SmoothTwoForm

variable {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁]
  [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂]
  [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra ℝ 𝔤₁] [LieRing 𝔤₂] [LieAlgebra ℝ 𝔤₂]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂}
  {a₁ : InfinitesimalAction 𝔤₁ I₁ M₁} {a₂ : InfinitesimalAction 𝔤₂ I₂ M₂}
  {μ₁ : M₁ → Module.Dual ℝ 𝔤₁} {μ₂ : M₂ → Module.Dual ℝ 𝔤₂}

/-- A tangent vector of `M₁ × M₂` lies in the image of `S₁ × S₂` under the orbit map of the
componentwise action exactly when its components lie in the images of `S₁` and `S₂`. -/
private theorem mem_map_eval_prod (a₁ : InfinitesimalAction 𝔤₁ I₁ M₁)
    (a₂ : InfinitesimalAction 𝔤₂ I₂ M₂) (p : M₁ × M₂) (S₁ : Submodule ℝ 𝔤₁)
    (S₂ : Submodule ℝ 𝔤₂) (u : TangentSpace (I₁.prod I₂) p) :
    u ∈ (S₁.prod S₂).map
        (((a₁.comp (LieHom.fst ℝ 𝔤₁ 𝔤₂)).prod (a₂.comp (LieHom.snd ℝ 𝔤₁ 𝔤₂))).eval p) ↔
      (Manifold.tangentSpaceProdEquiv p u).1 ∈ S₁.map (a₁.eval p.1) ∧
        (Manifold.tangentSpaceProdEquiv p u).2 ∈ S₂.map (a₂.eval p.2) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w.1, hw.1, by simp⟩, ⟨w.2, hw.2, by simp⟩⟩
  · rintro ⟨⟨w₁, hw₁, hu₁⟩, ⟨w₂, hw₂, hu₂⟩⟩
    refine ⟨(w₁, w₂), ⟨hw₁, hw₂⟩, Prod.ext ?_ ?_⟩
    · simp only [InfinitesimalAction.eval_apply] at hu₁
      rw [Manifold.tangentSpaceProdEquiv_apply] at hu₁
      -- The two sides are stated in `TangentSpace I₁ p.1` and in its defining type `E₁`.
      simp only [InfinitesimalAction.eval_apply, InfinitesimalAction.prod_apply,
        InfinitesimalAction.comp_apply, LieHom.fst_apply, Manifold.prodVectorField_fst]
      exact hu₁
    · simp only [InfinitesimalAction.eval_apply] at hu₂
      rw [Manifold.tangentSpaceProdEquiv_apply] at hu₂
      simp only [InfinitesimalAction.eval_apply, InfinitesimalAction.prod_apply,
        InfinitesimalAction.comp_apply, LieHom.snd_apply, Manifold.prodVectorField_snd]
      exact hu₂

/-- **The cocycle of a product.** The cocycle of the moment map `μ₁(x₁).coprod μ₂(x₂)` of the
componentwise action of `𝔤₁ × 𝔤₂` on `M₁ × M₂` vanishes at `(x₁, x₂)` exactly when the cocycles
of `μ₁` at `x₁` and of `μ₂` at `x₂` vanish. -/
theorem momentCocycle_prodMap_eq_zero_iff (p : M₁ × M₂) :
    (σ₁.prod σ₂).momentCocycle
        ((a₁.comp (LieHom.fst ℝ 𝔤₁ 𝔤₂)).prod (a₂.comp (LieHom.snd ℝ 𝔤₁ 𝔤₂)))
        (fun q ↦ (μ₁ q.1).coprod (μ₂ q.2)) p = 0 ↔
      σ₁.momentCocycle a₁ μ₁ p.1 = 0 ∧ σ₂.momentCocycle a₂ μ₂ p.2 = 0 := by
  simp only [momentCocycle_eq_zero_iff, InfinitesimalAction.prod_apply,
    InfinitesimalAction.comp_apply, eval₂_prod, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.prodVectorField_fst, Manifold.prodVectorField_snd, Prod.forall,
    LieAlgebra.Prod.bracket_apply, LinearMap.coprod_apply, LieHom.fst_apply, LieHom.snd_apply]
  refine ⟨fun h ↦ ⟨fun Z Z' ↦ ?_, fun Z Z' ↦ ?_⟩, fun h Z₁ Z₂ Z₁' Z₂' ↦ by rw [h.1, h.2]⟩
  · simpa using h Z 0 Z' 0
  · simpa using h 0 Z 0 Z'

namespace IsMomentMap

/-- **Moment maps of products.** If `μ₁` and `μ₂` are moment maps of infinitesimal actions of
`𝔤₁` on `(M₁, σ₁)` and of `𝔤₂` on `(M₂, σ₂)`, then `(x₁, x₂) ↦ μ₁(x₁).coprod μ₂(x₂)`, that is
`(Z₁, Z₂) ↦ μ₁(x₁)(Z₁) + μ₂(x₂)(Z₂)`, is a moment map of the componentwise action of `𝔤₁ × 𝔤₂`
on `M₁ × M₂` for the product form. -/
theorem prodMap (h₁ : σ₁.IsMomentMap a₁ μ₁) (h₂ : σ₂.IsMomentMap a₂ μ₂) :
    (σ₁.prod σ₂).IsMomentMap
      ((a₁.comp (LieHom.fst ℝ 𝔤₁ 𝔤₂)).prod (a₂.comp (LieHom.snd ℝ 𝔤₁ 𝔤₂)))
      fun p ↦ (μ₁ p.1).coprod (μ₂ p.2) :=
  (h₁.comp (LieHom.fst ℝ 𝔤₁ 𝔤₂)).prod (h₂.comp (LieHom.snd ℝ 𝔤₁ 𝔤₂))

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
    InfinitesimalAction.prod_apply, InfinitesimalAction.comp_apply, LieHom.fst_apply,
    LieHom.snd_apply, Manifold.tangentSpaceProdEquiv_apply, Manifold.prodVectorField_fst,
    Manifold.prodVectorField_snd]

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

variable {EZ₁ HZ₁ Z₁ : Type*} [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
  {J₁ : ModelWithCorners ℝ EZ₁ HZ₁} [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁]
  [IsManifold J₁ ∞ Z₁]
  {EZ₂ HZ₂ Z₂ : Type*} [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
  {J₂ : ModelWithCorners ℝ EZ₂ HZ₂} [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂]
  [IsManifold J₂ ∞ Z₂]
  {EQ₁ HQ₁ Q₁ : Type*} [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [TopologicalSpace HQ₁]
  {JQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
  [IsManifold JQ₁ ∞ Q₁]
  {EQ₂ HQ₂ Q₂ : Type*} [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [TopologicalSpace HQ₂]
  {JQ₂ : ModelWithCorners ℝ EQ₂ HQ₂} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂]
  [IsManifold JQ₂ ∞ Q₂]
  {i₁ : Z₁ → M₁} {i₂ : Z₂ → M₂} {p₁ : Z₁ → Q₁} {p₂ : Z₂ → Q₂}
  {c₁ : Module.Dual ℝ 𝔤₁} {c₂ : Module.Dual ℝ 𝔤₂}

omit [IsManifold J₁ ∞ Z₁] [IsManifold J₂ ∞ Z₂] in
/-- **The product of levels is a level of the product.** If the tangent images of `i₁` at `z₁`
and of `i₂` at `z₂` are the kernels of the differentials of `μ₁` and `μ₂`, then the tangent image
of `i₁ × i₂` at `(z₁, z₂)` is the kernel of the differential of the moment map of the product. -/
theorem range_mfderiv_prodMap_eq_ker_differential_prodMap (h₁ : σ₁.IsMomentMap a₁ μ₁)
    (h₂ : σ₂.IsMomentMap a₂ μ₂) {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2)
    (hrange₁ : LinearMap.range (mfderiv J₁ I₁ i₁ z.1).toLinearMap =
      LinearMap.ker (h₁.differential (i₁ z.1)))
    (hrange₂ : LinearMap.range (mfderiv J₂ I₂ i₂ z.2).toLinearMap =
      LinearMap.ker (h₂.differential (i₂ z.2))) :
    LinearMap.range (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap =
      LinearMap.ker ((h₁.prodMap h₂).differential (Prod.map i₁ i₂ z)) := by
  ext v
  rw [ker_differential_prodMap h₁ h₂, Submodule.mem_comap, Submodule.mem_prod, Prod.map_fst,
    Prod.map_snd, ← hrange₁, ← hrange₂, mfderiv_prodMap hi₁ hi₂]
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, LinearMap.mem_range]
  rw [Manifold.tangentSpaceProdEquiv_apply]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨w.1, rfl⟩, ⟨w.2, rfl⟩⟩
  · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩
    exact ⟨(w₁, w₂), Prod.ext hw₁ hw₂⟩

omit [IsManifold J₁ ∞ Z₁] [IsManifold J₂ ∞ Z₂] [IsManifold JQ₁ ∞ Q₁] [IsManifold JQ₂ ∞ Q₂] in
/-- **The vertical directions of a product of reduction data.** If the vertical tangent vectors of
`p₁` at `z₁` and of `p₂` at `z₂` are those sent by `di₁` and `di₂` into the stabilizer orbit
directions `(𝔤₁)_{c₁} · i₁(z₁)` and `(𝔤₂)_{c₂} · i₂(z₂)`, then the vertical vectors of `p₁ × p₂`
at `(z₁, z₂)` are those sent by `d(i₁ × i₂)` into the orbit directions of the stabilizer of
`c₁.coprod c₂` for the componentwise action of `𝔤₁ × 𝔤₂`. -/
theorem ker_mfderiv_prodMap_eq_comap_map_eval_prod {z : Z₁ × Z₂}
    (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.1) (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.2)
    (hp₁ : MDifferentiableAt J₁ JQ₁ p₁ z.1) (hp₂ : MDifferentiableAt J₂ JQ₂ p₂ z.2)
    (hker₁ : (mfderiv J₁ JQ₁ p₁ z.1).ker =
      ((lieAnnihilator ℝ 𝔤₁ c₁).toSubmodule.map (a₁.eval (i₁ z.1))).comap
        (mfderiv J₁ I₁ i₁ z.1).toLinearMap)
    (hker₂ : (mfderiv J₂ JQ₂ p₂ z.2).ker =
      ((lieAnnihilator ℝ 𝔤₂ c₂).toSubmodule.map (a₂.eval (i₂ z.2))).comap
        (mfderiv J₂ I₂ i₂ z.2).toLinearMap) :
    (mfderiv (J₁.prod J₂) (JQ₁.prod JQ₂) (Prod.map p₁ p₂) z).ker =
      ((lieAnnihilator ℝ (𝔤₁ × 𝔤₂) (c₁.coprod c₂)).toSubmodule.map
        (((a₁.comp (LieHom.fst ℝ 𝔤₁ 𝔤₂)).prod (a₂.comp (LieHom.snd ℝ 𝔤₁ 𝔤₂))).eval
          (Prod.map i₁ i₂ z))).comap
        (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z).toLinearMap := by
  ext v
  rw [Submodule.mem_comap, Module.Dual.toSubmodule_lieAnnihilator_coprod, mem_map_eval_prod,
    LinearMap.mem_ker, mfderiv_prodMap hp₁ hp₂, mfderiv_prodMap hi₁ hi₂]
  simp only [Manifold.tangentSpaceProdEquiv_apply]
  -- The product of two continuous linear maps acts componentwise (`coe_prodMap'`).
  exact Prod.mk_eq_zero.trans
    (and_congr (SetLike.ext_iff.1 hker₁ v.1) (SetLike.ext_iff.1 hker₂ v.2))

/-- **The reduced symplectic form of a product.** Let `i₁ : Z₁ → M₁`, `p₁ : Z₁ → Q₁` and
`i₂ : Z₂ → M₂`, `p₂ : Z₂ → Q₂` be level data for moment maps `μ₁` at `c₁` and `μ₂` at `c₂`, in the
sense of `TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`,
with `K₁` and `K₂` acting along the fibres of `p₁` and `p₂`. Then `i₁ × i₂`, `p₁ × p₂` are level
data for the moment map `μ₁(x₁).coprod μ₂(x₂)` of the componentwise action of `𝔤₁ × 𝔤₂` at
`c₁.coprod c₂`, with `K₁ × K₂` acting componentwise, so there is a unique symplectic form on
`Q₁ × Q₂` pulling back along `p₁ × p₂` to the restriction of the product form along `i₁ × i₂`. -/
theorem existsUnique_isSymplectic_mpullback_prodMap_eq_mpullback_prodMap [FiniteDimensional ℝ E₁]
    [FiniteDimensional ℝ E₂] [J₁.Boundaryless] [J₂.Boundaryless] {K₁ K₂ : Type*} [SMul K₁ Z₁]
    [SMul K₂ Z₂] (h₁ : σ₁.IsMomentMap a₁ μ₁) (h₂ : σ₂.IsMomentMap a₂ μ₂)
    (hσ₁ : σ₁.IsSymplectic) (hσ₂ : σ₂.IsSymplectic)
    (hi₁ : ContMDiff J₁ I₁ ∞ i₁) (hi₂ : ContMDiff J₂ I₂ ∞ i₂)
    (hμi₁ : ∀ z, μ₁ (i₁ z) = c₁) (hμi₂ : ∀ z, μ₂ (i₂ z) = c₂)
    (hc₁ : ∀ z, σ₁.momentCocycle a₁ μ₁ (i₁ z) = 0) (hc₂ : ∀ z, σ₂.momentCocycle a₂ μ₂ (i₂ z) = 0)
    (hrange₁ : ∀ z, LinearMap.range (mfderiv J₁ I₁ i₁ z).toLinearMap =
      LinearMap.ker (h₁.differential (i₁ z)))
    (hrange₂ : ∀ z, LinearMap.range (mfderiv J₂ I₂ i₂ z).toLinearMap =
      LinearMap.ker (h₂.differential (i₂ z)))
    (hp₁ : IsSubmersion J₁ JQ₁ ∞ p₁) (hp₂ : IsSubmersion J₂ JQ₂ ∞ p₂)
    (hsurj₁ : Surjective p₁) (hsurj₂ : Surjective p₂)
    (hker₁ : ∀ z, (mfderiv J₁ JQ₁ p₁ z).ker =
      ((lieAnnihilator ℝ 𝔤₁ c₁).toSubmodule.map (a₁.eval (i₁ z))).comap
        (mfderiv J₁ I₁ i₁ z).toLinearMap)
    (hker₂ : ∀ z, (mfderiv J₂ JQ₂ p₂ z).ker =
      ((lieAnnihilator ℝ 𝔤₂ c₂).toSubmodule.map (a₂.eval (i₂ z))).comap
        (mfderiv J₂ I₂ i₂ z).toLinearMap)
    (hK₁ : ∀ k : K₁, ContMDiff J₁ J₁ ∞ fun z : Z₁ ↦ k • z)
    (hK₂ : ∀ k : K₂, ContMDiff J₂ J₂ ∞ fun z : Z₂ ↦ k • z)
    (hpK₁ : ∀ (k : K₁) z, p₁ (k • z) = p₁ z) (hpK₂ : ∀ (k : K₂) z, p₂ (k • z) = p₂ z)
    (hfib₁ : ∀ z z', p₁ z = p₁ z' → ∃ k : K₁, k • z = z')
    (hfib₂ : ∀ z z', p₂ z = p₂ z' → ∃ k : K₂, k • z = z')
    (hinv₁ : ∀ k : K₁, SmoothForm.mpullback (fun z : Z₁ ↦ k • z) (hK₁ k)
      (SmoothForm.mpullback i₁ hi₁ σ₁) = SmoothForm.mpullback i₁ hi₁ σ₁)
    (hinv₂ : ∀ k : K₂, SmoothForm.mpullback (fun z : Z₂ ↦ k • z) (hK₂ k)
      (SmoothForm.mpullback i₂ hi₂ σ₂) = SmoothForm.mpullback i₂ hi₂ σ₂) :
    ∃! η : SmoothTwoForm (JQ₁.prod JQ₂) (Q₁ × Q₂),
      η.IsSymplectic ∧ SmoothForm.mpullback (Prod.map p₁ p₂) (hp₁.prodMap hp₂).contMDiff η =
        SmoothForm.mpullback (Prod.map i₁ i₂) (hi₁.prodMap hi₂) (σ₁.prod σ₂) := by
  -- `K₁ × K₂` acts on `Z₁ × Z₂` componentwise.
  let _ : SMul (K₁ × K₂) (Z₁ × Z₂) := ⟨fun k z ↦ (k.1 • z.1, k.2 • z.2)⟩
  have hdi₁ z := (hi₁ z).mdifferentiableAt (n := ∞) (by simp)
  have hdi₂ z := (hi₂ z).mdifferentiableAt (n := ∞) (by simp)
  have hdp₁ z := (hp₁.contMDiff z).mdifferentiableAt (n := ∞) (by simp)
  have hdp₂ z := (hp₂.contMDiff z).mdifferentiableAt (n := ∞) (by simp)
  refine (h₁.prodMap h₂).existsUnique_isSymplectic_mpullback_eq_mpullback (c := c₁.coprod c₂)
    (K := K₁ × K₂) (hσ₁.prod hσ₂) (hi₁.prodMap hi₂) (fun z ↦ by simp [hμi₁, hμi₂])
    (fun z ↦ (momentCocycle_prodMap_eq_zero_iff _).2 ⟨hc₁ z.1, hc₂ z.2⟩)
    (fun z ↦ range_mfderiv_prodMap_eq_ker_differential_prodMap h₁ h₂ (hdi₁ z.1) (hdi₂ z.2)
      (hrange₁ z.1) (hrange₂ z.2))
    (hp₁.prodMap hp₂) (hsurj₁.prodMap hsurj₂)
    (fun z ↦ ker_mfderiv_prodMap_eq_comap_map_eval_prod (hdi₁ z.1) (hdi₂ z.2) (hdp₁ z.1)
      (hdp₂ z.2) (hker₁ z.1) (hker₂ z.2))
    (fun k ↦ (hK₁ k.1).prodMap (hK₂ k.2)) (fun k z ↦ Prod.ext (hpK₁ k.1 z.1) (hpK₂ k.2 z.2))
    (fun z z' hzz' ↦ ?_) fun k ↦ ?_
  · obtain ⟨k₁, hk₁⟩ := hfib₁ z.1 z'.1 congr($hzz'.1)
    obtain ⟨k₂, hk₂⟩ := hfib₂ z.2 z'.2 congr($hzz'.2)
    exact ⟨(k₁, k₂), Prod.ext hk₁ hk₂⟩
  · -- The action of `k` is the product map of the actions of its components.
    have h := mpullback_prodMap_prod (hK₁ k.1) (hK₂ k.2) (SmoothForm.mpullback i₁ hi₁ σ₁)
      (SmoothForm.mpullback i₂ hi₂ σ₂)
    rw [hinv₁, hinv₂, ← mpullback_prodMap_prod hi₁ hi₂] at h
    rw [mpullback_prodMap_prod hi₁ hi₂] at h ⊢
    exact h

end IsMomentMap

end SmoothTwoForm

end TauCeti
