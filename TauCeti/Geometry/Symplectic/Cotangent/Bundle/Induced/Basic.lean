/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LeftTrivialization
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The induced form on `G × N`

Let `G` be a real Lie group with Lie algebra `𝔤`, let `N` be a manifold carrying a two-form `σ`,
and let `f : N → 𝔤*` be a smooth map. Write `θ_g = d(L_{g⁻¹})_g` for the left Maurer–Cartan form.
On the product `G × N` this file builds the one-form

`λ = ⟨f, θ⟩`, `λ_(g, n)(v, u) = f n (θ_g v)`

(`TauCeti.CotangentBundle.inducedLiouvilleForm`), the pullback of the Liouville form of `T*G`
along `(g, n) ↦ (g, f n)` read in the left trivialization `G × 𝔤* ≃ T*G`, and the two-form

`Ω = -dλ + pr₂^* σ`

(`TauCeti.CotangentBundle.inducedForm`). This is the two-form of *symplectic induction*: when a
closed subgroup `H` of `G` acts on `(N, σ)` with moment map given by the restriction of `f` to the
Lie algebra `𝔥` of `H`, the form `Ω` is basic for the action `h • (g, n) = (g h⁻¹, h • n)` and
descends to the balanced product `G ×_H N`, on which `G` acts by left multiplication with moment
map `[g, n] ↦ Ad*_g (f n)`. With `N = 𝔪* × V` and `f (η, v) = ν + η + μ_V v`, for a splitting
`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and the symplectic slice `V` with its quadratic moment map `μ_V`, it is the form of
the Marle–Guillemin–Sternberg local model `G ×_H (𝔪* × V)` of a Hamiltonian action near an
orbit. With `H` trivial, `N = 𝔤*` and `f = id` it is the canonical form of `T*G`
(`TauCeti.CotangentBundle.inducedForm_id_zero`).

The statements here are made on `G × N` itself. The descent of `Ω` and of the moment map to the
balanced product `G ×_H N` is
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct`.

* **The formula.** `Ω` pairs `(v, u)` and `(w, u')` at `(g, n)` to
  `df_n u' (θ v) - df_n u (θ w) + f n ⁅θ v, θ w⁆ + σ(u, u')`
  (`TauCeti.CotangentBundle.eval₂_inducedForm`); at `g = 1`, where `θ` is the identity, it is
  `df_n u' v - df_n u w + f n ⁅v, w⁆ + σ(u, u')`
  (`TauCeti.CotangentBundle.eval₂_inducedForm_one`).
* **Closedness.** `Ω` is closed when `σ` is (`TauCeti.CotangentBundle.isClosed_inducedForm`).
* **Invariance.** Left translations of the `G`-factor preserve `λ` and `Ω`
  (`TauCeti.CotangentBundle.mpullback_prodMap_mul_left_inducedForm`). Right translation by `k`
  together with a map `φ` of `N` preserves them as soon as `f (φ n) = f n ∘ Ad_k` and, for `Ω`,
  `φ^* σ = σ` (`TauCeti.CotangentBundle.mpullback_prodMap_mul_right_inducedForm`). For the action
  of `H` this is the case `k = h⁻¹`, `φ = (h • ·)`, where the condition on `f` is its
  equivariance `f (h • n) = Ad*_h (f n)`.
* **Vertical vectors.** Let `v` be a tangent vector at `(g, n)` with first component `ξ^L(g)`,
  the value of the left-invariant vector field of `ξ ∈ 𝔤`. If its second component `u` satisfies
  `df_n u = f n ∘ ad_ξ` and `σ(u, ·) = -d(f · ξ)`, then `Ω(v, ·) = 0`
  (`TauCeti.CotangentBundle.eval₂_inducedForm_eq_zero`). For the action of `H`, the orbit
  direction of `ξ ∈ 𝔥` at `(g, n)` is `-(ξ^L(g), -ξ_N(n))`; the first condition on `u = -ξ_N(n)`
  is the derivative of the equivariance of `f`, and the second is the moment map equation of `f`
  in the direction `ξ`. The contraction of `-dλ` with the orbit direction is `-d(f · ξ)` and that
  of `pr₂^* σ` is `+d(f · ξ)`, so they cancel. Together with the invariance this makes `Ω` basic.
* **The moment map.** For the infinitesimal action of `𝔤` on `G × N` by the fundamental vector
  fields of left multiplication on the first factor, `(g, n) ↦ Ad*_g (f n)` is a moment map of `Ω`
  (`TauCeti.CotangentBundle.isMomentMap_inducedForm`). It is the pullback of the moment map of the
  cotangent lift of left multiplication along `(g, n) ↦ (g, f n)`, and `pr₂^* σ` does not see the
  fundamental vector fields, which are tangent to the `G`-factor.

## Main definitions

* `TauCeti.CotangentBundle.inducedLiouvilleForm I G hf`: the one-form `⟨f, θ⟩` on `G × N`.
* `TauCeti.CotangentBundle.inducedForm I G σ hf`: the two-form `-d⟨f, θ⟩ + pr₂^* σ` on `G × N`.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific J. Math.
  181 (1997), 201–229, §2 (the local model and its moment map for a proper action).
* D. Kazhdan, B. Kostant, S. Sternberg, *Hamiltonian group actions and dynamical systems of
  Calogero type*, Comm. Pure Appl. Math. 31 (1978), 481–507 (symplectic induction).
-/

public section

open Bundle Manifold VectorField TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold IN ∞ N] {f : N → E →L[ℝ] ℝ}

/-! ### The one-form `⟨f, θ⟩` -/

variable (I G) in
/-- The **induced Liouville form** `⟨f, θ⟩` on `G × N` of a smooth map `f : N → 𝔤*`: the pullback
of the Liouville form of `T*G` along `(g, n) ↦ (g, f n)`, read in the left trivialization
`G × 𝔤* ≃ T*G`. It sends a tangent vector `(v, u)` at `(g, n)` to `f n (d(L_{g⁻¹})_g v)`
(`TauCeti.CotangentBundle.inducedLiouvilleForm_apply`). -/
def inducedLiouvilleForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    SmoothForm (I.prod IN) (G × N) ℝ 1 :=
  SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf)
    (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
      (liouvilleForm I G))

/-- The induced Liouville form is the pullback of the left-trivialized Liouville form of `T*G`
along `(g, n) ↦ (g, f n)`. -/
theorem inducedLiouvilleForm_def (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    inducedLiouvilleForm I G hf = SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf)
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (liouvilleForm I G)) :=
  (rfl)

/-- The induced Liouville form sends a tangent vector `(v, u)` at `(g, n)` to
`f n (d(L_{g⁻¹})_g v)`. -/
theorem inducedLiouvilleForm_apply (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (p : G × N)
    (v : Fin 1 → TangentSpace (I.prod IN) p) :
    (inducedLiouvilleForm I G hf).val p v = f p.2 (mfderiv I I (p.1⁻¹ * ·) p.1 (v 0).1) := by
  rw [inducedLiouvilleForm_def, SmoothForm.coe_mpullback, TauCeti.mpullback_apply,
    mpullback_leftTrivialization_liouvilleForm_apply,
    mfderiv_prodMap_apply_fst ((hf p.2).mdifferentiableAt (by simp)), mfderiv_id]
  -- `Prod.map id f p = (p.1, f p.2)` definitionally.
  rfl

/-- On a tangent vector whose `G`-component is the value `ξ^L(g)` of the left-invariant vector
field of `ξ`, the induced Liouville form takes the value `f n ξ`. -/
theorem inducedLiouvilleForm_apply_of_fst_eq (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
    (p : G × N) {v : Fin 1 → TangentSpace (I.prod IN) p} {ξ : GroupLieAlgebra I G}
    (hv : (v 0).1 = mulInvariantVectorField ξ p.1) :
    (inducedLiouvilleForm I G hf).val p v = f p.2 ξ := by
  rw [inducedLiouvilleForm_apply, hv, mfderiv_inv_mul_mulInvariantVectorField]

/-- **Left invariance of the induced Liouville form.** Left translation of the `G`-factor
preserves `⟨f, θ⟩`. -/
@[simp]
theorem mpullback_prodMap_mul_left_inducedLiouvilleForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
    (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
      (inducedLiouvilleForm I G hf) = inducedLiouvilleForm I G hf := by
  apply Subtype.ext
  funext p
  ext v
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (I := I) (G := G) (g := p.1) (v 0).1
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply,
    inducedLiouvilleForm_apply_of_fst_eq hf p hξ.symm]
  refine inducedLiouvilleForm_apply_of_fst_eq hf _ ?_
  rw [mfderiv_prodMap_apply_fst mdifferentiableAt_id, ← hξ,
    mfderiv_mul_left_mulInvariantVectorField, Prod.map_fst]

/-- **Right translation of the induced Liouville form.** Right translation of the `G`-factor by
`k`, together with a map `φ` of `N` such that `f (φ n) = f n ∘ Ad_k`, preserves `⟨f, θ⟩`. -/
theorem mpullback_prodMap_mul_right_inducedLiouvilleForm
    (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (k : G) {φ : N → N} (hφ : ContMDiff IN IN ∞ φ)
    (hfφ : ∀ n, f (φ n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) k) :
    SmoothForm.mpullback (Prod.map (· * k) φ) (contMDiff_mul_right.prodMap hφ)
      (inducedLiouvilleForm I G hf) = inducedLiouvilleForm I G hf := by
  apply Subtype.ext
  funext p
  ext v
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (I := I) (G := G) (g := p.1) (v 0).1
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply,
    inducedLiouvilleForm_apply_of_fst_eq hf p hξ.symm,
    inducedLiouvilleForm_apply_of_fst_eq hf _ (ξ := Lie.adjointContinuousLinearMap (I := I) k⁻¹ ξ)]
  · rw [Prod.map_snd, hfφ]
    -- `(f ∘ Ad_k) (Ad_{k⁻¹} ξ) = f (Ad_k (Ad_{k⁻¹} ξ))`, by `ContinuousLinearMap.comp_apply`, which
    -- `rw` cannot use since `Ad_k` acts on `GroupLieAlgebra I G` and `f p.2` on the model space.
    exact congrArg (f p.2) (Lie.adjointContinuousLinearMap_adjointContinuousLinearMap_inv k ξ)
  · rw [mfderiv_prodMap_apply_fst ((hφ p.2).mdifferentiableAt (by simp)), ← hξ,
      Lie.mfderiv_mul_right_mulInvariantVectorField, Prod.map_fst]

/-! ### The two-form `-d⟨f, θ⟩ + pr₂^* σ` -/

variable (I G) in
/-- The **induced form** `Ω = -d⟨f, θ⟩ + pr₂^* σ` on `G × N` of a two-form `σ` on `N` and a smooth
map `f : N → 𝔤*`. It pairs `(v, u)` and `(w, u')` at `(g, n)` to
`df_n u' (θ v) - df_n u (θ w) + f n ⁅θ v, θ w⁆ + σ(u, u')`, where `θ = d(L_{g⁻¹})_g`
(`TauCeti.CotangentBundle.eval₂_inducedForm`). For a subgroup `H` acting on `(N, σ)` with moment
map the restriction of `f`, it is the form of symplectic induction from `H` to `G`. -/
def inducedForm (σ : SmoothTwoForm IN N) (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    SmoothTwoForm (I.prod IN) (G × N) :=
  -mextDerivₗ (I.prod IN) 1 (inducedLiouvilleForm I G hf) +
    SmoothForm.mpullback Prod.snd contMDiff_snd σ

variable {σ : SmoothTwoForm IN N}

/-- The induced form is `-d⟨f, θ⟩ + pr₂^* σ`. -/
theorem inducedForm_def (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    inducedForm I G σ hf = -mextDerivₗ (I.prod IN) 1 (inducedLiouvilleForm I G hf) +
      SmoothForm.mpullback Prod.snd contMDiff_snd σ :=
  (rfl)

/-- `-d⟨f, θ⟩` is the pullback of the canonical symplectic form of `T*G` along
`(g, n) ↦ (g, f n)`, read in the left trivialization. -/
theorem neg_mextDerivₗ_inducedLiouvilleForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    -mextDerivₗ (I.prod IN) 1 (inducedLiouvilleForm I G hf) =
      SmoothForm.mpullback (Prod.map id f) (contMDiff_id.prodMap hf)
        (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
          (symplecticForm I G)) := by
  rw [inducedLiouvilleForm_def, SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback,
    ← map_neg, ← map_neg, symplecticForm_eq_neg_mextDerivₗ]

/-- **The induced form is closed** when `σ` is. -/
theorem isClosed_inducedForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (hσ : σ.IsClosed) :
    (inducedForm I G σ hf).IsClosed :=
  (SmoothForm.isClosed_mextDerivₗ _).neg.add (hσ.mpullback _ _)

/-- **Left invariance of the induced form.** Left translation of the `G`-factor preserves
`-d⟨f, θ⟩ + pr₂^* σ`. -/
@[simp]
theorem mpullback_prodMap_mul_left_inducedForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
      (inducedForm I G σ hf) = inducedForm I G σ hf := by
  rw [inducedForm, map_add, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_prodMap_mul_left_inducedLiouvilleForm, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr _ contMDiff_snd ((Prod.map_snd' _ _).trans (Function.id_comp _))]

/-- **Right translation of the induced form.** Right translation of the `G`-factor by `k`, together
with a map `φ` of `N` preserving `σ` with `f (φ n) = f n ∘ Ad_k`, preserves
`-d⟨f, θ⟩ + pr₂^* σ`. -/
theorem mpullback_prodMap_mul_right_inducedForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (k : G)
    {φ : N → N} (hφ : ContMDiff IN IN ∞ φ)
    (hfφ : ∀ n, f (φ n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) k)
    (hσφ : SmoothForm.mpullback φ hφ σ = σ) :
    SmoothForm.mpullback (Prod.map (· * k) φ) (contMDiff_mul_right.prodMap hφ)
      (inducedForm I G σ hf) = inducedForm I G σ hf := by
  rw [inducedForm, map_add, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_prodMap_mul_right_inducedLiouvilleForm hf k hφ hfφ, SmoothForm.mpullback_mpullback]
  conv_rhs => rw [← hσφ, SmoothForm.mpullback_mpullback]
  rw [SmoothForm.mpullback_congr _ (hφ.comp contMDiff_snd) (Prod.map_snd' _ _)]

/-! ### The cotangent bundle of `G` -/

/-- **The cotangent bundle as an induced space.** For `N = 𝔤*`, `f = id` and `σ = 0`, the induced
form is the canonical symplectic form of `T*G` read in the left trivialization: the induced space
from the trivial subgroup. -/
theorem inducedForm_id_zero :
    inducedForm I G (0 : SmoothTwoForm 𝓘(ℝ, E →L[ℝ] ℝ) (E →L[ℝ] ℝ)) contMDiff_id =
      SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G) := by
  rw [inducedForm, neg_mextDerivₗ_inducedLiouvilleForm, map_zero, add_zero,
    SmoothForm.mpullback_congr _ contMDiff_id Prod.map_id, SmoothForm.mpullback_id,
    LinearMap.id_apply]

variable [CompleteSpace E]

/-- **The induced form in coordinates.** At `(g, n)` it pairs `(v, u)` and `(w, u')` to
`df_n u' (θ v) - df_n u (θ w) + f n ⁅θ v, θ w⁆ + σ(u, u')`, where `θ = d(L_{g⁻¹})_g`: the
left-trivialized canonical form of `T*G` pulled back along `(g, n) ↦ (g, f n)`, plus `σ`. -/
theorem eval₂_inducedForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (p : G × N)
    (v w : TangentSpace (I.prod IN) p) :
    (inducedForm I G σ hf).eval₂ p v w =
      mvfderiv IN f p.2 w.2 (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) -
        mvfderiv IN f p.2 v.2 (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f p.2 : E →ₗ[ℝ] ℝ)
          (mfderiv I I (p.1⁻¹ * ·) p.1 v.1) (mfderiv I I (p.1⁻¹ * ·) p.1 w.1) +
        σ.eval₂ p.2 v.2 w.2 := by
  rw [inducedForm, SmoothBundleForm.eval₂_add, neg_mextDerivₗ_inducedLiouvilleForm,
    eval₂_mpullback_prodMap_leftTrivialization_symplecticForm hf, SmoothForm.eval₂_mpullback_snd,
    tangentSpaceProdEquiv_apply, tangentSpaceProdEquiv_apply]

/-- **The induced form at the identity.** At `(1, n)` the Maurer–Cartan form is the identity, and
the induced form pairs `(v, u)` and `(w, u')` to `df_n u' v - df_n u w + f n ⁅v, w⁆ + σ(u, u')`. -/
theorem eval₂_inducedForm_one (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) (n : N)
    (v w : TangentSpace (I.prod IN) ((1 : G), n)) :
    (inducedForm I G σ hf).eval₂ (1, n) v w =
      mvfderiv IN f n w.2 v.1 - mvfderiv IN f n v.2 w.1 +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) v.1 w.1 +
        σ.eval₂ n v.2 w.2 := by
  have hθ (u : TangentSpace I (1 : G)) : mfderiv I I ((1 : G)⁻¹ * ·) 1 u = u := by
    have h := mfderiv_inv_mul_mulInvariantVectorField u (1 : G)
    rwa [mulInvariantVectorField_one] at h
  rw [eval₂_inducedForm hf, hθ v.1, hθ w.1]

/-- **Vertical vectors lie in the kernel of the induced form.** Let `v` be a tangent vector at
`(g, n)` whose `G`-component is the value `ξ^L(g)` of the left-invariant vector field of `ξ ∈ 𝔤`,
and whose `N`-component `u` satisfies `df_n u = f n ∘ ad_ξ` and `σ(u, ·) = -d(f · ξ)`. Then
`Ω(v, w) = 0` for every `w`. For a subgroup `H` acting on `(N, σ)`, with `f` equivariant and
restricting to a moment map on `𝔥`, the orbit directions of `h • (g, n) = (g h⁻¹, h • n)` are such
vectors. -/
theorem eval₂_inducedForm_eq_zero (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) {p : G × N}
    {v : TangentSpace (I.prod IN) p} {ξ : GroupLieAlgebra I G}
    (hv : v.1 = mulInvariantVectorField ξ p.1)
    (hfv : ∀ ζ : GroupLieAlgebra I G,
      mvfderiv IN f p.2 v.2 ζ = f p.2 (⁅ξ, ζ⁆ : GroupLieAlgebra I G))
    (hσv : ∀ u, σ.eval₂ p.2 v.2 u = -mvfderiv IN f p.2 u ξ) (w : TangentSpace (I.prod IN) p) :
    (inducedForm I G σ hf).eval₂ p v w = 0 := by
  set ζ : GroupLieAlgebra I G := mfderiv I I (p.1⁻¹ * ·) p.1 w.1
  have hk : Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f p.2 : E →ₗ[ℝ] ℝ) ξ ζ =
      f p.2 (⁅ξ, ζ⁆ : GroupLieAlgebra I G) :=
    (Module.Dual.kirillovForm_apply _ ξ ζ).trans (congrFun (ContinuousLinearMap.coe_coe (f p.2)) _)
  rw [eval₂_inducedForm, hv, mfderiv_inv_mul_mulInvariantVectorField, hfv ζ, hσv w.2]
  linear_combination hk

variable [CompleteSpace EN]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space G]

/-- **The moment map of the induced form.** For the infinitesimal action of `𝔤` on `G × N` by the
fundamental vector fields of left multiplication on the `G`-factor, `(g, n) ↦ Ad*_g (f n)` is a
moment map of `-d⟨f, θ⟩ + pr₂^* σ`. -/
theorem isMomentMap_inducedForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    (inducedForm I G σ hf).IsMomentMap ((InfinitesimalAction.fundamental I G I G).prod
      (0 : InfinitesimalAction (GroupLieAlgebra I G) IN N))
      fun p ↦ Lie.coadjointRepresentation ℝ I G p.1 (f p.2 : E →ₗ[ℝ] ℝ) := by
  set Ψ := leftTrivialization I G ∘ Prod.map id f
  have hΨ : ContMDiff (I.prod IN) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ Ψ :=
    (leftTrivialization I G).contMDiff.comp (contMDiff_id.prodMap hf)
  -- `Ψ` relates the fundamental vector fields on `G × N` to those of the cotangent lift.
  have hΨa : ∀ ξ p, mfderiv (I.prod IN) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Ψ p
      (((InfinitesimalAction.fundamental I G I G).prod
        (0 : InfinitesimalAction (GroupLieAlgebra I G) IN N)) ξ p) =
        InfinitesimalAction.fundamental I G (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I G) ξ
          (Ψ p) := by
    intro ξ p
    have hcomp : Ψ ∘ (fun k : G ↦ (k • p.1, p.2)) = fun k ↦ k • Ψ p := by
      funext k
      simp only [Ψ, Function.comp_apply, Prod.map_apply', id_eq, smul_eq_mul]
      exact leftTrivialization_mul k p.1 (f p.2)
    rw [InfinitesimalAction.fundamental_prod_zero_apply, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply, ← hcomp]
    exact (mfderiv_comp_apply_of_eq (f := fun k : G ↦ (k • p.1, p.2)) (1 : G)
      ((hΨ p).mdifferentiableAt (by simp))
      (by simpa only [smul_eq_mul] using mdifferentiableAt_mul_right.prodMk mdifferentiableAt_const)
      (by simp) ξ).symm
  -- The cotangent moment map along `Ψ` is the coadjoint orbit map of `f`.
  have hμ : momentMap I G ∘ Ψ = fun p ↦ Lie.coadjointRepresentation ℝ I G p.1 (f p.2 : E →ₗ[ℝ] ℝ) :=
    funext fun p ↦ by
      simp only [Ψ, Function.comp_apply, Prod.map_apply', id_eq]
      exact momentMap_leftTrivialization (p.1, f p.2)
  have h := (isEquivariantMomentMap_momentMap (IG := I) (G := G) (I := I)
    (M := G)).toIsMomentMap.mpullback hΨ hΨa
  rw [← SmoothForm.mpullback_mpullback (Prod.map id f) (leftTrivialization I G)
    (contMDiff_id.prodMap hf) (leftTrivialization I G).contMDiff,
    ← neg_mextDerivₗ_inducedLiouvilleForm hf, hμ] at h
  refine ⟨h.contMDiff, fun ξ ↦ SmoothTwoForm.isHamiltonianVectorField_iff.2 fun p w ↦ ?_⟩
  -- The fundamental vector fields have no `N`-component, so `pr₂^* σ` does not see them.
  rw [inducedForm, SmoothBundleForm.eval₂_add, h.eval₂_apply, SmoothForm.eval₂_mpullback_snd,
    tangentSpaceProdEquiv_apply, InfinitesimalAction.prod_apply, prodVectorField_snd,
    InfinitesimalAction.zero_apply, Pi.zero_apply, SmoothBundleForm.eval₂_zero_left, add_zero]

end TauCeti.CotangentBundle
