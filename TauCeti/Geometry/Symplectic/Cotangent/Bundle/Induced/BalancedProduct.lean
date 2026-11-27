/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap
public import TauCeti.Geometry.Symplectic.Manifold.Descent
import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
import TauCeti.Geometry.Lie.FundamentalVectorField.Coadjoint
import TauCeti.Geometry.Manifold.GroupAction.BalancedProduct
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# Symplectic induction: the induced form on `G ×_K N`

Let `G` be a finite-dimensional real Lie group with Lie algebra `𝔤`, let `K` be a closed subgroup
with Lie algebra `𝔨` and inclusion `ι : 𝔨 → 𝔤`, and let `K` act smoothly on a manifold `N` carrying
a two-form `σ`. Let `f : N → 𝔤*` be a smooth map which is `K`-equivariant,
`f (k • n) = Ad*_k (f n)`, and whose restriction `n ↦ f n ∘ ι` to `𝔨` is a moment map of the action
of `K` on `(N, σ)`, and let `σ` be `K`-invariant. On `G × N`,
`TauCeti.CotangentBundle.inducedForm` is the two-form `Ω = -d⟨f, θ⟩ + pr₂^* σ`, where `θ` is the
left Maurer–Cartan form. This file shows that `Ω` descends to the balanced product

`G ×_K N = (G × N) / K`, `k • (g, n) = (g k⁻¹, k • n)`,

(`TauCeti.BalancedProduct.rightTranslationChartedSpace`), and that the left action of `G` on it
has the group-level moment map `[g, n] ↦ Ad*_g (f n)`.

The form `Ω` is basic for the projection `(g, n) ↦ [g, n]`
(`TauCeti.CotangentBundle.isBasic_inducedForm`). It is invariant under each `k ∈ K`, by
`TauCeti.CotangentBundle.mpullback_prodMap_mul_right_inducedForm`, since `f` is equivariant and `σ`
is invariant. It vanishes on the orbit directions of `K`, which make up the kernel of the
differential of the projection
(`TauCeti.BalancedProduct.ker_mfderiv_quotientMk_rightTranslation`). The orbit direction of
`ξ ∈ 𝔨` at `(g, n)` is `(-(ι ξ)^L(g), ξ_N(n))`, where `ξ^L` is the left-invariant vector field and
`ξ_N` the fundamental vector field. The contraction of `-d⟨f, θ⟩` with it is `-d⟨f, ι ξ⟩`, because
the derivative of the equivariance of `f` is `df (ξ_N) = -f ∘ ad_(ι ξ)`
(`TauCeti.mvfderiv_apply_fundamentalVectorField`), and the contraction of `pr₂^* σ` is
`+d⟨f, ι ξ⟩` by the moment map equation, so they cancel
(`TauCeti.CotangentBundle.eval₂_inducedForm_eq_zero`).

The descended form `TauCeti.CotangentBundle.balancedProductInducedForm` is the unique smooth
two-form on `G ×_K N` pulling back to `Ω`
(`TauCeti.CotangentBundle.eq_balancedProductInducedForm_iff`), and it is closed when `σ` is
(`TauCeti.CotangentBundle.isClosed_balancedProductInducedForm`). The map
`TauCeti.CotangentBundle.balancedProductInducedMomentMap`, `[g, n] ↦ Ad*_g (f n)`, is well defined
by the equivariance of `f`, and it is a group-level moment map of the action
`k • [g, n] = [k g, n]` of `G` on `(G ×_K N, Ω)`
(`TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductInducedForm`): it descends from
the moment map `(g, n) ↦ Ad*_g (f n)` of `Ω` on `G × N`
(`TauCeti.CotangentBundle.isMomentMap_inducedForm`).

No nondegeneracy or closedness of `σ` is needed for the descent and the moment map, and `K` need
not be compact or act freely on `N`. Let `K` be the stabilizer of a point `p` of a Hamiltonian
`G`-manifold with moment value `ν`, let `𝔪` be a `K`-invariant complement of `𝔨` in the Lie
algebra of the coadjoint stabilizer of `ν`, and let `V` be the symplectic slice at `p`, a
symplectic representation of `K` with quadratic moment map `μ_V`. With `N = 𝔪* × V` and
`f (η, v) = ν + η + μ_V v`, this is the Marle–Guillemin–Sternberg local model `G ×_K (𝔪* × V)` of
the action near the orbit of `p`, with moment map `[g, η, v] ↦ Ad*_g (ν + η + μ_V v)`.

## Main definitions

* `TauCeti.CotangentBundle.balancedProductInducedForm`: the descent of `-d⟨f, θ⟩ + pr₂^* σ` to
  `G ×_K N`.
* `TauCeti.CotangentBundle.balancedProductInducedMomentMap`: the map `[g, n] ↦ Ad*_g (f n)`.

## Main results

* `TauCeti.CotangentBundle.isBasic_inducedForm`: the induced form is basic for `G × N → G ×_K N`.
* `TauCeti.CotangentBundle.mpullback_quotientMk_balancedProductInducedForm`,
  `TauCeti.CotangentBundle.eq_balancedProductInducedForm_iff`: the descended form is the unique
  smooth form pulling back to the induced form.
* `TauCeti.CotangentBundle.eval₂_balancedProductInducedForm_mfderiv_one`: its value at `[1, n]`.
* `TauCeti.CotangentBundle.isClosed_balancedProductInducedForm`: it is closed when `σ` is.
* `TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductInducedForm`: the moment map of
  the action of `G`.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific J. Math.
  181 (1997), 201–229, §2 (the local model `G ×_H (𝔪* × V)` and its moment map).
* D. Kazhdan, B. Kostant, S. Sternberg, *Hamiltonian group actions and dynamical systems of
  Calogero type*, Comm. Pure Appl. Math. 31 (1978), 481–507 (symplectic induction).
-/

public section

noncomputable section

open Function Manifold TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {K : Subgroup G}
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- The map `K.RightTranslation × N → G × N` forgetting that `K` acts on the first factor. -/
private theorem contMDiff_prodMap_toRightTranslation_symm :
    ContMDiff (I.prod IN) (I.prod IN) ∞ (Prod.map K.toRightTranslation.symm (id : N → N)) :=
  (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id

/-- The map `K.RightTranslation × N → G × N` forgetting that `K` acts on the first factor has
identity differential. -/
private theorem mfderiv_prodMap_toRightTranslation_symm (x : K.RightTranslation × N)
    (v : TangentSpace (I.prod IN) x) :
    mfderiv (I.prod IN) (I.prod IN) (Prod.map K.toRightTranslation.symm (id : N → N)) x v = v := by
  rw [mfderiv_prodMap ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞ x.1)
    |>.mdifferentiableAt (by simp)) mdifferentiableAt_id]
  exact Prod.ext (Subgroup.RightTranslation.mfderiv_toRightTranslation_symm _ _)
    (congrArg (· v.2) (mfderiv_id (I := IN) (x := x.2)))

variable [LieGroup I ∞ G] [IsManifold IN ∞ N] {σ : SmoothTwoForm IN N} {f : N → E →L[ℝ] ℝ}

/-- The induced form `-d⟨f, θ⟩ + pr₂^* σ`, read on `K.RightTranslation × N`, the space on which `K`
acts by `k • (g, n) = (g k⁻¹, k • n)`. -/
private abbrev inducedFormRT (σ : SmoothTwoForm IN N)
    (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f) :
    SmoothTwoForm (I.prod IN) (K.RightTranslation × N) :=
  SmoothForm.mpullback _ contMDiff_prodMap_toRightTranslation_symm (inducedForm I G σ hf)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EN]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [MulAction K N] [ContMDiffSMul 𝓘(ℝ, F) IN ∞ K N]

/-- **The orbit directions of `K` are null for the induced form.** The fundamental vector field of
`ξ ∈ 𝔨` for the action `k • (g, n) = (g k⁻¹, k • n)` is `((-ι ξ)^L(g), ξ_N(n))`, and the induced
form vanishes on it: the contraction of `-d⟨f, θ⟩` is `-d⟨f, ι ξ⟩`, by the derivative of the
equivariance of `f`, and that of `pr₂^* σ` is `d⟨f, ι ξ⟩`, by the moment map equation. -/
private theorem eval₂_inducedFormRT_fundamental (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
    (hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
      fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap)
    (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) (x : K.RightTranslation × N)
    (w : TangentSpace (I.prod IN) x) :
    (inducedFormRT (G := G) (K := K) σ hf).eval₂ x
      (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IN) (K.RightTranslation × N) ξ x) w =
      0 := by
  set ι := K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I
  have hfn : MDifferentiableAt IN 𝓘(ℝ, E →L[ℝ] ℝ) f x.2 := (hf x.2).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt 𝓘(ℝ, F) I K.subtype 1 :=
    (K.contMDiff_subtypeVal_of_contMDiffSMul (I' := 𝓘(ℝ, F)) (n := ∞)).mdifferentiableAt
      (by simp)
  have hfv (ζ : GroupLieAlgebra I G) : mvfderiv IN f x.2 (fundamentalVectorField IN ξ x.2) ζ =
      f x.2 (⁅-ι ξ, ζ⁆ : GroupLieAlgebra I G) := by
    rw [mvfderiv_apply_fundamentalVectorField hfn K.subtype hι (hfK · x.2), neg_lie, ← lie_skew]
  have hσv (u : TangentSpace IN x.2) :
      σ.eval₂ x.2 (fundamentalVectorField IN ξ x.2) u = -mvfderiv IN f x.2 u (-ι ξ) := by
    rw [← InfinitesimalAction.fundamental_apply, hμ.eval₂_apply]
    -- The component `y ↦ (f y ∘ ι) ξ` of the moment map is `y ↦ f y (ι ξ)` by definition.
    refine (mvfderiv_clm_apply_const hfn (ι ξ) u).trans ?_
    -- `-ι ξ` is negated in `GroupLieAlgebra I G`, while `mvfderiv IN f x.2 u` is linear on the
    -- model space `E`; the two negations agree only up to unfolding, hence `erw`.
    erw [map_neg, neg_neg]
  rw [SmoothForm.eval₂_mpullback, mfderiv_prodMap_toRightTranslation_symm,
    mfderiv_prodMap_toRightTranslation_symm, InfinitesimalAction.fundamental_apply,
    Subgroup.RightTranslation.fundamentalVectorField_prod_apply]
  exact eval₂_inducedForm_eq_zero (I := I) (G := G) (IN := IN) (σ := σ) hf
    (p := (K.toRightTranslation.symm x.1, x.2))
    (v := (mulInvariantVectorField (-ι ξ) (K.toRightTranslation.symm x.1),
      fundamentalVectorField IN ξ x.2)) (ξ := -ι ξ) rfl hfv hσv w

omit [TopologicalSpace N] [FiniteDimensional ℝ E] in
/-- The pairing of `f (k • n)` is the coadjoint translate `Ad*_k (f n)`, when `f` is
`K`-equivariant. -/
private theorem coe_apply_smul
    (hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹)
    (k : K) (n : N) :
    (f (k • n) : E →ₗ[ℝ] ℝ) = Lie.coadjointRepresentation ℝ I G k (f n : E →ₗ[ℝ] ℝ) :=
  LinearMap.ext fun ζ ↦ by
    rw [hfK]
    -- `(f n ∘ Ad_{k⁻¹}) ζ = f n (Ad_{k⁻¹} ζ)` holds by definition of the composition.
    exact (Lie.coadjointRepresentation_apply (I := I) (k : G) (f n : E →ₗ[ℝ] ℝ) ζ).symm

variable [I.Boundaryless] [IsClosed (K : Set G)] [IN.Boundaryless] [T2Space N]

/-- **The induced form is basic** for the projection `(g, n) ↦ [g, n]` onto `G ×_K N`, read on
`K.RightTranslation × N`. Let `f : N → 𝔤*` be `K`-equivariant, let the restriction
`n ↦ f n ∘ ι` of `f` to `𝔨` be a moment map of the action of `K` on `(N, σ)`, and let `σ` be
`K`-invariant. Then `-d⟨f, θ⟩ + pr₂^* σ` is invariant under `k • (g, n) = (g k⁻¹, k • n)` and
vanishes on the orbit directions of `K`. -/
theorem isBasic_inducedForm (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
    (hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹)
    (hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
      fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    RoughForm.IsBasic (V := ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)))
      (SmoothForm.mpullback (Prod.map K.toRightTranslation.symm id)
        ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
        (inducedForm I G σ hf)).val := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have hπ := BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I)
    (IZ := IN) (F := F)
  refine SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le
    (τ := fun (k : K) (x : K.RightTranslation × N) ↦ k • x) (hπ.contMDiff.mdifferentiable (by simp))
    (fun k ↦ (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := I.prod IN) (n := ∞)
      k).mdifferentiable (by simp))
    (fun k ↦ funext fun x ↦ Quotient.sound ⟨k, rfl⟩) (fun x y hxy ↦ ?_) (fun x v hv ↦ ?_)
    (fun k ↦ ?_)
  · -- Two points with the same class differ by an element of `K`.
    obtain ⟨k, hk⟩ := Quotient.exact hxy
    exact .inr ⟨k⁻¹, by rw [← hk, inv_smul_smul]⟩
  · -- A vertical vector is an orbit direction, which is null.
    rw [BalancedProduct.ker_mfderiv_quotientMk_rightTranslation,
      InfinitesimalAction.mem_orbitTangent_iff] at hv
    obtain ⟨ξ, rfl⟩ := hv
    refine LinearMap.mem_ker.2 (LinearMap.ext fun w ↦ ?_)
    rw [SmoothForm.bilinFormAt_apply, LinearMap.zero_apply]
    exact eval₂_inducedFormRT_fundamental hf hfK hμ ξ x w
  · -- On representatives, `k` acts by right translation by `k⁻¹` and by `k` on `N`.
    have hφ := ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := IN) (n := ∞) (M := N) k
    have hcomp : Prod.map K.toRightTranslation.symm id ∘ (fun x : K.RightTranslation × N ↦ k • x) =
        Prod.map (· * (k : G)⁻¹) (fun n : N ↦ k • n) ∘ Prod.map K.toRightTranslation.symm id :=
      funext fun x ↦ Prod.ext (by simp) rfl
    have h := congrArg Subtype.val (SmoothForm.mpullback_mpullback_of_comp_eq
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := I.prod IN) k)
      contMDiff_prodMap_toRightTranslation_symm contMDiff_prodMap_toRightTranslation_symm
      (contMDiff_mul_right.prodMap hφ) hcomp (inducedForm I G σ hf))
    rwa [mpullback_prodMap_mul_right_inducedForm hf (k : G)⁻¹ hφ (hfK k)
      (hσK k), SmoothForm.coe_mpullback] at h

variable (I G) in
/-- **The induced form on `G ×_K N`**: the descent of `-d⟨f, θ⟩ + pr₂^* σ` along the projection
`(g, n) ↦ [g, n]`, for `f : N → 𝔤*` `K`-equivariant with restriction to `𝔨` a moment map of the
action of `K` on `(N, σ)`, and `σ` `K`-invariant. It is the unique smooth two-form pulling back
to the induced form (`TauCeti.CotangentBundle.eq_balancedProductInducedForm_iff`). -/
def balancedProductInducedForm (σ : SmoothTwoForm IN N) (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
    (hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹)
    (hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
      fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      (BalancedProduct K K.RightTranslation N) :=
  letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
  haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  SmoothForm.descendedForm (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K)
    (Z := N) (I := I) (IZ := IN) (F := F)) Quotient.mk_surjective _
    (isBasic_inducedForm hf hfK hσK hμ)

variable {hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f}
  {hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹}
  {hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ}
  {hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
    fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap}

/-- **The induced form on `G ×_K N` pulls back to the induced form** along the projection
`(g, n) ↦ [g, n]`, read on `K.RightTranslation × N`. -/
theorem mpullback_quotientMk_balancedProductInducedForm :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    SmoothForm.mpullback _ (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K)
        (Z := N) (I := I) (IZ := IN) (F := F)).contMDiff
        (balancedProductInducedForm I G σ hf hfK hσK hμ) =
      SmoothForm.mpullback (Prod.map K.toRightTranslation.symm id)
        ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
        (inducedForm I G σ hf) := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  exact SmoothForm.mpullback_descendedForm

/-- **Uniqueness of the induced form on `G ×_K N`**: it is the only smooth two-form whose pullback
along `(g, n) ↦ [g, n]` is the induced form. -/
theorem eq_balancedProductInducedForm_iff :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ∀ β : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      (BalancedProduct K K.RightTranslation N),
      β = balancedProductInducedForm I G σ hf hfK hσK hμ ↔
        SmoothForm.mpullback _ (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K)
          (Z := N) (I := I) (IZ := IN) (F := F)).contMDiff β =
        SmoothForm.mpullback (Prod.map K.toRightTranslation.symm id)
          ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
          (inducedForm I G σ hf) := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  exact fun β ↦ SmoothForm.eq_descendedForm_iff

/-- **The induced form on `G ×_K N` at `[1, n]`.** On images of tangent vectors `(v, u)` and
`(w, u')` at `(1, n)`, it is `df_n u' v - df_n u w + f n ⁅v, w⁆ + σ(u, u')`. -/
theorem eval₂_balancedProductInducedForm_mfderiv_one (n : N)
    (v w : TangentSpace (I.prod IN) (K.toRightTranslation 1, n)) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    (balancedProductInducedForm I G σ hf hfK hσK hμ).eval₂
        (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)) (K.toRightTranslation 1, n))
        (mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))) _ v)
        (mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))) _ w) =
      mvfderiv IN f n w.2 v.1 - mvfderiv IN f n v.2 w.1 +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) v.1 w.1 +
        σ.eval₂ n v.2 w.2 := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  rw [← SmoothForm.eval₂_mpullback _ (BalancedProduct.isSubmersion_quotientMk_rightTranslation
      (K := K) (Z := N) (I := I) (IZ := IN) (F := F)).contMDiff,
    mpullback_quotientMk_balancedProductInducedForm, SmoothForm.eval₂_mpullback,
    mfderiv_prodMap_toRightTranslation_symm (G := G),
    mfderiv_prodMap_toRightTranslation_symm (G := G)]
  -- The tangent spaces of `K.RightTranslation × N` and of `G × N` at `(1, n)` are both the model
  -- space `E × EN`; the formula is elaborated on `G × N` before being applied to `v` and `w`.
  have h := eval₂_inducedForm_one (I := I) (G := G) (σ := σ) hf n
  exact h v w

/-- **The induced form on `G ×_K N` is closed** when `σ` is. -/
theorem isClosed_balancedProductInducedForm (hσ : σ.IsClosed) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    (balancedProductInducedForm I G σ hf hfK hσK hμ).IsClosed := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  exact SmoothForm.isClosed_descendedForm_iff.2 ((isClosed_inducedForm hf hσ).mpullback _ _)

/-! ### The moment map -/

variable (G) in
/-- **The moment map of the induced space** `[g, n] ↦ Ad*_g (f n)` on `G ×_K N`, well defined since
`f` is `K`-equivariant: `Ad*_(g k⁻¹) (f (k • n)) = Ad*_g (f n)`. -/
def balancedProductInducedMomentMap
    (hfK : ∀ (k : K) (n : N),
      f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹) :
    BalancedProduct K K.RightTranslation N → Module.Dual ℝ (GroupLieAlgebra I G) :=
  Quotient.lift (fun x ↦ Lie.coadjointRepresentation ℝ I G (K.toRightTranslation.symm x.1)
    (f x.2 : E →ₗ[ℝ] ℝ)) fun _ y ⟨k, hk⟩ ↦ by
      rw [← hk, Prod.smul_fst, Prod.smul_snd, coe_apply_smul hfK,
        Subgroup.RightTranslation.toRightTranslation_symm_smul]
      -- `Ad*_(g k⁻¹) (Ad*_k ν) = Ad*_(g k⁻¹ k) ν`: the product of `Module.End` acts by
      -- composition.
      exact (LinearMap.congr_fun (map_mul (Lie.coadjointRepresentation ℝ I G) _ (k : G))
        _).symm.trans (by rw [inv_mul_cancel_right])

omit [TopologicalSpace N] [FiniteDimensional ℝ E] [I.Boundaryless] [IsClosed (K : Set G)]
  [T2Space N] in
/-- The moment map of the induced space at `[g, n]` is `Ad*_g (f n)`. -/
@[simp]
theorem balancedProductInducedMomentMap_mk (g : G) (n : N) :
    balancedProductInducedMomentMap G hfK (BalancedProduct.mk K (K.toRightTranslation g) n) =
      Lie.coadjointRepresentation ℝ I G g (f n : E →ₗ[ℝ] ℝ) := by
  simp [balancedProductInducedMomentMap]

/-- **The moment map of the induced space** `G ×_K N`. For the left action `k • [g, n] = [k g, n]`
of `G`, the map `[g, n] ↦ Ad*_g (f n)` is a coadjoint-equivariant moment map of the induced form
on `G ×_K N`. It descends from the moment map `(g, n) ↦ Ad*_g (f n)` of `-d⟨f, θ⟩ + pr₂^* σ`
on `G × N` (`TauCeti.CotangentBundle.isMomentMap_inducedForm`). -/
theorem isEquivariantMomentMap_balancedProductInducedForm :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    haveI := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    (balancedProductInducedForm I G σ hf hfK hσK hμ).IsEquivariantMomentMap
      (balancedProductInducedMomentMap G hfK) := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hπ := BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I)
    (IZ := IN) (F := F)
  refine ⟨(isMomentMap_inducedForm (G := G) (σ := σ) hf).of_comp_eq
    contMDiff_prodMap_toRightTranslation_symm hπ mpullback_quotientMk_balancedProductInducedForm
    Quotient.mk_surjective (fun ξ x ↦ ?_) (funext fun x ↦ rfl), fun g y ↦ ?_⟩
  · -- The fundamental vector field of `ξ` on `G × N` lifts that on `G ×_K N`.
    have hL : MDifferentiableAt I (I.prod IN)
        (fun g : G ↦ (K.toRightTranslation (g * K.toRightTranslation.symm x.1), x.2)) 1 :=
      ((Subgroup.RightTranslation.contMDiff_toRightTranslation (I := I) ∞).mdifferentiableAt
        (by simp) |>.comp_of_eq 1 (mdifferentiableAt_mul_right (I := I)) rfl).prodMk
        mdifferentiableAt_const
    have horbit : (fun g : G ↦ g • Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)) x) =
        Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)) ∘
          fun g : G ↦ (K.toRightTranslation (g * K.toRightTranslation.symm x.1), x.2) :=
      funext fun g ↦ by
        rw [comp_apply, BalancedProduct.quotientMk_eq_mk_toRightTranslation,
          BalancedProduct.smul_mk_toRightTranslation]
    refine ⟨InfinitesimalAction.prod (InfinitesimalAction.fundamental I G I G) 0 ξ
      (Prod.map K.toRightTranslation.symm id x), mfderiv_prodMap_toRightTranslation_symm _ _, ?_⟩
    rw [InfinitesimalAction.fundamental_apply, fundamentalVectorField_apply, horbit]
    refine Eq.trans ?_ (mfderiv_comp_apply_of_eq (1 : G) ((hπ.contMDiff x).mdifferentiableAt
      (by simp)) hL (Prod.ext (by simp) rfl) ξ).symm
    rw [InfinitesimalAction.fundamental_prod_zero_apply]
    -- The two orbit maps `g ↦ (g g₀, n)` into `G × N` and into `K.RightTranslation × N` agree up to
    -- the identification of `G` with its type synonym, which carries the charts of `G`.
    rfl
  · induction y using BalancedProduct.induction_on_toRightTranslation with
    | h g' n =>
      rw [BalancedProduct.smul_mk_toRightTranslation, balancedProductInducedMomentMap_mk,
        balancedProductInducedMomentMap_mk, map_mul]
      exact mul_apply_eq_comp _ _ _

end TauCeti.CotangentBundle
