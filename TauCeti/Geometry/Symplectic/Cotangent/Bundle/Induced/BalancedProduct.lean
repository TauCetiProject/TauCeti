/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap
public import TauCeti.Geometry.Symplectic.Manifold.Descent
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Lie.Adjoint.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# The induced form on the balanced product `G ×_K N`

Let `G` be a real Lie group with Lie algebra `𝔤`, let `K` be a closed subgroup with Lie algebra
`𝔨`, included in `𝔤` by the differential `ι` of the inclusion, and let `K` act smoothly on a
manifold `N` carrying a two-form `σ`. Let `f : N → 𝔤*` be a smooth map such that

* `f` is `K`-equivariant, `f (k • n) = Ad*_k (f n)`, that is `f (k • n) = f n ∘ Ad_{k⁻¹}`;
* each `k ∈ K` preserves `σ`;
* the components `n ↦ f n (ι ζ)`, `ζ ∈ 𝔨`, form a moment map of the action of `K` on `(N, σ)`.

On `G × N` the induced form `Ω = -d⟨f, θ⟩ + pr₂^* σ` (`TauCeti.CotangentBundle.inducedForm`) is
then **basic** for the projection `q : G × N → G ×_K N` onto the balanced product, the quotient by
`k • (g, n) = (g k⁻¹, k • n)` (`TauCeti.CotangentBundle.isBasic_mpullback_inducedForm`):

* `Ω` is invariant under this action, by its invariance under right translation of the
  `G`-factor together with an equivariant map of `N`
  (`TauCeti.CotangentBundle.mpullback_prodMap_mul_right_inducedForm`);
* the kernel of `dq` is spanned by the orbit directions `(-(ι ζ)^L(g), ζ_N(n))`
  (`TauCeti.BalancedProduct.ker_mfderiv_quotientMk_rightTranslation`,
  `Subgroup.RightTranslation.fundamentalVectorField_toRightTranslation`), and these lie in the
  kernel of `Ω` (`TauCeti.CotangentBundle.eval₂_inducedForm_eq_zero`). The two conditions of that
  lemma are the differentiated equivariance of `f`,
  `df_n (ζ_N n) = -f n ∘ ad_(ι ζ)` (`TauCeti.mvfderiv_fundamentalVectorField_apply_of_apply_smul`),
  and the moment map equation of `f` in the direction `ι ζ`.

So `Ω` descends to a unique two-form `Ω_K` on `G ×_K N` with `q^* Ω_K = Ω`
(`TauCeti.CotangentBundle.balancedProductInducedForm`,
`TauCeti.CotangentBundle.mpullback_quotientMk_balancedProductInducedForm`). It is closed when `σ`
is, and invariant under the action `k • [g, n] = [k g, n]` of `G`. The map
`[g, n] ↦ Ad*_g (f n)` is well defined by the equivariance of `f`
(`TauCeti.CotangentBundle.balancedProductMomentMap`), and it is a coadjoint-equivariant moment
map of the action of `G` on `(G ×_K N, Ω_K)`
(`TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductMomentMap`), because on `G × N`
the map `(g, n) ↦ Ad*_g (f n)` is a moment map of `Ω` for left multiplication on the first factor
(`TauCeti.CotangentBundle.isMomentMap_inducedForm`).

This is **symplectic induction** from `K` to `G`. For a splitting `𝔤 = 𝔨 ⊕ 𝔪 ⊕ 𝔮`, the space
`N = 𝔪* × V` over a symplectic `K`-representation `V` with quadratic moment map `μ_V`, and
`f (η, v) = ν + η + μ_V v`, the space `(G ×_K N, Ω_K)` is the Marle–Guillemin–Sternberg local
model of a Hamiltonian action near an orbit. Nondegeneracy of `Ω_K`, which holds near the zero
section in that case, is not discussed here.

## Main definitions

* `TauCeti.CotangentBundle.balancedProductInducedForm`: the descent of the induced form to
  `G ×_K N`.
* `TauCeti.CotangentBundle.balancedProductMomentMap`: the moment map `[g, n] ↦ Ad*_g (f n)`.

## Main results

* `TauCeti.mvfderiv_fundamentalVectorField_apply_of_apply_smul`: the derivative of the
  equivariance of `f`.
* `TauCeti.CotangentBundle.isBasic_mpullback_inducedForm`: the induced form is basic for
  `G × N → G ×_K N`.
* `TauCeti.CotangentBundle.mpullback_quotientMk_balancedProductInducedForm`,
  `TauCeti.CotangentBundle.eq_balancedProductInducedForm_iff`: the descended form is the unique
  form pulling back to the induced form.
* `TauCeti.CotangentBundle.isClosed_balancedProductInducedForm`: it is closed when `σ` is.
* `TauCeti.CotangentBundle.mpullback_smul_balancedProductInducedForm`: it is `G`-invariant.
* `TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductMomentMap`: the action of `G` on
  `G ×_K N` is Hamiltonian with moment map `[g, n] ↦ Ad*_g (f n)`.

## References

* D. Kazhdan, B. Kostant, S. Sternberg, *Hamiltonian group actions and dynamical systems of
  Calogero type*, Comm. Pure Appl. Math. 31 (1978), 481–507 (symplectic induction).
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific J. Math.
  181 (1997), 201–229, §2.
-/

public section

noncomputable section

open Function Manifold TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### The derivative of the equivariance of a map to `𝔤*` -/

section Equivariance

variable {G : Type*} [Group G] {K : Subgroup G}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace G] [ChartedSpace H G]
  [LieGroup I ∞ G]
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [TopologicalSpace HK]
  {IK : ModelWithCorners ℝ EK HK} [ChartedSpace HK K] [ContMDiffSMul IK I ∞ K G]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [MulAction K N] [ContMDiffSMul IK IN ∞ K N]

/-- **Infinitesimal equivariance of a map to `𝔤*`.** Let a subgroup `K` of `G` act on `N`, and let
`f : N → 𝔤*` be equivariant along the orbit of `n`, `f (k • n) = f n ∘ Ad_{k⁻¹}`. Then the
derivative of `f` along the fundamental vector field of `ζ ∈ Lie(K)` is
`df_n (ζ_N n) = -f n ∘ ad_(ι ζ)`, where `ι ζ` is the image of `ζ` in the Lie algebra of `G`. -/
theorem mvfderiv_fundamentalVectorField_apply_of_apply_smul {f : N → E →L[ℝ] ℝ} {n : N}
    (hf : MDifferentiableAt IN 𝓘(ℝ, E →L[ℝ] ℝ) f n)
    (hfK : ∀ k : K, f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) ((k : G)⁻¹))
    (ζ : GroupLieAlgebra IK K) (η : GroupLieAlgebra I G) :
    mvfderiv IN f n (fundamentalVectorField IN ζ n) η =
      -f n (⁅K.subtype.groupLieAlgebraMap IK I ζ, η⁆ : GroupLieAlgebra I G) := by
  have hι : MDifferentiableAt IK I ((↑) : K → G) 1 :=
    (K.contMDiff_subtypeVal_of_contMDiffSMul (I' := IK) (n := ∞)).mdifferentiableAt (by simp)
  have hinv : MDifferentiableAt IK I (fun k : K ↦ (k : G)⁻¹) 1 :=
    ((contMDiff_inv I ∞).mdifferentiableAt (by simp)).comp _ hι
  have horbit : MDifferentiableAt IK IN (fun k : K ↦ k • n) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := IK) (I' := IN) (n := ∞) n).mdifferentiableAt
      (by simp)
  have hT : MDifferentiableAt I 𝓘(ℝ, E) (fun g : G ↦ show E from Lie.tangentAd (I := I) g η)
      ((1 : K) : G)⁻¹ :=
    (Lie.contMDiff_tangentAd_apply_const (I := I) (G := G) (show E from η)).mdifferentiableAt
      (by simp)
  -- Differentiate `k ↦ f (k • n) η = f n (Ad_(k⁻¹) η)` at `k = 1` in the direction `ζ`, once
  -- through the orbit map of `n` and once through the adjoint action.
  have h₁ : mvfderiv IK (fun k : K ↦ f (k • n) η) 1 ζ =
      mvfderiv IN f n (fundamentalVectorField IN ζ n) η :=
    (mvfderiv_comp_apply_of_eq (g := fun m ↦ f m η) 1 (hf.clm_apply mdifferentiableAt_const)
      horbit (one_smul K n) ζ).trans <| by
        rw [fundamentalVectorField_apply]
        exact mvfderiv_clm_apply_const hf η _
  have hh : mfderiv IK I (fun k : K ↦ (k : G)⁻¹) 1 ζ = -K.subtype.groupLieAlgebraMap IK I ζ := by
    rw [show (fun k : K ↦ (k : G)⁻¹) = (fun x : G ↦ x⁻¹) ∘ ((↑) : K → G) from rfl,
      mfderiv_comp_apply_of_eq 1 ((contMDiff_inv I ∞).mdifferentiableAt (by simp)) hι rfl,
      OneMemClass.coe_one, GroupLieAlgebra.mfderiv_inv_one_apply,
      MonoidHom.groupLieAlgebraMap_apply, Subgroup.coe_subtype]
  have h₂ : mvfderiv IK (fun k : K ↦ f (k • n) η) 1 ζ =
      f n (⁅-K.subtype.groupLieAlgebraMap IK I ζ, η⁆ : GroupLieAlgebra I G) := by
    have hfun : (fun k : K ↦ f (k • n) η) =
        f n ∘ (fun g : G ↦ show E from Lie.tangentAd (I := I) g η) ∘ (fun k : K ↦ (k : G)⁻¹) :=
      funext fun k ↦ by simp only [comp_apply, hfK, Lie.tangentAd_apply]; rfl
    rw [hfun, (f n).mvfderiv_comp_apply (hT.comp_of_eq 1 hinv rfl) ζ]
    congr 1
    rw [mvfderiv_comp_apply_of_eq 1 hT hinv rfl, hh, OneMemClass.coe_one, inv_one]
    exact Lie.mvfderiv_tangentAd_apply_one (I := I) (G := G) _ η
  rw [← h₁, h₂, neg_lie]
  exact (f n).map_neg _

end Equivariance

namespace CotangentBundle

open BalancedProduct

variable {G : Type*} [Group G] {K : Subgroup G}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless] {N : Type*}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [T2Space N] [MulAction K N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IN ∞ K N]
  {σ : SmoothTwoForm IN N} {f : N → E →L[ℝ] ℝ}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  [FiniteDimensional ℝ EN] [IN.Boundaryless] [IsManifold IN ∞ N] [T2Space N] [MulAction K N] in
/-- The identification `K.RightTranslation × N = G × N` has the identity as differential. -/
private theorem mfderiv_prodMap_toRightTranslation_symm_apply (x : K.RightTranslation × N)
    (v : TangentSpace (I.prod IN) x) :
    mfderiv (I.prod IN) (I.prod IN) (Prod.map K.toRightTranslation.symm (id : N → N)) x v = v := by
  -- `K.toRightTranslation.symm` is the identity of `G`, and `K.RightTranslation` carries the
  -- manifold structure of `G`; `change` passes to the identity map, which `rw` cannot do across
  -- the type synonym.
  change mfderiv (I.prod IN) (I.prod IN) (id : G × N → G × N) x v = v
  exact DFunLike.congr_fun (mfderiv_id (I := I.prod IN) (x := show G × N from x)) v

variable (hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f)
  (hfK : ∀ (k : K) n, f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) ((k : G)⁻¹))
  (hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ)
  (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
    fun n ↦ (f n : E →ₗ[ℝ] ℝ).comp (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap)

include hfK hσK hμ in
/-- **The induced form is basic for `G × N → G ×_K N`.** Let `K` act on `(N, σ)` preserving `σ`,
let `f : N → 𝔤*` be `K`-equivariant, and let the components `n ↦ f n (ι ζ)`, `ζ ∈ Lie(K)`, form a
moment map of the action of `K`. Then the induced form `-d⟨f, θ⟩ + pr₂^* σ`, read on
`K.RightTranslation × N`, is basic for the projection onto the balanced product `G ×_K N`. -/
theorem isBasic_mpullback_inducedForm :
    letI := rightTranslationChartedSpace K N I IN F
    RoughForm.IsBasic (V := ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)))
      (SmoothForm.mpullback (Prod.map K.toRightTranslation.symm (id : N → N))
        ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
        (inducedForm I G σ hf)).val := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IN) (G := K) (M := N) ∞
  have hq := isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have he : ContMDiff (I.prod IN) (I.prod IN) ∞ (Prod.map K.toRightTranslation.symm (id : N → N)) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id
  refine SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le
    (τ := fun (k : K) (x : K.RightTranslation × N) ↦ k • x) (hq.contMDiff.mdifferentiable (by simp))
    (fun k ↦ ?_) (fun k ↦ funext fun x ↦ Quotient.sound (MulAction.mem_orbit x k))
    (fun x y hxy ↦ ?_) (fun x v hv ↦ ?_) (fun k ↦ ?_)
  · -- Each `k` acts by the smooth map `(g, n) ↦ (g k⁻¹, k • n)`.
    exact (((ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := I) (n := ∞)
      (M := K.RightTranslation) k).prodMap
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := IN) (n := ∞) k)).mdifferentiable
      (by simp))
  · obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact hxy)
    exact Or.inr ⟨k⁻¹, inv_smul_smul k y⟩
  · -- A vertical vector is the generator `(-(ι ζ)^L(g), ζ_N(n))` of some `ζ ∈ Lie(K)`.
    have hv' := (ker_mfderiv_quotientMk_rightTranslation (I := I) (IZ := IN) (F := F) x).le hv
    obtain ⟨ζ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1 hv'
    rw [InfinitesimalAction.fundamental_apply, fundamentalVectorField_prod]
    refine LinearMap.mem_ker.2 (LinearMap.ext fun w ↦ ?_)
    rw [LinearMap.zero_apply, SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback,
      mfderiv_prodMap_toRightTranslation_symm_apply, mfderiv_prodMap_toRightTranslation_symm_apply]
    refine eval₂_inducedForm_eq_zero hf (ξ := -K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ) ?_
      (fun η ↦ ?_) (fun u ↦ ?_) w
    · rw [prodVectorField_fst]
      exact Subgroup.RightTranslation.fundamentalVectorField_toRightTranslation ζ
        (K.toRightTranslation.symm x.1)
    · rw [prodVectorField_snd,
        mvfderiv_fundamentalVectorField_apply_of_apply_smul ((hf x.2).mdifferentiableAt (by simp))
          (fun k ↦ hfK k x.2), neg_lie]
      exact ((f x.2).map_neg _).symm
    · -- The moment map equation of `n ↦ f n (ι ζ)` in the direction `u`.
      have h := SmoothTwoForm.isHamiltonianVectorField_iff.1 (hμ.isHamiltonianVectorField ζ) x.2 u
      rw [InfinitesimalAction.fundamental_apply] at h
      rw [prodVectorField_snd, h]
      refine (mvfderiv_clm_apply_const ((hf x.2).mdifferentiableAt (by simp)) _ u).trans ?_
      exact (neg_neg _).symm.trans (congrArg Neg.neg ((mvfderiv IN f x.2 u).map_neg _).symm)
  · -- On `G × N`, the action of `k` is `(g, n) ↦ (g k⁻¹, k • n)`, which preserves the induced form.
    have hφ := ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := IN) (n := ∞) (M := N) k
    have hτ : ContMDiff (I.prod IN) (I.prod IN) ∞ (fun x : K.RightTranslation × N ↦ k • x) :=
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := I) (n := ∞)
        (M := K.RightTranslation) k).prodMap hφ
    rw [← SmoothForm.coe_mpullback _ hτ, SmoothForm.mpullback_mpullback_of_comp_eq hτ he he
      (contMDiff_mul_right.prodMap hφ) (g' := Prod.map (· * (k : G)⁻¹) (k • ·)) rfl,
      mpullback_prodMap_mul_right_inducedForm hf _ hφ (hfK k) (hσK k)]

/-! ### The descended form -/

/-- **The induced form on the balanced product** `G ×_K N`: the unique two-form whose pullback
along the projection `G × N → G ×_K N` is the induced form `-d⟨f, θ⟩ + pr₂^* σ`
(`TauCeti.CotangentBundle.eq_balancedProductInducedForm_iff`). It exists because the induced form
is basic (`TauCeti.CotangentBundle.isBasic_mpullback_inducedForm`). -/
def balancedProductInducedForm :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      (BalancedProduct K K.RightTranslation N) :=
  letI := rightTranslationChartedSpace K N I IN F
  haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  SmoothForm.descendedForm
    (isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F))
    Quotient.mk_surjective _ (isBasic_mpullback_inducedForm hf hfK hσK hμ)

/-- The induced form on `G ×_K N` pulls back to the induced form on `G × N`. -/
theorem mpullback_quotientMk_balancedProductInducedForm :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)))
        (isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
          (F := F)).contMDiff
        (balancedProductInducedForm hf hfK hσK hμ) =
      SmoothForm.mpullback (Prod.map K.toRightTranslation.symm (id : N → N))
        ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
        (inducedForm I G σ hf) := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  exact SmoothForm.mpullback_descendedForm

/-- The induced form on `G ×_K N` is the unique two-form pulling back to the induced form on
`G × N`. -/
theorem eq_balancedProductInducedForm_iff :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    ∀ β : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
        (BalancedProduct K K.RightTranslation N),
      β = balancedProductInducedForm hf hfK hσK hμ ↔
        SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)))
            (isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
              (F := F)).contMDiff β =
          SmoothForm.mpullback (Prod.map K.toRightTranslation.symm (id : N → N))
            ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
            (inducedForm I G σ hf) := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  exact fun β ↦ SmoothForm.eq_descendedForm_iff

/-- **The induced form on `G ×_K N` in terms of representatives.** On the images of tangent
vectors `v` and `w` of `G × N` under the differential of the projection, the induced form on
`G ×_K N` takes the value of the induced form on `G × N`. -/
theorem eval₂_balancedProductInducedForm_mfderiv_quotientMk (x : K.RightTranslation × N)
    (v w : TangentSpace (I.prod IN) x) :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    SmoothBundleForm.eval₂ (balancedProductInducedForm hf hfK hσK hμ)
        (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)) x)
        (mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))) x v)
        (mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))) x w) =
      SmoothBundleForm.eval₂ (inducedForm I G σ hf) (K.toRightTranslation.symm x.1, x.2) v w := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  rw [← SmoothForm.eval₂_mpullback _ (isSubmersion_quotientMk_rightTranslation (K := K) (Z := N)
      (I := I) (IZ := IN) (F := F)).contMDiff, mpullback_quotientMk_balancedProductInducedForm,
    SmoothForm.eval₂_mpullback, mfderiv_prodMap_toRightTranslation_symm_apply,
    mfderiv_prodMap_toRightTranslation_symm_apply]
  -- `Prod.map K.toRightTranslation.symm id x` is `(K.toRightTranslation.symm x.1, x.2)`.
  rfl

/-- **The induced form on `G ×_K N` is closed** when `σ` is. -/
theorem isClosed_balancedProductInducedForm (hσ : σ.IsClosed) :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    (balancedProductInducedForm hf hfK hσK hμ).IsClosed := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  exact SmoothForm.isClosed_descendedForm_iff.2 ((isClosed_inducedForm hf hσ).mpullback _ _)

/-- **The induced form on `G ×_K N` is `G`-invariant**: the action `[g, n] ↦ [k g, n]` of `k ∈ G`
preserves it, as left translation of the `G`-factor preserves the induced form on `G × N`. -/
theorem mpullback_smul_balancedProductInducedForm (k : G) :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    haveI := contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    SmoothForm.mpullback (fun y : BalancedProduct K K.RightTranslation N ↦ k • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) k)
        (balancedProductInducedForm hf hfK hσK hμ) =
      balancedProductInducedForm hf hfK hσK hμ := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have := contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have hq := isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have he : ContMDiff (I.prod IN) (I.prod IN) ∞ (Prod.map K.toRightTranslation.symm (id : N → N)) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id
  -- On representatives, `k` acts by `(g, n) ↦ (k g, n)`, which preserves the induced form.
  have hL : ContMDiff (I.prod IN) (I.prod IN) ∞
      (Prod.map (K.toRightTranslation ∘ (k * ·) ∘ K.toRightTranslation.symm) (id : N → N)) :=
    ((Subgroup.RightTranslation.contMDiff_toRightTranslation ∞).comp (contMDiff_mul_left.comp
      (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞))).prodMap contMDiff_id
  refine SmoothForm.mpullback_injective_of_surjective hq.contMDiff Quotient.mk_surjective
    (hq.surjective_mfderiv (by simp)) ?_
  rw [SmoothForm.mpullback_mpullback_of_comp_eq hq.contMDiff
      (ContMDiffSMul.contMDiff_const_smul (I := I) k) hL hq.contMDiff (hcomp := rfl),
    mpullback_quotientMk_balancedProductInducedForm,
    SmoothForm.mpullback_mpullback_of_comp_eq hL he he
      (contMDiff_mul_left.prodMap contMDiff_id) (g' := Prod.map (k * ·) (id : N → N))
      (hcomp := rfl),
    mpullback_prodMap_mul_left_inducedForm]

/-! ### The moment map -/

/-- **The moment map of the induced space** `G ×_K N`: `[g, n] ↦ Ad*_g (f n)`, well defined by the
equivariance `f (k • n) = f n ∘ Ad_{k⁻¹}` of `f`. -/
def balancedProductMomentMap :
    BalancedProduct K K.RightTranslation N → Module.Dual ℝ (GroupLieAlgebra I G) :=
  Quotient.lift
    (fun x ↦ Lie.coadjointRepresentation ℝ I G (K.toRightTranslation.symm x.1) (f x.2 : E →ₗ[ℝ] ℝ))
    fun x y ⟨k, hk⟩ ↦ by
      -- `Ad*_(g k⁻¹) (f (k • n)) = Ad*_g (Ad*_(k⁻¹) (Ad*_k (f n))) = Ad*_g (f n)`.
      subst hk
      refine LinearMap.ext fun X ↦ ?_
      simp only [Lie.coadjointRepresentation_apply, Prod.smul_fst, Prod.smul_snd,
        Subgroup.RightTranslation.toRightTranslation_symm_smul, hfK, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, mul_inv_rev, inv_inv, Lie.adjointContinuousLinearMap_mul]
      have h := Lie.adjointContinuousLinearMap_adjointContinuousLinearMap_inv (I := I) ((k : G)⁻¹)
        (Lie.adjointContinuousLinearMap (I := I) (K.toRightTranslation.symm y.1)⁻¹ X)
      rw [inv_inv] at h
      exact (congrArg (f y.2) h).trans (Lie.coadjointRepresentation_apply _ _ _).symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsClosed (K : Set G)] [TopologicalSpace N]
  [T2Space N] in
/-- The moment map of the induced space on a class `[g, n]`. -/
@[simp]
theorem balancedProductMomentMap_mk (g : G) (n : N) :
    balancedProductMomentMap hfK (mk K (K.toRightTranslation g) n) =
      Lie.coadjointRepresentation ℝ I G g (f n : E →ₗ[ℝ] ℝ) :=
  (rfl)

/-- **The induced space is a Hamiltonian `G`-space.** The map `[g, n] ↦ Ad*_g (f n)` is a
coadjoint-equivariant moment map of the action `k • [g, n] = [k g, n]` of `G` on `G ×_K N` with
the induced form: it is the descent of the moment map `(g, n) ↦ Ad*_g (f n)` of the induced form on
`G × N` (`TauCeti.CotangentBundle.isMomentMap_inducedForm`). -/
theorem isEquivariantMomentMap_balancedProductMomentMap :
    letI := rightTranslationChartedSpace K N I IN F
    haveI := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    haveI := contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
    (balancedProductInducedForm hf hfK hσK hμ).IsEquivariantMomentMap
      (balancedProductMomentMap hfK) := by
  let _ := rightTranslationChartedSpace K N I IN F
  have := isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have := contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hq := isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN) (F := F)
  have he : ContMDiff (I.prod IN) (I.prod IN) ∞ (Prod.map K.toRightTranslation.symm (id : N → N)) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id
  -- The generator `(ξ_G(g), 0)` of left multiplication on `G × N` is sent to the generator of the
  -- action of `G` on `G ×_K N`, as the projection intertwines the two actions.
  have hlift (ξ : GroupLieAlgebra I G) (x : K.RightTranslation × N) :
      ∃ Y : TangentSpace (I.prod IN) x,
        mfderiv (I.prod IN) (I.prod IN) (Prod.map K.toRightTranslation.symm (id : N → N)) x Y =
            ((InfinitesimalAction.fundamental I G I G).prod
              (0 : InfinitesimalAction (GroupLieAlgebra I G) IN N)) ξ
              (Prod.map K.toRightTranslation.symm id x) ∧
          mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
              (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))) x Y =
            InfinitesimalAction.fundamental I G 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
              (BalancedProduct K K.RightTranslation N) ξ
              (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N)) x) := by
    have hφ : MDifferentiableAt I (I.prod IN)
        (fun g : G ↦ (K.toRightTranslation (g * K.toRightTranslation.symm x.1), x.2)) 1 :=
      (((Subgroup.RightTranslation.contMDiff_toRightTranslation ∞).comp
        (contMDiff_mul_right (I := I))).mdifferentiableAt (by simp)).prodMk mdifferentiableAt_const
    refine ⟨mfderiv I (I.prod IN)
      (fun g : G ↦ (K.toRightTranslation (g * K.toRightTranslation.symm x.1), x.2)) 1 ξ,
      ?_, ?_⟩
    · refine (mfderiv_prodMap_toRightTranslation_symm_apply x _).trans ?_
      rw [InfinitesimalAction.fundamental_prod_zero_apply]
      -- `K.RightTranslation` is `G`, and the curve `g ↦ (g x.1, x.2)` of
      -- `K.RightTranslation × N` is the curve `g ↦ (g • (e x).1, (e x).2)` of `G × N`.
      rfl
    · rw [InfinitesimalAction.fundamental_apply, fundamentalVectorField_apply,
        ← mfderiv_comp_apply_of_eq 1 (hq.contMDiff.mdifferentiableAt (by simp)) hφ (by simp)]
      -- The projection of the curve `g ↦ (g x.1, x.2)` is the orbit `g ↦ g • [x]`.
      rfl
  refine ⟨(isMomentMap_inducedForm (σ := σ) hf).of_comp_eq he hq
    (mpullback_quotientMk_balancedProductInducedForm hf hfK hσK hμ) Quotient.mk_surjective hlift
    (funext fun _ ↦ rfl), fun k y ↦ ?_⟩
  induction y using induction_on_toRightTranslation with
  | h g n =>
    rw [smul_mk_toRightTranslation, balancedProductMomentMap_mk, balancedProductMomentMap_mk,
      map_mul]
    -- The product in `Module.End` is composition.
    rfl

end CotangentBundle

end TauCeti
