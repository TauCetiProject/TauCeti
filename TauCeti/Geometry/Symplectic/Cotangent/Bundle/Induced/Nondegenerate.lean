/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct
public import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Nondegeneracy of the induced form on `G ×_K N` at `[1, n]`

Let `K` be a closed subgroup of a finite-dimensional real Lie group `G`, acting smoothly on a
manifold `N` with a `K`-invariant two-form `σ`, and let `f : N → 𝔤*` be `K`-equivariant with
`𝔨`-components a moment map. The form `Ω = -d⟨f, θ⟩ + pr₂^* σ` descends to the balanced product
`G ×_K N` (`TauCeti.CotangentBundle.balancedProductInducedForm`). This file decides when the
descended form is nondegenerate at the base point `[1, n]`.

At `(1, n)` the induced form pairs `(ξ, u)` and `(ζ, w)` in `𝔤 × T_n N` to

`B_n((ξ, u), (ζ, w)) = df_n(w)(ξ) - df_n(u)(ζ) + f(n) ⁅ξ, ζ⁆ + σ_n(u, w)`

(`TauCeti.CotangentBundle.eval₂_balancedProductInducedForm_mfderiv_one`). Its null space always
contains the orbit directions `(-ι κ, κ_N(n))` of `κ ∈ 𝔨`, which span the kernel of the
differential of `G × N → G ×_K N`, and the descended form is nondegenerate at `[1, n]` exactly when
the null space of `B_n` consists of these orbit directions
(`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff`). When
`n` is fixed by `K`, the orbit directions are the vectors `(ξ, 0)` with `ξ` in the image of `𝔨`
(`nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff_of_forall_smul_eq`, in the
namespace `TauCeti.CotangentBundle`).

The main application is the **Marle–Guillemin–Sternberg local model** `G ×_H (𝔪* × V)` of a
Hamiltonian action near the orbit of a point `p` with stabilizer `H` and moment value `ν`. There
`𝔨_ν = {ξ | ν ⁅ξ, ·⁆ = 0}` is the coadjoint stabilizer, `𝔪` a complement of `𝔥` in `𝔨_ν`, `V` the
symplectic slice with its form `ω_V`, and `f(a, v) = ν + a ∘ P + μ_V(v)`, where `P : 𝔤 → 𝔪` is a
projection along `𝔥` and a complement of `𝔨_ν`, and the slice moment map `μ_V(v) ∈ 𝔥*` is extended
to `𝔤` along the same splitting. At the `H`-fixed base point `n = (0, 0)`, the quadratic slice
moment map has zero differential, so `df_n(a, v)(ξ) = a(P ξ)` and `σ_n = ω_V`, and `B_n` becomes
the model tensor

`B_n((ξ, a, v), (ζ, b, w)) = b(P ξ) - a(P ζ) + ν ⁅ξ, ζ⁆ + ω_V(v, w)`.

Its null space is `𝔥 × 0 × 0`: pairing with `(0, b, 0)` and `(0, 0, w)` forces `P ξ = 0` and
`v = 0`, pairing with `(ζ, 0, 0)` for `ζ ∈ 𝔨_ν` forces `a = 0` because `P` maps `𝔨_ν` onto `𝔪`,
and then `ν ⁅ξ, ·⁆ = 0`, so that `ξ ∈ 𝔨_ν ∩ ker P = 𝔥`. Hence the induced form of the local model
is nondegenerate at `[1, 0, 0]`
(`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one`). The
statement takes the pointwise shape of `f` and `σ` at `n` as hypotheses, through a linear
identification `e : T_n N ≃ 𝔪* × V`, so it applies to any realization of the model in which `f`
and `σ` have this shape at the base point.

## Main results

All declarations are in the namespace `TauCeti.CotangentBundle`.

* `nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff`: the induced form is
  nondegenerate at `[1, n]` exactly when the null space of `B_n` consists of orbit directions.
* `nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff_of_forall_smul_eq`: the same at
  a point fixed by `K`.
* `nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one`: the induced form of the
  Marle–Guillemin–Sternberg model is nondegenerate at its base point.
* `eventually_nondegenerate_bilinFormAt_balancedProductInducedForm`: it is nondegenerate on a
  neighbourhood of its base point.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific J. Math.
  181 (1997), 201–229, §2 (the local model `G ×_H (𝔪* × V)` and its symplectic form).
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
  [LieGroup I ∞ G] [IsManifold IN ∞ N] {σ : SmoothTwoForm IN N} {f : N → E →L[ℝ] ℝ}
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ EN]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [MulAction K N] [ContMDiffSMul 𝓘(ℝ, F) IN ∞ K N]

/-- The orbit direction of `κ ∈ 𝔨` at `(1, n)`, for the action `k • (g, n) = (g k⁻¹, k • n)` of
`K` on `G × N`, is `(-ι κ, κ_N(n))`. -/
private theorem fundamental_toRightTranslation_one (κ : GroupLieAlgebra 𝓘(ℝ, F) K) (n : N) :
    (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IN) (K.RightTranslation × N) κ
      (K.toRightTranslation 1, n) : GroupLieAlgebra I G × TangentSpace IN n) =
      (-K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ, fundamentalVectorField IN κ n) := by
  rw [InfinitesimalAction.fundamental_apply,
    Subgroup.RightTranslation.fundamentalVectorField_prod_apply, Equiv.symm_apply_apply,
    mulInvariantVectorField_one]

variable [I.Boundaryless] [IsClosed (K : Set G)] [IN.Boundaryless] [T2Space N]
  {hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f}
  {hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹}
  {hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ}
  {hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
    fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap}

/-- **Nondegeneracy of the induced form at `[1, n]`.** The induced form on `G ×_K N` is
nondegenerate at `[1, n]` exactly when every `(ξ, u) ∈ 𝔤 × T_n N` that is null for

`B_n((ξ, u), (ζ, w)) = df_n(w)(ξ) - df_n(u)(ζ) + f(n) ⁅ξ, ζ⁆ + σ_n(u, w)`

is an orbit direction `(-ι κ, κ_N(n))` of some `κ ∈ 𝔨`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff (n : N) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt
        (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))
          (K.toRightTranslation 1, n))).Nondegenerate ↔
      ∀ (ξ : GroupLieAlgebra I G) (u : TangentSpace IN n),
        (∀ (ζ : GroupLieAlgebra I G) (w : TangentSpace IN n),
          mvfderiv IN f n w ξ - mvfderiv IN f n u ζ +
            Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) ξ ζ +
            σ.eval₂ n u w = 0) →
        ∃ κ : GroupLieAlgebra 𝓘(ℝ, F) K,
          K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ = -ξ ∧ fundamentalVectorField IN κ n = u := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have hπ := BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I)
    (IZ := IN) (F := F)
  have hdπ := hπ.surjective_mfderiv (by simp) (K.toRightTranslation 1, n)
  rw [SmoothTwoForm.nondegenerate_bilinFormAt_iff_ker_bilinFormAt_mpullback hπ.contMDiff hdπ,
    BalancedProduct.ker_mfderiv_quotientMk_rightTranslation]
  -- The orbit directions span the kernel of the differential of the projection, so they are
  -- null for the pulled-back form.
  have hle : (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IN)
      (K.RightTranslation × N)).orbitTangent (K.toRightTranslation 1, n) ≤
        LinearMap.ker ((SmoothForm.mpullback _ hπ.contMDiff
          (balancedProductInducedForm I G σ hf hfK hσK hμ)).bilinFormAt
            (K.toRightTranslation 1, n)) := by
    rw [← BalancedProduct.ker_mfderiv_quotientMk_rightTranslation,
      SmoothTwoForm.ker_bilinFormAt_mpullback hπ.contMDiff _ hdπ, ← Submodule.comap_bot]
    exact Submodule.comap_mono bot_le
  -- A vector is null for the pulled-back form exactly when it is null for `B_n`.
  have hker (v : TangentSpace (I.prod IN) (K.toRightTranslation 1, n)) :
      v ∈ LinearMap.ker ((SmoothForm.mpullback _ hπ.contMDiff
        (balancedProductInducedForm I G σ hf hfK hσK hμ)).bilinFormAt
          (K.toRightTranslation 1, n)) ↔
        ∀ (ζ : GroupLieAlgebra I G) (w : TangentSpace IN n),
          mvfderiv IN f n w v.1 - mvfderiv IN f n v.2 ζ +
            Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) v.1 ζ +
            σ.eval₂ n v.2 w = 0 := by
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, SmoothForm.bilinFormAt_apply,
      SmoothForm.eval₂_mpullback, LinearMap.zero_apply]
    have key (w : TangentSpace (I.prod IN) (K.toRightTranslation 1, n)) :=
      eval₂_balancedProductInducedForm_mfderiv_one (F := F) (hf := hf) (hfK := hfK) (hσK := hσK)
        (hμ := hμ) n v w
    exact ⟨fun h ζ w ↦ (key (ζ, w)).symm.trans (h _), fun h w ↦ (key w).trans (h w.1 w.2)⟩
  refine (le_antisymm_iff.trans (and_iff_left hle)).trans ⟨fun h ξ u hξu ↦ ?_, fun h v hv ↦ ?_⟩
  · obtain ⟨κ, hκ⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ _).1
      (h ((hker ((ξ, u) : TangentSpace (I.prod IN) (K.toRightTranslation 1, n))).2 hξu))
    rw [fundamental_toRightTranslation_one] at hκ
    exact ⟨κ, neg_eq_iff_eq_neg.1 (congrArg Prod.fst hκ), congrArg Prod.snd hκ⟩
  · obtain ⟨κ, hκξ, hκu⟩ := h v.1 v.2 ((hker v).1 hv)
    refine (InfinitesimalAction.mem_orbitTangent_iff _ _).2 ⟨κ, ?_⟩
    rw [fundamental_toRightTranslation_one, hκξ, hκu]
    exact Prod.ext (neg_neg _) rfl

/-- **Nondegeneracy of the induced form at a `K`-fixed point.** If `n` is fixed by `K`, the induced
form on `G ×_K N` is nondegenerate at `[1, n]` exactly when every `(ξ, u)` null for `B_n` has
`u = 0` and `ξ` in the image of `𝔨`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff_of_forall_smul_eq
    {n : N} (hn : ∀ k : K, k • n = n) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt
        (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))
          (K.toRightTranslation 1, n))).Nondegenerate ↔
      ∀ (ξ : GroupLieAlgebra I G) (u : TangentSpace IN n),
        (∀ (ζ : GroupLieAlgebra I G) (w : TangentSpace IN n),
          mvfderiv IN f n w ξ - mvfderiv IN f n u ζ +
            Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) ξ ζ +
            σ.eval₂ n u w = 0) →
        u = 0 ∧ ∃ κ : GroupLieAlgebra 𝓘(ℝ, F) K, K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ = ξ := by
  rw [nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff]
  simp only [fundamentalVectorField_eq_zero_of_forall_smul_eq hn]
  refine forall₂_congr fun ξ u ↦ imp_congr_right fun _ ↦ ⟨fun ⟨κ, hκ, hu⟩ ↦ ⟨hu.symm, -κ, ?_⟩,
    fun ⟨hu, κ, hκ⟩ ↦ ⟨-κ, ?_, hu.symm⟩⟩
  · rw [map_neg, hκ, neg_neg]
  · rw [map_neg, hκ]

/-- **The Marle–Guillemin–Sternberg model is nondegenerate at its base point.** Let `n` be fixed
by `K`, put `ν = f(n)`, and identify `T_n N` with `𝔪* × V` by a linear equivalence `e`, where
`df_n(u)(ξ) = (e u).1 (P ξ)` for a linear map `P : 𝔤 → 𝔪` and `σ_n(u, w) = β((e u).2, (e w).2)`
for a two-form `β` on `V` with trivial left radical. Suppose that `P` maps the coadjoint
stabilizer `𝔨_ν = {ξ | ν ⁅ξ, ·⁆ = 0}` onto `𝔪`, and that every `ξ ∈ 𝔨_ν` with `P ξ = 0` lies in the
image of `𝔨`. Then the induced form on `G ×_K N` is nondegenerate at `[1, n]`: on
`𝔤 × 𝔪* × V` the form `B_n` is the model tensor
`((ξ, a, v), (ζ, b, w)) ↦ b(P ξ) - a(P ζ) + ν ⁅ξ, ζ⁆ + β(v, w)`, whose null space is
`(𝔨_ν ∩ ker P) × 0 × 0`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one {n : N}
    (hn : ∀ k : K, k • n = n) {𝔪 V : Type*} [AddCommGroup 𝔪] [Module ℝ 𝔪] [AddCommGroup V]
    [Module ℝ V] (e : TangentSpace IN n ≃ₗ[ℝ] Module.Dual ℝ 𝔪 × V)
    (P : GroupLieAlgebra I G →ₗ[ℝ] 𝔪) {β : LinearMap.BilinForm ℝ V} (hβ : β.SeparatingLeft)
    (hdf : ∀ (u : TangentSpace IN n) (ξ : GroupLieAlgebra I G),
      mvfderiv IN f n u ξ = (e u).1 (P ξ))
    (hσ : ∀ u w : TangentSpace IN n, σ.eval₂ n u w = β (e u).2 (e w).2)
    (hP : ∀ m : 𝔪, ∃ κ : GroupLieAlgebra I G,
      (∀ ζ : GroupLieAlgebra I G, f n (⁅κ, ζ⁆ : GroupLieAlgebra I G) = 0) ∧ P κ = m)
    (hK : ∀ ξ : GroupLieAlgebra I G,
      (∀ ζ : GroupLieAlgebra I G, f n (⁅ξ, ζ⁆ : GroupLieAlgebra I G) = 0) → P ξ = 0 →
      ∃ κ : GroupLieAlgebra 𝓘(ℝ, F) K, K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ = ξ) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt
        (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))
          (K.toRightTranslation 1, n))).Nondegenerate := by
  refine (nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff_of_forall_smul_eq
    hn).2 fun ξ u h ↦ ?_
  have hkir (ζ ζ' : GroupLieAlgebra I G) :
      Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) ζ ζ' =
        f n (⁅ζ, ζ'⁆ : GroupLieAlgebra I G) :=
    (Module.Dual.kirillovForm_apply _ ζ ζ').trans (congrFun (ContinuousLinearMap.coe_coe (f n)) _)
  -- Pairing with `(0, w)`: `(e w).1 (P ξ) + β((e u).2, (e w).2) = 0` for every `w`.
  have hw (w : TangentSpace IN n) : (e w).1 (P ξ) + β (e u).2 (e w).2 = 0 := by
    have h' := h 0 w
    rw [hdf, hdf, hσ] at h'
    simp only [map_zero, sub_zero, add_zero] at h'
    linear_combination h'
  -- Pairing with `(ζ, 0)`: `ν ⁅ξ, ζ⁆ = (e u).1 (P ζ)` for every `ζ`.
  have hζ (ζ : GroupLieAlgebra I G) : f n (⁅ξ, ζ⁆ : GroupLieAlgebra I G) = (e u).1 (P ζ) := by
    have h' := h ζ 0
    rw [hdf, hdf, hσ] at h'
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, LinearMap.zero_apply, zero_sub,
      add_zero] at h'
    linear_combination h' - hkir ξ ζ
  have hPξ : P ξ = 0 := (Module.forall_dual_apply_eq_zero_iff ℝ (P ξ)).1 fun b ↦ by
    simpa using hw (e.symm (b, 0))
  have hv : (e u).2 = 0 := hβ _ fun y ↦ by simpa using hw (e.symm (0, y))
  -- `(e u).1` vanishes on `P(𝔨_ν) = 𝔪`, since `ν ⁅ξ, κ⁆ = -ν ⁅κ, ξ⁆ = 0` for `κ ∈ 𝔨_ν`.
  have ha : (e u).1 = 0 := LinearMap.ext fun m ↦ by
    obtain ⟨κ, hκ, rfl⟩ := hP m
    have hskew := LinearMap.IsAlt.neg (Module.Dual.isAlt_kirillovForm (L := GroupLieAlgebra I G)
      (f n : E →ₗ[ℝ] ℝ)) κ ξ
    rw [LinearMap.zero_apply, ← hζ κ]
    linear_combination -hkir ξ κ - hskew - hkir κ ξ - hκ ξ
  have hu : u = 0 := e.injective (by rw [map_zero]; exact Prod.ext ha hv)
  subst hu
  exact ⟨rfl, hK ξ (fun ζ ↦ by simp [hζ]) hPξ⟩

/-- **The Marle–Guillemin–Sternberg model is nondegenerate near its base point.** Under the
hypotheses of `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one`,
the induced form on `G ×_K N` is nondegenerate at every point of a neighbourhood of `[1, n]`. -/
theorem eventually_nondegenerate_bilinFormAt_balancedProductInducedForm {n : N}
    (hn : ∀ k : K, k • n = n) {𝔪 V : Type*} [AddCommGroup 𝔪] [Module ℝ 𝔪] [AddCommGroup V]
    [Module ℝ V] (e : TangentSpace IN n ≃ₗ[ℝ] Module.Dual ℝ 𝔪 × V)
    (P : GroupLieAlgebra I G →ₗ[ℝ] 𝔪) {β : LinearMap.BilinForm ℝ V} (hβ : β.SeparatingLeft)
    (hdf : ∀ (u : TangentSpace IN n) (ξ : GroupLieAlgebra I G),
      mvfderiv IN f n u ξ = (e u).1 (P ξ))
    (hσ : ∀ u w : TangentSpace IN n, σ.eval₂ n u w = β (e u).2 (e w).2)
    (hP : ∀ m : 𝔪, ∃ κ : GroupLieAlgebra I G,
      (∀ ζ : GroupLieAlgebra I G, f n (⁅κ, ζ⁆ : GroupLieAlgebra I G) = 0) ∧ P κ = m)
    (hK : ∀ ξ : GroupLieAlgebra I G,
      (∀ ζ : GroupLieAlgebra I G, f n (⁅ξ, ζ⁆ : GroupLieAlgebra I G) = 0) → P ξ = 0 →
      ∃ κ : GroupLieAlgebra 𝓘(ℝ, F) K, K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I κ = ξ) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ∀ᶠ y in nhds (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × N))
        (K.toRightTranslation 1, n)),
      ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt y).Nondegenerate := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  exact (SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt _).mem_nhds
    (nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one hn e P hβ hdf hσ hP hK)

end TauCeti.CotangentBundle
