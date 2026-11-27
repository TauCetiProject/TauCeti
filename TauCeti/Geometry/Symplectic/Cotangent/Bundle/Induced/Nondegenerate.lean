/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct

/-!
# Nondegeneracy of the induced form on `G ×_K N`

Let `G` be a finite-dimensional real Lie group with Lie algebra `𝔤`, let `K` be a closed subgroup
acting on a manifold `N` with a `K`-invariant two-form `σ`, and let `f : N → 𝔤*` be
`K`-equivariant, with restriction to `𝔨` a moment map of the action of `K` on `(N, σ)`. The
induced form `Ω` on the balanced product `G ×_K N`
(`TauCeti.CotangentBundle.balancedProductInducedForm`) is the descent of `-d⟨f, θ⟩ + pr₂^* σ`.
This file gives a criterion for `Ω` to be nondegenerate along the `G`-orbit of a point `[1, n]`.

* **The radical criterion.** At `(1, n)` the induced form on `G × N` pairs `(v, u)` and
  `(w, u')` to `B((v, u), (w, u')) = df_n u' v - df_n u w + (f n) ⁅v, w⁆ + σ(u, u')`. Since the
  projection `G × N → G ×_K N` is a submersion whose differential has kernel the orbit directions
  of `K`, the descended form is nondegenerate at `[1, n]` exactly when the radical of `B` consists
  of orbit directions
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff`).
* **`G`-invariance.** `Ω` is `G`-invariant, so it is nondegenerate at `g • y` exactly when it is
  nondegenerate at `y`
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_smul_iff`). As
  `[g, n] = g • [1, n]`, nondegeneracy at `[1, n]` gives nondegeneracy at every `[g, n]`
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk`).
* **Marle–Guillemin–Sternberg coordinates.** In the local model `G ×_H (𝔪* × V)` of a Hamiltonian
  action near an orbit, the form at the base point `[1, 0, 0]` is

  `Ω((ξ, a, v), (ζ, b, w)) = b(ξ_𝔪) - a(ζ_𝔪) + ν ⁅ξ, ζ⁆ + ω_V(v, w)`.

  For a projection `π : 𝔤 → P` mapping the coadjoint stabilizer `𝔤_ν` onto `P` and a
  nondegenerate `ω_V`, the radical of this tensor is `(𝔤_ν ∩ ker π) × 0 × 0`
  (`Module.Dual.forall_kirillovForm_add_eq_zero_iff`). This reduces nondegeneracy along the orbit
  to conditions in these coordinates
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod`):
  if `f n = ν`, the tangent space at `n` is identified with `P* × V` so that `df_n` and `σ_n` take
  the form above, `n` is a zero of the fundamental vector fields of `K`, and `𝔤_ν ∩ ker π` is
  contained in the image of `𝔨`, then the induced form is nondegenerate at every `[g, n]`. For the
  model, `π` is the projection onto `𝔪` along `𝔥 ⊕ 𝔮`, where `𝔤_ν = 𝔥 ⊕ 𝔪`; then `𝔤_ν ∩ ker π`
  is `𝔥`, the orbit directions of `H` at a fixed point, so the model satisfies these conditions
  once it is instantiated.

## Main results

* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff`: the
  induced form is nondegenerate at `[1, n]` exactly when the radical of the induced form on
  `G × N` at `(1, n)` consists of orbit directions of `K`.
* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_smul_iff`:
  nondegeneracy of the induced form at a point is `G`-invariant.
* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk`: under the
  radical criterion the induced form is nondegenerate at every `[g, n]`.
* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod`:
  a criterion for nondegeneracy along the orbit of `[1, n]` in Marle–Guillemin–Sternberg
  coordinates.

## References

* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific J. Math.
  181 (1997), 201–229, §2 (the local model `G ×_H (𝔪* × V)` and its nondegeneracy).
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Mathematical Physics Studies 6, Reidel, 1984, 161–175.
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
-/

public section

noncomputable section

open Function Manifold TauCeti TauCeti.Manifold Module
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
  [I.Boundaryless] [IsClosed (K : Set G)] [IN.Boundaryless] [T2Space N]
  {hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f}
  {hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹}
  {hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ}
  {hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
    fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap}

/-- **The radical criterion for the induced form on `G ×_K N`.** The induced form is
nondegenerate at `[1, n]` exactly when every tangent vector `(v, u)` of `G × N` at `(1, n)` with
`df_n u' v - df_n u w + (f n) ⁅v, w⁆ + σ(u, u') = 0` for all `(w, u')` is an orbit direction of
the action `k • (g, n) = (g k⁻¹, k • n)` of `K`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff (n : N) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt
        (BalancedProduct.mk K (K.toRightTranslation 1) n)).Nondegenerate ↔
      ∀ v : TangentSpace (I.prod IN) (K.toRightTranslation 1, n),
        (∀ w : TangentSpace (I.prod IN) (K.toRightTranslation 1, n),
          mvfderiv IN f n w.2 v.1 - mvfderiv IN f n v.2 w.1 +
            Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) v.1 w.1 +
            σ.eval₂ n v.2 w.2 = 0) →
        v ∈ (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IN)
          (K.RightTranslation × N)).orbitTangent (K.toRightTranslation 1, n) := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have hq := BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K) (Z := N) (I := I)
    (IZ := IN) (F := F)
  have hsurj := hq.surjective_mfderiv (by simp) (K.toRightTranslation 1, n)
  -- The radical of the pullback to `G × N` is the preimage of that of the induced form, so the
  -- latter vanishes exactly when the former is the kernel of the projection's differential.
  have hker := SmoothTwoForm.ker_bilinFormAt_mpullback hq.contMDiff
    (balancedProductInducedForm I G σ hf hfK hσK hμ) hsurj
  rw [LinearMap.BilinForm.Nondegenerate,
    (SmoothForm.isAlt_bilinFormAt _ _).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot,
    ← (Submodule.comap_injective_of_surjective hsurj).eq_iff, Submodule.comap_bot, ← hker,
    ← BalancedProduct.ker_mfderiv_quotientMk_rightTranslation,
    le_antisymm_iff, and_iff_left (hker ▸ Submodule.comap_mono bot_le)]
  refine forall_congr' fun v ↦ imp_congr_left ?_
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, SmoothForm.bilinFormAt_apply,
    SmoothForm.eval₂_mpullback, eval₂_balancedProductInducedForm_mfderiv_one, LinearMap.zero_apply]

/-- **Nondegeneracy of the induced form on `G ×_K N` is `G`-invariant.** The induced form is
nondegenerate at `g • y` exactly when it is nondegenerate at `y`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_smul_iff (g : G)
    (y : BalancedProduct K K.RightTranslation N) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt (g • y)).Nondegenerate ↔
      ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt y).Nondegenerate := by
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have := ContMDiffSMul.contMDiffConstSMul I (I' := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)))
    (n := ∞) (G := G) (M := BalancedProduct K K.RightTranslation N)
  -- Left translation by `g` preserves the induced form and has bijective differential.
  have hd : Bijective (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) (fun x ↦ g • x) y) :=
    ⟨ContMDiffConstSMul.injective_mfderiv_const_smul (n := ∞) (by simp) g y,
      fun w ↦ ⟨_, ContMDiffConstSMul.mfderiv_smul_mfderiv_inv_smul (n := ∞) (by simp) g y rfl w⟩⟩
  conv_rhs => rw [← mpullback_smul_balancedProductInducedForm (hf := hf) (hfK := hfK)
    (hσK := hσK) (hμ := hμ) g]
  exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_iff _ _ hd).symm

/-- **The induced form is nondegenerate along the orbit of `[1, n]`.** If the radical of the
induced form on `G × N` at `(1, n)` consists of orbit directions of `K`, the induced form on
`G ×_K N` is nondegenerate at every point `[g, n]`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk {n : N}
    (hn : ∀ v : TangentSpace (I.prod IN) (K.toRightTranslation 1, n),
      (∀ w : TangentSpace (I.prod IN) (K.toRightTranslation 1, n),
        mvfderiv IN f n w.2 v.1 - mvfderiv IN f n v.2 w.1 +
          Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) v.1 w.1 +
          σ.eval₂ n v.2 w.2 = 0) →
      v ∈ (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IN)
        (K.RightTranslation × N)).orbitTangent (K.toRightTranslation 1, n))
    (g : G) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt
        (BalancedProduct.mk K (K.toRightTranslation g) n)).Nondegenerate := by
  -- `[g, n] = g • [1, n]`.
  have h := (nondegenerate_bilinFormAt_balancedProductInducedForm_smul_iff (hf := hf) (hfK := hfK)
    (hσK := hσK) (hμ := hμ) g _).2
    ((nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff n).2 hn)
  rwa [BalancedProduct.smul_mk_toRightTranslation, mul_one] at h

/-- **Nondegeneracy along the orbit of `[1, n]` in Marle–Guillemin–Sternberg coordinates.** Let
`n ∈ N` be a zero of every fundamental vector field of `K`, with `f n = ν`. Suppose the tangent
space at `n` is identified with `P* × V` by `e` so that

`df_n u ζ = (e u).1 (π ζ)` and `σ(u, u') = β((e u).2, (e u').2)`,

where `β` has trivial left radical, and suppose `π : 𝔤 → P` maps the coadjoint stabilizer `𝔤_ν`
onto `P` with `𝔤_ν ∩ ker π` contained in the image of `𝔨`. Then the induced form on `G ×_K N` is
nondegenerate at every `[g, n]`. For the model `G ×_H (𝔪* × V)`, with `n = (0, 0)`,
`f (η, v) = ν + η + μ_V v` and `π` the projection onto `𝔪` along `𝔥 ⊕ 𝔮`, these hypotheses become
the conditions `𝔤_ν = 𝔥 ⊕ 𝔪` and `𝔥 ⊆ 𝔤_ν`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod
    {P V : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup V] [Module ℝ V] {n : N}
    {ν : Dual ℝ (GroupLieAlgebra I G)} (hfn : (f n : E →ₗ[ℝ] ℝ) = ν)
    {π : GroupLieAlgebra I G →ₗ[ℝ] P} {β : LinearMap.BilinForm ℝ V}
    (e : TangentSpace IN n ≃ₗ[ℝ] Dual ℝ P × V)
    (hD : ∀ (u : TangentSpace IN n) (ζ : GroupLieAlgebra I G),
      mvfderiv IN f n u ζ = (e u).1 (π ζ))
    (hσ : ∀ u u' : TangentSpace IN n, σ.eval₂ n u u' = β (e u).2 (e u').2)
    (hβ : β.SeparatingLeft)
    (hπ : (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule.map π = ⊤)
    (hker : ∀ ζ ∈ lieAnnihilator ℝ (GroupLieAlgebra I G) ν, π ζ = 0 →
      ζ ∈ LinearMap.range (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap)
    (hfix : ∀ ξ : GroupLieAlgebra 𝓘(ℝ, F) K, fundamentalVectorField IN ξ n = 0) (g : G) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ((balancedProductInducedForm I G σ hf hfK hσK hμ).bilinFormAt
        (BalancedProduct.mk K (K.toRightTranslation g) n)).Nondegenerate := by
  refine nondegenerate_bilinFormAt_balancedProductInducedForm_mk (fun v hv ↦ ?_) g
  -- Read the radical condition in the coordinates `𝔤 × P* × V`.
  have hrad := (Module.Dual.forall_kirillovForm_add_eq_zero_iff ν hβ hπ v.1 (e v.2).1
    (e v.2).2).1 fun ζ b w ↦ by
      have h := hv (ζ, e.symm (b, w))
      -- The components of `(ζ, e.symm (b, w))` are `ζ` and `e.symm (b, w)` only after unfolding
      -- the product tangent space, so they are exposed with `change`.
      change mvfderiv IN f n (e.symm (b, w)) v.1 - mvfderiv IN f n v.2 ζ +
        Module.Dual.kirillovForm (L := GroupLieAlgebra I G) (f n : E →ₗ[ℝ] ℝ) v.1 ζ +
        σ.eval₂ n v.2 (e.symm (b, w)) = 0 at h
      rw [hD (e.symm (b, w)) v.1, hD v.2 ζ, hσ v.2 (e.symm (b, w)), LinearEquiv.apply_symm_apply]
        at h
      subst hfn
      exact h
  obtain ⟨hstab, hπv, ha, hu⟩ := hrad
  have hv₂ : v.2 = 0 := e.map_eq_zero_iff.1 (Prod.ext ha hu)
  obtain ⟨ξ, hξ⟩ := hker v.1 hstab hπv
  -- `v = (ι ξ, 0)` is the orbit direction of `-ξ`.
  refine (InfinitesimalAction.mem_orbitTangent_iff _ _).2 ⟨-ξ, Prod.ext ?_ ?_⟩
  · simp only [InfinitesimalAction.fundamental_prod, InfinitesimalAction.prod_apply,
      prodVectorField_fst, InfinitesimalAction.fundamental_apply,
      Subgroup.RightTranslation.fundamentalVectorField_eq_mulInvariantVectorField_neg]
    -- The tangent space depends on the base point, so `simp` cannot rewrite it; `rw` can.
    rw [Equiv.symm_apply_apply, mulInvariantVectorField_one, map_neg, neg_neg]
    exact hξ
  · rw [InfinitesimalAction.fundamental_prod, InfinitesimalAction.prod_apply, prodVectorField_snd,
      InfinitesimalAction.fundamental_apply]
    -- The second component of `(K.toRightTranslation 1, n)` is `n` only definitionally.
    change fundamentalVectorField IN (-ξ) n = v.2
    exact (hfix _).trans hv₂.symm

end TauCeti.CotangentBundle
