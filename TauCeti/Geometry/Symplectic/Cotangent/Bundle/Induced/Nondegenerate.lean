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
* **Transport along the orbit.** `Ω` is `G`-invariant and `[g, n] = g • [1, n]`, so nondegeneracy
  at `[1, n]` gives nondegeneracy at every `[g, n]`
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk`).
* **The Marle–Guillemin–Sternberg tensor.** In the local model `G ×_H (𝔪* × V)` of a Hamiltonian
  action near an orbit, the form at the base point `[1, 0, 0]` is

  `Ω((ξ, a, v), (ζ, b, w)) = b(ξ_𝔪) - a(ζ_𝔪) + ν ⁅ξ, ζ⁆ + ω_V(v, w)`.

  For a projection `π : 𝔤 → P` mapping the coadjoint stabilizer `𝔤_ν` onto `P` and a
  nondegenerate `ω_V`, the radical of this tensor is `(𝔤_ν ∩ ker π) × 0 × 0`
  (`Module.Dual.forall_kirillovForm_add_eq_zero_iff`). In the model `π` is the projection onto
  `𝔪` along `𝔥 ⊕ 𝔮`, where `𝔤_ν = 𝔥 ⊕ 𝔪`, so the radical is `𝔥 × 0 × 0`, the orbit directions
  of `H` at a fixed point. Hence the model form is nondegenerate along the zero orbit
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod`):
  if `f n = ν`, the tangent space at `n` is identified with `P* × V` so that `df_n` and `σ_n` take
  the form above, `n` is a zero of the fundamental vector fields of `K`, and `𝔤_ν ∩ ker π` is the
  image of `𝔨`, then the induced form is nondegenerate at every `[g, n]`.

## Main results

* `Module.Dual.forall_kirillovForm_add_eq_zero_iff`: the radical of the Marle–Guillemin–Sternberg
  tensor.
* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff`: the
  induced form is nondegenerate at `[1, n]` exactly when the radical of the induced form on
  `G × N` at `(1, n)` consists of orbit directions of `K`.
* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk`: then it is
  nondegenerate at every `[g, n]`.
* `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod`:
  nondegeneracy along the zero orbit of the Marle–Guillemin–Sternberg model.

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

namespace Module.Dual

variable {𝕜 L P V : Type*} [Field 𝕜] [LieRing L] [LieAlgebra 𝕜 L] [AddCommGroup P] [Module 𝕜 P]
  [AddCommGroup V] [Module 𝕜 V] (ν : Dual 𝕜 L) {π : L →ₗ[𝕜] P} {β : LinearMap.BilinForm 𝕜 V}

/-- **The radical of the Marle–Guillemin–Sternberg tensor.** Let `ν ∈ 𝔤*`, let `π : 𝔤 → P` map
the coadjoint stabilizer `𝔤_ν` onto `P`, and let `β` be a bilinear form on `V` with trivial left
radical. Then `(ξ, a, v) ∈ 𝔤 × P* × V` pairs to zero with every `(ζ, b, w)` under

`b(π ξ) - a(π ζ) + ν ⁅ξ, ζ⁆ + β(v, w)`

exactly when `ξ ∈ 𝔤_ν`, `π ξ = 0`, `a = 0` and `v = 0`. -/
theorem forall_kirillovForm_add_eq_zero_iff (hβ : β.SeparatingLeft)
    (hπ : (lieAnnihilator 𝕜 L ν).toSubmodule.map π = ⊤) (ξ : L) (a : Dual 𝕜 P) (v : V) :
    (∀ (ζ : L) (b : Dual 𝕜 P) (w : V),
        b (π ξ) - a (π ζ) + ν.kirillovForm ξ ζ + β v w = 0) ↔
      ξ ∈ lieAnnihilator 𝕜 L ν ∧ π ξ = 0 ∧ a = 0 ∧ v = 0 := by
  -- An element of the stabilizer pairs to zero with every `ξ` under the Kirillov form.
  have hstab {ζ : L} (hζ : ζ ∈ lieAnnihilator 𝕜 L ν) (ξ : L) : ν.kirillovForm ξ ζ = 0 := by
    rw [kirillovForm_apply, ← lie_skew, map_neg, ← kirillovForm_apply,
      kirillovForm_eq_neg_lie_apply, (mem_lieAnnihilator 𝕜 L).1 hζ, LinearMap.zero_apply,
      neg_zero, neg_zero]
  constructor
  · intro h
    have hv : v = 0 := hβ v fun w ↦ by simpa using h 0 0 w
    have hπξ : π ξ = 0 :=
      (forall_dual_apply_eq_zero_iff 𝕜 (π ξ)).1 fun b ↦ by simpa using h 0 b 0
    -- `a` vanishes on `π 𝔤_ν = P`, since `ν ⁅ξ, ζ⁆ = 0` for `ζ ∈ 𝔤_ν`.
    have ha : a = 0 := by
      refine LinearMap.ext fun p ↦ ?_
      obtain ⟨ζ, hζ, rfl⟩ : p ∈ (lieAnnihilator 𝕜 L ν).toSubmodule.map π := hπ ▸ Submodule.mem_top
      simpa [hπξ, hv, hstab hζ ξ] using h ζ 0 0
    refine ⟨?_, hπξ, ha, hv⟩
    rw [← LieSubalgebra.mem_toSubmodule, ← ker_kirillovForm, LinearMap.mem_ker]
    exact LinearMap.ext fun ζ ↦ by simpa [hπξ, ha, hv] using h ζ 0 0
  · rintro ⟨hξ, hπξ, rfl, rfl⟩ ζ b w
    have h₀ : ν.kirillovForm ξ ζ = 0 := by
      rw [← LieSubalgebra.mem_toSubmodule, ← ker_kirillovForm, LinearMap.mem_ker] at hξ
      rw [hξ, LinearMap.zero_apply]
    simp [hπξ, h₀]

end Module.Dual

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
  set Ω := balancedProductInducedForm I G σ hf hfK hσK hμ
  set y := BalancedProduct.mk K (K.toRightTranslation 1) n
  -- `BilinForm.Nondegenerate` unfolds to `LinearMap.Nondegenerate` only definitionally, which `rw`
  -- does not see through, so the criterion for reflexive forms is stated with `show`.
  rw [show (Ω.bilinFormAt y).Nondegenerate ↔ (Ω.bilinFormAt y).SeparatingLeft from
      LinearMap.IsRefl.nondegenerate_iff_separatingLeft (SmoothForm.isAlt_bilinFormAt Ω y).isRefl,
    ← BalancedProduct.ker_mfderiv_quotientMk_rightTranslation]
  constructor
  · intro h v hv
    refine LinearMap.mem_ker.2 (h _ fun Y ↦ ?_)
    obtain ⟨w, rfl⟩ := hsurj Y
    rw [SmoothForm.bilinFormAt_apply]
    exact (eval₂_balancedProductInducedForm_mfderiv_one n v w).trans (hv w)
  · intro h X hX
    obtain ⟨v, rfl⟩ := hsurj X
    refine LinearMap.mem_ker.1 (h v fun w ↦ ?_)
    rw [← eval₂_balancedProductInducedForm_mfderiv_one (hf := hf) (hfK := hfK) (hσK := hσK)
      (hμ := hμ) n v w, ← SmoothForm.bilinFormAt_apply]
    exact hX _

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
  let _ := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  set Ω := balancedProductInducedForm I G σ hf hfK hσK hμ
  set y := BalancedProduct.mk K (K.toRightTranslation 1) n
  have h₁ := (nondegenerate_bilinFormAt_balancedProductInducedForm_mk_one_iff (hf := hf)
    (hfK := hfK) (hσK := hσK) (hμ := hμ) n).2 hn
  -- Left translation by `g` preserves `Ω`, sends `[1, n]` to `[g, n]` and is a diffeomorphism, so
  -- its differential at `[1, n]` is onto.
  have hy : g • y = BalancedProduct.mk K (K.toRightTranslation g) n := by
    rw [BalancedProduct.smul_mk_toRightTranslation, mul_one]
  have hsurj : Surjective (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) (fun x ↦ g • x) y) := by
    obtain ⟨e, he⟩ := (Diffeomorph.smul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) ∞ g
      (M := BalancedProduct K K.RightTranslation N)).isInvertible_mfderiv (x := y) (by simp)
    intro X
    obtain ⟨v, rfl⟩ := e.surjective X
    -- `Diffeomorph.smul I _ ∞ g` is `x ↦ g • x` by definition.
    exact ⟨v, by rw [← ContinuousLinearEquiv.coe_coe, he]; rfl⟩
  have hΩ (v w : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) y) :
      Ω.eval₂ (g • y)
        (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) (fun x ↦ g • x) y v)
        (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) (fun x ↦ g • x) y w) =
      Ω.eval₂ y v w := by
    have h := congrArg (fun φ ↦ SmoothBundleForm.eval₂ φ y v w)
      (mpullback_smul_balancedProductInducedForm (hf := hf) (hfK := hfK) (hσK := hσK)
        (hμ := hμ) g)
    simp only [SmoothForm.eval₂_mpullback] at h
    exact h
  -- `BilinForm.Nondegenerate` unfolds to `LinearMap.Nondegenerate` only definitionally, which `rw`
  -- does not see through, so the criterion for reflexive forms is stated with `show`.
  rw [← hy, show (Ω.bilinFormAt (g • y)).Nondegenerate ↔ (Ω.bilinFormAt (g • y)).SeparatingLeft
    from LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (SmoothForm.isAlt_bilinFormAt Ω _).isRefl]
  rw [show (Ω.bilinFormAt y).Nondegenerate ↔ (Ω.bilinFormAt y).SeparatingLeft from
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft (SmoothForm.isAlt_bilinFormAt Ω _).isRefl]
    at h₁
  intro X hX
  obtain ⟨v, rfl⟩ := hsurj X
  rw [h₁ v fun w ↦ ?_, map_zero]
  rw [SmoothForm.bilinFormAt_apply, ← hΩ, ← SmoothForm.bilinFormAt_apply]
  exact hX _

/-- **The Marle–Guillemin–Sternberg model is nondegenerate along its zero orbit.** Let `n ∈ N` be
a zero of every fundamental vector field of `K`, with `f n = ν`. Suppose the tangent space at `n`
is identified with `P* × V` by `e` so that

`df_n u ζ = (e u).1 (π ζ)` and `σ(u, u') = β((e u).2, (e u').2)`,

where `β` has trivial left radical, and suppose `π : 𝔤 → P` maps the coadjoint stabilizer `𝔤_ν`
onto `P` with `𝔤_ν ∩ ker π` contained in the image of `𝔨`. Then the induced form on `G ×_K N` is
nondegenerate at every `[g, n]`. For the model `G ×_H (𝔪* × V)`, with `n = (0, 0)`,
`f (η, v) = ν + η + μ_V v` and `π` the projection onto `𝔪` along `𝔥 ⊕ 𝔮`, these are the
conditions `𝔤_ν = 𝔥 ⊕ 𝔪` and `𝔥 ⊆ 𝔤_ν`. -/
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
  · rw [InfinitesimalAction.fundamental_prod, InfinitesimalAction.prod_apply, prodVectorField_fst,
      InfinitesimalAction.fundamental_apply,
      Subgroup.RightTranslation.fundamentalVectorField_eq_mulInvariantVectorField_neg,
      Equiv.symm_apply_apply, mulInvariantVectorField_one, map_neg, neg_neg]
    exact hξ
  · rw [InfinitesimalAction.fundamental_prod, InfinitesimalAction.prod_apply, prodVectorField_snd,
      InfinitesimalAction.fundamental_apply]
    -- The second component of `(K.toRightTranslation 1, n)` is `n` only definitionally.
    change fundamentalVectorField IN (-ξ) n = v.2
    exact (hfix _).trans hv₂.symm

end TauCeti.CotangentBundle
