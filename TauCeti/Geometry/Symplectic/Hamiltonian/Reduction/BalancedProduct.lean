/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ShiftingForm

/-!
# Reduced forms on the balanced product `G ×_{G_c} μ⁻¹(c)`

Let a Lie group `G` act by symplectomorphisms of `(M, σ)` with moment map `μ : M → 𝔤*`, and fix
`c ∈ 𝔤*` with coadjoint stabilizer `G_c` and coadjoint orbit `O = G ⧸ G_c`, carrying the
Kirillov–Kostant–Souriau form `ω_KKS` (`Module.Dual.coadjointOrbitForm`). Orbit reduction
compares the reduced space `Q = μ⁻¹(c) ⧸ G_c` with the balanced product

`Y_O = G ×_{G_c} μ⁻¹(c)`

of `G` and the level, the quotient of `G × μ⁻¹(c)` by `h • (g, z) = (g h⁻¹, h • z)`
(`TauCeti.Geometry.Lie.Subgroup.BalancedProduct`). Its point `[g, z]` records the point `g • z`
of `μ⁻¹(O)` together with the coset `g G_c`. It has three maps:

* `q_Y : Y_O → Q`, `[g, z] ↦ [z]` (`TauCeti.BalancedProduct.orbitProj`), a surjective submersion
  (`TauCeti.BalancedProduct.isSubmersion_orbitProj_rightTranslation`) whose fibres are the
  `G`-orbits (`TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`);
* `i_Y : Y_O → M`, `[g, z] ↦ g • z` (`TauCeti.BalancedProduct.liftRightTranslation`);
* `pr_Y : Y_O → O`, `[g, z] ↦ g G_c` (`TauCeti.BalancedProduct.proj`).

This file proves that a two-form `η` on `Q` is the reduced form, `π^* η = i^* σ` for the orbit
projection `π` and the inclusion `i` of the level, exactly when

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`

(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub`). Both
sides are compared on `G × μ⁻¹(c)`, after pulling back along the submersion `(g, z) ↦ [g, z]`.
There `q_Y^* η` becomes `pr_Z^* (π^* η)`, while `i_Y^* σ - pr_Y^* ω_KKS` becomes `pr_Z^* (i^* σ)`
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_quotientMk_liftRightTranslation_sub_proj`): by the
shifting identity `a^* σ = pr_G^* σ_c + pr_Z^* (i^* σ)` for the action map `a(g, z) = g • z`
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`), since
`ω_KKS` pulls back to the left-invariant Kirillov form `σ_c` on `G`.

These statements hold for any manifold `Z` with a smooth action of `G_c`, any smooth
`G_c`-equivariant map `ι : Z → M` into the level along which the moment cocycle vanishes, and any
manifold structure on `Z ⧸ G_c` for which the orbit projection is a submersion. For a
coadjoint-equivariant moment map with `c` a regular value and `G_c` acting freely on the level,
the Marsden–Weinstein–Meyer theorem then says that `Q` carries a unique symplectic form `η` with
`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`
(`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_orbitProj_eq_sub`).
Consequently the two-form `i_Y^* σ - pr_Y^* ω_KKS` on `Y_O` is closed, and its null space at each
point is the kernel of the differential of `q_Y`
(`IsEquivariantMomentMap.isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv`):
the reduced space is the quotient of `Y_O` by the null foliation of this form.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm`.

* `IsMomentMap.mpullback_quotientMk_liftRightTranslation_sub_proj`: the form
  `i_Y^* σ - pr_Y^* ω_KKS` pulls back to `pr_Z^* (ι^* σ)` on `G × Z`.
* `IsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub`:
  `π^* η = ι^* σ` exactly when `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`.
* `IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_orbitProj_eq_sub`: the reduced
  space carries a unique symplectic form `η` with `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`.
* `IsEquivariantMomentMap.isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv`:
  `i_Y^* σ - pr_Y^* ω_KKS` is closed, with null spaces the kernels of `d q_Y`.

## References

* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Sections 6.1 and 6.4 (orbit reduction and the shifting theorem).
* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Section 1.2 (orbit reduction
  through `G ×_{G_c} μ⁻¹(c)`).
-/

public section

noncomputable section

open Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  Lie.isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)}

namespace IsMomentMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F ((Lie.coadjointRepresentation ℝ I G).stabilizer c)]
  [LieGroup 𝓘(ℝ, F) ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c) G]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  [MulAction ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z]
  {ι : Z →ₑ[((↑) : (Lie.coadjointRepresentation ℝ I G).stabilizer c → G)] M}

/-- **The shifting identity on the balanced product, read on `G × Z`.** Let `G` act by
symplectomorphisms of `(M, σ)` with moment map `μ`, and let `ι : Z → M` be a smooth
`G_c`-equivariant map into the level `μ⁻¹(c)` along which the moment cocycle vanishes. On
`Y_O = G ×_{G_c} Z`, the form `i_Y^* σ - pr_Y^* ω_KKS`, for `i_Y [g, z] = g • ι z` and the
projection `pr_Y [g, z] = g G_c` onto the coadjoint orbit, pulls back along `(g, z) ↦ [g, z]` to
`pr_Z^* (ι^* σ)`. -/
theorem mpullback_quotientMk_liftRightTranslation_sub_proj
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hc : ∀ z, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ (ι z) = 0) :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
      (F := F)
    SmoothForm.mpullback _
        (BalancedProduct.isSubmersion_quotientMk_rightTranslation
          (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
          (F := F)).contMDiff
        (SmoothForm.mpullback (BalancedProduct.liftRightTranslation ι)
            (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := IZ) (F := F) hι) σ -
          SmoothForm.mpullback (BalancedProduct.proj Z Subgroup.RightTranslation.quotientMk_smul)
            (BalancedProduct.contMDiff_proj_rightTranslation
              (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I)
              (IZ := IZ) (F := F)) c.coadjointOrbitForm) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback ι hι σ) := by
  let _ := BalancedProduct.rightTranslationChartedSpace
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
  have := BalancedProduct.isManifold_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have hπ := (BalancedProduct.isSubmersion_quotientMk_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
    (F := F)).contMDiff
  have hfst : ContMDiff (I.prod IZ) I ∞
      ((Subgroup.toRightTranslation ((Lie.coadjointRepresentation ℝ I G).stabilizer c)).symm ∘
        Prod.fst) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).comp
      (contMDiff_fst (J := IZ) (N := Z))
  -- On representatives, `i_Y` is the action map `(g, z) ↦ g • ι z`, which pulls `σ` back to
  -- `pr_G^* σ_c + pr_Z^* (ι^* σ)`.
  have hi : SmoothForm.mpullback _ hπ (SmoothForm.mpullback _
      (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := IZ) (F := F) hι) σ) =
        SmoothForm.mpullback _ hfst c.leftInvariantKirillovForm +
          SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback ι hι σ) := by
    have hψ : ContMDiff (I.prod IZ) (I.prod IZ) ∞
        (Prod.map (Subgroup.toRightTranslation
          ((Lie.coadjointRepresentation ℝ I G).stabilizer c)).symm (id : Z → Z)) :=
      (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap
        (contMDiff_id (I := IZ) (M := Z))
    have ha : ContMDiff (I.prod IZ) I' ∞ fun p : G × Z ↦ p.1 • ι p.2 :=
      (contMDiff_fst (J := IZ) (N := Z)).smul (hι.comp (contMDiff_snd (I := I) (M := G)))
    rw [SmoothForm.mpullback_mpullback_of_comp_eq hπ _ hψ ha
      (funext fun x ↦ by
        rw [comp_apply, BalancedProduct.quotientMk_eq_mk_toRightTranslation,
          BalancedProduct.liftRightTranslation_mk]
        rfl) σ,
      h.mpullback_smul_eq_prod_leftInvariantKirillovForm hG hι hιc hc, prod_def, map_add,
      SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
    simp only [Prod.map_fst', Prod.map_snd', id_comp]
  -- On representatives, `pr_Y` is `(g, z) ↦ g G_c`, and `ω_KKS` pulls back to `σ_c` on `G`.
  have hp : SmoothForm.mpullback _ hπ (SmoothForm.mpullback _
      (BalancedProduct.contMDiff_proj_rightTranslation
        (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
        (F := F)) c.coadjointOrbitForm) =
        SmoothForm.mpullback _ hfst c.leftInvariantKirillovForm := by
    rw [SmoothForm.mpullback_mpullback_of_comp_eq hπ _ hfst
      c.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff
      (funext fun x ↦ by
        rw [comp_apply, BalancedProduct.quotientMk_eq_mk_toRightTranslation,
          BalancedProduct.proj_mk, Subgroup.RightTranslation.quotientMk_toRightTranslation]
        rfl), Module.Dual.mpullback_quotientMk_coadjointOrbitForm]
  rw [map_sub, hi, hp, add_sub_cancel_left]

variable {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace HQ] {JQ : ModelWithCorners ℝ EQ HQ}
  [ChartedSpace HQ
    (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)]
  [IsManifold JQ ∞
    (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)]

/-- **Reduced forms on the balanced product.** Let `G` act by symplectomorphisms of `(M, σ)` with
moment map `μ`, and let `ι : Z → M` be a smooth `G_c`-equivariant map into the level `μ⁻¹(c)`
along which the moment cocycle vanishes. Give `Z ⧸ G_c` a manifold structure for which the orbit
projection `π : Z → Z ⧸ G_c` is a submersion, such as the charts of the quotient manifold theorem
when `G_c` acts freely and properly on `Z`. A two-form `η` on `Z ⧸ G_c` descends `ι^* σ`, that is
`π^* η = ι^* σ`, exactly when on `Y_O = G ×_{G_c} Z` it satisfies

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`,

for `q_Y [g, z] = [z]`, `i_Y [g, z] = g • ι z` and the projection `pr_Y [g, z] = g G_c` onto the
coadjoint orbit with its Kirillov–Kostant–Souriau form. -/
theorem mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hc : ∀ z, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ (ι z) = 0)
    (hπZ : IsSubmersion IZ JQ ∞
      (Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)))
    (η : SmoothTwoForm JQ
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)) :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
      (F := F)
    SmoothForm.mpullback _ hπZ.contMDiff η = SmoothForm.mpullback ι hι σ ↔
      SmoothForm.mpullback BalancedProduct.orbitProj
          (BalancedProduct.isSubmersion_orbitProj_rightTranslation (I := I) (F := F)
            hπZ).contMDiff η =
        SmoothForm.mpullback (BalancedProduct.liftRightTranslation ι)
            (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := IZ) (F := F) hι) σ -
          SmoothForm.mpullback (BalancedProduct.proj Z Subgroup.RightTranslation.quotientMk_smul)
            (BalancedProduct.contMDiff_proj_rightTranslation
              (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I)
              (IZ := IZ) (F := F)) c.coadjointOrbitForm := by
  let _ := BalancedProduct.rightTranslationChartedSpace
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
  have := BalancedProduct.isManifold_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have hπ := BalancedProduct.isSubmersion_quotientMk_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have hq := BalancedProduct.isSubmersion_orbitProj_rightTranslation (I := I) (F := F) hπZ
  -- Both sides are compared after pulling back to `G × Z`, along the submersion `π` onto `Y_O`
  -- and then along the second projection.
  have hsnd : Injective (SmoothForm.mpullback (F := ℝ) (k := 2)
      (Prod.snd : ((Lie.coadjointRepresentation ℝ I G).stabilizer c).RightTranslation × Z → Z)
      (contMDiff_snd (I := I) (J := IZ))) :=
    SmoothForm.mpullback_injective_of_surjective contMDiff_snd Prod.snd_surjective fun x v ↦
      ⟨(0, v), by rw [mfderiv_snd]; rfl⟩
  have hqπ : SmoothForm.mpullback _ hπ.contMDiff
      (SmoothForm.mpullback BalancedProduct.orbitProj hq.contMDiff η) =
        SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback _ hπZ.contMDiff η) :=
    SmoothForm.mpullback_mpullback_of_comp_eq hπ.contMDiff hq.contMDiff
      (contMDiff_snd (I := I) (J := IZ)) hπZ.contMDiff
      (funext fun x ↦ BalancedProduct.orbitProj_mk x.1 x.2) η
  rw [← (SmoothForm.mpullback_injective_of_surjective hπ.contMDiff Quotient.mk_surjective
    (hπ.surjective_mfderiv (by simp))).eq_iff, hqπ,
    h.mpullback_quotientMk_liftRightTranslation_sub_proj hG hι hιc hc]
  exact hsnd.eq_iff.symm

end IsMomentMap

namespace IsEquivariantMomentMap

variable [I'.Boundaryless] [FiniteDimensional ℝ E'] [T2Space M] [ProperSMul G M]
  (h : σ.IsEquivariantMomentMap μ) {n : ℕ}
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)

/-- **The Marsden–Weinstein–Meyer reduced form on the balanced product.** Let a Lie group `G` act
smoothly and properly by symplectomorphisms on a symplectic manifold `(M, σ)`, with
coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ`, and let the coadjoint
stabilizer `G_c` act freely on the level `μ⁻¹(c)`. Then the reduced space `Q = μ⁻¹(c) ⧸ G_c`
carries a unique symplectic form `η` with

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`

on `Y_O = G ×_{G_c} μ⁻¹(c)`, for `q_Y [g, z] = [z]`, `i_Y [g, z] = g • z` and the projection
`pr_Y [g, z] = g G_c` onto the coadjoint orbit with its Kirillov–Kostant–Souriau form. It is the
reduced form `π^* η = i^* σ` of `existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`. -/
theorem existsUnique_isSymplectic_mpullback_orbitProj_eq_sub (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := d.chartedSpace
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (M := G) (I'' := I)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
      (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsSymplectic ∧
        SmoothForm.mpullback BalancedProduct.orbitProj
            (BalancedProduct.isSubmersion_orbitProj_rightTranslation (I := I) (F := F)
              (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d)).contMDiff η =
          SmoothForm.mpullback (BalancedProduct.liftRightTranslation (h.levelSubMulActionVal c))
              (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ))
                (F := F) (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff) σ -
            SmoothForm.mpullback (BalancedProduct.proj (h.levelSubMulAction c)
                Subgroup.RightTranslation.quotientMk_smul)
              (BalancedProduct.contMDiff_proj_rightTranslation
                (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c)
                (Z := h.levelSubMulAction c) (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F))
              c.coadjointOrbitForm := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have hemb := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal hemb
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  -- The reduced form is characterized on the balanced product by the previous equivalence.
  refine (existsUnique_congr fun η ↦ and_congr_right fun _ ↦
    h.toIsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub (F := F)
      (ι := h.levelSubMulActionVal c) hG hemb.contMDiff
      (fun z ↦ h.mem_levelSubMulAction.1 z.property) (fun z ↦ h.momentCocycle_eq_zero z)
      (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d) η).1 ?_
  exact h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg hn d hσ hG

/-- **The null foliation of `i_Y^* σ - pr_Y^* ω_KKS`.** With the hypotheses of the
Marsden–Weinstein–Meyer theorem, the two-form `i_Y^* σ - pr_Y^* ω_KKS` on
`Y_O = G ×_{G_c} μ⁻¹(c)`, for `i_Y [g, z] = g • z` and the projection `pr_Y [g, z] = g G_c` onto
the coadjoint orbit, is closed, and its null space at each point is the kernel of the differential
of `q_Y : Y_O → μ⁻¹(c) ⧸ G_c`, `[g, z] ↦ [z]`. So the reduced space is the quotient of `Y_O` by the
null foliation of this form, whose leaves are the fibres of `q_Y`, the `G`-orbits
(`TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`). -/
theorem isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := d.chartedSpace
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (M := G) (I'' := I)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
      (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
    (SmoothForm.mpullback (BalancedProduct.liftRightTranslation (h.levelSubMulActionVal c))
          (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ))
            (F := F) (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff) σ -
        SmoothForm.mpullback (BalancedProduct.proj (h.levelSubMulAction c)
            Subgroup.RightTranslation.quotientMk_smul)
          (BalancedProduct.contMDiff_proj_rightTranslation
            (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
            (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F))
          c.coadjointOrbitForm).IsClosed ∧
      ∀ y, LinearMap.ker ((SmoothForm.mpullback
          (BalancedProduct.liftRightTranslation (h.levelSubMulActionVal c))
            (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ))
              (F := F) (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff) σ -
          SmoothForm.mpullback (BalancedProduct.proj (h.levelSubMulAction c)
              Subgroup.RightTranslation.quotientMk_smul)
            (BalancedProduct.contMDiff_proj_rightTranslation
              (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c)
              (Z := h.levelSubMulAction c) (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F))
            c.coadjointOrbitForm).bilinFormAt y) =
        (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (Fin n → ℝ)))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) BalancedProduct.orbitProj y).ker := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let _ := BalancedProduct.rightTranslationChartedSpace
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
    𝓘(ℝ, Fin n → ℝ) F
  have := BalancedProduct.isManifold_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
    (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
  have hq := BalancedProduct.isSubmersion_orbitProj_rightTranslation (I := I) (F := F)
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d)
  -- A symplectic form on the base of a surjective submersion pulls back to a closed form whose
  -- null spaces are the vertical directions.
  obtain ⟨η, ⟨hη, hηq⟩, -⟩ :=
    h.existsUnique_isSymplectic_mpullback_orbitProj_eq_sub hreg hn d hσ hG
  exact (isSymplectic_iff_of_mpullback_eq hq.contMDiff BalancedProduct.orbitProj_surjective
    (hq.surjective_mfderiv (by simp)) hηq).1 hη

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
