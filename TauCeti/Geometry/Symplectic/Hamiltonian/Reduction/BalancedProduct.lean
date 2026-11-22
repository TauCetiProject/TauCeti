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
# The orbit-reduction identity on `G ×_{G_c} Z`

Let a Lie group `G` act smoothly by symplectomorphisms on `(M, σ)`, with coadjoint-equivariant
moment map `μ : M → 𝔤*`, and fix `c ∈ 𝔤*` with coadjoint stabilizer `G_c`. Let `Z` be a manifold
on which `G_c` acts smoothly, with a smooth `G_c`-equivariant map `ι : Z → M` into the level
`μ⁻¹(c)`, and give the orbit space `Z / G_c` charts for which the orbit projection
`π : Z → Z / G_c` is smooth. The motivating case is the regular level `μ⁻¹(c)`, with its submanifold
atlas and inclusion, acted on freely by `G_c`, and the reduced space `μ⁻¹(c) / G_c` with the charts
of the quotient manifold theorem. The balanced product

`Y_O = G ×_{G_c} Z`, the quotient of `G × Z` by `(g, z) ∼ (g h, h⁻¹ • z)` for `h ∈ G_c`,

(`TauCeti.BalancedProduct.rightTranslationChartedSpace`) carries three smooth maps:

* `q_Y : Y_O → Z / G_c`, `[g, z] ↦ [z]` (`TauCeti.BalancedProduct.orbitProj`);
* `i_Y : Y_O → M`, `[g, z] ↦ g • ι z` (`TauCeti.BalancedProduct.liftRightTranslation`);
* `pr_Y : Y_O → O = G ⧸ G_c`, `[g, z] ↦ [g]` (`TauCeti.BalancedProduct.proj`), onto the coadjoint
  orbit with its Kirillov–Kostant–Souriau form `ω_KKS` (`Module.Dual.coadjointOrbitForm`).

The main result of this file is the **orbit-reduction identity**: a two-form `η` on the quotient
`Z / G_c` satisfies

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`

exactly when it is a reduced form, `π^* η = ι^* σ`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_orbitProj_eq_sub_iff`). In particular
the Marsden–Weinstein–Meyer reduced form `ω_red` on `μ⁻¹(c) / G_c`
(`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`)
is the unique symplectic form with `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS`. The identity compares
reduction at `c` with the form `pr_M^* σ - pr_O^* ω_KKS` of the shifting construction on `M × O⁻`,
read on `Y_O` through `[g, z] ↦ (g • ι z, [g])`.

The proof pulls both sides back along the projection `G × Z → Y_O`, a surjective submersion, so
that pullback along it is injective. There `q_Y` becomes `π ∘ pr_Z`, `i_Y` the action map
`(g, z) ↦ g • ι z` and `pr_Y` the projection `G → G ⧸ G_c` after `pr_G`. The KKS form pulls back
to the left-invariant Kirillov form `σ_c` on `G`, and the shifting identity
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`)

`(g, z) ↦ g • ι z` pulls `σ` back to `pr_G^* σ_c + pr_Z^* (ι^* σ)`

turns the right side into `pr_Z^* (ι^* σ)` and the left side into `pr_Z^* (π^* η)`. Pullback along
`pr_Z` is injective as `G` is nonempty.

## Main results

All results are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `mpullback_orbitProj_eq_sub_iff`: a two-form `η` on `Z / G_c` satisfies
  `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS` if and only if `π^* η = ι^* σ`.
* `mpullback_orbitProj_eq_sub`: the orbit-reduction identity for a reduced form.
* `existsUnique_isSymplectic_mpullback_orbitProj_eq_sub`: on the regular level `μ⁻¹(c)`, the
  reduced space carries a unique symplectic form `ω_red` with
  `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS`, the Marsden–Weinstein–Meyer reduced form.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the shifting trick).
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction).
-/

public section

noncomputable section

open Module TauCeti.Lie
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)}

section BalancedProduct

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F ((coadjointRepresentation ℝ I G).stabilizer c)]
  [LieGroup 𝓘(ℝ, F) ∞ ((coadjointRepresentation ℝ I G).stabilizer c)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ ((coadjointRepresentation ℝ I G).stabilizer c) G]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  [MulAction ((coadjointRepresentation ℝ I G).stabilizer c) Z]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ ((coadjointRepresentation ℝ I G).stabilizer c) Z]
  {ι : Z →ₑ[((↑) : (coadjointRepresentation ℝ I G).stabilizer c → G)] M}
  {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ}
  [ChartedSpace HQ (MulAction.orbitRel.Quotient ((coadjointRepresentation ℝ I G).stabilizer c) Z)]
  [IsManifold IQ ∞
    (MulAction.orbitRel.Quotient ((coadjointRepresentation ℝ I G).stabilizer c) Z)]

/-- The right side `i_Y^* σ - pr_Y^* ω_KKS` of the orbit-reduction identity pulls back to
`pr_Z^* (ι^* σ)` along the projection `G × Z → G ×_{G_c} Z`. -/
private theorem mpullback_quotientMk_sub (h : σ.IsEquivariantMomentMap μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c) :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation (K :=
      (coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
    SmoothForm.mpullback _ BalancedProduct.isSubmersion_quotientMk_rightTranslation.contMDiff
        (SmoothForm.mpullback _ (BalancedProduct.contMDiff_liftRightTranslation hι) σ -
          SmoothForm.mpullback _ (BalancedProduct.contMDiff_proj_rightTranslation (K :=
            (coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F))
            c.coadjointOrbitForm) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback ι hι σ) := by
  let K := (coadjointRepresentation ℝ I G).stabilizer c
  let _ := BalancedProduct.rightTranslationChartedSpace K Z I IZ F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)
  -- Read `K.RightTranslation × Z` as `G × Z` through the identity `e × id`.
  have he : ContMDiff (I.prod IZ) (I.prod IZ) ∞
      (Prod.map K.toRightTranslation.symm id : K.RightTranslation × Z → G × Z) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id
  have ha : ContMDiff (I.prod IZ) I' ∞ fun p : G × Z ↦ p.1 • ι p.2 :=
    contMDiff_fst.smul (hι.comp contMDiff_snd)
  -- On representatives, `i_Y` is the action map and `pr_Y` is `G → G ⧸ G_c` after `pr_G`.
  have hlift : SmoothForm.mpullback _
      BalancedProduct.isSubmersion_quotientMk_rightTranslation.contMDiff
        (SmoothForm.mpullback _ (BalancedProduct.contMDiff_liftRightTranslation (K := K)
          (Z := Z) (I := I) (IZ := IZ) (F := F) hι) σ) =
      SmoothForm.mpullback _ he (SmoothForm.mpullback _ ha σ) :=
    SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext fun x ↦ by
      rw [Function.comp_apply, BalancedProduct.quotientMk_eq_mk_toRightTranslation,
        BalancedProduct.liftRightTranslation_mk]
      rfl) σ
  have hproj : SmoothForm.mpullback _
      BalancedProduct.isSubmersion_quotientMk_rightTranslation.contMDiff
        (SmoothForm.mpullback _ (BalancedProduct.contMDiff_proj_rightTranslation (K := K)
          (Z := Z) (I := I) (IZ := IZ) (F := F)) c.coadjointOrbitForm) =
      SmoothForm.mpullback _ he
        (SmoothForm.mpullback Prod.fst contMDiff_fst c.leftInvariantKirillovForm) := by
    rw [← c.mpullback_quotientMk_coadjointOrbitForm
      c.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff,
      SmoothForm.mpullback_mpullback Prod.fst]
    exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext fun x ↦ by
      rw [Function.comp_apply, BalancedProduct.quotientMk_eq_mk_toRightTranslation,
        BalancedProduct.proj_mk, Subgroup.RightTranslation.quotientMk_toRightTranslation]
      rfl) _
  rw [map_sub, hlift, hproj, ← map_sub,
    h.toIsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm hG hι hιc
      (fun z ↦ h.momentCocycle_eq_zero (ι z)),
    prod_def, add_sub_cancel_left, SmoothForm.mpullback_prodMap_mpullback_snd
      (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞) contMDiff_id,
    SmoothForm.mpullback_id, LinearMap.id_apply]

/-- **The orbit-reduction identity characterizes reduced forms.** Let `ι : Z → M` be a smooth
`G_c`-equivariant map into the level `μ⁻¹(c)` of a coadjoint-equivariant moment map for a
symplectic action, and give `Z / G_c` charts for which the orbit projection `π : Z → Z / G_c` is
smooth. A two-form `η` on `Z / G_c` satisfies `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS` on
`G ×_{G_c} Z` if and only if `π^* η = ι^* σ`. Here `q_Y [g, z] = [z]`, `i_Y [g, z] = g • ι z` and
`pr_Y [g, z] = [g]`, and `ω_KKS` is the Kirillov–Kostant–Souriau form on `G ⧸ G_c`. -/
theorem mpullback_orbitProj_eq_sub_iff (h : σ.IsEquivariantMomentMap μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hπ : ContMDiff IZ IQ ∞
      (Quotient.mk (MulAction.orbitRel ((coadjointRepresentation ℝ I G).stabilizer c) Z)))
    {η : SmoothTwoForm IQ
      (MulAction.orbitRel.Quotient ((coadjointRepresentation ℝ I G).stabilizer c) Z)} :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation (K :=
      (coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
    SmoothForm.mpullback _ (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff
        (I := I) (F := F) hπ) η =
        SmoothForm.mpullback _ (BalancedProduct.contMDiff_liftRightTranslation hι) σ -
          SmoothForm.mpullback _ (BalancedProduct.contMDiff_proj_rightTranslation (K :=
            (coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F))
            c.coadjointOrbitForm ↔
      SmoothForm.mpullback _ hπ η = SmoothForm.mpullback ι hι σ := by
  let K := (coadjointRepresentation ℝ I G).stabilizer c
  let _ := BalancedProduct.rightTranslationChartedSpace K Z I IZ F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)
  have hP := BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K) (Z := Z) (I := I)
    (IZ := IZ) (F := F)
  -- On representatives, `q_Y` is `π` after `pr_Z`.
  have hq : SmoothForm.mpullback _ hP.contMDiff
      (SmoothForm.mpullback _ (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff
        (I := I) (F := F) hπ) η) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback _ hπ η) :=
    SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _
      (funext fun x : K.RightTranslation × Z ↦ BalancedProduct.orbitProj_mk x.1 x.2) η
  rw [← (SmoothForm.mpullback_injective_of_surjective hP.contMDiff Quotient.mk_surjective
    (hP.surjective_mfderiv (by simp))).eq_iff, h.mpullback_quotientMk_sub hG hι hιc, hq,
    SmoothForm.mpullback_snd_injective.eq_iff]

/-- **The orbit-reduction identity.** If a two-form `η` on `Z / G_c` is a reduced form,
`π^* η = ι^* σ`, then `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS` on `G ×_{G_c} Z`, where
`q_Y [g, z] = [z]`, `i_Y [g, z] = g • ι z`, `pr_Y [g, z] = [g]`, and `ω_KKS` is the
Kirillov–Kostant–Souriau form on the coadjoint orbit `G ⧸ G_c`. -/
theorem mpullback_orbitProj_eq_sub (h : σ.IsEquivariantMomentMap μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hπ : ContMDiff IZ IQ ∞
      (Quotient.mk (MulAction.orbitRel ((coadjointRepresentation ℝ I G).stabilizer c) Z)))
    {η : SmoothTwoForm IQ
      (MulAction.orbitRel.Quotient ((coadjointRepresentation ℝ I G).stabilizer c) Z)}
    (hη : SmoothForm.mpullback _ hπ η = SmoothForm.mpullback ι hι σ) :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation (K :=
      (coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
    SmoothForm.mpullback _ (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff
        (I := I) (F := F) hπ) η =
      SmoothForm.mpullback _ (BalancedProduct.contMDiff_liftRightTranslation hι) σ -
        SmoothForm.mpullback _ (BalancedProduct.contMDiff_proj_rightTranslation (K :=
          (coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F))
          c.coadjointOrbitForm :=
  (h.mpullback_orbitProj_eq_sub_iff hG hι hιc hπ).2 hη

end BalancedProduct

/-! ### The Marsden–Weinstein–Meyer reduced form -/

section ReducedSpace

variable [FiniteDimensional ℝ E'] [I'.Boundaryless] [ProperSMul G M] {n : ℕ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The orbit-reduction identity for the Marsden–Weinstein–Meyer reduced form.** Let `G` act
properly by symplectomorphisms on a symplectic manifold `(M, σ)` with coadjoint-equivariant
moment map `μ`, let `c` be a regular value of `μ` and let the coadjoint stabilizer `G_c`, with the
Lie group structure `d`, act freely on the level `Z = μ⁻¹(c)`. Then the reduced space `Z / G_c`
carries a unique symplectic form `ω_red` with `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS` on
`Y_O = G ×_{G_c} Z`, where `q_Y [g, z] = [z]`, `i_Y [g, z] = g • z`, `pr_Y [g, z] = [g]` and
`ω_KKS` is the Kirillov–Kostant–Souriau form on `G ⧸ G_c`. It is the reduced form with
`π^* ω_red = i^* σ` of
`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`. -/
theorem existsUnique_isSymplectic_mpullback_orbitProj_eq_sub (h : σ.IsEquivariantMomentMap μ)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    [IsCancelSMul ((coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
    (d : EmbeddedLieSubgroupData I ((coadjointRepresentation ℝ I G).stabilizer c) F) :
    letI := d.chartedSpace
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (I'' := I) (M := G)
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    haveI := h.properSMul_levelSubMulAction (c := c)
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
    letI := BalancedProduct.rightTranslationChartedSpace
      ((coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    haveI := BalancedProduct.isManifold_rightTranslation (K :=
      (coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c) (I := I)
      (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsSymplectic ∧
        SmoothForm.mpullback _ (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff
            (I := I) (F := F) (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff) η =
          SmoothForm.mpullback _ (BalancedProduct.contMDiff_liftRightTranslation (I := I)
              (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F) (ι := h.levelSubMulActionSubtype c) (by
                rw [coe_levelSubMulActionSubtype]
                exact (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff)) σ -
            SmoothForm.mpullback _ (BalancedProduct.contMDiff_proj_rightTranslation (K :=
              (coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
              (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)) c.coadjointOrbitForm := by
  let := d.chartedSpace
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := d.lieGroup
  have := d.contMDiffSMul (I'' := I) (M := G)
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hemb := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal hemb
  have := h.properSMul_levelSubMulAction (c := c)
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have hιc (z : h.levelSubMulAction c) : μ (h.levelSubMulActionSubtype c z) = c := by
    rw [coe_levelSubMulActionSubtype]
    exact h.mem_levelSubMulAction.1 z.property
  have hι : ContMDiff 𝓘(ℝ, Fin n → ℝ) I' ∞ (h.levelSubMulActionSubtype c) := by
    rw [coe_levelSubMulActionSubtype]
    exact hemb.contMDiff
  have hπ := (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
  obtain ⟨η, ⟨hη, hηπ⟩, huniq⟩ :=
    h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg hn d hσ hG
  -- The reduced form pulls back to `ι^* σ` along `π`, as `ι` is the inclusion of the level.
  have hred (η' : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
      (MulAction.orbitRel.Quotient ((coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c))) :
      SmoothForm.mpullback _ hπ η' = SmoothForm.mpullback _ hι σ ↔
        SmoothForm.mpullback _ hπ η' = SmoothForm.mpullback Subtype.val hemb.contMDiff σ := by
    simp only [coe_levelSubMulActionSubtype]
  exact ⟨η, ⟨hη, h.mpullback_orbitProj_eq_sub hG hι hιc hπ ((hred η).2 hηπ)⟩,
    fun η' hη' ↦ huniq η' ⟨hη'.1, (hred η').1 ((h.mpullback_orbitProj_eq_sub_iff hG hι hιc hπ).1
      hη'.2)⟩⟩

end ReducedSpace

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
