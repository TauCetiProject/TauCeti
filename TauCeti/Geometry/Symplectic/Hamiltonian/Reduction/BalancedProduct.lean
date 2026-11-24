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

Let a Lie group `G` act smoothly by symplectomorphisms on `(M, σ)`, with moment map
`μ : M → 𝔤*`, and fix `c ∈ 𝔤*` with coadjoint stabilizer `G_c` and coadjoint orbit `O = G ⧸ G_c`,
carrying the Kirillov–Kostant–Souriau form `ω_KKS` (`Module.Dual.coadjointOrbitForm`). Let `Z` be
a manifold on which `G_c` acts smoothly, with a smooth `G_c`-equivariant map `ι : Z → M` into the
level `μ⁻¹(c)` along which the moment cocycle vanishes, and give the orbit space `Z / G_c` charts
for which the orbit projection `π : Z → Z / G_c` is smooth. The motivating case is the regular
level `μ⁻¹(c)` of a coadjoint-equivariant moment map, with its submanifold atlas and inclusion,
acted on freely by `G_c`, and the reduced space `Q = μ⁻¹(c) / G_c` with the charts of the quotient
manifold theorem. The balanced product

`Y_O = G ×_{G_c} Z`, the quotient of `G × Z` by `(g, z) ∼ (g h, h⁻¹ • z)` for `h ∈ G_c`,

(`TauCeti.BalancedProduct.rightTranslationChartedSpace`) carries three smooth maps:

* `q_Y : Y_O → Z / G_c`, `[g, z] ↦ [z]` (`TauCeti.BalancedProduct.orbitProj`), a surjective
  submersion when `π` is one (`TauCeti.BalancedProduct.isSubmersion_orbitProj_rightTranslation`),
  whose fibres are the `G`-orbits (`TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`);
* `i_Y : Y_O → M`, `[g, z] ↦ g • ι z` (`TauCeti.BalancedProduct.liftRightTranslation`);
* `pr_Y : Y_O → O`, `[g, z] ↦ g G_c` (`TauCeti.BalancedProduct.proj`).

The main result of this file is the **orbit-reduction identity**: a two-form `η` on `Z / G_c` is
a reduced form, `π^* η = ι^* σ`, exactly when

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`

(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub`).
Both sides are compared on `G × Z`, after pulling back along the submersion `(g, z) ↦ [g, z]`.
There `q_Y^* η` becomes `pr_Z^* (π^* η)`, while `i_Y^* σ - pr_Y^* ω_KKS` becomes `pr_Z^* (ι^* σ)`
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_quotientMk_liftRightTranslation_sub_proj`): by the
shifting identity `a^* σ = pr_G^* σ_c + pr_Z^* (ι^* σ)` for the action map `a(g, z) = g • ι z`
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`), since
`ω_KKS` pulls back to the left-invariant Kirillov form `σ_c` on `G`. Pullback along `pr_Z` is
injective as `G` is nonempty.

For a coadjoint-equivariant moment map with `c` a regular value and `G_c` acting freely on the
level, the Marsden–Weinstein–Meyer theorem then says that `Q` carries a unique symplectic form
`ω_red` with `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS`
(`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_orbitProj_eq_sub`). Consequently the
two-form `i_Y^* σ - pr_Y^* ω_KKS` on `Y_O` is closed, and its null space at each point is the
kernel of the differential of `q_Y`
(`IsEquivariantMomentMap.isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv`), so the null spaces of
this form are the tangent spaces to the fibres of `q_Y`, the `G`-orbits. The identity compares
reduction at `c` with the form `pr_M^* σ - pr_O^* ω_KKS` of the shifting construction on `M × O⁻`,
read on `Y_O` through `[g, z] ↦ (g • ι z, [g])`.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm`.

* `IsMomentMap.mpullback_quotientMk_liftRightTranslation_sub_proj`: the form
  `i_Y^* σ - pr_Y^* ω_KKS` pulls back to `pr_Z^* (ι^* σ)` on `G × Z`.
* `IsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub`:
  `π^* η = ι^* σ` exactly when `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`.
* `IsEquivariantMomentMap.mpullback_orbitProj_eq_sub`: the orbit-reduction identity for a reduced
  form, for a coadjoint-equivariant moment map.
* `IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_orbitProj_eq_sub`: on the regular
  level `μ⁻¹(c)`, the reduced space carries a unique symplectic form `ω_red` with
  `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS`, the Marsden–Weinstein–Meyer reduced form.
* `IsEquivariantMomentMap.isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv`:
  `i_Y^* σ - pr_Y^* ω_KKS` is closed, with null spaces the kernels of `d q_Y`.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the shifting trick).
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

section BalancedProduct

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
  {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ}
  [ChartedSpace HQ
    (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)]
  [IsManifold IQ ∞
    (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)]

namespace IsMomentMap

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
      (by rw [BalancedProduct.liftRightTranslation_comp_quotientMk]; rfl) σ,
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

/-- **The orbit-reduction identity characterizes reduced forms.** Let `G` act by
symplectomorphisms of `(M, σ)` with moment map `μ`, and let `ι : Z → M` be a smooth
`G_c`-equivariant map into the level `μ⁻¹(c)` along which the moment cocycle vanishes. Give
`Z ⧸ G_c` charts for which the orbit projection `π : Z → Z ⧸ G_c` is smooth, such as the charts
of the quotient manifold theorem when `G_c` acts freely and properly on `Z`. A two-form `η` on
`Z ⧸ G_c` descends `ι^* σ`, that is `π^* η = ι^* σ`, exactly when on `Y_O = G ×_{G_c} Z` it
satisfies

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`,

for `q_Y [g, z] = [z]`, `i_Y [g, z] = g • ι z` and the projection `pr_Y [g, z] = g G_c` onto the
coadjoint orbit with its Kirillov–Kostant–Souriau form. -/
theorem mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hc : ∀ z, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ (ι z) = 0)
    (hπZ : ContMDiff IZ IQ ∞
      (Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)))
    (η : SmoothTwoForm IQ
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)) :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
      (F := F)
    SmoothForm.mpullback _ hπZ η = SmoothForm.mpullback ι hι σ ↔
      SmoothForm.mpullback BalancedProduct.orbitProj
          (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff (I := I) (F := F)
            hπZ) η =
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
  have hq := BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff (I := I) (F := F)
    hπZ
  -- Both sides are compared after pulling back to `G × Z`, along the submersion `π` onto `Y_O`
  -- and then along the second projection.
  have hqπ : SmoothForm.mpullback _ hπ.contMDiff
      (SmoothForm.mpullback BalancedProduct.orbitProj hq η) =
        SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback _ hπZ η) :=
    SmoothForm.mpullback_mpullback_of_comp_eq hπ.contMDiff hq
      (contMDiff_snd (I := I) (J := IZ)) hπZ
      (funext fun x ↦ BalancedProduct.orbitProj_mk x.1 x.2) η
  rw [← (SmoothForm.mpullback_injective_of_surjective hπ.contMDiff Quotient.mk_surjective
    (hπ.surjective_mfderiv (by simp))).eq_iff, hqπ,
    h.mpullback_quotientMk_liftRightTranslation_sub_proj hG hι hιc hc]
  exact SmoothForm.mpullback_snd_injective.eq_iff.symm

end IsMomentMap

namespace IsEquivariantMomentMap

/-- **The orbit-reduction identity.** For a coadjoint-equivariant moment map, if a two-form `η`
on `Z / G_c` is a reduced form, `π^* η = ι^* σ`, then `q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS` on
`G ×_{G_c} Z`, where `q_Y [g, z] = [z]`, `i_Y [g, z] = g • ι z`, `pr_Y [g, z] = g G_c`, and
`ω_KKS` is the Kirillov–Kostant–Souriau form on the coadjoint orbit `G ⧸ G_c`. -/
theorem mpullback_orbitProj_eq_sub (h : σ.IsEquivariantMomentMap μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hπ : ContMDiff IZ IQ ∞
      (Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)))
    {η : SmoothTwoForm IQ
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z)}
    (hη : SmoothForm.mpullback _ hπ η = SmoothForm.mpullback ι hι σ) :
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ)
      (F := F)
    SmoothForm.mpullback BalancedProduct.orbitProj
        (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff (I := I) (F := F)
          hπ) η =
      SmoothForm.mpullback (BalancedProduct.liftRightTranslation ι)
          (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := IZ) (F := F) hι) σ -
        SmoothForm.mpullback (BalancedProduct.proj Z Subgroup.RightTranslation.quotientMk_smul)
          (BalancedProduct.contMDiff_proj_rightTranslation
            (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I)
            (IZ := IZ) (F := F)) c.coadjointOrbitForm :=
  (h.toIsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub hG hι hιc
    (fun z ↦ h.momentCocycle_eq_zero (ι z)) hπ η).1 hη

end IsEquivariantMomentMap

end BalancedProduct

/-! ### The Marsden–Weinstein–Meyer reduced form -/

namespace IsEquivariantMomentMap

variable [I'.Boundaryless] [FiniteDimensional ℝ E'] [ProperSMul G M]
  (h : σ.IsEquivariantMomentMap μ) {n : ℕ}
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)

/-- **The Marsden–Weinstein–Meyer reduced form on the balanced product.** Let a Lie group `G` act
smoothly and properly by symplectomorphisms on a symplectic manifold `(M, σ)`, with
coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ`, and let the coadjoint
stabilizer `G_c`, with the Lie group structure `d`, act freely on the level `μ⁻¹(c)`. Then the
reduced space `Q = μ⁻¹(c) ⧸ G_c` carries a unique symplectic form `ω_red` with

`q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS`

on `Y_O = G ×_{G_c} μ⁻¹(c)`, for `q_Y [g, z] = [z]`, `i_Y [g, z] = g • z` and the projection
`pr_Y [g, z] = g G_c` onto the coadjoint orbit with its Kirillov–Kostant–Souriau form. It is the
reduced form `π^* ω_red = i^* σ` of
`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`. -/
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
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
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
            (BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff (I := I) (F := F)
              (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff) η =
          SmoothForm.mpullback
              (BalancedProduct.liftRightTranslation (h.levelSubMulActionSubtype c))
              (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ))
                (F := F) (h.contMDiff_levelSubMulActionSubtype hreg hn)) σ -
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
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  -- The reduced form is characterized on the balanced product by the orbit-reduction identity.
  refine (existsUnique_congr fun η ↦ and_congr_right fun _ ↦
    h.toIsMomentMap.mpullback_quotientMk_eq_iff_mpullback_orbitProj_eq_sub (F := F)
      (ι := h.levelSubMulActionSubtype c) hG (h.contMDiff_levelSubMulActionSubtype hreg hn)
      (fun z ↦ by simpa using h.mem_levelSubMulAction.1 z.property)
      (fun _ ↦ h.momentCocycle_eq_zero _)
      (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η).1 ?_
  simpa only [coe_levelSubMulActionSubtype] using
    h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg hn d hσ hG

/-- **The null foliation of `i_Y^* σ - pr_Y^* ω_KKS`.** With the hypotheses of the
Marsden–Weinstein–Meyer theorem, the two-form `i_Y^* σ - pr_Y^* ω_KKS` on
`Y_O = G ×_{G_c} μ⁻¹(c)`, for `i_Y [g, z] = g • z` and the projection `pr_Y [g, z] = g G_c` onto
the coadjoint orbit, is closed, and its null space at each point is the kernel of the differential
of `q_Y : Y_O → μ⁻¹(c) ⧸ G_c`, `[g, z] ↦ [z]`. So the null distribution of this form is the
vertical bundle `ker d q_Y`, and the fibres of `q_Y`, the `G`-orbits
(`TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`), are unions of its null leaves. -/
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
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    haveI := BalancedProduct.isManifold_rightTranslation
      (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
      (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
    (SmoothForm.mpullback
          (BalancedProduct.liftRightTranslation (h.levelSubMulActionSubtype c))
          (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ))
            (F := F) (h.contMDiff_levelSubMulActionSubtype hreg hn)) σ -
        SmoothForm.mpullback (BalancedProduct.proj (h.levelSubMulAction c)
            Subgroup.RightTranslation.quotientMk_smul)
          (BalancedProduct.contMDiff_proj_rightTranslation
            (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
            (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F))
          c.coadjointOrbitForm).IsClosed ∧
      ∀ y, LinearMap.ker ((SmoothForm.mpullback
          (BalancedProduct.liftRightTranslation (h.levelSubMulActionSubtype c))
            (BalancedProduct.contMDiff_liftRightTranslation (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ))
              (F := F) (h.contMDiff_levelSubMulActionSubtype hreg hn)) σ -
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
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
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
