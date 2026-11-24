/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Lie.InvariantVectorField.Basic

/-!
# The shifting identity on `G × μ⁻¹(c)` and on `G ×_{G_c} μ⁻¹(c)`

Let a Lie group `G` act smoothly by symplectomorphisms on `(M, σ)`, with coadjoint-equivariant
moment map `μ : M → 𝔤*`, and fix `c ∈ 𝔤*`. In orbit reduction one compares the level
`Z = μ⁻¹(c)` with the preimage `μ⁻¹(O)` of the coadjoint orbit `O = G · c` through the action
map

`a : G × Z → M`, `a(g, z) = g • z`,

whose image is `μ⁻¹(O)`. The coadjoint orbit carries the Kirillov–Kostant–Souriau form `ω_KKS`,
and its pullback along the orbit map `g ↦ Ad*_g c` is the left-invariant Kirillov form `σ_c` of
`c` on `G` (`Module.Dual.leftInvariantKirillovForm`), which pairs the left-invariant vector fields
of `ξ` and `η` to `c ⁅ξ, η⁆`. This file proves the **shifting identity**

`a^* σ = pr_G^* σ_c + pr_Z^* (i^* σ)`

on `G × Z`, for the inclusion `i : Z → M`
(`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`).
It is stated for any smooth map `i : Z → M` from a manifold into the level, so it applies to the
regular level `μ⁻¹(c)` with its submanifold atlas, and needs neither a regular value nor
nondegeneracy of `σ`. Instead of equivariance of `μ` it only assumes that the moment cocycle
vanishes on the image of `i`, which holds for a coadjoint-equivariant moment map
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`).

The computation is pointwise. A tangent vector of `G × Z` at `(g, z)` is a pair of the left
translate of some `ξ ∈ 𝔤` and a tangent vector `v` of `Z`, and the action map sends it to
`d(g •)(ξ_M + v)`, where `v` is read in `T_z M`
(`TauCeti.mfderiv_smul_mulInvariantVectorField`). As `g` preserves `σ`,

`σ(d(g •)(ξ_M + v), d(g •)(η_M + w)) = σ(ξ_M, η_M) + σ(ξ_M, w) - σ(η_M, v) + σ(v, w)`.

The moment map identity `σ(ξ_M, w) = ⟨dμ(w), ξ⟩` kills the two cross terms when `v` and `w` are
tangent to the level, and infinitesimal equivariance gives `σ(ξ_M, η_M) = μ(z) ⁅ξ, η⁆ = c ⁅ξ, η⁆`
(`TauCeti.SmoothTwoForm.IsMomentMap.eval₂_mfderiv_smul_add_fundamentalVectorField`).

The quotient `Y_O = G ×_{G_c} Z` of `G × Z` by `h · (g, z) = (g h⁻¹, h • z)` maps to the reduced
space `Q = Z / G_c` by `q_Y [g, z] = [z]`, to `M` by `i_Y [g, z] = g • z` and to `O` by
`pr_Y [g, z] = [g]`. When `G_c` acts freely and properly on `Z`, the balanced product `Y_O` and the
quotient `Q` are smooth manifolds (`TauCeti.BalancedProduct.rightTranslationChartedSpace` and
`ProperSMul.orbitRelQuotientChartedSpace`), and for the reduced form, characterized by
`π^* ω_red = i^* σ`, the shifting identity descends to

`q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS`

on `Y_O` (`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_orbitProj_eq_sub_coadjointOrbitForm`).
Indeed, pulled back along the quotient map `G × Z → Y_O`, both sides become the two sides of the
shifting identity on `G × Z`, with `ω_KKS` pulled back to `σ_c` along `G → G ⧸ G_c`
(`Module.Dual.mpullback_quotientMk_coadjointOrbitForm`), and pullback along this surjective
submersion is injective.

## Main results

All results are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `IsMomentMap.eval₂_mfderiv_smul_add_fundamentalVectorField`: the pointwise identity
  `σ(d(g •)(ξ_M + v), d(g •)(η_M + w)) = μ(x) ⁅ξ, η⁆ + σ(v, w)` for `v`, `w` in `ker dμ_x`,
  wherever the moment cocycle vanishes at `x`.
* `mpullback_smul_eq_prod_leftInvariantKirillovForm`: the shifting identity
  `a^* σ = pr_G^* σ_c + pr_Z^* (i^* σ)` on `G × Z`.
* `mpullback_smul_prodMk_prod_neg_leftInvariantKirillovForm`: equivalently, the map
  `(g, z) ↦ (g • i z, g)` pulls `pr_M^* σ - pr_G^* σ_c` on `M × G` back to `pr_Z^* (i^* σ)`, the
  form of the shifting construction on `M × O⁻` read on `G × Z`.
* `mpullback_orbitProj_eq_sub_coadjointOrbitForm`: the shifting identity
  `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS` on `Y_O = G ×_{G_c} Z`, for any two-form `ω_red` on
  `Z / G_c` with `π^* ω_red = i^* σ`.

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

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

namespace IsMomentMap

/-- **The shifting identity at a point.** Let `g` act by a symplectomorphism and let `v`, `w` be
tangent to the level of `μ` through `x`, that is in the kernel of `dμ_x`. Then
`σ(d(g •)(ξ_M + v), d(g •)(η_M + w)) = μ(x) ⁅ξ, η⁆ + σ(v, w)`: the orbit directions pair through
the Kirillov form of `μ(x)`, and they are `σ`-orthogonal to the level. Only the vanishing of the
moment cocycle at `x` is needed, not equivariance of `μ`. -/
theorem eval₂_mfderiv_smul_add_fundamentalVectorField
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {g : G}
    (hg : SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {x : M} (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0)
    (ξ η : GroupLieAlgebra I G) {v w : TangentSpace I' x}
    (hv : h.differential x v = 0) (hw : h.differential x w = 0) :
    σ.eval₂ (g • x)
        (mfderiv I' I' (fun y : M ↦ g • y) x (fundamentalVectorField I' ξ x + v))
        (mfderiv I' I' (fun y : M ↦ g • y) x (fundamentalVectorField I' η x + w)) =
      μ x ⁅ξ, η⁆ + σ.eval₂ x v w := by
  -- The cross terms are `⟨dμ_x w, ξ⟩` and `-⟨dμ_x v, η⟩`.
  have hcross (ζ : GroupLieAlgebra I G) {u : TangentSpace I' x}
      (hu : h.differential x u = 0) :
      σ.eval₂ x (fundamentalVectorField I' ζ x) u = 0 := by
    rw [← InfinitesimalAction.fundamental_apply, ← h.differential_apply_eq_eval₂,
      hu, LinearMap.zero_apply]
  have horbit : σ.eval₂ x (fundamentalVectorField I' ξ x) (fundamentalVectorField I' η x) =
      μ x ⁅ξ, η⁆ := by
    simpa only [InfinitesimalAction.fundamental_apply] using
      momentCocycle_eq_zero_iff.1 hc ξ η
  rw [← SmoothForm.eval₂_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) g), hg,
    SmoothBundleForm.eval₂_add_left, SmoothBundleForm.eval₂_add_right,
    SmoothBundleForm.eval₂_add_right, horbit, hcross ξ hw,
    SmoothBundleForm.eval₂_swap σ x v, hcross η hv, neg_zero, add_zero, zero_add]

variable {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]
  [IsManifold IZ ∞ Z] {i : Z → M}

/-- **The shifting identity.** Let `G` act by symplectomorphisms of `(M, σ)` with moment map `μ`,
and let `i : Z → M` be a smooth map into the level `μ⁻¹(c)`, such as the inclusion of a regular
level, on whose image the moment cocycle vanishes, as it does everywhere for a
coadjoint-equivariant moment map. The action map `a(g, z) = g • i z` on `G × Z` pulls `σ` back to
`pr_G^* σ_c + pr_Z^* (i^* σ)`, where `σ_c` is the left-invariant Kirillov form of `c`, the
pullback of the Kirillov–Kostant–Souriau form of the coadjoint orbit of `c` along
`g ↦ Ad*_g c`. -/
theorem mpullback_smul_eq_prod_leftInvariantKirillovForm
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hi : ContMDiff IZ I' ∞ i) {c : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hic : ∀ z, μ (i z) = c)
    (hc : ∀ z, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ (i z) = 0) :
    SmoothForm.mpullback (fun p : G × Z ↦ p.1 • i p.2)
        (contMDiff_fst.smul (hi.comp contMDiff_snd)) σ =
      SmoothTwoForm.prod c.leftInvariantKirillovForm (SmoothForm.mpullback i hi σ) := by
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  obtain ⟨g, z⟩ := p
  have ha : MDifferentiableAt (I.prod IZ) I' (fun p : G × Z ↦ p.1 • i p.2) (g, z) :=
    (contMDiff_fst.smul (hi.comp contMDiff_snd) :
      ContMDiff (I.prod IZ) I' ∞ fun p : G × Z ↦ p.1 • i p.2).mdifferentiableAt (by simp)
  have hsmul : MDifferentiableAt I' I' (fun y : M ↦ g • y) (i z) :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt (by simp)
  -- The action map sends `(X^L_ξ(g), u)` to `d(g •)(ξ_M + di u)`.
  have hda (u : TangentSpace (I.prod IZ) (g, z)) {ξ : GroupLieAlgebra I G}
      (hξ : mulInvariantVectorField ξ g = u.1) :
      mfderiv (I.prod IZ) I' (fun p : G × Z ↦ p.1 • i p.2) (g, z) u =
        mfderiv I' I' (fun y : M ↦ g • y) (i z)
          (fundamentalVectorField I' ξ (i z) + mfderiv IZ I' i z u.2) := by
    rw [mfderiv_prod_eq_add_apply ha, map_add]
    dsimp only
    rw [← hξ, mfderiv_smul_mulInvariantVectorField]
    congr 1
    exact mfderiv_comp_apply_of_eq z hsmul (hi.mdifferentiableAt (by simp)) rfl _
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (I := I) (g := g) v.1
  obtain ⟨η, hη⟩ := exists_mulInvariantVectorField_eq (I := I) (g := g) w.1
  rw [SmoothForm.eval₂_mpullback, eval₂_prod, hda v hξ, hda w hη]
  refine (h.eval₂_mfderiv_smul_add_fundamentalVectorField (hG g) (hc z) ξ η
    (h.differential_mfderiv_eq_zero hic z v.2) (h.differential_mfderiv_eq_zero hic z w.2)).trans ?_
  rw [hic z, SmoothForm.eval₂_mpullback, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.tangentSpaceProdEquiv_apply, ← hξ, ← hη,
    c.eval₂_leftInvariantKirillovForm_mulInvariantVectorField]

/-- **The shifting identity on `M × G`.** With the hypotheses of
`TauCeti.SmoothTwoForm.IsMomentMap.mpullback_smul_eq_prod_leftInvariantKirillovForm`,
the map `(g, z) ↦ (g • i z, g)` from `G × Z` to `M × G` pulls the product form
`pr_M^* σ - pr_G^* σ_c` back to `pr_Z^* (i^* σ)`. When `μ` is moreover coadjoint-equivariant,
its image lies over the zero level of the shifting moment map `(x, g) ↦ μ x - Ad*_g c`, and on
`M × O⁻` this is the identity `q_O^* ω_red = pr_M^* σ - pr_O^* ω_KKS` read on `G × Z`. -/
theorem mpullback_smul_prodMk_prod_neg_leftInvariantKirillovForm
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hi : ContMDiff IZ I' ∞ i) {c : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hic : ∀ z, μ (i z) = c)
    (hc : ∀ z, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ (i z) = 0) :
    SmoothForm.mpullback (fun p : G × Z ↦ (p.1 • i p.2, p.1))
        ((contMDiff_fst.smul (hi.comp contMDiff_snd)).prodMk contMDiff_fst)
        (SmoothTwoForm.prod σ (-c.leftInvariantKirillovForm)) =
      SmoothForm.mpullback Prod.snd contMDiff_snd (SmoothForm.mpullback i hi σ) := by
  have ha : ContMDiff (I.prod IZ) I' ∞ fun p : G × Z ↦ p.1 • i p.2 :=
    contMDiff_fst.smul (hi.comp contMDiff_snd)
  -- The components of `(g, z) ↦ (g • i z, g)` are the action map and the first projection.
  have hM : SmoothForm.mpullback _ (ha.prodMk contMDiff_fst)
      (SmoothForm.mpullback Prod.fst contMDiff_fst σ) = SmoothForm.mpullback _ ha σ :=
    SmoothForm.mpullback_mpullback _ _ _ _ _
  have hK : SmoothForm.mpullback _ (ha.prodMk contMDiff_fst)
      (SmoothForm.mpullback Prod.snd contMDiff_snd c.leftInvariantKirillovForm) =
        SmoothForm.mpullback Prod.fst contMDiff_fst c.leftInvariantKirillovForm :=
    SmoothForm.mpullback_mpullback _ _ _ _ _
  rw [prod_def, map_add, map_neg, map_neg, hM, hK,
    h.mpullback_smul_eq_prod_leftInvariantKirillovForm hG hi hic hc, prod_def, add_neg_cancel_comm]

/-! ### The shifting identity on `G ×_{G_c} Z` -/

section BalancedProduct

open BalancedProduct

attribute [local instance] Lie.isClosed_stabilizer_coadjointRepresentation

variable [I.Boundaryless] [FiniteDimensional ℝ EZ] [IZ.Boundaryless] [T2Space Z]
  {c : Module.Dual ℝ (GroupLieAlgebra I G)}
  [MulAction ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F ((Lie.coadjointRepresentation ℝ I G).stabilizer c)]
  [LieGroup 𝓘(ℝ, F) ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c) G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z]
  [ProperSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z]

/-- **The shifting identity on `Y_O = G ×_{G_c} Z`.** Let `G` act by symplectomorphisms of
`(M, σ)` with moment map `μ`, let the coadjoint stabilizer `G_c` act freely and properly on a
manifold `Z`, and let `ι : Z → M` be a smooth `G_c`-equivariant map into the level `μ⁻¹(c)`, on
whose image the moment cocycle vanishes, such as the inclusion of a regular level. If a two-form
`η` on the quotient `Q = Z ⧸ G_c` satisfies `π^* η = ι^* σ`, as the reduced form does, then on the
balanced product `Y_O`

`q_Y^* η = i_Y^* σ - pr_Y^* ω_KKS`,

where `q_Y [g, z] = [z]` maps to `Q`, `i_Y [g, z] = g • ι z` maps to `M`, and
`pr_Y [g, z] = g G_c` maps to the coadjoint orbit `G ⧸ G_c` with its Kirillov–Kostant–Souriau form
`ω_KKS`. -/
theorem mpullback_orbitProj_eq_sub_coadjointOrbitForm
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {ι : Z →ₑ[((↑) : (Lie.coadjointRepresentation ℝ I G).stabilizer c → G)] M}
    (hι : ContMDiff IZ I' ∞ ι) (hιc : ∀ z, μ (ι z) = c)
    (hc : ∀ z, σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ (ι z) = 0) :
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F)
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) IZ Z
    letI := rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
    haveI := isManifold_rightTranslation (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (Z := Z) (I := I) (IZ := IZ) (F := F)
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F EZ)
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z),
      SmoothForm.mpullback _ ProperSMul.isSubmersion_quotientMk.contMDiff η =
          SmoothForm.mpullback ι hι σ →
        SmoothForm.mpullback orbitProj contMDiff_orbitProj_rightTranslation η =
          SmoothForm.mpullback (liftRightTranslation ι)
              (contMDiff_liftRightTranslation (I := I) (F := F) hι) σ -
            SmoothForm.mpullback (proj Z Subgroup.RightTranslation.quotientMk_smul)
              (contMDiff_proj_rightTranslation
                (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (I := I) (IZ := IZ)
                (F := F)) c.coadjointOrbitForm := by
  intro η hη
  let _ := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F)
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) IZ Z
  let _ := rightTranslationChartedSpace ((Lie.coadjointRepresentation ℝ I G).stabilizer c) Z I IZ F
  have := isManifold_rightTranslation (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    (Z := Z) (I := I) (IZ := IZ) (F := F)
  have hP := isSubmersion_quotientMk_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := Z) (I := I) (IZ := IZ) (F := F)
  -- The projection `P : G_c.RightTranslation × Z → Y_O` is a surjective submersion, so it suffices
  -- to compare pullbacks along `P`. Composed with `P`, each of `q_Y`, `i_Y` and `pr_Y` factors
  -- through the identification `e` of `G_c.RightTranslation × Z` with `G × Z`.
  refine SmoothForm.mpullback_injective_of_surjective hP.contMDiff Quotient.mk_surjective
    (hP.surjective_mfderiv (by simp)) ?_
  have he : ContMDiff (I.prod IZ) (I.prod IZ) ∞
      (Prod.map ((Lie.coadjointRepresentation ℝ I G).stabilizer c).toRightTranslation.symm
        (id : Z → Z)) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id
  have hq := SmoothForm.mpullback_mpullback_of_comp_eq hP.contMDiff
    (contMDiff_orbitProj_rightTranslation (I := I) (IZ := IZ) (F := F)) he
    (ProperSMul.isSubmersion_quotientMk.contMDiff.comp contMDiff_snd)
    (funext fun x ↦ orbitProj_mk x.1 x.2) η
  have hi := SmoothForm.mpullback_mpullback_of_comp_eq (g' := fun p : G × Z ↦ p.1 • ι p.2)
    hP.contMDiff (contMDiff_liftRightTranslation (I := I) (F := F) hι) he
    (contMDiff_fst.smul (hι.comp contMDiff_snd)) (funext fun x ↦ by
      rw [Function.comp_apply, quotientMk_eq_mk_toRightTranslation, liftRightTranslation_mk]
      rfl) σ
  have hpr := SmoothForm.mpullback_mpullback_of_comp_eq hP.contMDiff
    (contMDiff_proj_rightTranslation (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (I := I) (IZ := IZ) (F := F)) he
    (c.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff.comp
      (contMDiff_fst (J := IZ) (N := Z)))
    (funext fun x ↦ by
      rw [Function.comp_apply, quotientMk_eq_mk_toRightTranslation, proj_mk,
        Subgroup.RightTranslation.quotientMk_toRightTranslation]
      rfl) c.coadjointOrbitForm
  rw [map_sub, hq, hi, hpr, ← map_sub,
    ← SmoothForm.mpullback_mpullback _ _ (contMDiff_snd (I := I) (J := IZ))
      ProperSMul.isSubmersion_quotientMk.contMDiff,
    ← SmoothForm.mpullback_mpullback _ _ (contMDiff_fst (I := I) (J := IZ))
      c.isSubmersion_quotientMk_stabilizer_coadjointRepresentation.contMDiff,
    hη, Module.Dual.mpullback_quotientMk_coadjointOrbitForm,
    h.mpullback_smul_eq_prod_leftInvariantKirillovForm hG hι hιc hc, SmoothTwoForm.prod_def,
    add_sub_cancel_left]

end BalancedProduct

end IsMomentMap

end SmoothTwoForm

end TauCeti
