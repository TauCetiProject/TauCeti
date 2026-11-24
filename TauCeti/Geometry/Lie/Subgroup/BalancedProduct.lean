/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Manifold.GroupAction.BalancedProduct
public import TauCeti.Topology.Covering.BalancedProduct.RightTranslation

import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The balanced product `G ×_K Z` of a Lie group with a manifold acted on by a closed subgroup

Let `G` be a finite-dimensional real Lie group with boundaryless model and `K` a closed subgroup,
with a Lie group structure for which it acts smoothly on `G` by left multiplication, such as its
closed-subgroup structure (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`). Let `K` act smoothly
on a Hausdorff boundaryless manifold `Z`. The balanced product `G ×_K Z`, the quotient of `G × Z`
by `h • (g, z) = (g h⁻¹, h • z)`, is `TauCeti.BalancedProduct K (Subgroup.RightTranslation K) Z`;
its algebra and topology are in `TauCeti.Topology.Covering.BalancedProduct.RightTranslation`.

Right translation by `K` on `G` is smooth, free, and proper because `K` is closed. So `G ×_K Z`
is a case of the smooth balanced product `P ×_K Z` of
`TauCeti.Geometry.Manifold.GroupAction.BalancedProduct`: a smooth manifold of dimension
`dim G + dim Z - dim K`
(`TauCeti.BalancedProduct.rightTranslationChartedSpace`), for which `(g, z) ↦ [g, z]` is a smooth
submersion, and whose projection `[g, z] ↦ [z]` onto `Z ⧸ K` is smooth when `K` acts freely and
properly on `Z` (`TauCeti.BalancedProduct.contMDiff_orbitProj_rightTranslation`). That projection
is a submersion for every manifold structure on `Z ⧸ K` for which the orbit projection of `Z` is
one (`TauCeti.BalancedProduct.isSubmersion_orbitProj_rightTranslation`). The action
`k • [g, z] = [k g, z]` of `G` and the two maps `[g, z] ↦ g K` and `[g, z] ↦ g • ι z` are smooth.
For a point `z₀` of `Z` fixed by `K`, the zero section `g K ↦ [g, z₀]` is a smooth embedding of
the homogeneous space `G ⧸ K` onto the `G`-orbit of `[1, z₀]`.

When `K` acts freely and properly on `Z`, so does `G` on `G ×_K Z`
(`TauCeti.BalancedProduct.instProperSMulRightTranslation` and the freeness instance of
`TauCeti.Topology.Covering.BalancedProduct.RightTranslation`). The quotient manifold theorem then
makes the orbit space `(G ×_K Z) ⧸ G` a smooth manifold, and the bijection
`G • [g, z] ↦ [z]` onto `Z ⧸ K` is a diffeomorphism for the charts of the quotient manifold
theorem on both sides (`TauCeti.BalancedProduct.orbitRelQuotientDiffeomorphRightTranslation`).
So `Z ⧸ K` is recovered from `G ×_K Z` as a manifold, not only as a set.

For a `K`-equivariant smooth embedding `ι : Z → M` into a smooth `G`-manifold, `G ×_K Z` is
recovered inside `M × G ⧸ K` as the set of pairs `(m, g K)` with `g⁻¹ • m ∈ ι(Z)`: the map
`[g, z] ↦ (g • ι z, g K)` is smooth and injective, and it lifts to a diffeomorphism onto every
manifold `W` smoothly embedded in `M × G ⧸ K` with that image
(`TauCeti.BalancedProduct.liftProjDiffeomorphRightTranslation`). The inverse is smooth because
over an open set of `G ⧸ K` with a smooth local section `s` of `G → G ⧸ K`, the preimage of
`(m, o)` is `[s o, ι⁻¹ ((s o)⁻¹ • m)]`.

For a Hamiltonian action with coadjoint-equivariant moment map `μ` and a regular value `c` of
`μ`, this is the space `G ×_{G_c} μ⁻¹(c)`, with its maps to the coadjoint orbit `G ⧸ G_c`, to the
symplectic manifold and to the reduced space `μ⁻¹(c) ⧸ G_c`, through which reduction at `c` is
compared with reduction at zero of the shifted moment map on the product with the orbit.

## Main definitions

* `TauCeti.BalancedProduct.rightTranslationChartedSpace`: the charts of the quotient manifold
  theorem on `G ×_K Z`.
* `TauCeti.BalancedProduct.orbitRelQuotientChartedSpaceRightTranslation`: the charts of the
  quotient manifold theorem on the orbit space `(G ×_K Z) ⧸ G`.
* `TauCeti.BalancedProduct.orbitRelQuotientDiffeomorphRightTranslation`: the diffeomorphism
  `(G ×_K Z) ⧸ G ≃ₘ Z ⧸ K`, `G • [g, z] ↦ [z]`.
* `TauCeti.BalancedProduct.liftProjDiffeomorphRightTranslation`: the diffeomorphism from `G ×_K Z`
  onto a submanifold of `M × G ⧸ K` with the image of `[g, z] ↦ (g • ι z, g K)`.

## Main results

* `TauCeti.BalancedProduct.isManifold_rightTranslation`,
  `TauCeti.BalancedProduct.isSubmersion_quotientMk_rightTranslation`: `G ×_K Z` is a smooth
  manifold and the projection from `G × Z` is a smooth submersion.
* `TauCeti.BalancedProduct.contMDiff_iff_rightTranslation`: a map out of `G ×_K Z` is smooth
  exactly when its composite with the projection is.
* `TauCeti.BalancedProduct.contMDiff_orbitProj_rightTranslation`: the projection onto `Z ⧸ K` is
  smooth; `TauCeti.BalancedProduct.contMDiff_orbitProj_rightTranslation_of_contMDiff` is the same
  for any charts on `Z ⧸ K` for which `Z → Z ⧸ K` is smooth.
* `TauCeti.BalancedProduct.isSubmersion_orbitProj_rightTranslation`: the projection onto `Z ⧸ K`
  is a submersion.
* `TauCeti.BalancedProduct.contMDiffSMul_rightTranslation`: `G` acts smoothly on `G ×_K Z`.
* `TauCeti.BalancedProduct.contMDiff_proj_rightTranslation`,
  `TauCeti.BalancedProduct.contMDiff_liftRightTranslation`: the maps to `G ⧸ K` and to a
  `G`-manifold are smooth.
* `TauCeti.BalancedProduct.contMDiff_zeroSectionRightTranslation`,
  `TauCeti.BalancedProduct.isSmoothEmbedding_zeroSectionRightTranslation`: the zero section
  `G ⧸ K → G ×_K Z` at a `K`-fixed point is a smooth embedding.
* `TauCeti.BalancedProduct.contMDiff_liftProjRightTranslation`: the map
  `[g, z] ↦ (g • ι z, g K)` is smooth.
* `TauCeti.BalancedProduct.contMDiff_iff_liftProjRightTranslation_comp`: a map into `G ×_K Z` is
  smooth exactly when its composite with `[g, z] ↦ (g • ι z, g K)` is, for a smooth embedding `ι`.
* `TauCeti.BalancedProduct.isManifold_orbitRelQuotient_rightTranslation`,
  `TauCeti.BalancedProduct.isSubmersion_quotientMk_orbitRelQuotient_rightTranslation`: the orbit
  space of `G` is a smooth manifold and the orbit projection is a smooth submersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem).
-/

public section

noncomputable section

open Function Manifold TauCeti
open scoped ContDiff Manifold

/-! ### Smooth right translation -/

namespace Subgroup.RightTranslation

variable {G : Type*} [Group G] {K : Subgroup G}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace G]
  [ChartedSpace H G]

instance : ChartedSpace H K.RightTranslation := inferInstanceAs (ChartedSpace H G)

instance {n : ℕ∞ω} [IsManifold I n G] : IsManifold I n K.RightTranslation :=
  inferInstanceAs (IsManifold I n G)

theorem contMDiff_toRightTranslation (n : ℕ∞ω) : ContMDiff I I n K.toRightTranslation :=
  contMDiff_id

theorem contMDiff_toRightTranslation_symm (n : ℕ∞ω) :
    ContMDiff I I n K.toRightTranslation.symm :=
  contMDiff_id

variable {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [TopologicalSpace HK]
  {IK : ModelWithCorners 𝕜 EK HK} [ChartedSpace HK K] {n : ℕ∞ω}

/-- Right translation is smooth. -/
instance [LieGroup I n G] [ContMDiffSMul IK I n K G] :
    ContMDiffSMul IK I n K K.RightTranslation where
  contMDiff_smul := (contMDiff_toRightTranslation n).comp
    (((contMDiff_toRightTranslation_symm n).comp contMDiff_snd).mul
      ((K.contMDiff_subtypeVal_of_contMDiffSMul (I' := IK)).comp contMDiff_fst).inv)

end Subgroup.RightTranslation

namespace TauCeti.BalancedProduct

variable {G : Type*} [Group G] {K : Subgroup G} {Z : Type*} [MulAction K Z]

/-! ### The manifold structure -/

section Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ K Z]

variable (K Z I IZ F) in
/-- **The charts of the balanced product** `G ×_K Z`: the charts
`TauCeti.BalancedProduct.chartedSpace` of the quotient manifold theorem, for right translation by
`K` on `G`, which is proper since `K` is closed. They are modelled on
`ℝ^(dim G + dim Z - dim K)`, and they make `G ×_K Z` a smooth manifold
(`TauCeti.BalancedProduct.isManifold_rightTranslation`) for which the projection from `G × Z` is
a smooth submersion (`TauCeti.BalancedProduct.isSubmersion_quotientMk_rightTranslation`). -/
@[instance_reducible]
def rightTranslationChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace F (E × EZ))
      (BalancedProduct K K.RightTranslation Z) :=
  haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
  chartedSpace 𝓘(ℝ, F) K I K.RightTranslation IZ Z

/-- **The balanced product `G ×_K Z` is a smooth manifold**, for the charts
`TauCeti.BalancedProduct.rightTranslationChartedSpace`. -/
theorem isManifold_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (BalancedProduct K K.RightTranslation Z) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact isManifold (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ)

/-- The projection `G × Z → G ×_K Z` is a smooth submersion. -/
theorem isSubmersion_quotientMk_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsSubmersion (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact isSubmersion_quotientMk (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ)

/-- Smoothness descends from `G × Z` to `G ×_K Z`: a map out of the balanced product is `C^m`,
for `m ≤ ∞`, exactly when its composite with the projection is. -/
theorem contMDiff_iff_rightTranslation {EN HN : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} {N : Type*}
    [TopologicalSpace N] [ChartedSpace HN N] {m : ℕ∞ω} (hm : m ≤ ∞)
    {f : BalancedProduct K K.RightTranslation Z → N} :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IN m f ↔
      ContMDiff (I.prod IZ) IN m
        (f ∘ Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact contMDiff_iff (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) hm

/-- The projection `[g, z] ↦ [z]` onto `Z ⧸ K` is smooth for any charts on `Z ⧸ K` for which the
orbit projection `Z → Z ⧸ K` is smooth. -/
theorem contMDiff_orbitProj_rightTranslation_of_contMDiff {EQ HQ : Type*}
    [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {IQ : ModelWithCorners ℝ EQ HQ} [ChartedSpace HQ (MulAction.orbitRel.Quotient K Z)]
    (hπ : ContMDiff IZ IQ ∞ (Quotient.mk (MulAction.orbitRel K Z))) :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IQ ∞
      (orbitProj : BalancedProduct K K.RightTranslation Z → MulAction.orbitRel.Quotient K Z) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact contMDiff_orbitProj_of_contMDiff (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) hπ

/-- **The projection `[g, z] ↦ [z]` onto `Z ⧸ K` is smooth** when `K` acts freely and properly
on `Z`, for the charts `ProperSMul.orbitRelQuotientChartedSpace` of the quotient manifold theorem
on `Z ⧸ K`. -/
theorem contMDiff_orbitProj_rightTranslation [ProperSMul K Z] [IsCancelSMul K Z] :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F EZ) ∞
      (orbitProj : BalancedProduct K K.RightTranslation Z → MulAction.orbitRel.Quotient K Z) :=
  letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
  contMDiff_orbitProj_rightTranslation_of_contMDiff (ProperSMul.contMDiff_quotientMk (I := 𝓘(ℝ, F)))

/-- **The projection `[g, z] ↦ [z]` onto `Z ⧸ K` is a smooth submersion** for every manifold
structure on `Z ⧸ K` for which the orbit projection `Z → Z ⧸ K` is a submersion, such as the
charts of the quotient manifold theorem when `K` acts freely and properly on `Z`. Its fibres are
the orbits of `G` (`TauCeti.BalancedProduct.orbitProj_eq_orbitProj_iff`). -/
theorem isSubmersion_orbitProj_rightTranslation {EQ HQ : Type*} [NormedAddCommGroup EQ]
    [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ} [ChartedSpace HQ (MulAction.orbitRel.Quotient K Z)]
    [IsManifold JQ ∞ (MulAction.orbitRel.Quotient K Z)]
    (hq : IsSubmersion IZ JQ ∞ (Quotient.mk (MulAction.orbitRel K Z))) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsSubmersion 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) JQ ∞
      (orbitProj : BalancedProduct K K.RightTranslation Z → MulAction.orbitRel.Quotient K Z) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact isSubmersion_orbitProj (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) hq

/-- **`G` acts smoothly on the balanced product.** The action lifts along the submersion
`(k, (g, z)) ↦ (k, [g, z])` to `(k, (g, z)) ↦ (k g, z)`, followed by the projection. -/
theorem contMDiffSMul_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiffSMul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ G
      (BalancedProduct K K.RightTranslation Z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := isManifold (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) (K := K) (P := K.RightTranslation)
    (Z := Z)
  have hπ := isSubmersion_quotientMk (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) (K := K)
    (P := K.RightTranslation) (Z := Z)
  refine ⟨((IsSubmersion.id.prodMap hπ).contMDiff_comp_iff
    (surjective_id.prodMap Quotient.mk_surjective) le_rfl).1 ?_⟩
  -- On representatives the action is left multiplication on the first factor.
  have hcomp : (fun p : G × BalancedProduct K K.RightTranslation Z ↦ p.1 • p.2) ∘
      Prod.map id (Quotient.mk _) = Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) ∘
        fun p : G × (K.RightTranslation × Z) ↦
          (K.toRightTranslation (p.1 * K.toRightTranslation.symm p.2.1), p.2.2) :=
    funext fun p ↦ by
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        quotientMk_eq_mk_toRightTranslation, smul_mk_toRightTranslation, Equiv.symm_apply_apply]
  rw [hcomp]
  exact hπ.contMDiff.comp
    (((Subgroup.RightTranslation.contMDiff_toRightTranslation (I := I) ∞).comp (contMDiff_fst.mul
      ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
        contMDiff_snd.fst))).prodMk contMDiff_snd.snd)

/-- **The projection onto `G ⧸ K` is smooth**, for the charts of the homogeneous space
`Subgroup.quotientChartedSpaceOfIsClosed`. -/
theorem contMDiff_proj_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      𝓘(ℝ, Subgroup.QuotientModelSpace I K) ∞
      (proj Z (Subgroup.RightTranslation.quotientMk_smul (K := K))) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [contMDiff_iff (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) le_rfl]
  have hcomp : proj Z (Subgroup.RightTranslation.quotientMk_smul (K := K)) ∘
      Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) =
        fun x ↦ (K.toRightTranslation.symm x.1 : G ⧸ K) :=
    funext fun x ↦ by
      rw [Function.comp_apply, quotientMk_eq_mk_toRightTranslation, proj_mk,
        Subgroup.RightTranslation.quotientMk_toRightTranslation]
  rw [hcomp]
  exact (Subgroup.contMDiff_quotientMk ‹_›).comp
    ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
      (contMDiff_fst (J := IZ) (N := Z)))

/-- **The action map to a `G`-manifold is smooth** when the `K`-equivariant map `ι` is. -/
theorem contMDiff_liftRightTranslation {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
    [ChartedSpace HM M] [MulAction G M] [ContMDiffSMul I IM ∞ G M]
    {ι : Z →ₑ[((↑) : K → G)] M} (hι : ContMDiff IZ IM ∞ ι) :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞ (liftRightTranslation ι) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [contMDiff_iff (IK := 𝓘(ℝ, F)) (IP := I) (IZ := IZ) le_rfl]
  rw [liftRightTranslation_comp_quotientMk]
  exact ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
    (contMDiff_fst (J := IZ) (N := Z))).smul (hι.comp contMDiff_snd)

/-- **The zero section is smooth**: for a point `z₀` of `Z` fixed by `K`, the map
`g K ↦ [g, z₀]` from the homogeneous space `G ⧸ K`, with the charts
`Subgroup.quotientChartedSpaceOfIsClosed`, is smooth. It descends along the submersion
`G → G ⧸ K` from the orbit map `g ↦ g • [1, z₀]`, which is smooth because `G` acts smoothly. -/
theorem contMDiff_zeroSectionRightTranslation {z₀ : Z} (hz₀ : z₀ ∈ MulAction.fixedPoints K Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
    ContMDiff 𝓘(ℝ, Subgroup.QuotientModelSpace I K)
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ (zeroSectionRightTranslation hz₀) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  have := contMDiffSMul_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  refine ((Subgroup.isSubmersion_quotientMk (I := I) ‹_›).contMDiff_comp_iff
    QuotientGroup.mk_surjective le_rfl).1 ?_
  have hcomp : zeroSectionRightTranslation hz₀ ∘ (QuotientGroup.mk : G → G ⧸ K) =
      fun g ↦ g • mk K (K.toRightTranslation 1) z₀ :=
    funext fun g ↦ by simp
  rw [hcomp]
  exact ContMDiffSMul.contMDiff_smul_const _

/-- **The zero section is a smooth embedding.** For a point `z₀` of `Z` fixed by `K`, the map
`G ⧸ K → G ×_K Z`, `g K ↦ [g, z₀]`, is a smooth embedding onto the `G`-orbit of `[1, z₀]`
(`TauCeti.BalancedProduct.range_zeroSectionRightTranslation`): the projection onto `G ⧸ K` is a
smooth left inverse. -/
theorem isSmoothEmbedding_zeroSectionRightTranslation {z₀ : Z}
    (hz₀ : z₀ ∈ MulAction.fixedPoints K Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
    IsSmoothEmbedding 𝓘(ℝ, Subgroup.QuotientModelSpace I K)
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ (zeroSectionRightTranslation hz₀) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  have := isManifold_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) ‹IsClosed (K : Set G)›
  exact (contMDiff_zeroSectionRightTranslation (I := I) (IZ := IZ) (F := F) hz₀
    ).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_proj_rightTranslation (I := I) (IZ := IZ) (F := F)).of_le (by simp))
    (proj_zeroSectionRightTranslation hz₀)

/-! ### `G ×_K Z` as a submanifold of `M × G ⧸ K` -/

section Embedding

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [MulAction G M] [ContMDiffSMul I IM ∞ G M]
  {ι : Z →ₑ[((↑) : K → G)] M}
  {EW HW : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW] [TopologicalSpace HW]
  {IW : ModelWithCorners ℝ EW HW} {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]

/-- **The map `[g, z] ↦ (g • ι z, g K)` is smooth** when `ι` is, for the charts of the
homogeneous space `Subgroup.quotientChartedSpaceOfIsClosed` on `G ⧸ K`. -/
theorem contMDiff_liftProjRightTranslation (hι : ContMDiff IZ IM ∞ ι) :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      (IM.prod 𝓘(ℝ, Subgroup.QuotientModelSpace I K)) ∞ (liftProjRightTranslation ι) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  refine ((contMDiff_liftRightTranslation (I := I) (F := F) hι).prodMk
    (contMDiff_proj_rightTranslation (I := I) (IZ := IZ) (F := F))).congr fun y ↦ ?_
  exact Prod.ext (fst_liftProjRightTranslation ι y) (snd_liftProjRightTranslation ι y)

/-- **Smoothness of maps into `G ×_K Z`.** For a `K`-equivariant smooth embedding `ι`, a map
`ψ : W → G ×_K Z` is smooth exactly when its composite with `[g, z] ↦ (g • ι z, g K)` is. Near a
point `w`, the preimage of `e w' = (g • ι z, g K)` is `[s (e w').2, z']`, for a smooth local section
`s` of `G → G ⧸ K` and the point `z'` with `ι z' = (s (e w').2)⁻¹ • (e w').1`, which depends
smoothly on `w'` since `ι` is a smooth embedding. -/
theorem contMDiff_iff_liftProjRightTranslation_comp (hι : IsSmoothEmbedding IZ IM ∞ ι)
    {ψ : W → BalancedProduct K K.RightTranslation Z} :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
    ContMDiff IW 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ ψ ↔
      ContMDiff IW (IM.prod 𝓘(ℝ, Subgroup.QuotientModelSpace I K)) ∞
        (liftProjRightTranslation ι ∘ ψ) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  refine ⟨(contMDiff_liftProjRightTranslation (I := I) (F := F) hι.contMDiff).comp, fun he ↦ ?_⟩
  generalize hψ : liftProjRightTranslation ι ∘ ψ = e at he
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have hinj := liftProjRightTranslation_injective ι hι.isEmbedding.injective
  intro w
  have hq := Subgroup.isSubmersion_quotientMk (I := I) ‹IsClosed (K : Set G)›
  obtain ⟨U, hU, hwU, s, hs, hsU⟩ :=
    hq.exists_contMDiffOn_section_of_surjective QuotientGroup.mk_surjective (e w).2
  have hmem : ∀ w', (e w').2 ∈ U → (s (e w').2)⁻¹ • (e w').1 ∈ Set.range ι := fun w' hw' ↦
    (mem_range_liftProjRightTranslation_iff ι (hsU _ hw')).1 ⟨ψ w', congrFun hψ w'⟩
  have : Nonempty Z := ⟨(hmem w hwU).choose⟩
  -- The point `z'` of `Z`, read off through the injective map `ι`.
  let z' : W → Z := fun w' ↦ Function.invFun ι ((s (e w').2)⁻¹ • (e w').1)
  have hV : ∀ᶠ w' in nhds w, (e w').2 ∈ U :=
    (he.continuous.snd).continuousAt.preimage_mem_nhds (hU.mem_nhds hwU)
  have hsw : ContMDiffAt IW I ∞ (fun w' ↦ s (e w').2) w :=
    (hs.contMDiffAt (hU.mem_nhds hwU)).comp w (he.snd w)
  have hz' : ContMDiffAt IW IZ ∞ z' w := by
    rw [hι.contMDiffAt_iff_comp]
    refine ContMDiffAt.congr_of_eventuallyEq (hsw.inv.smul (he.fst w)) ?_
    filter_upwards [hV] with w' hw' using Function.invFun_eq (hmem w' hw')
  have hπ := isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ) (F := F) (K := K)
    (Z := Z)
  refine ContMDiffAt.congr_of_eventuallyEq (hπ.contMDiff.contMDiffAt.comp w
    (((Subgroup.RightTranslation.contMDiff_toRightTranslation (I := I) ∞).contMDiffAt.comp w
      hsw).prodMk hz')) ?_
  filter_upwards [hV] with w' hw'
  -- Both points have the image `e w'` under the injective map `[g, z] ↦ (g • ι z, g K)`.
  refine hinj ?_
  simp only [Function.comp_apply, quotientMk_eq_mk_toRightTranslation, Equiv.symm_apply_apply,
    liftProjRightTranslation_mk]
  rw [Function.invFun_eq (hmem w' hw'), smul_inv_smul, hsU _ hw']
  exact congrFun hψ w'

/-- The bijection from `G ×_K Z` onto `W` through `[g, z] ↦ (g • ι z, g K)` and an injective
map `e : W → M × G ⧸ K` with the same image. -/
private def liftProjEquiv (hι : Function.Injective ι) {e : W → M × G ⧸ K}
    (he : Function.Injective e) (hrange : Set.range e = Set.range (liftProjRightTranslation ι)) :
    BalancedProduct K K.RightTranslation Z ≃ W :=
  (Equiv.ofInjective _ (liftProjRightTranslation_injective ι hι)).trans
    ((Set.equivOfEq hrange.symm).trans (Equiv.ofInjective e he).symm)

omit [TopologicalSpace G] [IsClosed (K : Set G)] [TopologicalSpace Z] [T2Space Z]
  [TopologicalSpace M] [TopologicalSpace W] in
private theorem apply_liftProjEquiv (hι : Function.Injective ι) {e : W → M × G ⧸ K}
    (he : Function.Injective e) (hrange : Set.range e = Set.range (liftProjRightTranslation ι))
    (y : BalancedProduct K K.RightTranslation Z) :
    e (liftProjEquiv hι he hrange y) = liftProjRightTranslation ι y := by
  simp only [liftProjEquiv, Equiv.trans_apply]
  exact Equiv.apply_ofInjective_symm he _

variable (ι) in
/-- **`G ×_K Z` is the submanifold `{(m, g K) | g⁻¹ • m ∈ ι(Z)}` of `M × G ⧸ K`.** Let `ι` be a
`K`-equivariant smooth embedding of `Z` into a smooth `G`-manifold `M`, and let `e : W → M × G ⧸ K`
be a smooth embedding with the same image as `[g, z] ↦ (g • ι z, g K)`, that is, onto the pairs
`(m, g K)` with `g⁻¹ • m` in the image of `ι`
(`TauCeti.BalancedProduct.mem_range_liftProjRightTranslation_iff`). Then `[g, z] ↦ (g • ι z, g K)`
lifts to a diffeomorphism `G ×_K Z ≃ W`
(`TauCeti.BalancedProduct.apply_liftProjDiffeomorphRightTranslation`). The inverse is smooth since
the preimage of `(m, o)` is `[s o, ι⁻¹ ((s o)⁻¹ • m)]` for a smooth local section `s` of
`G → G ⧸ K`. -/
def liftProjDiffeomorphRightTranslation (hι : IsSmoothEmbedding IZ IM ∞ ι) {e : W → M × G ⧸ K}
    (he : letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
      IsSmoothEmbedding IW (IM.prod 𝓘(ℝ, Subgroup.QuotientModelSpace I K)) ∞ e)
    (hrange : Set.range e = Set.range (liftProjRightTranslation ι)) :
    letI := rightTranslationChartedSpace K Z I IZ F
    BalancedProduct K K.RightTranslation Z ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)), IW⟯
      W :=
  letI := rightTranslationChartedSpace K Z I IZ F
  letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  { toEquiv := liftProjEquiv hι.isEmbedding.injective he.isEmbedding.injective hrange
    contMDiff_toFun := he.contMDiff_iff_comp.2 <|
      (contMDiff_liftProjRightTranslation (I := I) (F := F) hι.contMDiff).congr fun y ↦
        apply_liftProjEquiv hι.isEmbedding.injective he.isEmbedding.injective hrange y
    contMDiff_invFun := (contMDiff_iff_liftProjRightTranslation_comp (F := F) hι).2 <|
      he.contMDiff.congr fun w ↦ by
        rw [Function.comp_apply, ← apply_liftProjEquiv hι.isEmbedding.injective
          he.isEmbedding.injective hrange, Equiv.apply_symm_apply] }

/-- The diffeomorphism `TauCeti.BalancedProduct.liftProjDiffeomorphRightTranslation` followed by
`e` is `[g, z] ↦ (g • ι z, g K)`. -/
theorem apply_liftProjDiffeomorphRightTranslation (hι : IsSmoothEmbedding IZ IM ∞ ι)
    {e : W → M × G ⧸ K}
    (he : letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
      IsSmoothEmbedding IW (IM.prod 𝓘(ℝ, Subgroup.QuotientModelSpace I K)) ∞ e)
    (hrange : Set.range e = Set.range (liftProjRightTranslation ι))
    (y : BalancedProduct K K.RightTranslation Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    e (liftProjDiffeomorphRightTranslation (F := F) ι hι he hrange y) =
      liftProjRightTranslation ι y := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
  exact apply_liftProjEquiv hι.isEmbedding.injective he.isEmbedding.injective hrange y

/-- The inverse of `TauCeti.BalancedProduct.liftProjDiffeomorphRightTranslation` sends `w` to the
point of `G ×_K Z` whose image under `[g, z] ↦ (g • ι z, g K)` is `e w`. -/
@[simp]
theorem liftProjRightTranslation_liftProjDiffeomorphRightTranslation_symm
    (hι : IsSmoothEmbedding IZ IM ∞ ι) {e : W → M × G ⧸ K}
    (he : letI := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (K : Set G)›
      IsSmoothEmbedding IW (IM.prod 𝓘(ℝ, Subgroup.QuotientModelSpace I K)) ∞ e)
    (hrange : Set.range e = Set.range (liftProjRightTranslation ι)) (w : W) :
    letI := rightTranslationChartedSpace K Z I IZ F
    liftProjRightTranslation ι
        ((liftProjDiffeomorphRightTranslation (F := F) ι hι he hrange).symm w) =
      e w := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  rw [← apply_liftProjDiffeomorphRightTranslation (F := F) hι he hrange,
    Diffeomorph.apply_symm_apply]

end Embedding

/-! ### The orbit space of `G` -/

section OrbitSpace

variable [ProperSMul K Z]

/-- The hypotheses of the quotient manifold theorem for the action of `G` on `G ×_K Z`, other
than freeness: `G ×_K Z` is a manifold on which `G` acts smoothly and properly. -/
private theorem orbitRelQuotient_hypotheses :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
        (BalancedProduct K K.RightTranslation Z) ∧
      ContMDiffSMul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ G
        (BalancedProduct K K.RightTranslation Z) ∧
      ProperSMul G (BalancedProduct K K.RightTranslation Z) :=
  letI := rightTranslationChartedSpace K Z I IZ F
  haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
  ⟨isManifold_rightTranslation, contMDiffSMul_rightTranslation, inferInstance⟩

variable [IsCancelSMul K Z]

variable (K Z I IZ F) in
/-- **The charts of the orbit space of `G` on `G ×_K Z`**: the slice charts
`ProperSMul.orbitRelQuotientChartedSpace` of the quotient manifold theorem for the action
`k • [g, z] = [k g, z]`, which is free and proper when `K` acts freely and properly on `Z`. The
orbit space is diffeomorphic to `Z ⧸ K`
(`TauCeti.BalancedProduct.orbitRelQuotientDiffeomorphRightTranslation`). -/
@[instance_reducible]
def orbitRelQuotientChartedSpaceRightTranslation :
    ChartedSpace (ProperSMul.QuotientModelSpace E (ProperSMul.QuotientModelSpace F (E × EZ)))
      (MulAction.orbitRel.Quotient G (BalancedProduct K K.RightTranslation Z)) :=
  letI := rightTranslationChartedSpace K Z I IZ F
  haveI := (orbitRelQuotient_hypotheses (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)).1
  haveI := (orbitRelQuotient_hypotheses (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)).2.1
  haveI := (orbitRelQuotient_hypotheses (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)).2.2
  ProperSMul.orbitRelQuotientChartedSpace I G 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
    (BalancedProduct K K.RightTranslation Z)

/-- **The orbit space of `G` on `G ×_K Z` is a smooth manifold**, for the charts
`TauCeti.BalancedProduct.orbitRelQuotientChartedSpaceRightTranslation`. -/
theorem isManifold_orbitRelQuotient_rightTranslation :
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (ProperSMul.QuotientModelSpace F (E × EZ))) ∞
      (MulAction.orbitRel.Quotient G (BalancedProduct K K.RightTranslation Z)) := by
  let := rightTranslationChartedSpace K Z I IZ F
  obtain ⟨_, _, _⟩ := orbitRelQuotient_hypotheses (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- The orbit projection `G ×_K Z → (G ×_K Z) ⧸ G` is a smooth submersion. -/
theorem isSubmersion_quotientMk_orbitRelQuotient_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    IsSubmersion 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      𝓘(ℝ, ProperSMul.QuotientModelSpace E (ProperSMul.QuotientModelSpace F (E × EZ))) ∞
      (Quotient.mk (MulAction.orbitRel G (BalancedProduct K K.RightTranslation Z))) := by
  let := rightTranslationChartedSpace K Z I IZ F
  obtain ⟨_, _, _⟩ := orbitRelQuotient_hypotheses (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  exact ProperSMul.isSubmersion_quotientMk (I := I) (G := G)

variable (K Z I IZ F) in
/-- **The orbit space of `G` on `G ×_K Z` is diffeomorphic to `Z ⧸ K`**, by `G • [g, z] ↦ [z]`
with inverse `[z] ↦ G • [1, z]` (`TauCeti.BalancedProduct.orbitRelQuotientEquivRightTranslation`),
for the charts of the quotient manifold theorem on both sides. -/
def orbitRelQuotientDiffeomorphRightTranslation :
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    MulAction.orbitRel.Quotient G (BalancedProduct K K.RightTranslation Z) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace E (ProperSMul.QuotientModelSpace F (E × EZ))),
      𝓘(ℝ, ProperSMul.QuotientModelSpace F EZ)⟯ MulAction.orbitRel.Quotient K Z :=
  letI := rightTranslationChartedSpace K Z I IZ F
  letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
  letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
  haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
  { toEquiv := orbitRelQuotientEquivRightTranslation K Z
    contMDiff_toFun :=
      -- Through the orbit projection of `G`, the map reads as `[g, z] ↦ [z]`.
      ((isSubmersion_quotientMk_orbitRelQuotient_rightTranslation (I := I) (IZ := IZ)
        (F := F)).contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 <|
        (contMDiff_orbitProj_rightTranslation (I := I) (IZ := IZ) (F := F)).congr fun y ↦
          orbitRelQuotientEquivRightTranslation_mk y
    contMDiff_invFun :=
      -- Through the orbit projection of `K`, the inverse reads as `z ↦ G • [1, z]`.
      ((ProperSMul.isSubmersion_quotientMk (I := 𝓘(ℝ, F)) (G := K) (I' := IZ)
        (M := Z)).contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 <|
        ((isSubmersion_quotientMk_orbitRelQuotient_rightTranslation (I := I) (IZ := IZ)
          (F := F)).contMDiff.comp ((isSubmersion_quotientMk_rightTranslation (I := I)
            (IZ := IZ) (F := F)).contMDiff.comp (contMDiff_const.prodMk contMDiff_id))).congr
          fun z ↦ orbitRelQuotientEquivRightTranslation_symm_mk z }

/-- The underlying equivalence of the diffeomorphism is
`TauCeti.BalancedProduct.orbitRelQuotientEquivRightTranslation`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphRightTranslation_toEquiv :
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    (orbitRelQuotientDiffeomorphRightTranslation K Z I IZ F).toEquiv =
      orbitRelQuotientEquivRightTranslation K Z :=
  (rfl)

/-- The diffeomorphism sends the `G`-orbit of `y` to the projection `[z]` of `y = [g, z]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphRightTranslation_mk
    (y : BalancedProduct K K.RightTranslation Z) :
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    orbitRelQuotientDiffeomorphRightTranslation K Z I IZ F (Quotient.mk _ y) = orbitProj y :=
  orbitRelQuotientEquivRightTranslation_mk y

/-- The inverse diffeomorphism sends `[z]` to the `G`-orbit of `[1, z]`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphRightTranslation_symm_mk (z : Z) :
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    (orbitRelQuotientDiffeomorphRightTranslation K Z I IZ F).symm (Quotient.mk _ z) =
      Quotient.mk _ (mk K (K.toRightTranslation 1) z) :=
  orbitRelQuotientEquivRightTranslation_symm_mk z

/-- Composed with the orbit projection of `G`, the diffeomorphism is the projection
`[g, z] ↦ [z]` onto `Z ⧸ K`. -/
@[simp]
theorem orbitRelQuotientDiffeomorphRightTranslation_comp_quotientMk :
    letI := orbitRelQuotientChartedSpaceRightTranslation K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    ⇑(orbitRelQuotientDiffeomorphRightTranslation K Z I IZ F) ∘
      Quotient.mk (MulAction.orbitRel G (BalancedProduct K K.RightTranslation Z)) = orbitProj :=
  funext fun y ↦ orbitRelQuotientEquivRightTranslation_mk y

end OrbitSpace

end Manifold

end TauCeti.BalancedProduct
