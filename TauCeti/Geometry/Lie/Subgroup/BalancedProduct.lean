/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Manifold.GroupAction.BalancedProduct
public import TauCeti.Topology.Covering.BalancedProduct.RightTranslation

import TauCeti.Geometry.Manifold.Algebra.SMul
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

For a Hamiltonian action with coadjoint-equivariant moment map `μ` and a regular value `c` of
`μ`, this is the space `G ×_{G_c} μ⁻¹(c)`, with its maps to the coadjoint orbit `G ⧸ G_c`, to the
symplectic manifold and to the reduced space `μ⁻¹(c) ⧸ G_c`, through which reduction at `c` is
compared with reduction at zero of the shifted moment map on the product with the orbit.

## Main definitions

* `TauCeti.BalancedProduct.rightTranslationChartedSpace`: the charts of the quotient manifold
  theorem on `G ×_K Z`.

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
  have hcomp :
      liftRightTranslation ι ∘ Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) =
        fun x ↦ K.toRightTranslation.symm x.1 • ι x.2 :=
    funext fun x ↦ by
      rw [Function.comp_apply, quotientMk_eq_mk_toRightTranslation, liftRightTranslation_mk]
  rw [hcomp]
  exact ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
    (contMDiff_fst (J := IZ) (N := Z))).smul (hι.comp contMDiff_snd)

end Manifold

end TauCeti.BalancedProduct
