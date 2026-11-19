/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Topology.Covering.BalancedProduct.RightTranslation
public import TauCeti.Algebra.GroupAction.DiagonalOrbits
public import TauCeti.Topology.Algebra.ProperAction.Basic

import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The balanced product `G ×_K Z` of a Lie group with a manifold acted on by a closed subgroup

Let `G` be a finite-dimensional real Lie group with boundaryless model and `K` a closed subgroup,
with a Lie group structure for which it acts smoothly on `G` by left multiplication, such as its
closed-subgroup structure (`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`). Let `K` act smoothly
on a Hausdorff boundaryless manifold `Z`. The balanced product `G ×_K Z`, the quotient of `G × Z`
by `h • (g, z) = (g h⁻¹, h • z)`, is `TauCeti.BalancedProduct K (Subgroup.RightTranslation K) Z`;
its algebra and topology are in `TauCeti.Topology.Covering.BalancedProduct.RightTranslation`.

Right translation by `K` on `G` is smooth, free, and proper because `K` is closed. So the
diagonal action of `K` on `G × Z` is free and proper (`TauCeti.isCancelSMul_prod`,
`TauCeti.properSMul_prod`), and by the quotient manifold theorem `G ×_K Z` is a smooth manifold of
dimension `dim G + dim Z - dim K` (`TauCeti.BalancedProduct.rightTranslationChartedSpace`), for
which `(g, z) ↦ [g, z]` is a smooth submersion. The action `k • [g, z] = [k g, z]` of `G` and the
three maps `[g, z] ↦ g K`, `[g, z] ↦ g • ι z` and `[g, z] ↦ [z]` are smooth, the last one when `K`
acts freely and properly on `Z`, so that `Z ⧸ K` is itself a manifold.

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
* `TauCeti.BalancedProduct.contMDiffSMul_rightTranslation`: `G` acts smoothly on `G ×_K Z`.
* `TauCeti.BalancedProduct.contMDiff_proj_rightTranslation`,
  `TauCeti.BalancedProduct.contMDiff_lift`, `TauCeti.BalancedProduct.contMDiff_orbitProj`: the
  three maps are smooth.

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

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace G] [ChartedSpace H G]

instance : ChartedSpace H K.RightTranslation := inferInstanceAs (ChartedSpace H G)

instance {n : ℕ∞ω} [IsManifold I n G] : IsManifold I n K.RightTranslation :=
  inferInstanceAs (IsManifold I n G)

theorem contMDiff_toRightTranslation (n : ℕ∞ω) : ContMDiff I I n K.toRightTranslation :=
  contMDiff_id

theorem contMDiff_toRightTranslation_symm (n : ℕ∞ω) :
    ContMDiff I I n K.toRightTranslation.symm :=
  contMDiff_id

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ChartedSpace F K]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]

/-- Right translation is smooth. -/
instance [LieGroup I ∞ G] : ContMDiffSMul 𝓘(ℝ, F) I ∞ K K.RightTranslation where
  contMDiff_smul := (contMDiff_toRightTranslation ∞).comp
    (((contMDiff_toRightTranslation_symm ∞).comp contMDiff_snd).mul
      ((K.contMDiff_subtypeVal_of_contMDiffSMul (I' := 𝓘(ℝ, F))).comp contMDiff_fst).inv)

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ EZ] [IZ.Boundaryless]
  [IsManifold IZ ∞ Z] [FiniteDimensional ℝ F] [LieGroup 𝓘(ℝ, F) ∞ K]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G] in
include I IZ F in
/-- The hypotheses of the quotient manifold theorem for the diagonal action of `K` on `G × Z`,
other than those found by instance search. -/
private theorem quotient_hypotheses :
    ProperSMul K (K.RightTranslation × Z) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IZ) (G := K) (M := Z) ∞
  infer_instance

variable (K Z I IZ F) in
/-- **The charts of the balanced product** `G ×_K Z`: the slice charts of the quotient manifold
theorem `ProperSMul.orbitRelQuotientChartedSpace` for the free and proper diagonal action of `K`
on `G × Z`, modelled on `ℝ^(dim G + dim Z - dim K)`. -/
@[instance_reducible]
def rightTranslationChartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace F (E × EZ))
      (BalancedProduct K K.RightTranslation Z) :=
  haveI := quotient_hypotheses (I := I) (IZ := IZ) (F := F) (K := K) (Z := Z)
  ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K (I.prod IZ) (K.RightTranslation × Z)

/-- **The balanced product is a smooth manifold**, for the charts
`TauCeti.BalancedProduct.rightTranslationChartedSpace`. -/
theorem isManifold_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (BalancedProduct K K.RightTranslation Z) := by
  have := quotient_hypotheses (I := I) (IZ := IZ) (F := F) (K := K) (Z := Z)
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- The projection `G × Z → G ×_K Z` is a smooth submersion. -/
theorem isSubmersion_quotientMk_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsSubmersion (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) := by
  have := quotient_hypotheses (I := I) (IZ := IZ) (F := F) (K := K) (Z := Z)
  exact ProperSMul.isSubmersion_quotientMk

/-- Smoothness descends from `G × Z` to `G ×_K Z`: a map out of the balanced product is `C^m`,
for `m ≤ ∞`, exactly when its composite with the projection is. -/
theorem contMDiff_iff_rightTranslation {EP HP : Type*} [NormedAddCommGroup EP]
    [NormedSpace ℝ EP] [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} {P : Type*}
    [TopologicalSpace P] [ChartedSpace HP P] {m : ℕ∞ω} (hm : m ≤ ∞)
    {f : BalancedProduct K K.RightTranslation Z → P} :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IP m f ↔
      ContMDiff (I.prod IZ) IP m
        (f ∘ Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  exact ((isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ)
    (F := F)).contMDiff_comp_iff Quotient.mk_surjective hm).symm

/-- **`G` acts smoothly on the balanced product.** The action lifts along the submersion
`(k, (g, z)) ↦ (k, [g, z])` to `(k, (g, z)) ↦ (k g, z)`, followed by the projection. -/
theorem contMDiffSMul_rightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiffSMul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ G
      (BalancedProduct K K.RightTranslation Z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := isManifold_rightTranslation (I := I) (IZ := IZ) (K := K) (Z := Z) (F := F)
  have hπ := isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ) (K := K) (Z := Z)
    (F := F)
  refine ⟨((IsSubmersion.id.prodMap hπ).contMDiff_comp_iff
    (surjective_id.prodMap Quotient.mk_surjective) le_rfl).1 ?_⟩
  -- On representatives the action is left multiplication on the first factor.
  have hcomp : (fun p : G × BalancedProduct K K.RightTranslation Z ↦ p.1 • p.2) ∘
      Prod.map id (Quotient.mk _) = Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) ∘
        fun p : G × (K.RightTranslation × Z) ↦
          (K.toRightTranslation (p.1 * K.toRightTranslation.symm p.2.1), p.2.2) :=
    (rfl)
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
  rw [contMDiff_iff_rightTranslation (I := I) (IZ := IZ) (F := F) le_rfl]
  have hcomp : proj Z (Subgroup.RightTranslation.quotientMk_smul (K := K)) ∘
      Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) =
        Subgroup.RightTranslation.quotientMk K ∘ Prod.fst :=
    funext fun x ↦ proj_mk Z Subgroup.RightTranslation.quotientMk_smul x.1 x.2
  rw [hcomp]
  exact (Subgroup.contMDiff_quotientMk ‹_›).comp
    ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
      (contMDiff_fst (J := IZ) (N := Z)))

/-- **The action map to a `G`-manifold is smooth** when the `K`-equivariant map `ι` is. -/
theorem contMDiff_lift {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
    [ChartedSpace HM M] [MulAction G M] [ContMDiffSMul I IM ∞ G M]
    {ι : Z →ₑ[((↑) : K → G)] M} (hι : ContMDiff IZ IM ∞ ι) :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞ (lift ι) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  rw [contMDiff_iff_rightTranslation (I := I) (IZ := IZ) (F := F) le_rfl]
  exact ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
    (contMDiff_fst (J := IZ) (N := Z))).smul (hι.comp contMDiff_snd)

/-- **The projection onto `Z ⧸ K` is smooth** when `K` acts freely and properly on `Z`, for the
charts `ProperSMul.orbitRelQuotientChartedSpace` of the quotient manifold theorem on `Z ⧸ K`. -/
theorem contMDiff_orbitProj [ProperSMul K Z] [IsCancelSMul K Z] :
    letI := rightTranslationChartedSpace K Z I IZ F
    letI := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F EZ) ∞
      (orbitProj : BalancedProduct K K.RightTranslation Z → MulAction.orbitRel.Quotient K Z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  let _ := ProperSMul.orbitRelQuotientChartedSpace 𝓘(ℝ, F) K IZ Z
  rw [contMDiff_iff_rightTranslation (I := I) (IZ := IZ) (F := F) le_rfl]
  exact ProperSMul.contMDiff_quotientMk.comp (contMDiff_snd (I := I) (M := K.RightTranslation))

end Manifold

end TauCeti.BalancedProduct
