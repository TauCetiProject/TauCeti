/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Geometry.Lie.Subgroup.Quotient
public import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Orbits as homogeneous spaces

Let a finite-dimensional real Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G` act smoothly
on the left on a manifold `M`, and fix `x : M`. The orbit map `g ↦ g • x` is studied in
`TauCeti.Geometry.Manifold.GroupAction.Orbit`; this file factors it through the homogeneous space
`G ⧸ G_x`.

At an arbitrary point the orbit map is constant on the cosets of the stabilizer `G_x`, which is a
closed subgroup when points of `M` are closed (`TauCeti.isClosed_stabilizer`). So it factors
through the homogeneous space `G ⧸ G_x`, with the charts of
`Subgroup.quotientChartedSpaceOfIsClosed`, as Mathlib's map `[g] ↦ g • x`
(`MulAction.ofQuotientStabilizer G x`). This map is smooth, and the image of its differential at
`[g]` is the orbit tangent space `𝔤 · (g • x)` (`TauCeti.range_mfderiv_ofQuotientStabilizer`). Since
the Lie algebra of `G_x` is the isotropy algebra `𝔤_x`
(`TauCeti.Lie.lieSubalgebraOfSubgroup_stabilizer`), the homogeneous space has the dimension
`dim 𝔤 - dim 𝔤_x` of that image, so the differential is injective
(`TauCeti.injective_mfderiv_ofQuotientStabilizer`). Hence:

* for every smooth action on a Hausdorff manifold, `[g] ↦ g • x` is an injective immersion of
  `G ⧸ G_x` onto the orbit of `x` (`TauCeti.isImmersion_ofQuotientStabilizer`);
* for a proper action it is moreover a closed topological embedding
  (`ProperSMul.isClosedEmbedding_ofQuotientStabilizer`), so **every orbit of a proper smooth action
  is a closed embedded submanifold, the image of the smooth embedding `[g] ↦ g • x` of the
  homogeneous space `G ⧸ G_x`** (`TauCeti.isSmoothEmbedding_ofQuotientStabilizer`). The stabilizer
  is then compact (`ProperSMul.isCompact_stabilizer`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Proposition 21.7 (orbits
  of proper actions are closed embedded submanifolds).
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [CompleteSpace E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [I.Boundaryless] [I'.Boundaryless]

/-! ### The orbit map of the homogeneous space `G ⧸ G_x` -/

section QuotientStabilizer

omit [CompleteSpace E] [CompleteSpace E'] [IsManifold I' ∞ M] [FiniteDimensional ℝ E']
  [I'.Boundaryless] in
/-- **The orbit map of `G ⧸ G_x` is smooth.** The map `[g] ↦ g • x`
(`MulAction.ofQuotientStabilizer G x`) out of the homogeneous space `G ⧸ G_x`, with the charts of
`Subgroup.quotientChartedSpaceOfIsClosed` for the closed subgroup `G_x`, is smooth: its composite
with the submersion `G → G ⧸ G_x` is the orbit map `g ↦ g • x`. The stabilizer of a point of a
`T₁` manifold is always closed (`TauCeti.isClosed_stabilizer`); the closedness proof `hx` only
selects the charts. -/
theorem contMDiff_ofQuotientStabilizer {x : M}
    (hx : IsClosed (MulAction.stabilizer G x : Set G)) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hx
    ContMDiff 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I' ∞
      (MulAction.ofQuotientStabilizer G x) := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hx
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) hx
  exact ((Subgroup.isSubmersion_quotientMk (I := I) hx).contMDiff_comp_iff
    QuotientGroup.mk_surjective le_rfl).1 (ContMDiffSMul.contMDiff_smul_const x)

omit [CompleteSpace E] [CompleteSpace E'] [IsManifold I' ∞ M] [FiniteDimensional ℝ E']
  [I'.Boundaryless] in
/-- **The differential of the orbit map of `G ⧸ G_x`.** Composed with the differential of the
projection `G → G ⧸ G_x` at `g`, the differential of `[g] ↦ g • x` at `[g]` is the differential of
the orbit map `g ↦ g • x` at `g`. -/
theorem mfderiv_ofQuotientStabilizer_comp_mfderiv_quotientMk {x : M}
    (hx : IsClosed (MulAction.stabilizer G x : Set G)) (g : G) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hx
    (mfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I'
        (MulAction.ofQuotientStabilizer G x) (g : G ⧸ MulAction.stabilizer G x)).comp
      (mfderiv I 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x))
        (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x) g) =
      mfderiv I I' (fun h : G ↦ h • x) g := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hx
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) hx
  have hπ := Subgroup.isSubmersion_quotientMk (I := I) hx
  exact (mfderiv_comp g ((contMDiff_ofQuotientStabilizer hx).mdifferentiableAt (by simp))
    (hπ.contMDiff.mdifferentiableAt (by simp))).symm

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] in
/-- **The tangent space of an orbit.** The image of the differential of `[g] ↦ g • x` at a point
`q` of `G ⧸ G_x` is the orbit tangent space `𝔤 · y` at its image `y`, spanned by the values of the
fundamental vector fields. -/
theorem range_mfderiv_ofQuotientStabilizer {x : M}
    (hx : IsClosed (MulAction.stabilizer G x : Set G)) (q : G ⧸ MulAction.stabilizer G x) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hx
    LinearMap.range (mfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I'
        (MulAction.ofQuotientStabilizer G x) q).toLinearMap =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent
        (MulAction.ofQuotientStabilizer G x q) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hx
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) hx
  have hπ := Subgroup.isSubmersion_quotientMk (I := I) hx
  -- The differential of the projection is onto, so both differentials have the same image.
  rw [← LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (hπ.surjective_mfderiv (by simp) g)),
    ← ContinuousLinearMap.toLinearMap_comp,
    mfderiv_ofQuotientStabilizer_comp_mfderiv_quotientMk hx g]
  exact range_mfderiv_smul_const x g

omit [CompleteSpace E] [FiniteDimensional ℝ E'] in
/-- **The differential of the orbit map of `G ⧸ G_x` is injective.** At every point of
`G ⧸ G_x`, the differential of `[g] ↦ g • x` has the rank `dim 𝔤 - dim 𝔤_x` of the orbit map,
which is the dimension of `G ⧸ G_x`, since the Lie algebra of `G_x` is the isotropy algebra
`𝔤_x`. -/
theorem injective_mfderiv_ofQuotientStabilizer [T2Space M] {x : M}
    (hx : IsClosed (MulAction.stabilizer G x : Set G)) (q : G ⧸ MulAction.stabilizer G x) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hx
    Injective (mfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I'
      (MulAction.ofQuotientStabilizer G x) q) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hx
  -- The differential at `[g]` has the image of the differential of the orbit map at `g`.
  have hrange : Module.finrank ℝ (LinearMap.range (mfderiv
        𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I'
        (MulAction.ofQuotientStabilizer G x) (g : G ⧸ MulAction.stabilizer G x)).toLinearMap) =
      Module.finrank ℝ (LinearMap.range (mfderiv I I' (fun h : G ↦ h • x) g).toLinearMap) := by
    rw [range_mfderiv_ofQuotientStabilizer, range_mfderiv_smul_const,
      MulAction.ofQuotientStabilizer_mk]
  have hrank := finrank_range_mfderiv_smul_const_add_finrank_isotropy (I := I) (I' := I') x g
  have hdim := Subgroup.finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I
    (MulAction.stabilizer G x) hx
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have hstab := Lie.finrank_lieSubalgebraOfSubgroup_stabilizer (I := I) (I' := I')
    (BoundarylessManifold.isInteriorPoint (M := G)) x
  have hker := LinearMap.finrank_range_add_finrank_ker
    (mfderiv 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I'
      (MulAction.ofQuotientStabilizer G x) (g : G ⧸ MulAction.stabilizer G x)).toLinearMap
  rw [hrange] at hker
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  -- `dim 𝔤 - dim 𝔤_x = dim (G ⧸ G_x)`, so the kernel is zero-dimensional. For `omega` to match
  -- the dimension counts, `e₁` and `e₃` hold because `GroupLieAlgebra I G` and the tangent spaces
  -- of `G ⧸ G_x` unfold to their model spaces, and `e₂` because a Lie subalgebra and its
  -- underlying submodule have the same carrier.
  have e₁ : Module.finrank ℝ (GroupLieAlgebra I G) = Module.finrank ℝ E := rfl
  have e₂ : Module.finrank ℝ (Lie.lieSubalgebraOfSubgroup (I := I)
      (MulAction.stabilizer G x)).toSubmodule =
      Module.finrank ℝ (Lie.lieSubalgebraOfSubgroup (I := I) (MulAction.stabilizer G x)) := rfl
  have e₃ : Module.finrank ℝ (TangentSpace
      𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x))
      (g : G ⧸ MulAction.stabilizer G x)) =
      Module.finrank ℝ (Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) := rfl
  omega

omit [CompleteSpace E] [CompleteSpace E'] in
/-- **The orbit map of `G ⧸ G_x` is an injective immersion.** For any smooth action of a
finite-dimensional Lie group on a Hausdorff manifold, `[g] ↦ g • x` is an immersion of the
homogeneous space `G ⧸ G_x` onto the orbit of `x`; it is injective by the definition of `G_x`
(`MulAction.injective_ofQuotientStabilizer`). -/
theorem isImmersion_ofQuotientStabilizer [T2Space M] {x : M}
    (hx : IsClosed (MulAction.stabilizer G x : Set G)) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hx
    IsImmersion 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I' ∞
      (MulAction.ofQuotientStabilizer G x) := by
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hx
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) hx
  exact (contMDiff_ofQuotientStabilizer hx).isImmersion_of_injective_mfderiv (by simp)
    (injective_mfderiv_ofQuotientStabilizer hx)

end QuotientStabilizer

/-! ### Orbits of proper actions -/

section Proper

variable [ProperSMul G M]

omit [CompleteSpace E] [CompleteSpace E'] in
/-- **Orbits of proper smooth actions are closed embedded submanifolds.** For a proper smooth
action of a finite-dimensional Lie group, `[g] ↦ g • x` is a smooth embedding of the homogeneous
space `G ⧸ G_x` with image the orbit of `x`, a closed set (`ProperSMul.isClosed_orbit`). Its
differential at `[g]` maps onto the orbit tangent space `𝔤 · (g • x)`
(`TauCeti.range_mfderiv_ofQuotientStabilizer`). The stabilizer `G_x` is compact
(`ProperSMul.isCompact_stabilizer`). -/
theorem isSmoothEmbedding_ofQuotientStabilizer {x : M}
    (hx : IsClosed (MulAction.stabilizer G x : Set G)) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hx
    IsSmoothEmbedding 𝓘(ℝ, Subgroup.QuotientModelSpace I (MulAction.stabilizer G x)) I' ∞
      (MulAction.ofQuotientStabilizer G x) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hx
  exact ⟨isImmersion_ofQuotientStabilizer hx,
    (ProperSMul.isClosedEmbedding_ofQuotientStabilizer x).isEmbedding⟩

end Proper

end TauCeti
