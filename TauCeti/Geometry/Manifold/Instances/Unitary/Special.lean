/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The special unitary group as a smooth Lie group

For `𝕜 = ℝ` or `ℂ` (any `RCLike` field), Mathlib's special unitary group
`Matrix.specialUnitaryGroup n 𝕜`, the unitary matrices of determinant one, is a compact topological
group for the subspace topology of `Matrix n n 𝕜`. This file makes it a smooth real Lie group on
that topology, with a smooth embedding into the matrices. For `𝕜 = ℝ` this is the special
orthogonal group `SO(n)`, Mathlib's `Matrix.specialOrthogonalGroup n ℝ`, which is the same
submonoid.

The atlas comes from the closed-subgroup theorem. The same group, seen as the subgroup
`TauCeti.GLSpecialUnitary n 𝕜` of the Lie group of units `GL n 𝕜`, is closed
(`TauCeti.isClosed_GLSpecialUnitary`), so it is an embedded Lie subgroup modelled on its Lie
algebra. The topological group isomorphism `TauCeti.GLSpecialUnitary.continuousMulEquiv`, which
sends a unit to its underlying matrix, carries this structure to `Matrix.specialUnitaryGroup n 𝕜`.
This is the construction of the native structure of the unitary group
(`Unitary.instChartedSpace`), applied to the special unitary subgroup of the units. The model space
is therefore the Lie algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to
`TauCeti.GLSpecialUnitary n 𝕜` when the matrices carry the `ℓ²` operator norm. For the `L∞`
operator norm, `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff`
identifies this Lie algebra in matrix coordinates with the trace-free skew-Hermitian matrices.

The inclusion into the matrices is a smooth embedding, so a map into the special unitary group is
`C^n` exactly when its matrix coercion is. In particular the inclusion of the special unitary group
into the unitary group `Matrix.unitaryGroup n 𝕜`, with its native structure, is a smooth embedding.
These are the smooth structures that the polar and Cartan coordinates of the special linear group
take values in: the special unitary group is a factor of the targets of
`Matrix.SpecialLinearGroup.polarHomeomorph` and `Matrix.SpecialLinearGroup.cartanHomeomorph`.

As for the unitary group, matrices carry the `ℓ²` operator norm. To state or use the smooth
structure, `open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `Matrix.specialUnitaryGroup.model`: the real vector-space model, the Lie algebra of the closed
  subgroup `TauCeti.GLSpecialUnitary n 𝕜`.
* `Matrix.specialUnitaryGroup.instChartedSpace`, `Matrix.specialUnitaryGroup.instIsManifold`,
  `Matrix.specialUnitaryGroup.instLieGroup`: the smooth Lie-group structure.
* `Matrix.specialUnitaryGroup.contMDiff_val`, `Matrix.specialUnitaryGroup.isImmersion_val`,
  `Matrix.specialUnitaryGroup.isSmoothEmbedding_val`: the inclusion into the matrices.
* `Matrix.specialUnitaryGroup.contMDiffWithinAt_iff`, `Matrix.specialUnitaryGroup.contMDiffAt_iff`,
  `Matrix.specialUnitaryGroup.contMDiffOn_iff`, `Matrix.specialUnitaryGroup.contMDiff_iff`:
  smoothness of maps into the special unitary group, tested after coercion to the matrices.
* `Matrix.specialUnitaryGroup.isSmoothEmbedding_inclusion_unitaryGroup`: the inclusion into the
  unitary group is a smooth embedding.
* `Matrix.specialUnitaryGroup.instContMDiffSMul`: a smooth action of the matrices restricts to the
  special unitary group.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 (closed subgroups) and Proposition 7.11 (embedded Lie subgroups).
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Section 1.2 (the special unitary and special orthogonal groups as matrix Lie groups).
-/

public section

open scoped ContDiff Manifold Matrix.Norms.L2Operator
noncomputable section

namespace Matrix.specialUnitaryGroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

local notation "𝕂" => TauCeti.GLSpecialUnitary n 𝕜
local notation "𝔰𝔲" => LieSubalgebra.toSubmodule
  (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) 𝕂)

-- Name the submodule structures with their ambient space: a search through the Lie subalgebra at
-- the concrete matrix algebra with its operator norm exceeds the default typeclass budget.
/-- The norm on the special unitary model is inherited from the ambient Lie algebra. -/
instance instNormedAddCommGroupModel : NormedAddCommGroup 𝔰𝔲 :=
  Submodule.normedAddCommGroup (E := LeftInvariantDerivation 𝓘(ℝ, Matrix n n 𝕜) (GL n 𝕜)) 𝔰𝔲

/-- The special unitary model is a real normed vector subspace of the ambient Lie algebra. -/
instance instNormedSpaceModel : NormedSpace ℝ 𝔰𝔲 :=
  Submodule.normedSpace (𝕜 := ℝ) (R := ℝ)
    (E := LeftInvariantDerivation 𝓘(ℝ, Matrix n n 𝕜) (GL n 𝕜)) 𝔰𝔲

variable (n 𝕜) in
/-- The vector-space model of the special unitary group: the Lie algebra of its embedded subgroup
of units `TauCeti.GLSpecialUnitary n 𝕜`. -/
abbrev model : ModelWithCorners ℝ 𝔰𝔲 𝔰𝔲 := 𝓘(ℝ, 𝔰𝔲)

/-- The special unitary group has a smooth real Lie-group atlas for its subspace topology, with an
immersive inclusion into the matrices. -/
private theorem exists_nativeStructure :
    ∃ c : ChartedSpace 𝔰𝔲 (specialUnitaryGroup n 𝕜),
      let _ := c
      IsManifold (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) ∧
        Manifold.IsImmersion (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
          (Subtype.val : specialUnitaryGroup n 𝕜 → Matrix n n 𝕜) ∧
        LieGroup (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) := by
  -- Use the closed-subgroup charts of `GLSpecialUnitary` in the units, and pull them back along
  -- the topological group isomorphism with the matrix special unitary group. The pulled-back
  -- diffeomorphism transfers the immersion, and the group isomorphism the Lie-group laws.
  obtain ⟨d⟩ := TauCeti.Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := 𝓘(ℝ, Matrix n n 𝕜)) (K := 𝕂) (TauCeti.isClosed_GLSpecialUnitary n 𝕜)
  let _ : ChartedSpace 𝔰𝔲 𝕂 := d.chartedSpace
  let _ : LieGroup (model n 𝕜) ∞ 𝕂 := d.lieGroup
  let f := (TauCeti.GLSpecialUnitary.continuousMulEquiv n 𝕜).symm
  let c := f.toHomeomorph.pullbackChartedSpace (H := 𝔰𝔲)
  let _ : ChartedSpace 𝔰𝔲 (specialUnitaryGroup n 𝕜) := c
  have hm : IsManifold (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) :=
    f.toHomeomorph.pullback_isManifold (model n 𝕜) ∞
  let φ := f.toHomeomorph.pullbackDiffeomorph (model n 𝕜) ∞
  have hphi : (fun A : specialUnitaryGroup n 𝕜 ↦ ((φ A : GL n 𝕜) : Matrix n n 𝕜)) =
      Subtype.val := by
    funext A
    simp only [φ, Homeomorph.coe_pullbackDiffeomorph, f]
    exact TauCeti.GLSpecialUnitary.coe_continuousMulEquiv_symm_apply A
  -- The inclusion of the closed subgroup into the units is an immersion; composing with the
  -- coercion `GL n 𝕜 → Matrix n n 𝕜`, which is the chart of the units at `1`, keeps it one.
  have hi₀ : Manifold.IsImmersion (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (fun x : 𝕂 ↦ (x : GL n 𝕜)) :=
    d.contMDiff_subtypeVal.isImmersion_of_injective_mfderiv (by simp)
      fun x ↦ d.injective_mfderiv_subtypeVal x
  have hi₁ : Manifold.IsImmersion (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (fun x : 𝕂 ↦ ((x : GL n 𝕜) : Matrix n n 𝕜)) :=
    TauCeti.isImmersion_isLocalDiffeomorphAt_comp (k := chartAt (Matrix n n 𝕜) (1 : GL n 𝕜))
      (fun _ ↦ (chartAt (Matrix n n 𝕜) (1 : GL n 𝕜)).isLocalDiffeomorphAt_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (1 : GL n 𝕜)) (by simp)) hi₀
  have hi : Manifold.IsImmersion (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (Subtype.val : specialUnitaryGroup n 𝕜 → Matrix n n 𝕜) :=
    (TauCeti.isImmersion_comp_isLocalDiffeomorph φ.isLocalDiffeomorph hi₁).congr hphi
  exact ⟨c, hm, hi, f.lieGroup_pullbackChartedSpace (I := model n 𝕜) (n := ∞)⟩

/-- The native atlas of the special unitary group, induced by its closed embedding into the units.
Its public properties are `instIsManifold`, `instLieGroup` and `isSmoothEmbedding_val`; individual
charts are not specified. -/
instance instChartedSpace : ChartedSpace 𝔰𝔲 (specialUnitaryGroup n 𝕜) :=
  Classical.choose (show ∃ c : ChartedSpace 𝔰𝔲 (specialUnitaryGroup n 𝕜),
      let _ := c
      IsManifold (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) ∧
        Manifold.IsImmersion (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
          (Subtype.val : specialUnitaryGroup n 𝕜 → Matrix n n 𝕜) ∧
        LieGroup (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) from by
    exact exists_nativeStructure)

/-- The special unitary group is a smooth real manifold. -/
instance instIsManifold : IsManifold (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) :=
  (Classical.choose_spec (exists_nativeStructure (n := n) (𝕜 := 𝕜))).1

/-- The special unitary group is a smooth real Lie group. -/
instance instLieGroup : LieGroup (model n 𝕜) ∞ (specialUnitaryGroup n 𝕜) :=
  (Classical.choose_spec (exists_nativeStructure (n := n) (𝕜 := 𝕜))).2.2

/-- The inclusion of the special unitary group into the matrices is an immersion. -/
theorem isImmersion_val : Manifold.IsImmersion (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
    (Subtype.val : specialUnitaryGroup n 𝕜 → Matrix n n 𝕜) :=
  (Classical.choose_spec (exists_nativeStructure (n := n) (𝕜 := 𝕜))).2.1

/-- The inclusion of the special unitary group into the matrices is a smooth embedding. -/
theorem isSmoothEmbedding_val : Manifold.IsSmoothEmbedding (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
    (Subtype.val : specialUnitaryGroup n 𝕜 → Matrix n n 𝕜) :=
  ⟨isImmersion_val, .subtypeVal⟩

/-- The inclusion of the special unitary group into the matrices is smooth. -/
theorem contMDiff_val : ContMDiff (model n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) ∞
    (Subtype.val : specialUnitaryGroup n 𝕜 → Matrix n n 𝕜) :=
  isSmoothEmbedding_val.contMDiff

section SmoothnessIff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ∞ω} [ENat.LEInfty k] {f : M → specialUnitaryGroup n 𝕜} {s : Set M} {x : M}

/-- A map into the special unitary group is `C^k` within a set at a point if and only if its
coercion to the matrices is. The `ENat.LEInfty k` hypothesis excludes real-analytic regularity
`ω`, as the atlas is `C^∞`. -/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I (model n 𝕜) k f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Matrix n n 𝕜) k (fun y ↦ (f y : Matrix n n 𝕜)) s x :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiffWithinAt_iff_comp

/-- A map into the special unitary group is `C^k` at a point if and only if its coercion to the
matrices is. -/
theorem contMDiffAt_iff :
    ContMDiffAt I (model n 𝕜) k f x ↔
      ContMDiffAt I 𝓘(ℝ, Matrix n n 𝕜) k (fun y ↦ (f y : Matrix n n 𝕜)) x :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiffAt_iff_comp

/-- A map into the special unitary group is `C^k` on a set if and only if its coercion to the
matrices is. -/
theorem contMDiffOn_iff :
    ContMDiffOn I (model n 𝕜) k f s ↔
      ContMDiffOn I 𝓘(ℝ, Matrix n n 𝕜) k (fun y ↦ (f y : Matrix n n 𝕜)) s :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiffOn_iff_comp

/-- A map into the special unitary group is `C^k` if and only if its coercion to the matrices
is. -/
theorem contMDiff_iff :
    ContMDiff I (model n 𝕜) k f ↔
      ContMDiff I 𝓘(ℝ, Matrix n n 𝕜) k (fun y ↦ (f y : Matrix n n 𝕜)) :=
  (isSmoothEmbedding_val.of_le ENat.LEInfty.out).contMDiff_iff_comp

end SmoothnessIff

/-- The inclusion of the special unitary group into the unitary group is a smooth embedding, for
the native smooth structures of both groups. -/
theorem isSmoothEmbedding_inclusion_unitaryGroup :
    Manifold.IsSmoothEmbedding (model n 𝕜) (Unitary.model (Matrix n n 𝕜)) ∞
      (Submonoid.inclusion (specialUnitaryGroup_le_unitaryGroup (n := n) (α := 𝕜))) :=
  -- Its composite with the embedding of the unitary group into the matrices is the immersive
  -- inclusion of the special unitary group.
  ⟨Unitary.isSmoothEmbedding_val.isImmersion_of_isImmersion_comp (by simp) isImmersion_val,
    .of_comp (continuous_inclusion specialUnitaryGroup_le_unitaryGroup) continuous_subtypeVal
      .subtypeVal⟩

/-- Any `C^k` action (`k ≤ ∞`) of the matrices on a manifold restricts to a `C^k` action of the
special unitary group. -/
instance instContMDiffSMul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {k : ℕ∞ω} [ENat.LEInfty k]
    [MulAction (Matrix n n 𝕜) M] [ContMDiffSMul 𝓘(ℝ, Matrix n n 𝕜) I k (Matrix n n 𝕜) M] :
    ContMDiffSMul (model n 𝕜) I k (specialUnitaryGroup n 𝕜) M :=
  MulAction.contMDiffSMul_compHom (f := (specialUnitaryGroup n 𝕜).subtype)
    (contMDiff_val.of_le ENat.LEInfty.out)

end Matrix.specialUnitaryGroup
