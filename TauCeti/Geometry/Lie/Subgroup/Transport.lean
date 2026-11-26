/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Lie-group atlases transported from closed subgroups

By the closed-subgroup theorem, a closed subgroup `K` of a finite-dimensional real Lie group `G`
is an embedded Lie subgroup modelled on its Lie algebra. Many concrete groups, such as the unitary
elements of a normed star algebra or the special unitary matrices, are not literally subgroups of
a Lie group but are identified with one by a topological group isomorphism `e : M ≃ₜ* K`. This
file pulls the closed-subgroup structure of `K` back along `e`, so that `M` becomes a smooth real
Lie group for its own topology, and the composite of `e` with the inclusion `K → G` is a smooth
immersion.

When `G` is the group of units of a finite-dimensional real normed algebra `R`, composing further
with the inclusion `Rˣ → R`, which is the chart of the units at `1`, keeps the immersion.

## Main declarations

* `TauCeti.Lie.IsLieGroupAtlas`: an atlas making a group a smooth real Lie group, together with a
  smooth immersion into a manifold.
* `TauCeti.Lie.exists_isLieGroupAtlas_of_isClosed`: the atlas transported from a closed subgroup
  along a topological group isomorphism.
* `Units.isImmersion_val_comp`: an immersion into the units of a complete normed algebra stays an
  immersion into the algebra.
* `TauCeti.Lie.exists_isLieGroupAtlas_units_of_isClosed`: the transported atlas for a closed
  subgroup of the units of a normed algebra, with an immersion into the algebra.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 (closed subgroups) and Proposition 7.11 (embedded Lie subgroups).
-/

public section

open scoped ContDiff Manifold
noncomputable section

namespace Units

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- Composing an immersion into the units of a complete normed algebra with the inclusion into the
algebra gives an immersion, since that inclusion is the chart of the units at `1`. -/
theorem isImmersion_val_comp {f : M → Rˣ} (hf : Manifold.IsImmersion I 𝓘(𝕜, R) n f) :
    Manifold.IsImmersion I 𝓘(𝕜, R) n (val ∘ f) :=
  -- `chartAt R (1 : Rˣ)` is defined to be `Units.val` on `Set.univ`.
  TauCeti.isImmersion_isLocalDiffeomorphAt_comp (k := chartAt R (1 : Rˣ))
    (fun _ ↦ (chartAt R (1 : Rˣ)).isLocalDiffeomorphAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (1 : Rˣ)) (by simp)) hf

end Units

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- An atlas `c` on a group `M`, modelled on the real normed space `E'`, making `M` a smooth real
Lie group for which `ι : M → N` is smooth and an immersion. -/
structure IsLieGroupAtlas {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {M : Type*} [TopologicalSpace M] [Group M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (ι : M → N) (c : ChartedSpace E' M) : Prop where
  /-- The atlas is a smooth real manifold structure. -/
  isManifold : let _ := c; IsManifold 𝓘(ℝ, E') ∞ M
  /-- The map `ι` is smooth. -/
  contMDiff : let _ := c; ContMDiff 𝓘(ℝ, E') I ∞ ι
  /-- The map `ι` is an immersion. -/
  isImmersion : let _ := c; Manifold.IsImmersion 𝓘(ℝ, E') I ∞ ι
  /-- Multiplication and inversion are smooth. -/
  lieGroup : let _ := c; LieGroup 𝓘(ℝ, E') ∞ M

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [T2Space G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {M : Type*} [TopologicalSpace M] [Group M]

/-- **Transport of the closed-subgroup structure.** If a topological group `M` is isomorphic to a
closed subgroup `K` of a finite-dimensional real Lie group `G`, then `M` has a smooth real
Lie-group atlas, modelled on the Lie algebra of `K`, for which the composite `ι` of the isomorphism
with the inclusion `K → G` is a smooth immersion. -/
theorem exists_isLieGroupAtlas_of_isClosed {K : Subgroup G} (hK : IsClosed (K : Set G))
    (e : M ≃ₜ* K) {ι : M → G} (hι : ∀ x, ((e x : K) : G) = ι x) :
    ∃ c : ChartedSpace (lieSubalgebraOfSubgroup (I := I) K).toSubmodule M,
      IsLieGroupAtlas I ι c := by
  -- Use the closed-subgroup charts on `K`, then pull them back along `e`. The pulled-back
  -- diffeomorphism transfers the smooth immersive inclusion, and the group isomorphism the
  -- Lie-group laws.
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed (I := I) hK
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let c := e.toHomeomorph.pullbackChartedSpace
    (H := (lieSubalgebraOfSubgroup (I := I) K).toSubmodule)
  let _ := c
  have hm := e.toHomeomorph.pullback_isManifold
    𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞
  let φ := e.toHomeomorph.pullbackDiffeomorph
    𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ∞
  have hφ : (fun x : M ↦ ((φ x : K) : G)) = ι := by
    funext x
    simp only [φ, Homeomorph.coe_pullbackDiffeomorph]
    exact hι x
  exact ⟨c,
    { isManifold := hm
      contMDiff := (d.contMDiff_subtypeVal.comp φ.contMDiff).congr fun x ↦ (congrFun hφ x).symm
      isImmersion := (TauCeti.isImmersion_comp_isLocalDiffeomorph φ.isLocalDiffeomorph
        d.isSmoothEmbedding_subtypeVal.isImmersion).congr hφ
      lieGroup := e.lieGroup_pullbackChartedSpace }⟩

/-- **Transport of the closed-subgroup structure, for the units of a normed algebra.** If a
topological group `M` is isomorphic to a closed subgroup `K` of the units of a finite-dimensional
real normed algebra `R`, then `M` has a smooth real Lie-group atlas, modelled on the Lie algebra
of `K`, for which the composite `ι : M → R` of the isomorphism with the inclusion `K → R` is a
smooth immersion. -/
theorem exists_isLieGroupAtlas_units_of_isClosed {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [FiniteDimensional ℝ R] {K : Subgroup Rˣ} (hK : IsClosed (K : Set Rˣ)) (e : M ≃ₜ* K)
    {ι : M → R} (hι : ∀ x, (((e x : K) : Rˣ) : R) = ι x) :
    ∃ c : ChartedSpace (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, R)) K).toSubmodule M,
      IsLieGroupAtlas 𝓘(ℝ, R) ι c := by
  have : CompleteSpace R := FiniteDimensional.completeSpace ℝ R
  obtain ⟨c, hc⟩ := exists_isLieGroupAtlas_of_isClosed (I := 𝓘(ℝ, R)) hK e fun _ ↦ rfl
  let _ := c
  have hι' : Units.val ∘ (fun x ↦ ((e x : K) : Rˣ)) = ι := funext hι
  exact ⟨c,
    { isManifold := hc.isManifold
      contMDiff := hι' ▸ Units.contMDiff_val.comp hc.contMDiff
      isImmersion := hι' ▸ Units.isImmersion_val_comp hc.isImmersion
      lieGroup := hc.lieGroup }⟩

end TauCeti.Lie
