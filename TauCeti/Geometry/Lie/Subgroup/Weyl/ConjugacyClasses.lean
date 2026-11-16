/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.GroupTheory.Subgroup.NormalizerOrbit
import TauCeti.Geometry.Lie.Subgroup.Torus.Exhaustion
import TauCeti.Topology.Algebra.Group.Conjugacy

/-!
# Conjugacy classes and the normalizer of a maximal torus

Two elements of a maximal torus `T` of a compact Lie group `G` that are conjugate in `G` are
conjugate by an element of the normalizer `N(T)`: if `g t g⁻¹ = u`, then `T` and `g T g⁻¹` are
maximal tori of the closed subgroup `C(u)`, so some `c` in `C(u)` conjugates `g T g⁻¹` to `T`, and
`c g` normalizes `T` and still conjugates `t` to `u`. Maximal tori are conjugate in any compact Lie
group, so neither `G` nor `C(u)` needs to be connected.

If `G` is also connected, then the conjugates of `T` cover `G`, so the orbit space of `N(T)` on `T`
is the space of conjugacy classes of `G`, as a topological space. This reduces class functions on
`G` to functions on `T` invariant under the Weyl group `N(T) / T`.

## Main results

* `TauCeti.Lie.IsMaximalTorus.exists_mem_normalizer_conj`: elements of a maximal torus conjugate
  in `G` are conjugate in the normalizer.
* `TauCeti.Lie.IsMaximalTorus.bijective_normalizerOrbitMap`: for connected `G`, every conjugacy
  class meets `T` in exactly one `N(T)`-orbit.
* `TauCeti.Lie.IsMaximalTorus.normalizerOrbitHomeomorph`: for connected `G`, the orbit space of
  `N(T)` on `T` is homeomorphic to the conjugation orbit space of `G`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §§ 1–2.
-/

public section

open MulAction
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G]

include I

/-- **Conjugacy in a maximal torus is controlled by its normalizer.** Two elements of a maximal
torus of a compact Lie group that are conjugate in the group are conjugate by an element of the
normalizer of the torus. -/
theorem IsMaximalTorus.exists_mem_normalizer_conj {T : Subgroup G} (hT : IsMaximalTorus T)
    {t u : G} (ht : t ∈ T) (hu : u ∈ T) (h : IsConj t u) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), n * t * n⁻¹ = u := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  have hS := hT.map_conj g
  -- Both `T` and `g T g⁻¹` contain `u = g t g⁻¹`, so they lie in the closed centralizer of `u`.
  have hle : ∀ {S : Subgroup G}, IsTorus S → g * t * g⁻¹ ∈ S →
      S ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := fun hS' hmem ↦
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hS'.isMulCommutative).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmem))
  obtain ⟨c, hc, hmap⟩ := hS.exists_mem_map_conj_eq_of_le I (Set.isClosed_centralizer _) hT
    (hle hS.isTorus ⟨t, ht, rfl⟩) (hle hT.isTorus hu)
  refine ⟨c * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, map_mul]
    exact (Subgroup.map_map _ _ _).symm.trans hmap
  · calc c * g * t * (c * g)⁻¹ = c * (g * t * g⁻¹) * c⁻¹ := by group
      _ = g * t * g⁻¹ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

/-- For a compact connected Lie group, every conjugacy class meets a maximal torus in exactly one
orbit of the normalizer. -/
theorem IsMaximalTorus.bijective_normalizerOrbitMap [ConnectedSpace G] {T : Subgroup G}
    (hT : IsMaximalTorus T) : Function.Bijective T.normalizerOrbitMap :=
  ⟨T.normalizerOrbitMap_injective_iff.mpr fun _ ht _ hu ↦ hT.exists_mem_normalizer_conj I ht hu,
    T.normalizerOrbitMap_surjective_iff.mpr (hT.iUnion_map_conj_eq_univ I)⟩

/-- For a maximal torus `T` of a compact connected Lie group `G`, the orbit space of the normalizer
on `T` is homeomorphic to the space of conjugacy classes of `G`, through the inclusion of `T`. -/
def IsMaximalTorus.normalizerOrbitHomeomorph [ConnectedSpace G] {T : Subgroup G}
    (hT : IsMaximalTorus T) :
    orbitRel.Quotient (Subgroup.normalizer (T : Set G)) T ≃ₜ orbitRel.Quotient (ConjAct G) G :=
  letI : T2Space G := I.t2Space_of_lieGroup ∞
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT.isTorus.isCompact
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (hT.bijective_normalizerOrbitMap I))
    T.continuous_normalizerOrbitMap

/-- The homeomorphism of `IsMaximalTorus.normalizerOrbitHomeomorph` sends the orbit of `t` to the
conjugacy class of `t`. -/
@[simp]
theorem IsMaximalTorus.normalizerOrbitHomeomorph_mk [ConnectedSpace G] {T : Subgroup G}
    (hT : IsMaximalTorus T) (t : T) :
    hT.normalizerOrbitHomeomorph I (Quotient.mk'' t) = Quotient.mk'' (t : G) :=
  T.normalizerOrbitMap_mk t

end TauCeti.Lie
