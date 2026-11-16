/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Geometry.Lie.Subgroup.Torus.Exhaustion

/-!
# The centralizer of a maximal torus

A maximal torus in a compact connected finite-dimensional real Lie group equals its own
centralizer. The statement applies to arbitrary models with corners.

## Main results

* `TauCeti.Lie.IsMaximalTorus.centralizer_eq`: the centralizer of a maximal torus is the torus.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Corollary 4.52, p.206.
-/

public section

open scoped ContDiff Manifold
noncomputable section
namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [ConnectedSpace G]

include I in
/-- A maximal torus of a compact connected finite-dimensional real Lie group is its own
centralizer. -/
theorem IsMaximalTorus.centralizer_eq {T : Subgroup G} (hT : IsMaximalTorus T) :
    Subgroup.centralizer (T : Set G) = T := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  refine le_antisymm ?_
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hT.isTorus.isMulCommutative)
  intro g hg
  -- A maximal torus through g and T both lie in the closed centralizer of g.
  obtain ⟨S, hS, hgS⟩ := exists_isMaximalTorus_mem I g
  have hTC : T ≤ Subgroup.centralizer ({g} : Set G) := fun t ht ↦
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg t ht)
  have hSC : S ≤ Subgroup.centralizer ({g} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hS.isTorus.isMulCommutative).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hgS))
  -- Conjugacy needs compactness of the centralizer, not connectedness. Its conjugator fixes g.
  obtain ⟨c, hc, hmap⟩ := hS.exists_mem_map_conj_eq_of_le I (Set.isClosed_centralizer _) hT
    hSC hTC
  have hconj : c * g * c⁻¹ = g := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  exact hmap ▸ ⟨g, hgS, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj]⟩

end TauCeti.Lie
