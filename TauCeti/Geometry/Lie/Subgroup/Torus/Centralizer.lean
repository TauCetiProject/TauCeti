/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Geometry.Lie.Subgroup.Torus.Exhaustion

/-!
# Centralizers of tori

In a compact connected finite-dimensional real Lie group, a maximal torus equals its own
centralizer, and the centralizer of any torus is connected. The statements apply to arbitrary
models with corners.

Both work in the centralizer `K` of an element `g`, a compact Lie group by Cartan's closed-subgroup
theorem in which `g` is central, and use that its maximal tori are conjugate in `K`. If `g`
centralizes a torus `S`, a maximal torus of `K` containing `S` is conjugate in `K` to a maximal
torus through `g`, by an element commuting with `g`, so it contains `g`. Thus `S` and `g` lie in a
common torus, which joins `1` to `g` inside the centralizer of `S`.
The full centralizer of an element need not be connected: in `SO(3)` the centralizer of
`diag(1, -1, -1)` is a copy of `O(2)`.

## Main results

* `TauCeti.Lie.IsMaximalTorus.centralizer_eq`: the centralizer of a maximal torus is the torus.
* `TauCeti.Lie.IsTorus.exists_isTorus_le_mem_of_mem_centralizer`: an element centralizing a torus
  lies in a common torus with it.
* `TauCeti.Lie.IsTorus.isConnected_centralizer`: the centralizer of a torus is connected.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Corollary 4.52, p.206.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 2.
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

include I in
/-- **An element centralizing a torus lies in a common torus with it.** In a compact connected
finite-dimensional real Lie group, if `h` commutes with every element of a torus `S`, then some
torus contains both `S` and `h`. -/
theorem IsTorus.exists_isTorus_le_mem_of_mem_centralizer {S : Subgroup G} (hS : IsTorus S) {h : G}
    (hh : h ∈ Subgroup.centralizer (S : Set G)) : ∃ R : Subgroup G, IsTorus R ∧ S ≤ R ∧ h ∈ R := by
  -- The centralizer `K` of `h` is a compact Lie group containing `S` and a maximal torus `T`
  -- through `h`. A maximal torus of `K` containing `S` is conjugate in `K` to `T`, and the
  -- conjugating element commutes with `h`, so it contains `h`.
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  -- `S` and a maximal torus `T` through `h` lie in the closed centralizer `K` of `h`.
  let K := Subgroup.centralizer ({h} : Set G)
  have hK : IsClosed (K : Set G) := Set.isClosed_centralizer _
  have hSK : S ≤ K := fun s hs ↦
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hh s hs)
  obtain ⟨T, hT, hhT⟩ := exists_isMaximalTorus_mem I h
  have hTK : T ≤ K :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hT.isTorus.isMulCommutative).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hhT))
  -- Cartan's theorem makes `K` a compact Lie group; it need not be connected.
  let L := (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := I) (K := K) hK
  let _ : ChartedSpace L K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, L) ∞ K := d.lieGroup
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  -- A maximal torus `S'` of `K` containing `S` is conjugate in `K` to `T`. The conjugating element
  -- `c` commutes with `h`, which therefore lies in `S'`.
  obtain ⟨S', hS', hSS'⟩ := (hS.subgroupOf hSK).exists_isMaximalTorus_le 𝓘(ℝ, L)
  obtain ⟨c, hc⟩ := hS'.exists_map_conj_eq 𝓘(ℝ, L) (hT.subgroupOf hTK)
  set x : K := ⟨h, hTK hhT⟩
  obtain ⟨s, hs, hcs⟩ : x ∈ S'.map (MulAut.conj c).toMonoidHom :=
    hc ▸ Subgroup.mem_subgroupOf.mpr hhT
  have hcx : c * x = x * c := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property)
  have hsx : s = x := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcs
    calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = x := by rw [hcs, mul_assoc, ← hcx, inv_mul_cancel_left]
  exact ⟨S'.map K.subtype, hS'.isTorus.map K.subtype continuous_subtypeVal,
    fun t ht ↦ ⟨⟨t, hSK ht⟩, hSS' (Subgroup.mem_subgroupOf.mpr ht), rfl⟩, ⟨x, hsx ▸ hs, rfl⟩⟩

include I in
/-- **The centralizer of a torus is connected.** In a compact connected finite-dimensional real Lie
group, the centralizer of a torus `S` is connected. -/
theorem IsTorus.isConnected_centralizer {S : Subgroup G} (hS : IsTorus S) :
    IsConnected (Subgroup.centralizer (S : Set G) : Set G) := by
  -- Each element `h` of the centralizer lies in a torus containing `S`, which is a connected
  -- subset of the centralizer joining `1` to `h`.
  set C := Subgroup.centralizer (S : Set G)
  refine ⟨⟨1, C.one_mem⟩, isPreconnected_of_forall 1 fun h hh ↦ ?_⟩
  obtain ⟨R, hR, hSR, hhR⟩ := hS.exists_isTorus_le_mem_of_mem_centralizer I hh
  -- A torus containing `S` is commutative, so it lies in the centralizer of `S`.
  have hRC : (R : Set G) ⊆ C := fun r hr s hs ↦
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hR.isMulCommutative hr s (hSR hs)
  exact ⟨R, hRC, R.one_mem, hhR, hR.isConnected.isPreconnected⟩

end TauCeti.Lie
