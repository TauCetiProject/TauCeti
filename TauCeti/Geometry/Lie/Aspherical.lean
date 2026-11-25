/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import TauCeti.AlgebraicTopology.EilenbergMacLane.QuotientProd
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Connectivity
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Classification
public import TauCeti.Geometry.Lie.Interior

import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
import TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane
import TauCeti.Geometry.Lie.UniversalCover.Compact
import TauCeti.Topology.Algebra.Group.Quotient.Prod

/-!
# Aspherical compact Lie groups

A compact Lie group is a compact manifold without boundary
(`ContMDiffMul.boundarylessManifold`), so it cannot be weakly contractible unless it is a single
point (`TauCeti.IsAspherical.subsingleton_of_boundarylessManifold`). Hence a compact Lie group that
is simply connected and aspherical is trivial
(`TauCeti.IsAspherical.subsingleton_of_contMDiffMul`).

This decides which compact Lie groups are aspherical. Let `G` be a compact Lie group presented as
a quotient `(A × K) ⧸ Γ`, where `A` is a contractible commutative group, such as a real vector
space, `K` is a simply connected Lie group whose Lie algebra is perfect and has trivial centre, and
`Γ` is a discrete normal subgroup with central image in `K`. A compact connected Lie group has such
a presentation through its universal cover, with `A` the centre of its Lie algebra and `K`
integrating the derived algebra (Bröcker–tom Dieck, Chapter V, Theorem 8.1). The quotient of `K`
by the image of `Γ` is compact (`Subgroup.compactSpace_quotient_map_snd`), so `K` is compact
(`Subgroup.compactSpace_of_le_center_of_derivedSeries_one_eq_top`), and the higher homotopy groups
of `G` are those of `K` (`Subgroup.isAspherical_quotient_iff`). So if `G` is aspherical, then so is
`K`, and `K` is trivial; then `G` is a quotient of the commutative group `A`, hence a compact
connected commutative Lie group, which is a torus (`TauCeti.nonempty_continuousMulEquiv_pi_circle`).
Conversely a torus is aspherical. Hence `G` is aspherical exactly when it is isomorphic to a torus
`(S¹)ʳ` (`Subgroup.isAspherical_iff_exists_continuousMulEquiv_torus`).

## Main results

* `TauCeti.IsAspherical.subsingleton_of_contMDiffMul`: a simply connected aspherical compact Lie
  group is trivial.
* `Subgroup.isAspherical_iff_exists_continuousMulEquiv_torus`: a compact Lie group presented as
  `(A × K) ⧸ Γ` as above is aspherical exactly when it is a torus.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and
  Proposition 6.31).
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, Theorem 8.1.
-/

public section

open scoped Manifold

universe w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **A simply connected aspherical compact Lie group is trivial.** A compact Hausdorff group with
`Cⁿ` multiplication, `n ≥ 1`, modelled with corners on a finite-dimensional real normed space,
which is simply connected and aspherical has a single element. -/
theorem IsAspherical.subsingleton_of_contMDiffMul {G : Type w} [TopologicalSpace G] [T2Space G]
    [ChartedSpace H G] [Group G] {n : WithTop ℕ∞} [ContMDiffMul I n G] (hn : 1 ≤ n)
    [CompactSpace G] [SimplyConnectedSpace G] (hG : IsAspherical G 1) : Subsingleton G := by
  have := ContMDiffMul.of_le (I := I) (G := G) hn
  have := ContMDiffMul.boundarylessManifold (I := I) (G := G)
  exact hG.subsingleton_of_boundarylessManifold (I := I)

end TauCeti

namespace Subgroup

open TauCeti
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K] [LieGroup I' ∞ K]
  [SimplyConnectedSpace K]
  {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [ContractibleSpace A]

include I in
/-- **The torus criterion.** Let `G` be a compact Lie group isomorphic to a quotient `(A × K) ⧸ Γ`,
where `A` is a contractible commutative topological group, `K` is a simply connected Lie group
whose Lie algebra is perfect and has trivial centre, and `Γ` is a discrete normal subgroup whose
image in `K` is central. Then `G` is aspherical exactly when it is isomorphic, as a topological
group, to a torus `(S¹)ʳ`. -/
theorem isAspherical_iff_exists_continuousMulEquiv_torus (Γ : Subgroup (A × K)) [Γ.Normal]
    [DiscreteTopology Γ] (h : LieAlgebra.derivedSeries ℝ (LeftInvariantDerivation I' K) 1 = ⊤)
    (hz : LieAlgebra.center ℝ (LeftInvariantDerivation I' K) = ⊥)
    (hΓ : Γ.map (MonoidHom.snd A K) ≤ center K) (e : G ≃ₜ* (A × K) ⧸ Γ) :
    IsAspherical G 1 ↔ ∃ r : ℕ, Nonempty (G ≃ₜ* (Fin r → Circle)) := by
  refine ⟨fun hG ↦ ?_, fun ⟨r, ⟨f⟩⟩ ↦
    (Circle.isAspherical_pi (f 1)).of_homotopyEquiv f.symm.toHomeomorph.toHomotopyEquiv 1⟩
  have : IsTopologicalGroup K := topologicalGroup_of_lieGroup I' ∞
  have : T2Space K := I'.t2Space_of_lieGroup ∞
  have : CompactSpace ((A × K) ⧸ Γ) := e.surjective.compactSpace e.continuous
  have : CompactSpace K :=
    (Γ.map (MonoidHom.snd A K)).compactSpace_of_le_center_of_derivedSeries_one_eq_top h hz hΓ
  -- The higher homotopy groups of `K` are those of `G`, so the compact `K` is a point.
  have hK := ((Γ.isAspherical_quotient_iff (e 1)).1
    (hG.of_homotopyEquiv e.toHomeomorph.toHomotopyEquiv (e 1))).2
  have : Subsingleton K :=
    IsAspherical.subsingleton_of_contMDiffMul (I := I') (n := ∞) (by simp) (.mk inferInstance hK)
  -- So `G` is a quotient of the commutative group `A × K`, hence a torus.
  have : IsMulCommutative K := ⟨⟨fun _ _ ↦ Subsingleton.elim _ _⟩⟩
  have : IsMulCommutative ((A × K) ⧸ Γ) := (QuotientGroup.mk'_surjective Γ).isMulCommutative
  have : IsMulCommutative G := e.symm.surjective.isMulCommutative
  have := hG.pathConnectedSpace
  exact ⟨_, nonempty_continuousMulEquiv_pi_circle (I := I)⟩

end Subgroup
