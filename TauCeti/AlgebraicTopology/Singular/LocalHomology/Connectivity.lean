/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Retraction
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.Geometry.Manifold.ModelTransport.Finrank
public import TauCeti.Geometry.Manifold.ModelTransport.Interior

/-!
# Compact manifolds are not highly connected

A nonempty compact `n`-manifold `M` has a fundamental class with coefficients in any
Dedekind-finite ring `K` whose only unit is `1`, such as `ZMod 2`, with no orientation hypothesis
(`TauCeti.existsUnique_isFundamentalClass_of_subsingleton_units`). Its image in the local homology
at a point generates a nontrivial module, so it is nonzero, and the top homology `Hₙ(M; K)` is
nontrivial (`TauCeti.nontrivial_singularHomology_of_subsingleton_units`).

On the other hand, if the homotopy groups `πₖ(M, x)` are trivial for all `k ≤ n`, the Hurewicz
vanishing theorem (`TauCeti.isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup`) kills
`Hₙ(M; K)` as soon as `n ≥ 1`. So a nonempty compact `n`-manifold with `n ≥ 1` has a nontrivial
homotopy group in some degree at most `n`: it is not `n`-connected
(`TauCeti.exists_le_nontrivial_homotopyGroup`). The bound is sharp, since the sphere `Sⁿ` is
`(n - 1)`-connected, and compactness is needed, since `ℝⁿ` is contractible.

A compact manifold whose homotopy groups vanish up to its dimension therefore has dimension zero
(`TauCeti.finrank_eq_zero_of_subsingleton_homotopyGroup`). Being path-connected, it is then a
single point (`TauCeti.subsingleton_of_subsingleton_homotopyGroup`). In particular a compact
manifold that is simply connected and aspherical, that is, weakly contractible, is a point
(`TauCeti.IsAspherical.subsingleton_of_simplyConnectedSpace`). This is how the asphericity of a
compact connected Lie group `G` is detected on the simply connected compact factor `K` of a finite
cover `T × K → G` by a torus `T`: the covering and the torus do not change the higher homotopy
groups, so if `G` is aspherical then so is `K`, which is therefore trivial.

Apart from the last section, the manifolds are topological: `M` is a Hausdorff space charted on a
finite-dimensional real normed space, with no smooth structure. The last section treats compact
boundaryless `C¹` manifolds modelled with corners, by reading their charts in the model vector
space (`TauCeti.BoundarylessModel`).

## Main results

* `TauCeti.nontrivial_singularHomology_of_subsingleton_units`: the top homology of a nonempty
  compact manifold is nontrivial with coefficients in a nontrivial ring whose only unit is `1`.
* `TauCeti.exists_le_nontrivial_homotopyGroup`: a nonempty compact `n`-manifold with `n ≥ 1` is
  not `n`-connected.
* `TauCeti.finrank_eq_zero_of_subsingleton_homotopyGroup`: a compact manifold whose homotopy groups
  vanish up to its dimension has dimension zero.
* `TauCeti.subsingleton_of_subsingleton_homotopyGroup`: such a manifold is a point.
* `TauCeti.IsAspherical.subsingleton_of_simplyConnectedSpace`: a simply connected aspherical
  compact manifold is a point.
* `TauCeti.IsAspherical.subsingleton_of_boundarylessManifold`: a simply connected aspherical
  compact boundaryless `C¹` manifold modelled with corners is a point.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.26 (the mod `2` fundamental class) and Theorem 4.32 (the Hurewicz theorem).
-/

public section

open AlgebraicTopology CategoryTheory Limits Module
open scoped Topology

universe w

namespace TauCeti

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **The top homology of a compact manifold is nontrivial.** On a nonempty compact `n`-manifold,
with coefficients in a nontrivial Dedekind-finite ring `K` whose only unit is `1`, such as
`ZMod 2`, the homology `Hₙ(M; K)` is nontrivial. No orientation and no connectedness is
needed. -/
theorem nontrivial_singularHomology_of_subsingleton_units (K : Type w) [Ring K]
    [IsDedekindFiniteMonoid K] [Subsingleton Kˣ] [Nontrivial K] [CompactSpace M] [Nonempty M]
    {n : ℕ} (hn : finrank ℝ E = n) :
    Nontrivial (((singularHomologyFunctor (ModuleCat.{w} K) n).obj (ModuleCat.of K K)).obj
      (TopCat.of M)) := by
  -- Move to a model space in the universe of `M`, as the fundamental class requires.
  let _ : ChartedSpace (ULift.{w} (Fin n) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [hn])
  have hn' : finrank ℝ (ULift.{w} (Fin n) → ℝ) = n := by simp
  obtain ⟨μ, hμ, -⟩ := existsUnique_isFundamentalClass_of_subsingleton_units K (M := M) hn'
  have : Nontrivial (ModuleCat.of K K) := inferInstanceAs (Nontrivial K)
  exact ⟨μ, 0, fun h ↦ not_isFundamentalClass_zero hn' (M := M) (ModuleCat.of K K) (h ▸ hμ)⟩

/-- **A compact `n`-manifold is not `n`-connected.** A nonempty compact Hausdorff space charted on a
real normed space of finite dimension `n ≥ 1` has a nontrivial homotopy group `πₖ(M, x)` in some
degree `k ≤ n`, at every point `x`. The bound is sharp: the sphere `Sⁿ` has `πₖ(Sⁿ) = 0` for
`k < n`. -/
theorem exists_le_nontrivial_homotopyGroup [CompactSpace M] {n : ℕ} (hn : finrank ℝ E = n)
    (hn0 : n ≠ 0) (x : M) : ∃ k ≤ n, Nontrivial (π_ k M x) := by
  by_contra! h
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have : Subsingleton (ULift.{w} (ZMod 2))ˣ :=
    (Units.map_injective (f := (ULift.ringEquiv : ULift.{w} (ZMod 2) ≃+* ZMod 2).toMonoidHom)
      ULift.ringEquiv.injective).subsingleton
  have : Nonempty M := ⟨x⟩
  -- The fundamental class makes `Hₙ(M; ℤ/2)` nontrivial, while the Hurewicz theorem kills it.
  have hnt := nontrivial_singularHomology_of_subsingleton_units (ULift.{w} (ZMod 2)) (M := M) hn
  refine not_subsingleton _ (ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_subsingleton_homotopyGroup (X := TopCat.of M) (x := x)
      (n := n + 1) (fun k hk ↦ ?_) (ULift.{w} (ZMod 2)) hn0 n.lt_succ_self))
  exact h k (Nat.le_of_lt_succ hk)

/-- **A compact manifold that is connected up to its dimension has dimension zero.** If the
homotopy groups `πₖ(M, x)` of a compact Hausdorff space charted on a finite-dimensional real
normed space `E` vanish for all `k ≤ dim E`, then `dim E = 0`. -/
theorem finrank_eq_zero_of_subsingleton_homotopyGroup [CompactSpace M] (x : M)
    (h : ∀ k ≤ finrank ℝ E, Subsingleton (π_ k M x)) : finrank ℝ E = 0 := by
  by_contra hne
  obtain ⟨k, hk, hkx⟩ := exists_le_nontrivial_homotopyGroup (M := M) rfl hne x
  exact not_nontrivial_iff_subsingleton.2 (h k hk) hkx

/-- **A compact manifold that is connected up to its dimension is a point.** If the homotopy groups
`πₖ(M, x)` of a compact Hausdorff space charted on a finite-dimensional real normed space `E` vanish
for all `k ≤ dim E`, then `M` is a single point. -/
theorem subsingleton_of_subsingleton_homotopyGroup [CompactSpace M] (x : M)
    (h : ∀ k ≤ finrank ℝ E, Subsingleton (π_ k M x)) : Subsingleton M := by
  have : Subsingleton E :=
    finrank_zero_iff.1 (finrank_eq_zero_of_subsingleton_homotopyGroup x h)
  have : DiscreteTopology M := ChartedSpace.discreteTopology E M
  have : PathConnectedSpace M :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).2 (h 0 (Nat.zero_le _))
  exact subsingleton_of_preconnected_totallyDisconnected

include E in
/-- **A weakly contractible compact manifold is a point.** A compact Hausdorff space charted on a
finite-dimensional real normed space which is simply connected and aspherical is a single point. -/
theorem IsAspherical.subsingleton_of_simplyConnectedSpace [CompactSpace M] [SimplyConnectedSpace M]
    {x : M} (hM : IsAspherical M x) : Subsingleton M := by
  refine subsingleton_of_subsingleton_homotopyGroup (E := E) x fun k _ ↦ ?_
  match k with
  | 0 | 1 => exact subsingleton_homotopyGroup_of_lt_two x (by omega)
  | k + 2 => exact hM.subsingleton_homotopyGroup k

section Boundaryless

open scoped Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **A weakly contractible compact boundaryless manifold is a point.** A compact Hausdorff `C¹`
manifold without boundary, modelled with corners on a finite-dimensional real normed space, which
is simply connected and aspherical is a single point. -/
theorem IsAspherical.subsingleton_of_boundarylessManifold {N : Type w} [TopologicalSpace N]
    [T2Space N] [ChartedSpace H N] [IsManifold I 1 N] [BoundarylessManifold I N] [CompactSpace N]
    [SimplyConnectedSpace N] {x : N} (hN : IsAspherical N x) : Subsingleton N := by
  -- The same space with its charts read in the model vector space `E`, reached through the
  -- identity homeomorphism, which carries simple connectivity and asphericity across.
  let _ : ChartedSpace E (BoundarylessModel I N) := BoundarylessModel.interiorChartedSpace I
  let e := BoundarylessModel.homeomorph I N
  have : SimplyConnectedSpace (BoundarylessModel I N) := e.symm.toHomotopyEquiv.simplyConnectedSpace
  have := (hN.of_homotopyEquiv e.toHomotopyEquiv (e x)).subsingleton_of_simplyConnectedSpace
    (E := E)
  exact e.injective.subsingleton

end Boundaryless

end TauCeti
