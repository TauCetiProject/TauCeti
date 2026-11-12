/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.QuotientProd
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Closed manifolds of positive dimension are not weakly contractible

Let `M` be a compact oriented topological manifold of dimension `n > 0`. Its top integral
homology `Hₙ(M; ℤ)` is nonzero, since it contains the fundamental class, which has infinite order
in the local homology at any point. A weakly contractible space has the homology of a point,
since its map to a point is a weak homotopy equivalence. So not every homotopy group of `M` is
trivial (`TauCeti.HomologicalOrientation.not_forall_subsingleton_homotopyGroup`).

A simply connected manifold is orientable, and a simply connected aspherical space is weakly
contractible. Hence a compact simply connected manifold of positive dimension is not aspherical
(`TauCeti.not_isAspherical_of_simplyConnectedSpace`): some homotopy group `π_(k + 2)` of it is
nontrivial.

For a contractible topological group `A`, a compact simply connected manifold `K` with a topological
group structure, and a discrete subgroup `Γ` of `A × K`, the quotient `(A × K) ⧸ Γ` has the higher
homotopy groups of `K` (`Subgroup.isAspherical_quotient_iff`). So it is aspherical exactly when it
is path connected and `K` is a single point (`Subgroup.isAspherical_quotient_iff_subsingleton`). A
compact connected Lie group `G` is such a quotient `(ℝʳ × K) ⧸ Γ`, with `K` compact, simply
connected and semisimple, so `G` is a `K(π, 1)` exactly when `K` is trivial. This uses only that
`K` is a compact simply connected manifold, not its Lie structure.

## Main results

* `TauCeti.HomologicalOrientation.not_forall_subsingleton_homotopyGroup`: a compact oriented
  manifold of positive dimension has a nontrivial homotopy group.
* `TauCeti.not_isAspherical_of_simplyConnectedSpace`: a compact simply connected manifold of
  positive dimension is not aspherical.
* `Subgroup.isAspherical_quotient_iff_subsingleton`: for `A` contractible and `K` a compact
  simply connected manifold, `(A × K) ⧸ Γ` is aspherical exactly when it is path connected and `K`
  is a point.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 3.26 and
  Proposition 4.21.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and
  Proposition 6.31).
-/

public section

open CategoryTheory Limits AlgebraicTopology Module
open scoped Topology Topology.Homotopy

namespace TauCeti

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

namespace HomologicalOrientation

variable {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)

include o hn in
/-- **A closed manifold of positive dimension is not weakly contractible.** A compact oriented
manifold of positive dimension `n` has a nontrivial homotopy group at every point: otherwise its map
to a point would be a weak homotopy equivalence, while its top homology `Hₙ(M; ℤ)` contains the
fundamental class, of infinite order. -/
theorem not_forall_subsingleton_homotopyGroup [CompactSpace M] (hn0 : n ≠ 0) (x : M) :
    ¬ ∀ k, Subsingleton (π_ k M x) := by
  intro h
  have : PathConnectedSpace M := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).2 (h 0)
  -- The map to a point is a weak homotopy equivalence, since all homotopy groups are trivial.
  let p : C(M, PUnit.{1}) := ContinuousMap.const M PUnit.unit
  have hp : p.IsWeakHomotopyEquivalence :=
    (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective x).2 fun k ↦
      have := h k
      Function.bijective_of_subsingleton' _
  -- So `Hₙ(M; ℤ)` is the homology of a point, which vanishes in the positive degree `n`.
  have hiso := hp.isIso_singularHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) n
  have hzero : IsZero ((TopCat.toSSet.obj (TopCat.of M)).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :=
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{0} ℤ) n
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (TopCat.of PUnit) hn0).of_iso (@asIso _ _ _ _ _ hiso)
  -- But the fundamental class identifies it with `ℤ`.
  have := ModuleCat.subsingleton_of_isZero hzero
  exact one_ne_zero ((o.fundamentalClassEquiv hn).injective (Subsingleton.elim _ _))

end HomologicalOrientation

/-- **A closed simply connected manifold of positive dimension is not aspherical.** A compact
simply connected manifold `M` of positive dimension is orientable, and if it were aspherical all of
its homotopy groups would be trivial, which
`TauCeti.HomologicalOrientation.not_forall_subsingleton_homotopyGroup` rules out. So some higher
homotopy group `π_(k + 2)(M, x)` is nontrivial. -/
theorem not_isAspherical_of_simplyConnectedSpace [CompactSpace M] [SimplyConnectedSpace M]
    (hE : finrank ℝ E ≠ 0) (x : M) : ¬ IsAspherical M x := by
  intro h
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace (M := M) (E := E) rfl
  refine o.not_forall_subsingleton_homotopyGroup rfl hE x fun k ↦ ?_
  match k with
  | 0 => exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).1 inferInstance
  | 1 => exact HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.2 inferInstance
  | k + 2 => exact h.subsingleton_homotopyGroup k

end TauCeti

namespace Subgroup

open TauCeti

variable {A : Type*} {K : Type} [Group A] [Group K] [TopologicalSpace A] [TopologicalSpace K]
  [IsTopologicalGroup A] [IsTopologicalGroup K] (Γ : Subgroup (A × K))

/-- **A quotient of `A × K` with `A` contractible and `K` a closed simply connected manifold is
aspherical exactly when `K` is a point.** For a discrete subgroup `Γ` of `A × K`, where `K` is a
compact simply connected topological manifold with a topological group structure, the quotient
`(A × K) ⧸ Γ` is aspherical exactly when it is path connected and `K` is trivial. Applied to a
compact connected Lie group `(ℝʳ × K) ⧸ Γ`, this says it is a `K(π, 1)` exactly when `K` is
trivial. -/
theorem isAspherical_quotient_iff_subsingleton {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E K] [ContractibleSpace A] [DiscreteTopology Γ]
    [T2Space K] [CompactSpace K] [SimplyConnectedSpace K] (x : (A × K) ⧸ Γ) :
    IsAspherical ((A × K) ⧸ Γ) x ↔ PathConnectedSpace ((A × K) ⧸ Γ) ∧ Subsingleton K := by
  rw [Γ.isAspherical_quotient_iff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun _ _ ↦ inferInstance⟩
  by_contra hK
  -- `K` has positive dimension: a connected manifold modelled on a point is a point.
  have hE : finrank ℝ E ≠ 0 := by
    intro hE
    have : Subsingleton E := finrank_zero_iff.1 hE
    have : DiscreteTopology K := ChartedSpace.discreteTopology E K
    exact hK subsingleton_of_preconnected_totallyDisconnected
  exact not_isAspherical_of_simplyConnectedSpace (M := K) hE 1 (IsAspherical.mk inferInstance h)

end Subgroup
