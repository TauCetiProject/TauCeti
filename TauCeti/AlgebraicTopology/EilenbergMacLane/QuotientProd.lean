/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.HomotopyEquiv
import TauCeti.Topology.Homotopy.HomotopyGroup.Covering

/-!
# Homotopy groups of a quotient of `A × K` with contractible `A`

Let `A` and `K` be topological groups with `A` contractible, such as a real vector space, and let
`Γ` be a discrete subgroup of `A × K`. The canonical map `k ↦ [(1, k)]` from `K` to `(A × K) ⧸ Γ`
induces a bijection on every homotopy group of dimension at least two
(`Subgroup.bijective_homotopyGroupMap_quotientMk_inr`): the inclusion of `K` into `A × K` is a
section of the second projection, which is a homotopy equivalence because `A` is contractible,
and the projection `A × K → (A × K) ⧸ Γ` is a covering map, bijective on these homotopy groups.

So `(A × K) ⧸ Γ` is aspherical exactly when it is path connected and every homotopy group of `K`
of dimension at least two is trivial (`Subgroup.isAspherical_quotient_iff`). For a compact
connected Lie group `G = (ℝʳ × K) ⧸ Γ`, with `K` compact, simply connected and semisimple, this
reduces the question whether `G` is a `K(π, 1)` to the higher homotopy groups of `K`.

## Main results

* `Subgroup.bijective_homotopyGroupMap_quotientMk_inr`: the canonical map from `K` is bijective
  on `π_(n + 2)`.
* `Subgroup.isAspherical_quotient_iff`: asphericity of `(A × K) ⧸ Γ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and
  Proposition 6.31).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 4.1.
-/

public section

open Topology TauCeti
open scoped Topology.Homotopy

namespace Subgroup

variable {A K : Type*} [Group A] [Group K] [TopologicalSpace A] [TopologicalSpace K]
  [IsTopologicalGroup A] [IsTopologicalGroup K] (Γ : Subgroup (A × K))

/-- **The higher homotopy groups of `K` are those of `(A × K) ⧸ Γ` for contractible `A`.** For a
discrete subgroup `Γ` of `A × K`, the canonical map `k ↦ [(1, k)]` induces a bijection
`π_(n + 2)(K, k) → π_(n + 2)((A × K) ⧸ Γ, [(1, k)])`. -/
theorem bijective_homotopyGroupMap_quotientMk_inr [ContractibleSpace A]
    [DiscreteTopology Γ] (k : K) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin (n + 2))
      (⟨fun k ↦ (((1 : A), k) : (A × K) ⧸ Γ), by fun_prop⟩ : C(K, (A × K) ⧸ Γ)) rfl :
        π_ (n + 2) K k → π_ (n + 2) ((A × K) ⧸ Γ) (((1 : A), k) : (A × K) ⧸ Γ)) := by
  -- The second projection is a homotopy equivalence, since `A` is contractible, and the
  -- inclusion `k ↦ (1, k)` is a section of it.
  let e : ContinuousMap.HomotopyEquiv (A × K) K :=
    (Homeomorph.prodComm A K).toHomotopyEquiv.trans
      (ContinuousMap.HomotopyEquiv.prodContractible K A)
  have he : e.toFun = ContinuousMap.snd := by
    ext x
    simp [e, ContinuousMap.HomotopyEquiv.trans]
  let inr : C(K, A × K) := (ContinuousMap.const K (1 : A)).prodMk (ContinuousMap.id K)
  have hinr : inr.IsWeakHomotopyEquivalence := by
    refine e.isWeakHomotopyEquivalence.of_postcomp ?_
    rw [he]
    exact ContinuousMap.IsWeakHomotopyEquivalence.id
  let q : C(A × K, (A × K) ⧸ Γ) := ⟨QuotientGroup.mk, continuous_quot_mk⟩
  have hq : Function.Bijective (HomotopyGroup.map (N := Fin (n + 2)) q (rfl : q (inr k) = _)) :=
    HomotopyGroup.map_bijective
      (Γ.isQuotientCoveringMap (isDiscrete_iff_discreteTopology.2 ‹_›)).isCoveringMap rfl
  exact HomotopyGroup.map_comp_map q rfl inr rfl ▸ hq.comp (hinr.bijective (n + 2) k)

/-- **Asphericity of `(A × K) ⧸ Γ` for contractible `A`.** For a discrete subgroup `Γ` of `A × K`,
the quotient is aspherical exactly when it is path connected and every homotopy group of `K` of
dimension at least two is trivial. -/
theorem isAspherical_quotient_iff [ContractibleSpace A] [DiscreteTopology Γ]
    (x : (A × K) ⧸ Γ) :
    IsAspherical ((A × K) ⧸ Γ) x ↔
      PathConnectedSpace ((A × K) ⧸ Γ) ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) K 1) := by
  refine ⟨fun h ↦ ⟨h.pathConnectedSpace, fun n ↦ ?_⟩, fun ⟨hX, h⟩ ↦ ?_⟩
  · have := (h.of_basepoint (((1 : A), (1 : K)) : (A × K) ⧸ Γ)).subsingleton_homotopyGroup n
    exact (Equiv.ofBijective _ (Γ.bijective_homotopyGroupMap_quotientMk_inr 1 n)).subsingleton
  · refine IsAspherical.of_basepoint
      (IsAspherical.mk (x := (((1 : A), (1 : K)) : (A × K) ⧸ Γ)) hX fun n ↦ ?_) x
    have := h n
    exact (Equiv.ofBijective _ (Γ.bijective_homotopyGroupMap_quotientMk_inr 1 n)).symm.subsingleton

end Subgroup
