/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# Congruence subgroups are open

For a Hopf algebra `H` of finite type over `k` and a topological `k`-algebra `R`, the group of
points `WithConv (H →ₐ[k] R)` carries the point topology, the coarsest topology making every
evaluation continuous. Membership in a congruence subgroup is a congruence condition on the values
of a point at finitely many generators of `H`, so the congruence subgroup of an open level is
open. Over a compact Hausdorff noetherian local ring, such as the valuation ring `O` of a
nonarchimedean local field, every power of the maximal ideal is open, so all the congruence
subgroups `𝒢(O)ₙ` of an affine group `𝒢` of finite type over `O` are open in `𝒢(O)`.

## Main declarations

* `TauCeti.HopfAlgebra.isOpen_congruenceSubgroup`: the congruence subgroup of an open level is
  open when `H` is of finite type.
* `TauCeti.HopfAlgebra.isOpen_congruenceSubgroup_maximalIdeal_pow`: over a compact Hausdorff
  noetherian local ring, the congruence subgroups of the levels `m ^ n` are open.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and Ex. 2.3, pp. 2–3.
* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic groups and number theory*, vol. 1,
  2nd ed. (2023), §3.1, p. 126.
-/

public section

open Coalgebra WithConv

namespace TauCeti

namespace HopfAlgebra

variable {k H R : Type*} [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H]
  [CommRing R] [Algebra k R] [TopologicalSpace R]

/-- The congruence subgroup of an open level `I` is open in the point topology, when `H` is of
finite type over `k`. -/
theorem isOpen_congruenceSubgroup [ContinuousSub R] [Algebra.FiniteType k H] {I : Ideal R}
    (hI : IsOpen (I : Set R)) :
    IsOpen (congruenceSubgroup k H I : Set (WithConv (H →ₐ[k] R))) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
  have hset : (congruenceSubgroup k H I : Set (WithConv (H →ₐ[k] R))) =
      ⋂ h ∈ (s : Set H), (fun x : WithConv (H →ₐ[k] R) ↦
        x.ofConv h - algebraMap k R (counit h)) ⁻¹' I := by
    ext x
    simp only [SetLike.mem_coe, mem_congruenceSubgroup_iff_of_adjoin_eq_top hs, Set.mem_iInter,
      Set.mem_preimage]
  rw [hset]
  exact s.finite_toSet.isOpen_biInter fun h _ ↦
    hI.preimage (((PointTopology.continuous_withConv_iff.1 continuous_id) h).sub continuous_const)

variable (k H R) in
/-- Over a compact Hausdorff noetherian local ring `R`, for instance the valuation ring of a
nonarchimedean local field, the congruence subgroup of level `m ^ n` of an affine group of finite
type is open in the point topology. -/
theorem isOpen_congruenceSubgroup_maximalIdeal_pow [IsTopologicalRing R] [CompactSpace R]
    [T2Space R] [IsNoetherianRing R] [IsLocalRing R] [Algebra.FiniteType k H] (n : ℕ) :
    IsOpen (congruenceSubgroup k H (IsLocalRing.maximalIdeal R ^ n) :
      Set (WithConv (H →ₐ[k] R))) :=
  isOpen_congruenceSubgroup (IsLocalRing.isOpen_maximalIdeal_pow R n)

end HopfAlgebra

end TauCeti
