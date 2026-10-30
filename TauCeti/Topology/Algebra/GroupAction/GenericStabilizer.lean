/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.GDelta.Basic
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus

import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# The generic stabilizer of a finite linear action

Every point stabilizer of a group action contains the kernel of the action, the subgroup
`(MulAction.toPermHom G X).ker` of elements acting trivially. This file shows that for a finite
group acting linearly on a topological vector space, the stabilizer is exactly that kernel on a
dense open set of points. No faithfulness is assumed: elements of the kernel are kept as genuine
isotropy, and the statement is that on a dense open set they are the only isotropy. For a
faithful action the kernel is trivial, so the free locus is dense.

The proof is the fixed-subspace calculation. A point fails to have the kernel as its stabilizer
exactly when it is fixed by some element outside the kernel, so the set in question is the
complement of the union of the fixed sets `MulAction.fixedBy X g` over `g` outside the kernel.
For a finite group acting by continuous maps on a Hausdorff space, this is a finite union of
closed sets, which gives openness. For a linear action, the fixed set of `g` is a submodule, and
it is a proper submodule when `g` is outside the kernel; over a ring such as a nontrivially normed
field a proper submodule has empty interior, so the finite union is nowhere dense.

The density statement is also recorded for an arbitrary finite action whose nontrivially acting
elements have fixed sets with empty interior; the linear case is the instance of it obtained from
the fixed-subspace calculation.

## Main results

* `TauCeti.setOf_stabilizer_eq_ker`: the points whose stabilizer is the action kernel are the
  complement of the fixed sets of the elements outside the kernel.
* `TauCeti.stabilizer_smul_eq_ker_iff`: this set of points is invariant under the action.
* `TauCeti.isOpen_setOf_stabilizer_eq_ker`: for a finite group acting continuously on a
  Hausdorff space, this set is open.
* `TauCeti.dense_setOf_stabilizer_eq_ker_of_interior_fixedBy`: it is dense when the fixed set of
  every element outside the kernel has empty interior.
* `TauCeti.interior_fixedBy_eq_empty_of_notMem_ker`: for a linear action, the fixed set of an
  element outside the kernel has empty interior.
* `TauCeti.dense_setOf_stabilizer_eq_ker`: for a finite linear action, the stabilizer is the
  action kernel on a dense set of points.
* `TauCeti.dense_freeLocus`: for a faithful finite linear action, the free locus is dense.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Chapter IV, §3.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

namespace TauCeti

open MulAction Set Topology

variable {G X : Type*} [Group G] [MulAction G X]

/-- A point has the action kernel as its stabilizer exactly when it is fixed by no element outside
the kernel. -/
theorem setOf_stabilizer_eq_ker :
    {x : X | stabilizer G x = (toPermHom G X).ker} =
      (⋃ (g : G) (_ : g ∉ (toPermHom G X).ker), fixedBy X g)ᶜ := by
  ext x
  simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, mem_fixedBy, exists_prop, not_exists,
    not_and, not_imp_not]
  refine ⟨fun h g hg ↦ h ▸ hg, fun h ↦ le_antisymm (fun g hg ↦ h g hg) fun g hg ↦ ?_⟩
  rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff] at hg
  exact hg x

/-- The set of points whose stabilizer is the action kernel is invariant under the action. -/
@[simp]
theorem stabilizer_smul_eq_ker_iff (g : G) (x : X) :
    stabilizer G (g • x) = (toPermHom G X).ker ↔ stabilizer G x = (toPermHom G X).ker := by
  have hK : (toPermHom G X).ker.map (MulAut.conj g).toMonoidHom = (toPermHom G X).ker :=
    Subgroup.Normal.map_conj_eq _ g
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  -- Write the kernel on the left as its own conjugate, then cancel the conjugation.
  conv_lhs => rw [← hK]
  exact (Subgroup.map_injective (MulAut.conj g).injective).eq_iff

section Topology

variable [TopologicalSpace X] [T2Space X] [ContinuousConstSMul G X]

/-- For a finite group acting continuously on a Hausdorff space, the points whose stabilizer is
the action kernel form an open set. -/
theorem isOpen_setOf_stabilizer_eq_ker [Finite G] :
    IsOpen {x : X | stabilizer G x = (toPermHom G X).ker} := by
  rw [setOf_stabilizer_eq_ker, isOpen_compl_iff]
  exact isClosed_iUnion_of_finite fun g ↦ isClosed_iUnion_of_finite fun _ ↦ isClosed_fixedBy g

/-- For a finite group acting continuously on a Hausdorff space, the points whose stabilizer is
the action kernel form a dense set, provided the fixed set of every element outside the kernel has
empty interior. -/
theorem dense_setOf_stabilizer_eq_ker_of_interior_fixedBy [Finite G]
    (h : ∀ g ∉ (toPermHom G X).ker, interior (fixedBy X g) = ∅) :
    Dense {x : X | stabilizer G x = (toPermHom G X).ker} := by
  rw [setOf_stabilizer_eq_ker]
  refine (isClosed_isNowhereDense_iff_compl.mp ⟨?_, ?_⟩).2
  · exact isClosed_iUnion_of_finite fun g ↦ isClosed_iUnion_of_finite fun _ ↦ isClosed_fixedBy g
  · simpa only [iUnion_subtype] using
      IsNowhereDense.iUnion fun g : {g : G // g ∉ (toPermHom G X).ker} ↦
        (isClosed_fixedBy (g : G)).isNowhereDense_iff.mpr (h g g.2)

end Topology

section Linear

variable (R : Type*) {V : Type*} [Ring R] [TopologicalSpace R]
  [Filter.NeBot (𝓝[{r : R | IsUnit r}] 0)] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul R V] [DistribMulAction G V] [SMulCommClass G R V]

include R

/-- For a linear action on a topological module over a ring in which `0` is a limit of units, for
instance a nontrivially normed field, the fixed set of an element outside the action kernel has
empty interior: it is a proper submodule. -/
theorem interior_fixedBy_eq_empty_of_notMem_ker {g : G} (hg : g ∉ (toPermHom G V).ker) :
    interior (fixedBy V g) = ∅ := by
  by_contra hne
  -- The fixed set of `g` is the submodule on which `g` agrees with the identity.
  have htop := (LinearMap.eqLocus (DistribSMul.toLinearMap R V g) LinearMap.id
    ).eq_top_of_nonempty_interior' (nonempty_iff_ne_empty.mpr hne)
  refine hg (MonoidHom.mem_ker.mpr (Equiv.ext fun v ↦ ?_))
  simpa using LinearMap.congr_fun (LinearMap.eqLocus_eq_top.mp htop) v

variable [T2Space V] [ContinuousConstSMul G V] [Finite G]

/-- **Generic stabilizer of a finite linear action.** For a finite group acting linearly and
continuously on a Hausdorff topological module over a ring in which `0` is a limit of units, for
instance a finite-dimensional real vector space, the points whose stabilizer is the kernel of the
action form a dense set. The action need not be faithful. The set is also open, by
`TauCeti.isOpen_setOf_stabilizer_eq_ker`. -/
theorem dense_setOf_stabilizer_eq_ker :
    Dense {v : V | stabilizer G v = (toPermHom G V).ker} :=
  dense_setOf_stabilizer_eq_ker_of_interior_fixedBy fun _ hg ↦
    interior_fixedBy_eq_empty_of_notMem_ker R hg

/-- For a faithful finite group action, linear and continuous on a Hausdorff topological module
over a ring in which `0` is a limit of units, the points with trivial stabilizer form a dense
set. -/
theorem dense_freeLocus [FaithfulSMul G V] : Dense (freeLocus G V : Set V) := by
  have hker : (toPermHom G V).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr toPerm_injective
  have hfree : (freeLocus G V : Set V) = {v | stabilizer G v = (toPermHom G V).ker} := by
    ext v
    simp [hker]
  exact hfree ▸ dense_setOf_stabilizer_eq_ker R

end Linear

end TauCeti
