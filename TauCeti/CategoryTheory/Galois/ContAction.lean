/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A profinite group is the fundamental group of its finite continuous actions

Let `G` be a topological group. Mathlib shows that finite sets with a continuous `G`-action form
a Galois category `ContAction FintypeCat G`. This file shows that the forgetful functor to finite
sets is a fibre functor and that, when `G` is profinite (compact, Hausdorff and totally
disconnected), `G` itself is a fundamental group of it in the sense of
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`. Consequently
`CategoryTheory.PreGaloisCategory.toAutMulEquiv` identifies `G` with the automorphism group of the
forgetful functor, as groups and as topological spaces.

Recognising a category as equivalent to `ContAction FintypeCat G` therefore computes the
fundamental group of a fibre functor: for instance, Galois theory identifies finite étale
algebras over a field with finite continuous sets under its absolute Galois group.

The two inputs are that a connected finite continuous `G`-set is a transitive `G`-set, since an
orbit is a subobject (`ContAction.isPretransitive_of_isConnected`), and that a nontrivial element
of a profinite group moves a coset of some open normal subgroup
(`ContAction.eq_one_of_forall_smul_eq`).

## Main results

* `ContAction.isPretransitive_of_isConnected`: `G` acts transitively on a connected object of
  `ContAction FintypeCat G`.
* `ContAction.instIsFundamentalGroup`: a profinite group `G` is a fundamental group of the
  forgetful fibre functor on `ContAction FintypeCat G`.

## References

* H. W. Lenstra, *Galois theory for schemes*, Example 3.5 and Theorem 3.17.
-/

public section

open CategoryTheory Limits PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The forgetful functor from finite continuous `G`-sets to finite sets is a fibre functor. -/
noncomputable instance : FiberFunctor (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) :=
  inferInstanceAs <|
    FiberFunctor ((Action.isContinuous FintypeCat G).ι ⋙ Action.forget FintypeCat G)

/-- `G` acts on the underlying finite set of a finite continuous `G`-set. -/
instance instMulActionObjForget₂ (X : ContAction FintypeCat.{u} G) :
    MulAction G ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}).obj X) :=
  inferInstanceAs (MulAction G X.obj.V)

/-- A connected finite continuous `G`-set is connected as a finite `G`-set: its subobjects as a
finite `G`-set are again continuous. -/
theorem isConnected_obj (X : ContAction FintypeCat.{u} G) [IsConnected X] : IsConnected X.obj where
  notInitial := (not_initial_iff_fiber_nonempty (Action.forget FintypeCat G) X.obj).mpr
    (nonempty_fiber_of_isConnected (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) X)
  noTrivialComponent Y i _ hY := by
    have hYc : Action.isContinuous FintypeCat G Y :=
      (Action.isContinuous FintypeCat G).prop_of_mono i X.property
    let j : (⟨Y, hYc⟩ : ContAction FintypeCat.{u} G) ⟶ X := ObjectProperty.homMk i
    have : Mono j := (Action.isContinuous FintypeCat G).ι.mono_of_mono_map ‹_›
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty (Action.forget FintypeCat G) Y).mp hY
    have : IsIso j := IsConnected.noTrivialComponent _ j
      (not_initial_of_inhabited (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) y)
    exact inferInstanceAs (IsIso ((Action.isContinuous FintypeCat G).ι.map j))

/-- `G` acts transitively on a connected finite continuous `G`-set. -/
theorem isPretransitive_of_isConnected (X : ContAction FintypeCat.{u} G) [IsConnected X] :
    MulAction.IsPretransitive G X.obj.V :=
  have := isConnected_obj X
  FintypeCat.Action.pretransitive_of_isConnected G X.obj

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- An element of a profinite group acting trivially on every finite continuous `G`-set is the
identity: otherwise it moves the base coset of an open normal subgroup avoiding it. -/
theorem eq_one_of_forall_smul_eq (g : G)
    (h : ∀ (X : ContAction FintypeCat.{u} G) (x : X.obj.V), g • x = x) : g = 1 := by
  by_contra hg
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := g)) (Ne.symm hg)
  have : Fintype (G ⧸ H.toSubgroup) := Fintype.ofFinite _
  -- `G ⧸ H` is a finite continuous `G`-set, since the normal subgroup `H` acts trivially on it.
  have hX : Action.isContinuous FintypeCat G (G ⧸ₐ H.toSubgroup) :=
    Action.trivialOnSet_le_isContinuous H.toOpenSubgroup _ fun h hh => by
      ext x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      -- The action of `h` on the finite `G`-set `G ⧸ₐ H` is left multiplication on cosets.
      change h • (a : G ⧸ H.toSubgroup) = (a : G ⧸ H.toSubgroup)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using H.isNormal'.conj_mem _ (H.inv_mem hh) a⁻¹
  have h1 := h ⟨_, hX⟩ (1 : G ⧸ H.toSubgroup)
  -- The action on the underlying set of `⟨G ⧸ₐ H, hX⟩` is the action of `G` on cosets.
  change g • (1 : G ⧸ H.toSubgroup) = 1 at h1
  rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    QuotientGroup.mk_one, QuotientGroup.eq_one_iff] at h1
  exact hH h1 rfl

/-- **A profinite group is a fundamental group of the forgetful functor on its finite continuous
actions.** -/
instance instIsFundamentalGroup :
    IsFundamentalGroup (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) G where
  naturality g _ _ f x := ConcreteCategory.congr_hom (f.hom.comm g) x
  transitive_of_isGalois X _ := isPretransitive_of_isConnected X
  continuous_smul X := X.property
  non_trivial' g h := eq_one_of_forall_smul_eq g h

end ContAction
