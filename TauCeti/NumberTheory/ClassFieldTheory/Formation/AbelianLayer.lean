/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic

/-!
# Abelian layers of a formation

An open normal subgroup `V` of a topological group has abelian quotient precisely when it contains
the closure of the commutator subgroup. This file packages that condition as
`IsAbelianClassFieldLayer V` and identifies it with commutativity of `G ⧸ V`.

Every open normal subgroup also has a canonical **maximal abelian sublayer**. In subgroup
language it is

```text
V ⊔ closure (commutator G),
```

the least abelian-layer subgroup containing `V`. When `G` is the relevant profinite Galois group,
the corresponding fixed field is therefore the largest abelian subextension of the field cut out
by `V`. This construction is the group-theoretic input to norm limitation: abstract reciprocity
later shows that a layer and this maximal abelian sublayer have the same norm subgroup.

Under the profinite hypotheses used for finite normal layers, the final part of the file removes
the algebraic abelianization from the quotient group. It supplies the canonical equivalence
`Abelianization (G ⧸ V) ≃* G ⧸ V` used, when `G` is a Galois group, to state local and global
class-field correspondences directly in terms of their abelian Galois groups.

## Main definitions

* `TauCeti.ClassFieldTheory.IsAbelianClassFieldLayer`: the closed-commutator condition on an open
  normal subgroup.
* `TauCeti.ClassFieldTheory.AbelianLayer`: the subtype of open normal subgroups satisfying that
  condition.
* `TauCeti.ClassFieldTheory.maximalAbelianLayer`: the least abelian-layer subgroup above a given
  open normal subgroup.
* `TauCeti.ClassFieldTheory.abelianizationGalEquiv`: the canonical equivalence from the
  abelianization of an abelian layer's Galois group to that Galois group.

## Main statements

* `TauCeti.ClassFieldTheory.isAbelianClassFieldLayer_iff_isMulCommutative`: the closed-commutator
  condition is equivalent to commutativity of `G ⧸ V`.
* `TauCeti.ClassFieldTheory.le_maximalAbelianLayer` and
  `TauCeti.ClassFieldTheory.maximalAbelianLayer_le`: the universal property of the maximal
  abelian sublayer.
* `TauCeti.ClassFieldTheory.maximalAbelianLayer_eq_self_iff`: the construction fixes exactly the
  abelian layers.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§4–5.
* J. Neukirch, *Class Field Theory*, Chapter III, §1.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

-- Formalization source: `TauCetiRoadmap/ClassFieldTheory/Suggested.lean`.

/-! ### Abelian layers -/

/-- An open normal subgroup cuts out an **abelian class-field layer** when it contains the
topological closure of the commutator subgroup. The closure is essential: it is the kernel used
by Mathlib's `TopologicalAbelianization`, and the unclosed commutator subgroup need not be closed
in a profinite group. -/
def IsAbelianClassFieldLayer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenNormalSubgroup G) : Prop :=
  (commutator G).topologicalClosure ≤ V.toSubgroup

/-- Open normal subgroups whose quotient is abelian. For a profinite Galois group, these form the
Galois-side carrier of class-field correspondences; subgroup inclusion becomes reverse inclusion
on fixed fields. -/
abbrev AbelianLayer (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  {V : OpenNormalSubgroup G // IsAbelianClassFieldLayer V}

section AbelianLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closed-commutator condition on `V` is equivalent to commutativity of the quotient
`G ⧸ V`. -/
theorem isAbelianClassFieldLayer_iff_isMulCommutative (V : OpenNormalSubgroup G) :
    IsAbelianClassFieldLayer V ↔ IsMulCommutative (G ⧸ V.toSubgroup) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  constructor
  · exact fun h ↦ (Subgroup.le_topologicalClosure _).trans h
  · exact fun h ↦ (commutator G).topologicalClosure_minimal h V.toOpenSubgroup.isClosed

/-! ### The maximal abelian sublayer -/

/-- The **maximal abelian sublayer** of `V`, represented on subgroups by
`V ⊔ closure (commutator G)`. It is the least abelian-layer subgroup containing `V`. When `G`
is the relevant profinite Galois group, it cuts out the largest abelian subextension of the
original fixed field. -/
def maximalAbelianLayer (V : OpenNormalSubgroup G) : OpenNormalSubgroup G :=
  ⟨⟨V.toSubgroup ⊔ (commutator G).topologicalClosure,
      Subgroup.isOpen_mono le_sup_left V.toOpenSubgroup.isOpen⟩,
    Subgroup.sup_normal _ _⟩

@[simp]
theorem toSubgroup_maximalAbelianLayer (V : OpenNormalSubgroup G) :
    (maximalAbelianLayer V).toSubgroup =
      V.toSubgroup ⊔ (commutator G).topologicalClosure :=
  (rfl)

@[simp]
theorem mem_maximalAbelianLayer {V : OpenNormalSubgroup G} {x : G} :
    x ∈ maximalAbelianLayer V ↔
      x ∈ V.toSubgroup ⊔ (commutator G).topologicalClosure :=
  (Iff.rfl)

/-- Every layer subgroup lies in its maximal abelian sublayer subgroup. -/
theorem le_maximalAbelianLayer (V : OpenNormalSubgroup G) : V ≤ maximalAbelianLayer V :=
  by
    intro x hx
    rw [mem_maximalAbelianLayer]
    exact (le_sup_left : V.toSubgroup ≤
      V.toSubgroup ⊔ (commutator G).topologicalClosure) hx

/-- The maximal abelian sublayer is an abelian class-field layer. -/
@[simp]
theorem isAbelianClassFieldLayer_maximalAbelianLayer (V : OpenNormalSubgroup G) :
    IsAbelianClassFieldLayer (maximalAbelianLayer V) :=
  by
    intro x hx
    exact mem_maximalAbelianLayer.2
      ((le_sup_right : (commutator G).topologicalClosure ≤
        V.toSubgroup ⊔ (commutator G).topologicalClosure) hx)

/-- The universal property of the maximal abelian sublayer: it is the least abelian-layer
subgroup containing `V`. -/
theorem maximalAbelianLayer_le {V W : OpenNormalSubgroup G} (hVW : V ≤ W)
    (hW : IsAbelianClassFieldLayer W) : maximalAbelianLayer V ≤ W :=
  by
    intro x hx
    rw [mem_maximalAbelianLayer] at hx
    exact (sup_le (fun _ hxV ↦ hVW hxV) hW :
      V.toSubgroup ⊔ (commutator G).topologicalClosure ≤ W.toSubgroup) hx

/-- A layer is already abelian exactly when its maximal abelian sublayer is itself. -/
@[simp]
theorem maximalAbelianLayer_eq_self_iff (V : OpenNormalSubgroup G) :
    maximalAbelianLayer V = V ↔ IsAbelianClassFieldLayer V := by
  constructor
  · intro h
    rw [← h]
    exact isAbelianClassFieldLayer_maximalAbelianLayer V
  · exact fun h ↦ le_antisymm (maximalAbelianLayer_le le_rfl h) (le_maximalAbelianLayer V)

/-! ### Finite Galois groups of abelian layers -/

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The finite Galois group of an abelian open normal layer is commutative. -/
theorem isMulCommutative_gal_ofOpenNormal {V : OpenNormalSubgroup G}
    (hV : IsAbelianClassFieldLayer V) :
    IsMulCommutative (NormalLayer.ofOpenNormal V).Gal := by
  apply Function.Surjective.isMulCommutative
    (f := (NormalLayer.galOfOpenNormalEquiv V).symm)
    (NormalLayer.galOfOpenNormalEquiv V).symm.surjective
  exact (isAbelianClassFieldLayer_iff_isMulCommutative V).1 hV

open scoped IsMulCommutative in
/-- For an abelian layer, the canonical quotient map to its algebraic abelianization is an
isomorphism. This equivalence removes the redundant abelianization from the target of the Artin
equivalence. -/
noncomputable def abelianizationGalEquiv {V : OpenNormalSubgroup G}
    (hV : IsAbelianClassFieldLayer V) :
    Abelianization (NormalLayer.ofOpenNormal V).Gal ≃*
      (NormalLayer.ofOpenNormal V).Gal :=
  letI := isMulCommutative_gal_ofOpenNormal hV
  Abelianization.equivOfComm.symm

open scoped IsMulCommutative in
/-- The inverse of `abelianizationGalEquiv` is the canonical abelianization map. -/
@[simp]
theorem abelianizationGalEquiv_symm_apply {V : OpenNormalSubgroup G}
    (hV : IsAbelianClassFieldLayer V) (x : (NormalLayer.ofOpenNormal V).Gal) :
    (abelianizationGalEquiv hV).symm x = Abelianization.of x := by
  let := isMulCommutative_gal_ofOpenNormal hV
  simp only [abelianizationGalEquiv, MulEquiv.symm_symm,
    Abelianization.equivOfComm_apply]

open scoped IsMulCommutative in
/-- The abelianization equivalence sends the canonical class of an element back to that element. -/
@[simp]
theorem abelianizationGalEquiv_of {V : OpenNormalSubgroup G}
    (hV : IsAbelianClassFieldLayer V) (x : (NormalLayer.ofOpenNormal V).Gal) :
    abelianizationGalEquiv hV (Abelianization.of x) = x := by
  rw [← abelianizationGalEquiv_symm_apply hV x]
  exact (abelianizationGalEquiv hV).apply_symm_apply x

end AbelianLayer

end TauCeti.ClassFieldTheory
