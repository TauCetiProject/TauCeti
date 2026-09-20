/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
import TauCeti.GroupTheory.PGroup

/-!
# Classes of finite groups

A **class of finite groups** in the sense of profinite group theory is a collection `C` of
finite groups that is closed under isomorphism, subgroups, quotients and extensions, and
contains the trivial group. Finite `p`-groups, finite solvable groups and all finite groups are
the examples of record. Such a class is exactly the data needed to speak of a pro-`C` group and
of the universal pro-`C` quotient of a topological group, so it is bundled here as a structure
rather than left as a loose predicate.

Closure under finite products is a *consequence* of the four closure properties, through the
extension `1 → H → H × K → K → 1`, and so is a theorem here rather than a field.

The membership predicate of a class carries the typeclass assumptions `[Group H] [Finite H]`,
which is awkward for a group that is not yet known to be finite. `FiniteGroupClass.MemFinite`
packages the two together: `C.MemFinite H` says that `H` is finite and belongs to `C`. All the
closure properties below are stated in that form, because the groups they are applied to —
quotients of a topological group by open normal subgroups — are finite for a reason that is
not visible in the statement.

A class speaks only about groups in a single universe, so every construction below confines a
group, and the homomorphisms between them, to that one universe.

## Main definitions

* `TauCeti.FiniteGroupClass`: a class of finite groups, as the data of its membership
  predicate together with its closure properties.
* `TauCeti.FiniteGroupClass.MemFinite`: membership of a group that is not yet known to be
  finite.
* `TauCeti.finiteGroupClassP`: the class of finite `p`-groups.
* `TauCeti.finiteGroupClassSolvable`: the class of finite solvable groups.
* `TauCeti.finiteGroupClassAll`: the class of all finite groups.

## Main results

* `TauCeti.FiniteGroupClass.MemFinite.prod`: a class of finite groups is closed under binary
  products.
* `TauCeti.FiniteGroupClass.MemFinite.quotient_inf`: the normal subgroups with quotient in the
  class are closed under binary intersection.
* `TauCeti.FiniteGroupClass.MemFinite.quotient_comap`: they are preserved by preimage along a
  group homomorphism.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.1.
-/

public section

namespace TauCeti

universe w

/-- A **class of finite groups**: a collection of finite groups containing the trivial group
and closed under isomorphism, subgroups, quotients and extensions. This is the data a pro-`C`
completion is built from. -/
@[ext]
structure FiniteGroupClass where
  /-- Membership of a finite group in the class. -/
  mem : ∀ (H : Type w) [Group H] [Finite H], Prop
  /-- Membership depends only on the isomorphism class. -/
  mem_congr : ∀ {H K : Type w} [Group H] [Finite H] [Group K] [Finite K],
    (H ≃* K) → (mem H ↔ mem K)
  /-- The trivial group is in the class. -/
  mem_trivial : mem PUnit
  /-- The class is closed under subgroups. -/
  mem_subgroup : ∀ {H : Type w} [Group H] [Finite H], mem H → ∀ K : Subgroup H, mem K
  /-- The class is closed under quotients. -/
  mem_quotient : ∀ {H : Type w} [Group H] [Finite H], mem H →
    ∀ (N : Subgroup H) [N.Normal], mem (H ⧸ N)
  /-- The class is closed under extensions. -/
  mem_extension : ∀ {H : Type w} [Group H] [Finite H] (N : Subgroup H) [N.Normal],
    mem N → mem (H ⧸ N) → mem H

namespace FiniteGroupClass

variable {C : FiniteGroupClass.{w}} {G H K : Type w} [Group G] [Group H] [Group K]

/-- `C.MemFinite H` says that the group `H` is finite and lies in the class `C`. It is the form
in which membership is used for a group whose finiteness is not part of the ambient context,
such as the quotient of a topological group by an open normal subgroup. -/
def MemFinite (C : FiniteGroupClass.{w}) (H : Type w) [Group H] : Prop :=
  ∃ _ : Finite H, C.mem H

/-- A group that lies in a class of finite groups is finite. -/
theorem MemFinite.finite (h : C.MemFinite H) : Finite H :=
  h.elim fun hH _ ↦ hH

/-- For a group already known to be finite, `MemFinite` is membership. -/
@[simp]
theorem memFinite_iff [Finite H] : C.MemFinite H ↔ C.mem H :=
  ⟨fun h ↦ h.elim fun _ hH ↦ hH, fun h ↦ ⟨‹_›, h⟩⟩

/-- A class of finite groups contains every trivial group. -/
theorem memFinite_of_subsingleton [Subsingleton H] : C.MemFinite H := by
  have : Finite H := Finite.of_subsingleton
  have : Unique H := uniqueOfSubsingleton 1
  exact memFinite_iff.mpr ((C.mem_congr (MulEquiv.ofUnique (M := PUnit) (N := H))).mp C.mem_trivial)

/-- A class of finite groups is closed under surjective images: a quotient of a member is a
member. -/
theorem MemFinite.of_surjective (hH : C.MemFinite H) (f : H →* K) (hf : Function.Surjective f) :
    C.MemFinite K := by
  have := hH.finite
  have : Finite K := Finite.of_surjective f hf
  exact memFinite_iff.mpr ((C.mem_congr (QuotientGroup.quotientKerEquivOfSurjective f hf)).mp
    (C.mem_quotient (memFinite_iff.mp hH) f.ker))

/-- A class of finite groups is closed under subobjects: a group that embeds in a member is a
member. -/
theorem MemFinite.of_injective (hK : C.MemFinite K) (f : H →* K) (hf : Function.Injective f) :
    C.MemFinite H := by
  have := hK.finite
  have : Finite H := Finite.of_injective f hf
  exact memFinite_iff.mpr ((C.mem_congr (MonoidHom.ofInjective hf)).mpr
    (C.mem_subgroup (memFinite_iff.mp hK) f.range))

/-- Membership in a class of finite groups is invariant under isomorphism. -/
theorem memFinite_congr (e : H ≃* K) : C.MemFinite H ↔ C.MemFinite K :=
  ⟨fun h ↦ h.of_surjective e.toMonoidHom e.surjective,
    fun h ↦ h.of_surjective e.symm.toMonoidHom e.symm.surjective⟩

/-- A class of finite groups is closed under extensions. -/
theorem MemFinite.extension {N : Subgroup H} [N.Normal] (hN : C.MemFinite N)
    (hQ : C.MemFinite (H ⧸ N)) : C.MemFinite H := by
  have := hN.finite
  have := hQ.finite
  have : Finite H := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := N)).symm
  exact memFinite_iff.mpr
    (C.mem_extension N (memFinite_iff.mp hN) (memFinite_iff.mp hQ))

/-- **A class of finite groups is closed under binary products.** This is the closure property
that is not a field of the structure: it follows from closure under extensions, applied to
`1 → H → H × K → K → 1`. -/
theorem MemFinite.prod (hH : C.MemFinite H) (hK : C.MemFinite K) : C.MemFinite (H × K) := by
  refine MemFinite.extension (N := (MonoidHom.snd H K).ker) ?_ ?_
  · refine hH.of_surjective ((MonoidHom.inl H K).codRestrict _ fun h ↦ ?_) ?_
    · simp [Subgroup.mem_prod]
    · rintro ⟨⟨h, k⟩, hk⟩
      rw [MonoidHom.mem_ker, MonoidHom.coe_snd] at hk
      exact ⟨h, Subtype.ext (Prod.ext rfl hk.symm)⟩
  · exact (memFinite_congr
      (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.snd H K)
        fun k ↦ ⟨(1, k), rfl⟩)).mpr hK

/-- **The normal subgroups with quotient in `C` are closed under binary intersection**, because
`G ⧸ (M ⊓ N)` embeds in `(G ⧸ M) × (G ⧸ N)`. This is what makes that family downward directed.
-/
theorem MemFinite.quotient_inf {M N : Subgroup G} [M.Normal] [N.Normal]
    (hM : C.MemFinite (G ⧸ M)) (hN : C.MemFinite (G ⧸ N)) : C.MemFinite (G ⧸ (M ⊓ N)) := by
  have hker : M ⊓ N = ((QuotientGroup.mk' M).prod (QuotientGroup.mk' N)).ker := by
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk', QuotientGroup.ker_mk']
  refine (hM.prod hN).of_injective ((QuotientGroup.kerLift _).comp
    (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom) ?_
  rw [MonoidHom.coe_comp]
  exact (QuotientGroup.kerLift_injective _).comp
    (QuotientGroup.quotientMulEquivOfEq hker).injective

/-- **The normal subgroups with quotient in `C` are preserved by preimage**, because
`G ⧸ N.comap f` embeds in `H ⧸ N`. -/
theorem MemFinite.quotient_comap {N : Subgroup H} [N.Normal] (hN : C.MemFinite (H ⧸ N))
    (f : G →* H) : C.MemFinite (G ⧸ N.comap f) := by
  have hker : N.comap f = ((QuotientGroup.mk' N).comp f).ker := by
    simpa using MonoidHom.comap_ker (QuotientGroup.mk' N) f
  refine hN.of_injective ((QuotientGroup.kerLift _).comp
    (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom) ?_
  rw [MonoidHom.coe_comp]
  exact (QuotientGroup.kerLift_injective _).comp
    (QuotientGroup.quotientMulEquivOfEq hker).injective

end FiniteGroupClass

/-! ### The examples of record -/

/-- The class of **finite `p`-groups**, the class that pro-`p` theory is about. -/
def finiteGroupClassP (p : ℕ) : FiniteGroupClass.{w} where
  mem H := IsPGroup p H
  mem_congr e := ⟨fun h ↦ h.of_equiv e, fun h ↦ h.of_equiv e.symm⟩
  mem_trivial := IsPGroup.of_subsingleton p PUnit
  mem_subgroup h K := h.to_subgroup K
  mem_quotient h N := h.to_quotient N
  mem_extension _ _ hN hQ := hN.of_subgroup_of_quotient hQ

/-- Membership in `finiteGroupClassP p` is being a `p`-group. -/
@[simp]
theorem finiteGroupClassP_mem_iff (p : ℕ) (H : Type w) [Group H] [Finite H] :
    (finiteGroupClassP p).mem H ↔ IsPGroup p H :=
  Iff.rfl

/-- The class of **finite solvable groups**. -/
def finiteGroupClassSolvable : FiniteGroupClass.{w} where
  mem H := Group.IsSolvable H
  mem_congr e := ⟨fun _h ↦ Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
    fun _h ↦ Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
  mem_trivial := inferInstance
  mem_subgroup _h _K := inferInstance
  mem_quotient _h _N := inferInstance
  mem_extension N _ hN hQ := (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨hN, hQ⟩

/-- Membership in `finiteGroupClassSolvable` is solvability. -/
@[simp]
theorem finiteGroupClassSolvable_mem_iff (H : Type w) [Group H] [Finite H] :
    finiteGroupClassSolvable.mem H ↔ Group.IsSolvable H :=
  Iff.rfl

/-- The class of **all finite groups**. Its `C`-kernel is the intersection of all the open
normal subgroups, which is trivial for a profinite group. -/
def finiteGroupClassAll : FiniteGroupClass.{w} where
  mem _ := True
  mem_congr _ := Iff.rfl
  mem_trivial := trivial
  mem_subgroup _ _ := trivial
  mem_quotient _ _ := trivial
  mem_extension _ _ _ _ := trivial

/-- Every finite group is a member of `finiteGroupClassAll`. -/
@[simp]
theorem finiteGroupClassAll_mem (H : Type w) [Group H] [Finite H] :
    finiteGroupClassAll.mem H :=
  trivial

end TauCeti
