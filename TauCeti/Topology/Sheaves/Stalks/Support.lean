/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The support of a section of a sheaf

Let `F` be a presheaf on a topological space `X`, valued in a concrete category whose objects
carry a zero element preserved by the morphisms, such as abelian groups or modules. The support
of a section `s` of `F` over an open set `U` is the set of points `x ∈ U` at which the germ of `s`
does not vanish (`TopCat.Presheaf.sectionSupport`).

When the forgetful functor preserves filtered colimits, a germ vanishes exactly when the section
vanishes on a neighbourhood of the point (`TopCat.Presheaf.germ_eq_zero_iff`), so the support is
closed in `U`: its complement in `U` is open (`TopCat.Presheaf.isOpen_diff_sectionSupport`). Taking
supports commutes with restriction to a smaller open set
(`TopCat.Presheaf.sectionSupport_map`), so the support of a section is the union of the supports
of its restrictions to the members of a cover (`TopCat.Presheaf.sectionSupport_eq_iUnion`).

For a sheaf, the support detects vanishing. A section restricts to zero on an open subset `V`
exactly when `V` misses its support (`TopCat.Presheaf.map_eq_zero_iff_disjoint_sectionSupport`).
In particular a section vanishes exactly when its support is empty, and its restriction to the
complement `U ∖ S` of a closed set vanishes exactly when its support lies in `S`
(`TopCat.Presheaf.map_eq_zero_iff_sectionSupport_subset`). This is the kernel criterion
identifying the sections supported in `S` with the kernel of restriction to `U ∖ S`; in these terms
the supported sections `CategoryTheory.Sheaf.supportedSections` and
`CategoryTheory.Sheaf.supportedSubmodule` are the sections whose support lies in `S`.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, 1958, II.2.2.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, Springer, 1990, §2.3.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C] {FC : C → C → Type u}
  {CC : C → Type u} [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits C]

section Zero

variable [∀ A, Zero (CC A)]

section Presheaf

variable (F : X.Presheaf C) {U V : Opens X} {x : X}

/-- The support of a section `s` of `F` over `U`: the points of `U` at which the germ of `s` is
nonzero. -/
def sectionSupport (s : ToType (F.obj (op U))) : Set X :=
  {x | ∃ hx : x ∈ U, F.germ U x hx s ≠ 0}

variable {F}

theorem mem_sectionSupport_iff {s : ToType (F.obj (op U))} :
    x ∈ F.sectionSupport s ↔ ∃ hx : x ∈ U, F.germ U x hx s ≠ 0 :=
  Iff.rfl

theorem notMem_sectionSupport_iff {s : ToType (F.obj (op U))} (hx : x ∈ U) :
    x ∉ F.sectionSupport s ↔ F.germ U x hx s = 0 := by
  simp [mem_sectionSupport_iff, hx]

/-- The support of a section over `U` lies in `U`. -/
theorem sectionSupport_subset (s : ToType (F.obj (op U))) : F.sectionSupport s ⊆ U :=
  fun _ hx ↦ hx.1

/-- **Supports and restriction.** The support of the restriction of a section to a smaller open
set `V` is the part of its support in `V`. -/
@[simp]
theorem sectionSupport_map (i : V ⟶ U) (s : ToType (F.obj (op U))) :
    F.sectionSupport (F.map i.op s) = (V : Set X) ∩ F.sectionSupport s := by
  ext x
  simp only [mem_sectionSupport_iff, Set.mem_inter_iff, SetLike.mem_coe]
  exact ⟨fun ⟨hx, h⟩ ↦ ⟨hx, i.le hx, by rwa [germ_res_apply] at h⟩,
    fun ⟨hx, _, h⟩ ↦ ⟨hx, by rwa [germ_res_apply]⟩⟩

/-- The support of a section is the union of the supports of its restrictions to the members of
an open cover. -/
theorem sectionSupport_eq_iUnion {ι : Sort*} {W : ι → Opens X} (i : ∀ j, W j ⟶ U)
    (hW : U ≤ ⨆ j, W j) (s : ToType (F.obj (op U))) :
    F.sectionSupport s = ⋃ j, F.sectionSupport (F.map (i j).op s) := by
  simp only [sectionSupport_map, ← Set.iUnion_inter]
  refine (Set.inter_eq_right.mpr ((sectionSupport_subset s).trans fun x hx ↦ ?_)).symm
  simpa using hW hx

variable [∀ A B, ZeroHomClass (FC A B) (CC A) (CC B)]

@[simp]
theorem sectionSupport_zero : F.sectionSupport (0 : ToType (F.obj (op U))) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hx⟩ ↦ hx (map_zero _)

/-- A morphism of presheaves does not enlarge supports. -/
theorem sectionSupport_app_subset {G : X.Presheaf C} (f : F ⟶ G) (s : ToType (F.obj (op U))) :
    G.sectionSupport (f.app (op U) s) ⊆ F.sectionSupport s := fun x ⟨hx, h⟩ ↦
  ⟨hx, fun h' ↦ h <| by rw [← stalkFunctor_map_germ_apply, h']; exact map_zero _⟩

/-- A morphism of presheaves that is injective on the stalks at the points of `U` preserves the
supports of sections over `U`. -/
theorem sectionSupport_app {G : X.Presheaf C} (f : F ⟶ G)
    (hf : ∀ x ∈ U, Function.Injective ((stalkFunctor C x).map f)) (s : ToType (F.obj (op U))) :
    G.sectionSupport (f.app (op U) s) = F.sectionSupport s := by
  refine (sectionSupport_app_subset f s).antisymm fun x ⟨hx, h⟩ ↦ ⟨hx, fun h' ↦ h ?_⟩
  refine hf x hx ?_
  rw [stalkFunctor_map_germ_apply, h']
  exact (map_zero _).symm

variable [PreservesFilteredColimits (forget C)]

/-- A germ vanishes exactly when the section vanishes on a neighbourhood of the point. -/
theorem germ_eq_zero_iff (s : ToType (F.obj (op U))) (hx : x ∈ U) :
    F.germ U x hx s = 0 ↔ ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧ F.map i.op s = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨V, i, hxV, hV⟩ ↦ ?_⟩
  · obtain ⟨W, hxW, iU, iV, hW⟩ := F.germ_eq x hx hx s 0 (h.trans (map_zero _).symm)
    exact ⟨W, iU, hxW, hW.trans (map_zero _)⟩
  · rw [← F.germ_res_apply i x hxV, hV, map_zero]

/-- **The support is closed in `U`**: its complement in `U` is open. -/
theorem isOpen_diff_sectionSupport (s : ToType (F.obj (op U))) :
    IsOpen ((U : Set X) \ F.sectionSupport s) := by
  refine isOpen_iff_forall_mem_open.mpr fun x ⟨hxU, hx⟩ ↦ ?_
  obtain ⟨V, i, hxV, hV⟩ := (germ_eq_zero_iff s hxU).mp ((notMem_sectionSupport_iff hxU).mp hx)
  refine ⟨V, fun y hyV ↦ ⟨i.le hyV, fun hy ↦ ?_⟩, V.isOpen, hxV⟩
  have : y ∈ F.sectionSupport (F.map i.op s) := by
    rw [sectionSupport_map]
    exact ⟨hyV, hy⟩
  simp [hV] at this

/-- The support is closed in `U`: it contains every point of `U` in its closure. -/
theorem closure_sectionSupport_inter_subset (s : ToType (F.obj (op U))) :
    closure (F.sectionSupport s) ∩ U ⊆ F.sectionSupport s := by
  rintro x ⟨hcl, hxU⟩
  by_contra hx
  obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hcl _ (isOpen_diff_sectionSupport s) ⟨hxU, hx⟩
  exact hy.2 hy'

/-- The support of a global section is closed. -/
theorem isClosed_sectionSupport (s : ToType (F.obj (op ⊤))) : IsClosed (F.sectionSupport s) :=
  closure_subset_iff_isClosed.mp fun x hx ↦
    closure_sectionSupport_inter_subset s ⟨hx, Set.mem_univ x⟩

end Presheaf

section Sheaf

variable [∀ A B, ZeroHomClass (FC A B) (CC A) (CC B)] [PreservesFilteredColimits (forget C)]
  [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]
  (F : TopCat.Sheaf C X) {U V : Opens X}

/-- **The kernel criterion.** A section of a sheaf restricts to zero on an open subset `V` of `U`
exactly when `V` is disjoint from its support. -/
theorem map_eq_zero_iff_disjoint_sectionSupport (i : V ⟶ U) (s : ToType (F.obj.obj (op U))) :
    F.presheaf.map i.op s = 0 ↔ Disjoint (V : Set X) (F.presheaf.sectionSupport s) := by
  refine ⟨fun h ↦ ?_, fun h ↦ section_ext F V _ _ fun x hx ↦ ?_⟩
  · have := F.presheaf.sectionSupport_map i s
    rw [h, sectionSupport_zero] at this
    exact Set.disjoint_iff_inter_eq_empty.mpr this.symm
  · rw [germ_res_apply, map_zero]
    exact (notMem_sectionSupport_iff (i.le hx)).mp (Set.disjoint_left.mp h hx)

/-- A section of a sheaf vanishes exactly when its support is empty. -/
@[simp]
theorem sectionSupport_eq_empty_iff {s : ToType (F.obj.obj (op U))} :
    F.presheaf.sectionSupport s = ∅ ↔ s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ sectionSupport_zero⟩
  have := (map_eq_zero_iff_disjoint_sectionSupport F (𝟙 U) s).mpr (by simp [h])
  simpa using this

/-- **The kernel criterion for a closed set.** A section of a sheaf over `U` restricts to zero on
`U ∖ S`, for a closed set `S`, exactly when its support lies in `S`. -/
theorem map_eq_zero_iff_sectionSupport_subset (S : Closeds X)
    (s : ToType (F.obj.obj (op U))) :
    F.presheaf.map (homOfLE (inf_le_left : U ⊓ S.compl ≤ U)).op s = 0 ↔
      F.presheaf.sectionSupport s ⊆ S := by
  rw [map_eq_zero_iff_disjoint_sectionSupport, disjoint_comm, Set.disjoint_left]
  refine ⟨fun h x hx ↦ by_contra fun hxS ↦ h hx ⟨sectionSupport_subset s hx, hxS⟩,
    fun h x hx hx' ↦ hx'.2 (h hx)⟩

end Sheaf

end Zero

section AddZeroClass

variable [∀ A, AddZeroClass (CC A)] [∀ A B, AddMonoidHomClass (FC A B) (CC A) (CC B)]
  (F : X.Presheaf C) {U : Opens X}

/-- The support of a sum of sections lies in the union of their supports. -/
theorem sectionSupport_add_subset (s t : ToType (F.obj (op U))) :
    F.sectionSupport (s + t) ⊆ F.sectionSupport s ∪ F.sectionSupport t := by
  rintro x ⟨hx, h⟩
  by_contra h'
  simp only [Set.mem_union, not_or, notMem_sectionSupport_iff hx] at h'
  exact h (by rw [map_add, h'.1, h'.2, add_zero])

end AddZeroClass

section AddGroup

variable [∀ A, AddGroup (CC A)] [∀ A B, AddMonoidHomClass (FC A B) (CC A) (CC B)]
  (F : X.Presheaf C) {U : Opens X}

/-- Negating a section does not change its support. -/
@[simp]
theorem sectionSupport_neg (s : ToType (F.obj (op U))) :
    F.sectionSupport (-s) = F.sectionSupport s := by
  ext x
  simp [mem_sectionSupport_iff, map_neg]

/-- The support of a difference of sections lies in the union of their supports. -/
theorem sectionSupport_sub_subset (s t : ToType (F.obj (op U))) :
    F.sectionSupport (s - t) ⊆ F.sectionSupport s ∪ F.sectionSupport t := by
  simpa [sub_eq_add_neg] using F.sectionSupport_add_subset s (-t)

end AddGroup

/-- Multiplying a section of a presheaf of modules by a scalar does not enlarge its support. -/
theorem sectionSupport_smul_subset {R : Type u} [Ring R] (F : X.Presheaf (ModuleCat.{u} R))
    {U : Opens X} (r : R) (s : F.obj (op U)) :
    F.sectionSupport (r • s) ⊆ F.sectionSupport s := fun x ⟨hx, h⟩ ↦
  ⟨hx, fun h' ↦ h <| by rw [map_smul, h', smul_zero]⟩

end TopCat.Presheaf
