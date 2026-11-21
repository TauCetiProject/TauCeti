/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restriction maps of presheaves

Composing restriction maps along inclusions of opens in both directions gives the identity after
any morphism into the starting section object, since the inclusions force the opens to be equal;
in particular restriction from an open to itself is the identity on sections. Because the category
of opens is thin, two successive restrictions of a section agree with the single restriction between
the same opens.
A family of sections over opens is compatible as soon as any two of its sections are restrictions
of a common section in the family, and two sections of a sheaf of types that agree on the
intersection of their domains glue to a section over the union.

## Main results

* `TopCat.Presheaf.comp_map_comp_map_eq_self`: composing restriction maps along inclusions in both
  directions gives the identity after any morphism into the starting section object.
* `TopCat.Presheaf.map_eq_id`: restriction from an open to itself is the identity morphism.
* `TopCat.Presheaf.map_apply_eq_self`: restriction from an open to itself is the identity on
  sections.
* `TopCat.Presheaf.map_map_apply`: two successive restrictions of a section agree with any single
  restriction between the same opens.
* `TopCat.Presheaf.map_map_apply_eq_map_map_apply`: two composites of two restrictions between the
  same opens agree on sections.
* `TopCat.Presheaf.isCompatible_of_directed`: a family of sections, any two of which are
  restrictions of a common member, is compatible.
* `TopCat.Presheaf.IsSheaf.exists_gluing_sup`: two sections of a sheaf of types that agree on the
  intersection of their domains glue to a section over the union.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

universe w v u

variable {C : Type u} [Category.{v} C] {T : TopCat.{w}}

/-- Composing restriction maps along inclusions of opens in both directions gives the identity
after any morphism into the starting section object, since those inclusions force the opens to be
equal. The sections are given by a morphism `a` into `F.obj (op V)`, so that the lemma applies by
`exact` even when the intermediate open is only definitionally equal to the one in the composite. -/
theorem comp_map_comp_map_eq_self {F : T.Presheaf C} {A : C} {V V' : Opens T}
    (a : A ⟶ F.obj (op V)) (i : op V ⟶ op V') (j : op V' ⟶ op V) :
    (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

/-- Restriction from an open to itself is the identity morphism: there is only one morphism
from an open to itself, the identity. -/
@[simp]
theorem map_eq_id (F : Presheaf C T) {V : Opens T} (i : op V ⟶ op V) :
    F.map i = 𝟙 (F.obj (op V)) := by
  rw [Subsingleton.elim i (𝟙 _), F.map_id]

/-- Restriction from an open to itself is the identity on sections: there is only one morphism
from an open to itself, the identity. -/
theorem map_apply_eq_self {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] (F : Presheaf C T)
    {V : Opens T} (i : op V ⟶ op V) (s : ToType (F.obj (op V))) : F.map i s = s := by
  rw [map_eq_id, ConcreteCategory.id_apply]

/-- Two successive restrictions of a section agree with any single restriction between the same
opens: in the thin category of opens there is only one morphism between two opens. -/
theorem map_map_apply {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] (F : Presheaf C T)
    {V W Y : Opens T} (i : op Y ⟶ op W) (j : op W ⟶ op V) (k : op Y ⟶ op V)
    (s : ToType (F.obj (op Y))) : F.map j (F.map i s) = F.map k s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, Subsingleton.elim (i ≫ j) k]

/-- Two composites of two restriction maps with the same source and target opens agree on
sections, whatever the intermediate opens. -/
theorem map_map_apply_eq_map_map_apply {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] (F : Presheaf C T)
    {V W₁ W₂ Y : Opens T} (a : op Y ⟶ op W₁) (b : op W₁ ⟶ op V) (c : op Y ⟶ op W₂)
    (d : op W₂ ⟶ op V) (s : ToType (F.obj (op Y))) :
    F.map b (F.map a s) = F.map d (F.map c s) := by
  rw [map_map_apply F a b (a ≫ b), map_map_apply F c d (a ≫ b)]

/-- A family of sections over a directed family of opens is compatible as soon as any two of its
sections are restrictions of a common section in the family. -/
theorem isCompatible_of_directed {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {F : Presheaf C T}
    {ι : Type*} {U : ι → Opens T} {sf : ∀ i, ToType (F.obj (op (U i)))}
    (h : ∀ i j, ∃ k, ∃ (hik : U i ≤ U k) (hjk : U j ≤ U k),
      F.map (homOfLE hik).op (sf k) = sf i ∧ F.map (homOfLE hjk).op (sf k) = sf j) :
    IsCompatible F U sf := by
  intro i j
  obtain ⟨k, hik, hjk, hi, hj⟩ := h i j
  rw [← hi, ← hj, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp,
    ← F.map_comp]
  rfl

/-- Two sections of a sheaf of types over `U` and `V` that agree on `U ⊓ V` glue to a section over
`U ⊔ V`. -/
theorem IsSheaf.exists_gluing_sup {F : Presheaf (Type u) T} (hF : F.IsSheaf) {U V : Opens T}
    (a : F.obj (op U)) (b : F.obj (op V))
    (h : F.map (homOfLE inf_le_left).op a = F.map (homOfLE inf_le_right).op b) :
    ∃ s : F.obj (op (U ⊔ V)),
      F.map (homOfLE le_sup_left).op s = a ∧ F.map (homOfLE le_sup_right).op s = b :=
  Types.exists_of_isPullback (.of_isLimit (Sheaf.isLimitPullbackCone ⟨F, hF⟩ U V)) a b h

end TopCat.Presheaf
