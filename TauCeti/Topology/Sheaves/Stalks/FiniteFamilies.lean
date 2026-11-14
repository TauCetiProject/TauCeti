/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Stalks

/-!
# Common representatives for finite families of germs

A finite family of germs can be represented on one neighbourhood, and finitely many equalities
of germs can be witnessed on one neighbourhood. These forms of the filteredness of open
neighbourhoods allow finitary operations on sections to descend to stalks.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {x : X}
  {C : Type v} [Category.{u} C] {FC : C → C → Type u}
  {CC : C → Type u} [∀ A B, FunLike (FC A B) (CC A) (CC B)]
  [ConcreteCategory C FC] [HasColimits C] [PreservesFilteredColimits (forget C)]
  (P : X.Presheaf C) {ι : Type w} [Finite ι]

/-- Finitely many germs have representatives on a common neighbourhood, inside any prescribed
neighbourhood. -/
theorem exists_le_germ_eq_family (t : ι → ToType (P.stalk x)) {V : Opens X} (hxV : x ∈ V) :
    ∃ U ≤ V, ∃ (hxU : x ∈ U) (s : ι → ToType (P.obj (op U))),
      ∀ i, P.germ U x hxU (s i) = t i := by
  classical
  choose U hxU s hs using fun i ↦ P.exists_germ_eq (t i)
  let W := V ⊓ ⨅ i, U i
  have hW : x ∈ W := ⟨hxV, by simpa only [← SetLike.mem_coe, Opens.coe_iInf,
    Set.mem_iInter] using hxU⟩
  have hWU (i : ι) : W ≤ U i := inf_le_right.trans (iInf_le U i)
  exact ⟨W, inf_le_left, hW, fun i ↦ P.map (homOfLE (hWU i)).op (s i),
    fun i ↦ (P.germ_res_apply (homOfLE (hWU i)) x hW (s i)).trans (hs i)⟩

/-- Equality of finitely many germs can be witnessed simultaneously on one neighbourhood. -/
theorem germ_eq_family {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : ι → ToType (P.obj (op U))) (t : ι → ToType (P.obj (op V)))
    (h : ∀ i, P.germ U x hxU (s i) = P.germ V x hxV (t i)) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (a : W ⟶ U) (b : W ⟶ V),
      ∀ i, P.map a.op (s i) = P.map b.op (t i) := by
  classical
  choose W hxW a b hab using fun i ↦ P.germ_eq x hxU hxV (s i) (t i) (h i)
  let A := (U ⊓ V) ⊓ ⨅ i, W i
  have hxA : x ∈ A := ⟨⟨hxU, hxV⟩, by simpa only [← SetLike.mem_coe, Opens.coe_iInf,
    Set.mem_iInter] using hxW⟩
  have hAW (i : ι) : A ≤ W i := inf_le_right.trans (iInf_le W i)
  refine ⟨A, hxA, homOfLE (inf_le_left.trans inf_le_left),
    homOfLE (inf_le_left.trans inf_le_right), fun i ↦ ?_⟩
  have hi := congrArg (P.map (homOfLE (hAW i)).op) (hab i)
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, Subsingleton.elim (homOfLE (hAW i) ≫ a i)
      (homOfLE (inf_le_left.trans inf_le_left)),
    Subsingleton.elim (homOfLE (hAW i) ≫ b i)
      (homOfLE (inf_le_left.trans inf_le_right))] using hi

end TopCat.Presheaf
