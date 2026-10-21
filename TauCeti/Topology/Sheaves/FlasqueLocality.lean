/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# A local criterion for flasque sheaves

A sheaf of sets, or of modules, is *flasque* when all of its restriction maps are surjective. This
file shows that it suffices to check this condition locally: if every point of the space has an open
neighbourhood `W` such that every restriction `F(V) ⟶ F(U)` with `U ≤ V ≤ W` is surjective, then
every restriction map of `F` is surjective. In other words, a locally flasque sheaf is flasque: the
global surjectivity of the restriction maps of a sheaf is reduced to a condition that can be checked
on a neighbourhood of each point. The criterion is available for sheaves of sets and for sheaves of
modules.

## Main declarations

* `TauCeti.Topology.IsLocallyFlasque`: a presheaf is locally flasque if every point has an open
  neighbourhood on which all restriction maps are surjective;
* `TauCeti.Topology.surjective_map_of_isLocallyFlasque`: the restriction maps of a locally flasque
  sheaf are surjective, for every pair of open sets;
* `TauCeti.Topology.isLocallyFlasque_of_forall_surjective`: surjectivity of all restriction maps
  implies local flasqueness;
* `TauCeti.Topology.isFlasque_of_isLocallyFlasque`: a locally flasque sheaf is flasque;
* `TauCeti.Topology.isLocallyFlasque_of_isFlasque` and
  `TauCeti.Topology.isFlasque_iff_isLocallyFlasque`: for sheaves of modules, local flasqueness and
  flasqueness are equivalent;
* `TauCeti.Topology.isLocallyFlasque_of_isFlasque_types` and
  `TauCeti.Topology.isFlasque_iff_isLocallyFlasque_types`: the same equivalence for sheaves of
  sets.

## Implementation notes

The results are stated for sheaves valued in a concrete category whose forgetful functor preserves
limits and reflects isomorphisms, the generality at which the sheaf condition is available in terms
of unique gluings (`TopCat.Sheaf.existsUnique_gluing'`). Sheaves of modules are recovered through
`ModuleCat` and sheaves of sets through `Type`.

## References

* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*: the maximal-extension argument,
  in which the extensions of a section are ordered by their open domains.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w w'

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}}

section General

variable {C : Type v} [Category.{w} C] {FC : C → C → Type*} {CC : C → Type w'}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- A presheaf is locally flasque if every point of the space has an open neighbourhood `W` on
which every restriction map is surjective, i.e. such that for all open sets `U ≤ V ≤ W` the
restriction `F(V) ⟶ F(U)` is surjective. -/
def IsLocallyFlasque (F : TopCat.Presheaf C X) : Prop :=
  ∀ x : X, ∃ W : Opens X, x ∈ W ∧
    ∀ ⦃U V : Opens X⦄ (h : U ≤ V), V ≤ W → Function.Surjective (F.map (homOfLE h).op)

/-- An extension of a section `a` of a presheaf over an open set `U` to a larger open set, together
with the section over that open set. -/
private structure Extension (F : TopCat.Presheaf C X) {U : Opens X}
    (a : ToType (F.obj (op U))) where
  /-- The open set on which the extended section is defined. -/
  dom : Opens X
  /-- The original open set is contained in the domain of the extension. -/
  le_dom : U ≤ dom
  /-- The extended section. -/
  sec : ToType (F.obj (op dom))
  /-- The extended section restricts to the original section. -/
  sec_le : F.map (homOfLE le_dom).op sec = a

/-- The order on extensions of a fixed section: `s` is below `t` if `t` is defined on a larger open
set and restricts to `s`. -/
private structure Extension.Le {F : TopCat.Presheaf C X} {U : Opens X}
    {a : ToType (F.obj (op U))} (s t : Extension F a) : Prop where
  /-- The domain of `s` is contained in the domain of `t`. -/
  le_dom : s.dom ≤ t.dom
  /-- `t` restricts to `s`. -/
  sec_le : ∀ h : s.dom ≤ t.dom, F.map (homOfLE h).op t.sec = s.sec

namespace Extension

section

variable {F : TopCat.Presheaf C X}

/-- Two proofs of the same inequality give the same restriction map. -/
private lemma map_homOfLE_congr {U V : Opens X} (h h' : U ≤ V) (s : ToType (F.obj (op V))) :
    F.map (homOfLE h).op s = F.map (homOfLE h').op s := by
  rw [Subsingleton.elim h h']

/-- Restricting a section twice is restricting it once. -/
private lemma map_homOfLE_apply_map {A B D : Opens X} (h₁ : A ≤ B) (h₂ : B ≤ D)
    (s : ToType (F.obj (op D))) :
    F.map (homOfLE h₁).op (F.map (homOfLE h₂).op s) = F.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, homOfLE_comp]

/-- Morphisms between two fixed open sets are unique. -/
private lemma hom_ext {U V : Opens X} (f g : U ⟶ V) : f = g :=
  (homOfLE_leOfHom f).symm.trans
    ((congrArg homOfLE (Subsingleton.elim (leOfHom f) (leOfHom g))).trans
      (homOfLE_leOfHom g))

/-- Transporting a section along an equality of open sets and then restricting is a single
restriction. -/
private lemma map_eqToHom_map_homOfLE {A B D : Opens X} (e : A = B) (h : B ≤ D) (h' : A ≤ D)
    (s : ToType (F.obj (op D))) :
    F.map (eqToHom e).op (F.map (homOfLE h).op s) = F.map (homOfLE h').op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, hom_ext (eqToHom e ≫ homOfLE h)
    (homOfLE h')]

variable {U : Opens X} {a : ToType (F.obj (op U))}

/-- The order on extensions is transitive. -/
private lemma trans {s t u : Extension F a} (h₁ : s.Le t) (h₂ : t.Le u) : s.Le u where
  le_dom := h₁.le_dom.trans h₂.le_dom
  sec_le h :=
    calc F.map (homOfLE h).op u.sec
        = F.map (homOfLE (h₁.le_dom.trans h₂.le_dom)).op u.sec := map_homOfLE_congr _ _ _
      _ = F.map (homOfLE h₁.le_dom).op (F.map (homOfLE h₂.le_dom).op u.sec) :=
            (map_homOfLE_apply_map _ _ _).symm
      _ = F.map (homOfLE h₁.le_dom).op t.sec := by rw [h₂.sec_le h₂.le_dom]
      _ = s.sec := h₁.sec_le h₁.le_dom

end

/-- A chain of extensions of a section is bounded by an extension over the supremum of the domains
of the chain: the sheaf condition glues the sections of the chain. -/
private lemma exists_ub_of_isChain [HasLimitsOfSize.{u, u} C]
    [(forget C).ReflectsIsomorphisms] [PreservesLimitsOfSize.{u, u} (forget C)]
    (F : TopCat.Sheaf C X) {U : Opens X} {a : ToType (F.1.obj (op U))}
    (c : Set (Extension F.1 a)) (hc : IsChain (fun s t => s.Le t) c) :
    ∃ ub : Extension F.1 a, ∀ s ∈ c, s.Le ub := by
  by_cases hne : c.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    let f : c → Opens X := fun s => s.1.dom
    let sf : ∀ s : c, ToType (F.1.obj (op (f s))) := fun s => s.1.sec
    have hcompat : TopCat.Presheaf.IsCompatible F.1 f sf := by
      intro s t
      by_cases hst : s = t
      · subst hst
        exact Extension.map_homOfLE_congr (F := F.1) _ _ _
      · have hne' : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
        rcases hc s.2 t.2 hne' with h | h
        · have hsf : F.1.map (homOfLE h.le_dom).op (sf t) = sf s := h.sec_le h.le_dom
          simp only [Opens.infLELeft, Opens.infLERight]
          rw [← hsf,
            Extension.map_homOfLE_apply_map (F := F.1)
              (inf_le_left : f s ⊓ f t ≤ f s) h.le_dom (sf t)]
        · have hsf : F.1.map (homOfLE h.le_dom).op (sf s) = sf t := h.sec_le h.le_dom
          simp only [Opens.infLELeft, Opens.infLERight]
          rw [← hsf,
            Extension.map_homOfLE_apply_map (F := F.1)
              (inf_le_right : f s ⊓ f t ≤ f t) h.le_dom (sf s)]
    obtain ⟨w, hw, -⟩ := F.existsUnique_gluing' f (iSup f) (fun s => homOfLE (le_iSup f s))
      le_rfl sf hcompat
    refine ⟨⟨iSup f, s₀.le_dom.trans (le_iSup f ⟨s₀, hs₀⟩), w, ?_⟩, ?_⟩
    · have h0 : F.1.map (homOfLE (le_iSup f ⟨s₀, hs₀⟩)).op w = s₀.sec := hw ⟨s₀, hs₀⟩
      calc F.1.map (homOfLE (s₀.le_dom.trans (le_iSup f ⟨s₀, hs₀⟩))).op w
          = F.1.map (homOfLE s₀.le_dom).op
              (F.1.map (homOfLE (le_iSup f ⟨s₀, hs₀⟩)).op w) :=
            (Extension.map_homOfLE_apply_map _ _ _).symm
        _ = F.1.map (homOfLE s₀.le_dom).op s₀.sec := by rw [h0]
        _ = a := s₀.sec_le
    · intro s hs
      exact ⟨le_iSup f ⟨s, hs⟩,
        fun hh => (Extension.map_homOfLE_congr hh _ w).trans (hw ⟨s, hs⟩)⟩
  · exact ⟨⟨U, le_rfl, a, by simp⟩, fun s hs => absurd ⟨s, hs⟩ hne⟩

/-- The domain of a maximal extension of a section contains the ambient open set: a point missing
from it has a neighbourhood on which all restriction maps are surjective, and the maximal extension
extends across that neighbourhood. -/
private lemma le_dom_of_maximal [HasLimitsOfSize.{u, u} C]
    [(forget C).ReflectsIsomorphisms] [PreservesLimitsOfSize.{u, u} (forget C)]
    (F : TopCat.Sheaf C X) {U V : Opens X} {a : ToType (F.1.obj (op U))}
    (hF : IsLocallyFlasque F.1) (m : Extension F.1 a)
    (hm : ∀ e : Extension F.1 a, m.Le e → e.Le m) : V ≤ m.dom := by
  intro x hxV
  by_contra hx
  obtain ⟨W, hxW, hW⟩ := hF x
  let W' : Opens X := W ⊓ V
  have hxW' : x ∈ W' := ⟨hxW, hxV⟩
  obtain ⟨bW, hbW⟩ := hW (inf_le_right : m.dom ⊓ W' ≤ W')
    ((le_rfl : W' ≤ W').trans inf_le_left)
    (F.1.map (homOfLE (inf_le_left : m.dom ⊓ W' ≤ m.dom)).op m.sec)
  -- glue the maximal section with the local lift
  let f : Fin 2 → Opens X := Fin.cases m.dom (fun _ => W')
  let sf : (i : Fin 2) → ToType (F.1.obj (op (f i)))
    | 0 => m.sec
    | 1 => bW
  have hcompat : TopCat.Presheaf.IsCompatible F.1 f sf := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [f, sf, Opens.infLELeft, Opens.infLERight]
    · exact hbW.symm
    · exact (Extension.map_eqToHom_map_homOfLE (F := F.1) (inf_comm W' m.dom)
        (inf_le_right : m.dom ⊓ W' ≤ W') (inf_le_left : W' ⊓ m.dom ≤ W') bW).symm.trans
        ((congrArg (fun z => F.1.map (eqToHom (inf_comm W' m.dom)).op z) hbW).trans
          (Extension.map_eqToHom_map_homOfLE (F := F.1) (inf_comm W' m.dom)
            (inf_le_left : m.dom ⊓ W' ≤ m.dom) (inf_le_right : W' ⊓ m.dom ≤ m.dom)
            m.sec))
  let iUV : ∀ i : Fin 2, f i ⟶ (m.dom ⊔ W')
    | 0 => homOfLE le_sup_left
    | 1 => homOfLE le_sup_right
  have hcover : m.dom ⊔ W' ≤ iSup f := by
    rw [sup_le_iff]
    exact ⟨le_iSup f 0, le_iSup f 1⟩
  obtain ⟨w, hw, -⟩ := F.existsUnique_gluing' f (m.dom ⊔ W') iUV hcover sf hcompat
  let e' : Extension F.1 a :=
    ⟨m.dom ⊔ W', m.le_dom.trans le_sup_left, w, by
      have h0 : F.1.map (homOfLE (le_sup_left : m.dom ≤ m.dom ⊔ W')).op w = m.sec := hw 0
      rw [← Extension.map_homOfLE_apply_map (F := F.1) m.le_dom le_sup_left w, h0, m.sec_le]⟩
  have hmle : m.Le e' := ⟨le_sup_left,
    fun hh => (Extension.map_homOfLE_congr hh _ w).trans (hw 0)⟩
  exact hx ((sup_le_iff.mp (hm e' hmle).le_dom).2 hxW')

end Extension

/-- **Flasque locality**: if every point of the space has an open neighbourhood on which all the
restriction maps of a sheaf are surjective, then all the restriction maps of the sheaf are
surjective. -/
theorem surjective_map_of_isLocallyFlasque [HasLimitsOfSize.{u, u} C]
    [(forget C).ReflectsIsomorphisms] [PreservesLimitsOfSize.{u, u} (forget C)]
    (F : TopCat.Sheaf C X) (hF : IsLocallyFlasque F.1) ⦃U V : Opens X⦄ (hUV : U ≤ V) :
    Function.Surjective (F.1.map (homOfLE hUV).op) := by
  intro a
  -- the extensions of `a`, ordered by extension; a maximal one is a greatest one
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (r := fun s t : Extension F.1 a => s.Le t)
    (fun c hc => Extension.exists_ub_of_isChain F c hc)
    (fun {s t u} h₁ h₂ => Extension.trans h₁ h₂)
  have hVle : V ≤ m.dom := Extension.le_dom_of_maximal F hF m hm
  refine ⟨F.1.map (homOfLE hVle).op m.sec, ?_⟩
  calc F.1.map (homOfLE hUV).op (F.1.map (homOfLE hVle).op m.sec)
      = F.1.map (homOfLE (hUV.trans hVle)).op m.sec :=
        Extension.map_homOfLE_apply_map _ _ _
    _ = F.1.map (homOfLE m.le_dom).op m.sec := Extension.map_homOfLE_congr _ _ _
    _ = a := m.sec_le

/-- If all the restriction maps of a presheaf are surjective, then it is locally flasque: the whole
space is a witness at every point. -/
theorem isLocallyFlasque_of_forall_surjective (F : TopCat.Presheaf C X)
    (hF : ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), Function.Surjective (F.map (homOfLE hUV).op)) :
    IsLocallyFlasque F := by
  intro x
  refine ⟨⊤, trivial, ?_⟩
  intro U V hUV _
  exact hF hUV

/-- **Flasque locality**: a locally flasque sheaf is flasque. -/
theorem isFlasque_of_isLocallyFlasque [HasLimitsOfSize.{u, u} C]
    [(forget C).ReflectsIsomorphisms] [PreservesLimitsOfSize.{u, u} (forget C)]
    (F : TopCat.Sheaf C X) (hF : IsLocallyFlasque F.1) : F.IsFlasque where
  epi {U V} i := by
    have hi : i = (homOfLE (leOfHom i.unop)).op :=
      (congrArg Quiver.Hom.op (homOfLE_leOfHom i.unop)).symm
    rw [hi]
    exact ConcreteCategory.epi_of_surjective _
      (surjective_map_of_isLocallyFlasque F hF (leOfHom i.unop))

end General

section Modules

variable {R : Type u} [Ring R]

/-- For a sheaf of modules, being flasque is a local property: it suffices to check that the
restriction maps inside a neighbourhood of each point are surjective. -/
theorem isLocallyFlasque_of_isFlasque (F : TopCat.Sheaf (ModuleCat.{u} R) X) (hF : F.IsFlasque) :
    IsLocallyFlasque F.1 := by
  refine isLocallyFlasque_of_forall_surjective F.1 ?_
  intro U V hUV
  exact (ModuleCat.epi_iff_surjective _).mp (hF.epi (homOfLE hUV).op)

/-- For sheaves of modules, being flasque is equivalent to being locally flasque. -/
theorem isFlasque_iff_isLocallyFlasque (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    F.IsFlasque ↔ IsLocallyFlasque F.1 :=
  ⟨isLocallyFlasque_of_isFlasque F, isFlasque_of_isLocallyFlasque F⟩

end Modules

section Types

/-- For a sheaf of sets, being flasque is a local property: it suffices to check that the
restriction maps inside a neighbourhood of each point are surjective. -/
theorem isLocallyFlasque_of_isFlasque_types (F : TopCat.Sheaf (Type u) X) (hF : F.IsFlasque) :
    IsLocallyFlasque F.1 := by
  refine isLocallyFlasque_of_forall_surjective F.1 ?_
  intro U V hUV
  exact (CategoryTheory.epi_iff_surjective _).mp (hF.epi (homOfLE hUV).op)

/-- For sheaves of sets, being flasque is equivalent to being locally flasque. -/
theorem isFlasque_iff_isLocallyFlasque_types (F : TopCat.Sheaf (Type u) X) :
    F.IsFlasque ↔ IsLocallyFlasque F.1 :=
  ⟨isLocallyFlasque_of_isFlasque_types F, isFlasque_of_isLocallyFlasque F⟩

end Types

end Topology

end TauCeti
