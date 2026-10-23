/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import TauCeti.Topology.Sheaves.Presheaf

/-!
# A local criterion for flasque sheaves

A sheaf of sets, or of modules, is *flasque* when all of its restriction maps are surjective. This
file shows that it suffices to check this condition locally: if every point of the space has an open
neighbourhood `W` such that every restriction `F(V) ⟶ F(U)` with `U ≤ V ≤ W` is surjective, then
every restriction map of `F` is surjective. In other words, a locally flasque sheaf is flasque: the
global surjectivity of the restriction maps of a sheaf is reduced to a condition that can be checked
on a neighbourhood of each point.

The criterion is stated for sheaves valued in a concrete category whose forgetful functor preserves
limits and reflects isomorphisms, the generality at which the sheaf condition is available in terms
of unique gluings (`TopCat.Sheaf.existsUnique_gluing'`). Sheaves of modules are recovered through
`ModuleCat`, and sheaves of sets through `Type`.

## Main declarations

* `TopCat.Presheaf.IsLocallyFlasque`: a presheaf is locally flasque if every point has an open
  neighbourhood on which all restriction maps are surjective;
* `TopCat.Sheaf.IsLocallyFlasque`: a sheaf is locally flasque if its underlying presheaf is;
* `TopCat.Sheaf.surjective_map_of_isLocallyFlasque`: the restriction maps of a locally flasque
  sheaf are surjective, for every pair of open sets;
* `TopCat.Presheaf.isLocallyFlasque_of_forall_surjective`: surjectivity of all restriction maps
  implies local flasqueness;
* `TopCat.Sheaf.isFlasque_of_isLocallyFlasque`: a locally flasque sheaf is flasque;
* `TopCat.Sheaf.isLocallyFlasque_of_isFlasque`: a flasque sheaf is locally flasque when the
  forgetful functor of the coefficient category preserves epimorphisms;
* `TopCat.Sheaf.isFlasque_iff_isLocallyFlasque`: local flasqueness and flasqueness are
  equivalent under these assumptions, in particular for sheaves of modules and sets.

## References

* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*: the maximal-extension argument,
  in which the extensions of a section are ordered by their open domains.
* Mathlib's `TopCat.Sheaf.IsFlasque.epi_of_shortExact` (`Mathlib/Topology/Sheaves/Flasque.lean`):
  the proof plan follows its maximal-extension argument, the chains of extensions being glued
  through `TopCat.Sheaf.existsUnique_gluing'` and the compatibility of the glued sections taken
  through `TopCat.Presheaf.IsCompatible`.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w w'

namespace TopCat.Presheaf

variable {C : Type v} [Category.{w} C] {FC : C → C → Type*} {CC : C → Type w'}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat.{u}}

/-- A presheaf is locally flasque if every point of the space has an open neighbourhood `W` on
which every restriction map is surjective, i.e. such that for all open sets `U ≤ V ≤ W` the
restriction `F(V) ⟶ F(U)` is surjective. -/
class IsLocallyFlasque (F : Presheaf C X) : Prop where
  /-- Every point has an open neighbourhood on which all the restriction maps are surjective. -/
  surj : ∀ x : X, ∃ W : Opens X, x ∈ W ∧
    ∀ ⦃U V : Opens X⦄ (h : U ≤ V), V ≤ W → Function.Surjective (F.map (homOfLE h).op)

/-- If all the restriction maps of a presheaf are surjective, then it is locally flasque: the whole
space is a witness at every point. -/
theorem isLocallyFlasque_of_forall_surjective (F : Presheaf C X)
    (hF : ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), Function.Surjective (F.map (homOfLE hUV).op)) :
    F.IsLocallyFlasque := by
  refine ⟨?_⟩
  intro x
  refine ⟨⊤, Set.mem_univ x, ?_⟩
  intro U V hUV _
  exact hF hUV

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {C : Type v} [Category.{w} C] {FC : C → C → Type*} {CC : C → Type w'}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat.{u}}

/-- A sheaf is locally flasque if its underlying presheaf is locally flasque. -/
abbrev IsLocallyFlasque (F : Sheaf C X) := Presheaf.IsLocallyFlasque F.obj

variable {X : TopCat.{u}}

section General

variable {C : Type v} [Category.{w} C] {FC : C → C → Type*} {CC : C → Type w'}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

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

variable {F : TopCat.Presheaf C X} {U : Opens X} {a : ToType (F.obj (op U))}

/-- The order on extensions is transitive. -/
private lemma trans {s t u : Extension F a} (h₁ : s.Le t) (h₂ : t.Le u) : s.Le u where
  le_dom := h₁.le_dom.trans h₂.le_dom
  sec_le h :=
    -- Inclusion proofs give definitionally equal restriction maps.
    calc F.map (homOfLE h).op u.sec
        = F.map (homOfLE h₁.le_dom).op (F.map (homOfLE h₂.le_dom).op u.sec) :=
            (TopCat.Presheaf.restrict_restrict h₁.le_dom h₂.le_dom u.sec).symm
      _ = F.map (homOfLE h₁.le_dom).op t.sec := by rw [h₂.sec_le h₂.le_dom]
      _ = s.sec := h₁.sec_le h₁.le_dom

end

/-- A chain of extensions of a section is bounded by an extension over the supremum of the domains
of the chain: the sheaf condition glues the sections of the chain. -/
private lemma exists_ub_of_isChain [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
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
        -- Both maps use the same inclusion, differing only in its proof.
        rfl
      · have hne' : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
        rcases hc s.2 t.2 hne' with h | h
        · have hsf : F.1.map (homOfLE h.le_dom).op (sf t) = sf s := h.sec_le h.le_dom
          simp only [Opens.infLELeft, Opens.infLERight]
          rw [← hsf]
          exact TopCat.Presheaf.restrict_restrict (F := F.1)
            (inf_le_left : f s ⊓ f t ≤ f s) h.le_dom (sf t)
        · have hsf : F.1.map (homOfLE h.le_dom).op (sf s) = sf t := h.sec_le h.le_dom
          simp only [Opens.infLELeft, Opens.infLERight]
          rw [← hsf]
          exact (TopCat.Presheaf.restrict_restrict (F := F.1)
            (inf_le_right : f s ⊓ f t ≤ f t) h.le_dom (sf s)).symm
    obtain ⟨w, hw, -⟩ := F.existsUnique_gluing' f (iSup f) (fun s => homOfLE (le_iSup f s))
      le_rfl sf hcompat
    refine ⟨⟨iSup f, s₀.le_dom.trans (le_iSup f ⟨s₀, hs₀⟩), w, ?_⟩, ?_⟩
    · have h0 : F.1.map (homOfLE (le_iSup f ⟨s₀, hs₀⟩)).op w = s₀.sec := hw ⟨s₀, hs₀⟩
      calc F.1.map (homOfLE (s₀.le_dom.trans (le_iSup f ⟨s₀, hs₀⟩))).op w
          = F.1.map (homOfLE s₀.le_dom).op
              (F.1.map (homOfLE (le_iSup f ⟨s₀, hs₀⟩)).op w) :=
            (TopCat.Presheaf.restrict_restrict s₀.le_dom (le_iSup f ⟨s₀, hs₀⟩) w).symm
        _ = F.1.map (homOfLE s₀.le_dom).op s₀.sec := by rw [h0]
        _ = a := s₀.sec_le
    · intro s hs
      exact ⟨le_iSup f ⟨s, hs⟩, fun _ => hw ⟨s, hs⟩⟩
  · exact ⟨⟨U, le_rfl, a, by simp⟩, fun s hs => absurd ⟨s, hs⟩ hne⟩

/-- The domain of a maximal extension of a section contains the ambient open set: a point missing
from it has a neighbourhood on which all restriction maps are surjective, and the maximal extension
extends across that neighbourhood. -/
private lemma le_dom_of_maximal [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
    (F : TopCat.Sheaf C X) [hF : F.IsLocallyFlasque] {U V : Opens X} {a : ToType (F.1.obj (op U))}
    (m : Extension F.1 a)
    (hm : ∀ e : Extension F.1 a, m.Le e → e.Le m) : V ≤ m.dom := by
  intro x hxV
  by_contra hx
  obtain ⟨W, hxW, hW⟩ := hF.surj x
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
    · -- the overlap is symmetric in the two open sets, so transport the equation along `inf_comm`
      have h₁ : TopCat.Presheaf.restrictOpen m.sec (m.dom ⊓ W')
          (inf_le_left : m.dom ⊓ W' ≤ m.dom) =
          TopCat.Presheaf.restrictOpen bW (m.dom ⊓ W')
            (inf_le_right : m.dom ⊓ W' ≤ W') := hbW.symm
      apply_fun (fun z => TopCat.Presheaf.restrictOpen z (W' ⊓ m.dom)
        (le_of_eq (inf_comm W' m.dom))) at h₁
      rw [TopCat.Presheaf.restrict_restrict, TopCat.Presheaf.restrict_restrict] at h₁
      exact h₁.symm
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
      calc F.1.map (homOfLE (m.le_dom.trans le_sup_left)).op w
          = F.1.map (homOfLE m.le_dom).op (F.1.map (homOfLE le_sup_left).op w) :=
            (TopCat.Presheaf.restrict_restrict m.le_dom le_sup_left w).symm
        _ = F.1.map (homOfLE m.le_dom).op m.sec := by rw [h0]
        _ = a := m.sec_le⟩
  have hmle : m.Le e' := ⟨le_sup_left, fun _ => hw 0⟩
  exact hx ((sup_le_iff.mp (hm e' hmle).le_dom).2 hxW')

end Extension

/-- **Flasque locality**: if every point of the space has an open neighbourhood on which all the
restriction maps of a sheaf are surjective, then all the restriction maps of the sheaf are
surjective. -/
theorem surjective_map_of_isLocallyFlasque [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
    (F : TopCat.Sheaf C X) [F.IsLocallyFlasque] ⦃U V : Opens X⦄ (hUV : U ≤ V) :
    Function.Surjective (F.1.map (homOfLE hUV).op) := by
  intro a
  -- the extensions of `a`, ordered by extension; a maximal one is a greatest one
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (r := fun s t : Extension F.1 a => s.Le t)
    (fun c hc => Extension.exists_ub_of_isChain F c hc)
    (fun {s t u} h₁ h₂ => Extension.trans h₁ h₂)
  have hVle : V ≤ m.dom := Extension.le_dom_of_maximal F m hm
  refine ⟨F.1.map (homOfLE hVle).op m.sec, ?_⟩
  calc F.1.map (homOfLE hUV).op (F.1.map (homOfLE hVle).op m.sec)
      = F.1.map (homOfLE (hUV.trans hVle)).op m.sec :=
        TopCat.Presheaf.restrict_restrict hUV hVle m.sec
    -- The composite inclusion and `m.le_dom` differ only in their proofs.
    _ = a := m.sec_le

/-- **Flasque locality**: a locally flasque sheaf is flasque. -/
instance isFlasque_of_isLocallyFlasque [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
    (F : TopCat.Sheaf C X) [F.IsLocallyFlasque] :
    F.IsFlasque where
  epi {U V} i := by
    have hi : i = (homOfLE (leOfHom i.unop)).op :=
      (congrArg Quiver.Hom.op (homOfLE_leOfHom i.unop)).symm
    rw [hi]
    exact ConcreteCategory.epi_of_surjective _
      (surjective_map_of_isLocallyFlasque F (leOfHom i.unop))

/-- **Flasque locality, converse**: a flasque sheaf is locally flasque when the forgetful functor
of its coefficient category preserves epimorphisms. -/
theorem isLocallyFlasque_of_isFlasque [(CategoryTheory.forget C).PreservesEpimorphisms]
    (F : TopCat.Sheaf C X) (hF : F.IsFlasque) :
    F.IsLocallyFlasque := by
  refine TopCat.Presheaf.isLocallyFlasque_of_forall_surjective F.1 ?_
  intro U V hUV
  let := hF.epi (homOfLE hUV).op
  exact (CategoryTheory.epi_iff_surjective
    ((CategoryTheory.forget C).map (F.1.map (homOfLE hUV).op))).mp inferInstance

/-- A sheaf is flasque exactly when it is locally flasque, provided its forgetful functor
preserves limits and epimorphisms and reflects isomorphisms. -/
theorem isFlasque_iff_isLocallyFlasque [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).PreservesEpimorphisms] (F : TopCat.Sheaf C X) :
    F.IsFlasque ↔ F.IsLocallyFlasque := by
  constructor
  · intro hF
    exact isLocallyFlasque_of_isFlasque F hF
  · intro h
    let : F.IsLocallyFlasque := h
    exact isFlasque_of_isLocallyFlasque F

end General

end TopCat.Sheaf
