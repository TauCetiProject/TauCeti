/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Final

/-!
# Initiality of base change in a Grothendieck construction

For `C : D ⥤ Cat` and `G : D' ⥤ D`, Mathlib's `Grothendieck.pre C G` compares the
Grothendieck construction of `G ⋙ C` with that of `C`, and Mathlib proves that it is final
whenever `G` is final (`Grothendieck.final_pre`). The Grothendieck construction is covariant
in its fibers, so the initial counterpart needs a condition on the fibers as well: `pre C G` is
initial when `G` is initial and every transition functor `C.map f` out of an object
`G.obj d'` is initial.

Restricting a diagram on the total category along `pre C G` is therefore an instance of
Mathlib's `Functor.Initial.limitIso`. A costructured arrow from `pre C G` to `⟨d, x⟩` consists
of a costructured arrow `f : G.obj d' ⟶ d` together with a costructured arrow to `x` for
`C.map f`, and the connected fibers over `CostructuredArrow G d` are linked along its arrows.

Adapted from `Mei/CategoryTheory/Limits/Final.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

namespace CategoryTheory.Grothendieck

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {C : D ⥤ Cat.{v₃, u₃}} {G : D' ⥤ D}

section InitialPre

variable {d : D} {x : C.obj d}

/-- The costructured arrow to `⟨d, x⟩` with base component `a` and fiber component `b`. -/
private abbrev preArrow (a : CostructuredArrow G d)
    (b : CostructuredArrow (C.map a.hom).toFunctor x) :
    CostructuredArrow (pre C G) ⟨d, x⟩ :=
  CostructuredArrow.mk (Y := (⟨a.left, b.left⟩ : Grothendieck (G ⋙ C))) (Hom.mk a.hom b.hom)

/-- The equation for assembled costructured arrows reduces to its base and fiber equations. -/
private lemma preArrow_hom_ext {a a' : CostructuredArrow G d}
    {b : CostructuredArrow (C.map a.hom).toFunctor x}
    {b' : CostructuredArrow (C.map a'.hom).toFunctor x}
    (u : a.left ⟶ a'.left)
    (φ : (C.map (G.map u)).toFunctor.obj b.left ⟶ b'.left)
    (h : G.map u ≫ a'.hom = a.hom)
    (w : eqToHom (by rw [← Cat.Hom.comp_obj, ← Functor.map_comp, h]) ≫
      (C.map a'.hom).toFunctor.map φ ≫ b'.hom = b.hom) :
    (pre C G).map (Hom.mk u φ : (preArrow a b).left ⟶ (preArrow a' b').left) ≫
      (preArrow a' b').hom = (preArrow a b).hom := by
  fapply Grothendieck.ext
  · exact h
  · simp only [CostructuredArrow.mk_left, pre_obj_base, CostructuredArrow.mk_hom_eq_self,
      pre_obj_fiber, comp_base, pre_map_base, comp_fiber, pre_map_fiber]
    -- `pre` preserves fibers definitionally: `(G ⋙ C).obj a.left = C.obj (G.obj a.left)`
    -- and `(G ⋙ C).map u = C.map (G.map u)`. The generated `Grothendieck.ext`
    -- transport still contains these wrappers; `erw` unfolds them when composing the casts.
    erw [eqToHom_trans_assoc]
    exact w

/-- Fiber components over a fixed base component map to costructured arrows on `pre C G`. -/
private def preFiberPrefunctor (a : CostructuredArrow G d) :
    CostructuredArrow (C.map a.hom).toFunctor x ⥤q CostructuredArrow (pre C G) ⟨d, x⟩ where
  obj b := preArrow a b
  map {b b'} g := CostructuredArrow.homMk (Hom.mk (𝟙 a.left) (eqToHom (by simp) ≫ g.left)) (by
    apply preArrow_hom_ext _ _ (by simp)
    simp [Functor.map_comp, eqToHom_map, eqToHom_trans_assoc])

/-- Transport of a fiber component along an arrow of base components. -/
private abbrev preTransport {a₁ a₂ : CostructuredArrow G d} (h : a₁ ⟶ a₂)
    (b : CostructuredArrow (C.map a₁.hom).toFunctor x) :
    CostructuredArrow (C.map a₂.hom).toFunctor x :=
  CostructuredArrow.mk (Y := (C.map (G.map h.left)).toFunctor.obj b.left)
    (eqToHom (by rw [← Cat.Hom.comp_obj, ← Functor.map_comp, CostructuredArrow.w h]) ≫ b.hom)

/-- The arrow from a costructured arrow to its transport along an arrow of base components. -/
private def toPreTransport {a₁ a₂ : CostructuredArrow G d} (h : a₁ ⟶ a₂)
    (b : CostructuredArrow (C.map a₁.hom).toFunctor x) :
    preArrow a₁ b ⟶ preArrow a₂ (preTransport h b) :=
  CostructuredArrow.homMk (Hom.mk h.left (𝟙 _)) (by
    apply preArrow_hom_ext _ _ (CostructuredArrow.w h)
    simp [eqToHom_trans_assoc])

end InitialPre

/-- Base change along an initial functor is initial on Grothendieck constructions when every
transition functor out of its image is initial. This is the initial counterpart of
`Grothendieck.final_pre`, which needs no condition on the fibers. -/
instance initial_pre [G.Initial]
    [∀ {d' : D'} {d : D} (f : G.obj d' ⟶ d), (C.map f).toFunctor.Initial] :
    (pre C G).Initial where
  out := by
    rintro ⟨d, x⟩
    obtain ⟨a₀⟩ : Nonempty (CostructuredArrow G d) := inferInstance
    obtain ⟨b₀⟩ : Nonempty (CostructuredArrow (C.map a₀.hom).toFunctor x) := inferInstance
    have : Nonempty (CostructuredArrow (pre C G) ⟨d, x⟩) := ⟨preArrow a₀ b₀⟩
    have fiber (a : CostructuredArrow G d) (b b' : CostructuredArrow (C.map a.hom).toFunctor x) :
        Zigzag (preArrow a b) (preArrow a b') :=
      zigzag_prefunctor_obj_of_zigzag (preFiberPrefunctor a) (isPreconnected_zigzag b b')
    refine zigzag_isConnected fun p q => ?_
    -- Every costructured arrow on `pre C G` is assembled from its two components.
    obtain ⟨a₁, b₁, rfl⟩ : ∃ a b, preArrow a b = p :=
      ⟨CostructuredArrow.mk p.hom.base, CostructuredArrow.mk p.hom.fiber, rfl⟩
    obtain ⟨a₂, b₂, rfl⟩ : ∃ a b, preArrow a b = q :=
      ⟨CostructuredArrow.mk q.hom.base, CostructuredArrow.mk q.hom.fiber, rfl⟩
    -- The base components whose whole fiber is linked to `q` form all of `CostructuredArrow G d`.
    let S : Set (CostructuredArrow G d) := {a | ∀ b, Zigzag (preArrow a b) (preArrow a₂ b₂)}
    refine induct_on_objects S (fun b => fiber a₂ b b₂) (fun {a a'} h => ?_) a₁ b₁
    obtain ⟨b⟩ : Nonempty (CostructuredArrow (C.map a.hom).toFunctor x) := inferInstance
    have e := Zigzag.of_hom (toPreTransport h b)
    exact ⟨fun ha b' => (fiber a' b' _).trans (e.symm.trans (ha b)),
      fun ha' b' => (fiber a b' b).trans (e.trans (ha' _))⟩

end CategoryTheory.Grothendieck
