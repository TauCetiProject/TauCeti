/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.CategoryTheory.Sites.Descent.BandFixtures.Constant

/-!
# Checks for the evaluation of intrinsic central sections

On the point site `Discrete PUnit`, the constant pseudofunctor `B(G)` (`Pseudofunctor.constant`)
has as its only fibre the one-object groupoid of a group `G`. The evaluation of an intrinsic
central section of `B(G)` is a central element of `G` (`IntrinsicBandSections.evaluation_comm`).

For `G = S₃` the centre of `S₃` is trivial, so `B(S₃)` has only the identity section (the point
case of the Checks for `BandFixtures.constantSectionsEquiv`), every evaluation is the identity and
the transposition `(0 1)` is not the evaluation of any central section: evaluation onto all six
automorphisms fails without abelian inertia.

For a commutative group `G` every element `g` gives a central section acting by `g`
(`centralSection`, the constant section of a centre unit), and these are all the sections: for
`G = C₃` there are exactly three, and the section of the generator evaluates to the nonidentity
automorphism `Multiplicative.ofAdd 1`.
-/

@[expose] public section

noncomputable section

namespace TauCeti.Examples.BandCenter

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.BandFixtures
  Opposite Bicategory

/-- The constant pseudofunctor `B(G)` on the point site, with fibre the one-object groupoid of
`G`. -/
abbrev pointBG (G : Type) [Group G] : LocallyDiscrete (Discrete PUnit.{1})ᵒᵖ ⥤ᵖ Cat.{0, 0} :=
  constant (Discrete PUnit.{1}) (SingleObj G)

/-- The point of the site. -/
abbrev pt : Discrete PUnit.{1} := ⟨⟨⟩⟩

/-- The object of `B(G)` over the point. -/
abbrev ptObj (G : Type) [Group G] : (pointBG G).obj (.mk (op pt)) :=
  SingleObj.star G

/-- The element of `G` underlying an endomorphism of an object of `B(G)`. -/
abbrev toElem {G : Type} [Group G] {V : Discrete PUnit.{1}} {x : (pointBG G).obj (.mk (op V))}
    (f : x ⟶ x) : G :=
  f

/-- An evaluation of a central section of `B(G)` commutes with every element of `G`. -/
theorem mul_evaluation_comm {G : Type} [Group G] {V : Discrete PUnit.{1}} (a : V ⟶ pt)
    (x : (pointBG G).obj (.mk (op V))) (s : IntrinsicBandSections (pointBG G) pt) (h : G) :
    toElem (IntrinsicBandSections.evaluation a x s).asIso.hom * h =
      h * toElem (IntrinsicBandSections.evaluation a x s).asIso.hom :=
  -- The fibre of `pointBG G` is `SingleObj G` by definition, so `h : G` is an endomorphism of `x`
  -- and composition is reversed multiplication (`SingleObj.comp_as_mul`).
  (SingleObj.comp_as_mul G _ _).symm.trans
    ((IntrinsicBandSections.evaluation_comm a x s h).trans (SingleObj.comp_as_mul G _ _))

/-- **The `B(S₃)` Check, sections.** `B(S₃)` has only the identity central section over the point,
rather than one for each of the six automorphisms of its object: the point-site case of the
`B(S₃)` Check for `BandFixtures.constantSectionsEquiv`. -/
instance : Subsingleton (IntrinsicBandSections (pointBG (Equiv.Perm (Fin 3))) pt) :=
  inferInstance

/-- **The `B(S₃)` Check, trivial centre.** Every evaluation of a central section of `B(S₃)` is the
identity, since `B(S₃)` has only the identity central section. -/
theorem evaluation_eq_one {V : Discrete PUnit.{1}} (a : V ⟶ pt)
    (x : (pointBG (Equiv.Perm (Fin 3))).obj (.mk (op V)))
    (s : IntrinsicBandSections (pointBG (Equiv.Perm (Fin 3))) pt) :
    IntrinsicBandSections.evaluation a x s = 1 := by
  rw [Subsingleton.elim s 1, map_one]

/-- **The `B(S₃)` Check, transposition.** The transposition `(0 1)` is not the evaluation of any
central section of `B(S₃)`. -/
theorem evaluation_ne_swap {V : Discrete PUnit.{1}} (a : V ⟶ pt)
    (x : (pointBG (Equiv.Perm (Fin 3))).obj (.mk (op V)))
    (s : IntrinsicBandSections (pointBG (Equiv.Perm (Fin 3))) pt) :
    toElem (IntrinsicBandSections.evaluation a x s).asIso.hom ≠ Equiv.swap 0 1 := by
  rw [evaluation_eq_one, Aut.one_asIso, Iso.refl_hom]
  -- The identity of `x` in the fibre `SingleObj (Equiv.Perm (Fin 3))` is `1`
  -- (`SingleObj.id_as_one`).
  exact (SingleObj.id_as_one _ _).trans_ne (by decide : (1 : Equiv.Perm (Fin 3)) ≠ Equiv.swap 0 1)

/-! ### `B(G)` for a commutative group -/

/-- For a commutative group `G`, the unit of the centre of the one-object groupoid of `G` acting
by `g` on its object. -/
def centerUnit {G : Type} [CommGroup G] (g : G) : (CatCenter (SingleObj G))ˣ :=
  (Aut.unitsEndEquivAut (𝟭 (SingleObj G))).symm <| .of <|
    NatIso.ofComponents (fun x ↦ asIso (g : x ⟶ x)) fun f ↦ by
      simp only [Functor.id_map, asIso_hom, SingleObj.comp_as_mul]
      exact mul_comm _ _

/-- The component of `centerUnit g` at an object of `B(G)` is `g`. -/
@[simp]
theorem toElem_centerUnit_app {G : Type} [CommGroup G] (g : G) {V : Discrete PUnit.{1}}
    (x : (pointBG G).obj (.mk (op V))) :
    toElem ((centerUnit g).val.app x) = g :=
  -- `Aut.unitsEndEquivAut.symm` keeps the underlying natural transformation, whose component
  -- built by `NatIso.ofComponents` is `g`.
  rfl

/-- For a commutative group `G`, the central section of `B(G)` over the point acting by `g`
on every fibre. -/
def centralSection {G : Type} [CommGroup G] (g : G) : IntrinsicBandSections (pointBG G) pt :=
  constantSection pt (centerUnit g)

/-- The components of `centralSection g` are `centerUnit g`. -/
@[simp]
theorem val_centralSection {G : Type} [CommGroup G] (g : G) (V : Discrete PUnit.{1})
    (a : V ⟶ pt) : (centralSection g).val V a = centerUnit g :=
  val_constantSection pt _ V a

/-- Evaluating `centralSection g` gives `g`. -/
theorem toElem_evaluation_centralSection {G : Type} [CommGroup G] (g : G)
    {V : Discrete PUnit.{1}} (a : V ⟶ pt) (x : (pointBG G).obj (.mk (op V))) :
    toElem (IntrinsicBandSections.evaluation a x (centralSection g)).asIso.hom = g := by
  simp

/-- For a commutative group `G`, every central section of `B(G)` over the point is
`centralSection g` for the evaluation `g` of the section at the object over the point. -/
theorem centralSection_toElem_evaluation {G : Type} [CommGroup G]
    (s : IntrinsicBandSections (pointBG G) pt) :
    centralSection (toElem (IntrinsicBandSections.evaluation (𝟙 pt)
      (ptObj G) s).asIso.hom) = s := by
  refine IntrinsicBandSections.ext fun V a x ↦ ?_
  obtain rfl : V = pt := Subsingleton.elim _ _
  obtain rfl : a = 𝟙 pt := Subsingleton.elim _ _
  -- The fibre over the point is `SingleObj G`, which has a single object.
  obtain rfl : x = ptObj G := Subsingleton.elim (α := SingleObj G) _ _
  simp

/-- For a commutative group `G`, the central sections of `B(G)` over the point are the elements
of `G`. -/
def centralSectionEquiv (G : Type) [CommGroup G] : G ≃ IntrinsicBandSections (pointBG G) pt where
  toFun := centralSection
  invFun s := toElem (IntrinsicBandSections.evaluation (𝟙 pt)
    (ptObj G) s).asIso.hom
  left_inv g := toElem_evaluation_centralSection g (𝟙 pt) _
  right_inv s := centralSection_toElem_evaluation s

/-- **The `B(C₃)` Check, count.** `B(C₃)` has exactly three central sections over the point. -/
theorem natCard_intrinsicBandSections_C₃ :
    Nat.card (IntrinsicBandSections (pointBG (Multiplicative (ZMod 3))) pt) = 3 := by
  rw [← Nat.card_congr (centralSectionEquiv _), Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **The `B(C₃)` Check, generator.** The evaluation of the central section of the generator of
`C₃` is the nonidentity automorphism `Multiplicative.ofAdd 1` of the object. -/
example :
    toElem (IntrinsicBandSections.evaluation (𝟙 pt)
      (ptObj (Multiplicative (ZMod 3)))
      (centralSection (Multiplicative.ofAdd (1 : ZMod 3)))).asIso.hom = Multiplicative.ofAdd 1 ∧
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 3)) ≠ 1 :=
  ⟨toElem_evaluation_centralSection _ _ _, by decide⟩

end TauCeti.Examples.BandCenter
