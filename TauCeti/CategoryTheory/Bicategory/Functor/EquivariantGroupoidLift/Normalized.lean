/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Normalized transport data of equivariant groupoid lifts

Let `Γ` be a category and `H` a monoid, and let `actions p` be a categorical action of `H` on a
category `C p` for each `p : Γ`. An `EquivariantGroupoidLift` of these actions is a pseudofunctor
`F : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat` whose fibers are identified with the prescribed
actions only up to equivariant equivalence. Its *normalized* form lives on the prescribed fibers
themselves. It consists of transport functors `E_g : C p ⥤ C q`, unit isomorphisms
`E_(𝟙 p) ≅ 𝟭`, composition isomorphisms `E_g ⋙ E_h ≅ E_gh` and isomorphisms
`T_a ⋙ E_g ≅ E_g ⋙ T_a` commuting transport with the actions. They are subject to the
associativity and unit conditions along `Γ` and to the mixed conditions relating the commuting
isomorphisms to the comparisons of transport along `Γ` and of the actions along `H`. This file
compares the two forms in both directions.

* `TauCeti.EquivariantGroupoidLift.NormalizedTransport`: the type of normalized transport data.
* `TauCeti.EquivariantGroupoidLift.normalizedTransport`: the normalized data of a lift, whose
  transport functors `e_p⁻¹ ⋙ F (g, 1) ⋙ e_q` conjugate the joint functors by the fiber
  comparisons `e_p`.
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.joint`: conversely, normalized data
  assemble into a pseudofunctor out of `LocallyDiscrete (Γ × SingleObj H)` with value `C p` at
  `(p, ⋆)`. It sends `(g, a)` to `T_a ⋙ E_g`, following the factorization
  `(g, a) = (𝟙 p, a) ≫ (g, 1)`. Its composition comparison at `(g, a) ≫ (h, b)` combines the
  comparison `T_(a ≫ b) ≅ T_a ⋙ T_b` of the action, the inverse composition isomorphism of
  transport and the commuting isomorphism `T_b ⋙ E_g ≅ E_g ⋙ T_b`; its coherence is
  `jointComp_associativity`, `jointComp_left_unitality` and `jointComp_right_unitality`.
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.toLift`: the lift with joint pseudofunctor
  `joint` whose fiber comparisons `comparison p` have identity components. Their naturality
  isomorphisms are the unit isomorphisms `E_(𝟙 p) ≅ 𝟭`.
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.toLiftTransportIso`: the transport functors
  of this lift are isomorphic to the given ones.

These constructions concern single lifts and single normalized data; morphisms between them are
not treated here. The composition order follows `Γ × SingleObj H`: in `SingleObj H` the
composite `a ≫ b` is the product `b * a`.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): the families of local categories over
  the groupoid of local Langlands parameters, with their loop group actions.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, arXiv:2002.06055, Chapter 4:
  pseudofunctors and strong transformations.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]

variable (Γ) in
/-- Normalized transport data for a family `actions` of categorical actions of `H` along `Γ`:
transport functors between the prescribed fibers, with unit and composition isomorphisms and
isomorphisms commuting transport with the actions, satisfying the coherence conditions of a
coherent equivariant transport. -/
structure NormalizedTransport (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) where
  /-- The transport functor `E_g : C p ⥤ C q` of an arrow `g : p ⟶ q`. -/
  transport {p q : Γ} (g : p ⟶ q) : fiber actions p ⥤ fiber actions q
  /-- The unit isomorphism `E_(𝟙 p) ≅ 𝟭`. -/
  transportId (p : Γ) : transport (𝟙 p) ≅ 𝟭 (fiber actions p)
  /-- The composition isomorphism `E_g ⋙ E_h ≅ E_gh` for `g ≫ h = gh`. -/
  transportComp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh) :
    transport g ⋙ transport h ≅ transport gh
  /-- The isomorphism `T_a ⋙ E_g ≅ E_g ⋙ T_a` commuting transport with the actions. -/
  transportCommIso {p q : Γ} (g : p ⟶ q) (a : SingleObj.star H ⟶ SingleObj.star H) :
    act actions p a ⋙ transport g ≅ transport g ⋙ act actions q a
  /-- Associativity of the composition isomorphisms. -/
  transportComp_associativity {p q r s : Γ} (f : p ⟶ q) (g : q ⟶ r) (h : r ⟶ s)
    (fg : p ⟶ r) (gh : q ⟶ s) (fgh : p ⟶ s) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (X : fiber actions p) :
    (transport h).map ((transportComp f g fg hfg).hom.app X) ≫
        (transportComp fg h fgh hfgh).hom.app X =
      (transportComp g h gh hgh).hom.app ((transport f).obj X) ≫
        (transportComp f gh fgh hfgh').hom.app X
  /-- Left unitality of the composition isomorphisms. -/
  transportComp_left_unitality {p q : Γ} (g : p ⟶ q) (hg : 𝟙 p ≫ g = g)
    (X : fiber actions p) :
    (transportComp (𝟙 p) g g hg).hom.app X = (transport g).map ((transportId p).hom.app X)
  /-- Right unitality of the composition isomorphisms. -/
  transportComp_right_unitality {p q : Γ} (g : p ⟶ q) (hg : g ≫ 𝟙 q = g)
    (X : fiber actions p) :
    (transportComp g (𝟙 q) g hg).hom.app X = (transportId q).hom.app ((transport g).obj X)
  /-- The commuting isomorphism of `E_gh` is the composite of those of `E_g` and `E_h`. -/
  transportCommIso_comp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh)
    (a : SingleObj.star H ⟶ SingleObj.star H) (X : fiber actions p) :
    (transport h).map ((transportCommIso g a).hom.app X) ≫
        (transportCommIso h a).hom.app ((transport g).obj X) ≫
          (act actions r a).map ((transportComp g h gh hgh).hom.app X) =
      (transportComp g h gh hgh).hom.app ((act actions p a).obj X) ≫
        (transportCommIso gh a).hom.app X
  /-- The commuting isomorphism with `T_ab` is the composite of those with `T_a` and `T_b`. -/
  transportCommIso_actComp {p q : Γ} (g : p ⟶ q)
    (a b ab : SingleObj.star H ⟶ SingleObj.star H) (hab : a ≫ b = ab) (X : fiber actions p) :
    (transport g).map ((actComp actions p a b ab hab).hom.app X) ≫
        (transportCommIso g b).hom.app ((act actions p a).obj X) ≫
          (act actions q b).map ((transportCommIso g a).hom.app X) =
      (transportCommIso g ab).hom.app X ≫
        (actComp actions q a b ab hab).hom.app ((transport g).obj X)
  /-- The commuting isomorphism of `E_(𝟙 p)` is induced by the unit isomorphism. -/
  transportCommIso_id (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (X : fiber actions p) :
    (transportCommIso (𝟙 p) a).hom.app X ≫ (act actions p a).map ((transportId p).hom.app X) =
      (transportId p).hom.app ((act actions p a).obj X)
  /-- The commuting isomorphism with `T_1` is induced by the unit comparisons of the actions. -/
  transportCommIso_actId {p q : Γ} (g : p ⟶ q) (X : fiber actions p) :
    (transportCommIso g (𝟙 (SingleObj.star H))).hom.app X ≫
        (actId actions q).hom.app ((transport g).obj X) =
      (transport g).map ((actId actions p).hom.app X)

variable {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- The normalized transport data of a lift `L`: its transport functors `L.transport g`, with the
unit, composition and commuting isomorphisms `L.transportId`, `L.transportComp` and
`L.transportCommIso`. -/
-- The body is exposed so that the data of `L.normalizedTransport` are definitionally those of `L`,
-- as needed to state `normalizedTransport_transportId` and its siblings.
@[expose] noncomputable def normalizedTransport (L : EquivariantGroupoidLift Γ actions) :
    NormalizedTransport Γ actions where
  transport := L.transport
  transportId := L.transportId
  transportComp g h gh hgh := L.transportComp g h gh hgh
  transportCommIso := L.transportCommIso
  transportComp_associativity f g h fg gh fgh hfg hgh hfgh _ X :=
    L.transportComp_associativity f g h fg gh fgh hfg hgh hfgh X
  transportComp_left_unitality := L.transportComp_left_unitality
  transportComp_right_unitality := L.transportComp_right_unitality
  transportCommIso_comp := L.transportCommIso_comp
  transportCommIso_actComp := L.transportCommIso_actComp
  transportCommIso_id := L.transportCommIso_id
  transportCommIso_actId := L.transportCommIso_actId

section normalizedTransport

variable (L : EquivariantGroupoidLift Γ actions)

@[simp]
lemma normalizedTransport_transport {p q : Γ} (g : p ⟶ q) :
    L.normalizedTransport.transport g = L.transport g :=
  (rfl)

@[simp]
lemma normalizedTransport_transportId (p : Γ) :
    L.normalizedTransport.transportId p = L.transportId p :=
  (rfl)

@[simp]
lemma normalizedTransport_transportComp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) :
    L.normalizedTransport.transportComp g h gh hgh = L.transportComp g h gh hgh :=
  (rfl)

@[simp]
lemma normalizedTransport_transportCommIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) :
    L.normalizedTransport.transportCommIso g a = L.transportCommIso g a :=
  (rfl)

end normalizedTransport

namespace NormalizedTransport

variable (N : NormalizedTransport Γ actions)

/-- The functor `T_a ⋙ E_g` attached to an arrow `(g, a)` of `Γ × SingleObj H`. -/
abbrev jointFunctor {X Y : Γ × SingleObj H} (f : X ⟶ Y) : fiber actions X.1 ⥤ fiber actions Y.1 :=
  act actions X.1 f.2 ⋙ N.transport f.1

/-- The unit comparison `T_1 ⋙ E_(𝟙 p) ≅ 𝟭` of the joint functors, built from the unit
comparison of the action and the unit isomorphism of transport. -/
noncomputable def jointId (X : Γ × SingleObj H) : N.jointFunctor (𝟙 X) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (actId actions X.1) (N.transport (𝟙 X.1)) ≪≫ Functor.leftUnitor _ ≪≫
    N.transportId X.1

/-- The composition comparison `T_(a ≫ b) ⋙ E_gh ≅ (T_a ⋙ E_g) ⋙ (T_b ⋙ E_h)` of the joint
functors at a factorization `(g, a) ≫ (h, b) = (gh, a ≫ b)`. It combines the composition
comparison of the action, the inverse composition isomorphism of transport and the commuting
isomorphism `T_b ⋙ E_g ≅ E_g ⋙ T_b`. -/
noncomputable def jointComp {X Y Z : Γ × SingleObj H} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) : N.jointFunctor fg ≅ N.jointFunctor f ⋙ N.jointFunctor g :=
  Functor.isoWhiskerRight (actComp actions X.1 f.2 g.2 fg.2 (congrArg Prod.snd hfg))
      (N.transport fg.1) ≪≫
    Functor.isoWhiskerLeft (act actions X.1 f.2 ⋙ act actions X.1 g.2)
      (N.transportComp f.1 g.1 fg.1 (congrArg Prod.fst hfg)).symm ≪≫
    Functor.isoWhiskerLeft (act actions X.1 f.2)
      (Functor.isoWhiskerRight (N.transportCommIso f.1 g.2) (N.transport g.1))

@[simp]
lemma jointId_hom_app (X : Γ × SingleObj H) (x : fiber actions X.1) :
    (N.jointId X).hom.app x =
      (N.transport (𝟙 X.1)).map ((actId actions X.1).hom.app x) ≫
        (N.transportId X.1).hom.app x := by
  simp [jointId]

@[simp]
lemma jointComp_hom_app {X Y Z : Γ × SingleObj H} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (x : fiber actions X.1) :
    (N.jointComp f g fg hfg).hom.app x =
      (N.transport fg.1).map
          ((actComp actions X.1 f.2 g.2 fg.2 (congrArg Prod.snd hfg)).hom.app x) ≫
        (N.transportComp f.1 g.1 fg.1 (congrArg Prod.fst hfg)).inv.app
          ((act actions X.1 g.2).obj ((act actions X.1 f.2).obj x)) ≫
        (N.transport g.1).map
          ((N.transportCommIso f.1 g.2).hom.app ((act actions X.1 f.2).obj x)) := by
  simp [jointComp]

attribute [reassoc] transportComp_associativity transportCommIso_comp transportCommIso_actComp
  transportCommIso_id transportCommIso_actId

/-- Associativity of the inverse composition isomorphisms of transport. -/
@[reassoc]
lemma transportComp_inv_associativity {p q r s : Γ} (f : p ⟶ q) (g : q ⟶ r) (h : r ⟶ s)
    (fg : p ⟶ r) (gh : q ⟶ s) (fgh : p ⟶ s) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (X : fiber actions p) :
    (N.transportComp fg h fgh hfgh).inv.app X ≫
        (N.transport h).map ((N.transportComp f g fg hfg).inv.app X) =
      (N.transportComp f gh fgh hfgh').inv.app X ≫
        (N.transportComp g h gh hgh).inv.app ((N.transport f).obj X) := by
  have := congrArg Iso.inv (Iso.ext (N.transportComp_associativity f g h fg gh fgh hfg hgh hfgh
    hfgh' X) : (N.transport h).mapIso ((N.transportComp f g fg hfg).app X) ≪≫
      (N.transportComp fg h fgh hfgh).app X =
        (N.transportComp g h gh hgh).app ((N.transport f).obj X) ≪≫
          (N.transportComp f gh fgh hfgh').app X)
  simpa using this

/-- The commuting isomorphism of `E_gh`, followed by the inverse composition isomorphism, is the
inverse composition isomorphism followed by the commuting isomorphisms of `E_g` and `E_h`. -/
@[reassoc]
lemma transportCommIso_comp_inv {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) (a : SingleObj.star H ⟶ SingleObj.star H) (X : fiber actions p) :
    (N.transportCommIso gh a).hom.app X ≫
        (act actions r a).map ((N.transportComp g h gh hgh).inv.app X) =
      (N.transportComp g h gh hgh).inv.app ((act actions p a).obj X) ≫
        (N.transport h).map ((N.transportCommIso g a).hom.app X) ≫
          (N.transportCommIso h a).hom.app ((N.transport g).obj X) := by
  rw [← cancel_epi ((N.transportComp g h gh hgh).hom.app _), ← N.transportCommIso_comp_assoc,
    Iso.hom_inv_id_app_assoc]
  simp [← Functor.map_comp]

/-- Associativity of the composition comparisons of the joint functors, for arbitrary composites
`fg`, `gh` and `fgh`. -/
lemma jointComp_associativity {X Y Z W : Γ × SingleObj H} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (x : fiber actions X.1) :
    (N.jointComp fg h fgh hfgh).hom.app x ≫
        (N.jointFunctor h).map ((N.jointComp f g fg hfg).hom.app x) =
      (N.jointComp f gh fgh hfgh').hom.app x ≫
        (N.jointComp g h gh hgh).hom.app ((N.jointFunctor f).obj x) := by
  simp only [jointComp_hom_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  -- Step 1: commute `κ(fg, c)` past `T_c (E_fg α(a, b))`.
  have n1 := (N.transportCommIso fg.1 h.2).hom.naturality
    ((actComp actions X.1 f.2 g.2 fg.2 (congrArg Prod.snd hfg)).hom.app x)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1
  rw [← Functor.map_comp_assoc (N.transport h.1)
    ((N.transportCommIso fg.1 h.2).hom.app _), ← n1, Functor.map_comp_assoc]
  -- Step 2: commute `μ(fg, h)⁻¹` past `E_h (E_fg (T_c α(a, b)))`.
  have n2 := (N.transportComp fg.1 h.1 fgh.1 (congrArg Prod.fst hfgh)).inv.naturality
    ((act actions X.1 h.2).map
      ((actComp actions X.1 f.2 g.2 fg.2 (congrArg Prod.snd hfg)).hom.app x))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n2
  rw [← reassoc_of% n2]
  -- Step 3: associativity of the action.
  rw [← Functor.map_comp_assoc, actComp_associativity X.1 f.2 g.2 h.2 fg.2 gh.2 fgh.2
    (congrArg Prod.snd hfg) (congrArg Prod.snd hgh) (congrArg Prod.snd hfgh)
    (congrArg Prod.snd hfgh'), Functor.map_comp_assoc]
  congr 1
  dsimp only [jointFunctor, Functor.comp_obj]
  -- Step 4: mixed coherence of `κ(f, -)` with the composition of `b` and `c`.
  rw [← Functor.map_comp_assoc (N.transport gh.1) ((N.transportCommIso f.1 gh.2).hom.app _),
    ← N.transportCommIso_actComp f.1 g.2 h.2 gh.2 (congrArg Prod.snd hgh), Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  -- Step 5: commute `μ(f, gh)⁻¹` past `E_gh (E_f α(b, c))`.
  have n3 := (N.transportComp f.1 gh.1 fgh.1 (congrArg Prod.fst hfgh')).inv.naturality
    ((actComp actions X.1 g.2 h.2 gh.2 (congrArg Prod.snd hgh)).hom.app
      ((act actions X.1 f.2).obj x))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n3
  rw [← reassoc_of% n3]
  congr 1
  -- Step 6: commute `μ(g, h)⁻¹` past `E_gh (T_c κ(f, b))`.
  have n4 := (N.transportComp g.1 h.1 gh.1 (congrArg Prod.fst hgh)).inv.naturality
    ((act actions Y.1 h.2).map ((N.transportCommIso f.1 g.2).hom.app ((act actions X.1 f.2).obj x)))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n4
  rw [reassoc_of% n4]
  -- Step 7: commute `κ(g, c)` past `E_g (T_c κ(f, b))`.
  have n5 := (N.transportCommIso g.1 h.2).hom.naturality
    ((N.transportCommIso f.1 g.2).hom.app ((act actions X.1 f.2).obj x))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n5
  rw [← Functor.map_comp (N.transport h.1) ((N.transport g.1).map ((act actions Y.1 h.2).map
    ((N.transportCommIso f.1 g.2).hom.app ((act actions X.1 f.2).obj x)))), n5, Functor.map_comp]
  -- Step 8: mixed coherence of `κ(-, c)` with the composition of `f` and `g`.
  rw [← Functor.map_comp_assoc (N.transport h.1) ((N.transportCommIso fg.1 h.2).hom.app _),
    N.transportCommIso_comp_inv f.1 g.1 fg.1 (congrArg Prod.fst hfg) h.2, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  -- Step 9: associativity of the composition isomorphisms of transport.
  rw [N.transportComp_inv_associativity_assoc f.1 g.1 h.1 fg.1 gh.1 fgh.1 (congrArg Prod.fst hfg)
    (congrArg Prod.fst hgh) (congrArg Prod.fst hfgh) (congrArg Prod.fst hfgh')]
  -- Step 10: commute `μ(g, h)⁻¹` past `E_h (E_g κ(f, c))`.
  have n6 := (N.transportComp g.1 h.1 gh.1 (congrArg Prod.fst hgh)).inv.naturality
    ((N.transportCommIso f.1 h.2).hom.app ((act actions X.1 g.2).obj ((act actions X.1 f.2).obj x)))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n6
  rw [reassoc_of% n6]

/-- Left unitality of the composition comparisons of the joint functors. -/
lemma jointComp_left_unitality {X Y : Γ × SingleObj H} (f : X ⟶ Y) (hf : 𝟙 X ≫ f = f)
    (x : fiber actions X.1) :
    (N.jointComp (𝟙 X) f f hf).hom.app x ≫ (N.jointFunctor f).map ((N.jointId X).hom.app x) =
      𝟙 _ := by
  obtain ⟨p, s⟩ := X
  obtain rfl : s = SingleObj.star H := rfl
  simp only [jointComp_hom_app, jointId_hom_app, Functor.comp_map, Functor.map_comp,
    Category.assoc, prod_id_fst, prod_id_snd]
  have n1 := (N.transportCommIso (𝟙 p) f.2).hom.naturality ((actId actions p).hom.app x)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at n1
  rw [← Functor.map_comp_assoc (N.transport f.1) ((N.transportCommIso (𝟙 p) f.2).hom.app _),
    ← n1, Functor.map_comp_assoc, ← Functor.map_comp (N.transport f.1)
      ((N.transportCommIso (𝟙 p) f.2).hom.app x), N.transportCommIso_id]
  have n2 := (N.transportComp (𝟙 p) f.1 f.1 (congrArg Prod.fst hf)).inv.naturality
    ((act actions p f.2).map ((actId actions p).hom.app x))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n2
  rw [← reassoc_of% n2, ← N.transportComp_left_unitality f.1 (congrArg Prod.fst hf),
    Iso.inv_hom_id_app, Category.comp_id, ← Functor.map_comp, actComp_left_unitality]
  exact (N.transport f.1).map_id _

/-- Right unitality of the composition comparisons of the joint functors. -/
lemma jointComp_right_unitality {X Y : Γ × SingleObj H} (f : X ⟶ Y) (hf : f ≫ 𝟙 Y = f)
    (x : fiber actions X.1) :
    (N.jointComp f (𝟙 Y) f hf).hom.app x ≫ (N.jointId Y).hom.app ((N.jointFunctor f).obj x) =
      𝟙 _ := by
  obtain ⟨q, s⟩ := Y
  obtain rfl : s = SingleObj.star H := rfl
  simp only [jointComp_hom_app, jointId_hom_app, Category.assoc, prod_id_fst, prod_id_snd]
  dsimp only [jointFunctor, Functor.comp_obj]
  rw [← Functor.map_comp_assoc (N.transport (𝟙 q)), N.transportCommIso_actId]
  have n1 := (N.transportComp f.1 (𝟙 q) f.1 (congrArg Prod.fst hf)).inv.naturality
    ((actId actions X.1).hom.app ((act actions X.1 f.2).obj x))
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1
  rw [← reassoc_of% n1, ← N.transportComp_right_unitality f.1 (congrArg Prod.fst hf),
    Iso.inv_hom_id_app, Category.comp_id ((N.transport f.1).map _), ← Functor.map_comp,
    actComp_right_unitality]
  exact (N.transport f.1).map_id _

private lemma jointComp_associativity_eqToHom {X Y Z W : Γ × SingleObj H} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh fgh' : X ⟶ W) (hfg : f ≫ g = fg)
    (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh') (x : fiber actions X.1)
    (hx : (N.jointFunctor fgh).obj x = (N.jointFunctor fgh').obj x) :
    (N.jointComp fg h fgh hfgh).hom.app x ≫
        (N.jointFunctor h).map ((N.jointComp f g fg hfg).hom.app x) ≫
          (N.jointComp g h gh hgh).inv.app ((N.jointFunctor f).obj x) ≫
            (N.jointComp f gh fgh' hfgh').inv.app x = eqToHom hx := by
  obtain rfl : fgh' = fgh := by rw [← hfgh', ← hfgh, ← hfg, ← hgh, Category.assoc]
  rw [← Category.assoc, N.jointComp_associativity f g h fg gh fgh' hfg hgh hfgh hfgh' x]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, eqToHom_refl]

private lemma jointComp_left_unitality_eqToHom {X Y : Γ × SingleObj H} (f k : X ⟶ Y)
    (hk : 𝟙 X ≫ f = k) (x : fiber actions X.1)
    (hx : (N.jointFunctor k).obj x = (N.jointFunctor f).obj x) :
    (N.jointComp (𝟙 X) f k hk).hom.app x ≫ (N.jointFunctor f).map ((N.jointId X).hom.app x) =
      eqToHom hx := by
  obtain rfl : k = f := hk.symm.trans (Category.id_comp f)
  rw [N.jointComp_left_unitality, eqToHom_refl]

private lemma jointComp_right_unitality_eqToHom {X Y : Γ × SingleObj H} (f k : X ⟶ Y)
    (hk : f ≫ 𝟙 Y = k) (x : fiber actions X.1)
    (hx : (N.jointFunctor k).obj x = (N.jointFunctor f).obj x) :
    (N.jointComp f (𝟙 Y) k hk).hom.app x ≫ (N.jointId Y).hom.app ((N.jointFunctor f).obj x) =
      eqToHom hx := by
  obtain rfl : k = f := hk.symm.trans (Category.comp_id f)
  rw [N.jointComp_right_unitality, eqToHom_refl]

/-- The joint pseudofunctor `LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat` of normalized transport
data. Its value at `(p, ⋆)` is the prescribed fiber `C p`, its value at `(g, a)` is
`T_a ⋙ E_g`, and its unit and composition comparisons are `jointId` and `jointComp`. -/
-- The body is exposed so that the value `N.joint.obj X` is definitionally the fiber
-- `fiber actions X.as.1`, as needed to state the component formulas below in terms of its objects.
@[expose] noncomputable def joint : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat.{v, w} :=
  LocallyDiscrete.mkPseudofunctor (fun X ↦ fiber actions X.1)
    (fun f ↦ (N.jointFunctor f).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (N.jointId X))
    (fun f g ↦ Cat.Hom.isoMk (N.jointComp f g (f ≫ g) rfl))
    (fun f g h ↦ by
      ext x
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv,
        Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, NatTrans.toCatHom₂_toNatTrans,
        Functor.toCatHom_toFunctor, Cat.Hom.comp_toFunctor, Functor.comp_obj]
      exact N.jointComp_associativity_eqToHom _ _ _ _ _ _ _ _ _ _ _ _ _)
    (fun f ↦ by
      ext x
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.toNatTrans_comp,
        Cat.whiskerRight_toNatTrans, Cat.leftUnitor_hom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor]
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (N.jointComp_left_unitality_eqToHom _ _ _ _ _))
    (fun f ↦ by
      ext x
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.toNatTrans_comp,
        Cat.whiskerLeft_toNatTrans, Cat.rightUnitor_hom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor]
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (N.jointComp_right_unitality_eqToHom _ _ _ _ _))

@[simp]
lemma joint_obj (X : LocallyDiscrete (Γ × SingleObj H)) : N.joint.obj X = fiber actions X.as.1 :=
  rfl

@[simp]
lemma joint_map_toFunctor {X Y : LocallyDiscrete (Γ × SingleObj H)} (f : X ⟶ Y) :
    (N.joint.map f).toFunctor = N.jointFunctor f.as :=
  rfl

@[simp]
lemma joint_mapId_hom_app (X : LocallyDiscrete (Γ × SingleObj H)) (x : fiber actions X.as.1) :
    (N.joint.mapId X).hom.toNatTrans.app x = (N.jointId X.as).hom.app x :=
  rfl

@[simp]
lemma joint_mapComp_hom_app {X Y Z : LocallyDiscrete (Γ × SingleObj H)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : fiber actions X.as.1) :
    (N.joint.mapComp f g).hom.toNatTrans.app x =
      (N.jointComp f.as g.as (f ≫ g).as rfl).hom.app x :=
  rfl

/-- A composition comparison of `N.joint` preceded by a `2`-cell of the locally discrete source
is the composition comparison `jointComp` at the corresponding factorization. -/
lemma joint_map₂_comp_mapComp_hom_app {X Y Z : LocallyDiscrete (Γ × SingleObj H)} (u : X ⟶ Y)
    (v : Y ⟶ Z) (w : X ⟶ Z) (θ : w ⟶ u ≫ v) (x : fiber actions X.as.1) :
    (N.joint.map₂ θ).toNatTrans.app x ≫ (N.joint.mapComp u v).hom.toNatTrans.app x =
      (N.jointComp u.as v.as w.as
        (by obtain rfl := LocallyDiscrete.eq_of_hom θ; rfl)).hom.app x := by
  obtain rfl := LocallyDiscrete.eq_of_hom θ
  rw [Subsingleton.elim θ (𝟙 _), PrelaxFunctor.map₂_id]
  -- The composition comparison of `joint` at `u` and `v` is `jointComp` by definition.
  exact Category.id_comp _

/-- The comparison of the restriction of `N.joint` to the fiber `{p} × SingleObj H` with the
prescribed action at `p`. Its component is the identity of `C p`, and its naturality
isomorphism at `a` is `T_a ⋙ E_(𝟙 p) ≅ T_a`, induced by the unit isomorphism of transport. -/
-- The body is exposed so that the components of the comparison are definitionally identities, as
-- needed to state the formula `comparison_naturality_hom_app` for its naturality isomorphisms.
@[expose] noncomputable def comparison (p : Γ) :
    Pseudofunctor.StrongTrans (N.joint.restrictFiber p) (actions p) where
  app _ := 𝟙 (fiber actions p)
  naturality {a b} f :=
    Cat.Hom.isoMk (Functor.isoWhiskerLeft (act actions p f.as) (N.transportId p))
  -- The component `𝟙 (fiber actions p)` has type `fiber actions p ⟶ fiber actions p`, while the
  -- values of the two pseudofunctors at `a` are only definitionally `fiber actions p`, so the
  -- component lemmas of `Cat` do not apply. The coherence conditions are instead stated
  -- componentwise and closed by definitional unfolding of the components.
  naturality_naturality {a b f g} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _)]
    simp only [PrelaxFunctor.map₂_id]
    have h (x : fiber actions p) :
        𝟙 _ ≫ (N.transportId p).hom.app ((act actions p f.as).obj x) =
          (N.transportId p).hom.app ((act actions p f.as).obj x) ≫ 𝟙 _ := by
      simp
    ext x
    exact h x
  naturality_id a := by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    have h (x : fiber actions p) :
        (N.transportId p).hom.app ((act actions p (𝟙 _)).obj x) ≫
            ((actions p).mapId ⟨SingleObj.star H⟩).hom.toNatTrans.app x =
          (𝟙 _ ≫ (N.jointId (p, SingleObj.star H)).hom.app x) ≫ 𝟙 _ ≫ 𝟙 _ := by
      rw [jointId_hom_app, actId_hom_app]
      simp only [Quiver.Hom.id_toLoc, Pseudofunctor.mapId'_eq_mapId, Category.id_comp,
        Category.comp_id]
      exact ((N.transportId p).hom.naturality _).symm
    ext x
    exact h x
  naturality_comp {a b c} f g := by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : b = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : c = ⟨SingleObj.star H⟩ := rfl
    have h (x : fiber actions p) :
        (N.transportId p).hom.app ((act actions p (f ≫ g).as).obj x) ≫
            (actComp actions p f.as g.as (f ≫ g).as rfl).hom.app x =
          (N.jointComp (𝟙 p ×ₘ f.as) (𝟙 p ×ₘ g.as) (𝟙 p ×ₘ (f ≫ g).as) (by simp)).hom.app x ≫
            𝟙 _ ≫ (N.transportId p).hom.app
              ((act actions p g.as).obj ((N.transport (𝟙 p)).obj ((act actions p f.as).obj x))) ≫
            𝟙 _ ≫
            (act actions p g.as).map ((N.transportId p).hom.app ((act actions p f.as).obj x)) ≫
            𝟙 _ := by
      rw [jointComp_hom_app]
      dsimp only
      simp only [Category.id_comp, Category.assoc]
      have n1 := (N.transportId p).hom.naturality
        ((N.transportCommIso (𝟙 p) g.as).hom.app ((act actions p f.as).obj x))
      have n2 := (N.transportId p).hom.naturality
        ((actComp actions p f.as g.as (f ≫ g).as rfl).hom.app x)
      dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map] at n1 n2
      rw [reassoc_of% n1, N.transportCommIso_id_assoc,
        ← N.transportComp_right_unitality (𝟙 p) (Category.comp_id _), Iso.inv_hom_id_app_assoc]
      exact n2.symm.trans (congrArg (_ ≫ ·) (Category.comp_id _).symm)
    have hα (x : fiber actions p) : ((actions p).mapComp f g).hom.toNatTrans.app x =
        (actComp actions p f.as g.as (f ≫ g).as rfl).hom.app x := by
      rw [actComp_hom_app]
      exact congrArg (fun e ↦ e.hom.toNatTrans.app x) ((actions p).mapComp'_eq_mapComp f g).symm
    ext x
    exact ((congrArg (_ ≫ ·) (hα x)).trans (h x)).trans (congrArg (· ≫ _)
      (N.joint_map₂_comp_mapComp_hom_app _ _ _
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.mapComp f g).hom x).symm)

@[simp]
lemma comparison_app (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    (N.comparison p).app a = 𝟙 (fiber actions p) :=
  rfl

@[simp]
lemma comparison_naturality_hom_app (p : Γ) {a b : LocallyDiscrete (SingleObj H)} (f : a ⟶ b)
    (x : fiber actions p) :
    ((N.comparison p).naturality f).hom.toNatTrans.app x =
      (N.transportId p).hom.app ((act actions p f.as).obj x) :=
  rfl

/-- The coherent equivariant lift generated by normalized transport data: its joint pseudofunctor
is `N.joint` and its fiber comparisons `N.comparison p` have identity components. -/
-- The body is exposed so that the joint pseudofunctor and the fiber comparisons of the lift are
-- definitionally `N.joint` and `N.comparison`, as stated by `toLift_joint` and `toLift_comparison`.
@[expose] noncomputable def toLift : EquivariantGroupoidLift Γ actions where
  joint := N.joint
  comparison := N.comparison
  isEquivalence_comparison p := inferInstanceAs (𝟭 (fiber actions p)).IsEquivalence

@[simp]
lemma toLift_joint : N.toLift.joint = N.joint :=
  rfl

@[simp]
lemma toLift_comparison (p : Γ) : N.toLift.comparison p = N.comparison p :=
  rfl

/-- The transport functor of `N.toLift` along `g` is isomorphic to the transport functor `E_g` of
`N`. The isomorphism removes the chosen inverse of the identity fiber comparison and the unit
comparison `T_1 ≅ 𝟭` of the action. -/
noncomputable def toLiftTransportIso {p q : Γ} (g : p ⟶ q) :
    N.toLift.transport g ≅ N.transport g :=
  Functor.isoWhiskerRight (N.toLift.fiberEquivalence p).counitIso
      (act actions p (𝟙 _) ⋙ N.transport g) ≪≫ Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerRight (actId actions p) (N.transport g) ≪≫ Functor.leftUnitor _


end NormalizedTransport

end TauCeti.EquivariantGroupoidLift
