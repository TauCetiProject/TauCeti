/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Rigidified line bundles

Let `s : T ⟶ Y` be a morphism of schemes. A line bundle on `Y` *rigidified along `s`* is a line
bundle `L` on `Y` together with a trivialization `s^* L ≅ 𝒪_T` of its pullback along `s`. Two
rigidified line bundles are isomorphic when some isomorphism of the underlying line bundles carries
one trivialization to the other.

Rigidified line bundles pull back along commutative squares
```
T' --s'--> Y'
|          |
g          h
v          v
T  --s-->  Y
```
by pulling the line bundle back along `h` and the trivialization back along `g`. On isomorphism
classes this pullback is compatible with identity squares and with stacking squares. Taking for
`s` the base changes of a section of a morphism `X ⟶ S` to the schemes over `S`, the classes
therefore form a functor of the scheme over `S`: the rigidified Picard functor
(`TauCeti.AlgebraicGeometry.rigidifiedPicardFunctor`).

Unlike isomorphism classes of line bundles, isomorphism classes of rigidified line bundles remember
the trivialization up to the automorphisms of `L`; an automorphism of `L` given by a unit `u` of
`Γ(Y, 𝒪_Y)` rescales the trivialization by the pullback of `u` along `s`.

## Main declarations

* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle s`: line bundles on `Y` rigidified along `s`;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundle.pullback`: pullback along a commutative square;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass s`: isomorphism classes of rigidified line
  bundles, with `RigidifiedLineBundleClass.mk_eq_mk_iff` characterizing equality of classes;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass.pullback`, with the functoriality
  statements `RigidifiedLineBundleClass.pullback_id` and `RigidifiedLineBundleClass.pullback_comp`;
* `TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass.toLineBundleClass`: forgetting the
  trivialization, compatibly with pullback (`toLineBundleClass_pullback`).

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1 (rigidified line bundles).
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u v

noncomputable section

variable {T Y : Scheme.{u}}

/-- A line bundle on `Y` rigidified along a morphism `s : T ⟶ Y`: a line bundle `L` on `Y`
together with a trivialization `s^* L ≅ 𝒪_T` of its pullback along `s`. -/
structure RigidifiedLineBundle (s : T ⟶ Y) where
  /-- The underlying line bundle on `Y`. -/
  lineBundle : InvertibleSheaf Y
  /-- The trivialization of the pullback of the line bundle along `s`. -/
  rigidification : (Scheme.Modules.pullback s).obj lineBundle.obj ≅ 𝟙_ T.Modules

namespace RigidifiedLineBundle

variable {s : T ⟶ Y}

/-- Isomorphism of rigidified line bundles: an isomorphism of the underlying line bundles whose
pullback along `s` carries the first trivialization to the second. -/
def setoid (s : T ⟶ Y) : Setoid (RigidifiedLineBundle s) where
  r P Q := ∃ e : P.lineBundle.obj ≅ Q.lineBundle.obj,
    (Scheme.Modules.pullback s).map e.hom ≫ Q.rigidification.hom = P.rigidification.hom
  iseqv :=
    { refl _ := ⟨Iso.refl _, by simp⟩
      symm := fun ⟨e, he⟩ ↦ ⟨e.symm, by simp [← he]⟩
      trans := fun ⟨e, he⟩ ⟨e', he'⟩ ↦ ⟨e ≪≫ e', by simp [he', he]⟩ }

variable {T' Y' : Scheme.{u}} {s' : T' ⟶ Y'} {h : Y' ⟶ Y} {g : T' ⟶ T}

/-- For a commutative square `s' ≫ h = g ≫ s`, the trivialization `s'^* h^* L ≅ 𝒪_{T'}` obtained
from a trivialization `α : s^* L ≅ 𝒪_T`: identify `s'^* h^* L` with `g^* s^* L` through the
composition isomorphisms of pullback, and pull `α` back along `g`. -/
def pullbackRigidification (w : s' ≫ h = g ≫ s) (L : Y.Modules)
    (α : (Scheme.Modules.pullback s).obj L ≅ 𝟙_ T.Modules) :
    (Scheme.Modules.pullback s').obj ((Scheme.Modules.pullback h).obj L) ≅ 𝟙_ T'.Modules :=
  (Scheme.Modules.pullbackComp s' h).app L ≪≫ (Scheme.Modules.pullbackCongr w).app L ≪≫
    ((Scheme.Modules.pullbackComp g s).app L).symm ≪≫ (Scheme.Modules.pullback g).mapIso α ≪≫
      Scheme.Modules.pullbackObjUnitIso g

/-- The trivializations obtained by pullback are natural in the line bundle: a morphism `e`
carrying `α` to `β` pulls back to a morphism carrying the pulled-back trivializations to each
other. -/
lemma pullbackRigidification_naturality (w : s' ≫ h = g ≫ s) {L M : Y.Modules} (e : L ⟶ M)
    (α : (Scheme.Modules.pullback s).obj L ≅ 𝟙_ T.Modules)
    (β : (Scheme.Modules.pullback s).obj M ≅ 𝟙_ T.Modules)
    (he : (Scheme.Modules.pullback s).map e ≫ β.hom = α.hom) :
    (Scheme.Modules.pullback s').map ((Scheme.Modules.pullback h).map e) ≫
      (pullbackRigidification w M β).hom = (pullbackRigidification w L α).hom := by
  simp only [pullbackRigidification, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, ← he, Functor.map_comp]
  rw [← Functor.comp_map, NatTrans.naturality_assoc, NatTrans.naturality_assoc,
    NatTrans.naturality_assoc, Functor.comp_map, Category.assoc]

/-- Pulling a trivialization back along the identity square recovers it, through the identity
isomorphism `𝟙^* L ≅ L`. -/
lemma pullbackRigidification_id (w : s ≫ 𝟙 Y = 𝟙 T ≫ s) (L : Y.Modules)
    (α : (Scheme.Modules.pullback s).obj L ≅ 𝟙_ T.Modules) :
    (Scheme.Modules.pullback s).map ((Scheme.Modules.pullbackId Y).hom.app L) ≫ α.hom =
      (pullbackRigidification w L α).hom := by
  simp only [pullbackRigidification, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Scheme.Modules.pullbackObjUnitIso_id]
  rw [← Iso.hom_inv_id_app_assoc (Scheme.Modules.pullbackComp s (𝟙 Y)) L
      ((Scheme.Modules.pullback s).map ((Scheme.Modules.pullbackId Y).hom.app L) ≫ α.hom),
    Scheme.Modules.pseudofunctor_left_unitality_app_assoc,
    (Scheme.Modules.pullbackId T).hom.naturality α.hom, Functor.id_map,
    Scheme.Modules.pseudofunctor_right_unitality_app_assoc]
  simp [Scheme.Modules.pullbackCongr]

/-- Pulling a trivialization back along two stacked squares agrees with pulling it back along the
composite square, through the composition isomorphism `h'^* h^* L ≅ (h' ≫ h)^* L`. -/
lemma pullbackRigidification_comp {T'' Y'' : Scheme.{u}} {s'' : T'' ⟶ Y''} {h' : Y'' ⟶ Y'}
    {g' : T'' ⟶ T'} (w : s' ≫ h = g ≫ s) (w' : s'' ≫ h' = g' ≫ s')
    (w'' : s'' ≫ h' ≫ h = (g' ≫ g) ≫ s) (L : Y.Modules)
    (α : (Scheme.Modules.pullback s).obj L ≅ 𝟙_ T.Modules) :
    (Scheme.Modules.pullback s'').map ((Scheme.Modules.pullbackComp h' h).hom.app L) ≫
        (pullbackRigidification w'' L α).hom =
      (pullbackRigidification w' ((Scheme.Modules.pullback h).obj L)
        (pullbackRigidification w L α)).hom := by
  simp only [pullbackRigidification, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  -- Split `𝒪` along `g' ≫ g`, move `α` past the composition isomorphism, and then match the
  -- remaining comparisons of iterated pullbacks, which are determined up to `eqToHom`.
  rw [← Scheme.Modules.pullbackObjUnitIso_comp g' g, ← Functor.comp_map,
    NatTrans.naturality_assoc,
    Scheme.Modules.pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app_assoc,
    Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    Scheme.Modules.pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc,
    Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app_assoc]
  simp [Scheme.Modules.pullbackCongr]

/-- The pullback of a rigidified line bundle along a commutative square `s' ≫ h = g ≫ s`: the line
bundle is pulled back along `h`, and its trivialization along `g`. -/
-- The trivialization's type mentions the pulled-back bundle, whose module must reduce.
@[expose]
def pullback (w : s' ≫ h = g ≫ s) (P : RigidifiedLineBundle s) : RigidifiedLineBundle s' where
  lineBundle := (InvertibleSheaf.pullback h).obj P.lineBundle
  rigidification := pullbackRigidification w P.lineBundle.obj P.rigidification

/-- The line bundle of a pulled-back rigidified line bundle is the pulled-back line bundle. -/
@[simp]
lemma pullback_lineBundle (w : s' ≫ h = g ≫ s) (P : RigidifiedLineBundle s) :
    (pullback w P).lineBundle = (InvertibleSheaf.pullback h).obj P.lineBundle :=
  rfl

/-- The trivialization of a pulled-back rigidified line bundle is `pullbackRigidification`. -/
@[simp]
lemma pullback_rigidification (w : s' ≫ h = g ≫ s) (P : RigidifiedLineBundle s) :
    (pullback w P).rigidification = pullbackRigidification w P.lineBundle.obj P.rigidification :=
  (rfl)

end RigidifiedLineBundle

/-- Isomorphism classes of line bundles on `Y` rigidified along `s : T ⟶ Y`. -/
def RigidifiedLineBundleClass (s : T ⟶ Y) : Type (u + 1) :=
  Quotient (RigidifiedLineBundle.setoid s)

namespace RigidifiedLineBundleClass

variable {s : T ⟶ Y}

/-- The isomorphism class of a rigidified line bundle. -/
def mk (P : RigidifiedLineBundle s) : RigidifiedLineBundleClass s :=
  Quotient.mk _ P

/-- Every class of rigidified line bundles is the class of a rigidified line bundle. -/
theorem mk_surjective :
    Function.Surjective (mk : RigidifiedLineBundle s → RigidifiedLineBundleClass s) :=
  Quotient.mk_surjective

/-- Two rigidified line bundles have the same class exactly when an isomorphism of their line
bundles carries one trivialization to the other. -/
@[simp]
theorem mk_eq_mk_iff {P Q : RigidifiedLineBundle s} :
    mk P = mk Q ↔ ∃ e : P.lineBundle.obj ≅ Q.lineBundle.obj,
      (Scheme.Modules.pullback s).map e.hom ≫ Q.rigidification.hom = P.rigidification.hom :=
  Quotient.eq

/-- Descend a function on rigidified line bundles that respects rigidified isomorphisms to
their isomorphism classes. -/
def lift {α : Sort v} (f : RigidifiedLineBundle s → α)
    (hf : ∀ P Q, (∃ e : P.lineBundle.obj ≅ Q.lineBundle.obj,
      (Scheme.Modules.pullback s).map e.hom ≫ Q.rigidification.hom = P.rigidification.hom) →
        f P = f Q) : RigidifiedLineBundleClass s → α :=
  Quotient.lift f (by
    intro P Q h
    exact hf P Q h)

/-- Applying `lift` to a representative returns the original function. -/
@[simp]
theorem lift_mk {α : Sort v} {f : RigidifiedLineBundle s → α}
    {hf : ∀ P Q, (∃ e : P.lineBundle.obj ≅ Q.lineBundle.obj,
      (Scheme.Modules.pullback s).map e.hom ≫ Q.rigidification.hom = P.rigidification.hom) →
        f P = f Q} (P : RigidifiedLineBundle s) :
    lift f hf (mk P) = f P :=
  by simp only [lift, mk, Quotient.lift_mk]

variable {T' Y' : Scheme.{u}} {s' : T' ⟶ Y'} {h : Y' ⟶ Y} {g : T' ⟶ T}

/-- Pullback of classes of rigidified line bundles along a commutative square
`s' ≫ h = g ≫ s`. -/
def pullback (w : s' ≫ h = g ≫ s) : RigidifiedLineBundleClass s → RigidifiedLineBundleClass s' :=
  Quotient.map (RigidifiedLineBundle.pullback w) fun _ _ ⟨e, he⟩ ↦
    ⟨(Scheme.Modules.pullback h).mapIso e,
      RigidifiedLineBundle.pullbackRigidification_naturality w e.hom _ _ he⟩

/-- Pullback of the class of a rigidified line bundle is the class of its pullback. -/
@[simp]
lemma pullback_mk (w : s' ≫ h = g ≫ s) (P : RigidifiedLineBundle s) :
    pullback w (mk P) = mk (RigidifiedLineBundle.pullback w P) :=
  (rfl)

/-- Pullback along a square whose vertical morphisms are identities is the identity on classes of
rigidified line bundles. -/
lemma pullback_id {h : Y ⟶ Y} {g : T ⟶ T} (hh : h = 𝟙 Y) (hg : g = 𝟙 T) (w : s ≫ h = g ≫ s)
    (a : RigidifiedLineBundleClass s) :
    pullback w a = a := by
  subst hh hg
  obtain ⟨P, rfl⟩ := mk_surjective a
  rw [pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨(Scheme.Modules.pullbackId Y).app P.lineBundle.obj,
    RigidifiedLineBundle.pullbackRigidification_id w _ _⟩

/-- Pullback of classes of rigidified line bundles along two stacked squares is pullback along the
composite square. -/
lemma pullback_comp {T'' Y'' : Scheme.{u}} {s'' : T'' ⟶ Y''} {h' : Y'' ⟶ Y'} {g' : T'' ⟶ T'}
    {h'' : Y'' ⟶ Y} {g'' : T'' ⟶ T} (hh : h' ≫ h = h'') (hg : g' ≫ g = g'')
    (w : s' ≫ h = g ≫ s) (w' : s'' ≫ h' = g' ≫ s') (w'' : s'' ≫ h'' = g'' ≫ s)
    (a : RigidifiedLineBundleClass s) :
    pullback w' (pullback w a) = pullback w'' a := by
  subst hh hg
  obtain ⟨P, rfl⟩ := mk_surjective a
  rw [pullback_mk, pullback_mk, pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨(Scheme.Modules.pullbackComp h' h).app P.lineBundle.obj,
    RigidifiedLineBundle.pullbackRigidification_comp w w' w'' _ _⟩

/-- The class of the underlying line bundle of a rigidified line bundle, forgetting the
trivialization. -/
def toLineBundleClass : RigidifiedLineBundleClass s → LineBundleClass Y :=
  lift (fun P ↦ LineBundleClass.mk P.lineBundle) fun _ _ ⟨e, _⟩ ↦
    LineBundleClass.mk_eq_mk_iff.mpr ⟨e⟩

/-- Forgetting the trivialization of the class of `P` gives the class of its line bundle. -/
@[simp]
lemma toLineBundleClass_mk (P : RigidifiedLineBundle s) :
    toLineBundleClass (mk P) = LineBundleClass.mk P.lineBundle :=
  (rfl)

/-- Forgetting the trivialization commutes with pullback. -/
@[simp]
lemma toLineBundleClass_pullback (w : s' ≫ h = g ≫ s) (a : RigidifiedLineBundleClass s) :
    toLineBundleClass (pullback w a) = LineBundleClass.pullback h (toLineBundleClass a) := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  rw [pullback_mk, toLineBundleClass_mk, toLineBundleClass_mk, LineBundleClass.pullback_mk,
    RigidifiedLineBundle.pullback_lineBundle]

end RigidifiedLineBundleClass

end

end AlgebraicGeometry

end TauCeti
