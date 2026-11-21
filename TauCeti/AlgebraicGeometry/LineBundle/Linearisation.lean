/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Linearised invertible sheaves

For a scheme `X` acted on over `S`, a linearisation of a line bundle `L` is an
isomorphism `a^* L ≅ pr₂^* L` over the product of the acting scheme and `X`. The
unit and cocycle laws are expressed on all test schemes over `S`, not merely on
field-valued points. The groupoid remembers compatible isomorphisms of line bundles.

We use the internal action `ModObj` in `Over S`, and the composition and unit
comparisons for `Scheme.Modules.pullback`.

## References

* Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, Chapter 1, §3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped MonObj

namespace TauCeti

open TauCeti.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {G X : Over S} [MonObj G] [ModObj G X]

namespace Linearisation

/-- Restrict an isomorphism between the action and projection pullbacks of a module sheaf to
`(g, x)`, using the pullback composition isomorphisms to identify its endpoints. -/
def atPoint (M : X.left.Modules)
    (φ : (pullback (γ[G,X]).left).obj M ≅ (pullback (snd G X).left).obj M)
    {T : Over S} (g : T ⟶ G) (x : T ⟶ X) :
    (pullback (g • x).left).obj M ≅ (pullback x.left).obj M := by
  let f := lift g x
  have ha : (g • x).left = f.left ≫ (γ[G,X]).left :=
    congrArg Over.Hom.left (CategoryTheory.Hom.smul_def T g x)
  have hp : f.left ≫ (snd G X).left = x.left := congrArg Over.Hom.left (lift_snd g x)
  exact (pullbackCongr ha).app M ≪≫ (pullbackComp f.left (γ[G,X]).left).symm.app M ≪≫
    (pullback f.left).mapIso φ ≪≫ (pullbackComp f.left (snd G X).left).app M ≪≫
    (pullbackCongr hp).app M

private theorem atPoint_unitIso {T : Over S} (g : T ⟶ G) (x : T ⟶ X) :
    atPoint (𝟙_ X.left.Modules)
      (pullbackObjUnitIso (γ[G,X]).left ≪≫ (pullbackObjUnitIso (snd G X).left).symm) g x =
      pullbackObjUnitIso (g • x).left ≪≫ (pullbackObjUnitIso x.left).symm := by
  apply Iso.ext
  apply (cancel_mono (pullbackObjUnitIso x.left).hom).mp
  let f := (lift g x).left
  let p := (snd G X).left
  have h : (pullback f).map (pullbackObjUnitIso p).inv ≫ (pullbackComp f p).hom.app _ ≫
      (pullbackObjUnitIso (f ≫ p)).hom = (pullbackObjUnitIso f).hom := by
    apply (cancel_epi (pullbackObjUnitIso f).inv).mp
    simp only [pullbackObjUnitIso_inv_comp_assoc, Iso.inv_hom_id]
  simp only [atPoint, Iso.trans_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    pullbackObjUnitIso_congr, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  -- First cancel the comparison for the second projection, then compose along the action.
  rw [h, pullbackObjUnitIso_comp, pullbackObjUnitIso_congr]

end Linearisation

/-- A linearisation of a sheaf of modules for an internal action on a scheme: the pullback
isomorphism `φ` identifies the pullback at `g • x` with the pullback at `x`, compatibly with
multiplication and the unit on every test scheme. Only the isomorphism on `G ×ₛ X` is stored. -/
@[ext]
structure Linearisation (G : Over S) {X : Over S} [MonObj G] [ModObj G X]
    (M : X.left.Modules) where
  /-- The comparison between pullbacks along the action and the second projection. -/
  iso : (pullback (γ[G,X]).left).obj M ≅ (pullback (snd G X).left).obj M
  /-- The unit acts by the identity, after identifying the two pullbacks. -/
  unit (T : Over S) (x : T ⟶ X) :
    Linearisation.atPoint M iso (1 : T ⟶ G) x =
      (pullbackCongr (congrArg Over.Hom.left (one_smul (T ⟶ G) x))).app M
  /-- The comparison for `g * h` is the composite of the comparisons for `g` and `h`. -/
  cocycle (T : Over S) (g h : T ⟶ G) (x : T ⟶ X) :
    Linearisation.atPoint M iso (g * h) x =
      (pullbackCongr (congrArg Over.Hom.left (mul_smul g h x))).app M ≪≫
        Linearisation.atPoint M iso g (h • x) ≪≫ Linearisation.atPoint M iso h x

/-- A line bundle together with a linearisation for the given action on `X`. -/
@[ext]
structure LinearisedLineBundle (G X : Over S) [MonObj G] [ModObj G X] where
  /-- The underlying invertible sheaf. -/
  lineBundle : InvertibleSheaf X.left
  /-- The lift of the action to the line bundle. -/
  linearisation : Linearisation G lineBundle.obj

namespace Linearisation

private abbrev unitActionIso (G X : Over S) [MonObj G] [ModObj G X] :
    (pullback (γ[G,X]).left).obj (𝟙_ X.left.Modules) ≅
      (pullback (snd G X).left).obj (𝟙_ X.left.Modules) :=
  pullbackObjUnitIso (γ[G,X]).left ≪≫ (pullbackObjUnitIso (snd G X).left).symm

private theorem unitActionIso_unit (T : Over S) (x : T ⟶ X) :
    atPoint (𝟙_ X.left.Modules) (unitActionIso G X) (1 : T ⟶ G) x =
      (pullbackCongr (congrArg Over.Hom.left (one_smul (T ⟶ G) x))).app (𝟙_ X.left.Modules) :=
  (atPoint_unitIso (1 : T ⟶ G) x).trans (by
    apply Iso.ext
    apply (cancel_mono (pullbackObjUnitIso x.left).hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.app_hom, pullbackObjUnitIso_congr])

private theorem unitActionIso_cocycle (T : Over S) (g h : T ⟶ G) (x : T ⟶ X) :
    atPoint (𝟙_ X.left.Modules) (unitActionIso G X) (g * h) x =
      (pullbackCongr (congrArg Over.Hom.left (mul_smul g h x))).app (𝟙_ X.left.Modules) ≪≫
        atPoint (𝟙_ X.left.Modules) (unitActionIso G X) g (h • x) ≪≫
        atPoint (𝟙_ X.left.Modules) (unitActionIso G X) h x := by
  let t : ((g * h) • x).left = (g • (h • x)).left :=
    congrArg Over.Hom.left (mul_smul g h x)
  let e := (pullbackCongr t).app (𝟙_ X.left.Modules)
  have hcomp {U V : Scheme.{u}} {a b c d : U ⟶ V} (ht : a = b) :
      pullbackObjUnitIso a ≪≫ (pullbackObjUnitIso d).symm =
        (pullbackCongr ht).app (𝟙_ V.Modules) ≪≫
          (pullbackObjUnitIso b ≪≫ (pullbackObjUnitIso c).symm) ≪≫
          (pullbackObjUnitIso c ≪≫ (pullbackObjUnitIso d).symm) := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.app_hom, reassoc_of% pullbackObjUnitIso_congr]
  exact (atPoint_unitIso (g * h) x).trans
    ((hcomp (c := (h • x).left) (d := x.left) t).trans
      (congrArg₂ (fun i j => e ≪≫ i ≪≫ j)
        (atPoint_unitIso g (h • x)).symm (atPoint_unitIso h x).symm))

/-- The canonical linearisation of the structure sheaf, identifying both pullbacks with
`𝒪` on the product. -/
def trivial (G X : Over S) [MonObj G] [ModObj G X] :
    Linearisation G (𝟙_ X.left.Modules) :=
  ⟨unitActionIso G X, unitActionIso_unit, unitActionIso_cocycle⟩

/-- The two canonical identifications with the structure sheaf give the trivial linearisation. -/
@[simp]
theorem trivial_iso (G X : Over S) [MonObj G] [ModObj G X] :
    (trivial G X).iso =
      pullbackObjUnitIso (γ[G,X]).left ≪≫ (pullbackObjUnitIso (snd G X).left).symm := (rfl)

end Linearisation

namespace LinearisedLineBundle

/-- The structure sheaf with its canonical linearisation. -/
def trivial (G X : Over S) [MonObj G] [ModObj G X] : LinearisedLineBundle G X :=
  ⟨𝟙_ _, Linearisation.trivial G X⟩

/-- The trivial linearised bundle has underlying line bundle `𝒪_X`. -/
@[simp]
theorem trivial_lineBundle (G X : Over S) [MonObj G] [ModObj G X] :
    (trivial G X).lineBundle = 𝟙_ (InvertibleSheaf X.left) := (rfl)

/-- An isomorphism of line bundles intertwining their linearisations. -/
@[ext]
structure Hom (L K : LinearisedLineBundle G X) where
  /-- The underlying isomorphism of invertible sheaves. -/
  iso : L.lineBundle ≅ K.lineBundle
  /-- The square with the two linearisation isomorphisms commutes. -/
  comm : (pullback (γ[G,X]).left).map iso.hom.hom ≫ K.linearisation.iso.hom =
    L.linearisation.iso.hom ≫ (pullback (snd G X).left).map iso.hom.hom

/-- The groupoid with compatible line-bundle isomorphisms as arrows. -/
instance : Groupoid (LinearisedLineBundle G X) where
  Hom := Hom
  id L := ⟨Iso.refl _, by simp⟩
  comp f g := ⟨f.iso ≪≫ g.iso, by
    simp only [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
      Category.assoc, g.comm, reassoc_of% f.comm]⟩
  inv {L K} f := ⟨f.iso.symm, by
    -- Cancel the two pullbacks of the forward isomorphism to recover the original square.
    apply (cancel_mono ((pullback (snd G X).left).map f.iso.hom.hom)).mp
    apply (cancel_epi ((pullback (γ[G,X]).left).map f.iso.hom.hom)).mp
    have ha := f.iso.hom_inv_id_map_assoc
      ((TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X.left).ι ⋙ pullback (γ[G,X]).left)
      (L.linearisation.iso.hom ≫ (pullback (snd G X).left).map f.iso.hom.hom)
    have hp := f.iso.inv_hom_id_map
      ((TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X.left).ι ⋙ pullback (snd G X).left)
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map,
      ObjectProperty.ι_map] at ha hp
    simp only [Iso.symm_hom, Category.assoc, ha, hp, Category.comp_id]
    exact f.comm.symm⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp
  inv_comp f := by ext; simp
  comp_inv f := by ext; simp

-- Expose the object map so that arrows of the functor have the underlying sheaves as endpoints.
/-- Forget the action on an invertible sheaf and the equivariance of its isomorphisms. -/
@[expose]
def forget : LinearisedLineBundle G X ⥤ InvertibleSheaf X.left where
  obj L := L.lineBundle
  map f := f.iso.hom

/-- The forgetful functor sends an object to its underlying invertible sheaf. -/
@[simp]
theorem forget_obj (L : LinearisedLineBundle G X) : forget.obj L = L.lineBundle := (rfl)

/-- The forgetful functor sends an arrow to its underlying sheaf isomorphism's forward map. -/
@[simp]
theorem forget_map {L K : LinearisedLineBundle G X} (f : L ⟶ K) :
    forget.map f = f.iso.hom := (rfl)

instance : (forget (G := G) (X := X)).Faithful where
  map_injective h := Hom.ext (Iso.ext h)

end LinearisedLineBundle

end TauCeti
