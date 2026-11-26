/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Rep.CoefficientChange
public import TauCeti.RepresentationTheory.Smooth.BaseChange
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# Change of coefficients as functors on smooth representations

Let `A → B` be a homomorphism of commutative rings and `G` a topological group. Base change
`V ↦ B ⊗_A V` and restriction of scalars are functors between categories of representations
(`Rep.extendScalars`, `Rep.restrictScalars`), and both preserve smoothness: base change by
`Representation.isSmooth_baseChange`, restriction because it keeps the operators. This file lifts
them to functors `TauCeti.SmoothRep.extendScalars B : SmoothRep A G ⥤ SmoothRep B G` and
`TauCeti.SmoothRep.restrictScalars A : SmoothRep B G ⥤ SmoothRep A G` between the full
subcategories of smooth representations, and transports the structure proved on `Rep`: both are
additive, and base change is left adjoint to restriction of scalars
(`TauCeti.SmoothRep.extendRestrictScalarsAdj`, with unit `v ↦ 1 ⊗ v` and counit `b ⊗ w ↦ b • w`),
naturally isomorphic to the identity along `A → A` (`TauCeti.SmoothRep.extendScalarsId`), and
compatible with composition along `A → B → C` (`TauCeti.SmoothRep.extendScalarsComp`).

Every morphism, component and correspondence here has the morphism of representations underlying
it in `Rep`, given by the `simp` lemmas below; the evaluation lemmas on `Rep` then apply.

## Main definitions

* `TauCeti.SmoothRep.extendScalars B`: base change `SmoothRep A G ⥤ SmoothRep B G`.
* `TauCeti.SmoothRep.restrictScalars A`: restriction of scalars `SmoothRep B G ⥤ SmoothRep A G`.
* `TauCeti.SmoothRep.extendRestrictScalarsAdj`: the adjunction
  `extendScalars B ⊣ restrictScalars A`.
* `TauCeti.SmoothRep.extendScalarsId`: base change along the identity is the identity functor.
* `TauCeti.SmoothRep.extendScalarsComp`: base change along `A → B → C` is base change along
  `A → C`.
-/

@[expose] public section

open CategoryTheory Representation

universe w u v

namespace TauCeti

namespace SmoothRep

variable {G : Type*} [Group G] [TopologicalSpace G]

/-! ### Base change -/

section ExtendScalars

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
  [SeparatelyContinuousMul G]

/-- **Base change of smooth representations**: `Rep.extendScalars B`, `V ↦ B ⊗_A V`, restricted to
smooth representations, which it preserves by `Representation.isSmooth_baseChange`. -/
noncomputable abbrev extendScalars : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} B G :=
  ObjectProperty.lift _ (ι A G ⋙ Rep.extendScalars B) fun V ↦
    inferInstanceAs (IsSmooth (V.obj.ρ.baseChange B))

variable {B}

/-- The morphism of representations underlying `(extendScalars B).map f` is
`(Rep.extendScalars B).map f`. -/
@[simp] lemma extendScalars_map_hom {V W : SmoothRep.{max v w} A G} (f : V ⟶ W) :
    ((extendScalars B).map f).hom = (Rep.extendScalars B).map f.hom :=
  (rfl)

variable (B) in
/-- Two morphisms out of `B ⊗_A V` that agree on pure tensors are equal. -/
lemma extendScalars_hom_ext {V : SmoothRep.{max v w} A G} {W : SmoothRep.{max v w} B G}
    {f g : (extendScalars B).obj V ⟶ W}
    (h : ∀ (b : B) (v : V.obj), f.hom.hom (b ⊗ₜ[A] v) = g.hom.hom (b ⊗ₜ[A] v)) : f = g :=
  ObjectProperty.hom_ext _ <| Rep.extendScalars_hom_ext B h

variable (B) in
/-- Base change of smooth representations is an additive functor. -/
instance additive_extendScalars :
    (extendScalars B : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} B G).Additive where
  map_add {_ _ f _} := ObjectProperty.hom_ext _ <| (Rep.extendScalars B).map_add (f := f.hom)

end ExtendScalars

/-! ### Restriction of scalars -/

section RestrictScalars

variable (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- **Restriction of scalars of smooth representations**: `Rep.restrictScalars A` restricted to
smooth representations, which it preserves because it keeps the operators. -/
noncomputable abbrev restrictScalars : SmoothRep.{w} B G ⥤ SmoothRep.{w} A G :=
  ObjectProperty.lift _ (ι B G ⋙ Rep.restrictScalars A) fun V ↦
    ⟨fun v ↦ by
      convert IsSmooth.isOpen_stabilizer (ρ := V.obj.ρ) v using 2
      ext g
      exact (congrArg (· = v) (Rep.restrictScalars_obj_ρ_apply V.obj g v)).to_iff⟩

variable {A}

/-- The morphism of representations underlying `(restrictScalars A).map f` is
`(Rep.restrictScalars A).map f`. -/
@[simp] lemma restrictScalars_map_hom {V W : SmoothRep.{w} B G} (f : V ⟶ W) :
    ((restrictScalars A).map f).hom = (Rep.restrictScalars A).map f.hom :=
  (rfl)

variable (A) in
/-- Restriction of scalars of smooth representations is an additive functor. -/
instance additive_restrictScalars :
    (restrictScalars A : SmoothRep.{w} B G ⥤ SmoothRep.{w} A G).Additive where
  map_add {_ _ f _} := ObjectProperty.hom_ext _ <| (Rep.restrictScalars A).map_add (f := f.hom)

end RestrictScalars

/-! ### The adjunction -/

section Adjunction

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
  [SeparatelyContinuousMul G]

/-- **Base change is left adjoint to restriction of scalars** on smooth representations: the
adjunction `Rep.extendRestrictScalarsAdj` on the underlying representations, with unit `v ↦ 1 ⊗ v`
and counit `b ⊗ w ↦ b • w`. -/
noncomputable def extendRestrictScalarsAdj :
    (extendScalars B : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} B G) ⊣
      restrictScalars A where
  unit :=
    { app V := ObjectProperty.homMk ((Rep.extendRestrictScalarsAdj A B).unit.app V.obj)
      naturality _ _ f := ObjectProperty.hom_ext _ <|
        (Rep.extendRestrictScalarsAdj A B).unit.naturality f.hom }
  counit :=
    { app W := ObjectProperty.homMk ((Rep.extendRestrictScalarsAdj A B).counit.app W.obj)
      naturality _ _ f := ObjectProperty.hom_ext _ <|
        (Rep.extendRestrictScalarsAdj A B).counit.naturality f.hom }
  left_triangle_components V := ObjectProperty.hom_ext _ <|
    (Rep.extendRestrictScalarsAdj A B).left_triangle_components V.obj
  right_triangle_components W := ObjectProperty.hom_ext _ <|
    (Rep.extendRestrictScalarsAdj A B).right_triangle_components W.obj

variable {A B}

/-- The unit of `extendScalars B ⊣ restrictScalars A` is that of `Rep.extendRestrictScalarsAdj`,
`v ↦ 1 ⊗ v`. -/
@[simp] lemma extendRestrictScalarsAdj_unit_app_hom (V : SmoothRep.{max v w} A G) :
    ((extendRestrictScalarsAdj A B).unit.app V).hom =
      (Rep.extendRestrictScalarsAdj A B).unit.app V.obj :=
  (rfl)

/-- The counit of `extendScalars B ⊣ restrictScalars A` is that of
`Rep.extendRestrictScalarsAdj`, `b ⊗ w ↦ b • w`. -/
@[simp] lemma extendRestrictScalarsAdj_counit_app_hom (W : SmoothRep.{max v w} B G) :
    ((extendRestrictScalarsAdj A B).counit.app W).hom =
      (Rep.extendRestrictScalarsAdj A B).counit.app W.obj :=
  (rfl)

/-- The adjunction acts on the underlying morphisms as `Rep.extendRestrictScalarsAdj`:
`f ↦ (v ↦ f (1 ⊗ v))`. -/
@[simp] lemma extendRestrictScalarsAdj_homEquiv_apply_hom {V : SmoothRep.{max v w} A G}
    {W : SmoothRep.{max v w} B G} (f : (extendScalars B).obj V ⟶ W) :
    ((extendRestrictScalarsAdj A B).homEquiv V W f).hom =
      (Rep.extendRestrictScalarsAdj A B).homEquiv V.obj W.obj f.hom :=
  (rfl)

/-- The inverse of the adjunction acts on the underlying morphisms as that of
`Rep.extendRestrictScalarsAdj`: `g ↦ (b ⊗ v ↦ b • g v)`. -/
@[simp] lemma extendRestrictScalarsAdj_homEquiv_symm_apply_hom {V : SmoothRep.{max v w} A G}
    {W : SmoothRep.{max v w} B G} (g : V ⟶ (restrictScalars A).obj W) :
    (((extendRestrictScalarsAdj A B).homEquiv V W).symm g).hom =
      ((Rep.extendRestrictScalarsAdj A B).homEquiv V.obj W.obj).symm g.hom :=
  (rfl)

end Adjunction

/-! ### Identity and composition -/

section IdComp

variable (A : Type u) [CommRing A] [SeparatelyContinuousMul G]

/-- **Base change along the identity is the identity**: `Rep.extendScalarsId`,
`A ⊗_A V ≅ V`, `a ⊗ v ↦ a • v`, on smooth representations. -/
noncomputable def extendScalarsId :
    (extendScalars A : SmoothRep.{max u w} A G ⥤ SmoothRep.{max u w} A G) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ ((Rep.extendScalarsId A).app V.obj))
    fun f ↦ ObjectProperty.hom_ext _ <| (Rep.extendScalarsId A).hom.naturality f.hom

/-- The components of `extendScalarsId` are those of `Rep.extendScalarsId`. -/
@[simp] lemma extendScalarsId_hom_app_hom (V : SmoothRep.{max u w} A G) :
    ((extendScalarsId A).hom.app V).hom = (Rep.extendScalarsId A).hom.app V.obj :=
  (rfl)

/-- The inverse components of `extendScalarsId` are those of `Rep.extendScalarsId`. -/
@[simp] lemma extendScalarsId_inv_app_hom (V : SmoothRep.{max u w} A G) :
    ((extendScalarsId A).inv.app V).hom = (Rep.extendScalarsId A).inv.app V.obj :=
  (rfl)

variable {A} (B : Type v) [CommRing B] [Algebra A B] (C : Type v) [CommRing C] [Algebra A C]
  [Algebra B C] [IsScalarTower A B C]

/-- **Base change is compatible with composition**: `Rep.extendScalarsComp`,
`C ⊗_B (B ⊗_A V) ≅ C ⊗_A V`, on smooth representations. The rings `B` and `C` are taken in one
universe, so that both functors act on `SmoothRep.{max v w}`. -/
noncomputable def extendScalarsComp :
    (extendScalars B ⋙ extendScalars C : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} C G) ≅
      extendScalars C :=
  NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ ((Rep.extendScalarsComp B C).app V.obj))
    fun f ↦ ObjectProperty.hom_ext _ <| (Rep.extendScalarsComp B C).hom.naturality f.hom

/-- The components of `extendScalarsComp` are those of `Rep.extendScalarsComp`. -/
@[simp] lemma extendScalarsComp_hom_app_hom (V : SmoothRep.{max v w} A G) :
    ((extendScalarsComp B C).hom.app V).hom = (Rep.extendScalarsComp B C).hom.app V.obj :=
  (rfl)

/-- The inverse components of `extendScalarsComp` are those of `Rep.extendScalarsComp`. -/
@[simp] lemma extendScalarsComp_inv_app_hom (V : SmoothRep.{max v w} A G) :
    ((extendScalarsComp B C).inv.app V).hom = (Rep.extendScalarsComp B C).inv.app V.obj :=
  (rfl)

end IdComp

end SmoothRep

end TauCeti
