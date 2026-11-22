/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Models with a marked generic fibre over an irreducible base

Let `S` be an irreducible scheme with function field `K = K(S)`, and let `C` be a scheme over
`Spec K`. A marked model of `C` over `S` (`TauCeti.MarkedModel S C toK`) is a flat morphism of
finite presentation `f : X ⟶ S` together with a morphism `ι : C ⟶ X` exhibiting `C` as the generic
fibre `X ×_S Spec K` of `f`: the square formed by `ι`, `C ⟶ Spec K`, `f` and the generic point
`Spec K ⟶ S` is a pullback. Equivalently, it is the datum of an isomorphism `X_η ≅ C` over `K`
(`TauCeti.MarkedModel.genericFiberIso`, and conversely `TauCeti.MarkedModel.ofGenericFiberIso`).
The typical base is a Dedekind scheme, such as the spectrum of a Dedekind domain or a field, and
then a marked model is an integral model of `C`.

Marked models form a category: a morphism is a morphism of total spaces over `S` which restricts to
the identity of `C` on generic fibres (`TauCeti.MarkedModel.genericι_comp_eq_iff` restates this
condition through the markings `X_η ≅ C`). The generic marking is data. Composing it with a
nontrivial automorphism of `C` gives a marked model with the same total space which is in general
not isomorphic to the original one through the identity of the total space.

Over an integral base, flatness makes the generic fibre scheme-theoretically dense in the total
space (`TauCeti.MarkedModel.isSchemeTheoreticallyDominant_genericι`), so a morphism of total spaces
into a scheme separated over `S` is determined by its restriction to the generic fibre
(`TauCeti.MarkedModel.ext_of_genericι_comp_eq`). In particular there is at most one morphism of
marked models into a model which is separated over `S`
(`TauCeti.MarkedModel.subsingleton_hom`). This gives uniqueness of morphisms extending a generic
identification, not their existence.

Over the spectrum of a field, or any base whose generic point `Spec K(S) ⟶ S` is an isomorphism,
the marking identifies the total space with `C` (`TauCeti.MarkedModel.isIso_genericι`).

Properness is deliberately not part of the definition (`TauCeti.MarkedModel.IsProper`): many
constructions produce a model first and establish properness separately.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, §10.1
  (models over Dedekind schemes) and §4.3 (flatness over Dedekind schemes).
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

/-- A marked model of a scheme `C` over the function field of an irreducible scheme `S`: a flat
morphism of finite presentation `toBase : total ⟶ S` together with a morphism `genericι : C ⟶ total`
exhibiting `C` as the generic fibre of `toBase`, that is, making the square with
`toK : C ⟶ Spec K(S)` and the generic point `Spec K(S) ⟶ S` a pullback.

Finite presentation is recorded by Mathlib's three constituent properties:
`LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`. -/
structure MarkedModel (S : Scheme.{u}) [IrreducibleSpace S] (C : Scheme.{u})
    (toK : C ⟶ Spec S.functionField) where
  /-- The total space of the model. -/
  total : Scheme.{u}
  /-- The structure morphism of the model. -/
  toBase : total ⟶ S
  /-- The structure morphism is flat. -/
  flat : Flat toBase
  /-- The structure morphism is locally of finite presentation. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation toBase
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact toBase
  /-- The structure morphism is quasi-separated. -/
  quasiSeparated : QuasiSeparated toBase
  /-- The inclusion of the marked generic fibre into the total space. -/
  genericι : C ⟶ total
  /-- The marked scheme `C` is the generic fibre of the structure morphism. -/
  isPullback : IsPullback genericι toK toBase (S.fromSpecStalk (genericPoint S))

namespace MarkedModel

variable {S : Scheme.{u}} [IrreducibleSpace S] {C : Scheme.{u}} {toK : C ⟶ Spec S.functionField}

attribute [instance] MarkedModel.flat MarkedModel.locallyOfFinitePresentation
  MarkedModel.quasiCompact MarkedModel.quasiSeparated

/-- Properness of the structure morphism is an additional property of a marked model. -/
abbrev IsProper (M : MarkedModel S C toK) : Prop :=
  AlgebraicGeometry.IsProper M.toBase

/-- The inclusion of the marked generic fibre lies over the generic point of the base. -/
@[reassoc (attr := simp)]
lemma genericι_toBase (M : MarkedModel S C toK) :
    M.genericι ≫ M.toBase = toK ≫ S.fromSpecStalk (genericPoint S) :=
  M.isPullback.w

section GenericFiber

variable (M : MarkedModel S C toK)

/-- The marking of a model: the identification of the generic fibre `X ×_S Spec K(S)` of the
structure morphism with the marked scheme `C`, as schemes over `Spec K(S)`
(`TauCeti.MarkedModel.genericFiberIso_hom_toK`). -/
def genericFiberIso : pullback M.toBase (S.fromSpecStalk (genericPoint S)) ≅ C :=
  M.isPullback.isoPullback.symm

/-- The marking followed by the inclusion of `C` is the projection of the generic fibre. -/
@[reassoc (attr := simp)]
lemma genericFiberIso_hom_genericι :
    M.genericFiberIso.hom ≫ M.genericι = pullback.fst _ _ :=
  M.isPullback.isoPullback_inv_fst

/-- The marking is an isomorphism of schemes over `Spec K(S)`. -/
@[reassoc (attr := simp)]
lemma genericFiberIso_hom_toK :
    M.genericFiberIso.hom ≫ toK = pullback.snd _ _ :=
  M.isPullback.isoPullback_inv_snd

/-- The inverse marking followed by the projection of the generic fibre is the inclusion of `C`. -/
@[reassoc (attr := simp)]
lemma genericFiberIso_inv_fst :
    M.genericFiberIso.inv ≫ pullback.fst _ _ = M.genericι :=
  M.isPullback.isoPullback_hom_fst

/-- The inverse marking is an isomorphism of schemes over `Spec K(S)`. -/
@[reassoc (attr := simp)]
lemma genericFiberIso_inv_snd :
    M.genericFiberIso.inv ≫ pullback.snd _ _ = toK :=
  M.isPullback.isoPullback_hom_snd

end GenericFiber

section OfGenericFiberIso

variable {X : Scheme.{u}} (toBase : X ⟶ S) [Flat toBase] [LocallyOfFinitePresentation toBase]
  [QuasiCompact toBase] [QuasiSeparated toBase]
  (e : pullback toBase (S.fromSpecStalk (genericPoint S)) ≅ C) (he : e.hom ≫ toK = pullback.snd _ _)

/-- The marked model given by a flat morphism of finite presentation `toBase : X ⟶ S` and an
identification `e` of its generic fibre with `C` over `Spec K(S)`. Its marking is `e`
(`TauCeti.MarkedModel.genericFiberIso_ofGenericFiberIso`). -/
-- The body is exposed so that the total space is `X` by definition.
@[expose] def ofGenericFiberIso : MarkedModel S C toK where
  total := X
  toBase := toBase
  flat := ‹_›
  locallyOfFinitePresentation := ‹_›
  quasiCompact := ‹_›
  quasiSeparated := ‹_›
  genericι := e.inv ≫ pullback.fst _ _
  isPullback := (IsPullback.of_hasPullback toBase (S.fromSpecStalk (genericPoint S))).of_iso
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [he]) (by simp) (by simp)

@[simp]
lemma ofGenericFiberIso_toBase : (ofGenericFiberIso toBase e he).toBase = toBase :=
  (rfl)

@[simp]
lemma ofGenericFiberIso_genericι :
    (ofGenericFiberIso toBase e he).genericι = e.inv ≫ pullback.fst _ _ :=
  (rfl)

/-- The marking of the marked model given by an identification of the generic fibre is that
identification. -/
@[simp]
lemma genericFiberIso_ofGenericFiberIso : (ofGenericFiberIso toBase e he).genericFiberIso = e :=
  Iso.ext <| (ofGenericFiberIso toBase e he).isPullback.hom_ext
    (by
      rw [genericFiberIso_hom_genericι, ofGenericFiberIso_genericι]
      exact (e.hom_inv_id_assoc _).symm)
    (by rw [genericFiberIso_hom_toK]; exact he.symm)

end OfGenericFiberIso

/-- A morphism of total spaces over the base carries the marked generic fibre of `M` identically
onto that of `N` if and only if its base change to the generic point is compatible with the two
markings `X_η ≅ C`. -/
theorem genericι_comp_eq_iff {M N : MarkedModel S C toK} (f : M.total ⟶ N.total)
    (overBase : f ≫ N.toBase = M.toBase) :
    M.genericι ≫ f = N.genericι ↔
      pullback.map M.toBase (S.fromSpecStalk (genericPoint S)) N.toBase
          (S.fromSpecStalk (genericPoint S)) f (𝟙 _) (𝟙 _) (by simp [overBase]) (by simp) ≫
        N.genericFiberIso.hom = M.genericFiberIso.hom := by
  constructor
  · intro h
    refine N.isPullback.hom_ext ?_ ?_
    · rw [Category.assoc, N.genericFiberIso_hom_genericι, ← h,
        M.genericFiberIso_hom_genericι_assoc]
      simp
    · simp
  · intro h
    simpa using congrArg (M.genericFiberIso.inv ≫ · ≫ N.genericι) h

/-- A morphism of marked models is a morphism of total spaces over the base which restricts to the
identity of the marked generic fibre. -/
structure Hom (M N : MarkedModel S C toK) where
  /-- The morphism of total spaces. -/
  hom : M.total ⟶ N.total
  /-- The morphism commutes with the structure maps to the base. -/
  overBase : hom ≫ N.toBase = M.toBase
  /-- The morphism restricts to the identity of the marked generic fibre. -/
  genericι_hom : M.genericι ≫ hom = N.genericι

attribute [reassoc (attr := simp)] Hom.overBase Hom.genericι_hom

/-- Morphisms of marked models are determined by their maps on total spaces. -/
@[ext]
lemma Hom.ext {M N : MarkedModel S C toK} {f g : Hom M N} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Marked models of a fixed scheme over the function field form a category. -/
instance : Category (MarkedModel S C toK) where
  Hom := Hom
  id M :=
    { hom := 𝟙 M.total
      overBase := Category.id_comp _
      genericι_hom := Category.comp_id _ }
  comp f g :=
    { hom := f.hom ≫ g.hom
      overBase := by rw [Category.assoc, g.overBase, f.overBase]
      genericι_hom := by rw [f.genericι_hom_assoc, g.genericι_hom] }
  id_comp f := by ext; exact Category.id_comp _
  comp_id f := by ext; exact Category.comp_id _
  assoc f g h := by ext; exact Category.assoc _ _ _

@[simp]
lemma id_hom (M : MarkedModel S C toK) : Hom.hom (𝟙 M) = 𝟙 M.total :=
  (rfl)

@[simp]
lemma comp_hom {M N P : MarkedModel S C toK} (f : M ⟶ N) (g : N ⟶ P) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  (rfl)

/-- Morphisms of marked models are determined by their maps on total spaces, stated for morphisms
in the category of marked models. -/
@[ext]
lemma hom_ext {M N : MarkedModel S C toK} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- The faithful functor sending a marked model to its total space. -/
def forget : MarkedModel S C toK ⥤ Scheme.{u} where
  obj M := M.total
  map f := f.hom
  map_id M := id_hom M
  map_comp f g := comp_hom f g

@[simp]
lemma forget_obj (M : MarkedModel S C toK) : (forget (toK := toK)).obj M = M.total :=
  (rfl)

/-- The map of the total-space functor is the underlying scheme morphism, transported along the
object-map equalities. -/
@[simp]
lemma forget_map {M N : MarkedModel S C toK} (f : M ⟶ N) :
    (forget (toK := toK)).map f = eqToHom (forget_obj M) ≫ f.hom ≫ eqToHom (forget_obj N).symm :=
  (rfl)

instance : (forget (toK := toK)).Faithful where
  map_injective {M N} _ _ h := Hom.ext (by
    rw [← cancel_epi (eqToHom (forget_obj M)), ← cancel_mono (eqToHom (forget_obj N).symm)]
    simpa only [Category.assoc, forget_map] using h)

/-- An isomorphism of marked models built from an isomorphism of total spaces over the base which
restricts to the identity of the marked generic fibre. -/
def isoMk {M N : MarkedModel S C toK} (e : M.total ≅ N.total)
    (overBase : e.hom ≫ N.toBase = M.toBase) (genericι_hom : M.genericι ≫ e.hom = N.genericι) :
    M ≅ N where
  hom := ⟨e.hom, overBase, genericι_hom⟩
  inv := ⟨e.inv, by rw [← overBase, e.inv_hom_id_assoc],
    by rw [← genericι_hom, Category.assoc, e.hom_inv_id, Category.comp_id]⟩

@[simp]
lemma isoMk_hom_hom {M N : MarkedModel S C toK} (e : M.total ≅ N.total)
    (overBase : e.hom ≫ N.toBase = M.toBase) (genericι_hom : M.genericι ≫ e.hom = N.genericι) :
    (isoMk e overBase genericι_hom).hom.hom = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom {M N : MarkedModel S C toK} (e : M.total ≅ N.total)
    (overBase : e.hom ≫ N.toBase = M.toBase) (genericι_hom : M.genericι ≫ e.hom = N.genericι) :
    (isoMk e overBase genericι_hom).inv.hom = e.inv :=
  (rfl)

/-- A morphism of marked models is an isomorphism exactly when its map of total spaces is. -/
theorem isIso_iff_isIso_hom {M N : MarkedModel S C toK} (f : M ⟶ N) : IsIso f ↔ IsIso f.hom := by
  refine ⟨fun _ ↦ ⟨(inv f).hom, ?_, ?_⟩,
    fun _ ↦ (isoMk (asIso f.hom) f.overBase f.genericι_hom).isIso_hom⟩
  · rw [← comp_hom, IsIso.hom_inv_id, id_hom]
  · rw [← comp_hom, IsIso.inv_hom_id, id_hom]

/-- Over a base whose generic point `Spec K(S) ⟶ S` is an isomorphism, such as the spectrum of a
field, the inclusion of the marked generic fibre is an isomorphism: the total space of a marked
model is the marked scheme itself. -/
instance isIso_genericι [IsIso (S.fromSpecStalk (genericPoint S))] (M : MarkedModel S C toK) :
    IsIso M.genericι :=
  M.isPullback.isIso_fst_of_isIso

section Integral

variable [IsIntegral S]

/-- Over an integral base, the marked generic fibre of a model is scheme-theoretically dense in its
total space, because the total space is flat over the base. In particular the total space need not
be reduced. -/
instance isSchemeTheoreticallyDominant_genericι (M : MarkedModel S C toK) :
    IsSchemeTheoreticallyDominant M.genericι := by
  have : IsSchemeTheoreticallyDominant (S.fromSpecStalk (genericPoint S)) :=
    .of_isDominant _
  exact .of_isPullback M.isPullback.flip

/-- Over an integral base, a morphism from the total space of a marked model to a scheme separated
over the base is determined by its restriction to the marked generic fibre. -/
theorem ext_of_genericι_comp_eq (M : MarkedModel S C toK) {Y : Scheme.{u}} (s : Y ⟶ S)
    [IsSeparated s] {f g : M.total ⟶ Y} (h : f ≫ s = g ≫ s)
    (hη : M.genericι ≫ f = M.genericι ≫ g) : f = g :=
  ext_of_isSchemeTheoreticallyDominant M.genericι s h hη

/-- Over an integral base, there is at most one morphism of marked models into a model which is
separated over the base. Existence is a separate question. -/
instance subsingleton_hom {M N : MarkedModel S C toK} [IsSeparated N.toBase] :
    Subsingleton (M ⟶ N) where
  allEq f g := hom_ext (ext_of_genericι_comp_eq M N.toBase (by simp) (by simp))

/-- Over an integral base, there is at most one isomorphism between two marked models when the
target is separated over the base. -/
instance subsingleton_iso {M N : MarkedModel S C toK} [IsSeparated N.toBase] :
    Subsingleton (M ≅ N) where
  allEq e e' := Iso.ext (Subsingleton.elim e.hom e'.hom)

end Integral

end MarkedModel

end TauCeti
