/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Base change and geometric fibres of finite étale schemes

Finite étale morphisms are stable under base change, so pulling back along `f : T ⟶ S`
restricts Mathlib's `Over.pullback f` to a functor `FiniteEtaleScheme.pullback f` from finite
étale `S`-schemes to finite étale `T`-schemes. Base change along identities and composites is
identified with the identity and with composites of base changes by `pullbackId` and
`pullbackComp`, whose components are those of `Over.pullbackId` and `Over.pullbackComp`. These
identifications are coherent: `pullbackComp x (𝟙 S)` is the base change of `pullbackId`
(`pullbackComp_id_inv_app_comp_eqToHom`), and the two identifications of base change along a
triple composite agree (`pullbackComp_comp_inv_app_comp_eqToHom`), up to the equalities
`x ≫ 𝟙 S = x` and `x ≫ f ≫ g = (x ≫ f) ≫ g`. In particular, base change along a scheme
isomorphism is an equivalence of categories (`pullbackIsoEquiv`).

For a geometric point `x : Spec Ω ⟶ S`, with `Ω` a separably closed field, the
*geometric fibre functor* `FiniteEtaleScheme.fiber x` sends a finite étale `S`-scheme `X` to the
finite set attached to `X ×_S Spec Ω` by the classification of finite étale schemes over a
separably closed field. This is the functor on finite étale covers whose automorphisms define
the étale fundamental group based at `x`.

The fibre functor is corepresented by the geometric point itself:
`FiniteEtaleScheme.fiberCompInclIso` identifies `fiber x` with the set of lifts of `x` to
`X`, that is, with morphisms `Over.mk x ⟶ X` in `Over S`. Its proof combines the adjunction
`Over.map x ⊣ Over.pullback x` with `equivOfIsSepClosedFunctorCompInclIso`, which identifies
the finite set attached to a finite étale `Spec Ω`-scheme with its set of sections.
Changing the geometric point along a morphism of bases is `pullbackCompFiberIso`, compatibly with
identities and composites (`pullbackCompFiberIso_id_hom_app`, `pullbackCompFiberIso_comp_hom_app`).
These compatibilities make the étale fundamental group functorial in the scheme.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*.
* The Stacks Project, Section 58.5 (*Finite étale covers of schemes*).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T U V : Scheme.{u}}

/-- Base change of finite étale schemes along `f : T ⟶ S`, sending `X` to `X ×_S T` over `T`.
On underlying objects over the bases it is Mathlib's `Over.pullback f`. -/
@[expose] noncomputable def pullback (f : T ⟶ S) : FiniteEtaleScheme S ⥤ FiniteEtaleScheme T :=
  (finiteEtaleSchemeProperty T).lift ((finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f)
    fun X ↦ (finiteEtaleSchemeProperty_iff _).mpr
      ⟨inferInstanceAs (IsFinite (Limits.pullback.snd X.obj.hom f)),
        inferInstanceAs (Etale (Limits.pullback.snd X.obj.hom f))⟩

/-- Forgetting finiteness and étaleness, base change is `Over.pullback`. -/
@[simp]
theorem pullback_comp_ι (f : T ⟶ S) :
    pullback f ⋙ (finiteEtaleSchemeProperty T).ι =
      (finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f :=
  (rfl)

/-- The scheme over `T` underlying a base change is `Over.pullback f` of the original. -/
@[simp]
theorem pullback_obj_obj (f : T ⟶ S) (X : FiniteEtaleScheme S) :
    ((pullback f).obj X).obj = (Over.pullback f).obj X.obj :=
  (rfl)

/-- On morphisms, base change is `Over.pullback f`. -/
@[simp]
theorem pullback_map_hom (f : T ⟶ S) {X Y : FiniteEtaleScheme S} (g : X ⟶ Y) :
    ((pullback f).map g).hom = (Over.pullback f).map g.hom :=
  (rfl)

/-- First projection of `((pullback f).map g).hom.left`. -/
@[reassoc]
theorem pullback_map_left_fst (f : T ⟶ S) {X Y : FiniteEtaleScheme S} (g : X ⟶ Y) :
    ((pullback f).map g).hom.left ≫ Limits.pullback.fst Y.obj.hom f =
      Limits.pullback.fst X.obj.hom f ≫ g.hom.left :=
  Over.pullback_map_left_fst f g.hom

/-- Two morphisms into `(pullback f).obj Y` are equal if their compositions with
`Limits.pullback.fst Y.obj.hom f` agree. -/
theorem pullback_hom_ext {f : T ⟶ S} {X : FiniteEtaleScheme T} {Y : FiniteEtaleScheme S}
    {v₁ v₂ : X ⟶ (pullback f).obj Y}
    (h : v₁.hom.left ≫ Limits.pullback.fst Y.obj.hom f =
      v₂.hom.left ≫ Limits.pullback.fst Y.obj.hom f) :
    v₁ = v₂ :=
  ObjectProperty.hom_ext _ <| Over.pullback_hom_ext h

/-- Base change along the identity is the identity, with components those of
`Over.pullbackId`. -/
noncomputable def pullbackId : pullback (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Over.pullbackId.app X.obj))
    fun f ↦ ObjectProperty.hom_ext _ (Over.pullbackId.hom.naturality f.hom)

/-- The components of `pullbackId.hom` are those of `Over.pullbackId.hom`. -/
@[simp]
theorem pullbackId_hom_app_hom (X : FiniteEtaleScheme S) :
    (pullbackId.hom.app X).hom = Over.pullbackId.hom.app X.obj :=
  (rfl)

/-- The components of `pullbackId.inv` are those of `Over.pullbackId.inv`. -/
@[simp]
theorem pullbackId_inv_app_hom (X : FiniteEtaleScheme S) :
    (pullbackId.inv.app X).hom = Over.pullbackId.inv.app X.obj :=
  (rfl)

/-- Base change along a composite is the composite of the base changes, with components those
of `Over.pullbackComp`. -/
noncomputable def pullbackComp (f : T ⟶ S) (g : S ⟶ U) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ ((Over.pullbackComp f g).app X.obj))
    fun h ↦ ObjectProperty.hom_ext _ ((Over.pullbackComp f g).hom.naturality h.hom)

/-- The components of `(pullbackComp f g).hom` are those of `Over.pullbackComp`. -/
@[simp]
theorem pullbackComp_hom_app_hom (f : T ⟶ S) (g : S ⟶ U) (X : FiniteEtaleScheme U) :
    ((pullbackComp f g).hom.app X).hom = (Over.pullbackComp f g).hom.app X.obj :=
  (rfl)

/-- The components of `(pullbackComp f g).inv` are those of `Over.pullbackComp`. -/
@[simp]
theorem pullbackComp_inv_app_hom (f : T ⟶ S) (g : S ⟶ U) (X : FiniteEtaleScheme U) :
    ((pullbackComp f g).inv.app X).hom = (Over.pullbackComp f g).inv.app X.obj :=
  (rfl)

/-- Base change along `x : T ⟶ S` of the identification `pullbackId` of base change along the
identity is the composition isomorphism `pullbackComp x (𝟙 S)`, up to the equality
`x ≫ 𝟙 S = x`. -/
@[reassoc]
theorem pullbackComp_id_inv_app_comp_eqToHom (x : T ⟶ S) (X : FiniteEtaleScheme S) :
    (pullbackComp x (𝟙 S)).inv.app X ≫
        eqToHom (congrArg (fun x ↦ (pullback x).obj X) (Category.comp_id x)) =
      (pullback x).map (pullbackId.hom.app X) :=
  -- Morphisms of finite étale schemes, and `eqToHom` between them, are those of `Over T`.
  ObjectProperty.hom_ext _ (Over.pullbackComp_id_inv_app_comp_eqToHom x X.obj)

/-- The two ways of identifying base change along `x ≫ f ≫ g` with the composite of the base
changes along `g`, `f` and `x` agree, up to the equality `x ≫ f ≫ g = (x ≫ f) ≫ g`. -/
@[reassoc]
theorem pullbackComp_comp_inv_app_comp_eqToHom (x : V ⟶ T) (f : T ⟶ S) (g : S ⟶ U)
    (X : FiniteEtaleScheme U) :
    (pullbackComp x (f ≫ g)).inv.app X ≫
        eqToHom (congrArg (fun x ↦ (pullback x).obj X) (Category.assoc x f g).symm) =
      (pullback x).map ((pullbackComp f g).hom.app X) ≫
        (pullbackComp x f).inv.app ((pullback g).obj X) ≫ (pullbackComp (x ≫ f) g).inv.app X :=
  -- As above, the identity is checked in `Over V`.
  ObjectProperty.hom_ext _ (Over.pullbackComp_comp_inv_app_comp_eqToHom x f g X.obj)

section Congr

/-- Pullback functors along equal base morphisms are naturally isomorphic. -/
noncomputable def pullbackCongr {f₁ f₂ : T ⟶ S} (h : f₁ = f₂) : pullback f₁ ≅ pullback f₂ :=
  eqToIso (congrArg pullback h)

/-- Along `rfl`, `pullbackCongr` is the identity natural isomorphism. -/
@[simp] theorem pullbackCongr_refl (f : T ⟶ S) :
    pullbackCongr (rfl : f = f) = Iso.refl (pullback f) := (rfl)

variable {f₁ f₂ : T ⟶ S}

/-- `pullbackCongr` reverses along `Eq.symm`. -/
@[simp] theorem pullbackCongr_symm (h : f₁ = f₂) :
    (pullbackCongr h).symm = pullbackCongr h.symm := by subst h; rfl

private lemma eqToIso_congrArg_pullback_hom_app_hom {f g : T ⟶ S} (h : f = g)
    (X : FiniteEtaleScheme S) :
    ((eqToIso (congrArg pullback h)).hom.app X).hom =
      eqToHom (congrArg (fun k ↦ (Over.pullback k).obj X.obj) h) := by
  subst h; rfl

/-- The components of `(pullbackCongr h).hom` are `eqToHom` along `h`. -/
theorem pullbackCongr_hom_app (h : f₁ = f₂) (X : FiniteEtaleScheme S) :
    (pullbackCongr h).hom.app X = eqToHom (congrArg (fun f ↦ (pullback f).obj X) h) := by
  subst h; rfl

/-- The components of `(pullbackCongr h).inv` are `eqToHom` along `h.symm`. -/
theorem pullbackCongr_inv_app (h : f₁ = f₂) (X : FiniteEtaleScheme S) :
    (pullbackCongr h).inv.app X = eqToHom (congrArg (fun f ↦ (pullback f).obj X) h.symm) := by
  subst h; rfl

/-- The components of `(pullbackCongr h).hom` are those of `Over.pullbackCongr`. -/
theorem pullbackCongr_hom_app_hom (h : f₁ = f₂) (X : FiniteEtaleScheme S) :
    ((pullbackCongr h).hom.app X).hom = (Over.pullbackCongr h).hom.app X.obj :=
  (eqToIso_congrArg_pullback_hom_app_hom h X).trans (Over.pullbackCongr_hom_app h X.obj).symm

/-- The components of `(pullbackCongr h).inv` are those of `Over.pullbackCongr`. -/
theorem pullbackCongr_inv_app_hom (h : f₁ = f₂) (X : FiniteEtaleScheme S) :
    ((pullbackCongr h).inv.app X).hom = (Over.pullbackCongr h).inv.app X.obj := by
  rw [← Iso.symm_hom, ← Iso.symm_hom, pullbackCongr_symm, Over.pullbackCongr_symm]
  exact pullbackCongr_hom_app_hom h.symm X

/-- First projection of `(pullbackCongr h).hom.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_hom_app_hom_left_fst (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) :
    ((pullbackCongr h).hom.app X).hom.left ≫ Limits.pullback.fst X.obj.hom f₂ =
      Limits.pullback.fst X.obj.hom f₁ := by
  rw [pullbackCongr_hom_app_hom]; exact Over.pullbackCongr_hom_app_left_fst h X.obj

/-- Reassociated first projection of `(pullbackCongr h).hom.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_hom_app_hom_left_fst_assoc (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : X.obj.left ⟶ Z) :
    ((pullbackCongr h).hom.app X).hom.left ≫ Limits.pullback.fst X.obj.hom f₂ ≫ k =
      Limits.pullback.fst X.obj.hom f₁ ≫ k := by
  rw [pullbackCongr_hom_app_hom]; exact Over.pullbackCongr_hom_app_left_fst_assoc h X.obj k

/-- Second projection of `(pullbackCongr h).hom.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_hom_app_hom_left_snd (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) :
    ((pullbackCongr h).hom.app X).hom.left ≫ Limits.pullback.snd X.obj.hom f₂ =
      Limits.pullback.snd X.obj.hom f₁ := by
  rw [pullbackCongr_hom_app_hom]; exact Over.pullbackCongr_hom_app_left_snd h X.obj

/-- Reassociated second projection of `(pullbackCongr h).hom.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_hom_app_hom_left_snd_assoc (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : T ⟶ Z) :
    ((pullbackCongr h).hom.app X).hom.left ≫ Limits.pullback.snd X.obj.hom f₂ ≫ k =
      Limits.pullback.snd X.obj.hom f₁ ≫ k := by
  rw [pullbackCongr_hom_app_hom]; exact Over.pullbackCongr_hom_app_left_snd_assoc h X.obj k

/-- First projection of `(pullbackCongr h).inv.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_inv_app_hom_left_fst (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) :
    ((pullbackCongr h).inv.app X).hom.left ≫ Limits.pullback.fst X.obj.hom f₁ =
      Limits.pullback.fst X.obj.hom f₂ := by
  rw [pullbackCongr_inv_app_hom]; exact Over.pullbackCongr_inv_app_left_fst h X.obj

/-- Reassociated first projection of `(pullbackCongr h).inv.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_inv_app_hom_left_fst_assoc (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : X.obj.left ⟶ Z) :
    ((pullbackCongr h).inv.app X).hom.left ≫ Limits.pullback.fst X.obj.hom f₁ ≫ k =
      Limits.pullback.fst X.obj.hom f₂ ≫ k := by
  rw [pullbackCongr_inv_app_hom]; exact Over.pullbackCongr_inv_app_left_fst_assoc h X.obj k

/-- Second projection of `(pullbackCongr h).inv.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_inv_app_hom_left_snd (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) :
    ((pullbackCongr h).inv.app X).hom.left ≫ Limits.pullback.snd X.obj.hom f₁ =
      Limits.pullback.snd X.obj.hom f₂ := by
  rw [pullbackCongr_inv_app_hom]; exact Over.pullbackCongr_inv_app_left_snd h X.obj

/-- Reassociated second projection of `(pullbackCongr h).inv.app X` on underlying schemes. -/
@[simp] theorem pullbackCongr_inv_app_hom_left_snd_assoc (h : f₁ = f₂)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : T ⟶ Z) :
    ((pullbackCongr h).inv.app X).hom.left ≫ Limits.pullback.snd X.obj.hom f₁ ≫ k =
      Limits.pullback.snd X.obj.hom f₂ ≫ k := by
  rw [pullbackCongr_inv_app_hom]; exact Over.pullbackCongr_inv_app_left_snd_assoc h X.obj k

end Congr

section CompIsoOfEq

/-- Natural isomorphism `pullback g ⋙ pullback f ≅ pullback fg` from `f ≫ g = fg`. -/
noncomputable def pullbackCompIsoOfEq (f : U ⟶ T) (g : T ⟶ S) (fg : U ⟶ S) (h : f ≫ g = fg) :
    pullback g ⋙ pullback f ≅ pullback fg := (pullbackComp f g).symm ≪≫ pullbackCongr h

variable {f : U ⟶ T} {g : T ⟶ S} {fg : U ⟶ S}

/-- Forward component of `pullbackCompIsoOfEq` at `X`. -/
theorem pullbackCompIsoOfEq_hom_app (h : f ≫ g = fg) (X : FiniteEtaleScheme S) :
    (pullbackCompIsoOfEq f g fg h).hom.app X =
      (pullbackComp f g).inv.app X ≫ (pullbackCongr h).hom.app X := (rfl)

/-- Inverse component of `pullbackCompIsoOfEq` at `X`. -/
theorem pullbackCompIsoOfEq_inv_app (h : f ≫ g = fg) (X : FiniteEtaleScheme S) :
    (pullbackCompIsoOfEq f g fg h).inv.app X =
      (pullbackCongr h).inv.app X ≫ (pullbackComp f g).hom.app X := (rfl)

/-- Underlying morphism of `(pullbackCompIsoOfEq f g fg h).hom.app X`. -/
theorem pullbackCompIsoOfEq_hom_app_hom (h : f ≫ g = fg) (X : FiniteEtaleScheme S) :
    ((pullbackCompIsoOfEq f g fg h).hom.app X).hom =
      (Over.pullbackCompIsoOfEq f g fg h).hom.app X.obj := by
  rw [pullbackCompIsoOfEq_hom_app, ObjectProperty.FullSubcategory.comp_hom,
    pullbackComp_inv_app_hom, pullbackCongr_hom_app_hom, Over.pullbackCompIsoOfEq_hom_app]; rfl

/-- Underlying morphism of `(pullbackCompIsoOfEq f g fg h).inv.app X`. -/
theorem pullbackCompIsoOfEq_inv_app_hom (h : f ≫ g = fg) (X : FiniteEtaleScheme S) :
    ((pullbackCompIsoOfEq f g fg h).inv.app X).hom =
      (Over.pullbackCompIsoOfEq f g fg h).inv.app X.obj := by
  rw [pullbackCompIsoOfEq_inv_app, ObjectProperty.FullSubcategory.comp_hom,
    pullbackCongr_inv_app_hom, pullbackComp_hom_app_hom, Over.pullbackCompIsoOfEq_inv_app]; rfl

/-- First projection of `(pullbackCompIsoOfEq f g fg h).hom.app X` on underlying schemes. -/
@[simp] theorem pullbackCompIsoOfEq_hom_app_hom_left_fst (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) :
    ((pullbackCompIsoOfEq f g fg h).hom.app X).hom.left ≫ Limits.pullback.fst X.obj.hom fg =
      Limits.pullback.fst (Limits.pullback.snd X.obj.hom g) f ≫
        Limits.pullback.fst X.obj.hom g := by
  rw [pullbackCompIsoOfEq_hom_app_hom]; exact Over.pullbackCompIsoOfEq_hom_app_left_fst h X.obj

/-- Reassociated first projection of `(pullbackCompIsoOfEq f g fg h).hom.app X` on underlying
schemes. -/
@[simp] theorem pullbackCompIsoOfEq_hom_app_hom_left_fst_assoc (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : X.obj.left ⟶ Z) :
    ((pullbackCompIsoOfEq f g fg h).hom.app X).hom.left ≫ Limits.pullback.fst X.obj.hom fg ≫ k =
      Limits.pullback.fst (Limits.pullback.snd X.obj.hom g) f ≫
        Limits.pullback.fst X.obj.hom g ≫ k := by
  rw [pullbackCompIsoOfEq_hom_app_hom]
  exact Over.pullbackCompIsoOfEq_hom_app_left_fst_assoc h X.obj k

/-- Second projection of `(pullbackCompIsoOfEq f g fg h).hom.app X` on underlying schemes. -/
@[simp] theorem pullbackCompIsoOfEq_hom_app_hom_left_snd (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) :
    ((pullbackCompIsoOfEq f g fg h).hom.app X).hom.left ≫ Limits.pullback.snd X.obj.hom fg =
      Limits.pullback.snd (Limits.pullback.snd X.obj.hom g) f := by
  rw [pullbackCompIsoOfEq_hom_app_hom]; exact Over.pullbackCompIsoOfEq_hom_app_left_snd h X.obj

/-- Reassociated second projection of `(pullbackCompIsoOfEq f g fg h).hom.app X` on underlying
schemes. -/
@[simp] theorem pullbackCompIsoOfEq_hom_app_hom_left_snd_assoc (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : U ⟶ Z) :
    ((pullbackCompIsoOfEq f g fg h).hom.app X).hom.left ≫ Limits.pullback.snd X.obj.hom fg ≫ k =
      Limits.pullback.snd (Limits.pullback.snd X.obj.hom g) f ≫ k := by
  rw [pullbackCompIsoOfEq_hom_app_hom]
  exact Over.pullbackCompIsoOfEq_hom_app_left_snd_assoc h X.obj k

/-- First projection of `(pullbackCompIsoOfEq f g fg h).inv.app X` on underlying schemes. -/
@[simp] theorem pullbackCompIsoOfEq_inv_app_hom_left_fst (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) :
    ((pullbackCompIsoOfEq f g fg h).inv.app X).hom.left ≫
        Limits.pullback.fst (Limits.pullback.snd X.obj.hom g) f =
      Limits.pullback.map X.obj.hom fg X.obj.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) := by
  rw [pullbackCompIsoOfEq_inv_app_hom]; exact Over.pullbackCompIsoOfEq_inv_app_left_fst h X.obj

/-- Reassociated first projection of `(pullbackCompIsoOfEq f g fg h).inv.app X` on underlying
schemes. -/
@[simp] theorem pullbackCompIsoOfEq_inv_app_hom_left_fst_assoc (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : Limits.pullback X.obj.hom g ⟶ Z) :
    ((pullbackCompIsoOfEq f g fg h).inv.app X).hom.left ≫
        Limits.pullback.fst (Limits.pullback.snd X.obj.hom g) f ≫ k =
      Limits.pullback.map X.obj.hom fg X.obj.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) ≫ k := by
  rw [pullbackCompIsoOfEq_inv_app_hom]
  exact Over.pullbackCompIsoOfEq_inv_app_left_fst_assoc h X.obj k

/-- Second projection of `(pullbackCompIsoOfEq f g fg h).inv.app X` on underlying schemes. -/
@[simp] theorem pullbackCompIsoOfEq_inv_app_hom_left_snd (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) :
    ((pullbackCompIsoOfEq f g fg h).inv.app X).hom.left ≫
        Limits.pullback.snd (Limits.pullback.snd X.obj.hom g) f =
      Limits.pullback.snd X.obj.hom fg := by
  rw [pullbackCompIsoOfEq_inv_app_hom]; exact Over.pullbackCompIsoOfEq_inv_app_left_snd h X.obj

/-- Reassociated second projection of `(pullbackCompIsoOfEq f g fg h).inv.app X` on underlying
schemes. -/
@[simp] theorem pullbackCompIsoOfEq_inv_app_hom_left_snd_assoc (h : f ≫ g = fg)
    (X : FiniteEtaleScheme S) {Z : Scheme.{u}} (k : U ⟶ Z) :
    ((pullbackCompIsoOfEq f g fg h).inv.app X).hom.left ≫
        Limits.pullback.snd (Limits.pullback.snd X.obj.hom g) f ≫ k =
      Limits.pullback.snd X.obj.hom fg ≫ k := by
  rw [pullbackCompIsoOfEq_inv_app_hom]
  exact Over.pullbackCompIsoOfEq_inv_app_left_snd_assoc h X.obj k

/-- First projection of a morphism between pullbacks of finite étale schemes conjugated along
`pullbackCompIsoOfEq`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_conj_hom_left_fst {f : U ⟶ T} {g : T ⟶ S} {fg : U ⟶ S}
    (h : f ≫ g = fg) {Y₁ Y₂ : FiniteEtaleScheme S}
    (β : (pullback g).obj Y₁ ⟶ (pullback g).obj Y₂) :
    ((pullbackCompIsoOfEq f g fg h).inv.app Y₁ ≫ (pullback f).map β ≫
        (pullbackCompIsoOfEq f g fg h).hom.app Y₂).hom.left ≫
      Limits.pullback.fst Y₂.obj.hom fg =
      Limits.pullback.map Y₁.obj.hom fg Y₁.obj.hom g (𝟙 _) f (𝟙 _) (by simp) (by simp [h]) ≫
        β.hom.left ≫ Limits.pullback.fst Y₂.obj.hom g := by
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom]
  exact Over.pullbackCompIsoOfEq_conj_left_fst h β.hom

/-- Associativity of `pullbackCompIsoOfEq.inv`: decomposing `pullback fgh` via `fg ≫ h = fgh`
and `f ≫ g = fg` agrees with decomposing via `f ≫ gh = fgh` and `g ≫ h = gh`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_comp_inv_app {W : Scheme.{u}} {f : W ⟶ U} {g : U ⟶ T} {h : T ⟶ S}
    {fg : W ⟶ T} {gh : U ⟶ S} {fgh : W ⟶ S}
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh₁ : f ≫ gh = fgh) (hfgh₂ : fg ≫ h = fgh)
    (X : FiniteEtaleScheme S) :
    (pullbackCompIsoOfEq fg h fgh hfgh₂).inv.app X ≫
        (pullbackCompIsoOfEq f g fg hfg).inv.app ((pullback h).obj X) =
      (pullbackCompIsoOfEq f gh fgh hfgh₁).inv.app X ≫
        (pullback f).map ((pullbackCompIsoOfEq g h gh hgh).inv.app X) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullback_map_hom]
  exact Over.pullbackCompIsoOfEq_comp_inv_app hfg hgh hfgh₁ hfgh₂ X.obj

/-- Associativity of `pullbackCompIsoOfEq.hom`: composing `pullbackCompIsoOfEq f g fg` and
`pullbackCompIsoOfEq fg h fgh` agrees with `pullbackCompIsoOfEq g h gh` and
`pullbackCompIsoOfEq f gh fgh`. -/
@[reassoc]
theorem pullbackCompIsoOfEq_comp_hom_app {W : Scheme.{u}} {f : W ⟶ U} {g : U ⟶ T} {h : T ⟶ S}
    {fg : W ⟶ T} {gh : U ⟶ S} {fgh : W ⟶ S}
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh₁ : f ≫ gh = fgh) (hfgh₂ : fg ≫ h = fgh)
    (X : FiniteEtaleScheme S) :
    (pullbackCompIsoOfEq f g fg hfg).hom.app ((pullback h).obj X) ≫
        (pullbackCompIsoOfEq fg h fgh hfgh₂).hom.app X =
      (pullback f).map ((pullbackCompIsoOfEq g h gh hgh).hom.app X) ≫
        (pullbackCompIsoOfEq f gh fgh hfgh₁).hom.app X := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_hom_app_hom,
    pullback_map_hom]
  exact Over.pullbackCompIsoOfEq_comp_hom_app hfg hgh hfgh₁ hfgh₂ X.obj

/-- Conjugating a morphism between pullbacks of finite étale schemes along `m₂` and then along
`m₁` agrees with conjugating along `m = m₁ ≫ m₂`. -/
theorem pullbackCompIsoOfEq_conj_comp {A B D S₁ S₂ : Scheme.{u}}
    {m₁ : A ⟶ B} {m₂ : B ⟶ D} {m : A ⟶ D}
    {g₁ : D ⟶ S₁} {g₂ : D ⟶ S₂} {b₁ : B ⟶ S₁} {b₂ : B ⟶ S₂} {a₁ : A ⟶ S₁} {a₂ : A ⟶ S₂}
    (hm : m₁ ≫ m₂ = m) (hm₂₁ : m₂ ≫ g₁ = b₁) (hm₂₂ : m₂ ≫ g₂ = b₂)
    (hm₁₁ : m₁ ≫ b₁ = a₁) (hm₁₂ : m₁ ≫ b₂ = a₂) (ha₁ : m ≫ g₁ = a₁) (ha₂ : m ≫ g₂ = a₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    (pullbackCompIsoOfEq m₁ b₁ a₁ hm₁₁).inv.app Y₁ ≫
        (pullback m₁).map ((pullbackCompIsoOfEq m₂ g₁ b₁ hm₂₁).inv.app Y₁ ≫
          (pullback m₂).map φ ≫ (pullbackCompIsoOfEq m₂ g₂ b₂ hm₂₂).hom.app Y₂) ≫
        (pullbackCompIsoOfEq m₁ b₂ a₂ hm₁₂).hom.app Y₂ =
      (pullbackCompIsoOfEq m g₁ a₁ ha₁).inv.app Y₁ ≫ (pullback m).map φ ≫
        (pullbackCompIsoOfEq m g₂ a₂ ha₂).hom.app Y₂ := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom]
  exact Over.pullbackCompIsoOfEq_conj_comp hm hm₂₁ hm₂₂ hm₁₁ hm₁₂ ha₁ ha₂ φ.hom

/-- Conjugating a morphism between pullbacks of finite étale schemes along a morphism equal to
the identity recovers the morphism. -/
theorem pullbackCompIsoOfEq_conj_of_eq_id {B S₁ S₂ : Scheme.{u}} {m : B ⟶ B} (hm : m = 𝟙 B)
    {g₁ : B ⟶ S₁} {g₂ : B ⟶ S₂} (h₁ : m ≫ g₁ = g₁) (h₂ : m ≫ g₂ = g₂)
    {Y₁ : FiniteEtaleScheme S₁} {Y₂ : FiniteEtaleScheme S₂}
    (φ : (pullback g₁).obj Y₁ ⟶ (pullback g₂).obj Y₂) :
    (pullbackCompIsoOfEq m g₁ g₁ h₁).inv.app Y₁ ≫ (pullback m).map φ ≫
        (pullbackCompIsoOfEq m g₂ g₂ h₂).hom.app Y₂ = φ := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullbackCompIsoOfEq_hom_app_hom, pullback_map_hom]
  exact Over.pullbackCompIsoOfEq_conj_of_eq_id hm h₁ h₂ φ.hom

/-- Projection cancellation for an isomorphism `e : (pullback j).obj V' ≅ V` of finite étale
schemes transported along `pullbackCompIsoOfEq f j ij h`. -/
theorem pullbackCompIsoOfEq_inv_map_hom_fst_inv_fst
    {Inf U UW : Scheme.{u}} {f : Inf ⟶ U} {j : U ⟶ UW} {ij : Inf ⟶ UW}
    (h : f ≫ j = ij) {V' : FiniteEtaleScheme UW} {V : FiniteEtaleScheme U}
    (e : (pullback j).obj V' ≅ V) :
    ((pullbackCompIsoOfEq f j ij h).inv.app V' ≫ (pullback f).map e.hom).hom.left ≫
        Limits.pullback.fst V.obj.hom f ≫ e.inv.hom.left ≫ Limits.pullback.fst V'.obj.hom j =
      Limits.pullback.fst V'.obj.hom ij := by
  let eOver : (Over.pullback j).obj V'.obj ≅ V.obj :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congr(($e.hom_inv_id).hom)
      inv_hom_id := congr(($e.inv_hom_id).hom) }
  simp only [ObjectProperty.FullSubcategory.comp_hom, pullbackCompIsoOfEq_inv_app_hom,
    pullback_map_hom]
  exact Over.pullbackCompIsoOfEq_inv_map_hom_fst_inv_fst h eOver

end CompIsoOfEq

/-- Base change of finite étale schemes along a scheme isomorphism is an equivalence, with unit and
counit given directly by `pullbackId` and `pullbackComp`. -/
noncomputable def pullbackIsoEquiv (e : T ≅ S) :
    FiniteEtaleScheme S ≌ FiniteEtaleScheme T where
  functor := pullback e.hom
  inverse := pullback e.inv
  unitIso := pullbackId.symm ≪≫ eqToIso (congrArg pullback e.inv_hom_id.symm) ≪≫
    pullbackComp e.inv e.hom
  counitIso := (pullbackComp e.hom e.inv).symm ≪≫ eqToIso (congrArg pullback e.hom_inv_id) ≪≫
    pullbackId
  functor_unitIso_comp X := by
    apply ObjectProperty.hom_ext
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom, pullbackId_inv_app_hom,
      pullbackId_hom_app_hom, pullbackComp_hom_app_hom, pullbackComp_inv_app_hom,
      ObjectProperty.FullSubcategory.id_hom]
    rw [eqToIso_congrArg_pullback_hom_app_hom e.inv_hom_id.symm,
      eqToIso_congrArg_pullback_hom_app_hom e.hom_inv_id]
    exact Over.pullback_iso_triangle e X.obj

/-- The forward functor of `pullbackIsoEquiv e` is base change along `e.hom`. -/
@[simp]
theorem pullbackIsoEquiv_functor (e : T ≅ S) :
    (pullbackIsoEquiv e).functor = pullback e.hom :=
  (rfl)

/-- The inverse functor of `pullbackIsoEquiv e` is base change along `e.inv`. -/
@[simp]
theorem pullbackIsoEquiv_inverse (e : T ≅ S) :
    (pullbackIsoEquiv e).inverse = pullback e.inv :=
  (rfl)

/-- The unit of `pullbackIsoEquiv e` is built from `pullbackId` and `pullbackComp e.inv e.hom`. -/
@[simp]
theorem pullbackIsoEquiv_unitIso (e : T ≅ S) :
    (pullbackIsoEquiv e).unitIso ≪≫ eqToIso (by
      rw [pullbackIsoEquiv_functor, pullbackIsoEquiv_inverse]) =
      pullbackId.symm ≪≫ eqToIso (congrArg pullback e.inv_hom_id.symm) ≪≫
        pullbackComp e.inv e.hom := by
  apply Iso.ext; apply NatTrans.ext; funext X
  exact Category.comp_id _

/-- The counit of `pullbackIsoEquiv e` is built from `pullbackComp e.hom e.inv` and `pullbackId`. -/
@[simp]
theorem pullbackIsoEquiv_counitIso (e : T ≅ S) :
    eqToIso (by rw [pullbackIsoEquiv_functor, pullbackIsoEquiv_inverse]) ≪≫
      (pullbackIsoEquiv e).counitIso =
      (pullbackComp e.hom e.inv).symm ≪≫ eqToIso (congrArg pullback e.hom_inv_id) ≪≫
        pullbackId := by
  apply Iso.ext; apply NatTrans.ext; funext X
  exact Category.id_comp _

/-- Base change of finite étale schemes along an isomorphism is an equivalence of categories. -/
instance isEquivalence_pullback (f : T ⟶ S) [IsIso f] : (pullback f).IsEquivalence := by
  rw [← asIso_hom f, ← pullbackIsoEquiv_functor]
  exact (pullbackIsoEquiv (asIso f)).isEquivalence_functor

/-- Faithfulness of `FiniteEtaleScheme.pullback` composes along any factorization `h ≫ f = g` of
base morphisms. -/
theorem faithful_pullback_of_fac (h : T ⟶ S) (f : S ⟶ U) (g : T ⟶ U) (hfac : h ≫ f = g)
    [(pullback h).Faithful] [(pullback f).Faithful] : (pullback g).Faithful :=
  Functor.Faithful.of_iso (eqToIso (congrArg pullback hfac.symm) ≪≫ pullbackComp h f).symm

/-- Fullness of `FiniteEtaleScheme.pullback` composes along any factorization `h ≫ f = g` of base
morphisms. -/
theorem full_pullback_of_fac (h : T ⟶ S) (f : S ⟶ U) (g : T ⟶ U) (hfac : h ≫ f = g)
    [(pullback h).Full] [(pullback f).Full] : (pullback g).Full :=
  Functor.Full.of_iso (eqToIso (congrArg pullback hfac.symm) ≪≫ pullbackComp h f).symm

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre functor at a geometric point `x : Spec Ω ⟶ S`, for `Ω` separably
closed: a finite étale `S`-scheme `X` goes to the finite set classifying `X ×_S Spec Ω`. -/
@[expose] noncomputable def fiber (x : Spec (.of Ω) ⟶ S) : FiniteEtaleScheme S ⥤ FintypeCat.{u} :=
  pullback x ⋙ (equivOfIsSepClosed Ω).functor

/-- The geometric fibre functor is base change to the geometric point followed by the
classification of finite étale schemes over a separably closed field. -/
theorem fiber_def (x : Spec (.of Ω) ⟶ S) :
    fiber x = pullback x ⋙ (equivOfIsSepClosed Ω).functor :=
  (rfl)

/-- The geometric fibre functor at `x` is corepresented by `x`: the fibre of `X` is naturally
the set of lifts of `x` to `X`, that is, of morphisms `Over.mk x ⟶ X` over `S`. -/
noncomputable def fiberCompInclIso (x : Spec (.of Ω) ⟶ S) :
    fiber x ⋙ FintypeCat.incl ≅
      (finiteEtaleSchemeProperty S).ι ⋙ coyoneda.obj (op (Over.mk x)) :=
  Iso.symm <| Functor.isoWhiskerLeft _
      (coyoneda.mapIso (Over.isoMk (Iso.refl _) :
          (Over.map x).obj (Over.mk (𝟙 _)) ≅ Over.mk x).op ≪≫
        (Over.mapPullbackAdj x).compCoyonedaIso.app (op (Over.mk (𝟙 _)))) ≪≫
    Functor.isoWhiskerLeft (pullback x) (equivOfIsSepClosedFunctorCompInclIso Ω).symm

/-- A lift `g : Over.mk x ⟶ X` of the geometric point `x` gives the point of the fibre
corresponding, under `equivOfIsSepClosedFunctorCompInclIso`, to the section of `X ×_S Spec Ω`
adjoint to `g` under `Over.map x ⊣ Over.pullback x`. -/
theorem fiberCompInclIso_inv_app_apply (x : Spec (.of Ω) ⟶ S) (X : FiniteEtaleScheme S)
    (g : Over.mk x ⟶ X.obj) :
    (fiberCompInclIso x).inv.app X g =
      (equivOfIsSepClosedFunctorCompInclIso Ω).inv.app ((pullback x).obj X)
        ((Over.mapPullbackAdj x).homEquiv _ _ (Over.homMk (𝟙 _) ≫ g)) :=
  (rfl)

/-- A point `y` of the fibre gives the lift of `x` adjoint, under `Over.map x ⊣ Over.pullback x`,
to the section of `X ×_S Spec Ω` corresponding to `y` under
`equivOfIsSepClosedFunctorCompInclIso`. -/
theorem fiberCompInclIso_hom_app_apply (x : Spec (.of Ω) ⟶ S) (X : FiniteEtaleScheme S)
    (y : (fiber x).obj X) :
    (fiberCompInclIso x).hom.app X y =
      Over.homMk (𝟙 _) ≫ ((Over.mapPullbackAdj x).homEquiv _ _).symm
        ((equivOfIsSepClosedFunctorCompInclIso Ω).hom.app ((pullback x).obj X) y) :=
  (rfl)

variable (Ω) in
/-- The geometric fibre functor of `Spec Ω` at its identity point is the classification of
finite étale schemes over the separably closed field `Ω` by finite sets. -/
noncomputable def fiberIdIso : fiber (𝟙 (Spec (.of Ω))) ≅ (equivOfIsSepClosed Ω).functor :=
  Functor.isoWhiskerRight pullbackId _ ≪≫ Functor.leftUnitor _

variable (Ω) in
/-- The components of `fiberIdIso` are the images of those of `pullbackId`. -/
@[simp]
theorem fiberIdIso_hom_app (X : FiniteEtaleScheme (Spec (.of Ω))) :
    (fiberIdIso Ω).hom.app X = (equivOfIsSepClosed Ω).functor.map (pullbackId.hom.app X) :=
  (rfl)

variable (Ω) in
/-- The components of `(fiberIdIso Ω).inv` are the images of those of `pullbackId.inv`. -/
@[simp]
theorem fiberIdIso_inv_app (X : FiniteEtaleScheme (Spec (.of Ω))) :
    (fiberIdIso Ω).inv.app X = (equivOfIsSepClosed Ω).functor.map (pullbackId.inv.app X) :=
  (rfl)

/-- Base change along `f : T ⟶ S` followed by the geometric fibre at `x : Spec Ω ⟶ T` is the
geometric fibre at the composite geometric point `x ≫ f`. -/
noncomputable def pullbackCompFiberIso (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T) :
    pullback f ⋙ fiber x ≅ fiber (x ≫ f) :=
  Functor.isoWhiskerRight (pullbackComp x f).symm _

/-- The components of `pullbackCompFiberIso` are the images of those of `pullbackComp`. -/
@[simp]
theorem pullbackCompFiberIso_hom_app (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T)
    (X : FiniteEtaleScheme S) :
    (pullbackCompFiberIso f x).hom.app X =
      (equivOfIsSepClosed Ω).functor.map ((pullbackComp x f).inv.app X) :=
  (rfl)

/-- The components of `(pullbackCompFiberIso f x).inv` are the images of those of
`pullbackComp`. -/
@[simp]
theorem pullbackCompFiberIso_inv_app (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T)
    (X : FiniteEtaleScheme S) :
    (pullbackCompFiberIso f x).inv.app X =
      (equivOfIsSepClosed Ω).functor.map ((pullbackComp x f).hom.app X) :=
  (rfl)

/-- Changing the geometric point along the identity: `pullbackCompFiberIso (𝟙 S) x` is the
geometric fibre of `pullbackId`, up to the equality `x ≫ 𝟙 S = x`. -/
@[reassoc]
theorem pullbackCompFiberIso_id_hom_app (x : Spec (.of Ω) ⟶ S) (X : FiniteEtaleScheme S) :
    (pullbackCompFiberIso (𝟙 S) x).hom.app X ≫
        eqToHom (congrArg (fun x ↦ (fiber x).obj X) (Category.comp_id x)) =
      (fiber x).map (pullbackId.hom.app X) := by
  -- The geometric fibre is base change followed by `(equivOfIsSepClosed Ω).functor`
  -- (`fiber_def`), so this is the image of `pullbackComp_id_inv_app_comp_eqToHom` under it.
  have := congrArg (equivOfIsSepClosed Ω).functor.map (pullbackComp_id_inv_app_comp_eqToHom x X)
  rw [Functor.map_comp, eqToHom_map] at this
  exact this

/-- Changing the geometric point along a composite `f ≫ g` is changing it along `f` and then
along `g`, up to the equality `x ≫ f ≫ g = (x ≫ f) ≫ g`. -/
@[reassoc]
theorem pullbackCompFiberIso_comp_hom_app (f : T ⟶ S) (g : S ⟶ U) (x : Spec (.of Ω) ⟶ T)
    (X : FiniteEtaleScheme U) :
    (pullbackCompFiberIso (f ≫ g) x).hom.app X ≫
        eqToHom (congrArg (fun x ↦ (fiber x).obj X) (Category.assoc x f g).symm) =
      (fiber x).map ((pullbackComp f g).hom.app X) ≫
        (pullbackCompFiberIso f x).hom.app ((pullback g).obj X) ≫
          (pullbackCompFiberIso g (x ≫ f)).hom.app X := by
  -- As above, this is the image of `pullbackComp_comp_inv_app_comp_eqToHom` under
  -- `(equivOfIsSepClosed Ω).functor`.
  have := congrArg (equivOfIsSepClosed Ω).functor.map
    (pullbackComp_comp_inv_app_comp_eqToHom x f g X)
  rw [Functor.map_comp, eqToHom_map, Functor.map_comp, Functor.map_comp] at this
  exact this

end TauCeti.FiniteEtaleScheme
