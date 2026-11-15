/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import TauCeti.CategoryTheory.Sites.LocallyBijective
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# Sheafifying a presheaf torsor

Let `G` be a sheaf of groups on a site `(C, J)`. A *pretorsor* under `G` is a presheaf of sets
`F` with a left action of `G` which is locally nonempty and on whose sections `G` acts simply
transitively, that is, `(g, x) ↦ (g • x, x)` is a bijection `G(U) × F(U) → F(U) × F(U)` for
every `U`. It differs from a `G`-torsor only in that `F` need not be a sheaf. Torsors are often
built as quotients of sheaves, such as the contracted product `P ×^G G'`, which are pretorsors
but not sheaves.

This file shows that the sheafification of a pretorsor is a `G`-torsor, and that it has the
universal property of sheafification among `G`-torsors. These results assume that presheaves of
sets on `C` with values in `Type w` can be sheafified and that the morphisms inverted by
sheafification are the locally bijective ones (`HasWeakSheafify J (Type w)` and
`J.WEqualsLocallyBijective (Type w)`); Mathlib provides both when `w = max u v`.

## Main declarations

* `CategoryTheory.Sheaf.PreTorsor G`: a pretorsor under `G`.
* `CategoryTheory.Sheaf.PreTorsor.sheafify`: the `G`-torsor obtained by sheafifying a pretorsor.
  The action of `G` is the sheafification of the action map `G × F → F`, using that
  sheafification commutes with the product with the sheaf `G`.
* `CategoryTheory.Sheaf.PreTorsor.toSheafify_smul`: the map from a pretorsor to its
  sheafification is `G`-equivariant.
* `CategoryTheory.Sheaf.PreTorsor.sheafifyLift`: a `G`-equivariant morphism from a pretorsor to
  a `G`-torsor induces a morphism of `G`-torsors from the sheafification.

## References

* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.4, for torsors as sheafifications of
  presheaves with a simply transitive action.
-/

public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A pretorsor under a sheaf of groups `G`: a presheaf of sets with a left action of `G` which
is locally nonempty and on whose sections `G` acts simply transitively. Its sheafification is a
`G`-torsor, see `PreTorsor.sheafify`. -/
structure PreTorsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying presheaf of sets. -/
  presheaf : Cᵒᵖ ⥤ Type w
  /-- The action of the sections of `G` on the sections of the presheaf. -/
  [mulAction (U : Cᵒᵖ) : MulAction (G.obj.obj U) (presheaf.obj U)]
  /-- The action commutes with restriction. -/
  map_smul ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (g : G.obj.obj U) (x : presheaf.obj U) :
    presheaf.map f (g • x) = G.obj.map f g • presheaf.map f x
  /-- The presheaf is locally nonempty: the objects over which it has a section cover the
  site. -/
  coversTop : J.CoversTop fun U : {U : C // Nonempty (presheaf.obj (op U))} ↦ U.1
  /-- The action is simply transitive: `(g, x) ↦ (g • x, x)` is a bijection on sections. -/
  bijective (U : Cᵒᵖ) :
    Function.Bijective fun x : G.obj.obj U × presheaf.obj U ↦ (x.1 • x.2, x.2)

attribute [instance] PreTorsor.mulAction

namespace PreTorsor

variable {G : Sheaf J GrpCat.{w}} (F : PreTorsor G)

/-- The action of `G` on a pretorsor, as a morphism of presheaves `G × F → F`. -/
private def act : (G.obj ⋙ forget GrpCat) ⊗ F.presheaf ⟶ F.presheaf where
  app U := ↾fun x : G.obj.obj U × F.presheaf.obj U ↦ x.1 • x.2
  naturality U V f := by
    ext x
    exact (F.map_smul f x.1 x.2).symm

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- The map from `G × F` to `G × F^#` is locally bijective, so it becomes an isomorphism after
sheafification. -/
private lemma W_whiskerLeft_toSheafify :
    J.W (𝟙 (G.obj ⋙ forget GrpCat) ⊗ₘ CategoryTheory.toSheafify J F.presheaf) :=
  J.W_of_isLocallyBijective _

/-- The action of `G` on the sheafification of a pretorsor, as a morphism of presheaves: the
unique extension of the action map along the map from `G × F` to `G × F^#`. -/
private def sheafifyAct :
    (G.obj ⋙ forget GrpCat) ⊗ CategoryTheory.sheafify J F.presheaf ⟶
      CategoryTheory.sheafify J F.presheaf :=
  (F.W_whiskerLeft_toSheafify.homEquiv _
    ((presheafToSheaf J (Type w)).obj F.presheaf).property).symm
      (F.act ≫ CategoryTheory.toSheafify J F.presheaf)

private lemma sheafifyAct_spec :
    (𝟙 (G.obj ⋙ forget GrpCat) ⊗ₘ CategoryTheory.toSheafify J F.presheaf) ≫
      F.sheafifyAct = F.act ≫ CategoryTheory.toSheafify J F.presheaf :=
  (F.W_whiskerLeft_toSheafify.homEquiv _
    ((presheafToSheaf J (Type w)).obj F.presheaf).property).apply_symm_apply _

/-- The action of a section of `G` on a section of the sheafification of a pretorsor. -/
private def smul {U : Cᵒᵖ} (g : G.obj.obj U)
    (q : (CategoryTheory.sheafify J F.presheaf).obj U) :
    (CategoryTheory.sheafify J F.presheaf).obj U :=
  F.sheafifyAct.app U (g, q)

private lemma smul_toSheafify {U : Cᵒᵖ} (g : G.obj.obj U) (x : F.presheaf.obj U) :
    F.smul g ((CategoryTheory.toSheafify J F.presheaf).app U x) =
      (CategoryTheory.toSheafify J F.presheaf).app U (g • x) :=
  congrArg (fun φ ↦ φ.app U (g, x)) F.sheafifyAct_spec

private lemma map_smul' {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U)
    (q : (CategoryTheory.sheafify J F.presheaf).obj U) :
    (CategoryTheory.sheafify J F.presheaf).map f (F.smul g q) =
      F.smul (G.obj.map f g) ((CategoryTheory.sheafify J F.presheaf).map f q) :=
  (NatTrans.naturality_apply F.sheafifyAct f _).symm

private lemma one_smul' {U : Cᵒᵖ} (q : (CategoryTheory.sheafify J F.presheaf).obj U) :
    F.smul 1 q = q :=
  Presheaf.ext_of_isLocallySurjective J (CategoryTheory.toSheafify J F.presheaf)
    (Z := (presheafToSheaf J (Type w)).obj F.presheaf) q fun V f x hx ↦ by
    rw [F.map_smul', map_one, ← hx, smul_toSheafify, one_smul]

private lemma mul_smul' {U : Cᵒᵖ} (g h : G.obj.obj U)
    (q : (CategoryTheory.sheafify J F.presheaf).obj U) :
    F.smul (g * h) q = F.smul g (F.smul h q) :=
  Presheaf.ext_of_isLocallySurjective J (CategoryTheory.toSheafify J F.presheaf)
    (Z := (presheafToSheaf J (Type w)).obj F.presheaf) q fun V f x hx ↦ by
    rw [F.map_smul', F.map_smul', F.map_smul', map_mul, ← hx, smul_toSheafify, smul_toSheafify,
      smul_toSheafify, mul_smul]

/-- The map `(g, q) ↦ (g • q, q)` on the sheafification is objectwise bijective: it is a locally
bijective morphism of sheaves, because it extends the corresponding bijective map on `F`. -/
private lemma bijective_sheafify (U : Cᵒᵖ) :
    Function.Bijective fun x : G.obj.obj U × (CategoryTheory.sheafify J F.presheaf).obj U ↦
      (F.smul x.1 x.2, x.2) := by
  let βF : (G.obj ⋙ forget GrpCat) ⊗ F.presheaf ⟶ F.presheaf ⊗ F.presheaf :=
    lift F.act (snd _ _)
  let β : (G.obj ⋙ forget GrpCat) ⊗ CategoryTheory.sheafify J F.presheaf ⟶
      CategoryTheory.sheafify J F.presheaf ⊗ CategoryTheory.sheafify J F.presheaf :=
    lift F.sheafifyAct (snd _ _)
  have fac : (𝟙 (G.obj ⋙ forget GrpCat) ⊗ₘ CategoryTheory.toSheafify J F.presheaf) ≫ β =
      βF ≫ (CategoryTheory.toSheafify J F.presheaf ⊗ₘ
        CategoryTheory.toSheafify J F.presheaf) := by
    ext V ⟨g, x⟩
    · exact F.smul_toSheafify g x
    · rfl
  have : Presheaf.IsLocallyInjective J βF :=
    Presheaf.isLocallyInjective_of_injective _ _ fun V ↦ (F.bijective V).1
  have : Presheaf.IsLocallySurjective J βF :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun V ↦ (F.bijective V).2
  have hinj : Presheaf.IsLocallyInjective J β :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J _ fac
  have hsurj : Presheaf.IsLocallySurjective J β :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J fac
  let Q := (presheafToSheaf J (Type w)).obj F.presheaf
  let s : (sheafCompose J (forget GrpCat)).obj G ⊗ Q ⟶ Q ⊗ Q :=
    ObjectProperty.homMk β
  have : IsIso s := (Sheaf.isLocallyBijective_iff_isIso (A := Type w) s).1
    ⟨hinj, hsurj⟩
  exact (isIso_iff_bijective (s.hom.app U)).1 inferInstance

/-- The sheafification of a pretorsor is a torsor. Use `toSheafify_smul` and `sheafifyLift`
rather than unfolding it. -/
def sheafify : Torsor G where
  sheaf := (presheafToSheaf J (Type w)).obj F.presheaf
  mulAction U :=
    { smul := F.smul
      one_smul := F.one_smul'
      mul_smul := F.mul_smul' }
  map_smul U V f g q := F.map_smul' f g q
  coversTop X := J.superset_covering (by
    rintro Y a ⟨⟨V, ⟨x⟩⟩, ⟨b⟩⟩
    exact ⟨⟨V, ⟨(CategoryTheory.toSheafify J F.presheaf).app _ x⟩⟩, ⟨b⟩⟩)
    (F.coversTop X)
  bijective := F.bijective_sheafify

/-- The underlying sheaf of the sheafification of a pretorsor is the sheafification of its
underlying presheaf. -/
lemma sheafify_sheaf : F.sheafify.sheaf = (presheafToSheaf J (Type w)).obj F.presheaf :=
  (rfl)

/-- The map from a pretorsor to its sheafification. -/
def toSheafify : F.presheaf ⟶ F.sheafify.sheaf.obj :=
  CategoryTheory.toSheafify J F.presheaf

/-- The map from a pretorsor to its sheafification is locally injective. -/
instance isLocallyInjective_toSheafify : Presheaf.IsLocallyInjective J F.toSheafify :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J F.presheaf))

/-- The map from a pretorsor to its sheafification is locally surjective. -/
instance isLocallySurjective_toSheafify : Presheaf.IsLocallySurjective J F.toSheafify :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J F.presheaf))

/-- The map from a pretorsor to its sheafification is `G`-equivariant. -/
@[simp]
lemma toSheafify_smul {U : Cᵒᵖ} (g : G.obj.obj U) (x : F.presheaf.obj U) :
    F.toSheafify.app U (g • x) = g • F.toSheafify.app U x :=
  (F.smul_toSheafify g x).symm

/-- Morphisms of torsors out of the sheafification of a pretorsor are determined by their
composite with the map from the pretorsor. -/
lemma sheafify_hom_ext {R : Torsor G} {f f' : F.sheafify ⟶ R}
    (h : F.toSheafify ≫ f.hom.hom = F.toSheafify ≫ f'.hom.hom) : f = f' :=
  Torsor.hom_ext (ObjectProperty.hom_ext _
    (CategoryTheory.sheafify_hom_ext J _ _ R.sheaf.property h))

/-- A `G`-equivariant morphism from a pretorsor to (the underlying presheaf of) a torsor extends
to a morphism of torsors from the sheafification of the pretorsor. -/
def sheafifyLift {R : Torsor G} (ρ : F.presheaf ⟶ R.sheaf.obj)
    (hρ : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (x : F.presheaf.obj U),
      ρ.app U (g • x) = g • ρ.app U x) :
    F.sheafify ⟶ R where
  hom := ObjectProperty.homMk (CategoryTheory.sheafifyLift J ρ R.sheaf.property)
  map_smul U g q := by
    have hρ' (V : Cᵒᵖ) (x : F.presheaf.obj V) :
        (CategoryTheory.sheafifyLift J ρ R.sheaf.property).app V (F.toSheafify.app V x) =
          ρ.app V x :=
      congrArg (fun φ ↦ φ.app V x)
        (CategoryTheory.toSheafify_sheafifyLift J ρ R.sheaf.property)
    refine Presheaf.ext_of_isLocallySurjective J F.toSheafify q fun V f x hx ↦ ?_
    rw [R.map_smul, ← NatTrans.naturality_apply,
      ← NatTrans.naturality_apply, F.sheafify.map_smul, ← hx, ← toSheafify_smul]
    exact (hρ' _ _).trans ((hρ _ _ _).trans (congrArg _ (hρ' _ _).symm))

/-- The morphism induced by an equivariant `ρ : F → R` restricts to `ρ` along the map from `F`
to its sheafification. -/
@[reassoc (attr := simp)]
lemma toSheafify_sheafifyLift {R : Torsor G} (ρ : F.presheaf ⟶ R.sheaf.obj)
    (hρ : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (x : F.presheaf.obj U),
      ρ.app U (g • x) = g • ρ.app U x) :
    F.toSheafify ≫ (F.sheafifyLift ρ hρ).hom.hom = ρ :=
  CategoryTheory.toSheafify_sheafifyLift J ρ R.sheaf.property

/-- Elementwise form of `toSheafify_sheafifyLift`. -/
@[simp]
lemma sheafifyLift_hom_app_toSheafify {R : Torsor G} (ρ : F.presheaf ⟶ R.sheaf.obj)
    (hρ : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (x : F.presheaf.obj U),
      ρ.app U (g • x) = g • ρ.app U x)
    {U : Cᵒᵖ} (x : F.presheaf.obj U) :
    (F.sheafifyLift ρ hρ).hom.hom.app U (F.toSheafify.app U x) = ρ.app U x :=
  congrArg (fun φ ↦ φ.app U x) (F.toSheafify_sheafifyLift ρ hρ)

end PreTorsor

end CategoryTheory.Sheaf
