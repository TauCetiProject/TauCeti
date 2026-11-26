/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.CategoryTheory.QuotientPresheaf

/-!
# The quotient sheaf of a pre-relation on a site

Let `J` be a subcanonical Grothendieck topology on a category `C`, and let `s t : R ⟶ U` be a
pair of morphisms of `C`, a *pre-relation* on `U`: a `T`-point `r` of `R` relates `t r` to `s r`.
The *quotient sheaf* `U/R` is the `J`-sheafification of the presheaf coequaliser
`T ↦ U(T)/R(T)`, which is `TauCeti.CategoryTheory.quotientPresheaf s t`. For schemes and the fppf
topology this is Stacks, Definition 39.20.1 (02VG). This file constructs it with its projection
`π : h_U ⟶ U/R`, shows that `π` is the coequaliser of `h_R ⇉ h_U` in `J`-sheaves, and shows that
`R` is the kernel pair of `π` when `(t, s)` is an equivalence relation (for schemes and the fppf
topology, Stacks, Lemma 39.20.4 (045Y), together with the injectivity of `R ⟶ U × U`).

The quotient sheaf takes values in `Type (max v w)` and the representable sheaves are the
universe-lifted ones `J.uliftYoneda.{w}`, so that the construction applies to large sites such as
the big fppf site of `Scheme.{u}`, where Mathlib's sheafification lands in `Type (u + 1)`.

## Main definitions

* `TauCeti.CategoryTheory.quotientSheaf J s t`: the `J`-sheafification `U/R` of the presheaf
  quotient.
* `TauCeti.CategoryTheory.quotientSheaf.π J s t`: the projection `h_U ⟶ U/R`.
* `TauCeti.CategoryTheory.quotientSheaf.desc`: the factorisation of an `R`-invariant map
  `h_U ⟶ F` to a `J`-sheaf through `U/R`.

## Main results

* `TauCeti.CategoryTheory.quotientSheaf.isColimit`: `π` is the coequaliser of `h_R ⇉ h_U` in
  `J`-sheaves.
* `TauCeti.CategoryTheory.quotientSheaf.isLocallySurjective_π`: `π` is `J`-locally surjective.
* `TauCeti.CategoryTheory.quotientSheaf.isIso_π_self`: for the pre-relation `(s, s)`, `π` is an
  isomorphism, with inverse `TauCeti.CategoryTheory.quotientSheaf.inv_π_self`.
* `TauCeti.CategoryTheory.quotientSheaf.kernelPair`: for an equivalence relation, `h_R ⇉ h_U` is
  the kernel pair of `π`, that is, `h_R = h_U ×_{U/R} h_U`.

## Implementation notes

The kernel pair is computed in presheaves, where it is
`TauCeti.CategoryTheory.quotientPresheaf.isKernelPair_uliftπ`, and carried to sheaves because
sheafification preserves finite limits. For schemes and the fppf topology this replaces the local
argument of Stacks, Lemma 39.20.4.

## References

* [Stacks Project, Definition 39.20.1](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Lemma 39.20.4](https://stacks.math.columbia.edu/tag/045Y)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type (max v w))] {R U : C} (s t : R ⟶ U)

/-- The quotient sheaf `U/R` of a pre-relation `s t : R ⟶ U`: the `J`-sheafification of the
presheaf quotient `T ↦ U(T)/R(T)`, lifted to `Type (max v w)` (for schemes and the fppf topology,
Stacks, Definition 39.20.1 (02VG)). -/
noncomputable abbrev quotientSheaf : Sheaf J (Type (max v w)) :=
  (presheafToSheaf J (Type (max v w))).obj (quotientPresheaf s t ⋙ uliftFunctor.{w})

variable [J.Subcanonical]

/-- The projection `π : h_U ⟶ U/R` onto the quotient sheaf, sending a `T`-point of `U` to its
class. -/
noncomputable def quotientSheaf.π : J.uliftYoneda.{w}.obj U ⟶ quotientSheaf.{w} J s t :=
  (sheafificationIso (J.uliftYoneda.{w}.obj U)).hom ≫
    (presheafToSheaf J (Type (max v w))).map (quotientPresheaf.uliftπ.{w} s t)

/-- On underlying presheaves, the projection onto the quotient sheaf is the projection onto the
presheaf quotient followed by the unit of sheafification. -/
theorem quotientSheaf.π_hom :
    (quotientSheaf.π.{w} J s t).hom = quotientPresheaf.uliftπ.{w} s t ≫ toSheafify J _ := by
  rw [quotientSheaf.π, ObjectProperty.FullSubcategory.comp_hom, sheafificationIso_hom_hom,
    isoSheafify_hom]
  exact (toSheafify_naturality J (quotientPresheaf.uliftπ.{w} s t)).symm

/-- The projection onto the quotient sheaf coequalises `h_R ⇉ h_U`. -/
@[reassoc]
theorem quotientSheaf.condition :
    J.uliftYoneda.{w}.map t ≫ quotientSheaf.π.{w} J s t =
      J.uliftYoneda.{w}.map s ≫ quotientSheaf.π.{w} J s t := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, quotientSheaf.π_hom]
  exact quotientPresheaf.uliftπ_condition_assoc.{w} s t _

variable {J s t}

/-- A morphism `φ : h_U ⟶ F` to a `J`-sheaf which agrees on `t r` and `s r` for every point `r`
of `R` factors through the quotient sheaf. -/
noncomputable def quotientSheaf.desc {F : Sheaf J (Type (max v w))}
    (φ : J.uliftYoneda.{w}.obj U ⟶ F)
    (hφ : J.uliftYoneda.{w}.map t ≫ φ = J.uliftYoneda.{w}.map s ≫ φ) :
    quotientSheaf.{w} J s t ⟶ F :=
  ObjectProperty.homMk <| sheafifyLift J
    (quotientPresheaf.uliftDesc.{w} φ.hom (congrArg (·.hom) hφ)) F.property

/-- The factorisation through the quotient sheaf is the sheafified lift of the factorisation
through the universe-lifted presheaf quotient. -/
theorem quotientSheaf.desc_def {F : Sheaf J (Type (max v w))}
    (φ : J.uliftYoneda.{w}.obj U ⟶ F)
    (hφ : J.uliftYoneda.{w}.map t ≫ φ = J.uliftYoneda.{w}.map s ≫ φ) :
    quotientSheaf.desc φ hφ = ObjectProperty.homMk (sheafifyLift J
      (quotientPresheaf.uliftDesc.{w} φ.hom (congrArg (·.hom) hφ)) F.property) :=
  (rfl)

/-- The factorisation through the quotient sheaf, composed with the projection, is the original
morphism. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.π_desc {F : Sheaf J (Type (max v w))}
    (φ : J.uliftYoneda.{w}.obj U ⟶ F)
    (hφ : J.uliftYoneda.{w}.map t ≫ φ = J.uliftYoneda.{w}.map s ≫ φ) :
    quotientSheaf.π J s t ≫ quotientSheaf.desc φ hφ = φ := by
  ext1
  rw [ObjectProperty.FullSubcategory.comp_hom, quotientSheaf.π_hom]
  refine (Category.assoc _ _ _).trans ?_
  rw [quotientSheaf.desc_def, ObjectProperty.homMk_hom, toSheafify_sheafifyLift]
  exact quotientPresheaf.uliftπ_uliftDesc.{w} _ _

/-- Morphisms out of the quotient sheaf agree when they agree after the projection. -/
theorem quotientSheaf.hom_ext {F : Sheaf J (Type (max v w))}
    {f g : quotientSheaf.{w} J s t ⟶ F}
    (hfg : quotientSheaf.π J s t ≫ f = quotientSheaf.π J s t ≫ g) : f = g := by
  ext1
  refine sheafify_hom_ext _ _ _ F.property (quotientPresheaf.uliftπ_hom_ext.{w} s t ?_)
  have h := congrArg (·.hom) hfg
  simp only [ObjectProperty.FullSubcategory.comp_hom, quotientSheaf.π_hom] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

variable (J s t) in
/-- The quotient sheaf is the coequaliser of `h_R ⇉ h_U` in `J`-sheaves. -/
noncomputable def quotientSheaf.isColimit :
    IsColimit (Cofork.ofπ (quotientSheaf.π.{w} J s t) (quotientSheaf.condition J s t)) :=
  Cofork.IsColimit.mk' _ fun c ↦ ⟨quotientSheaf.desc c.π c.condition,
    quotientSheaf.π_desc _ _, fun hm ↦ quotientSheaf.hom_ext (by simpa using hm)⟩

/-- The projection onto the quotient sheaf is an epimorphism of `J`-sheaves. -/
instance quotientSheaf.epi_π : Epi (quotientSheaf.π.{w} J s t) :=
  ⟨fun _ _ h ↦ quotientSheaf.hom_ext h⟩

/-- For the pre-relation `(s, s)`, which relates each point only to itself, the projection
`h_U ⟶ U/R` is an isomorphism: the quotient sheaf is `h_U`. -/
instance quotientSheaf.isIso_π_self : IsIso (quotientSheaf.π.{w} J s s) :=
  isIso_colimit_cocone_parallelPair_of_self (quotientSheaf.isColimit.{w} J s s)

/-- For the pre-relation `(s, s)`, the inverse of the projection `h_U ⟶ U/R` is the factorisation
of the identity of `h_U` through the quotient sheaf. -/
@[simp]
theorem quotientSheaf.inv_π_self :
    inv (quotientSheaf.π.{w} J s s) = quotientSheaf.desc (𝟙 _) rfl :=
  IsIso.inv_eq_of_hom_inv_id (quotientSheaf.π_desc _ _)

/-- For the pre-relation `(s, s)`, the factorisation of the identity of `h_U` through the quotient
sheaf, composed with the projection, is the identity of `U/R`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.desc_π_self :
    quotientSheaf.desc (𝟙 _) rfl ≫ quotientSheaf.π.{w} J s s = 𝟙 _ := by
  rw [← quotientSheaf.inv_π_self, IsIso.inv_hom_id]

/-- The projection onto the quotient sheaf is `J`-locally surjective: every section of `U/R` is,
`J`-locally, the class of a point of `U`. -/
theorem quotientSheaf.isLocallySurjective_π [HasSheafify J (Type (max v w))] :
    Sheaf.IsLocallySurjective (quotientSheaf.π.{w} J s t) :=
  (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance

/-- For an equivalence relation `(t, s)`, `h_R ⇉ h_U` is the kernel pair of the projection onto
the quotient sheaf: `h_R = h_U ×_{U/R} h_U` (for schemes and the fppf topology, Stacks,
Lemma 39.20.4 (045Y), and the injectivity of `R ⟶ U × U`). -/
theorem quotientSheaf.kernelPair [HasSheafify J (Type (max v w))]
    (h : IsEquivalenceRelation t s) :
    IsKernelPair (quotientSheaf.π.{w} J s t) (J.uliftYoneda.{w}.map t)
      (J.uliftYoneda.{w}.map s) :=
  ((presheafToSheaf J (Type (max v w))).map_isPullback
    (quotientPresheaf.isKernelPair_uliftπ.{w} h)).of_iso' (sheafificationIso _)
    (sheafificationIso _)
    (sheafificationIso _) (Iso.refl _)
    ((sheafificationNatIso J (Type (max v w))).hom.naturality (J.uliftYoneda.{w}.map t)).symm
    ((sheafificationNatIso J (Type (max v w))).hom.naturality (J.uliftYoneda.{w}.map s)).symm
    (Category.comp_id (quotientSheaf.π J s t)).symm
    (Category.comp_id (quotientSheaf.π J s t)).symm

end TauCeti.CategoryTheory
