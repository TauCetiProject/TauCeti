/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Limits
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Relative
public import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties
public import TauCeti.RingTheory.Etale.Equalizer

/-!
# Quotients of finite étale schemes by finite groups

Let `S` be an arbitrary scheme and let a finite group `G` act on a finite étale `S`-scheme
`p : Y ⟶ S` by automorphisms over `S`, given as a functor `F : SingleObj G ⥤ FiniteEtaleScheme S`.
The quotient `Y / G` exists in `FiniteEtaleScheme S`. This is the quotient half of Lenstra's axiom
(G2) for a Galois category, over any base; over an affine base it was obtained from finite étale
algebras in `TauCeti.AlgebraicGeometry.FiniteEtale.Colimits`.

The quotient is the relative invariant quotient of
`TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Relative`. The finite morphism `p` is affine, so
`Y` is the relative spectrum of its function algebra `A = p_* 𝒪_Y`
(`AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsIso`), and `G` acts on `A` by pullback of
functions (`TauCeti.FiniteEtaleScheme.functionAlgebraAction`). The quotient is the relative
spectrum `Spec_S(A)/G` of the presheaf of invariant sections
(`CategoryTheory.CommMon.invariantSubalgebraPresheaf`).
Over an affine open `U` of `S`, its coordinate ring is the ring of invariants of the finite étale
`Γ(S, U)`-algebra `Γ(Y, p⁻¹ U)`, which is again finite étale
(`TauCeti.FixedPoints.etale_subalgebra`, `TauCeti.FixedPoints.finite_subalgebra`). Hence
`Spec_S(A)/G` is finite étale over `S`. The quotient projection is a categorical quotient among
all schemes (`CategoryTheory.CommMon.existsUnique_relativeSpecπ_comp_eq`), and in particular
among finite étale `S`-schemes.

With the finite limits, finite coproducts and direct summands of
`TauCeti.AlgebraicGeometry.FiniteEtale.Limits`, finite étale schemes over every scheme form a
`CategoryTheory.PreGaloisCategory`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.functionAlgebraAction F`: the action of `G` on the function algebra
  of `Y` by pullback of functions along the inverse action.
* `TauCeti.FiniteEtaleScheme.quotient F`: the relative invariant quotient `Y / G`, as a finite
  étale `S`-scheme.
* `TauCeti.FiniteEtaleScheme.quotientπ F`: the quotient map `Y ⟶ Y / G`, invariant under `G`
  (`TauCeti.FiniteEtaleScheme.map_quotientπ`).
* `TauCeti.FiniteEtaleScheme.quotientCocone F`: the quotient map as a cocone over `F`.

## Main results

* `TauCeti.FiniteEtaleScheme.isColimitQuotientCocone F`: the relative invariant quotient is the
  quotient of `Y` by `G` in finite étale `S`-schemes.
* `TauCeti.FiniteEtaleScheme.exists_comp_map_eq_of_comp_quotientπ_eq F`: two points of `Y` with
  values in a field and the same image in `Y / G` differ by the action of an element of `G`
  (`CommMon.exists_comp_relativeSpecMap_eq`).
* `HasColimitsOfShape (SingleObj G) (FiniteEtaleScheme S)` for a finite group `G`.
* `PreGaloisCategory (FiniteEtaleScheme S)` for every scheme `S`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §1 and §§4–5.
* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

universe u v

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {G : Type v} [Group G] (F : SingleObj G ⥤ FiniteEtaleScheme S)

/-- The action map of `g ∈ G` on `F.obj (SingleObj.star G)`. -/
private abbrev act (g : G) : F.obj (SingleObj.star G) ⟶ F.obj (SingleObj.star G) := F.map g

private lemma act_comp (g h : G) : act F g ≫ act F h = act F (h * g) := by
  rw [← F.map_comp, SingleObj.comp_as_mul]

private lemma act_one : act F 1 = 𝟙 _ :=
  -- In `SingleObj G`, the unit `1` is the identity of the single object.
  F.map_id _

/-- Pullback of functions along the action map of `g ∈ G`. -/
private noncomputable abbrev pullbackFunctions (g : G) :
    (F.obj (SingleObj.star G)).obj.hom.pushforwardStructureAlgebra ⟶
      (F.obj (SingleObj.star G)).obj.hom.pushforwardStructureAlgebra :=
  Scheme.Hom.pushforwardStructureAlgebraMap (act F g).hom.left (Over.w (act F g).hom)

private lemma pullbackFunctions_comp (g h : G) :
    pullbackFunctions F g ≫ pullbackFunctions F h = pullbackFunctions F (g * h) := by
  rw [← Scheme.Hom.pushforwardStructureAlgebraMap_comp]
  congr 1
  rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, act_comp]

private lemma pullbackFunctions_one : pullbackFunctions F 1 = 𝟙 _ := by
  have h : (act F 1).hom.left = 𝟙 _ := by
    rw [act_one, ObjectProperty.FullSubcategory.id_hom, Over.id_left]
  simp only [pullbackFunctions, h, Scheme.Hom.pushforwardStructureAlgebraMap_id]

/-- **The action of `G` on the function algebra.** For `F : SingleObj G ⥤ FiniteEtaleScheme S`,
an element `g` acts on the function algebra `p_* 𝒪_Y` of `p : Y ⟶ S`, where
`Y = F.obj (SingleObj.star G)`, by pullback of functions along the action map of `g⁻¹`, so that
the action is by algebra automorphisms on the left. -/
noncomputable def functionAlgebraAction :
    G →* Aut (F.obj (SingleObj.star G)).obj.hom.pushforwardStructureAlgebra where
  toFun g := .of
    { hom := pullbackFunctions F g⁻¹
      inv := pullbackFunctions F g
      hom_inv_id := by rw [pullbackFunctions_comp, inv_mul_cancel, pullbackFunctions_one]
      inv_hom_id := by rw [pullbackFunctions_comp, mul_inv_cancel, pullbackFunctions_one] }
  map_one' := Aut.ext (Iso.ext (by simpa using pullbackFunctions_one F))
  map_mul' g h := Aut.ext (Iso.ext (by
    simp only [Aut.mul_asIso, Iso.trans_hom, mul_inv_rev, pullbackFunctions_comp]))

/-- `g` acts on the function algebra by pullback of functions along the action map of `g⁻¹`. -/
@[simp]
lemma functionAlgebraAction_apply_asIso_hom (g : G) :
    (functionAlgebraAction F g).asIso.hom =
      Scheme.Hom.pushforwardStructureAlgebraMap
        (F.map (X := SingleObj.star G) (Y := SingleObj.star G) g⁻¹).hom.left (Over.w _) :=
  (rfl)

/-- The function algebra of a finite étale scheme is finite étale over each affine open. -/
private lemma finite_and_etale_sections {U : S.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(S, U) Γ((F.obj (SingleObj.star G)).obj.hom.pushforwardStructureAlgebra.X, U) ∧
      Algebra.Etale Γ(S, U)
        Γ((F.obj (SingleObj.star G)).obj.hom.pushforwardStructureAlgebra.X, U) := by
  set p := (F.obj (SingleObj.star G)).obj.hom
  -- The relative spectrum of the function algebra is `Y` itself, finite étale over `S`.
  have hp : p.relativeSpecFunctionsToScheme ≫ p =
      p.pushforwardStructureAlgebra.relativeSpecToBase :=
    p.relativeSpecFunctionsToScheme_comp
  have hf : IsFinite p.pushforwardStructureAlgebra.relativeSpecToBase := hp ▸ inferInstance
  have he : Etale p.pushforwardStructureAlgebra.relativeSpecToBase := hp ▸ inferInstance
  exact ⟨(CommMon.relativeSpec_finite_iff _).mp hf U hU,
    (CommMon.relativeSpec_etale_iff _).mp he U hU⟩

/-- The identification of `Y` with the relative spectrum of its function algebra intertwines the
action of `g⁻¹` on `Y` with the action of `g` on the function algebra. -/
private lemma relativeSpecMap_relativeSpecFunctionsToScheme (g : G) :
    CommMon.relativeSpecMap (functionAlgebraAction F g).asIso.hom ≫
        (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme =
      (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme ≫
        (act F g⁻¹).hom.left :=
  Scheme.Hom.relativeSpecFunctionsToScheme_naturality _ _

variable [Finite G]

/-- Over each affine open, the invariant sections of the function algebra form a finite étale
algebra. -/
private lemma finite_and_etale_invariantSections {U : S.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(S, U) (CommMon.invariantSections (functionAlgebraAction F) U) ∧
      Algebra.Etale Γ(S, U) (CommMon.invariantSections (functionAlgebraAction F) U) := by
  obtain ⟨_, _⟩ := finite_and_etale_sections F hU
  let _ := CommMon.sectionsMulSemiringAction (functionAlgebraAction F) U
  have := CommMon.smulCommClass_sectionsMulSemiringAction (functionAlgebraAction F) U
  -- The invariant sections are the fixed points of the action on the sections.
  let e := Subalgebra.equivOfEq _ _
    (CommMon.invariantSections_eq_fixedPoints (functionAlgebraAction F) U)
  exact ⟨.equiv e.symm.toLinearEquiv, .of_equiv e.symm⟩

/-- The relative invariant quotient of a finite étale scheme by a finite group is finite over the
base. -/
instance isFinite_relativeSpecToBase :
    IsFinite
      (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecToBase := by
  observe hasFiniteAffineProperty : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasFiniteAffineProperty
  refine (CommMon.SubalgebraPresheaf.relativeSpecToBase_iff _ @IsFinite).mpr fun U ↦ ?_
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap,
    CommMon.invariantSubalgebraPresheaf_sections]
  exact (finite_and_etale_invariantSections F U.2).1

/-- The relative invariant quotient of a finite étale scheme by a finite group is étale over the
base. -/
instance etale_relativeSpecToBase :
    Etale (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecToBase := by
  have : IsZariskiLocalAtTarget @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Etale)
  refine (CommMon.SubalgebraPresheaf.relativeSpecToBase_iff _ @Etale).mpr fun U ↦ ?_
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap,
    CommMon.invariantSubalgebraPresheaf_sections]
  exact (finite_and_etale_invariantSections F U.2).2

/-- **The quotient of a finite étale scheme by a finite group.** For a finite group `G` acting on
a finite étale `S`-scheme `p : Y ⟶ S` through `F : SingleObj G ⥤ FiniteEtaleScheme S`, this is the
relative invariant quotient `Spec_S(p_* 𝒪_Y)/G`, finite étale over `S`. It is the colimit of `F`
(`isColimitQuotientCocone`). -/
@[expose]
noncomputable def quotient : FiniteEtaleScheme S :=
  ⟨Over.mk (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecToBase,
    (finiteEtaleSchemeProperty_iff _).mpr
      ⟨(inferInstance : IsFinite (CommMon.invariantSubalgebraPresheaf _).relativeSpecToBase),
        (inferInstance : Etale (CommMon.invariantSubalgebraPresheaf _).relativeSpecToBase)⟩⟩

/-- The quotient is the relative invariant quotient of the function algebra, over the base. -/
@[simp]
lemma quotient_obj : (quotient F).obj =
    Over.mk (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecToBase :=
  (rfl)

/-- The relative invariant quotient projection, precomposed with the identification of `Y` with
the relative spectrum of its function algebra. -/
private noncomputable abbrev quotientMap : (F.obj (SingleObj.star G)).obj.left ⟶
    (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpec :=
  inv (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme ≫
    (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecπ

private lemma quotientMap_relativeSpecToBase :
    quotientMap F ≫
        (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecToBase =
      (F.obj (SingleObj.star G)).obj.hom := by
  rw [Category.assoc, CommMon.SubalgebraPresheaf.relativeSpecπ_relativeSpecToBase,
    IsIso.inv_comp_eq, Scheme.Hom.relativeSpecFunctionsToScheme_comp]

private lemma act_quotientMap (g : G) : (act F g).hom.left ≫ quotientMap F = quotientMap F := by
  have h := relativeSpecMap_relativeSpecFunctionsToScheme F g⁻¹
  rw [inv_inv] at h
  have h' : (act F g).hom.left ≫
      inv (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme =
      inv (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme ≫
        CommMon.relativeSpecMap (functionAlgebraAction F g⁻¹).asIso.hom := by
    rw [IsIso.comp_inv_eq, Category.assoc, h, IsIso.inv_hom_id_assoc]
  rw [quotientMap, reassoc_of% h',
    CommMon.relativeSpecMap_invariantSubalgebraPresheaf_relativeSpecπ]

/-- The quotient map `Y ⟶ Y / G` of finite étale `S`-schemes. On underlying schemes it is the
relative invariant quotient projection, after identifying `Y` with the relative spectrum of its
function algebra (`quotientπ_hom_left`). -/
noncomputable def quotientπ : F.obj (SingleObj.star G) ⟶ quotient F :=
  ObjectProperty.homMk (Over.homMk (quotientMap F) (quotientMap_relativeSpecToBase F))

/-- On underlying schemes, the quotient map is the inverse of the identification of `Y` with the
relative spectrum of its function algebra, followed by the relative invariant quotient
projection. -/
@[simp]
lemma quotientπ_hom_left : (quotientπ F).hom.left =
    inv (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme ≫
      (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecπ :=
  (rfl)

/-- The quotient map is invariant under the action of `G`. -/
@[reassoc (attr := simp)]
lemma map_quotientπ (g : G) :
    F.map (X := SingleObj.star G) (Y := SingleObj.star G) g ≫ quotientπ F = quotientπ F :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (act_quotientMap F g))

/-- **Points of the quotient are orbits.** Two morphisms from the spectrum of a field to `Y` with
the same image in `Y / G` differ by the action of an element of `G`. -/
theorem exists_comp_map_eq_of_comp_quotientπ_eq {K : Type u} [Field K]
    {x₁ x₂ : Spec (CommRingCat.of K) ⟶ (F.obj (SingleObj.star G)).obj.left}
    (h : x₁ ≫ (quotientπ F).hom.left = x₂ ≫ (quotientπ F).hom.left) :
    ∃ g : G, x₁ ≫ (F.map (X := SingleObj.star G) (Y := SingleObj.star G) g).hom.left = x₂ := by
  -- The underlying scheme of `quotient F` is the relative invariant quotient by definition
  -- (`quotient_obj`), and the quotient map is `quotientMap F` (`quotientπ_hom_left`).
  have h₀ : x₁ ≫ quotientMap F = x₂ ≫ quotientMap F := h
  -- Pass to points of the relative spectrum of the function algebra.
  obtain ⟨g, hg⟩ := CommMon.exists_comp_relativeSpecMap_eq
    (x₁ := x₁ ≫ inv (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme)
    (x₂ := x₂ ≫ inv (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme)
    (by simpa only [Category.assoc] using h₀)
  refine ⟨g⁻¹, ?_⟩
  -- The action of `g` on the function algebra is pullback along the action map of `g⁻¹`.
  have h' := congr($hg ≫ (F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme)
  rwa [Category.assoc, Category.assoc, relativeSpecMap_relativeSpecFunctionsToScheme,
    IsIso.inv_hom_id_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at h'

/-- The quotient of a finite étale scheme by a finite group, as a cocone over the action. It is a
colimit (`isColimitQuotientCocone`). -/
@[expose, simps]
noncomputable def quotientCocone : Cocone F where
  pt := quotient F
  ι :=
    { app _ := quotientπ F
      naturality _ _ g := (map_quotientπ F g).trans (Category.comp_id _).symm }

/-- A cocone over `F` induces a morphism out of the relative invariant quotient, on underlying
schemes. -/
private noncomputable abbrev descLeft (s : Cocone F) :
    (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpec ⟶
      s.pt.obj.left :=
  CommMon.invariantQuotientDesc
    ((F.obj (SingleObj.star G)).obj.hom.relativeSpecFunctionsToScheme ≫
      (s.ι.app (SingleObj.star G)).hom.left) fun g ↦ by
    rw [reassoc_of% relativeSpecMap_relativeSpecFunctionsToScheme F g, ← Over.comp_left,
      ← ObjectProperty.FullSubcategory.comp_hom, s.w]

private lemma quotientMap_descLeft (s : Cocone F) :
    quotientMap F ≫ descLeft F s = (s.ι.app (SingleObj.star G)).hom.left := by
  rw [Category.assoc, CommMon.relativeSpecπ_invariantQuotientDesc, IsIso.inv_hom_id_assoc]

/-- Morphisms out of the relative invariant quotient are determined by their composite with the
quotient map. -/
private lemma hom_ext_quotientMap {Z : Scheme.{u}}
    {h₁ h₂ : (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpec ⟶ Z}
    (e : quotientMap F ≫ h₁ = quotientMap F ≫ h₂) : h₁ = h₂ :=
  CommMon.invariantQuotient_hom_ext
    ((cancel_epi (inv _)).mp (by simpa only [Category.assoc] using e))

private lemma descLeft_comp_hom (s : Cocone F) :
    descLeft F s ≫ s.pt.obj.hom =
      (CommMon.invariantSubalgebraPresheaf (functionAlgebraAction F)).relativeSpecToBase :=
  hom_ext_quotientMap F (by
    rw [← Category.assoc, quotientMap_descLeft, quotientMap_relativeSpecToBase]
    exact Over.w (s.ι.app (SingleObj.star G)).hom)

/-- **The relative invariant quotient is the quotient in finite étale schemes.** Every
`G`-invariant morphism from `Y` to a finite étale `S`-scheme factors uniquely through the quotient
map `Y ⟶ Y / G`. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone F) where
  desc s := ObjectProperty.homMk (Over.homMk (descLeft F s) (descLeft_comp_hom F s))
  fac s _ := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (quotientMap_descLeft F s))
  uniq s _ hm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (hom_ext_quotientMap F
    ((congrArg (fun f ↦ f.hom.left) (hm (SingleObj.star G))).trans
      (quotientMap_descLeft F s).symm)))

/-- A finite group action on a finite étale scheme has a quotient. -/
instance hasColimit : HasColimit F :=
  ⟨⟨⟨quotientCocone F, isColimitQuotientCocone F⟩⟩⟩

variable (G) in
/-- **Finite étale schemes over any scheme have quotients by finite groups.** -/
instance : HasColimitsOfShape (SingleObj G) (FiniteEtaleScheme S) where
  has_colimit _ := inferInstance

end TauCeti.FiniteEtaleScheme

namespace TauCeti.FiniteEtaleScheme

/-- **Finite étale schemes over any scheme form a pre-Galois category.** -/
instance {S : Scheme.{u}} : PreGaloisCategory (FiniteEtaleScheme S) where
  hasQuotientsByFiniteGroups _ := inferInstance
  monoInducesIsoOnDirectSummand i _ := exists_isColimit_binaryCofanMk_of_mono i

end TauCeti.FiniteEtaleScheme
