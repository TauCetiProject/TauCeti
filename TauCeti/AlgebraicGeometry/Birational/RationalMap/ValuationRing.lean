/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Scheme.Normal
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
# Rational maps into proper schemes from schemes with valuation rings as local rings

Let `X` be an integral `S`-scheme all of whose local rings are valuation rings, for instance a
regular integral scheme of dimension one (a normal curve), and let `Y` be an `S`-scheme which is
universally closed and locally of finite type over `S`. Then every `S`-rational map `X ⤏ Y` is
defined everywhere (`AlgebraicGeometry.Scheme.RationalMap.domain_eq_top_of_valuationRing`).

At a point `x` of `X`, the rational map gives a morphism `Spec K(X) ⟶ Y` from the generic point,
and `𝒪_{X,x}` is a valuation ring with fraction field `K(X)`. The existence part of the valuative
criterion lifts this morphism to `Spec 𝒪_{X,x} ⟶ Y`, and the lift spreads out to a partial map
defined at `x` which represents the same rational map.

When `Y` is moreover separated over `S`, these partial maps agree on the overlaps of their domains,
since they agree on the generic point, which is dense; so they glue to a morphism. This gives the
extension theorem: every `S`-morphism `Spec K(X) ⟶ Y` extends uniquely to an `S`-morphism `X ⟶ Y`
(`AlgebraicGeometry.Scheme.homOfFunctionField`). Only the relative separatedness of `Y` is used;
the base `S` need not be separated. For curves this is the statement that a rational map from a
normal curve to a proper scheme extends to a morphism, through which morphisms of normal proper
curves are read off from embeddings of their function fields.

Taking `X = S` gives the sections of a proper morphism over a base whose local rings are valuation
rings, for instance a Dedekind scheme (a locally Noetherian normal integral scheme of dimension at
most one, such as the spectrum of a Dedekind domain): restriction to the generic point identifies
the sections of a proper `f : X ⟶ S` with the morphisms `Spec K(S) ⟶ X` over the generic point of
`S`, that is with the rational points of the generic fibre
(`AlgebraicGeometry.Scheme.Hom.sectionEquivOfValuationRing`). On a model of a curve over a Dedekind
base, this extends every rational point of the generic fibre to a section, along which it
specializes to each closed fibre.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.toHom`: a rational map from a reduced scheme to a separated
  scheme that is defined everywhere, as a morphism.
* `AlgebraicGeometry.Scheme.homOfFunctionField`: the morphism `X ⟶ Y` extending an `S`-morphism
  `Spec K(X) ⟶ Y`.
* `AlgebraicGeometry.Scheme.Hom.sectionEquivOfValuationRing`: sections of a proper morphism over a
  base whose local rings are valuation rings correspond to morphisms from the generic point.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.domain_eq_top_of_valuationRing`: an `S`-rational map from
  an integral scheme whose local rings are valuation rings to a universally closed `S`-scheme
  locally of finite type is defined everywhere.
* `AlgebraicGeometry.Scheme.fromSpecStalk_homOfFunctionField` and
  `AlgebraicGeometry.Scheme.eq_homOfFunctionField_iff`: `homOfFunctionField` extends the given
  morphism, and is the only `S`-morphism that does.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_section_of_valuationRing` and
  `AlgebraicGeometry.Scheme.Hom.existsUnique_section_of_isNormalScheme`: a morphism from the
  generic point of the base into a proper scheme extends uniquely to a section, over a base whose
  local rings are valuation rings and over a Dedekind scheme respectively.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition I.6.8 (the case of a
  nonsingular curve and a projective variety) and Theorem II.4.7 (the valuative criterion).
* The Stacks Project, Tag 0BX6 (spreading out morphisms from local rings).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}}

/-- The canonical morphisms from the spectra of stalks into an open subscheme are compatible with
generization: for a generization `y` of a point `x` of `U`, the morphism `Spec 𝒪_{X,y} ⟶ U` is
the morphism `Spec 𝒪_{X,x} ⟶ U` precomposed with `Spec` of the specialization map. -/
@[reassoc]
theorem Opens.SpecMap_stalkSpecializes_fromSpecStalkOfMem (U : X.Opens) {x y : X} (h : y ⤳ x)
    (hx : x ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem y (h.mem_open U.is_open' hx) := by
  rw [← cancel_mono U.ι]
  simp [SpecMap_stalkSpecializes_fromSpecStalk]

/-- The morphism `Spec K(X) ⟶ Y` of a partial map is its morphism `Spec 𝒪_{X,x} ⟶ Y` at any point
`x` of its domain, precomposed with `Spec` of the specialization map from the generic point. -/
@[reassoc]
theorem PartialMap.SpecMap_stalkSpecializes_fromSpecStalkOfMem [IrreducibleSpace X]
    (g : X.PartialMap Y) {x : X} (hx : x ∈ g.domain) :
    Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
      g.fromSpecStalkOfMem hx = g.fromFunctionField := by
  simp only [PartialMap.fromSpecStalkOfMem, Opens.SpecMap_stalkSpecializes_fromSpecStalkOfMem_assoc]

/-! ### Rational maps defined everywhere -/

/-- The domain of the representative `RationalMap.toPartialMap` is the domain of definition. -/
theorem RationalMap.toPartialMap_domain [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) :
    f.toPartialMap.domain = f.domain := (rfl)

/-- A rational map from a reduced scheme to a separated scheme which is defined everywhere, as a
morphism: its representative on its domain of definition `⊤`. -/
noncomputable def RationalMap.toHom [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y)
    (hf : f.domain = ⊤) : X ⟶ Y :=
  X.topIso.inv ≫ X.homOfLE (f.toPartialMap_domain.trans hf).ge ≫ f.toPartialMap.hom

/-- On the spectrum of the stalk at a point, `RationalMap.toHom` is the representative of the
rational map on its domain of definition. -/
@[reassoc]
theorem RationalMap.fromSpecStalk_toHom [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y)
    (hf : f.domain = ⊤) (x : X) :
    X.fromSpecStalk x ≫ f.toHom hf = f.toPartialMap.fromSpecStalkOfMem
      ((f.toPartialMap_domain.trans hf).ge (Set.mem_univ x)) := by
  rw [toHom, PartialMap.fromSpecStalkOfMem, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (Opens.ι _)]
  simp

/-- At the generic point, `RationalMap.toHom` is the morphism `Spec K(X) ⟶ Y` of the rational
map. -/
@[reassoc]
theorem RationalMap.fromSpecStalk_genericPoint_toHom [IsIntegral X] [Y.IsSeparated] (f : X ⤏ Y)
    (hf : f.domain = ⊤) :
    X.fromSpecStalk (genericPoint X) ≫ f.toHom hf = f.fromFunctionField := by
  rw [fromSpecStalk_toHom]
  conv_rhs => rw [← f.toRationalMap_toPartialMap, fromFunctionField_toRationalMap]

/-- The morphism `RationalMap.toHom` represents the rational map. -/
@[simp]
theorem RationalMap.toRationalMap_toHom [IsIntegral X] [Y.IsSeparated] (f : X ⤏ Y)
    (hf : f.domain = ⊤) : (f.toHom hf).toRationalMap = f := by
  refine eq_of_fromFunctionField_eq _ _ ?_
  rw [Hom.toRationalMap, fromFunctionField_toRationalMap, PartialMap.fromFunctionField,
    PartialMap.fromSpecStalkOfMem_toPartialMap, fromSpecStalk_genericPoint_toHom]

/-! ### Rational maps into universally closed schemes -/

section UniversallyClosed

variable [X.Over S] [Y.Over S] [IsIntegral X] [UniversallyClosed (Y ↘ S)]
  (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (φ : Spec X.functionField ⟶ Y)
  (hφ : φ ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S)

/-- The valuative square with `φ` on top and `Spec 𝒪_{X,x} ⟶ S` at the bottom. -/
private noncomputable def valuativeSquare (x : X) : ValuativeCommSq (Y ↘ S) where
  R := X.presheaf.stalk x
  K := X.functionField
  valuationRing := hX x
  i₁ := φ
  i₂ := X.fromSpecStalk x ≫ X ↘ S
  commSq := ⟨by
    rw [hφ, ← SpecMap_stalkSpecializes_fromSpecStalk_assoc
      ((genericPoint_spec X).specializes (Set.mem_univ x))]
    -- the algebra map from a stalk to the function field is the specialization map
    rfl⟩

/-- The lift of `φ` to `Spec 𝒪_{X,x}` given by the existence part of the valuative criterion. -/
private noncomputable def valuativeLift (x : X) : (valuativeSquare hX φ hφ x).commSq.LiftStruct :=
  ((UniversallyClosed.eq_valuativeCriterion.le _ _ (Y ↘ S) ‹_›).1
    (valuativeSquare hX φ hφ x)).exists_lift.some

private theorem valuativeLift_comp (x : X) :
    (valuativeLift hX φ hφ x).l ≫ Y ↘ S = X.fromSpecStalk x ≫ X ↘ S :=
  (valuativeLift hX φ hφ x).fac_right

private theorem SpecMap_stalkSpecializes_valuativeLift (x : X) :
    Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
      (valuativeLift hX φ hφ x).l = φ :=
  (valuativeLift hX φ hφ x).fac_left

variable [LocallyOfFiniteType (Y ↘ S)]

/-- The valuative lift at `x`, spread out to a partial map defined at `x`. -/
private noncomputable def localExtension (x : X) : X.PartialMap Y :=
  PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) (valuativeLift hX φ hφ x).l
    (valuativeLift_comp hX φ hφ x)

private theorem mem_domain_localExtension (x : X) : x ∈ (localExtension hX φ hφ x).domain :=
  PartialMap.mem_domain_ofFromSpecStalk _ _ _ _

private theorem localExtension_hom_comp (x : X) :
    (localExtension hX φ hφ x).hom ≫ Y ↘ S = (localExtension hX φ hφ x).domain.ι ≫ X ↘ S :=
  PartialMap.ofFromSpecStalk_comp _ _ _ _

/-- At the generic point, the local extension at any point is `φ`. -/
private theorem fromSpecStalkOfMem_localExtension (x : X)
    (h : genericPoint X ∈ (localExtension hX φ hφ x).domain) :
    (localExtension hX φ hφ x).fromSpecStalkOfMem h = φ := by
  refine Eq.trans ?_ (SpecMap_stalkSpecializes_valuativeLift hX φ hφ x)
  rw [← PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (X ↘ S) (Y ↘ S) _
    (valuativeLift_comp hX φ hφ x)]
  exact ((localExtension hX φ hφ x).SpecMap_stalkSpecializes_fromSpecStalkOfMem
    (mem_domain_localExtension hX φ hφ x)).symm

include hX in
/-- **Rational maps from schemes with valuation rings as local rings into universally closed
schemes are defined everywhere**, in the form of the rational map spread out from an `S`-morphism
`φ : Spec K(X) ⟶ Y`. At a point `x`, the valuative criterion lifts `φ` to `Spec 𝒪_{X,x}`, and the
lift spreads out to a partial map defined at `x`. -/
theorem RationalMap.domain_ofFunctionField_eq_top :
    (ofFunctionField (X ↘ S) (Y ↘ S) φ hφ).domain = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ RationalMap.mem_domain.mpr
    ⟨localExtension hX φ hφ x, mem_domain_localExtension hX φ hφ x, ?_⟩
  refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [fromFunctionField_ofFunctionField, fromFunctionField_toRationalMap]
  exact fromSpecStalkOfMem_localExtension hX φ hφ x _

include hX in
/-- **Rational maps from schemes with valuation rings as local rings into universally closed
schemes are defined everywhere**: let `X` be an integral `S`-scheme whose local rings are valuation
rings (for instance a normal curve) and `Y` an `S`-scheme universally closed and locally of finite
type over `S`. Then every `S`-rational map `X ⤏ Y` is defined at every point of `X`. -/
theorem RationalMap.domain_eq_top_of_valuationRing (f : X ⤏ Y) [f.IsOver (X ↘ S) (Y ↘ S)] :
    f.domain = ⊤ := by
  obtain ⟨g, hg, rfl⟩ := f.exists_partialMap_over (X ↘ S) (Y ↘ S)
  have hφ : g.fromFunctionField ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S := by
    rw [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem, Category.assoc,
      g.over (X ↘ S) (Y ↘ S), Opens.fromSpecStalkOfMem_ι_assoc]
  rw [← domain_ofFunctionField_eq_top hX _ hφ]
  congr 1
  exact eq_of_fromFunctionField_eq _ _ (fromFunctionField_ofFunctionField _ _ _ _).symm

/-! ### Extending morphisms from the generic point -/

private theorem isOpenCover_domain_localExtension :
    TopologicalSpace.IsOpenCover fun x ↦ (localExtension hX φ hφ x).domain :=
  eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
    ⟨x, mem_domain_localExtension hX φ hφ x⟩

variable [IsSeparated (Y ↘ S)]

/-- Two local extensions agree on the overlap of their domains: they are equivalent partial maps,
since both restrict to `φ` on the generic point, and `Y` is separated over `S`. -/
private theorem localExtension_compat (x y : X) :
    pullback.fst (localExtension hX φ hφ x).domain.ι (localExtension hX φ hφ y).domain.ι ≫
        (localExtension hX φ hφ x).hom =
      pullback.snd _ _ ≫ (localExtension hX φ hφ y).hom := by
  set g := localExtension hX φ hφ x
  set g' := localExtension hX φ hφ y
  have hη : genericPoint X ∈ g.domain :=
    (genericPoint_specializes x).mem_open g.domain.is_open' (mem_domain_localExtension hX φ hφ x)
  have hη' : genericPoint X ∈ g'.domain :=
    (genericPoint_specializes y).mem_open g'.domain.is_open' (mem_domain_localExtension hX φ hφ y)
  have : g.IsOver (X ↘ S) (Y ↘ S) := ⟨localExtension_hom_comp hX φ hφ x⟩
  have : g'.IsOver (X ↘ S) (Y ↘ S) := ⟨localExtension_hom_comp hX φ hφ y⟩
  have H := (PartialMap.equiv_iff_of_isSeparated (X ↘ S) (Y ↘ S)).mp
    (PartialMap.equiv_of_fromSpecStalkOfMem_eq g g' hη hη'
      ((fromSpecStalkOfMem_localExtension hX φ hφ x hη).trans
        (fromSpecStalkOfMem_localExtension hX φ hφ y hη').symm))
  rw [← cancel_epi (isPullback_opens_inf g.domain g'.domain).isoPullback.hom,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact H

/-- **A morphism from the generic point extends to the whole scheme**: for an integral `S`-scheme
`X` whose local rings are valuation rings and an `S`-scheme `Y` universally closed, locally of
finite type and separated over `S` (for instance proper over `S`), the `S`-morphism `X ⟶ Y`
extending an `S`-morphism `φ : Spec K(X) ⟶ Y` (`fromSpecStalk_homOfFunctionField`), which is
unique (`eq_homOfFunctionField_iff`). The base `S` need not be separated. -/
noncomputable def homOfFunctionField : X ⟶ Y :=
  (X.openCoverOfIsOpenCover _ (isOpenCover_domain_localExtension hX φ hφ)).glueMorphisms
    (fun x ↦ (localExtension hX φ hφ x).hom) (localExtension_compat hX φ hφ)

@[reassoc]
private theorem ι_homOfFunctionField (x : X) :
    (localExtension hX φ hφ x).domain.ι ≫ homOfFunctionField hX φ hφ =
      (localExtension hX φ hφ x).hom :=
  Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover _ (isOpenCover_domain_localExtension hX φ hφ))
    _ _ x

/-- `homOfFunctionField` extends the morphism from the generic point. -/
@[reassoc (attr := simp)]
theorem fromSpecStalk_homOfFunctionField :
    X.fromSpecStalk (genericPoint X) ≫ homOfFunctionField hX φ hφ = φ := by
  have hη := mem_domain_localExtension hX φ hφ (genericPoint X)
  rw [← Opens.fromSpecStalkOfMem_ι _ _ hη, Category.assoc, ι_homOfFunctionField]
  exact fromSpecStalkOfMem_localExtension hX φ hφ _ hη

/-- `homOfFunctionField` is a morphism over `S`. -/
instance isOver_homOfFunctionField : (homOfFunctionField hX φ hφ).IsOver S := by
  rw [Hom.isOver_iff]
  refine (X.openCoverOfIsOpenCover _ (isOpenCover_domain_localExtension hX φ hφ)).hom_ext _ _
    fun x ↦ ?_
  -- the cover's inclusions are the inclusions of the domains of the local extensions
  exact (ι_homOfFunctionField_assoc hX φ hφ x _).trans (localExtension_hom_comp hX φ hφ x)

/-- **The extension of a morphism from the generic point is unique**: an `S`-morphism `X ⟶ Y` is
`homOfFunctionField hX φ hφ` exactly when it restricts to `φ` on the generic point. -/
theorem eq_homOfFunctionField_iff (f : X ⟶ Y) [f.IsOver S] :
    f = homOfFunctionField hX φ hφ ↔ X.fromSpecStalk (genericPoint X) ≫ f = φ := by
  refine ⟨fun h ↦ h ▸ fromSpecStalk_homOfFunctionField hX φ hφ, fun h ↦ ?_⟩
  exact ext_of_isDominant_of_isSeparated' S (X.fromSpecStalk (genericPoint X))
    (by rw [h, fromSpecStalk_homOfFunctionField])

end UniversallyClosed

/-! ### Sections over a base whose local rings are valuation rings -/

section Sections

variable [IsIntegral S] (hS : ∀ s : S, ValuationRing (S.presheaf.stalk s)) (f : X ⟶ S)
  [UniversallyClosed f] [LocallyOfFiniteType f] [IsSeparated f]

/-- **Sections of a proper morphism are the rational points of its generic fibre**: over an
integral scheme `S` whose local rings are valuation rings, such as a Dedekind scheme, restriction
to the generic point identifies the sections of a morphism `f : X ⟶ S` which is universally
closed, separated and locally of finite type (for instance proper) with the morphisms
`Spec K(S) ⟶ X` lying over the generic point of `S`, that is with the `K(S)`-rational points of
the generic fibre. The base `S` need not be separated. -/
noncomputable def Hom.sectionEquivOfValuationRing :
    {σ : S ⟶ X // σ ≫ f = 𝟙 S} ≃
      {x : Spec S.functionField ⟶ X // x ≫ f = S.fromSpecStalk (genericPoint S)} :=
  letI : X.Over S := ⟨f⟩
  haveI : UniversallyClosed (X ↘ S) := ‹UniversallyClosed f›
  haveI : LocallyOfFiniteType (X ↘ S) := ‹LocallyOfFiniteType f›
  haveI : IsSeparated (X ↘ S) := ‹IsSeparated f›
  { toFun σ := ⟨S.fromSpecStalk (genericPoint S) ≫ σ.val, by
      rw [Category.assoc, σ.property, Category.comp_id]⟩
    invFun x := ⟨homOfFunctionField hS x.val (x.property.trans (Category.comp_id _).symm),
      (Hom.isOver_iff _).mp (isOver_homOfFunctionField hS _ _)⟩
    left_inv σ := by
      have : σ.val.IsOver S := (Hom.isOver_iff _).mpr σ.property
      exact Subtype.ext ((eq_homOfFunctionField_iff hS _ _ σ.val).mpr rfl).symm
    right_inv x := Subtype.ext (fromSpecStalk_homOfFunctionField hS _ _) }

/-- The section-to-generic-point map restricts a section to the generic point of the base. -/
@[simp]
theorem Hom.sectionEquivOfValuationRing_apply_coe (σ : {σ : S ⟶ X // σ ≫ f = 𝟙 S}) :
    (f.sectionEquivOfValuationRing hS σ : Spec S.functionField ⟶ X) =
      S.fromSpecStalk (genericPoint S) ≫ σ.val :=
  (rfl)

/-- The section attached to a morphism from the generic point of the base extends it. -/
@[reassoc (attr := simp)]
theorem Hom.fromSpecStalk_sectionEquivOfValuationRing_symm_apply_coe
    (x : {x : Spec S.functionField ⟶ X // x ≫ f = S.fromSpecStalk (genericPoint S)}) :
    S.fromSpecStalk (genericPoint S) ≫ ((f.sectionEquivOfValuationRing hS).symm x).val = x.val := by
  rw [← sectionEquivOfValuationRing_apply_coe hS f, Equiv.apply_symm_apply]

include hS in
/-- **A rational point of the generic fibre extends uniquely to a section**: over an integral
scheme `S` whose local rings are valuation rings, a morphism `Spec K(S) ⟶ X` over the generic point
of `S` is the restriction of a unique section of `f : X ⟶ S`, when `f` is universally closed,
separated and locally of finite type (for instance proper). -/
theorem Hom.existsUnique_section_of_valuationRing (x : Spec S.functionField ⟶ X)
    (hx : x ≫ f = S.fromSpecStalk (genericPoint S)) :
    ∃! σ : S ⟶ X, σ ≫ f = 𝟙 S ∧ S.fromSpecStalk (genericPoint S) ≫ σ = x := by
  obtain ⟨⟨σ, hσ⟩, h⟩ := (f.sectionEquivOfValuationRing hS).surjective ⟨x, hx⟩
  have hσx : S.fromSpecStalk (genericPoint S) ≫ σ = x := congrArg Subtype.val h
  refine ⟨σ, ⟨hσ, hσx⟩, fun τ hτ ↦ ?_⟩
  exact congrArg Subtype.val <| (f.sectionEquivOfValuationRing hS).injective
    (a₁ := ⟨τ, hτ.1⟩) (a₂ := ⟨σ, hσ⟩) (Subtype.ext (hτ.2.trans hσx.symm))

omit hS in
/-- **Sections of proper schemes over a Dedekind base**: let `S` be a locally Noetherian normal
integral scheme of dimension at most one, for instance the spectrum of a Dedekind domain or of a
field. A morphism `Spec K(S) ⟶ X` over the generic point of `S` is the restriction of a unique
section of `f : X ⟶ S`, when `f` is universally closed, separated and locally of finite type (for
instance proper). -/
theorem Hom.existsUnique_section_of_isNormalScheme [IsLocallyNoetherian S]
    [TauCeti.AlgebraicGeometry.IsNormalScheme S] (hdim : topologicalKrullDim S ≤ 1)
    (x : Spec S.functionField ⟶ X) (hx : x ≫ f = S.fromSpecStalk (genericPoint S)) :
    ∃! σ : S ⟶ X, σ ≫ f = 𝟙 S ∧ S.fromSpecStalk (genericPoint S) ≫ σ = x :=
  have (y : TauCeti.AlgebraicGeometry.CodimensionOnePoint S) :
      IsDiscreteValuationRing (S.presheaf.stalk (y : S)) :=
    TauCeti.AlgebraicGeometry.IsNormalScheme.isDiscreteValuationRing_stalk y.val y.property
  f.existsUnique_section_of_valuationRing
    (TauCeti.AlgebraicGeometry.Scheme.valuationRing_stalk_of_topologicalKrullDim_le_one hdim) x hx

end Sections

end AlgebraicGeometry.Scheme
