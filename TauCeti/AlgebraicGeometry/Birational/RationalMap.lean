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

When `Y` is moreover separated over a separated base, the rational map is a morphism. Together with
Mathlib's correspondence between rational maps and morphisms from the generic point, this gives
the extension theorem: every `S`-morphism `Spec K(X) ⟶ Y` extends uniquely to an `S`-morphism
`X ⟶ Y` (`AlgebraicGeometry.Scheme.homOfFunctionField`). For curves this is the statement that a
rational map from a normal curve to a proper scheme extends to a morphism, through which morphisms
of normal proper curves are read off from embeddings of their function fields.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.toHom`: a rational map from a reduced scheme to a separated
  scheme that is defined everywhere, as a morphism.
* `AlgebraicGeometry.Scheme.homOfFunctionField`: the morphism `X ⟶ Y` extending an `S`-morphism
  `Spec K(X) ⟶ Y`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.domain_eq_top_of_valuationRing`: an `S`-rational map from
  an integral scheme whose local rings are valuation rings to a universally closed `S`-scheme
  locally of finite type is defined everywhere.
* `AlgebraicGeometry.Scheme.fromSpecStalk_homOfFunctionField` and
  `AlgebraicGeometry.Scheme.eq_homOfFunctionField_iff`: `homOfFunctionField` extends the given
  morphism, and is the only `S`-morphism that does.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition I.6.8 (the case of a
  nonsingular curve and a projective variety) and Theorem II.4.7 (the valuative criterion).
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
      U.fromSpecStalkOfMem y (h.mem_open U.2 hx) := by
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
  [LocallyOfFiniteType (Y ↘ S)]

/-- **Rational maps from schemes with valuation rings as local rings into universally closed
schemes are defined everywhere**, in the form of the rational map spread out from an `S`-morphism
`φ : Spec K(X) ⟶ Y`. At a point `x`, the valuative criterion lifts `φ` to `Spec 𝒪_{X,x}`, and the
lift spreads out to a partial map defined at `x`. -/
theorem RationalMap.domain_ofFunctionField_eq_top
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (φ : Spec X.functionField ⟶ Y)
    (hφ : φ ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S) :
    (ofFunctionField (X ↘ S) (Y ↘ S) φ hφ).domain = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have := hX x
  have hηx := (genericPoint_spec X).specializes (Set.mem_univ x)
  -- the valuative square with `φ` on top and `Spec 𝒪_{X,x} ⟶ S` at the bottom
  have hsq : CommSq φ (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField))) (Y ↘ S) (X.fromSpecStalk x ≫ X ↘ S) :=
    ⟨by rw [hφ, ← SpecMap_stalkSpecializes_fromSpecStalk_assoc hηx]; rfl⟩
  obtain ⟨l, hl₁, hl₂⟩ := (UniversallyClosed.eq_valuativeCriterion.le _ _ (Y ↘ S) ‹_›).1
    { R := X.presheaf.stalk x, K := X.functionField, i₁ := φ, i₂ := _, commSq := hsq }
    |>.exists_lift
  dsimp only at hl₁ hl₂
  -- the lift spreads out to a partial map defined at `x`, with the same generic behaviour as `φ`
  let g := PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) l hl₂
  refine RationalMap.mem_domain.mpr ⟨g, PartialMap.mem_domain_ofFromSpecStalk _ _ _ _, ?_⟩
  refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [fromFunctionField_ofFunctionField, fromFunctionField_toRationalMap, ← hl₁,
    ← PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (X ↘ S) (Y ↘ S) l hl₂,
    ← g.SpecMap_stalkSpecializes_fromSpecStalkOfMem]
  rfl

/-- **Rational maps from schemes with valuation rings as local rings into universally closed
schemes are defined everywhere**: let `X` be an integral `S`-scheme whose local rings are valuation
rings (for instance a normal curve) and `Y` an `S`-scheme universally closed and locally of finite
type over `S`. Then every `S`-rational map `X ⤏ Y` is defined at every point of `X`. -/
theorem RationalMap.domain_eq_top_of_valuationRing
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (f : X ⤏ Y) [f.IsOver S] :
    f.domain = ⊤ := by
  obtain ⟨g, hg, rfl⟩ := f.exists_partialMap_over S
  have hφ : g.fromFunctionField ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S := by
    rw [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem, Category.assoc, comp_over,
      ← Opens.ι_comp_over, Opens.fromSpecStalkOfMem_ι_assoc]
  rw [← domain_ofFunctionField_eq_top hX _ hφ]
  congr 1
  exact eq_of_fromFunctionField_eq _ _ (fromFunctionField_ofFunctionField _ _ _ _).symm

end UniversallyClosed

/-! ### Extending morphisms from the generic point -/

section Separated

variable [X.Over S] [Y.Over S] [IsIntegral X] [S.IsSeparated] [UniversallyClosed (Y ↘ S)]
  [LocallyOfFiniteType (Y ↘ S)] [IsSeparated (Y ↘ S)]

/-- **A morphism from the generic point extends to the whole scheme**: for an integral `S`-scheme
`X` whose local rings are valuation rings and an `S`-scheme `Y` universally closed, locally of
finite type and separated over a separated base `S` (for instance proper over `S`), the
`S`-morphism `X ⟶ Y` extending an `S`-morphism `φ : Spec K(X) ⟶ Y`
(`fromSpecStalk_homOfFunctionField`), which is unique (`eq_homOfFunctionField_iff`). -/
noncomputable def homOfFunctionField (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (φ : Spec X.functionField ⟶ Y) (hφ : φ ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S) : X ⟶ Y :=
  have := Scheme.IsSeparated.of_isSeparated (Y ↘ S)
  (RationalMap.ofFunctionField (X ↘ S) (Y ↘ S) φ hφ).toHom
    (RationalMap.domain_ofFunctionField_eq_top hX φ hφ)

variable (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (φ : Spec X.functionField ⟶ Y)
  (hφ : φ ≫ Y ↘ S = X.fromSpecStalk _ ≫ X ↘ S)

/-- `homOfFunctionField` extends the morphism from the generic point. -/
@[reassoc (attr := simp)]
theorem fromSpecStalk_homOfFunctionField :
    X.fromSpecStalk (genericPoint X) ≫ homOfFunctionField hX φ hφ = φ := by
  have := Scheme.IsSeparated.of_isSeparated (Y ↘ S)
  rw [homOfFunctionField, RationalMap.fromSpecStalk_genericPoint_toHom,
    RationalMap.fromFunctionField_ofFunctionField]

/-- `homOfFunctionField` is a morphism over `S`. -/
instance isOver_homOfFunctionField : (homOfFunctionField hX φ hφ).IsOver S := by
  rw [Hom.isOver_iff]
  refine ext_of_isDominant (ι := X.fromSpecStalk (genericPoint X)) ?_
  rw [fromSpecStalk_homOfFunctionField_assoc, hφ]

/-- **The extension of a morphism from the generic point is unique**: an `S`-morphism `X ⟶ Y` is
`homOfFunctionField hX φ hφ` exactly when it restricts to `φ` on the generic point. -/
theorem eq_homOfFunctionField_iff (f : X ⟶ Y) [f.IsOver S] :
    f = homOfFunctionField hX φ hφ ↔ X.fromSpecStalk (genericPoint X) ≫ f = φ := by
  refine ⟨fun h ↦ h ▸ fromSpecStalk_homOfFunctionField hX φ hφ, fun h ↦ ?_⟩
  exact ext_of_isDominant_of_isSeparated' S (X.fromSpecStalk (genericPoint X))
    (by rw [h, fromSpecStalk_homOfFunctionField])

end Separated

end AlgebraicGeometry.Scheme
