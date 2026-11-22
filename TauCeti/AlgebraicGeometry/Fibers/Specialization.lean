/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.RationalMap
public import TauCeti.AlgebraicGeometry.Fibers.BaseChange
public import TauCeti.AlgebraicGeometry.Fibers.Composition
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Section

/-!
# Specialization of rational points of the generic fibre

A section `σ` of `f : X ⟶ S` meets the fibre `f⁻¹(s)` over every point `s` of `S` in a
`κ(s)`-rational point, the restriction of `σ` along `Spec κ(s) ⟶ S`
(`AlgebraicGeometry.Scheme.Hom.fiberPointOfSection`). These fibre points are compatible with
morphisms of families and with base change along any commutative square.

Let `S` be an integral scheme whose local rings are valuation rings, for instance a Dedekind
scheme, and let `f` be universally closed, separated and locally of finite type (for instance
proper). Every morphism `x : Spec K(S) ⟶ X` over the generic point of `S`, that is every
`K(S)`-rational point of the generic fibre, extends uniquely to a section of `f`
(`AlgebraicGeometry.Scheme.Hom.sectionEquivOfValuationRing`). Its fibre point over `s` is the
*specialization* `sp_s(x)` of `x` to the fibre over `s`
(`AlgebraicGeometry.Scheme.Hom.specializePoint`). For a model of a curve over a Dedekind base
this is the reduction of rational points of the curve to each closed fibre.

The specialization over the generic point recovers `x`, it commutes with morphisms of families
over `S`, and it commutes with base change along any morphism of such bases covered by a map of
families, compatibly with the given rational points: this includes restriction to opens of `S`,
localization at points of `S` and extension of a discrete valuation ring. When `X` is regular
and `f` is locally of finite presentation, every specialization lies in the smooth locus of `f`,
also over imperfect residue fields.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberPointOfSection`: the rational point of the fibre `f⁻¹(s)`
  cut out by a section of `f`.
* `AlgebraicGeometry.Scheme.Hom.specializePoint`: the specialization to the fibre over `s` of a
  rational point of the generic fibre.

## Main results

* `AlgebraicGeometry.Scheme.Hom.specializePoint_eq_fiberPointOfSection`: the specialization is
  the fibre point of any section extending the rational point.
* `AlgebraicGeometry.Scheme.Hom.specializePoint_genericPoint_fiberι`: over the generic point the
  specialization is the given rational point.
* `AlgebraicGeometry.Scheme.Hom.specializePoint_fiberCompMap`: compatibility with morphisms of
  families over `S`.
* `AlgebraicGeometry.Scheme.Hom.specializePoint_fiberBaseChangeMap`: compatibility with base
  change.
* `AlgebraicGeometry.Scheme.Hom.fiberι_specializePoint_mem_smoothLocus`: on a regular scheme,
  specializations lie in the smooth locus.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 10 (reduction of points of models).
* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, §3.1, Proposition 2 (sections of a
  regular scheme over a discrete valuation ring lie in the smooth locus).
* R. Hartshorne, *Algebraic Geometry*, Theorem II.4.7 (the valuative criterion).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-! ### Fibre points of sections -/

section FiberPoint

variable (f : X ⟶ S) {σ : S ⟶ X} (hσ : σ ≫ f = 𝟙 S) (s : S)

/-- The `κ(s)`-rational point of the fibre `f⁻¹(s)` through which a section `σ` of `f` passes:
the restriction of `σ` along `Spec κ(s) ⟶ S`. -/
def fiberPointOfSection : Spec (S.residueField s) ⟶ f.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ σ) (𝟙 _) (by simp [hσ])

/-- The fibre point of a section maps to the section in the total space. -/
@[reassoc (attr := simp)]
lemma fiberPointOfSection_fiberι :
    f.fiberPointOfSection hσ s ≫ f.fiberι s = S.fromSpecResidueField s ≫ σ :=
  pullback.lift_fst _ _ _

/-- The fibre point of a section is a `κ(s)`-rational point of the fibre. -/
@[reassoc (attr := simp)]
lemma fiberPointOfSection_fiberToSpecResidueField :
    f.fiberPointOfSection hσ s ≫ f.fiberToSpecResidueField s = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- A morphism into the fibre `f⁻¹(s)` is the fibre point of a section `σ` exactly when its
composite with the embedding of the fibre is the restriction of `σ`. -/
lemma eq_fiberPointOfSection_iff (p : Spec (S.residueField s) ⟶ f.fiber s) :
    p = f.fiberPointOfSection hσ s ↔ p ≫ f.fiberι s = S.fromSpecResidueField s ≫ σ := by
  rw [← cancel_mono (f.fiberι s), fiberPointOfSection_fiberι]

/-- The fibre point of a section `σ` over `s` is the point `σ s` of the total space. -/
@[simp]
lemma fiberι_fiberPointOfSection_apply (p : Spec (S.residueField s)) :
    f.fiberι s (f.fiberPointOfSection hσ s p) = σ s := by
  rw [← Scheme.Hom.comp_apply, fiberPointOfSection_fiberι, Scheme.Hom.comp_apply,
    fromSpecResidueField_apply]

/-- Fibre points of sections are compatible with morphisms of families: for `j : Y ⟶ X`, the
fibre point of a section `σ` of `j ≫ f` maps to the fibre point of the section `σ ≫ j` of `f`. -/
@[reassoc (attr := simp)]
lemma fiberPointOfSection_fiberCompMap (j : Y ⟶ X) {σ : S ⟶ Y} (hσ : σ ≫ j ≫ f = 𝟙 S) :
    (j ≫ f).fiberPointOfSection hσ s ≫ j.fiberCompMap f s =
      f.fiberPointOfSection (σ := σ ≫ j) (by rw [Category.assoc, hσ]) s := by
  rw [eq_fiberPointOfSection_iff, Category.assoc, fiberCompMap_fiberι,
    fiberPointOfSection_fiberι_assoc]

/-- Fibre points of sections are compatible with base change: in a commutative square of
families over `g : S' ⟶ S`, if a section `σ'` of `f'` lies over a section `σ` of `f`, then the
fibre point of `σ'` over `s'` maps to the fibre point of `σ` over `g s'`, after extending scalars
along `κ(g s') ⟶ κ(s')`. -/
@[reassoc]
lemma fiberPointOfSection_fiberBaseChangeMap {X' S' : Scheme.{u}} {f' : X' ⟶ S'} {g : S' ⟶ S}
    {g' : X' ⟶ X} (H : CommSq g' f' f g) {σ' : S' ⟶ X'} (hσ' : σ' ≫ f' = 𝟙 S')
    (hσσ' : σ' ≫ g' = g ≫ σ) (s' : S') :
    f'.fiberPointOfSection hσ' s' ≫ H.fiberBaseChangeMap s' =
      Spec.map (g.residueFieldMap s') ≫ f.fiberPointOfSection hσ (g s') := by
  rw [← cancel_mono (f.fiberι (g s'))]
  simp [hσσ']

end FiberPoint

/-! ### Specialization of rational points of the generic fibre -/

section Specialization

variable [IsIntegral S] (hS : ∀ s : S, ValuationRing (S.presheaf.stalk s)) (f : X ⟶ S)
  [UniversallyClosed f] [LocallyOfFiniteType f] [IsSeparated f]
  (x : Spec S.functionField ⟶ X) (hx : x ≫ f = S.fromSpecStalk (genericPoint S))

/-- The **specialization** `sp_s(x)` of a `K(S)`-rational point `x` of the generic fibre of `f`
to the fibre over `s`: the fibre point over `s` of the unique section of `f` extending `x`. Here
`S` is an integral scheme whose local rings are valuation rings (for instance a Dedekind scheme)
and `f` is universally closed, separated and locally of finite type (for instance proper). -/
def specializePoint (s : S) : Spec (S.residueField s) ⟶ f.fiber s :=
  f.fiberPointOfSection ((f.sectionEquivOfValuationRing hS).symm ⟨x, hx⟩).property s

/-- The specialization of `x` is the fibre point of any section of `f` extending `x`. -/
theorem specializePoint_eq_fiberPointOfSection {σ : S ⟶ X} (hσ : σ ≫ f = 𝟙 S)
    (hσx : S.fromSpecStalk (genericPoint S) ≫ σ = x) (s : S) :
    f.specializePoint hS x hx s = f.fiberPointOfSection hσ s := by
  have h : (f.sectionEquivOfValuationRing hS).symm ⟨x, hx⟩ = ⟨σ, hσ⟩ :=
    (Equiv.symm_apply_eq _).mpr <| Subtype.ext <|
      hσx.symm.trans (f.sectionEquivOfValuationRing_apply_coe hS ⟨σ, hσ⟩).symm
  simp only [specializePoint, h]

/-- The specialization of `x` maps to the section extending `x` in the total space. -/
@[reassoc (attr := simp)]
lemma specializePoint_fiberι (s : S) :
    f.specializePoint hS x hx s ≫ f.fiberι s =
      S.fromSpecResidueField s ≫ ((f.sectionEquivOfValuationRing hS).symm ⟨x, hx⟩).val :=
  fiberPointOfSection_fiberι _ _ _

/-- The specialization of `x` is a `κ(s)`-rational point of the fibre over `s`. -/
@[reassoc (attr := simp)]
lemma specializePoint_fiberToSpecResidueField (s : S) :
    f.specializePoint hS x hx s ≫ f.fiberToSpecResidueField s = 𝟙 _ :=
  fiberPointOfSection_fiberToSpecResidueField _ _ _

/-- The specialization of `x` over `s` is the point over `s` of the section extending `x`. -/
@[simp]
lemma fiberι_specializePoint_apply (s : S) (p : Spec (S.residueField s)) :
    f.fiberι s (f.specializePoint hS x hx s p) =
      ((f.sectionEquivOfValuationRing hS).symm ⟨x, hx⟩).val s :=
  fiberι_fiberPointOfSection_apply _ _ _ _

/-- **Specialization to the generic fibre is restriction**: over the generic point of `S`, the
specialization of `x` is `x` itself, read through `Spec κ(η) ⟶ Spec K(S)`; since the local ring
`K(S)` at the generic point is a field, this map is an isomorphism. -/
theorem specializePoint_genericPoint_fiberι :
    f.specializePoint hS x hx (genericPoint S) ≫ f.fiberι (genericPoint S) =
      Spec.map (S.residue (genericPoint S)) ≫ x := by
  rw [specializePoint_fiberι, fromSpecResidueField, Category.assoc,
    fromSpecStalk_sectionEquivOfValuationRing_symm_apply_coe]

/-- **Specialization commutes with morphisms of families**: for `j : Y ⟶ X` over `S`, the
specialization of a rational point `y` of the generic fibre of `j ≫ f` maps to the
specialization of `y ≫ j`. -/
@[reassoc (attr := simp)]
theorem specializePoint_fiberCompMap (j : Y ⟶ X) [UniversallyClosed (j ≫ f)]
    [LocallyOfFiniteType (j ≫ f)] [IsSeparated (j ≫ f)] (y : Spec S.functionField ⟶ Y)
    (hy : y ≫ j ≫ f = S.fromSpecStalk (genericPoint S)) (s : S) :
    (j ≫ f).specializePoint hS y hy s ≫ j.fiberCompMap f s =
      f.specializePoint hS (y ≫ j) (by rw [Category.assoc, hy]) s := by
  set σ := ((j ≫ f).sectionEquivOfValuationRing hS).symm ⟨y, hy⟩
  rw [specializePoint, fiberPointOfSection_fiberCompMap,
    specializePoint_eq_fiberPointOfSection hS f _ _ (σ := σ.val ≫ j) _ (by
      rw [← Category.assoc, fromSpecStalk_sectionEquivOfValuationRing_symm_apply_coe])]

/-- **Specialization commutes with base change.** Consider a commutative square of families
`f' : X' ⟶ S'` over `f : X ⟶ S`, along `g : S' ⟶ S`, where `S'` is again an integral scheme
whose local rings are valuation rings and `f'` is universally closed, separated and locally of
finite type. Let `x'` be a rational point of the generic fibre of `f'` lying over `x` through a
map `φ : K(S) ⟶ K(S')` of function fields. Then the specialization of `x'` to the fibre over
`s'` maps to the specialization of `x` to the fibre over `g s'`, after extending scalars along
`κ(g s') ⟶ κ(s')`. This covers restriction to an open of `S`, localization at a point and
extension of a discrete valuation ring. -/
@[reassoc]
theorem specializePoint_fiberBaseChangeMap {X' S' : Scheme.{u}} [IsIntegral S']
    (hS' : ∀ s' : S', ValuationRing (S'.presheaf.stalk s')) {f' : X' ⟶ S'}
    [UniversallyClosed f'] [LocallyOfFiniteType f'] [IsSeparated f'] {g : S' ⟶ S}
    {g' : X' ⟶ X} (H : CommSq g' f' f g) (φ : S.functionField ⟶ S'.functionField)
    (x' : Spec S'.functionField ⟶ X') (hx' : x' ≫ f' = S'.fromSpecStalk (genericPoint S'))
    (hxx' : x' ≫ g' = Spec.map φ ≫ x) (s' : S') :
    f'.specializePoint hS' x' hx' s' ≫ H.fiberBaseChangeMap s' =
      Spec.map (g.residueFieldMap s') ≫ f.specializePoint hS x hx (g s') := by
  set σ := (f.sectionEquivOfValuationRing hS).symm ⟨x, hx⟩
  set σ' := (f'.sectionEquivOfValuationRing hS').symm ⟨x', hx'⟩
  -- the generic point of `S'` maps to that of `S` through `φ`
  have hg : S'.fromSpecStalk (genericPoint S') ≫ g =
      Spec.map φ ≫ S.fromSpecStalk (genericPoint S) := by
    rw [← hx', Category.assoc, ← H.w, ← Category.assoc, hxx', Category.assoc, hx]
  -- `σ'` lies over `σ`: both are morphisms `S' ⟶ X` over `S` that agree at the generic point
  have hσσ' : σ'.val ≫ g' = g ≫ σ.val := by
    refine ext_of_isDominant_of_isSeparated f ?_ (S'.fromSpecStalk (genericPoint S')) ?_
    · rw [Category.assoc, H.w, ← Category.assoc, σ'.property, Category.assoc, σ.property]
      simp
    · rw [← Category.assoc, fromSpecStalk_sectionEquivOfValuationRing_symm_apply_coe, hxx',
        ← Category.assoc, hg, Category.assoc,
        fromSpecStalk_sectionEquivOfValuationRing_symm_apply_coe]
  exact fiberPointOfSection_fiberBaseChangeMap f σ.property H σ'.property hσσ' s'

/-- **Specializations on a regular scheme are smooth points.** If `f` is moreover locally of
finite presentation and all local rings of `X` are regular, then every specialization of a
rational point of the generic fibre lies in the smooth locus of `f`. This holds also over
imperfect residue fields. Regularity of `X` cannot be weakened to normality: over a discrete
valuation ring with uniformizer `π`, the section `x = y = π` of the normal scheme `xy = π²` passes
through its singular point. -/
theorem fiberι_specializePoint_mem_smoothLocus [LocallyOfFinitePresentation f]
    [∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)] (s : S) (p : Spec (S.residueField s)) :
    f.fiberι s (f.specializePoint hS x hx s p) ∈ f.smoothLocus := by
  set σ := (f.sectionEquivOfValuationRing hS).symm ⟨x, hx⟩
  -- the local ring of `S` at `s` is a quotient of the Noetherian local ring of `X` at `σ s`,
  -- so it is a Noetherian valuation ring, hence a regular local ring
  have : SurjectiveOnStalks (σ.val ≫ f) := by rw [σ.property]; infer_instance
  have := SurjectiveOnStalks.of_comp σ.val f
  have := isNoetherianRing_of_surjective _ _ _ (σ.val.stalkMap_surjective s)
  have := hS s
  rw [fiberι_specializePoint_apply]
  exact f.mem_smoothLocus_of_isRegularLocalRing σ.property s

end Specialization

end AlgebraicGeometry.Scheme.Hom
