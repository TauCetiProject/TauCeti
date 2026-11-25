/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Family
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic
public import TauCeti.AlgebraicGeometry.Fibers.SchematicDensity
public import TauCeti.AlgebraicGeometry.SpecialFiber.Components

/-!
# Generic fibres of models over a discrete valuation ring

This file defines the canonical inclusion of a model's chosen generic fibre into its total space.
It records compatibility with the structure morphism and proves that the inclusion is an open
immersion and an affine morphism, with scheme-theoretically dense image. A morphism of total spaces
over the base is compatible with the chosen generic fibres exactly when it commutes with these
inclusions.
Conversely, a flat finitely presented scheme over the discrete valuation ring together with a
pullback square exhibiting a prescribed scheme over the fraction field as its generic fibre is a
model (`TauCeti.Model.ofIsPullback`).

When the model is a family of curves, so is its generic fibre.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- The chosen generic fibre of a model, included into its total space. -/
noncomputable def genericι (M : Model R K C toK) : C ⟶ M.total :=
  M.genericFiberIso.inv.left ≫ genericFiberι R K M.toBase

/-- The chosen generic-fibre inclusion is the pullback projection transported along the
model's prescribed generic-fibre identification. -/
lemma genericι_def (M : Model R K C toK) :
    M.genericι = M.genericFiberIso.inv.left ≫ genericFiberι R K M.toBase :=
  (rfl)

/-- A morphism of models restricts to the prescribed identification on the generic fibre. -/
@[reassoc (attr := simp)]
lemma genericι_hom {M N : Model R K C toK} (f : M ⟶ N) :
    M.genericι ≫ f.hom = N.genericι := by
  have h : M.genericFiberIso.inv.left ≫ M.baseChangeHom f.hom f.overBase =
      N.genericFiberIso.inv.left := by
    rw [← cancel_mono N.genericFiberIso.hom.left]
    simp only [Category.assoc, f.genericFiber, Over.inv_left_hom_left]
  rw [genericι_def, genericι_def, Category.assoc,
    ← M.baseChangeHom_genericFiberι f.hom f.overBase, ← Category.assoc, h]

/-- Precomposed with the chosen identification of the generic fibre with `C`, the inclusion of a
model's chosen generic fibre is the canonical inclusion of the generic fibre. -/
@[reassoc (attr := simp)]
lemma genericFiberIso_hom_left_genericι (M : Model R K C toK) :
    M.genericFiberIso.hom.left ≫ M.genericι = genericFiberι R K M.toBase := by
  rw [genericι, Over.hom_left_inv_left_assoc]

/-- The inclusion of a model's chosen generic fibre lies over the fraction-field morphism. -/
@[reassoc (attr := simp)]
lemma genericι_toBase (M : Model R K C toK) :
    M.genericι ≫ M.toBase =
      toK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [genericι, Category.assoc, genericFiberι_toBase, ← Category.assoc, Over.w]
  rfl

/-- The square defining a model's chosen generic fibre is a pullback. -/
lemma isPullback_genericι (M : Model R K C toK) :
    IsPullback M.genericι toK M.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  refine (isPullback_genericFiber R K M.toBase).of_iso (Comma.leftIso M.genericFiberIso)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · have hleft :
        (Comma.leftIso M.genericFiberIso).hom = M.genericFiberIso.hom.left := rfl
    rw [hleft, genericFiberIso_hom_left_genericι]
    simp
  · exact M.genericFiberIso.hom.w.symm
  · simp
  · simp

/-- A model's chosen generic fibre is an open subscheme of its total space. -/
lemma isOpenImmersion_genericι (M : Model R K C toK) : IsOpenImmersion M.genericι := by
  let : IsOpenImmersion (genericFiberι R K M.toBase) :=
    isOpenImmersion_genericFiberι R K M.toBase
  let : IsIso M.genericFiberIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericFiberIso.inv))
  rw [genericι]
  infer_instance

/-- The inclusion of a model's chosen generic fibre is an affine morphism, being a base change of
`Spec K ⟶ Spec R`. -/
instance isAffineHom_genericι (M : Model R K C toK) : IsAffineHom M.genericι := by
  have : IsIso M.genericFiberIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericFiberIso.inv))
  have : IsAffineHom (genericFiberι R K M.toBase) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip
      (inferInstanceAs (IsAffineHom (Spec.map _)))
  rw [genericι_def]
  infer_instance

/-- A model's chosen generic fibre is scheme-theoretically dense in its total space, since the
total space is flat over the discrete valuation ring. -/
instance isSchemeTheoreticallyDominant_genericι (M : Model R K C toK) :
    IsSchemeTheoreticallyDominant M.genericι := by
  have : IsIso M.genericFiberIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericFiberIso.inv))
  have := isSchemeTheoreticallyDominant_genericFiberι R K (IsFractionRing.injective R K) M.toBase
  rw [genericι_def]
  infer_instance

section OfIsPullback

variable {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [Flat toBase]
  [LocallyOfFinitePresentation toBase] [QuasiCompact toBase] [QuasiSeparated toBase] {j : C ⟶ X}

/-- The model with total space `X` determined by a pullback square exhibiting `C` as the generic
fibre of `X`. Its generic-fibre identification is the canonical comparison of `C` with the chosen
pullback, so that its generic-fibre inclusion is `j` (`TauCeti.Model.genericι_ofIsPullback`).
This is the converse of `TauCeti.Model.isPullback_genericι`. -/
def ofIsPullback (h : IsPullback j toK toBase (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    Model R K C toK where
  total := X
  toBase := toBase
  flat := ‹_›
  locallyOfFinitePresentation := ‹_›
  quasiCompact := ‹_›
  quasiSeparated := ‹_›
  genericFiberIso := Over.isoMk h.isoPullback.symm (IsPullback.isoPullback_inv_snd _)

variable (h : IsPullback j toK toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- The total space of the model given by a pullback square is the scheme in that square. -/
@[simp]
lemma ofIsPullback_total : (ofIsPullback toBase h).total = X :=
  (rfl)

/-- The structure morphism of the model given by a pullback square is the morphism in that
square. -/
@[simp]
lemma ofIsPullback_toBase :
    (ofIsPullback toBase h).toBase = eqToHom (ofIsPullback_total toBase h) ≫ toBase :=
  (rfl)

/-- The generic-fibre inclusion of the model given by a pullback square is the morphism in that
square. -/
@[simp]
lemma genericι_ofIsPullback :
    (ofIsPullback toBase h).genericι = j ≫ eqToHom (ofIsPullback_total toBase h).symm := by
  rw [genericι_def]
  -- By definition of `ofIsPullback`, the inverse generic-fibre identification is
  -- `h.isoPullback.hom` and the `eqToHom` is the identity of `X`.
  exact (h.isoPullback_hom_fst).trans (Category.comp_id j).symm

end OfIsPullback

/-- The set-theoretic image of a model's chosen generic fibre in its total space is the complement
of the special fibre. -/
theorem range_genericι_eq_setOf_base_ne_closedPoint (M : Model R K C toK) :
    Set.range M.genericι = {x : M.total | M.toBase x ≠ closedPoint R} := by
  have : IsIso M.genericFiberIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericFiberIso.inv))
  rw [M.genericι_def]
  calc Set.range (M.genericFiberIso.inv.left ≫ genericFiberι R K M.toBase)
      = Set.range (genericFiberι R K M.toBase ∘ M.genericFiberIso.inv.left) :=
        congrArg Set.range (funext fun x ↦ Scheme.Hom.comp_apply _ _ x)
    _ = Set.range (genericFiberι R K M.toBase) :=
        M.genericFiberIso.inv.left.surjective.range_comp _
    _ = {x : M.total | M.toBase x ≠ closedPoint R} :=
        range_genericFiberι_of_isDiscreteValuationRing R K M.toBase

/-- The image of a model's chosen generic fibre in its total space is the basic open of the
pullback of a nonzero element `π` of the maximal ideal, such as a uniformizer. -/
theorem range_genericι_eq_basicOpen (M : Model R K C toK) {π : R}
    (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    Set.range M.genericι =
      M.total.basicOpen (M.toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π)) := by
  rw [M.range_genericι_eq_setOf_base_ne_closedPoint]
  ext x
  refine (not_congr (M.toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0 x)).trans ?_
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not]

/-- If the total space of a model `M` is irreducible, then its generic fibre `C` is nonempty. -/
theorem nonempty_generic (M : Model R K C toK) [IrreducibleSpace M.total] : Nonempty C :=
  (M.toBase.nonempty_genericFiber_of_base_ne_closedPoint K
    (M.toBase.base_genericPoint_ne_closedPoint (IsDiscreteValuationRing.not_a_field R))).map
    M.genericFiberIso.hom.left

/-- A morphism of total spaces over the base respects the chosen identifications of generic fibres
as soon as it carries the chosen generic fibre of `M` to that of `N`. This is the converse of
`TauCeti.Model.genericι_hom`. -/
lemma baseChangeHom_genericFiberIso_hom_left {M N : Model R K C toK} (f : M.total ⟶ N.total)
    (overBase : f ≫ N.toBase = M.toBase) (h : M.genericι ≫ f = N.genericι) :
    M.baseChangeHom f overBase ≫ N.genericFiberIso.hom.left = M.genericFiberIso.hom.left := by
  have := N.isOpenImmersion_genericι
  rw [← cancel_mono N.genericι, Category.assoc, genericFiberIso_hom_left_genericι,
    baseChangeHom_genericFiberι, ← h, genericFiberIso_hom_left_genericι_assoc]

/-- If a model is a family of curves, then so is its chosen generic fibre over the fraction
field. -/
lemma familyOfCurves_toK (M : Model R K C toK) [AlgebraicGeometry.FamilyOfCurves M.toBase] :
    AlgebraicGeometry.FamilyOfCurves toK :=
  .of_isPullback M.isPullback_genericι

end Model

end TauCeti
