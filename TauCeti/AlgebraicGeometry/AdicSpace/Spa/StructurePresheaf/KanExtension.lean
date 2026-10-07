/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic
public import TauCeti.Topology.Sheaves.Adapted

/-!
# The structure presheaf is the limit of its values on rational opens

Wedhorn §8.1 defines `𝒪_X(V)`, for an open `V ⊆ Spa(A, A⁺)`, as the limit of `𝒪_X(W)` over the
rational opens `W ⊆ V`. This file proves that `presentationLimitPresheaf`, whose value at `V` is a
limit over presentations, has this property naturally in `V`: it is the pointwise right Kan
extension of its restriction to the rational opens (`rationalOpensFunctor`). Since the rational
opens form a basis, a right Kan extension along their inclusion of a sheaf for the restricted
topology is a sheaf, so the sheaf condition on `Spa(A, A⁺)` reduces to the rational opens, as in
the proof of Wedhorn's Proposition A.4.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPresheafIsPointwiseRightKanExtension` :
  `presentationLimitPresheaf` is the pointwise right Kan extension of its restriction to the
  rational opens.

## Main results

* `TauCeti.ValuationSpectrum.isAdapted_presentationLimitPresheaf` :
  `presentationLimitPresheaf` is adapted to the rational opens, in the sense of
  `TopCat.Presheaf.IsAdapted`.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_isSheaf_rational` :
  `presentationLimitPresheaf` is a sheaf once its restriction to the rational opens is a sheaf for
  the restricted topology.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition A.4.
* M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
  (SGA 4), Tome 1, Exposé III, 2.2: a right Kan extension of a sheaf along a cocontinuous functor
  is a sheaf. This is Mathlib's `CategoryTheory.ran_isSheaf_of_isCocontinuous`; see also
  The Stacks Project, [Tag 00XK](https://stacks.math.columbia.edu/tag/00XK).
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti.Huber

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}

/-! ### Indices as rational opens -/

section Lift

variable {V : Opens ↥(spa Aplus)}

/-- An index `i` of `V` as an object of the category of rational opens contained in `V`: the
rational open `R(i) = spaBasicOpen Aplus i.pres.num i.pres.den` together with its inclusion into
`V`. For `h : R(j) ≤ R(i)`, `StructuredArrow.homMk (InducedCategory.homMk h.hom).op` is a morphism
`i.toStructuredArrow ⟶ j.toStructuredArrow`. -/
-- `implicit_reducible`: statements below, and unification of implicit arguments, must see
-- `i.toStructuredArrow.right` as `R(i)`
@[implicit_reducible]
private def PresentationIndex.toStructuredArrow (i : PresentationIndex (P := P) Aplus V) :
    StructuredArrow (op V) (rationalOpensFunctor Aplus).op :=
  -- `StructuredArrow.mk` elaborates `Y` before `T`, so `C` is given for the anonymous constructor
  StructuredArrow.mk (C := (InducedCategory _ (Subtype.val : spaRationalOpens Aplus → _))ᵒᵖ)
    (Y := op ⟨_, spaBasicOpen_mem_spaRationalOpens i.isOpen_span⟩) i.le_open.hom.op

/-- **Each projection factors through a rational open**: the projection of `presentationLimit V`
at an index `i` is the restriction to the rational open
`R(i) = spaBasicOpen Aplus i.pres.num i.pres.den` followed by the projection at the presentation
of `i`, read as an index of `R(i)`. -/
-- Not `@[simp]`: `presentationLimitMap_comp_πToPresentation` rewrites the left-hand side, so the
-- left-hand side is not in simp-normal form.
private theorem presentationLimitMap_le_open_comp_πToPresentation
    (i : PresentationIndex (P := P) Aplus V) :
    presentationLimitMap i.le_open ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩ =
      presentationLimitπToPresentation Aplus V i := by
  -- the index `i.pres` of `R(i)`, read as an index of `V`, is `i`, so the transport is trivial
  simp [PresentationIndex.ext_iff]

/-! ### Cones over the rational opens -/

variable (s : Cone (StructuredArrow.proj (op V) (rationalOpensFunctor Aplus).op ⋙
  (rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus))

/-- The legs of `s` at the rational opens `R(i)`, read at the presentations of the indices `i`,
are compatible with the restriction maps between presentations. -/
-- A named lemma rather than a proof inside `presentationLimitRationalLift`, so that
-- `presentationLimitRationalLift_comp_πToPresentation` can pass it to
-- `presentationIndexCone_lift_comp_πToPresentation`.
private theorem presentationLimitRationalLift_naturality {i j : PresentationIndex (P := P) Aplus V}
    (f : i ⟶ j) :
    (s.π.app i.toStructuredArrow ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩) ≫
          PairOfDefinition.Presentation.restrictionHom f.le =
      s.π.app j.toStructuredArrow ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
        presentationLimitπToPresentation Aplus _ ⟨j.pres, j.isOpen_span, le_rfl⟩ := by
  -- inside `presentationLimit R(i)`, the projection at `j` is the projection at `i` followed by
  -- restriction, and restricting `s` from `R(i)` to `R(j)` is naturality of `s`
  have h := spaBasicOpen_le_spaBasicOpen_iff.mpr <|
    rationalSubset_subset_rationalSubset_of_le Aplus f.le
  simp [presentationLimitπ_comp_restriction (j := ⟨j.pres, j.isOpen_span, h⟩),
    presentationLimitMap_le_open_comp_πToPresentation ⟨j.pres, j.isOpen_span, h⟩,
    ← s.w (StructuredArrow.homMk (InducedCategory.homMk h.hom).op :
      i.toStructuredArrow ⟶ j.toStructuredArrow)]

/-- **The morphism induced by a cone over the rational opens in `V`**: its projection at an index
`i` is the leg of `s` at the rational open `R(i) = spaBasicOpen Aplus i.pres.num i.pres.den`
followed by the projection at the presentation of `i`
(`presentationLimitRationalLift_comp_πToPresentation`), and its restriction to a rational open
`W ⊆ V` is the leg of `s` at `W` (`presentationLimitRationalLift_comp_presentationLimitMap`). -/
private noncomputable def presentationLimitRationalLift :
    s.pt ⟶ presentationLimit (P := P) Aplus V :=
  eqToHom (presentationIndexCone_pt Aplus V s.pt _ _).symm ≫
    presentationLimitLift Aplus V (presentationIndexCone Aplus V s.pt
      (fun i ↦ s.π.app i.toStructuredArrow ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩)
      (presentationLimitRationalLift_naturality s))

/-- The projection of `presentationLimitRationalLift s` at an index `i` is the leg of `s` at the
rational open `R(i) = spaBasicOpen Aplus i.pres.num i.pres.den`, followed by the projection at the
presentation of `i`, read as an index of `R(i)`. Together with
`presentationLimit_hom_ext_toPresentation`, this identifies `presentationLimitRationalLift s` as
the only morphism into `presentationLimit V` with these projections. -/
@[simp]
private theorem presentationLimitRationalLift_comp_πToPresentation (i : PresentationIndex Aplus V) :
    presentationLimitRationalLift s ≫ presentationLimitπToPresentation Aplus V i =
      s.π.app i.toStructuredArrow ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) ≫
        presentationLimitπToPresentation Aplus _ ⟨i.pres, i.isOpen_span, le_rfl⟩ := by
  rw [presentationLimitRationalLift, Category.assoc]
  exact presentationIndexCone_lift_comp_πToPresentation Aplus V s.pt _
    (presentationLimitRationalLift_naturality s) i

/-- **The induced morphism restricts to the legs of the cone**: for a rational open `W ⊆ V`, given
by `g` with `W = g.right.unop`, the lift `presentationLimitRationalLift s` followed by the
restriction map `presentationLimitMap` from `V` to `W` is the leg `s.π.app g`, read in
`presentationLimit W` along `presentationLimitPresheaf_obj`. -/
@[reassoc (attr := simp)]
private theorem presentationLimitRationalLift_comp_presentationLimitMap
    (g : StructuredArrow (op V) (rationalOpensFunctor Aplus).op) :
    presentationLimitRationalLift s ≫ presentationLimitMap (leOfHom g.hom.unop) =
      s.π.app g ≫ eqToHom (presentationLimitPresheaf_obj P Aplus _) := by
  refine presentationLimit_hom_ext_toPresentation fun j ↦ ?_
  -- the index of `V` with the presentation of `j`
  let k : PresentationIndex Aplus V := ⟨j.pres, j.isOpen_span, j.le_open.trans g.hom.unop.le⟩
  -- on both sides, projecting at `j` is restricting to `R(j)` and projecting there; on the left
  -- the two restrictions compose, giving the projection at `k`
  rw [← presentationLimitMap_le_open_comp_πToPresentation j, Category.assoc,
    reassoc_of% presentationLimitMap_comp, presentationLimitMap_le_open_comp_πToPresentation k]
  -- the lift's projection at `k` is through the leg of `s` at `R(j)`; by naturality of `s`, its
  -- leg at `R(j)` is its leg at `W` followed by restriction
  simp [k, -presentationLimitMap_comp_πToPresentation,
    ← s.w (StructuredArrow.homMk (InducedCategory.homMk j.le_open.hom).op :
      g ⟶ k.toStructuredArrow)]

end Lift

/-! ### The Kan extension and the sheaf condition -/

/-- **`presentationLimitPresheaf` is the right Kan extension of its restriction to the rational
opens**, pointwise: at every open `V`, its value with the restriction maps to the rational opens
`W ⊆ V` is a limit cone over those `W`. This is Wedhorn §8.1's description of `𝒪_X(V)` as the
limit of `𝒪_X(W)` over the rational `W ⊆ V`. -/
noncomputable def presentationLimitPresheafIsPointwiseRightKanExtension : (Functor.RightExtension.mk
    (presentationLimitPresheaf P Aplus) (𝟙 ((rationalOpensFunctor Aplus).op ⋙
      presentationLimitPresheaf P Aplus))).IsPointwiseRightKanExtension := fun V ↦
  IsLimit.mk (fun s ↦ presentationLimitRationalLift s ≫
      eqToHom (presentationLimitPresheaf_obj P Aplus V).symm)
    -- restricted to a rational open `W ⊆ V`, the lift is the leg of `s` at `W`
    (fun s g ↦ by simp)
    -- a morphism into `presentationLimit V` is determined by its projections at the indices of `V`
    (fun s m hm ↦ (comp_eqToHom_iff (presentationLimitPresheaf_obj P Aplus V) m _).mp <|
      presentationLimit_hom_ext_toPresentation fun i ↦ by
        simp [← hm, presentationLimitMap_le_open_comp_πToPresentation])

/-- **The legs of the Kan-extension cone are the restriction maps**: at an open `V`, the leg of
the cone of `presentationLimitPresheafIsPointwiseRightKanExtension` indexed by a rational open
`W ⊆ V` (an object `g` of the category of rational opens over `V`) is the restriction map from `V`
to `W`. -/
theorem presentationLimitPresheaf_coneAt_π_app (V : Opens ↥(spa Aplus))
    (g : StructuredArrow (op V) (rationalOpensFunctor Aplus).op) :
    ((Functor.RightExtension.mk (presentationLimitPresheaf P Aplus)
      (𝟙 ((rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus))).coneAt
        (op V)).π.app g =
      (presentationLimitPresheaf P Aplus).map (homOfLE (leOfHom g.hom.unop)).op := by
  simp

/-- **`presentationLimitPresheaf` is adapted to the rational opens**: at every open `V`, it is the
limit of its values on the rational opens `W ⊆ V`. This is Wedhorn §8.1's description of `𝒪_X(V)`
in the sense of Wedhorn's Remark and Definition 8.9. -/
theorem isAdapted_presentationLimitPresheaf :
    TopCat.Presheaf.IsAdapted (X := TopCat.of ↥(spa Aplus)) (presentationLimitPresheaf P Aplus)
      (spaRationalOpens Aplus) :=
  ⟨presentationLimitPresheafIsPointwiseRightKanExtension⟩

/-- **The sheaf condition on the rational opens suffices**: if the restriction of
`presentationLimitPresheaf` to the rational opens is a sheaf for the restricted topology, then
`presentationLimitPresheaf` is a sheaf on `Spa(A, A⁺)`. With the rational opens as the basis, this
is the step in the proof of Wedhorn's Proposition A.4 from a sheaf on the basis to a sheaf on the
whole space: `presentationLimitPresheaf` is adapted to the basis of rational opens, and a presheaf
adapted to a basis is a sheaf once it is a sheaf on the basis
(`TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology`). A sieve on a rational
open covers for the restricted topology exactly when its image covers in `Spa(A, A⁺)`
(`Functor.mem_restrictedTopology_iff`), so the hypothesis only involves covers of rational opens
by rational opens. -/
theorem isSheaf_presentationLimitPresheaf_of_isSheaf_rational (h : Presheaf.IsSheaf
      ((rationalOpensFunctor Aplus).restrictedTopology (Opens.grothendieckTopology ↥(spa Aplus)))
      ((rationalOpensFunctor Aplus).op ⋙ presentationLimitPresheaf P Aplus)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) :=
  -- `P` makes `A` a Huber ring, so the rational opens form a basis
  have : IsHuberRing A := ⟨⟨P⟩⟩
  TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology (X := TopCat.of ↥(spa Aplus))
    _ _ (isBasis_spaRationalOpens Aplus)
    (isAdapted_presentationLimitPresheaf (P := P) (Aplus := Aplus)) h

end TauCeti.ValuationSpectrum
