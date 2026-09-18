/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

/-!
# The presentation limit on a rational open is `A⟨T/s⟩`

Wedhorn §8.1 defines `𝒪_X(V)` for an open `V ⊆ Spa(A,A⁺)` as the limit of `A⟨T/s⟩` over the
rational subsets `R(T/s) ⊆ V`, and states that on a rational open `U = R(T/s)` this limit is
`A_U = A⟨T/s⟩` again. This file proves that statement for `presentationLimit`, the limit indexed by
admissible presentations: when `A⁺` consists of power-bounded elements, the projection of
`presentationLimit Aplus R(T/s)` at the presentation `(T, s)` itself is an isomorphism, and under
these isomorphisms the restriction maps of `presentationLimitPresheaf` between rational opens are
the comparison maps of Wedhorn's Proposition 8.2(1).

## The argument

For a containment `R(T'/s') ⊆ R(T/s)` there is a unique continuous homomorphism
`A⟨T/s⟩ → A⟨T'/s'⟩` compatible with the structure maps from `A`
(`existsUnique_continuous_ringHom_of_rationalSubset_subset`); `homOfRationalSubsetSubset` is it as
a morphism of `CompleteSeparatedTopCommRingCat`. Uniqueness makes these maps functorial, and
identifies every restriction map of a refinement with one of them.

If `V ⊆ R(T/s)` and `(T, s)` is an index of `V`, the comparison maps out of `A⟨T/s⟩` form a cone
over the diagram of `V`, which gives an inverse to the projection at `(T, s)`. That the projection
is also injective comes from the key identity `presentationLimitπ_eq_π_comp`: the projection at any
index `j` factors through the projection at any index `i` with `R(j) ⊆ R(i)`. To prove it, pass to
the common refinement `k` of `i` and `j`, which presents `R(i) ∩ R(j) = R(j)`. The restriction map
`A_j → A_k` is then a split monomorphism, since the comparison map back is a left inverse.

## Main definitions

* `TauCeti.ValuationSpectrum.homOfRationalSubsetSubset` : the comparison morphism
  `A⟨T/s⟩ ⟶ A⟨T'/s'⟩` of a containment `R(T'/s') ⊆ R(T/s)`.
* `TauCeti.ValuationSpectrum.presentationLimitRationalIso` : the isomorphism
  `presentationLimit Aplus R(T/s) ≅ A⟨T/s⟩` for an admissible presentation `(T, s)`.

## Main results

* `TauCeti.ValuationSpectrum.restrictionHom_eq_homOfRationalSubsetSubset` : the restriction
  morphism of a refinement is the comparison morphism of the containment it induces.
* `TauCeti.ValuationSpectrum.presentationLimitπ_eq_π_comp` : projections of the limit factor
  through each other along comparison morphisms.
* `TauCeti.ValuationSpectrum.isIso_presentationLimitπ` : the projection at an index whose
  rational subset contains `V` is an isomorphism.
* `TauCeti.ValuationSpectrum.presentationLimitRationalIso_inv_comp_map_comp_hom` : between rational
  opens, the restriction maps of `presentationLimitPresheaf` are the comparison morphisms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.2(1).
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A}

/-! ### Comparison morphisms between completed rational localizations -/

omit [IsTopologicalRing A] in
/-- **A refinement of presentations shrinks the rational subset**: if `q` refines `p`, then
`R(q) ⊆ R(p)`. -/
theorem rationalSubset_subset_rationalSubset_of_le (Aplus : Subring A) {p q : Presentation P}
    (h : p ≤ q) : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den := by
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h
  rw [hr]
  exact rationalSubset_mul_subset_rationalSubset Aplus hT

/-- **The comparison morphism of a containment** `R(q) ⊆ R(p)`: Wedhorn's Proposition 8.2(1) map
`A⟨p⟩ → A⟨q⟩`, the unique continuous ring homomorphism compatible with the structure maps from `A`,
as a morphism of `CompleteSeparatedTopCommRingCat`. -/
noncomputable def homOfRationalSubsetSubset (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q : Presentation P}
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den) :
    p.completionLocObj ⟶ q.completionLocObj :=
  completionLocObjHom P p.num p.den _ p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower
    (ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower q.num q.den _
      q.hasDenominatorPower h)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower
      q.num q.den _ q.hasDenominatorPower h)

/-- The comparison morphism of `R(p) ⊆ R(p)` is the identity. -/
@[simp]
theorem homOfRationalSubsetSubset_self (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p : Presentation P}
    (h : rationalSubset Aplus p.num p.den ⊆ rationalSubset Aplus p.num p.den) :
    homOfRationalSubsetSubset Aplus hAplus h = 𝟙 p.completionLocObj :=
  completionLocObjHom_eq_id P p.num p.den _ p.hasDenominatorPower _ _
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus p.num p.den _
      p.hasDenominatorPower p.num p.den _ p.hasDenominatorPower h)

/-- Comparison morphisms compose along a chain of containments. -/
@[reassoc (attr := simp)]
theorem homOfRationalSubsetSubset_comp (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q w : Presentation P}
    (h₁ : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den)
    (h₂ : rationalSubset Aplus w.num w.den ⊆ rationalSubset Aplus q.num q.den) :
    homOfRationalSubsetSubset Aplus hAplus h₁ ≫ homOfRationalSubsetSubset Aplus hAplus h₂ =
      homOfRationalSubsetSubset Aplus hAplus (h₂.trans h₁) :=
  (completionLocObjHom_eq_comp P p.num p.den _ p.hasDenominatorPower q.num q.den _
    q.hasDenominatorPower w.num w.den _ w.hasDenominatorPower _ _ _ _ _ _
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus _ _ _ _ _ _ _ _ h₁)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus _ _ _ _ _ _ _ _ h₂)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus _ _ _ _ _ _ _ _
      (h₂.trans h₁))).symm

/-- **The restriction morphism of a refinement is a comparison morphism**: both are continuous
and compatible with the structure maps from `A`, which determines the map. -/
theorem restrictionHom_eq_homOfRationalSubsetSubset (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q : Presentation P} (h : p ≤ q) :
    Presentation.restrictionHom h =
      homOfRationalSubsetSubset Aplus hAplus
        (rationalSubset_subset_rationalSubset_of_le Aplus h) := by
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h
  rw [Presentation.restrictionHom_eq h r hr hT, restrictionObjHom_eq_completionLocObjHom]
  -- both are `completionLocObjHom` of a ring homomorphism; the two ring homomorphisms agree by
  -- the uniqueness in Proposition 8.2(1)
  unfold homOfRationalSubsetSubset
  congr 1
  exact eq_ringHomOfRationalSubsetSubset P Aplus hAplus _ _ _ _ _ _ _ _ _ _
    (continuous_restrictionRingHom P _ _ _ _ _ _ _ _ r hr hT)
    (restrictionRingHom_comp_toCompletionLoc P _ _ _ _ _ _ _ _ r hr hT)

/-! ### The projections of the presentation limit -/

variable {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- **Projections factor through comparison morphisms**: if `R(j) ⊆ R(i)` for two indices of `V`,
the projection of the limit at `j` is the projection at `i` followed by the comparison morphism
`A⟨i⟩ → A⟨j⟩`. -/
theorem presentationLimitπ_eq_π_comp (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (i j : PresentationIndex (P := P) Aplus V)
    (h : rationalSubset Aplus j.pres.num j.pres.den ⊆ rationalSubset Aplus i.pres.num i.pres.den) :
    presentationLimitπ Aplus V j =
      presentationLimitπ Aplus V i ≫ homOfRationalSubsetSubset Aplus hAplus h := by
  -- `k` refines `j` and `i`, and presents `R(j) ∩ R(i) = R(j)`
  let k := j.commonRefinement i
  have hk : rationalSubset Aplus j.pres.num j.pres.den ⊆
      rationalSubset Aplus k.pres.num k.pres.den := by
    rw [PresentationIndex.commonRefinement_pres, rationalSubset_commonRefinement]
    exact Set.subset_inter subset_rfl h
  -- the restriction `A_j → A_k` has the comparison map back as a left inverse
  have hsplit : Presentation.restrictionHom (j.le_commonRefinement_left i) ≫
      homOfRationalSubsetSubset Aplus hAplus hk = 𝟙 _ := by
    rw [restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus, homOfRationalSubsetSubset_comp,
      homOfRationalSubsetSubset_self]
  calc presentationLimitπ Aplus V j
      = presentationLimitπ Aplus V j ≫ Presentation.restrictionHom (j.le_commonRefinement_left i) ≫
          homOfRationalSubsetSubset Aplus hAplus hk := by rw [hsplit, Category.comp_id]
    _ = presentationLimitπ Aplus V k ≫ homOfRationalSubsetSubset Aplus hAplus hk := by
        rw [← presentationLimitπ_comp_map (P := P) (homOfLE (j.le_commonRefinement_left i)),
          Category.assoc, presentationIndexDiagram_map]
    _ = presentationLimitπ Aplus V i ≫ homOfRationalSubsetSubset Aplus hAplus h := by
        rw [← presentationLimitπ_comp_map (P := P) (homOfLE (j.le_commonRefinement_right i)),
          Category.assoc, presentationIndexDiagram_map,
          restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus, homOfRationalSubsetSubset_comp]

/-- **The projection at an index whose rational subset contains `V` is an isomorphism**: then
`R(i) = V`, and the limit over the presentations inside `V` is `A⟨i⟩`. -/
theorem isIso_presentationLimitπ (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (i : PresentationIndex (P := P) Aplus V) (hV : V ≤ spaBasicOpen Aplus i.pres.num i.pres.den) :
    IsIso (presentationLimitπ Aplus V i) := by
  -- the comparison morphisms out of `A⟨i⟩` form a cone over the diagram of `V`
  let c : Cone (presentationIndexDiagram (P := P) Aplus V) :=
    { pt := (presentationIndexDiagram (P := P) Aplus V).obj i
      π :=
        { app j := homOfRationalSubsetSubset Aplus hAplus (j.rationalSubset_subset hV)
          naturality j₁ j₂ f := by
            dsimp
            rw [Category.id_comp, restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus,
              homOfRationalSubsetSubset_comp] } }
  refine ⟨presentationLimitLift Aplus V c, ?_, ?_⟩
  · refine presentationLimit_hom_ext fun j ↦ ?_
    rw [Category.assoc, presentationLimitLift_comp_π, Category.id_comp]
    exact (presentationLimitπ_eq_π_comp hAplus i j _).symm
  · exact (presentationLimitLift_comp_π Aplus V c i).trans
      (homOfRationalSubsetSubset_self Aplus hAplus _)

variable (Aplus) in
/-- **The presentation limit on a rational open is its coordinate ring**: for an admissible
presentation `p`, the limit over the presentations inside `R(p)` is isomorphic to `A⟨p⟩` by the
projection at `p` itself (`presentationLimitRationalIso_hom`). This is Wedhorn §8.1's
`𝒪_X(U) = A_U`, stated for `presentationLimit`. -/
noncomputable def presentationLimitRationalIso (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    presentationLimit (P := P) Aplus (spaBasicOpen Aplus p.num p.den) ≅ p.completionLocObj :=
  haveI := isIso_presentationLimitπ (V := spaBasicOpen Aplus p.num p.den) hAplus ⟨p, hp, le_rfl⟩
    le_rfl
  asIso (presentationLimitπ Aplus _ ⟨p, hp, le_rfl⟩)

variable (Aplus) in
/-- The isomorphism `presentationLimitRationalIso` is the projection at the presentation itself. -/
@[simp]
theorem presentationLimitRationalIso_hom (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    (presentationLimitRationalIso Aplus hAplus p hp).hom =
      presentationLimitπ Aplus (spaBasicOpen Aplus p.num p.den) ⟨p, hp, le_rfl⟩ :=
  (rfl)

variable (Aplus) in
/-- The inverse of `presentationLimitRationalIso`, followed by the projection at an index `j`, is
the comparison morphism `A⟨p⟩ → A⟨j⟩`. -/
@[simp]
theorem presentationLimitRationalIso_inv_comp_π (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (j : PresentationIndex (P := P) Aplus (spaBasicOpen Aplus p.num p.den)) :
    (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
        presentationLimitπ Aplus (spaBasicOpen Aplus p.num p.den) j =
      homOfRationalSubsetSubset Aplus hAplus (j.rationalSubset_subset le_rfl) := by
  rw [Iso.inv_comp_eq, presentationLimitRationalIso_hom]
  exact presentationLimitπ_eq_π_comp hAplus _ j _

/-- A comparison morphism followed by the transport along an equality of presentations is again
a comparison morphism. -/
private theorem homOfRationalSubsetSubset_comp_eqToHom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q q' : Presentation P} (e : q = q')
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den)
    (h' : rationalSubset Aplus q'.num q'.den ⊆ rationalSubset Aplus p.num p.den)
    (e' : q.completionLocObj = q'.completionLocObj) :
    homOfRationalSubsetSubset Aplus hAplus h ≫ eqToHom e' =
      homOfRationalSubsetSubset Aplus hAplus h' := by
  subst e
  rw [eqToHom_refl, Category.comp_id]

variable (Aplus) in
/-- **Between rational opens, restriction is the comparison morphism**: for admissible
presentations `p` and `q` with `R(q) ⊆ R(p)`, the restriction map of the presentation limit from
`R(p)` to `R(q)` becomes, under `presentationLimitRationalIso`, the comparison morphism of
Wedhorn's Proposition 8.2(1). -/
theorem presentationLimitRationalIso_inv_comp_map_comp_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (hq : IsOpen (Ideal.span (q.num : Set A) : Set A))
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den) :
    (presentationLimitRationalIso Aplus hAplus p hp).inv ≫ presentationLimitMap (P := P) h ≫
        (presentationLimitRationalIso Aplus hAplus q hq).hom =
      homOfRationalSubsetSubset Aplus hAplus
        (spaBasicOpen_le_spaBasicOpen_iff.mp h) := by
  rw [presentationLimitRationalIso_hom, presentationLimitMap_comp_π,
    reassoc_of% presentationLimitRationalIso_inv_comp_π]
  exact homOfRationalSubsetSubset_comp_eqToHom hAplus (presentationIndexRestrict_obj_pres h _) _ _ _

end

end TauCeti.ValuationSpectrum
