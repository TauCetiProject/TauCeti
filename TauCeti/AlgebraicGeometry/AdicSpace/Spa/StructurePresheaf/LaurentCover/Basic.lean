/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic
public import Mathlib.Topology.Maps.Basic

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections

/-!
# The Laurent cover for the presentation-limit presheaf

For `f ∈ A` the rational opens `R({f, 1}/1) = {|f| ≤ 1}` and `R({1}/f) = {|f| ≥ 1}` cover
`X = Spa(A, A⁺)`. When `A` is a complete Hausdorff strongly noetherian Tate ring and `A⁺` consists
of power-bounded elements, the augmented two-piece Čech sequence of the presentation-limit
presheaf is exact: sections glue uniquely, and every section on the overlap is a difference of
restrictions. This is Wedhorn's Lemma 8.33 and the Laurent-cover case of Lemma 8.34(i), stated
for `presentationLimit`. The degree-zero injectivity and gluing statements are transported from
the corresponding statements for `A` and the completed rational localisations of the pieces by
lemmas that take those ring-level statements as hypotheses, so they also apply when `A` is uniform
(Buzzard--Verberkmoes, Corollary 4). The topology induced by restriction is transported in the
same way.

## Main definitions

* `TauCeti.ValuationSpectrum.laurentCoverOpen` : the two pieces `R({f, 1}/1)` and `R({1}/f)` of
  the Laurent cover, indexed by `Bool`. Both are rational opens
  (`TauCeti.ValuationSpectrum.laurentCoverOpen_mem_spaRationalOpens`).

## Main results

* `TauCeti.ValuationSpectrum.laurentCoverOpen_inv_mul_true` and
  `TauCeti.ValuationSpectrum.laurentCoverOpen_inv_mul_false` : for a unit `u`, the pieces of the
  Laurent cover of `u⁻¹ g` are `R({g, u}/u) = {|g| ≤ |u|}` and `R({u}/g) = {|g| ≥ |u|}`.
* `TauCeti.ValuationSpectrum.injective_presentationLimitMap_laurentCoverOpen` : restriction from
  `X` to the two pieces is injective.
* `TauCeti.ValuationSpectrum.exists_presentationLimitMap_eq_of_laurentCoverOpen` : sections over
  the two pieces that agree on their overlap come from a section over `X`.
* `TauCeti.ValuationSpectrum.surjective_presentationLimitMap_sub_laurentCoverOpen` : the difference
  of restrictions from the two pieces onto their overlap is surjective.
* `injective_presentationLimitMap_laurentCoverOpen_of_injective_toCompletionLoc` and
  `exists_presentationLimitMap_eq_of_laurentCoverOpen_of_exact_toCompletionLoc` : the degree-zero
  statements for any complete Hausdorff `A`, assuming their ring-level counterparts.
* `isClosedEmbedding_presentationLimitMap_laurentCoverOpen_of_isClosedEmbedding_toCompletionLoc` :
  the analogous transport for the topology on sections.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.33 and Lemma 8.34(i).
* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25--39, Corollary 4.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

-- Decidable equality is only used to write the numerator sets `{f, 1}`, `{1}` and
-- `{f * f, f, 1}`, so it is supplied classically rather than assumed of `A`.
attribute [local instance] Classical.decEq

/-! ### Elements under equality transports -/

-- An equality transport of topological rings is undone by the reverse transport. This is
-- `(eqToIso e).hom_inv_id_apply x` restated with `.1`, so that `rw` matches the `.1` terms here.
private theorem eqToHom_symm_apply_eqToHom_apply {X Y : TopCommRingCat.{v}} (e : X = Y) (x : X) :
    (eqToHom e.symm).1 ((eqToHom e).1 x) = x := (eqToIso e).hom_inv_id_apply x

-- The underlying map of an equality transport of topological rings is injective.
private theorem injective_eqToHom {X Y : TopCommRingCat.{v}} (e : X = Y) :
    Function.Injective (eqToHom e).1 :=
  Function.LeftInverse.injective (eqToHom_symm_apply_eqToHom_apply e)

/-! ### Restriction between rational opens -/

section Rational

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)

-- A set containing `1` spans the unit ideal, which is open.
omit [IsTopologicalRing A] in
private theorem isOpen_span_of_one_mem {s : Set A} (h : (1 : A) ∈ s) :
    IsOpen (Ideal.span s : Set A) := (Ideal.eq_top_iff_one _).2 (Ideal.subset_span h) ▸ isOpen_univ

-- The presentation `({f, 1}, 1)` (`true`) or `({1}, f)` (`false`) of a Laurent piece.
variable (P) in
private noncomputable abbrev laurentPresentation (f : A) (b : Bool) : Presentation P where
  num := cond b ({f, 1} : Finset A) ({1} : Finset A)
  den := cond b 1 f
  hasDenominatorPower := hasDenominatorPower_of_isOpen_span P _ _ _ <|
    isOpen_span_of_one_mem <| by cases b <;> simp

-- The presentation `({f², f, 1}, 1 · f)` of the overlap of the two Laurent pieces, spelled
-- `({f * f, f, 1}, 1 * f)` as in `laurentCover_exact` so that the two agree definitionally.
variable (P) in
private noncomputable abbrev laurentOverlapPresentation (f : A) : Presentation P where
  num := ({f * f, f, 1} : Finset A)
  den := 1 * f
  hasDenominatorPower := hasDenominatorPower_of_isOpen_span P _ _ _ <|
    isOpen_span_of_one_mem <| by simp

-- The numerator ideals of the Laurent pieces are open.
variable (P) in
private theorem isOpen_span_laurentPresentation (f : A) (b : Bool) :
    IsOpen (Ideal.span ((laurentPresentation P f b).num : Set A) : Set A) :=
  isOpen_span_of_one_mem <| by cases b <;> simp

-- Under `presentationLimitRationalIso`, restriction from `R(p)` to `R(q)` along a refinement with
-- cofactor `r` is `restrictionRingHom`.
private theorem rationalIso_map_apply (p q : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (hq : IsOpen (Ideal.span (q.num : Set A) : Set A)) (r : A) (hr : q.den = p.den * r)
    (hT : ∀ t ∈ p.num, t * r ∈ q.num)
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den)
    (z : presentationLimit (P := P) Aplus (spaBasicOpen Aplus p.num p.den)) :
    (eqToHom (completionLocObj_obj P q.num q.den _ q.hasDenominatorPower)).1
        ((presentationLimitRationalIso Aplus hAplus q hq).hom.hom.1
          ((presentationLimitMap h).hom.1 z)) =
      restrictionRingHom P p.num p.den _ p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower r
        hr hT ((eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus p hp).hom.hom.1 z)) := by
  have key := (Iso.inv_comp_eq _).1 <|
    (presentationLimitRationalIso_inv_comp_map_comp_hom Aplus hAplus p q hp hq h).trans <|
      (restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus
        (Presentation.le_def.mpr ⟨r, hr, hT⟩)).symm.trans (Presentation.restrictionHom_eq _ r hr hT)
  refine (congrArg (fun g ↦ (eqToHom (completionLocObj_obj ..)).1 (g.hom.1 z)) key).trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, restrictionObjHom_eq_completionLocObjHom,
    completionLocObjHom_hom]
  exact eqToHom_symm_apply_eqToHom_apply _ _

end Rational

/-! ### Restriction from the whole spectrum -/

section Top

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] {P : PairOfDefinition A} {Aplus : Subring A}
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)

-- Under `presentationLimitRationalIso`, restriction from the whole spectrum to `R(p)` is the
-- structure map `A → A⟨p⟩`.
private theorem rationalIso_map_top_apply (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (c : CompleteSeparatedTopCommRingCat.of A) :
    (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1
        ((presentationLimitRationalIso Aplus hAplus p hp).hom.hom.1
          ((presentationLimitMap le_top).hom.1 ((toPresentationLimit Aplus ⊤).hom.1 c))) =
      toCompletionLoc P p.num p.den _ p.hasDenominatorPower
        ((eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 c) := by
  have key : toPresentationLimit Aplus ⊤ ≫ presentationLimitMap le_top ≫
      (presentationLimitRationalIso Aplus hAplus p hp).hom = p.toCompletionLocObjHom := by simp
  refine (congrArg (fun g ↦ (eqToHom (completionLocObj_obj ..)).1 (g.hom.1 c)) key).trans ?_
  rw [Presentation.toCompletionLocObjHom_hom]
  exact eqToHom_symm_apply_eqToHom_apply _ _

-- Under `presentationLimitRationalIso`, the section of `c : A` over the whole spectrum restricts to
-- `z` over `R(p)` exactly when the structure map `A → A⟨p⟩` sends `c` to the image of `z`.
private theorem presentationLimitMap_apply_toPresentationLimit_apply_eq_iff (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) {c : CompleteSeparatedTopCommRingCat.of A}
    {z : presentationLimit (P := P) Aplus (spaBasicOpen Aplus p.num p.den)} :
    (presentationLimitMap le_top).hom.1 ((toPresentationLimit Aplus ⊤).hom.1 c) = z ↔
      toCompletionLoc P p.num p.den _ p.hasDenominatorPower
          ((eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 c) =
        (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus p hp).hom.hom.1 z) :=
  (bijective_presentationLimitRationalIso_hom Aplus hAplus p hp).1.eq_iff.symm.trans
    (rationalIso_map_top_apply hAplus p hp c).congr_left

end Top

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] (P : PairOfDefinition A) {Aplus : Subring A}

variable (Aplus) in
/-- **The Laurent cover of `f`**: the rational opens `R({f, 1}/1) = {|f| ≤ 1}` (at `true`) and
`R({1}/f) = {|f| ≥ 1}` (at `false`) of `Spa(A, A⁺)`, indexed by `Bool` so that they form one
family. They cover the adic spectrum (`spa_subset_iUnion_laurentCover`). Since this is an
`abbrev` for `spaBasicOpen`, the `spaBasicOpen` API (such as `mem_spaBasicOpen`) applies to it
directly. -/
noncomputable abbrev laurentCoverOpen (f : A) (b : Bool) : Opens ↥(spa Aplus) :=
  spaBasicOpen Aplus (cond b ({f, 1} : Finset A) ({1} : Finset A)) (cond b 1 f)

omit [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] in
variable (Aplus) in
/-- Each piece of the Laurent cover is a rational open: its numerators contain `1`, so they span
the unit ideal, which is open. -/
theorem laurentCoverOpen_mem_spaRationalOpens (f : A) (b : Bool) :
    laurentCoverOpen Aplus f b ∈ spaRationalOpens Aplus :=
  spaBasicOpen_mem_spaRationalOpens <| isOpen_span_of_one_mem <| by cases b <;> simp

omit [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] in
variable (Aplus) in
/-- **The Laurent cover of `u⁻¹ g` for a unit `u`, first piece**: `{|u⁻¹ g| ≤ 1}` is
`R({g, u}/u) = {|g| ≤ |u|}`. -/
theorem laurentCoverOpen_inv_mul_true [DecidableEq A] (u : Aˣ) (g : A) :
    laurentCoverOpen Aplus (↑u⁻¹ * g) true = spaBasicOpen Aplus {g, ↑u} u := by
  ext v
  have hu : (v : Spv A).valuation u ≠ 0 := (u.isUnit.map (v : Spv A).valuation).ne_zero
  simp [laurentCoverOpen, ← valuation_le_iff, map_units_inv, hu, v.2,
    inv_mul_le_iff₀ (zero_lt_iff.mpr hu)]

omit [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] in
variable (Aplus) in
/-- **The Laurent cover of `u⁻¹ g` for a unit `u`, second piece**: `{|u⁻¹ g| ≥ 1}` is
`R({u}/g) = {|g| ≥ |u|}`. -/
theorem laurentCoverOpen_inv_mul_false (u : Aˣ) (g : A) :
    laurentCoverOpen Aplus (↑u⁻¹ * g) false = spaBasicOpen Aplus {↑u} g := by
  ext v
  have hu : (v : Spv A).valuation u ≠ 0 := (u.isUnit.map (v : Spv A).valuation).ne_zero
  simp [laurentCoverOpen, ← valuation_le_iff, map_units_inv, hu, v.2,
    le_inv_mul_iff₀ (zero_lt_iff.mpr hu)]

/-! ### Transport from the completed rational localisations -/

/-- **Laurent injectivity transported to the presentation-limit presheaf.** Let `A` be a complete
Hausdorff Huber ring, `A⁺` a subring of power-bounded elements and `f ∈ A`. If the map
`a ↦ (a, a)` from `A` into the completed rational localisations of `R({f, 1}/1)` and `R({1}/f)`
is injective, then a section of `presentationLimit` over `Spa(A, A⁺)` is determined by its
restrictions to the two pieces `laurentCoverOpen Aplus f b` of the Laurent cover. The hypothesis
holds for strongly noetherian Tate rings (`laurentCover_injective`) and for uniform Tate rings
(`isClosedEmbedding_laurentCover_of_isUniform`). -/
theorem injective_presentationLimitMap_laurentCoverOpen_of_injective_toCompletionLoc
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
    (hinj : ∀ hden₂ : HasDenominatorPower P ({1} : Finset A) f (Localization.Away f),
      letI hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) (Localization.Away (1 : A))
      letI := locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isTopologicalRing_locUniformSpace P ({1} : Finset A) f _ hden₂
      Function.Injective
        (RingHom.prod (toCompletionLoc P ({f, 1} : Finset A) 1 _ hden₁)
            (toCompletionLoc P ({1} : Finset A) f _ hden₂))) :
    Function.Injective fun (x : presentationLimit (P := P) Aplus ⊤) (b : Bool) ↦
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 x := by
  have := isIso_toPresentationLimit_top (P := P) Aplus hAplus
  let p := laurentPresentation P f
  have hp := isOpen_span_laurentPresentation P f
  -- through `A ≅ presentationLimit ⊤` and `presentationLimitRationalIso`, restriction to the
  -- pieces becomes the pair of structure maps `A → A⟨p b⟩`, injective by `hinj`
  refine .of_comp_right (fun c d hcd ↦ ?_) <|
    Function.RightInverse.surjective (asIso (toPresentationLimit Aplus ⊤)).inv_hom_id_apply
  have key (b : Bool) :=
    ((presentationLimitMap_apply_toPresentationLimit_apply_eq_iff hAplus (p b) (hp b)).1
      (congrFun hcd b)).trans (rationalIso_map_top_apply hAplus (p b) (hp b) d)
  exact injective_eqToHom _ <| hinj (p false).hasDenominatorPower <| Prod.ext (key true) (key false)

/-- **The topology of Laurent restriction transported to the presentation-limit presheaf.**
Let `A` be a complete Hausdorff Huber ring, `A⁺` a subring of power-bounded elements and
`f ∈ A`. If the map `a ↦ (a, a)` from `A` to the two completed Laurent localizations is a
closed embedding, then restriction from `presentationLimit A⁺ ⊤` to the two Laurent pieces is
a closed embedding.

The hypothesis holds for strongly noetherian Tate rings
(`isClosedEmbedding_laurentCover`) and for uniform Tate rings
(`isClosedEmbedding_laurentCover_of_isUniform`). -/
theorem isClosedEmbedding_presentationLimitMap_laurentCoverOpen_of_isClosedEmbedding_toCompletionLoc
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
    (hemb : ∀ hden₂ : HasDenominatorPower P ({1} : Finset A) f (Localization.Away f),
      letI hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) (Localization.Away (1 : A))
      letI := locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isTopologicalRing_locUniformSpace P ({1} : Finset A) f _ hden₂
      IsClosedEmbedding
        (RingHom.prod (toCompletionLoc P ({f, 1} : Finset A) 1 _ hden₁)
          (toCompletionLoc P ({1} : Finset A) f _ hden₂))) :
    IsClosedEmbedding fun x : presentationLimit (P := P) Aplus ⊤ ↦
      ((presentationLimitMap (P := P)
          (le_top : laurentCoverOpen Aplus f true ≤ ⊤)).hom.1 x,
        (presentationLimitMap (P := P)
          (le_top : laurentCoverOpen Aplus f false ≤ ⊤)).hom.1 x) := by
  let p := laurentPresentation P f
  have hp := isOpen_span_laurentPresentation P f
  -- Identify global sections with `A` and the sections on each Laurent piece with its completed
  -- coordinate ring.  These homeomorphisms are the source and target changes of coordinates.
  let F := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ _root_.TopCommRingCat TopCat
  let d : presentationLimit (P := P) Aplus ⊤ ≃ₜ A :=
    (TopCat.homeoOfIso (F.mapIso (presentationLimitTopIso (P := P) Aplus hAplus))).trans
      (TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso
        (eqToIso (CompleteSeparatedTopCommRingCat.of_obj A))))
  let E (b : Bool) := (TopCat.homeoOfIso (F.mapIso
      (presentationLimitRationalIso Aplus hAplus (p b) (hp b)))).trans
    (TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso
      (eqToIso (completionLocObj_obj P (p b).num (p b).den _ (p b).hasDenominatorPower))))
  -- After these changes of coordinates, the desired restriction map is the ring-level map in
  -- `hemb`; it remains to verify that the resulting square commutes.
  -- The `cast` below only changes the function underlying the embedding.  The two functions agree
  -- by `rfl` after unfolding `Function.comp`, `Homeomorph.prodCongr`, `Homeomorph.trans`,
  -- `TopCat.homeoOfIso` applied to `Functor.mapIso`, and `RingHom.prod_apply`; `E b z` is
  -- definitionally `(eqToHom _).1 ((presentationLimitRationalIso ..).hom.hom.1 z)`.
  refine ((E true).prodCongr (E false)).isClosedEmbedding.of_comp_iff.mp
    (cast (congrArg IsClosedEmbedding (funext fun x ↦ ?_))
      ((hemb (p false).hasDenominatorPower).comp d.isClosedEmbedding))
  -- Check commutativity pointwise after writing a global section as the image of some `c : A`.
  symm
  have := isIso_toPresentationLimit_top (P := P) Aplus hAplus
  obtain ⟨c, rfl⟩ : ∃ c, (toPresentationLimit (P := P) Aplus ⊤).hom.1 c = x :=
    Function.RightInverse.surjective
      (asIso (toPresentationLimit (P := P) Aplus ⊤)).inv_hom_id_apply x
  -- The source comparison cancels on `c`; the target comparisons are `rationalIso_map_top_apply`.
  -- `d` unfolds definitionally to the composite `(eqToHom _).1 ∘ (presentationLimitTopIso ..).hom`,
  -- so `hd` is `congrArg (eqToHom _).1` of the identity `inv_hom_id_apply` for
  -- `toPresentationLimit`.
  have hd : d ((toPresentationLimit (P := P) Aplus ⊤).hom.1 c) =
      (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 c := by
    have h := (presentationLimitTopIso (P := P) Aplus hAplus).inv_hom_id_apply c
    rw [presentationLimitTopIso_inv] at h
    exact congrArg (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 h
  exact Prod.ext
    ((rationalIso_map_top_apply hAplus (p true) (hp true) c).trans (congrArg _ hd.symm))
    ((rationalIso_map_top_apply hAplus (p false) (hp false) c).trans (congrArg _ hd.symm))

-- Sections over the two Laurent pieces that agree on their overlap are, read through
-- `presentationLimitRationalIso`, the images of one `c : A` under the structure maps `A → A⟨p b⟩`,
-- as soon as the ring-level two-piece sequence `hexact` is exact in the middle.
private theorem exists_toCompletionLoc_eq_of_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
    (hexact : ∀ hden₂ : HasDenominatorPower P ({1} : Finset A) f (Localization.Away f),
      letI hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) (Localization.Away (1 : A))
      letI hden₁₂ := hasDenominatorPower_mul P ({f, 1} : Finset A) ({1} : Finset A)
        ({f * f, f, 1} : Finset A) 1 f
        (Localization.Away (1 : A)) (Localization.Away f) (Localization.Away (1 * f))
        (by simp) (by simp) hden₁ hden₂
      letI := locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isTopologicalRing_locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) _ hden₁₂
      letI := isUniformAddGroup_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) _ hden₁₂
      letI := isTopologicalRing_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) _ hden₁₂
      Function.Exact
        (RingHom.prod (toCompletionLoc P ({f, 1} : Finset A) 1 _ hden₁)
            (toCompletionLoc P ({1} : Finset A) f _ hden₂))
        ((restrictionRingHom P ({f, 1} : Finset A) 1 _ hden₁ ({f * f, f, 1} : Finset A) (1 * f) _
            hden₁₂ f rfl
            (by simp)).toAddMonoidHom.comp
            (AddMonoidHom.fst (UniformSpace.Completion (Localization.Away (1 : A)))
              (UniformSpace.Completion (Localization.Away f))) -
          (restrictionRingHom P ({1} : Finset A) f _ hden₂ ({f * f, f, 1} : Finset A) (1 * f) _
            hden₁₂ 1 (mul_comm 1 f)
            (by simp)).toAddMonoidHom.comp
            (AddMonoidHom.snd (UniformSpace.Completion (Localization.Away (1 : A)))
              (UniformSpace.Completion (Localization.Away f)))))
    (x : ∀ b, presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f b))
    (hx : (presentationLimitMap (P := P) (inf_le_left : laurentCoverOpen Aplus f true ⊓
        laurentCoverOpen Aplus f false ≤ _)).hom.1 (x true) =
      (presentationLimitMap (P := P) (inf_le_right : laurentCoverOpen Aplus f true ⊓
        laurentCoverOpen Aplus f false ≤ _)).hom.1 (x false)) :
    ∃ c : CompleteSeparatedTopCommRingCat.of A, ∀ b, letI p := laurentPresentation P f b
      toCompletionLoc P p.num p.den _ p.hasDenominatorPower
          ((eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 c) =
        (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus p
            (isOpen_span_laurentPresentation P f b)).hom.hom.1 (x b)) := by
  let p := laurentPresentation P f
  let q := laurentOverlapPresentation P f
  have hp := isOpen_span_laurentPresentation P f
  have hq : IsOpen (Ideal.span (q.num : Set A) : Set A) := isOpen_span_of_one_mem <| by simp [q]
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have hT₁ : ∀ t ∈ (p true).num, t * f ∈ q.num := by grind
  have hT₂ : ∀ t ∈ (p false).num, t * 1 ∈ q.num := by grind
  have hU (b : Bool) : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus (p b).num (p b).den :=
    spaBasicOpen_le_spaBasicOpen_iff.mpr <| rationalSubset_subset_rationalSubset_of_le Aplus <|
      Presentation.le_def.mpr <| b.rec ⟨1, mul_comm 1 f, hT₂⟩ ⟨f, rfl, hT₁⟩
  -- restricted further to `R(q)` and read through `presentationLimitRationalIso`, `hx` says that
  -- the pair of sections is in the kernel of the difference of 8.33's restriction maps
  have h := congrArg (fun z ↦
    (eqToHom (completionLocObj_obj P q.num q.den _ q.hasDenominatorPower)).1
      ((presentationLimitRationalIso Aplus hAplus q hq).hom.hom.1
        ((presentationLimitMap (le_inf (hU true) (hU false))).hom.1 z))) hx
  simp only [presentationLimitMap_apply_presentationLimitMap_apply,
    rationalIso_map_apply hAplus (p true) q (hp true) hq f rfl hT₁,
    rationalIso_map_apply hAplus (p false) q (hp false) hq 1 (mul_comm 1 f) hT₂] at h
  obtain ⟨c, hc⟩ := (hexact (p false).hasDenominatorPower (_, _)).1 (sub_eq_zero.2 h)
  refine ⟨(eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm).1 c, fun b ↦ ?_⟩
  rw [eqToHom_symm_apply_eqToHom_apply]
  exact b.rec (congrArg Prod.snd hc) (congrArg Prod.fst hc)

/-- **Laurent gluing transported to the presentation-limit presheaf.** Let `A` be a complete
Hausdorff Huber ring, `A⁺` a subring of power-bounded elements and `f ∈ A`. If the ring-level
sequence `A → A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩` of the Laurent cover of `f` is exact in the middle,
then sections `x b` of `presentationLimit` over the two pieces `laurentCoverOpen Aplus f b` that
agree on their overlap are the restrictions of one section over `Spa(A, A⁺)`. The hypothesis
holds for strongly noetherian Tate rings (`laurentCover_exact`) and for uniform Tate rings
(`laurentCover_exact_of_isUniform`). -/
theorem exists_presentationLimitMap_eq_of_laurentCoverOpen_of_exact_toCompletionLoc
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
    (hexact : ∀ hden₂ : HasDenominatorPower P ({1} : Finset A) f (Localization.Away f),
      letI hden₁ := hasDenominatorPower_denom_one P ({f, 1} : Finset A) (Localization.Away (1 : A))
      letI hden₁₂ := hasDenominatorPower_mul P ({f, 1} : Finset A) ({1} : Finset A)
        ({f * f, f, 1} : Finset A) 1 f
        (Localization.Away (1 : A)) (Localization.Away f) (Localization.Away (1 * f))
        (by simp) (by simp) hden₁ hden₂
      letI := locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isUniformAddGroup_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := isTopologicalRing_locUniformSpace P ({f, 1} : Finset A) 1 _ hden₁
      letI := locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isUniformAddGroup_locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := isTopologicalRing_locUniformSpace P ({1} : Finset A) f _ hden₂
      letI := locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) _ hden₁₂
      letI := isUniformAddGroup_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) _ hden₁₂
      letI := isTopologicalRing_locUniformSpace P ({f * f, f, 1} : Finset A) (1 * f) _ hden₁₂
      Function.Exact
        (RingHom.prod (toCompletionLoc P ({f, 1} : Finset A) 1 _ hden₁)
            (toCompletionLoc P ({1} : Finset A) f _ hden₂))
        ((restrictionRingHom P ({f, 1} : Finset A) 1 _ hden₁ ({f * f, f, 1} : Finset A) (1 * f) _
            hden₁₂ f rfl
            (by simp)).toAddMonoidHom.comp
            (AddMonoidHom.fst (UniformSpace.Completion (Localization.Away (1 : A)))
              (UniformSpace.Completion (Localization.Away f))) -
          (restrictionRingHom P ({1} : Finset A) f _ hden₂ ({f * f, f, 1} : Finset A) (1 * f) _
            hden₁₂ 1 (mul_comm 1 f)
            (by simp)).toAddMonoidHom.comp
            (AddMonoidHom.snd (UniformSpace.Completion (Localization.Away (1 : A)))
              (UniformSpace.Completion (Localization.Away f)))))
    (x : ∀ b, presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f b))
    (hx : (presentationLimitMap (P := P) (inf_le_left :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1 (x true) =
      (presentationLimitMap (P := P) (inf_le_right :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1
          (x false)) :
    ∃ a : presentationLimit (P := P) Aplus ⊤, ∀ b,
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 a =
        x b := by
  -- `hexact` gives `c : A` with the right structure maps; its image in `presentationLimit ⊤`
  -- restricts to `x b`, since both agree after `presentationLimitRationalIso`
  obtain ⟨c, hc⟩ := exists_toCompletionLoc_eq_of_laurentCoverOpen P hAplus f hexact x hx
  exact ⟨(toPresentationLimit Aplus ⊤).hom.1 c, fun b ↦
    (presentationLimitMap_apply_toPresentationLimit_apply_eq_iff hAplus _
      (isOpen_span_laurentPresentation P f b)).2 (hc b)⟩

/-! ### Strongly noetherian Tate rings -/

variable [IsTateRing A] [IsStronglyNoetherian A]

/-- **Wedhorn's Lemma 8.33, injectivity, for the presentation-limit presheaf.** Let `A` be a
complete Hausdorff strongly noetherian Tate ring, `A⁺` a subring of power-bounded elements and
`f ∈ A`. A section of `presentationLimit` over `Spa(A, A⁺)` is determined by its restrictions to
the two pieces `laurentCoverOpen Aplus f b` of the Laurent cover. The corresponding statement for
the map `a ↦ (a, a)` from `A` into the completed rational localisations of the two pieces is
`laurentCover_injective`. Sections over the pieces that agree on their overlap do come from a
section over `Spa(A, A⁺)`: `exists_presentationLimitMap_eq_of_laurentCoverOpen`. -/
theorem injective_presentationLimitMap_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A) :
    Function.Injective fun (x : presentationLimit (P := P) Aplus ⊤) (b : Bool) ↦
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 x :=
  injective_presentationLimitMap_laurentCoverOpen_of_injective_toCompletionLoc P hAplus f <|
    laurentCover_injective P f _ _

/-- **Wedhorn's Lemma 8.33, exactness in the middle, for the presentation-limit presheaf.** Let `A`
be a complete Hausdorff strongly noetherian Tate ring, `A⁺` a subring of power-bounded elements and
`f ∈ A`. Sections `x b` of `presentationLimit` over the two pieces `laurentCoverOpen Aplus f b` of
the Laurent cover that agree on their overlap are the restrictions of one section over
`Spa(A, A⁺)`, which is unique by `injective_presentationLimitMap_laurentCoverOpen`. The
corresponding statement for `A` and the completed rational localisations of the two pieces and of
their overlap is `laurentCover_exact`. -/
theorem exists_presentationLimitMap_eq_of_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
    (x : ∀ b, presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f b))
    (hx : (presentationLimitMap (P := P) (inf_le_left :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1 (x true) =
      (presentationLimitMap (P := P) (inf_le_right :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1
          (x false)) :
    ∃ a : presentationLimit (P := P) Aplus ⊤, ∀ b,
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 a =
        x b :=
  exists_presentationLimitMap_eq_of_laurentCoverOpen_of_exact_toCompletionLoc P hAplus f
    (fun hden₂ ↦ laurentCover_exact P f _ _ _ hden₂) x hx

open scoped Pointwise in
/-- **Wedhorn's Lemma 8.33, degree-one surjectivity, for the presentation-limit presheaf.**
Every section on the intersection of the two Laurent pieces is a difference of restrictions of
sections on the pieces. Together with the degree-zero results above, this gives exactness of the
augmented two-piece Čech complex. -/
theorem surjective_presentationLimitMap_sub_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A) :
    Function.Surjective fun (x :
        presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f true) ×
          presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f false)) ↦
      (presentationLimitMap (P := P) (inf_le_left :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1 x.1 -
      (presentationLimitMap (P := P) (inf_le_right :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1 x.2 := by
  classical
  let p := laurentPresentation P f
  let q := laurentOverlapPresentation P f
  have hp := isOpen_span_laurentPresentation P f
  have hq : IsOpen (Ideal.span (q.num : Set A) : Set A) :=
    isOpen_span_of_one_mem (by simp [q])
  have hT₁ : ∀ t ∈ (p true).num, t * f ∈ q.num := by grind
  have hT₂ : ∀ t ∈ (p false).num, t * 1 ∈ q.num := by grind
  -- The ring-level overlap presentation represents the intersection of the two Laurent opens.
  have hnum : ({f, 1} : Finset A) * ({f, 1} : Finset A) = ({f * f, f, 1} : Finset A) := by
    ext
    simp [Finset.mem_mul, eq_comm]
    tauto
  have hEq : spaBasicOpen Aplus q.num q.den =
      laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false := by
    ext x
    simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_spaBasicOpen]
    rw [← Set.mem_inter_iff, rationalSubset_inter]
    simp [q, hnum]
  have hInv : Function.LeftInverse (presentationLimitMap (P := P) hEq.ge).hom.1
      (presentationLimitMap (P := P) hEq.le).hom.1 := fun z ↦ by
    rw [presentationLimitMap_apply_presentationLimitMap_apply, presentationLimitMap_refl]
    exact ConcreteCategory.id_apply z
  -- Transport `laurentCover_surjective` through the rational-section isomorphisms.
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := laurentCover_surjective P f (Localization.Away (1 : A))
    (Localization.Away f) (Localization.Away (1 * f)) (p false).hasDenominatorPower
    ((eqToHom (completionLocObj_obj P q.num q.den _ q.hasDenominatorPower)).1
      ((presentationLimitRationalIso Aplus hAplus q hq).hom.hom.1
        ((presentationLimitMap hEq.le).hom.1 z)))
  obtain ⟨x₁, rfl⟩ :=
    (bijective_presentationLimitRationalIso_hom Aplus hAplus (p true) (hp true)).2 u
  obtain ⟨x₂, rfl⟩ :=
    (bijective_presentationLimitRationalIso_hom Aplus hAplus (p false) (hp false)).2 v
  refine ⟨(x₁, x₂),
    (bijective_presentationLimitRationalIso_hom Aplus hAplus q hq).1.comp hInv.injective ?_⟩
  simp only [Function.comp_apply, map_sub, presentationLimitMap_apply_presentationLimitMap_apply,
    rationalIso_map_apply hAplus (p true) q (hp true) hq f rfl hT₁,
    rationalIso_map_apply hAplus (p false) q (hp false) hq 1 (mul_comm 1 f) hT₂]
  -- `huv` is the same statement up to definitional unfolding: the pointwise difference
  -- `restrictionRingHom .. u - restrictionRingHom .. v` is `AddMonoidHom.sub_apply` of the
  -- compositions with `AddMonoidHom.fst`/`snd` of `RingHom.toAddMonoidHom`, and the localisations
  -- `Localization.Away (1 * f)` and `{f * f, f, 1}` agree with `q.den`/`q.num` by `rfl`.
  exact huv

end TauCeti.ValuationSpectrum
