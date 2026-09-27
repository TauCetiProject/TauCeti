/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections

/-!
# The Laurent cover for the presentation-limit presheaf

For `f ∈ A` the rational opens `R({f, 1}/1) = {|f| ≤ 1}` and `R({1}/f) = {|f| ≥ 1}` cover
`X = Spa(A, A⁺)`. When `A` is a complete Hausdorff strongly noetherian Tate ring and `A⁺` consists
of power-bounded elements, the presentation-limit presheaf satisfies the sheaf condition for this
cover: a section over `X` is determined by its restrictions to the two pieces, and sections over the
pieces that agree on their overlap are the restrictions of a section over `X`. This is the
degree-zero part of Wedhorn's Lemma 8.33, and of the acyclicity of this cover in his
Lemma 8.34(i), stated for `presentationLimit`.

## Main definitions

* `TauCeti.ValuationSpectrum.laurentCoverOpen` : the two pieces `R({f, 1}/1)` and `R({1}/f)` of
  the Laurent cover, indexed by `Bool`.

## Main results

* `TauCeti.ValuationSpectrum.injective_presentationLimitMap_laurentCoverOpen` : restriction from
  `X` to the two pieces is injective.
* `TauCeti.ValuationSpectrum.exists_presentationLimitMap_eq_of_laurentCoverOpen` : sections over
  the two pieces that agree on their overlap come from a section over `X`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.33 and Lemma 8.34(i).
-/

@[expose] public section

open CategoryTheory TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

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
  num := cond b {f, 1} {1}
  den := cond b 1 f
  hasDenominatorPower := hasDenominatorPower_of_isOpen_span P _ _ _ <|
    isOpen_span_of_one_mem <| by cases b <;> simp

-- The presentation `({f², f, 1}, 1 · f)` of the overlap of the two Laurent pieces, spelled
-- `({f * f, f, 1}, 1 * f)` as in `laurentCover_exact` so that the two agree definitionally.
variable (P) in
private noncomputable abbrev laurentOverlapPresentation (f : A) : Presentation P where
  num := {f * f, f, 1}
  den := 1 * f
  hasDenominatorPower := hasDenominatorPower_of_isOpen_span P _ _ _ <|
    isOpen_span_of_one_mem <| by simp

-- The numerator ideals of the Laurent pieces are open.
variable (P) in
private theorem isOpen_span_laurentPresentation (f : A) (b : Bool) :
    IsOpen (Ideal.span ((laurentPresentation P f b).num : Set A) : Set A) :=
  isOpen_span_of_one_mem <| by cases b <;> simp

-- Restrictions of the presentation limit compose, elementwise: `presentationLimitMap_comp`
-- restated with `.hom.1`, so that `simp` matches the `.hom.1` terms here.
private theorem presentationLimitMap_apply_presentationLimitMap_apply {U V W : Opens ↥(spa Aplus)}
    (h₁ : W ≤ V) (h₂ : U ≤ W) (z : presentationLimit (P := P) Aplus V) :
    (presentationLimitMap h₂).hom.1 ((presentationLimitMap h₁).hom.1 z) =
      (presentationLimitMap (h₂.trans h₁)).hom.1 z :=
  ConcreteCategory.congr_hom (presentationLimitMap_comp h₁ h₂) z

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
  ((injective_eqToHom _).comp <| Function.LeftInverse.injective
    (presentationLimitRationalIso Aplus hAplus p hp).hom_inv_id_apply).eq_iff.symm.trans
      (rationalIso_map_top_apply hAplus p hp c).congr_left

end Top

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A]
  (P : PairOfDefinition A) {Aplus : Subring A}

variable (Aplus) in
/-- **The Laurent cover of `f`**: the rational opens `R({f, 1}/1) = {|f| ≤ 1}` (at `true`) and
`R({1}/f) = {|f| ≥ 1}` (at `false`) of `Spa(A, A⁺)`, indexed by `Bool` so that they form one
family. They cover the adic spectrum (`spa_subset_iUnion_laurentCover`). Since this is an
`abbrev` for `spaBasicOpen`, the `spaBasicOpen` API (such as `mem_spaBasicOpen`) applies to it
directly. -/
noncomputable abbrev laurentCoverOpen (f : A) (b : Bool) : Opens ↥(spa Aplus) :=
  spaBasicOpen Aplus (cond b {f, 1} {1}) (cond b 1 f)

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
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 x := by
  have := isIso_toPresentationLimit_top (P := P) Aplus hAplus
  let p := laurentPresentation P f
  have hp := isOpen_span_laurentPresentation P f
  -- through `A ≅ presentationLimit ⊤` and `presentationLimitRationalIso`, restriction to the
  -- pieces becomes the pair of structure maps `A → A⟨p b⟩`, injective by `laurentCover_injective`
  refine .of_comp_right (fun c d hcd ↦ ?_) <|
    Function.RightInverse.surjective (asIso (toPresentationLimit Aplus ⊤)).inv_hom_id_apply
  have key (b : Bool) :=
    ((presentationLimitMap_apply_toPresentationLimit_apply_eq_iff hAplus (p b) (hp b)).1
      (congrFun hcd b)).trans (rationalIso_map_top_apply hAplus (p b) (hp b) d)
  exact injective_eqToHom _ <| laurentCover_injective P f (Localization.Away (1 : A))
    (Localization.Away f) _ <| Prod.ext (key true) (key false)

-- Sections over the two Laurent pieces that agree on their overlap are, read through
-- `presentationLimitRationalIso`, the images of one `c : A` under the structure maps `A → A⟨p b⟩`.
private theorem exists_toCompletionLoc_eq_of_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
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
  obtain ⟨c, hc⟩ := (laurentCover_exact P f (Localization.Away (1 : A)) (Localization.Away f)
    (Localization.Away (1 * f)) (p false).hasDenominatorPower (_, _)).1 (sub_eq_zero.2 h)
  refine ⟨(eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm).1 c, fun b ↦ ?_⟩
  rw [eqToHom_symm_apply_eqToHom_apply]
  exact b.rec (congrArg Prod.snd hc) (congrArg Prod.fst hc)

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
        x b := by
  -- `laurentCover_exact` gives `c : A` with the right structure maps; its image in
  -- `presentationLimit ⊤` restricts to `x b`, since both agree after `presentationLimitRationalIso`
  obtain ⟨c, hc⟩ := exists_toCompletionLoc_eq_of_laurentCoverOpen P hAplus f x hx
  exact ⟨(toPresentationLimit Aplus ⊤).hom.1 c, fun b ↦
    (presentationLimitMap_apply_toPresentationLimit_apply_eq_iff hAplus _
      (isOpen_span_laurentPresentation P f b)).2 (hc b)⟩

end TauCeti.ValuationSpectrum
