/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.AlgebraicGeometry.AdicSpace.CAff.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PresentationIndependence
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.OpenEmbedding
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison

/-!
# Rational localizations of complete Huber pairs

This file characterizes rational localizations `φ : X ⟶ Y` in `TauCeti.CAff.{u}` via their
universal property (`IsRationalLocalization`) and constructs the canonical completed rational
localizations `X.rationalLocalization T s hT = (A⟨T/s⟩, A_U⁺)` together with their restriction,
composition, and base-change pullback APIs.

## Main definitions

* `TauCeti.CAff.IsRationalLocalization`: the intrinsic universal property characterizing a morphism
  `φ : X ⟶ Y` in `CAff` as a completed rational localization of `X` at `(T, s)`.
* `TauCeti.CAff.rationalLocalization` and `TauCeti.CAff.rationalLocalizationHom`: the canonical
  completed rational localization `(A⟨T/s⟩, A_U⁺)` in `CAff` for an open span `(T)`.
* `TauCeti.CAff.rationalLocalizationRingEquiv`: identifies `(X.rationalLocalization T s hT).ring`
  with the completed localization `A⟨T/s⟩`.
* `TauCeti.CAff.rationalLocalizationRestrict`: the canonical restriction morphism between
  canonical rational localizations along a containment `R(T'/s') ⊆ R(T/s)`.
* `TauCeti.CAff.IsRationalLocalization.baseChange` and
  `TauCeti.CAff.rationalLocalizationBaseChange`: the comparison morphism induced by base change
  along a morphism whose mapped numerator ideal is open.

## Main results

* `TauCeti.CAff.IsRationalLocalization.lift`, `TauCeti.CAff.IsRationalLocalization.hom_ext`,
  `TauCeti.CAff.IsRationalLocalization.epi`, `TauCeti.CAff.IsRationalLocalization.restrict`,
  `TauCeti.CAff.IsRationalLocalization.iso`, and `TauCeti.CAff.IsRationalLocalization.isPullback`:
  universal factorization, epimorphism property, restriction maps, canonical isomorphism, and
  intersection pullbacks for arbitrary rational localizations.
* `TauCeti.CAff.isRationalLocalization_rationalLocalizationHom`: the canonical morphism
  `X ⟶ X.rationalLocalization T s hT` satisfies `IsRationalLocalization` (Wedhorn Lemma 8.1
  upgraded to Huber pairs via `comap_mem_spa_completedPlusSubring`).
* `TauCeti.CAff.IsRationalLocalization.isOpenEmbedding_spaComap` and
  `TauCeti.CAff.IsRationalLocalization.range_spaComap`: any rational localization induces an open
  embedding on `Spa` with range `R(T/s)`.
* `TauCeti.CAff.IsRationalLocalization.comp_of_spaComap_image` and
  `TauCeti.CAff.IsRationalLocalization.exists_comp`: composition of two rational localizations is a
  rational localization for the rational image of the second locus in the original spectrum.
* `TauCeti.CAff.IsRationalLocalization.isPullback_baseChange` and
  `TauCeti.CAff.isPullback_rationalLocalizationBaseChange`: base change along a map with open mapped
  numerator ideal forms a pullback square in `CAffᵒᵖ`.
* `TauCeti.CAff.isPullback_rationalLocalizationRestrict`: the canonical localization of an
  intersection of two rational subsets is a pullback in `CAffᵒᵖ`.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §2–3.
* P. Scholze and J. Weinstein, *Berkeley Lectures on `p`-adic Geometry*, Annals of Mathematics
  Studies 207, Princeton University Press (2020), Lectures 2–4.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.3, §8.1–8.2 (Lemma 8.1,
  Proposition 8.2, Remark 8.4).
-/

public section

open CategoryTheory Opposite TopologicalSpace Topology UniformSpace
open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.ValuationSpectrum

universe u

namespace TauCeti.CAff

/-- A morphism `φ : X ⟶ Y` in `CAff` is a *rational localization* of `X` for `(T, s)` if `T` spans
an open ideal in `X.ring`, `φ.spaComap` maps `Spa(Y)` into `R(T/s)`, and `φ` is initial among
morphisms `ψ : X ⟶ Z` in `CAff` whose pullback on `Spa` lands in `R(T/s)`. -/
structure IsRationalLocalization {X Y : CAff.{u}} (φ : X ⟶ Y)
    (T : Finset X.ring) (s : X.ring) : Prop where
  /-- The numerator set `T` generates an open ideal in `X.ring`. -/
  isOpen_span : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)
  /-- Every point of `Spa(Y)` pulls back along `φ` into `R(T/s)`. -/
  mapsTo_spaComap : ∀ w : ValuationSpectrum.spa Y.pair.plus,
    (φ.spaComap w).val ∈ rationalSubset X.pair.plus T s
  /-- Any morphism `ψ : X ⟶ Z` mapping `Spa(Z)` into `R(T/s)` factors uniquely through `φ`. -/
  existsUnique_factorization : ∀ ⦃Z : CAff.{u}⦄ (ψ : X ⟶ Z),
    (∀ w : ValuationSpectrum.spa Z.pair.plus,
      (ψ.spaComap w).val ∈ rationalSubset X.pair.plus T s) →
    ∃! χ : Y ⟶ Z, φ ≫ χ = ψ

namespace IsRationalLocalization

/-- The universal factorization morphism `Y ⟶ Z` out of a rational localization `φ : X ⟶ Y`
for any `ψ : X ⟶ Z` whose pullback on `Spa` lands in `R(T/s)`. -/
noncomputable def lift {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) {Z : CAff.{u}} (ψ : X ⟶ Z)
    (hψ : ∀ w : ValuationSpectrum.spa Z.pair.plus,
      (ψ.spaComap w).val ∈ rationalSubset X.pair.plus T s) :
    Y ⟶ Z :=
  (hφ.existsUnique_factorization ψ hψ).choose

/-- Factoring `ψ` through a rational localization `φ` recovers `ψ`. -/
@[reassoc (attr := simp)]
theorem fac {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) {Z : CAff.{u}} (ψ : X ⟶ Z)
    (hψ : ∀ w : ValuationSpectrum.spa Z.pair.plus,
      (ψ.spaComap w).val ∈ rationalSubset X.pair.plus T s) :
    φ ≫ hφ.lift ψ hψ = ψ :=
  (hφ.existsUnique_factorization ψ hψ).choose_spec.1

/-- Uniqueness of the factorization morphism `IsRationalLocalization.lift`. -/
theorem lift_unique {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) {Z : CAff.{u}} (ψ : X ⟶ Z)
    (hψ : ∀ w : ValuationSpectrum.spa Z.pair.plus,
      (ψ.spaComap w).val ∈ rationalSubset X.pair.plus T s)
    {χ : Y ⟶ Z} (hχ : φ ≫ χ = ψ) :
    χ = hφ.lift ψ hψ :=
  (hφ.existsUnique_factorization ψ hψ).choose_spec.2 χ hχ

/-- A rational localization is an epimorphism in `CAff`: two morphisms out of `Y` that agree after
precomposition with `φ` are equal. -/
theorem hom_ext {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) {Z : CAff.{u}} {χ₁ χ₂ : Y ⟶ Z}
    (h : φ ≫ χ₁ = φ ≫ χ₂) :
    χ₁ = χ₂ :=
  (hφ.existsUnique_factorization (φ ≫ χ₁) fun w ↦ by
    rw [comp_spaComap]; exact hφ.mapsTo_spaComap _).unique rfl h.symm

/-- Every rational localization in `CAff` is an epimorphism (equivalently, a monomorphism in
`CAffᵒᵖ`). -/
theorem epi {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) : Epi φ :=
  ⟨fun _ _ h ↦ hφ.hom_ext h⟩

/-- A rational localization with denominator `0` has a trivial target ring. -/
theorem subsingleton_ring {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring}
    (hφ : IsRationalLocalization φ T 0) : Subsingleton Y.ring :=
  (isEmpty_spa_iff Y).mp ⟨fun w ↦
    ((mem_rationalSubset_iff X.pair.plus T 0 _).mp (hφ.mapsTo_spaComap w)).2.2
      ((φ.spaComap w).val.toValuativeRel.vle_refl 0)⟩

/-- Postcomposing a rational localization with an isomorphism in `CAff` yields a rational
localization for the same `(T, s)`. -/
theorem comp_iso {X Y₁ Y₂ : CAff.{u}} {φ : X ⟶ Y₁} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) (e : Y₁ ≅ Y₂) :
    IsRationalLocalization (φ ≫ e.hom) T s where
  isOpen_span := hφ.isOpen_span
  mapsTo_spaComap w := by
    rw [comp_spaComap]
    exact hφ.mapsTo_spaComap (e.hom.spaComap w)
  existsUnique_factorization {Z} ψ hψ :=
    ⟨e.inv ≫ hφ.lift ψ hψ, by dsimp; rw [Category.assoc, e.hom_inv_id_assoc, hφ.fac],
      fun χ' hχ' ↦ by
        rw [← e.inv_hom_id_assoc χ',
          hφ.lift_unique ψ hψ (χ := e.hom ≫ χ') (by simpa [Category.assoc] using hχ')]⟩

/-- The canonical restriction morphism between two rational localizations of `X` along a containment
`R(T₂/s₂) ⊆ R(T₁/s₁)` of rational subsets. -/
noncomputable def restrict {X Y₁ Y₂ : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (hsub : rationalSubset X.pair.plus T₂ s₂ ⊆ rationalSubset X.pair.plus T₁ s₁) :
    Y₁ ⟶ Y₂ :=
  h₁.lift φ₂ fun w ↦ hsub (h₂.mapsTo_spaComap w)

/-- Precomposing `IsRationalLocalization.restrict` with `φ₁` recovers `φ₂`. -/
@[reassoc (attr := simp)]
theorem comp_restrict {X Y₁ Y₂ : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (hsub : rationalSubset X.pair.plus T₂ s₂ ⊆ rationalSubset X.pair.plus T₁ s₁) :
    φ₁ ≫ h₁.restrict h₂ hsub = φ₂ :=
  h₁.fac _ _

/-- Restricting a rational localization to itself is the identity morphism. -/
@[simp]
theorem restrict_self {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) :
    hφ.restrict hφ subset_rfl = 𝟙 Y :=
  hφ.hom_ext (by simp)

/-- Restriction morphisms between rational localizations compose functorially. -/
@[reassoc (attr := simp)]
theorem restrict_comp {X Y₁ Y₂ Y₃ : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂} {φ₃ : X ⟶ Y₃}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    {T₃ : Finset X.ring} {s₃ : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (h₃ : IsRationalLocalization φ₃ T₃ s₃)
    (h₁₂ : rationalSubset X.pair.plus T₂ s₂ ⊆ rationalSubset X.pair.plus T₁ s₁)
    (h₂₃ : rationalSubset X.pair.plus T₃ s₃ ⊆ rationalSubset X.pair.plus T₂ s₂) :
    h₁.restrict h₂ h₁₂ ≫ h₂.restrict h₃ h₂₃ = h₁.restrict h₃ (h₂₃.trans h₁₂) :=
  h₁.hom_ext (by simp)

/-- Any two rational localizations of `X` cutting out the same rational subset are canonically
isomorphic. -/
noncomputable def iso {X Y₁ Y₂ : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (heq : rationalSubset X.pair.plus T₁ s₁ = rationalSubset X.pair.plus T₂ s₂ := by rfl) :
    Y₁ ≅ Y₂ where
  hom := h₁.restrict h₂ heq.symm.le
  inv := h₂.restrict h₁ heq.le
  hom_inv_id := by rw [restrict_comp, restrict_self]
  inv_hom_id := by rw [restrict_comp, restrict_self]

@[reassoc (attr := simp)]
theorem comp_iso_hom {X Y₁ Y₂ : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (heq : rationalSubset X.pair.plus T₁ s₁ = rationalSubset X.pair.plus T₂ s₂ := by rfl) :
    φ₁ ≫ (h₁.iso h₂ heq).hom = φ₂ :=
  h₁.comp_restrict h₂ heq.symm.le

@[reassoc (attr := simp)]
theorem comp_iso_inv {X Y₁ Y₂ : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (heq : rationalSubset X.pair.plus T₁ s₁ = rationalSubset X.pair.plus T₂ s₂ := by rfl) :
    φ₂ ≫ (h₁.iso h₂ heq).inv = φ₁ :=
  h₂.comp_restrict h₁ heq.le

/-- Any rational localization of an intersection `R(T'/s') = R(T₁/s₁) ∩ R(T₂/s₂)` of two rational
subsets is a pullback in `CAffᵒᵖ`. -/
theorem isPullback {X Y₁ Y₂ Y' : CAff.{u}} {φ₁ : X ⟶ Y₁} {φ₂ : X ⟶ Y₂} {φ' : X ⟶ Y'}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset X.ring} {s₂ : X.ring}
    {T' : Finset X.ring} {s' : X.ring}
    (h₁ : IsRationalLocalization φ₁ T₁ s₁) (h₂ : IsRationalLocalization φ₂ T₂ s₂)
    (h' : IsRationalLocalization φ' T' s')
    (hinter : rationalSubset X.pair.plus T' s' =
      rationalSubset X.pair.plus T₁ s₁ ∩ rationalSubset X.pair.plus T₂ s₂) :
    IsPullback
      (h₁.restrict h' (hinter.le.trans Set.inter_subset_left)).op
      (h₂.restrict h' (hinter.le.trans Set.inter_subset_right)).op
      φ₁.op φ₂.op := by
  have hsub₁ : rationalSubset X.pair.plus T' s' ⊆ rationalSubset X.pair.plus T₁ s₁ :=
    hinter.le.trans Set.inter_subset_left
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← op_comp, ← op_comp, comp_restrict, comp_restrict]
  · rintro ⟨Z⟩ ⟨g₁⟩ ⟨g₂⟩ hg _
    have hg' : h₁.restrict h' hsub₁ ≫ g₁ = h₁.restrict h' hsub₁ ≫ g₂ :=
      Quiver.Hom.op_inj (by rw [op_comp, op_comp]; exact hg)
    have hcomp : φ' ≫ g₁ = φ' ≫ g₂ := by
      rw [← h₁.comp_restrict h' hsub₁, Category.assoc, Category.assoc, hg']
    exact Quiver.Hom.unop_inj (h'.hom_ext hcomp.symm).symm
  · rintro ⟨Z⟩ ⟨a⟩ ⟨b⟩ hab
    have hab' : φ₁ ≫ a = φ₂ ≫ b := Quiver.Hom.op_inj hab
    let χ : Y' ⟶ Z := h'.lift (φ₁ ≫ a) fun w ↦ hinter ▸
      ⟨by rw [comp_spaComap]; exact h₁.mapsTo_spaComap _,
        by rw [hab', comp_spaComap]; exact h₂.mapsTo_spaComap _⟩
    refine ⟨χ.op, Quiver.Hom.unop_inj (h₁.hom_ext ?_), Quiver.Hom.unop_inj (h₂.hom_ext ?_)⟩
    · simp only [← op_comp, Quiver.Hom.unop_op]
      rw [← Category.assoc, comp_restrict, h'.fac]
      rfl
    · simp only [← op_comp, Quiver.Hom.unop_op]
      rw [← Category.assoc, comp_restrict, h'.fac, hab']
      rfl

end IsRationalLocalization

/-- The canonical completed rational localization `(A⟨T/s⟩, A_U⁺)` of `X : CAff` at `(T, s)` when
`T` spans an open ideal in `X.ring`. -/
@[expose]
noncomputable def rationalLocalization (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) : CAff.{u} :=
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  letI := locUniformSpace P T s (Localization.Away s) hden
  letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  letI := isHuberRing_completion_locTopology P T s (Localization.Away s) hden
  CAff.of (P.rationalLocalizationPair X.pair X.ringOfDefinition_le_plus T s
    (Localization.Away s) hden)

/-- The canonical rational localization of a Tate Huber pair is again Tate. -/
instance instIsTateRingRationalLocalization (X : CAff.{u}) [IsTateRing X.ring]
    (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    IsTateRing (X.rationalLocalization T s hT).ring :=
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  letI := locUniformSpace P T s (Localization.Away s) hden
  letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  isTateRing_completion_locTopology_of_isTateRing P T s (Localization.Away s) hden

/-- The plus ring of `X.rationalLocalization T s hT` is `completedPlusSubring`. -/
@[simp]
theorem rationalLocalization_plus (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    (X.rationalLocalization T s hT).pair.plus =
      completedPlusSubring P X.pair.plus T s (Localization.Away s) hden :=
  X.pairOfDefinition.rationalLocalizationPair_plus X.pair X.ringOfDefinition_le_plus T s
    (Localization.Away s)
    (hasDenominatorPower_of_isOpen_span X.pairOfDefinition T s (Localization.Away s) hT)

/-- The canonical structure morphism `X ⟶ X.rationalLocalization T s hT` in `CAff`. -/
noncomputable def rationalLocalizationHom (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    X ⟶ X.rationalLocalization T s hT :=
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  letI := locUniformSpace P T s (Localization.Away s) hden
  letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  letI := isHuberRing_completion_locTopology P T s (Localization.Away s) hden
  P.toCompletionLocHom X.pair X.ringOfDefinition_le_plus T s (Localization.Away s) hden

/-- Canonical ring isomorphism identifying `(X.rationalLocalization T s hT).ring` with the
completed rational localization `A⟨T/s⟩`. -/
noncomputable def rationalLocalizationRingEquiv (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    (X.rationalLocalization T s hT).ring ≃+* UniformSpace.Completion (Localization.Away s) :=
  RingEquiv.refl _

/-- The canonical ring isomorphism `rationalLocalizationRingEquiv` is continuous. -/
theorem continuous_rationalLocalizationRingEquiv (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    Continuous (rationalLocalizationRingEquiv X T s hT) :=
  continuous_id

/-- The inverse of `rationalLocalizationRingEquiv` is continuous. -/
theorem continuous_rationalLocalizationRingEquiv_symm (X : CAff.{u}) (T : Finset X.ring)
    (s : X.ring) (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    Continuous (rationalLocalizationRingEquiv X T s hT).symm :=
  continuous_id

/-- An element of `(X.rationalLocalization T s hT).ring` belongs to its plus subring if and only
if its image under `rationalLocalizationRingEquiv` belongs to `completedPlusSubring`. -/
theorem mem_rationalLocalization_plus_iff (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    (a : (X.rationalLocalization T s hT).ring) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    a ∈ (X.rationalLocalization T s hT).pair.plus ↔
      rationalLocalizationRingEquiv X T s hT a ∈
        completedPlusSubring P X.pair.plus T s (Localization.Away s) hden := by
  rw [rationalLocalization_plus]
  rfl

/-- Under `rationalLocalizationRingEquiv`, `(X.rationalLocalizationHom T s hT).toRingHom`
computes to `toCompletionLoc`. -/
@[simp]
theorem rationalLocalizationHom_toRingHom_apply (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) (a : X.ring) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    rationalLocalizationRingEquiv X T s hT ((X.rationalLocalizationHom T s hT).toRingHom a) =
      toCompletionLoc P T s (Localization.Away s) hden a := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s (Localization.Away s) hden
  let _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  let _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  dsimp only [rationalLocalizationRingEquiv, rationalLocalizationHom]
  exact congrFun (congrArg DFunLike.coe
    (P.toRingHom_toCompletionLocHom X.pair X.ringOfDefinition_le_plus T s
      (Localization.Away s) hden)) a

private theorem spaComap_rationalLocalizationHom (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    (w : ValuationSpectrum.spa (X.rationalLocalization T s hT).pair.plus) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    (X.rationalLocalizationHom T s hT).spaComap w =
      spaComapLoc P X.pair.plus T s (Localization.Away s) hden
        ⟨w.val, rationalLocalization_plus X T s hT ▸ w.property⟩ := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  let w' : ValuationSpectrum.spa
      (completedPlusSubring P X.pair.plus T s (Localization.Away s) hden) :=
    ⟨w.val, rationalLocalization_plus X T s hT ▸ w.property⟩
  apply Subtype.ext
  have h1 : ((X.rationalLocalizationHom T s hT).spaComap w).val =
      ValuationSpectrum.comap (toCompletionLoc P T s (Localization.Away s) hden) w'.val := by
    rw [Pair.Hom.spaComap_val]
    dsimp only [rationalLocalizationHom]
    rw [P.toRingHom_toCompletionLocHom]
    rfl
  have h2 := congrArg (fun f : TopCat.of _ ⟶ TopCat.of _ ↦ (f w').val)
    (spaComapTopHom_toCompletionLoc P X.pair.plus T s (Localization.Away s) hden)
  exact h1.trans ((spaComap_val _ _ _ _ _ w').symm.trans (h2.trans
    (congrArg Subtype.val
      (congrFun (coe_spaComapLocHom P X.pair.plus T s (Localization.Away s) hden) w'))))

/-- **Wedhorn Lemma 8.1 and Proposition 8.2 in `CAff`**: the canonical morphism
`X.rationalLocalizationHom T s hT` satisfies `IsRationalLocalization`. -/
theorem isRationalLocalization_rationalLocalizationHom (X : CAff.{u}) (T : Finset X.ring)
    (s : X.ring) (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    IsRationalLocalization (X.rationalLocalizationHom T s hT) T s := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  have _ := isHuberRing_completion_locTopology P T s (Localization.Away s) hden
  let e := rationalLocalizationRingEquiv X T s hT
  refine ⟨hT, fun w ↦ ?_, fun {Z} ψ hψ ↦ ?_⟩
  · rw [spaComap_rationalLocalizationHom]
    exact spaComapLoc_mem_rationalSubset P X.pair.plus T s (Localization.Away s) hden _
  · have hfac : ∀ w ∈ ValuationSpectrum.spa Z.pair.plus,
        comap ψ.toRingHom w ∈ rationalSubset X.pair.plus T s := fun w hw ↦ by
      simpa only [Pair.Hom.spaComap_val] using hψ ⟨w, hw⟩
    obtain ⟨g, ⟨hg_cont, hg_comp⟩, hg_uniq⟩ :=
      existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P X.pair.plus T s
        (Localization.Away s) hden Z.pair.plus Z.pair.isRingOfIntegralElements
        ψ.continuous_toRingHom.continuousAt hfac
    have hg_plus : ∀ a ∈ completedPlusSubring P X.pair.plus T s (Localization.Away s) hden,
        g a ∈ Z.pair.plus := by
      intro a ha
      refine Z.pair.isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ ?_
      have hw' : comap g w ∈ ValuationSpectrum.spa
          (completedPlusSubring P X.pair.plus T s (Localization.Away s) hden) :=
        comap_mem_spa_completedPlusSubring P X.pair.plus T s (Localization.Away s) hden g hg_cont
          ((mem_spa_iff _ _).mp hw).1 (by rw [hg_comp]; exact hfac w hw)
      have hw_le := ((mem_spa_iff _ _).mp hw').2 a ha
      rwa [comap_vle, map_one] at hw_le
    refine ⟨⟨g.comp e.toRingHom, hg_cont.comp (continuous_rationalLocalizationRingEquiv X T s hT),
        fun a ha ↦ hg_plus (e a) ((mem_rationalLocalization_plus_iff X T s hT a).mp ha)⟩,
      Pair.Hom.ext (RingHom.ext fun a ↦ ?_), fun χ hχ ↦ Pair.Hom.ext ?_⟩
    · rw [comp_toRingHom, RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, rationalLocalizationHom_toRingHom_apply]
      exact RingHom.congr_fun hg_comp a
    · have hχ_uniq := hg_uniq (χ.toRingHom.comp e.symm.toRingHom)
        ⟨χ.continuous_toRingHom.comp (continuous_rationalLocalizationRingEquiv_symm X T s hT), by
          ext a
          rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
            RingEquiv.coe_toRingHom, ← rationalLocalizationHom_toRingHom_apply X T s hT a,
            RingEquiv.symm_apply_apply, ← RingHom.comp_apply, ← comp_toRingHom, hχ]⟩
      ext a
      have ha := RingHom.congr_fun hχ_uniq (e a)
      simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply] using ha

/-- The canonical restriction morphism between canonical rational localizations of `X : CAff`
along a containment `R(T'/s') ⊆ R(T/s)` of rational subsets. -/
noncomputable def rationalLocalizationRestrict {X : CAff.{u}} {T : Finset X.ring} {s : X.ring}
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    {T' : Finset X.ring} {s' : X.ring}
    (hT' : IsOpen (Ideal.span (T' : Set X.ring) : Set X.ring))
    (hsub : rationalSubset X.pair.plus T' s' ⊆ rationalSubset X.pair.plus T s) :
    X.rationalLocalization T s hT ⟶ X.rationalLocalization T' s' hT' :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).restrict
    (isRationalLocalization_rationalLocalizationHom X T' s' hT') hsub

/-- Composing the canonical structure morphism with `rationalLocalizationRestrict` yields the
canonical structure morphism for the smaller rational subset. -/
@[reassoc (attr := simp)]
theorem rationalLocalizationHom_comp_rationalLocalizationRestrict {X : CAff.{u}}
    {T : Finset X.ring} {s : X.ring} (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    {T' : Finset X.ring} {s' : X.ring}
    (hT' : IsOpen (Ideal.span (T' : Set X.ring) : Set X.ring))
    (hsub : rationalSubset X.pair.plus T' s' ⊆ rationalSubset X.pair.plus T s) :
    X.rationalLocalizationHom T s hT ≫ rationalLocalizationRestrict hT hT' hsub =
      X.rationalLocalizationHom T' s' hT' :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).comp_restrict _ hsub

/-- Restricting a canonical rational localization to itself is the identity morphism. -/
@[simp]
theorem rationalLocalizationRestrict_id {X : CAff.{u}} {T : Finset X.ring} {s : X.ring}
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    rationalLocalizationRestrict (X := X) hT hT subset_rfl =
      𝟙 (X.rationalLocalization T s hT) :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).restrict_self

/-- Restriction morphisms between canonical rational localizations compose functorially. -/
@[reassoc (attr := simp)]
theorem rationalLocalizationRestrict_comp {X : CAff.{u}}
    {T : Finset X.ring} {s : X.ring} (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    {T' : Finset X.ring} {s' : X.ring}
    (hT' : IsOpen (Ideal.span (T' : Set X.ring) : Set X.ring))
    {T'' : Finset X.ring} {s'' : X.ring}
    (hT'' : IsOpen (Ideal.span (T'' : Set X.ring) : Set X.ring))
    (h₁ : rationalSubset X.pair.plus T' s' ⊆ rationalSubset X.pair.plus T s)
    (h₂ : rationalSubset X.pair.plus T'' s'' ⊆ rationalSubset X.pair.plus T' s') :
    rationalLocalizationRestrict hT hT' h₁ ≫ rationalLocalizationRestrict hT' hT'' h₂ =
      rationalLocalizationRestrict hT hT'' (h₂.trans h₁) :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).restrict_comp _ _ h₁ h₂

/-- Under `rationalLocalizationRingEquiv`, `rationalLocalizationRestrict` is the comparison ring
homomorphism `ringHomOfRationalSubsetSubset`. -/
@[simp]
theorem rationalLocalizationRestrict_toRingHom_apply {X : CAff.{u}}
    {T : Finset X.ring} {s : X.ring} (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    {T' : Finset X.ring} {s' : X.ring}
    (hT' : IsOpen (Ideal.span (T' : Set X.ring) : Set X.ring))
    (hsub : rationalSubset X.pair.plus T' s' ⊆ rationalSubset X.pair.plus T s)
    (a : (X.rationalLocalization T s hT).ring) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
    let hden' := hasDenominatorPower_of_isOpen_span P T' s' (Localization.Away s') hT'
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    letI := locUniformSpace P T' s' (Localization.Away s') hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' (Localization.Away s') hden'
    letI := isTopologicalRing_locUniformSpace P T' s' (Localization.Away s') hden'
    rationalLocalizationRingEquiv X T' s' hT'
      ((rationalLocalizationRestrict hT hT' hsub).toRingHom a) =
        ringHomOfRationalSubsetSubset P X.pair.plus
          X.pair.isRingOfIntegralElements.isPowerBounded_of_mem
          T s (Localization.Away s) hden T' s' (Localization.Away s') hden' hsub
          (rationalLocalizationRingEquiv X T s hT a) := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let hden' := hasDenominatorPower_of_isOpen_span P T' s' (Localization.Away s') hT'
  let _ := locUniformSpace P T s (Localization.Away s) hden
  let _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  let _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  let _ := isHuberRing_completion_locTopology P T s (Localization.Away s) hden
  let _ := locUniformSpace P T' s' (Localization.Away s') hden'
  let _ := isUniformAddGroup_locUniformSpace P T' s' (Localization.Away s') hden'
  let _ := isTopologicalRing_locUniformSpace P T' s' (Localization.Away s') hden'
  let _ := isHuberRing_completion_locTopology P T' s' (Localization.Away s') hden'
  let g_pair := pairHomOfRationalSubsetSubset P X.pair.plus
    (fun j _ ↦ X.ringOfDefinition_le_plus j.property)
    X.pair.isRingOfIntegralElements.isPowerBounded_of_mem
    T s (Localization.Away s) hden T' s' (Localization.Away s') hden' hsub
  let f_pair : X.rationalLocalization T s hT ⟶ X.rationalLocalization T' s' hT' :=
    { toRingHom := g_pair.toRingHom
      continuous_toRingHom := g_pair.continuous_toRingHom
      map_mem_plus := fun x hx ↦ by
        rw [rationalLocalization_plus] at hx ⊢
        exact g_pair.map_mem_plus x hx }
  have hf_eq : rationalLocalizationRestrict hT hT' hsub = f_pair := by
    refine (isRationalLocalization_rationalLocalizationHom X T s hT).hom_ext ?_
    rw [rationalLocalizationHom_comp_rationalLocalizationRestrict]
    refine Pair.Hom.ext (RingHom.ext fun x ↦ ?_)
    rw [comp_toRingHom, RingHom.comp_apply]
    dsimp only [f_pair, rationalLocalizationHom]
    rw [pairHomOfRationalSubsetSubset_toRingHom, P.toRingHom_toCompletionLocHom,
      P.toRingHom_toCompletionLocHom]
    exact (RingHom.congr_fun (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P X.pair.plus
      X.pair.isRingOfIntegralElements.isPowerBounded_of_mem
      T s (Localization.Away s) hden T' s' (Localization.Away s') hden' hsub) x).symm
  rw [hf_eq]
  dsimp only [f_pair, rationalLocalizationRingEquiv, g_pair]
  exact RingHom.congr_fun
    (pairHomOfRationalSubsetSubset_toRingHom P X.pair.plus
      (fun j _ ↦ X.ringOfDefinition_le_plus j.property)
      X.pair.isRingOfIntegralElements.isPowerBounded_of_mem
      T s (Localization.Away s) hden T' s' (Localization.Away s') hden' hsub) a

namespace IsRationalLocalization

/-- Canonical isomorphism between `X.rationalLocalization T s hφ.isOpen_span` and any rational
localization `Y` of `X` for `(T, s)`. -/
noncomputable def isoCanonical {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) :
    X.rationalLocalization T s hφ.isOpen_span ≅ Y :=
  (isRationalLocalization_rationalLocalizationHom X T s hφ.isOpen_span).iso hφ

@[reassoc (attr := simp)]
theorem rationalLocalizationHom_comp_isoCanonical_hom {X Y : CAff.{u}} {φ : X ⟶ Y}
    {T : Finset X.ring} {s : X.ring} (hφ : IsRationalLocalization φ T s) :
    X.rationalLocalizationHom T s hφ.isOpen_span ≫ hφ.isoCanonical.hom = φ :=
  comp_iso_hom _ hφ

@[reassoc (attr := simp)]
theorem comp_isoCanonical_inv {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) :
    φ ≫ hφ.isoCanonical.inv = X.rationalLocalizationHom T s hφ.isOpen_span :=
  comp_iso_inv _ hφ

private theorem spaComap_eq_spaComapLoc {X Y : CAff.{u}} {φ : X ⟶ Y}
    {T : Finset X.ring} {s : X.ring} (hφ : IsRationalLocalization φ T s)
    (y : ValuationSpectrum.spa Y.pair.plus) :
    let P := X.pairOfDefinition
    let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hφ.isOpen_span
    letI := locUniformSpace P T s (Localization.Away s) hden
    letI := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
    letI := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
    φ.spaComap y = spaComapLoc P X.pair.plus T s (Localization.Away s) hden
      ⟨(hφ.isoCanonical.hom.spaComap y).val,
        rationalLocalization_plus X T s hφ.isOpen_span ▸
          (hφ.isoCanonical.hom.spaComap y).property⟩ := by
  have hc := congrFun (comp_spaComap
    (X.rationalLocalizationHom T s hφ.isOpen_span) hφ.isoCanonical.hom) y
  rw [rationalLocalizationHom_comp_isoCanonical_hom] at hc
  exact hc.trans (spaComap_rationalLocalizationHom X T s hφ.isOpen_span
    (hφ.isoCanonical.hom.spaComap y))

private theorem isOpenEmbedding_and_range_spaComap {X Y : CAff.{u}} {φ : X ⟶ Y}
    {T : Finset X.ring} {s : X.ring} (hφ : IsRationalLocalization φ T s) :
    IsOpenEmbedding φ.spaComap ∧
      Set.range φ.spaComap = Subtype.val ⁻¹' rationalSubset X.pair.plus T s := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hφ.isOpen_span
  let _ := locUniformSpace P T s (Localization.Away s) hden
  have _ := isUniformAddGroup_locUniformSpace P T s (Localization.Away s) hden
  have _ := isTopologicalRing_locUniformSpace P T s (Localization.Away s) hden
  have _ := isHuberRing_completion_locTopology P T s (Localization.Away s) hden
  let ePlus : ↥(ValuationSpectrum.spa (X.rationalLocalization T s hφ.isOpen_span).pair.plus) ≃ₜ
      ↥(ValuationSpectrum.spa
        (completedPlusSubring P X.pair.plus T s (Localization.Away s) hden)) :=
    Homeomorph.setCongr
      (congrArg ValuationSpectrum.spa (rationalLocalization_plus X T s hφ.isOpen_span))
  let he : ↥(ValuationSpectrum.spa Y.pair.plus) ≃ₜ
      ↥(ValuationSpectrum.spa (X.rationalLocalization T s hφ.isOpen_span).pair.plus) :=
    TopCat.homeoOfIso (spa.mapIso hφ.isoCanonical.op)
  have hcomp : φ.spaComap =
      spaComapLoc P X.pair.plus T s (Localization.Away s) hden ∘ (⇑ePlus ∘ ⇑he) :=
    funext fun w ↦ hφ.spaComap_eq_spaComapLoc w
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact (isOpenEmbedding_spaComapLoc P X.pair.plus X.ringOfDefinition_le_plus T s
      (Localization.Away s) hden).comp (ePlus.isOpenEmbedding.comp he.isOpenEmbedding)
  · rw [hcomp, (ePlus.surjective.comp he.surjective).range_comp,
      range_spaComapLoc P X.pair.plus X.ringOfDefinition_le_plus T s (Localization.Away s) hden]
    exact Set.ext fun _ ↦ mem_spaBasicOpen

/-- Any rational localization `φ : X ⟶ Y` for `(T, s)` induces an open embedding
`Spa(Y) → Spa(X)`. -/
theorem isOpenEmbedding_spaComap {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) : IsOpenEmbedding φ.spaComap :=
  hφ.isOpenEmbedding_and_range_spaComap.1

/-- The image of `Spa(Y) → Spa(X)` for any rational localization `φ : X ⟶ Y` at `(T, s)` is the
rational subset `R(T/s)`. -/
theorem range_spaComap {X Y : CAff.{u}} {φ : X ⟶ Y} {T : Finset X.ring} {s : X.ring}
    (hφ : IsRationalLocalization φ T s) :
    Set.range φ.spaComap = Subtype.val ⁻¹' rationalSubset X.pair.plus T s :=
  hφ.isOpenEmbedding_and_range_spaComap.2

/-- **Composition of rational localizations (for any presenting data in `X`)**: if `φ : X ⟶ Y` is
a rational localization for `(T₁, s₁)`, `ψ : Y ⟶ Z` is a rational localization for `(T₂, s₂)`, and
`(T', s')` has open numerator span in `X.ring` with rational subset `φ.spaComap '' R_Y(T₂/s₂)`, then
the composite `φ ≫ ψ` is a rational localization for `(T', s')`. -/
theorem comp_of_spaComap_image {X Y Z : CAff.{u}} {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset Y.ring} {s₂ : Y.ring}
    (hφ : IsRationalLocalization φ T₁ s₁) (hψ : IsRationalLocalization ψ T₂ s₂)
    {T' : Finset X.ring} {s' : X.ring}
    (hT' : IsOpen (Ideal.span (T' : Set X.ring) : Set X.ring))
    (him : (Subtype.val ⁻¹' rationalSubset X.pair.plus T' s' :
        Set ↥(ValuationSpectrum.spa X.pair.plus)) =
      φ.spaComap '' (Subtype.val ⁻¹' rationalSubset Y.pair.plus T₂ s₂)) :
    IsRationalLocalization (φ ≫ ψ) T' s' where
  isOpen_span := hT'
  mapsTo_spaComap w := by
    rw [comp_spaComap]
    have hw : φ.spaComap (ψ.spaComap w) ∈
        (Subtype.val ⁻¹' rationalSubset X.pair.plus T' s' :
          Set ↥(ValuationSpectrum.spa X.pair.plus)) :=
      him ▸ Set.mem_image_of_mem _ (hψ.mapsTo_spaComap w)
    exact hw
  existsUnique_factorization {W} χ hχ := by
    have hχ₁ : ∀ w : ValuationSpectrum.spa W.pair.plus,
        (χ.spaComap w).val ∈ rationalSubset X.pair.plus T₁ s₁ := fun w ↦ by
      have hw : χ.spaComap w ∈
          (Subtype.val ⁻¹' rationalSubset X.pair.plus T' s' :
            Set ↥(ValuationSpectrum.spa X.pair.plus)) := hχ w
      rw [him] at hw
      obtain ⟨y, -, hy⟩ := hw
      rw [← hy]
      exact hφ.mapsTo_spaComap y
    let χ₁ := hφ.lift χ hχ₁
    have hχ₂ : ∀ w : ValuationSpectrum.spa W.pair.plus,
        (χ₁.spaComap w).val ∈ rationalSubset Y.pair.plus T₂ s₂ := fun w ↦ by
      have hw : φ.spaComap (χ₁.spaComap w) ∈
          (Subtype.val ⁻¹' rationalSubset X.pair.plus T' s' :
            Set ↥(ValuationSpectrum.spa X.pair.plus)) := by
        rw [← Function.comp_apply (f := φ.spaComap) (g := χ₁.spaComap), ← comp_spaComap, hφ.fac]
        exact hχ w
      rw [him] at hw
      obtain ⟨y, hy, hy_eq⟩ := hw
      rwa [← hφ.isOpenEmbedding_spaComap.injective hy_eq]
    refine ⟨hψ.lift χ₁ hχ₂, ?_, fun f hf ↦ ?_⟩
    · dsimp only
      rw [Category.assoc, hψ.fac, hφ.fac]
    · refine hψ.hom_ext (hφ.hom_ext ?_)
      rw [← Category.assoc, hf, hψ.fac, hφ.fac]

open scoped Classical in
/-- **Composition of rational localizations**: the composite `φ ≫ ψ` of two rational localizations
`φ : X ⟶ Y` and `ψ : Y ⟶ Z` is a rational localization for a pair `(T', s')` in `X.ring` whose
rational subset is `φ.spaComap '' R_Y(T₂/s₂)`. -/
theorem exists_comp {X Y Z : CAff.{u}} {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    {T₁ : Finset X.ring} {s₁ : X.ring} {T₂ : Finset Y.ring} {s₂ : Y.ring}
    (hφ : IsRationalLocalization φ T₁ s₁) (hψ : IsRationalLocalization ψ T₂ s₂) :
    ∃ (T' : Finset X.ring) (s' : X.ring),
      (Subtype.val ⁻¹' rationalSubset X.pair.plus T' s' :
          Set ↥(ValuationSpectrum.spa X.pair.plus)) =
        φ.spaComap '' (Subtype.val ⁻¹' rationalSubset Y.pair.plus T₂ s₂) ∧
      IsRationalLocalization (φ ≫ ψ) T' s' := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T₁ s₁ (Localization.Away s₁) hφ.isOpen_span
  let _ := locUniformSpace P T₁ s₁ (Localization.Away s₁) hden
  have _ := isUniformAddGroup_locUniformSpace P T₁ s₁ (Localization.Away s₁) hden
  have _ := isTopologicalRing_locUniformSpace P T₁ s₁ (Localization.Away s₁) hden
  have _ := isHuberRing_completion_locTopology P T₁ s₁ (Localization.Away s₁) hden
  let eIso := hφ.isoCanonical
  let T₂' : Finset (X.rationalLocalization T₁ s₁ hφ.isOpen_span).ring :=
    T₂.image eIso.inv.toRingHom
  let s₂' : (X.rationalLocalization T₁ s₁ hφ.isOpen_span).ring := eIso.inv.toRingHom s₂
  have hT₂' : IsOpen (Ideal.span (T₂' : Set (X.rationalLocalization T₁ s₁ hφ.isOpen_span).ring) :
      Set (X.rationalLocalization T₁ s₁ hφ.isOpen_span).ring) := by
    have heq : (Ideal.span (T₂' : Set (X.rationalLocalization T₁ s₁ hφ.isOpen_span).ring) :
        Set (X.rationalLocalization T₁ s₁ hφ.isOpen_span).ring) =
        eIso.hom.toRingHom ⁻¹' (Ideal.span (T₂ : Set Y.ring) : Set Y.ring) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_preimage, T₂', Finset.coe_image, ← Ideal.map_span]
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · have hle : Ideal.map eIso.inv.toRingHom (Ideal.span (T₂ : Set Y.ring)) ≤
            Ideal.comap eIso.hom.toRingHom (Ideal.span (T₂ : Set Y.ring)) :=
          Ideal.map_le_iff_le_comap.mpr fun y hy ↦ by
            have h := RingHom.congr_fun (comp_toRingHom eIso.inv eIso.hom) y
            rw [eIso.inv_hom_id, id_toRingHom, RingHom.id_apply, RingHom.comp_apply] at h
            rw [Ideal.mem_comap]
            simpa [← h] using hy
        exact hle hx
      · have hx' := Ideal.mem_map_of_mem eIso.inv.toRingHom hx
        rwa [← RingHom.comp_apply, ← comp_toRingHom, eIso.hom_inv_id, id_toRingHom,
          RingHom.id_apply] at hx'
    rw [heq]
    exact hψ.isOpen_span.preimage eIso.hom.continuous_toRingHom
  let W : Opens ↥(ValuationSpectrum.spa
      (completedPlusSubring P X.pair.plus T₁ s₁ (Localization.Away s₁) hden)) :=
    spaBasicOpen (completedPlusSubring P X.pair.plus T₁ s₁ (Localization.Away s₁) hden) T₂' s₂'
  obtain ⟨V, hV, hVT, hloc⟩ := exists_mem_spaRationalOpens_locOpensComap_eq P X.pair.plus T₁ s₁
    (Localization.Away s₁) hden hφ.isOpen_span W (spaBasicOpen_mem_spaRationalOpens hT₂')
  obtain ⟨T', s', hT', rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  have him : (Subtype.val ⁻¹' rationalSubset X.pair.plus T' s' :
        Set ↥(ValuationSpectrum.spa X.pair.plus)) =
      φ.spaComap '' (Subtype.val ⁻¹' rationalSubset Y.pair.plus T₂ s₂) := by
    have hid (y : ValuationSpectrum.spa Y.pair.plus) :
        eIso.inv.spaComap (eIso.hom.spaComap y) = y := by
      have h := congrFun (comp_spaComap eIso.inv eIso.hom) y
      rw [eIso.inv_hom_id, id_spaComap, id_eq] at h
      exact h.symm
    ext v
    refine ⟨fun hv ↦ ?_, ?_⟩
    · have hv₁ : v ∈ (Subtype.val ⁻¹' rationalSubset X.pair.plus T₁ s₁ :
          Set ↥(ValuationSpectrum.spa X.pair.plus)) :=
        mem_spaBasicOpen.mp (hVT (mem_spaBasicOpen.mpr hv))
      rw [← hφ.range_spaComap] at hv₁
      obtain ⟨y, rfl⟩ := hv₁
      refine ⟨y, ?_, rfl⟩
      let w' : ValuationSpectrum.spa
          (completedPlusSubring P X.pair.plus T₁ s₁ (Localization.Away s₁) hden) :=
        ⟨(eIso.hom.spaComap y).val,
          rationalLocalization_plus X T₁ s₁ hφ.isOpen_span ▸ (eIso.hom.spaComap y).property⟩
      have hcomp := hφ.spaComap_eq_spaComapLoc y
      have hy' : w' ∈ locOpensComap P X.pair.plus T₁ s₁ (Localization.Away s₁) hden
          (spaBasicOpen X.pair.plus T' s') := by
        refine (mem_locOpensComap P X.pair.plus T₁ s₁ (Localization.Away s₁) hden _ _).mpr ?_
        rw [← hcomp]
        exact mem_spaBasicOpen.mpr hv
      rw [hloc] at hy'
      have hmem := (mem_rationalSubset_iff _ _ _ _).mp (mem_spaBasicOpen.mp hy')
      have hy'' : eIso.hom.spaComap y ∈
          (Subtype.val ⁻¹' rationalSubset
            (X.rationalLocalization T₁ s₁ hφ.isOpen_span).pair.plus T₂' s₂' :
            Set ↥(ValuationSpectrum.spa (X.rationalLocalization T₁ s₁ hφ.isOpen_span).pair.plus)) :=
        (mem_rationalSubset_iff _ _ _ _).mpr
          ⟨(eIso.hom.spaComap y).property, hmem.2.1, hmem.2.2⟩
      rw [← Pair.Hom.spaComap_preimage_rationalSubset eIso.inv T₂ s₂, Set.mem_preimage,
        hid y] at hy''
      exact hy''
    · rintro ⟨y, hy, rfl⟩
      have hy'' : eIso.hom.spaComap y ∈ eIso.inv.spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset Y.pair.plus T₂ s₂) := by
        simpa only [Set.mem_preimage, hid y] using hy
      rw [Pair.Hom.spaComap_preimage_rationalSubset eIso.inv T₂ s₂] at hy''
      have hy''m := (mem_rationalSubset_iff _ _ _ _).mp hy''
      let w' : ValuationSpectrum.spa
          (completedPlusSubring P X.pair.plus T₁ s₁ (Localization.Away s₁) hden) :=
        ⟨(eIso.hom.spaComap y).val,
          rationalLocalization_plus X T₁ s₁ hφ.isOpen_span ▸ (eIso.hom.spaComap y).property⟩
      have hmem : w'.val ∈ rationalSubset
          (completedPlusSubring P X.pair.plus T₁ s₁ (Localization.Away s₁) hden) T₂' s₂' :=
        (mem_rationalSubset_iff _ _ _ _).mpr ⟨w'.property, hy''m.2.1, hy''m.2.2⟩
      have hy' : w' ∈ locOpensComap P X.pair.plus T₁ s₁ (Localization.Away s₁) hden
          (spaBasicOpen X.pair.plus T' s') := by
        rw [hloc]
        exact mem_spaBasicOpen.mpr hmem
      have hres := (mem_locOpensComap P X.pair.plus T₁ s₁ (Localization.Away s₁) hden _ _).mp hy'
      rw [← hφ.spaComap_eq_spaComapLoc y] at hres
      exact mem_spaBasicOpen.mp hres
  exact ⟨T', s', him, hφ.comp_of_spaComap_image hψ hT' him⟩

open scoped Classical in
/-- Given a morphism `ψ : X ⟶ Y` in `CAff`, a rational localization `φ : X ⟶ X'` for `(T, s)`, and
a rational localization `φ' : Y ⟶ Y'` for `(ψ '' T, ψ s)`, `baseChange` is the induced comparison
morphism `X' ⟶ Y'`. -/
noncomputable def baseChange {X Y X' Y' : CAff.{u}} {φ : X ⟶ X'} {φ' : Y ⟶ Y'}
    {T : Finset X.ring} {s : X.ring} (ψ : X ⟶ Y)
    (hφ : IsRationalLocalization φ T s)
    (hφ' : IsRationalLocalization φ' (T.image ψ.toRingHom) (ψ.toRingHom s)) :
    X' ⟶ Y' :=
  hφ.lift (ψ ≫ φ') fun w ↦ by
    rw [comp_spaComap]
    have hw : φ'.spaComap w ∈
        (Subtype.val ⁻¹' rationalSubset Y.pair.plus (T.image ψ.toRingHom) (ψ.toRingHom s) :
          Set ↥(ValuationSpectrum.spa Y.pair.plus)) := hφ'.mapsTo_spaComap w
    rwa [← Pair.Hom.spaComap_preimage_rationalSubset ψ T s] at hw

open scoped Classical in
/-- Base change commutes with the rational localization morphisms:
`φ ≫ hφ.baseChange ψ hφ' = ψ ≫ φ'`. -/
@[reassoc (attr := simp)]
theorem comp_baseChange {X Y X' Y' : CAff.{u}} {φ : X ⟶ X'} {φ' : Y ⟶ Y'}
    {T : Finset X.ring} {s : X.ring} (ψ : X ⟶ Y)
    (hφ : IsRationalLocalization φ T s)
    (hφ' : IsRationalLocalization φ' (T.image ψ.toRingHom) (ψ.toRingHom s)) :
    φ ≫ hφ.baseChange ψ hφ' = ψ ≫ φ' :=
  hφ.fac _ _

open scoped Classical in
/-- Base change of a rational localization along any morphism `ψ : X ⟶ Y` (when the mapped
numerator ideal is open) forms a pullback square in `CAffᵒᵖ`. -/
theorem isPullback_baseChange {X Y X' Y' : CAff.{u}} {φ : X ⟶ X'} {φ' : Y ⟶ Y'}
    {T : Finset X.ring} {s : X.ring} (ψ : X ⟶ Y)
    (hφ : IsRationalLocalization φ T s)
    (hφ' : IsRationalLocalization φ' (T.image ψ.toRingHom) (ψ.toRingHom s)) :
    IsPullback (hφ.baseChange ψ hφ').op φ'.op φ.op ψ.op := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← op_comp, ← op_comp, comp_baseChange]
  · rintro ⟨Z⟩ ⟨g₁⟩ ⟨g₂⟩ _ hg
    have hg' : φ' ≫ g₁ = φ' ≫ g₂ :=
      Quiver.Hom.op_inj (by rw [op_comp, op_comp]; exact hg)
    exact Quiver.Hom.unop_inj (hφ'.hom_ext hg'.symm).symm
  · rintro ⟨Z⟩ ⟨a⟩ ⟨b⟩ hab
    have hab' : φ ≫ a = ψ ≫ b := Quiver.Hom.op_inj hab
    let χ : Y' ⟶ Z := hφ'.lift b fun w ↦ by
      have hw : ψ.spaComap (b.spaComap w) ∈
          (Subtype.val ⁻¹' rationalSubset X.pair.plus T s :
            Set ↥(ValuationSpectrum.spa X.pair.plus)) := by
        rw [← Function.comp_apply (f := ψ.spaComap) (g := b.spaComap), ← comp_spaComap, ← hab',
          comp_spaComap]
        exact hφ.mapsTo_spaComap _
      exact Set.mem_preimage.mp
        ((Set.ext_iff.mp (Pair.Hom.spaComap_preimage_rationalSubset ψ T s) (b.spaComap w)).mp hw)
    refine ⟨χ.op, Quiver.Hom.unop_inj (hφ.hom_ext ?_), Quiver.Hom.unop_inj ?_⟩
    · rw [← op_comp, Quiver.Hom.unop_op, ← Category.assoc, comp_baseChange, Category.assoc,
        hφ'.fac, ← hab']
      rfl
    · rw [← op_comp, Quiver.Hom.unop_op, hφ'.fac]
      rfl

end IsRationalLocalization

open scoped Classical in
/-- Canonical comparison morphism between canonical rational localizations induced by a morphism
`ψ : X ⟶ Y` in `CAff` whose mapped numerator ideal `Ideal.span (ψ '' T)` is open in `Y.ring`. -/
noncomputable def rationalLocalizationBaseChange {X Y : CAff.{u}} (ψ : X ⟶ Y)
    {T : Finset X.ring} {s : X.ring}
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    (hT' : IsOpen (Ideal.span ((T.image ψ.toRingHom) : Set Y.ring) : Set Y.ring)) :
    X.rationalLocalization T s hT ⟶
      Y.rationalLocalization (T.image ψ.toRingHom) (ψ.toRingHom s) hT' :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).baseChange ψ
    (isRationalLocalization_rationalLocalizationHom Y (T.image ψ.toRingHom) (ψ.toRingHom s) hT')

open scoped Classical in
/-- Canonical rational localization commutes with `rationalLocalizationBaseChange`. -/
@[reassoc (attr := simp)]
theorem rationalLocalizationHom_comp_rationalLocalizationBaseChange {X Y : CAff.{u}} (ψ : X ⟶ Y)
    {T : Finset X.ring} {s : X.ring}
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    (hT' : IsOpen (Ideal.span ((T.image ψ.toRingHom) : Set Y.ring) : Set Y.ring)) :
    X.rationalLocalizationHom T s hT ≫ rationalLocalizationBaseChange ψ hT hT' =
      ψ ≫ Y.rationalLocalizationHom (T.image ψ.toRingHom) (ψ.toRingHom s) hT' :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).comp_baseChange ψ _

open scoped Classical in
/-- The canonical base change of a rational localization along a morphism `ψ : X ⟶ Y` with open
mapped numerator ideal is a pullback square in `CAffᵒᵖ`. -/
theorem isPullback_rationalLocalizationBaseChange {X Y : CAff.{u}} (ψ : X ⟶ Y)
    {T : Finset X.ring} {s : X.ring}
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring))
    (hT' : IsOpen (Ideal.span ((T.image ψ.toRingHom) : Set Y.ring) : Set Y.ring)) :
    IsPullback
      (rationalLocalizationBaseChange ψ hT hT').op
      (Y.rationalLocalizationHom (T.image ψ.toRingHom) (ψ.toRingHom s) hT').op
      (X.rationalLocalizationHom T s hT).op
      ψ.op :=
  (isRationalLocalization_rationalLocalizationHom X T s hT).isPullback_baseChange ψ _

/-- For open-span data `(T, s)` on `X : CAff`, the identity `𝟙 X` is a rational localization for
`(T, s)` if and only if `R(T/s)` contains all of `Spa(X)`. -/
theorem isRationalLocalization_id_iff (X : CAff.{u}) (T : Finset X.ring) (s : X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    IsRationalLocalization (𝟙 X) T s ↔
      ∀ w : ValuationSpectrum.spa X.pair.plus, w.val ∈ rationalSubset X.pair.plus T s :=
  ⟨fun h w ↦ by simpa using h.mapsTo_spaComap w,
    fun h ↦ ⟨hT, fun w ↦ by simpa using h w,
      fun {Z} ψ _ ↦ ⟨ψ, Category.id_comp ψ, fun χ hχ ↦ by simpa using hχ⟩⟩⟩

/-- The identity morphism `𝟙 X` is a rational localization of `X` for `({1}, 1)`. -/
theorem isRationalLocalization_id_one (X : CAff.{u}) :
    IsRationalLocalization (𝟙 X) {1} 1 :=
  (isRationalLocalization_id_iff X {1} 1 (by simp)).mpr fun w ↦ by
    rw [rationalSubset_singleton_one]
    exact w.property

/-- For an open numerator ideal `(T)`, the identity `𝟙 X` is a rational localization at `(T, 0)`
if and only if `X.ring` is trivial. -/
theorem isRationalLocalization_id_zero_iff (X : CAff.{u}) (T : Finset X.ring)
    (hT : IsOpen (Ideal.span (T : Set X.ring) : Set X.ring)) :
    IsRationalLocalization (𝟙 X) T 0 ↔ Subsingleton X.ring :=
  ⟨fun h ↦ h.subsingleton_ring, fun h ↦
    (isRationalLocalization_id_iff X T 0 hT).mpr fun w ↦
      ((isEmpty_spa_iff X).mpr h).elim w⟩

/-- The canonical rational localization of an intersection `R(T'/s') = R(T₁/s₁) ∩ R(T₂/s₂)` of
two rational subsets is a pullback in `CAffᵒᵖ`. -/
theorem isPullback_rationalLocalizationRestrict {X : CAff.{u}}
    {T₁ : Finset X.ring} {s₁ : X.ring} (hT₁ : IsOpen (Ideal.span (T₁ : Set X.ring) : Set X.ring))
    {T₂ : Finset X.ring} {s₂ : X.ring} (hT₂ : IsOpen (Ideal.span (T₂ : Set X.ring) : Set X.ring))
    {T' : Finset X.ring} {s' : X.ring} (hT' : IsOpen (Ideal.span (T' : Set X.ring) : Set X.ring))
    (hinter : rationalSubset X.pair.plus T' s' =
      rationalSubset X.pair.plus T₁ s₁ ∩ rationalSubset X.pair.plus T₂ s₂) :
    IsPullback
      (rationalLocalizationRestrict hT₁ hT' (hinter.le.trans Set.inter_subset_left)).op
      (rationalLocalizationRestrict hT₂ hT' (hinter.le.trans Set.inter_subset_right)).op
      (X.rationalLocalizationHom T₁ s₁ hT₁).op
      (X.rationalLocalizationHom T₂ s₂ hT₂).op :=
  (isRationalLocalization_rationalLocalizationHom X T₁ s₁ hT₁).isPullback
    (isRationalLocalization_rationalLocalizationHom X T₂ s₂ hT₂)
    (isRationalLocalization_rationalLocalizationHom X T' s' hT') hinter

end TauCeti.CAff

end
