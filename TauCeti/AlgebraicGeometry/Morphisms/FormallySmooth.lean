/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism

/-!
# Formally smooth and formally étale morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *formally smooth* if it has the infinitesimal lifting
property: for every first-order thickening `i : T ⟶ T'` with `T'` affine, every morphism `T ⟶ X`
compatible with a morphism `T' ⟶ S` extends along `i` to at least one morphism `T' ⟶ X` over `S`.
It is *formally étale* if such an extension always exists and is unique (Stacks,
Definitions 37.11.1 (02H0) and 37.8.1 (02HG)). The test thickenings are Tau Ceti's
`IsFirstOrderThickening`: closed immersions whose ideal sheaf squares to zero.

## Main definitions

* `TauCeti.AlgebraicGeometry.FormallySmooth f`: lifts exist along affine first-order
  thickenings.
* `TauCeti.AlgebraicGeometry.FormallyEtale f`: lifts exist and are unique along affine
  first-order thickenings.

## Main results

* Isomorphisms are formally smooth and formally étale, and both classes are stable under
  composition and base change.
* `TauCeti.AlgebraicGeometry.FormallyEtale.formallySmooth`: a formally étale morphism is formally
  smooth.
* `TauCeti.AlgebraicGeometry.formallyEtale_iff`: `f` is formally étale exactly when it is formally
  smooth and lifts along affine first-order thickenings are unique.
* `TauCeti.AlgebraicGeometry.formallySmooth_iff_exists_lift_quotient` and
  `TauCeti.AlgebraicGeometry.formallyEtale_iff_existsUnique_lift_quotient`: it suffices to test
  the lifting property on `Spec (B ⧸ I) ⟶ Spec B` for rings `B` and ideals `I` with `I ^ 2 = ⊥`.
* `TauCeti.AlgebraicGeometry.formallySmooth_Spec_algebraMap_iff` and
  `TauCeti.AlgebraicGeometry.formallyEtale_Spec_algebraMap_iff`, with the ring-map forms
  `formallySmooth_SpecMap_iff` and `formallyEtale_SpecMap_iff`: `Spec A ⟶ Spec R` is formally
  smooth (formally étale) exactly when `A` is, in the sense of Mathlib's `Algebra.FormallySmooth`
  (`Algebra.FormallyEtale`).
* `TauCeti.AlgebraicGeometry.FormallyEtale.of_isOpenImmersion`: open immersions are formally
  étale, hence formally smooth.
* `TauCeti.AlgebraicGeometry.formallyEtale_iff_formallySmooth_and_formallyUnramified`: formally
  étale means formally smooth and formally unramified in the sense of Mathlib's
  `AlgebraicGeometry.FormallyUnramified`.
* `TauCeti.AlgebraicGeometry.FormallySmooth.formallySmooth_appLE` and
  `TauCeti.AlgebraicGeometry.FormallyEtale.formallyEtale_appLE`: the ring maps of a formally smooth
  (formally étale) morphism on affine opens are formally smooth (formally étale), and
  `formallySmooth_iff_of_isAffine`, `formallyEtale_iff_of_isAffine` characterise morphisms of
  affine schemes by their ring maps on global sections.
* `TauCeti.AlgebraicGeometry.etale_iff_formallyEtale`: a morphism locally of finite presentation
  is étale if and only if it is formally étale. Étale morphisms are formally étale
  (`FormallyEtale.of_etale`) because first-order thickenings are universal homeomorphisms, which
  lift uniquely against étale morphisms.
* `TauCeti.AlgebraicGeometry.smooth_of_formallySmooth`: a formally smooth morphism locally of
  finite presentation is smooth; conversely a smooth affine morphism is formally smooth
  (`FormallySmooth.of_smooth_of_isAffineHom`), so `smooth_iff_formallySmooth_of_isAffineHom`.
  That an arbitrary smooth morphism is formally smooth requires gluing lifts over a cover of the
  source, which form a torsor rather than being unique, and is not proved here.

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0).
* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG).
* [Stacks Project, Lemmas 37.11.4 and 37.11.5](https://stacks.math.columbia.edu/tag/02HH), for
  composition and base change.
* [Stacks Project, Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6), smooth morphisms
  and formally smooth morphisms locally of finite presentation.
* [Stacks Project, Lemma 37.8.10](https://stacks.math.columbia.edu/tag/02HM), étale morphisms
  and formally étale morphisms locally of finite presentation.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is *formally smooth* if for every first-order thickening
`i : T ⟶ T'` with `T'` affine, every morphism `g : T ⟶ X` with `g ≫ f = i ≫ h` for some
`h : T' ⟶ S` extends along `i` to a morphism `l : T' ⟶ X` over `S`. Stacks, Definition 37.11.1
(02H0). -/
@[stacks 02H0]
class FormallySmooth (f : X ⟶ S) : Prop where
  exists_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h → ∃ l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

/-- A morphism of schemes `f : X ⟶ S` is *formally étale* if lifts as in `FormallySmooth` exist
and are unique. Stacks, Definition 37.8.1 (02HG). -/
@[stacks 02HG]
class FormallyEtale (f : X ⟶ S) : Prop where
  existsUnique_lift : ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T')
    [IsFirstOrderThickening i] (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h →
      ∃! l : T' ⟶ X, i ≫ l = g ∧ l ≫ f = h

namespace FormallySmooth

/-- An isomorphism is formally smooth: the lift is `h ≫ f⁻¹`. -/
instance (priority := 100) of_isIso (f : X ⟶ S) [IsIso f] : FormallySmooth f where
  exists_lift i _ g h w := ⟨h ≫ inv f, by rw [← Category.assoc, ← w, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id], by simp⟩

/-- A composite of formally smooth morphisms is formally smooth: lift through the second
morphism, then through the first. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) where
  exists_lift i _ a h w := by
    obtain ⟨l₁, hl₁, hl₁'⟩ := exists_lift (f := g) i (a ≫ f) h (by rw [Category.assoc, w])
    obtain ⟨l₂, hl₂, hl₂'⟩ := exists_lift (f := f) i a l₁ hl₁.symm
    exact ⟨l₂, hl₂, by rw [← Category.assoc, hl₂', hl₁']⟩

/-- Formal smoothness is stable under base change: lift into `X` and pair with the given map to
`Y`. -/
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth f] :
    FormallySmooth (pullback.snd f g) where
  exists_lift i _ a h w := by
    obtain ⟨l, hl, hl'⟩ := exists_lift (f := f) i (a ≫ pullback.fst f g) (h ≫ g) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, Category.assoc])
    refine ⟨pullback.lift l h (by rw [hl']), ?_, by simp⟩
    apply pullback.hom_ext <;> simp [hl, w]

/-- Formal smoothness is stable under base change, on the other side. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallySmooth g] :
    FormallySmooth (pullback.fst f g) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

/-- If `g ≫ j` is formally smooth and `j` is a monomorphism, for instance an open immersion, then
`g` is formally smooth. -/
theorem of_comp_of_mono (g : X ⟶ Y) (j : Y ⟶ S) [Mono j] [FormallySmooth (g ≫ j)] :
    FormallySmooth g where
  exists_lift i _ a h w := by
    obtain ⟨l, hl, hl'⟩ := exists_lift (f := g ≫ j) i a (h ≫ j) (by simp [reassoc_of% w])
    exact ⟨l, hl, by rwa [← cancel_mono j, Category.assoc]⟩

end FormallySmooth

namespace FormallyEtale

/-- A formally étale morphism is formally smooth. -/
instance (priority := 100) formallySmooth (f : X ⟶ S) [FormallyEtale f] : FormallySmooth f where
  exists_lift i _ g h w := (existsUnique_lift i g h w).exists

/-- Lifts along an affine first-order thickening through a formally étale morphism are unique. -/
theorem lift_unique (f : X ⟶ S) [FormallyEtale f] {T T' : Scheme.{u}} [IsAffine T']
    (i : T ⟶ T') [IsFirstOrderThickening i] {l₁ l₂ : T' ⟶ X} (h₁ : i ≫ l₁ = i ≫ l₂)
    (h₂ : l₁ ≫ f = l₂ ≫ f) : l₁ = l₂ :=
  (existsUnique_lift (f := f) i (i ≫ l₁) (l₁ ≫ f) (Category.assoc _ _ _)).unique
    ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

end FormallyEtale

/-- A morphism is formally étale exactly when it is formally smooth and lifts along affine
first-order thickenings are unique. -/
theorem formallyEtale_iff (f : X ⟶ S) :
    FormallyEtale f ↔ FormallySmooth f ∧
      ∀ {T T' : Scheme.{u}} [IsAffine T'] (i : T ⟶ T') [IsFirstOrderThickening i]
        (l₁ l₂ : T' ⟶ X), i ≫ l₁ = i ≫ l₂ → l₁ ≫ f = l₂ ≫ f → l₁ = l₂ := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun i _ _ _ h₁ h₂ ↦ FormallyEtale.lift_unique f i h₁ h₂⟩,
    fun ⟨hs, hu⟩ ↦ ⟨fun i _ g h w ↦ ?_⟩⟩
  obtain ⟨l, hl, hl'⟩ := hs.exists_lift i g h w
  exact ⟨l, ⟨hl, hl'⟩, fun l' ⟨hl₁, hl₂⟩ ↦ hu i l' l (hl₁.trans hl.symm) (hl₂.trans hl'.symm)⟩

namespace FormallyEtale

/-- An isomorphism is formally étale. -/
instance (priority := 100) of_isIso (f : X ⟶ S) [IsIso f] : FormallyEtale f :=
  (formallyEtale_iff f).mpr ⟨inferInstance, fun _ _ _ _ _ h ↦ by simpa using h =≫ inv f⟩

/-- A composite of formally étale morphisms is formally étale. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [FormallyEtale f] [FormallyEtale g] :
    FormallyEtale (f ≫ g) := by
  refine (formallyEtale_iff _).mpr ⟨inferInstance, fun i _ l₁ l₂ h₁ h₂ ↦ ?_⟩
  have h₂' : l₁ ≫ f = l₂ ≫ f := lift_unique g i (by simp [reassoc_of% h₁]) (by simpa using h₂)
  exact lift_unique f i h₁ h₂'

/-- Formal étaleness is stable under base change. -/
instance pullback_snd (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale f] :
    FormallyEtale (pullback.snd f g) := by
  refine (formallyEtale_iff _).mpr ⟨inferInstance, fun i _ l₁ l₂ h₁ h₂ ↦ ?_⟩
  have h : l₁ ≫ pullback.fst f g = l₂ ≫ pullback.fst f g :=
    lift_unique f i (by simp [reassoc_of% h₁]) (by simp [pullback.condition, reassoc_of% h₂])
  exact pullback.hom_ext h h₂

/-- Formal étaleness is stable under base change, on the other side. -/
instance pullback_fst (f : X ⟶ S) (g : Y ⟶ S) [FormallyEtale g] :
    FormallyEtale (pullback.fst f g) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

/-- If `g ≫ j` is formally étale and `j` is a monomorphism, for instance an open immersion, then
`g` is formally étale. -/
theorem of_comp_of_mono (g : X ⟶ Y) (j : Y ⟶ S) [Mono j] [FormallyEtale (g ≫ j)] :
    FormallyEtale g :=
  (formallyEtale_iff g).mpr ⟨FormallySmooth.of_comp_of_mono g j,
    fun i _ _ _ h₁ h₂ ↦ lift_unique (g ≫ j) i h₁ (by simp [reassoc_of% h₂])⟩

end FormallyEtale

/-- Formal smoothness can be tested on the first-order thickenings `Spec (B ⧸ I) ⟶ Spec B` with
`I ^ 2 = ⊥`. -/
theorem formallySmooth_iff_exists_lift_quotient (f : X ⟶ S) :
    FormallySmooth f ↔ ∀ (B : CommRingCat.{u}) (I : Ideal B), I ^ 2 = ⊥ →
      ∀ (g : Spec (.of (B ⧸ I)) ⟶ X) (h : Spec B ⟶ S),
        g ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ h →
        ∃ l : Spec B ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = g ∧
          l ≫ f = h := by
  refine ⟨fun hf B I hI g h w ↦ ?_, fun H ↦ ⟨fun {T T'} _ i _ g h w ↦ ?_⟩⟩
  · have := IsFirstOrderThickening.SpecMap_quotient_mk hI
    exact hf.exists_lift _ g h w
  · obtain ⟨I, e, hI, he⟩ := IsFirstOrderThickening.exists_iso_quotient i
    have he' := (Iso.inv_comp_eq _).2 he
    obtain ⟨l, hl, hl'⟩ := H _ I hI (e.inv ≫ g) (T'.isoSpec.inv ≫ h) (by simp [← he', w])
    refine ⟨T'.isoSpec.hom ≫ l, ?_, by simp [hl']⟩
    rw [reassoc_of% he, hl, Iso.hom_inv_id_assoc]

/-- Formal étaleness can be tested on the first-order thickenings `Spec (B ⧸ I) ⟶ Spec B` with
`I ^ 2 = ⊥`. -/
theorem formallyEtale_iff_existsUnique_lift_quotient (f : X ⟶ S) :
    FormallyEtale f ↔ ∀ (B : CommRingCat.{u}) (I : Ideal B), I ^ 2 = ⊥ →
      ∀ (g : Spec (.of (B ⧸ I)) ⟶ X) (h : Spec B ⟶ S),
        g ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ h →
        ∃! l : Spec B ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = g ∧
          l ≫ f = h := by
  refine ⟨fun hf B I hI g h w ↦ ?_, fun H ↦ ⟨fun {T T'} _ i _ g h w ↦ ?_⟩⟩
  · have := IsFirstOrderThickening.SpecMap_quotient_mk hI
    exact hf.existsUnique_lift _ g h w
  · obtain ⟨I, e, hI, he⟩ := IsFirstOrderThickening.exists_iso_quotient i
    have he' := (Iso.inv_comp_eq _).2 he
    obtain ⟨l, ⟨hl, hl'⟩, hu⟩ := H _ I hI (e.inv ≫ g) (T'.isoSpec.inv ≫ h) (by simp [← he', w])
    refine ⟨T'.isoSpec.hom ≫ l, ⟨?_, by simp [hl']⟩, fun l₁ ⟨h₁, h₂⟩ ↦ ?_⟩
    · rw [reassoc_of% he, hl, Iso.hom_inv_id_assoc]
    · rw [← hu (T'.isoSpec.inv ≫ l₁) ⟨by simp [← he', h₁], by simp [h₂]⟩, Iso.hom_inv_id_assoc]

section Algebra

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- For an `R`-algebra `A`, the morphism `Spec A ⟶ Spec R` is formally smooth if and only if `A` is
formally smooth over `R` (Stacks, 00TI, for the ring-theoretic notion). -/
theorem formallySmooth_Spec_algebraMap_iff :
    FormallySmooth (Spec.algebraMap R A) ↔ Algebra.FormallySmooth R A := by
  rw [formallySmooth_iff_exists_lift_quotient, Algebra.FormallySmooth.iff_comp_surjective]
  refine ⟨fun H B _ _ I hI f ↦ ?_, fun H B I hI g h w ↦ ?_⟩
  · obtain ⟨l, hl, hl'⟩ := H (.of B) I hI _ _ (SpecMap_algHom_comp_quotient I f)
    obtain ⟨f', rfl⟩ := exists_algHom_SpecMap_eq l hl'
    rw [SpecMap_quotient_mk_comp_SpecMap_algHom] at hl
    exact ⟨f', AlgHom.ext fun a ↦ congr($(Spec.map_injective hl) a)⟩
  · let := (Spec.preimage h).hom.toAlgebra
    obtain ⟨f, rfl⟩ := exists_algHom_SpecMap_eq (R := R) (B := B ⧸ I) g (by
      rw [w, ← Spec.map_preimage h, ← Spec.map_comp]
      rfl)
    obtain ⟨f', rfl⟩ := H (B := B) I hI f
    refine ⟨_, SpecMap_quotient_mk_comp_SpecMap_algHom I f', ?_⟩
    exact (Spec.homEquivAlgHom.symm f').property.trans (Spec.map_preimage h)

/-- For an `R`-algebra `A`, the morphism `Spec A ⟶ Spec R` is formally étale if and only if `A` is
formally étale over `R` (Stacks, 00UQ, for the ring-theoretic notion). -/
theorem formallyEtale_Spec_algebraMap_iff :
    FormallyEtale (Spec.algebraMap R A) ↔ Algebra.FormallyEtale R A := by
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  refine ⟨fun hE B _ _ I hI ↦ ⟨fun f₁ f₂ hf ↦ ?_, ?_⟩, fun H ↦ ?_⟩
  · have := (formallyEtale_iff_existsUnique_lift_quotient _).1 hE (.of B) I hI _ _
      (SpecMap_algHom_comp_quotient I ((Ideal.Quotient.mkₐ R I).comp f₁))
    have := this.unique
      ⟨SpecMap_quotient_mk_comp_SpecMap_algHom I f₁, (Spec.homEquivAlgHom.symm f₁).property⟩
      ⟨(SpecMap_quotient_mk_comp_SpecMap_algHom I f₂).trans (by rw [hf]),
        (Spec.homEquivAlgHom.symm f₂).property⟩
    exact AlgHom.ext fun a ↦ congr($(Spec.map_injective this) a)
  · have : Algebra.FormallySmooth R A := formallySmooth_Spec_algebraMap_iff.1 inferInstance
    exact Algebra.FormallySmooth.comp_surjective R A I hI
  rw [formallyEtale_iff_existsUnique_lift_quotient]
  intro B I hI g h w
  let := (Spec.preimage h).hom.toAlgebra
  have hh : Spec.algebraMap R B = h := Spec.map_preimage h
  obtain ⟨f, rfl⟩ := exists_algHom_SpecMap_eq (R := R) (B := B ⧸ I) g (by
    rw [w, ← hh, ← Spec.map_comp]
    rfl)
  obtain ⟨f', rfl⟩ := (H (B := B) I hI).2 f
  refine ⟨_, ⟨SpecMap_quotient_mk_comp_SpecMap_algHom I f',
    (Spec.homEquivAlgHom.symm f').property.trans hh⟩, fun l ⟨hl, hl'⟩ ↦ ?_⟩
  obtain ⟨f'', rfl⟩ := exists_algHom_SpecMap_eq (R := R) (B := B) l (hl'.trans hh.symm)
  rw [SpecMap_quotient_mk_comp_SpecMap_algHom] at hl
  rw [(H (B := B) I hI).1 (AlgHom.ext fun a ↦ congr($(Spec.map_injective hl) a))]

end Algebra

/-- The morphism `Spec A ⟶ Spec R` induced by a ring map `φ : R ⟶ A` is formally smooth if and only
if `φ` is formally smooth. -/
theorem formallySmooth_SpecMap_iff {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    FormallySmooth (Spec.map φ) ↔ φ.hom.FormallySmooth :=
  let := φ.hom.toAlgebra
  formallySmooth_Spec_algebraMap_iff (R := R) (A := A)

/-- The morphism `Spec A ⟶ Spec R` induced by a ring map `φ : R ⟶ A` is formally étale if and only
if `φ` is formally étale. -/
theorem formallyEtale_SpecMap_iff {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    FormallyEtale (Spec.map φ) ↔ φ.hom.FormallyEtale :=
  let := φ.hom.toAlgebra
  formallyEtale_Spec_algebraMap_iff (R := R) (A := A)

/-- An open immersion `j : X ⟶ S` is formally étale. A thickening `i : T ⟶ T'` is surjective, so a
morphism `h : T' ⟶ S` with `i ≫ h` factoring through `j` lands in the image of `j`, and then
factors uniquely through `j`. -/
instance (priority := 100) FormallyEtale.of_isOpenImmersion (j : X ⟶ S) [IsOpenImmersion j] :
    FormallyEtale j where
  existsUnique_lift {T T'} _ i _ g h w := by
    have hr : Set.range h ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := i.surjective y
      exact ⟨g x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩
    refine ⟨IsOpenImmersion.lift j h hr, ⟨?_, IsOpenImmersion.lift_fac _ _ _⟩,
      fun l ⟨_, hl⟩ ↦ IsOpenImmersion.lift_uniq _ _ _ l hl⟩
    rw [← cancel_mono j, Category.assoc, IsOpenImmersion.lift_fac, w]

/-! ### Formal unramifiedness -/

/-- A morphism is formally étale exactly when it is formally smooth and formally unramified in the
sense of Mathlib's `AlgebraicGeometry.FormallyUnramified`. -/
theorem formallyEtale_iff_formallySmooth_and_formallyUnramified (f : X ⟶ S) :
    FormallyEtale f ↔ FormallySmooth f ∧ FormallyUnramified f := by
  rw [formallyEtale_iff]
  refine and_congr_right fun _ ↦ ⟨fun H ↦ ?_, fun _ {_ _} _ i _ _ _ h₁ h₂ ↦ ?_⟩
  · refine FormallyUnramified.of_hom_ext f fun R _ φ hφ hker g₁ g₂ h₁ h₂ ↦ ?_
    have := (IsFirstOrderThickening.SpecMap_iff φ hφ).2 (by rwa [← pow_two])
    exact H (Spec.map φ) g₁ g₂ h₁ h₂
  · exact FormallyUnramified.hom_ext i
      ⟨2, by simp [pow_two, IsFirstOrderThickening.ker_mul_self]⟩ f h₁ h₂

/-- A formally étale morphism is formally unramified. -/
instance (priority := 100) FormallyEtale.formallyUnramified (f : X ⟶ S) [FormallyEtale f] :
    FormallyUnramified f :=
  ((formallyEtale_iff_formallySmooth_and_formallyUnramified f).1 ‹_›).2

/-! ### Ring maps on affine opens -/

/-- For affine opens `U ⊆ S` and `V ⊆ X` with `f(V) ⊆ U`, the ring map `Γ(S, U) ⟶ Γ(X, V)` induced
by a formally smooth morphism `f : X ⟶ S` is formally smooth. -/
theorem FormallySmooth.formallySmooth_appLE (f : X ⟶ S) [FormallySmooth f] {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V e).hom.FormallySmooth := by
  have : FormallySmooth (Spec.map (f.appLE U V e) ≫ hU.fromSpec) := by
    rw [hU.SpecMap_appLE_fromSpec f hV e]
    infer_instance
  have := FormallySmooth.of_comp_of_mono (Spec.map (f.appLE U V e)) hU.fromSpec
  exact (formallySmooth_SpecMap_iff _).1 this

/-- For affine opens `U ⊆ S` and `V ⊆ X` with `f(V) ⊆ U`, the ring map `Γ(S, U) ⟶ Γ(X, V)` induced
by a formally étale morphism `f : X ⟶ S` is formally étale. -/
theorem FormallyEtale.formallyEtale_appLE (f : X ⟶ S) [FormallyEtale f] {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V e).hom.FormallyEtale := by
  have : FormallyEtale (Spec.map (f.appLE U V e) ≫ hU.fromSpec) := by
    rw [hU.SpecMap_appLE_fromSpec f hV e]
    infer_instance
  have := FormallyEtale.of_comp_of_mono (Spec.map (f.appLE U V e)) hU.fromSpec
  exact (formallyEtale_SpecMap_iff _).1 this

/-- A morphism `f : X ⟶ S` of affine schemes is formally smooth if and only if the ring map
`Γ(S, ⊤) ⟶ Γ(X, ⊤)` is formally smooth. -/
theorem formallySmooth_iff_of_isAffine [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    FormallySmooth f ↔ f.appTop.hom.FormallySmooth := by
  rw [← formallySmooth_SpecMap_iff]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rw [(Iso.eq_inv_comp _).2 (Scheme.isoSpec_hom_naturality f)]
    infer_instance
  · rw [(Iso.inv_comp_eq _).1 (Scheme.isoSpec_inv_naturality f).symm]
    infer_instance

/-- A morphism `f : X ⟶ S` of affine schemes is formally étale if and only if the ring map
`Γ(S, ⊤) ⟶ Γ(X, ⊤)` is formally étale. -/
theorem formallyEtale_iff_of_isAffine [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    FormallyEtale f ↔ f.appTop.hom.FormallyEtale := by
  rw [← formallyEtale_SpecMap_iff]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rw [(Iso.eq_inv_comp _).2 (Scheme.isoSpec_hom_naturality f)]
    infer_instance
  · rw [(Iso.inv_comp_eq _).1 (Scheme.isoSpec_inv_naturality f).symm]
    infer_instance

/-! ### Smooth and étale morphisms -/

/-- A smooth affine morphism is formally smooth. -/
instance (priority := 100) FormallySmooth.of_smooth_of_isAffineHom (f : X ⟶ S) [Smooth f]
    [IsAffineHom f] : FormallySmooth f where
  exists_lift {T T'} _ i _ a h w := by
    -- Lift through the base change `X ×_S T' ⟶ T'`, a smooth morphism of affine schemes.
    have : FormallySmooth (pullback.snd f h) := by
      rw [formallySmooth_iff_of_isAffine]
      exact ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).1 inferInstance).formallySmooth
    obtain ⟨l, hl, hl'⟩ := exists_lift (f := pullback.snd f h) i (pullback.lift a i w) (𝟙 T')
      (by simp)
    refine ⟨l ≫ pullback.fst f h, by rw [reassoc_of% hl, pullback.lift_fst], ?_⟩
    rw [Category.assoc, pullback.condition, reassoc_of% hl']

/-- A formally smooth morphism locally of finite presentation is smooth. -/
@[stacks 02H6]
theorem smooth_of_formallySmooth (f : X ⟶ S) [FormallySmooth f]
    [LocallyOfFinitePresentation f] : Smooth f := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  exact fun U V e ↦ RingHom.smooth_def.2
    ⟨FormallySmooth.formallySmooth_appLE f U.property V.property e,
      f.finitePresentation_appLE U.property V.property e⟩

/-- An affine morphism locally of finite presentation is smooth if and only if it is formally
smooth. -/
theorem smooth_iff_formallySmooth_of_isAffineHom (f : X ⟶ S) [IsAffineHom f]
    [LocallyOfFinitePresentation f] : Smooth f ↔ FormallySmooth f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ smooth_of_formallySmooth f⟩

/-- An étale morphism is formally étale. -/
instance (priority := 100) FormallyEtale.of_etale (f : X ⟶ S) [Etale f] : FormallyEtale f :=
  -- First-order thickenings are universal homeomorphisms, which lift against étale morphisms.
  (formallyEtale_iff_formallySmooth_and_formallyUnramified f).2
    ⟨⟨fun i _ a h w ↦ let sq : CommSq a i f h := ⟨w⟩; ⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩,
      inferInstance⟩

/-- A formally étale morphism locally of finite presentation is étale. -/
theorem etale_of_formallyEtale (f : X ⟶ S) [FormallyEtale f]
    [LocallyOfFinitePresentation f] : Etale f := by
  rw [HasRingHomProperty.iff_appLE (P := @Etale)]
  intro U V e
  have := FormallyEtale.formallyEtale_appLE f U.property V.property e
  have := f.finitePresentation_appLE U.property V.property e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.etale_algebraMap.2 ⟨inferInstance, inferInstance⟩

/-- A morphism locally of finite presentation is étale if and only if it is formally étale. -/
@[stacks 02HM]
theorem etale_iff_formallyEtale (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Etale f ↔ FormallyEtale f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ etale_of_formallyEtale f⟩

end TauCeti.AlgebraicGeometry
