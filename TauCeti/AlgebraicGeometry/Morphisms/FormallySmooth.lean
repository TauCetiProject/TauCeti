/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

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

## References

* [Stacks Project, Definition 37.11.1](https://stacks.math.columbia.edu/tag/02H0).
* [Stacks Project, Definition 37.8.1](https://stacks.math.columbia.edu/tag/02HG).
* [Stacks Project, Lemmas 37.11.4 and 37.11.5](https://stacks.math.columbia.edu/tag/02HH), for
  composition and base change.
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

end TauCeti.AlgebraicGeometry
