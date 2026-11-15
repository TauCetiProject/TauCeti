/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.EquivalenceRelation
public import TauCeti.CategoryTheory.Sites.KernelPair
public import TauCeti.RingTheory.Invariant.EquivalenceRelation.Quotient

/-!
# The quotient of an affine scheme by a finite locally free equivalence relation

Let `s = algebraMap A B` and `t : A →+* B` define an equivalence relation `Spec B ⇉ Spec A`
(`RingHom.IsSpecEquivRel`) with `B` finite projective over `A` through `s`, and let
`C = {a : s a = t a}` be its ring of invariants. Write `π : Spec A ⟶ Spec C` for the morphism
induced by the inclusion `C → A`. This file states SGA 3, Exposé V, Théorème 4.1, in the affine
case, in terms of schemes:

* `π` is finite, flat, surjective and locally of finite presentation, so it is finite locally free
  and an fppf covering (`RingHom.IsSpecEquivRel.isFinite_SpecMap`,
  `RingHom.IsSpecEquivRel.flat_SpecMap`, `RingHom.IsSpecEquivRel.surjective_SpecMap`,
  `RingHom.IsSpecEquivRel.locallyOfFinitePresentation_SpecMap`);
* the relation is the kernel pair of `π`: `Spec B ≅ Spec A ×_{Spec C} Spec A`, with the two
  projections induced by `s` and `t` (`RingHom.IsSpecEquivRel.isPullback_SpecMap`);
* `π` is the coequalizer of `Spec B ⇉ Spec A` in schemes
  (`RingHom.IsSpecEquivRel.isColimitCofork`), and, under the Yoneda embedding, in fppf sheaves
  (`RingHom.IsSpecEquivRel.isColimitFppfYonedaCofork`). Thus `Spec C` represents the fppf quotient
  sheaf of `Spec A` by the relation.

The ring-theoretic input is `TauCeti.RingTheory.Invariant.EquivalenceRelation.Quotient`: `A` is a
finite, finitely presented and faithfully flat `C`-module, and `A ⊗[C] A → B`,
`x ⊗ y ↦ s x * t y`, is bijective. The latter says that the square formed by `C → A` twice, `s`
and `t` is a pushout of commutative rings (`RingHom.IsSpecEquivRel.isPushout`, in that file),
which `Spec` turns into a pullback. A flat surjective morphism locally of finite presentation is
an effective epimorphism and generates an fppf covering sieve, so both coequalizer statements
follow from the kernel pair.

The same theorem holds for an equivalence relation of schemes. Let `p₁ p₂ : R ⟶ X` be an
equivalence relation in the category of schemes (`CategoryTheory.IsEquivalenceRelation`), with `X`
affine and `p₁` finite locally free, that is, finite, flat and locally of finite presentation.
Then `R` is affine, being finite over `X`, and `p₁` and `p₂` are induced by an affine equivalence
relation on global sections (`AlgebraicGeometry.Scheme.Hom.isSpecEquivRel_appTop`). Its quotient
is the spectrum `X/R` of the ring `{a ∈ Γ(X, ⊤) : p₁^* a = p₂^* a}` of functions on `X` whose two
pullbacks to `R` agree (`AlgebraicGeometry.Scheme.Hom.affineCoequalizer`). The projection
`X ⟶ X/R` is finite locally free and surjective, `R` is its kernel pair `X ×_{X/R} X`, and `X/R`
is the coequalizer of `R ⇉ X` both in schemes and in fppf sheaves. This form applies to relations
given by morphisms of affine schemes which are not presented as spectra of ring homomorphisms.

## Main results

* `RingHom.IsSpecEquivRel.isPullback_SpecMap`: `Spec B ⇉ Spec A` is the kernel pair of `π`.
* `RingHom.IsSpecEquivRel.isColimitCofork`: `π` is the coequalizer of `Spec B ⇉ Spec A`.
* `RingHom.IsSpecEquivRel.isColimitFppfYonedaCofork`: `Spec C` represents the fppf quotient sheaf.
* `AlgebraicGeometry.Scheme.Hom.isSpecEquivRel_appTop`: an equivalence relation of affine schemes
  is an affine equivalence relation on global sections.
* `AlgebraicGeometry.Scheme.Hom.isKernelPair_affineCoequalizerπ`,
  `AlgebraicGeometry.Scheme.Hom.isColimitAffineCoequalizerCofork` and
  `AlgebraicGeometry.Scheme.Hom.isColimitFppfYonedaAffineCoequalizerCofork`: the quotient of an
  affine scheme by a finite locally free equivalence relation of schemes.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, Théorème 4.1.
* The Stacks Project, Chapter *Groupoid Schemes*, Section *Finite flat groupoids, affine case*.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace RingHom.IsSpecEquivRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (h : (algebraMap A B).IsSpecEquivRel t) [Module.Finite A B] [Module.Projective A B]
include h

/-- **The relation is the kernel pair of the quotient map.** If `Spec B ⇉ Spec A` is an
equivalence relation with `B` finite projective over `A` through `s`, and `C = {a : s a = t a}`
is the ring of invariants, then `Spec B` is the fibre product `Spec A ×_{Spec C} Spec A`, with
projections the morphisms induced by `s` and `t`. -/
theorem isPullback_SpecMap :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Spec.map (CommRingCat.ofHom t))
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ h.isPushout

/-- **The quotient map is flat.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
projective over `A` through `s`, then `Spec A ⟶ Spec C` is flat, where `C = {a : s a = t a}` is
the ring of invariants. -/
theorem flat_SpecMap :
    AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.flat
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr ‹_›

/-- **The quotient map is surjective.** If `Spec B ⇉ Spec A` is an equivalence relation with `B`
finite projective over `A` through `s`, then `Spec A ⟶ Spec C` is surjective, where
`C = {a : s a = t a}` is the ring of invariants. -/
theorem surjective_SpecMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.faithfullyFlat
  exact ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›)).2

/-- **The quotient map is locally of finite presentation.** If `Spec B ⇉ Spec A` is an
equivalence relation with `B` finite projective over `A` through `s`, then `Spec A ⟶ Spec C` is
locally of finite presentation, where `C = {a : s a = t a}` is the ring of invariants. -/
theorem locallyOfFinitePresentation_SpecMap :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.finitePresentation
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- **The quotient map is finite.** If `Spec B ⇉ Spec A` is an equivalence relation with `B`
finite projective over `A` through `s`, then `Spec A ⟶ Spec C` is finite, where
`C = {a : s a = t a}` is the ring of invariants. -/
theorem isFinite_SpecMap :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))) := by
  have := h.finite
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr ‹_›

/-- **The categorical quotient.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
projective over `A` through `s`, and `C = {a : s a = t a}` is the ring of invariants, then
`Spec A ⟶ Spec C` is the coequalizer in schemes of the two morphisms `Spec B ⇉ Spec A` induced by
`s` and `t`. -/
noncomputable def isColimitCofork :
    IsColimit (Cofork.ofπ _ h.isPullback_SpecMap.w :
      Cofork (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Spec.map (CommRingCat.ofHom t))) :=
  have := h.flat_SpecMap
  have := h.surjective_SpecMap
  have := h.locallyOfFinitePresentation_SpecMap
  (EffectiveEpi.getStruct _).isColimitCoforkOfIsPullback h.isPullback_SpecMap

/-- **The fppf quotient sheaf.** If `Spec B ⇉ Spec A` is an equivalence relation with `B` finite
projective over `A` through `s`, and `C = {a : s a = t a}` is the ring of invariants, then under
the Yoneda embedding into fppf sheaves, `Spec A ⟶ Spec C` is the coequalizer of the two morphisms
`Spec B ⇉ Spec A` induced by `s` and `t`. Thus `Spec C` represents the fppf quotient sheaf of
`Spec A` by the relation. -/
noncomputable def isColimitFppfYonedaCofork :
    IsColimit (Cofork.ofπ (Scheme.fppfTopology.yoneda.map
        (Spec.map (CommRingCat.ofHom (algebraMap ((algebraMap A B).eqLocus t) A))))
        (by simp only [← Functor.map_comp, h.isPullback_SpecMap.w]) :
      Cofork (Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B))))
        (Scheme.fppfTopology.yoneda.map (Spec.map (CommRingCat.ofHom t)))) :=
  have := h.flat_SpecMap
  have := h.surjective_SpecMap
  have := h.locallyOfFinitePresentation_SpecMap
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology h.isPullback_SpecMap
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _))

end RingHom.IsSpecEquivRel

/-! ### Equivalence relations of schemes on an affine scheme -/

namespace AlgebraicGeometry.Scheme.Hom

variable {R X : Scheme.{u}} (p₁ p₂ : R ⟶ X)

/-- The **affine coequalizer** of two morphisms `p₁ p₂ : R ⟶ X`: the spectrum of the ring
`{a ∈ Γ(X, ⊤) : p₁^* a = p₂^* a}` of functions on `X` whose pullbacks along `p₁` and `p₂` agree.
When `X` is affine and `p₁ p₂` is an equivalence relation with `p₁` finite locally free, it is the
quotient of `X` by the relation (`AlgebraicGeometry.Scheme.Hom.isKernelPair_affineCoequalizerπ`,
`AlgebraicGeometry.Scheme.Hom.isColimitAffineCoequalizerCofork`). -/
noncomputable abbrev affineCoequalizer : Scheme.{u} :=
  Spec (.of (p₁.appTop.hom.eqLocus p₂.appTop.hom))

/-- The projection `X ⟶ Spec {a ∈ Γ(X, ⊤) : p₁^* a = p₂^* a}` to the affine coequalizer of
`p₁ p₂ : R ⟶ X`, induced by the inclusion of the ring of functions with equal pullbacks. -/
noncomputable def affineCoequalizerπ : X ⟶ p₁.affineCoequalizer p₂ :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (p₁.appTop.hom.eqLocus p₂.appTop.hom).subtype)

lemma affineCoequalizerπ_def : p₁.affineCoequalizerπ p₂ =
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (p₁.appTop.hom.eqLocus p₂.appTop.hom).subtype) :=
  (rfl)

/-- The projection to the affine coequalizer coequalizes `p₁` and `p₂`. -/
@[reassoc]
theorem affineCoequalizer_condition :
    p₁ ≫ p₁.affineCoequalizerπ p₂ = p₂ ≫ p₁.affineCoequalizerπ p₂ := by
  rw [affineCoequalizerπ_def, Scheme.toSpecΓ_naturality_assoc,
    Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  exact a.2

section Points

variable (Y Z : Scheme.{u}) [IsAffine Y] [IsAffine Z] {T : Type u} [CommRing T]

-- the `T`-valued point of an affine scheme `Y` given by a ring homomorphism `Γ(Y, ⊤) →+* T`
private noncomputable def pt (x : Γ(Y, ⊤) →+* T) : Spec (.of T) ⟶ Y :=
  Spec.map (CommRingCat.ofHom x) ≫ Y.isoSpec.inv

private lemma pt_injective : Function.Injective (pt Y (T := T)) := fun x y h ↦ by
  simpa using congr(($(Spec.map_injective (cancel_mono _ |>.mp h))).hom)

private lemma pt_surjective : Function.Surjective (pt Y (T := T)) := fun f ↦
  ⟨(Spec.preimage (f ≫ Y.isoSpec.hom)).hom, by simp [pt]⟩

variable {Y Z} in
private lemma pt_comp (f : Y ⟶ Z) (x : Γ(Y, ⊤) →+* T) :
    pt Y x ≫ f = pt Z (x.comp f.appTop.hom) := by
  simp [pt, CommRingCat.ofHom_comp, Scheme.isoSpec_inv_naturality]

end Points

/-- **Equivalence relations of affine schemes are affine equivalence relations.** If
`p₁ p₂ : R ⟶ X` is an equivalence relation in the category of schemes with `R` and `X` affine, then
the ring homomorphisms `Γ(X, ⊤) → Γ(R, ⊤)` induced by `p₁` and `p₂` form an affine equivalence
relation (`RingHom.IsSpecEquivRel`). -/
theorem isSpecEquivRel_appTop [IsAffine R] [IsAffine X] [IsEquivalenceRelation p₁ p₂] :
    p₁.appTop.hom.IsSpecEquivRel p₂.appTop.hom := by
  obtain ⟨e⟩ := IsEquivalenceRelation.nonempty_equivalenceRelation (p₁ := p₁) (p₂ := p₂)
  -- a `T`-valued point of `R` or `X` is a morphism `Spec T ⟶ R` or `Spec T ⟶ X`
  refine ⟨fun T _ x y h₁ h₂ ↦ ?_, fun T _ u ↦ ?_, fun T _ x ↦ ?_, fun T _ x y h ↦ ?_⟩
  · exact pt_injective R (e.right_cancellation _ _ (by rw [pt_comp, pt_comp, h₁])
      (by rw [pt_comp, pt_comp, h₂]))
  · obtain ⟨z, hz⟩ := pt_surjective R (pt X u ≫ e.r)
    refine ⟨z, pt_injective X ?_, pt_injective X ?_⟩ <;>
      simp [← pt_comp, hz]
  · obtain ⟨z, hz⟩ := pt_surjective R (pt R x ≫ e.s)
    refine ⟨z, pt_injective X ?_, pt_injective X ?_⟩ <;>
      simp [← pt_comp, hz, e.symmetry₁, e.symmetry₂]
  · have w : pt R x ≫ p₂ = pt R y ≫ p₁ := by rw [pt_comp, pt_comp, h]
    obtain ⟨z, hz⟩ := pt_surjective R (PullbackCone.IsLimit.lift e.isLimit _ _ w ≫ e.t)
    refine ⟨z, pt_injective X ?_, pt_injective X ?_⟩ <;>
      simp [← pt_comp, hz, e.transitivity₁, e.transitivity₂]

section Quotient

variable [IsAffine X] [IsEquivalenceRelation p₁ p₂] [IsFinite p₁] [Flat p₁]
  [LocallyOfFinitePresentation p₁]

-- the affine case on global sections, `RingHom.IsSpecEquivRel.isPullback_SpecMap` and the
-- properties of `Spec A ⟶ Spec C`, transported along `R ≅ Spec Γ(R, ⊤)` and `X ≅ Spec Γ(X, ⊤)`
private theorem isKernelPair_and :
    IsKernelPair (p₁.affineCoequalizerπ p₂) p₁ p₂ ∧ IsFinite (p₁.affineCoequalizerπ p₂) ∧
      Flat (p₁.affineCoequalizerπ p₂) ∧ Surjective (p₁.affineCoequalizerπ p₂) ∧
      LocallyOfFinitePresentation (p₁.affineCoequalizerπ p₂) := by
  have := isAffine_of_isAffineHom p₁
  let := p₁.appTop.hom.toAlgebra
  have h : (algebraMap Γ(X, ⊤) Γ(R, ⊤)).IsSpecEquivRel p₂.appTop.hom :=
    p₁.isSpecEquivRel_appTop p₂
  have : Module.Finite Γ(X, ⊤) Γ(R, ⊤) := p₁.finite_appTop
  have : Module.Flat Γ(X, ⊤) Γ(R, ⊤) := HasRingHomProperty.appTop @Flat p₁ ‹_›
  have : Algebra.FinitePresentation Γ(X, ⊤) Γ(R, ⊤) :=
    HasRingHomProperty.appTop @LocallyOfFinitePresentation p₁ ‹_›
  have := Module.FinitePresentation.of_finite_of_finitePresentation Γ(X, ⊤) Γ(R, ⊤)
  have := Module.Flat.projective_of_finitePresentation (R := Γ(X, ⊤)) (M := Γ(R, ⊤))
  -- by definition of `RingHom.toAlgebra`, `algebraMap Γ(X, ⊤) Γ(R, ⊤)` is `p₁.appTop.hom`, so the
  -- two rings of invariants agree and `algebraMap` of the subring is its inclusion
  have hπ : p₁.affineCoequalizerπ p₂ = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ((algebraMap Γ(X, ⊤) Γ(R, ⊤)).eqLocus p₂.appTop.hom) Γ(X, ⊤))) := (rfl)
  have := h.isFinite_SpecMap
  have := h.flat_SpecMap
  have := h.surjective_SpecMap
  have := h.locallyOfFinitePresentation_SpecMap
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine h.isPullback_SpecMap.of_iso R.isoSpec.symm X.isoSpec.symm X.isoSpec.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact Scheme.isoSpec_inv_naturality p₁
    · exact Scheme.isoSpec_inv_naturality p₂
    · simp [hπ]
    · simp [hπ]
  all_goals rw [hπ]; infer_instance

/-- **The relation is the kernel pair of the quotient map.** If `p₁ p₂ : R ⟶ X` is an equivalence
relation of schemes with `X` affine and `p₁` finite locally free, then `R` is the fibre product
`X ×_{X/R} X` for the projection `X ⟶ X/R` to the affine coequalizer. -/
theorem isKernelPair_affineCoequalizerπ : IsKernelPair (p₁.affineCoequalizerπ p₂) p₁ p₂ :=
  (isKernelPair_and p₁ p₂).1

/-- The projection to the quotient of an affine scheme by a finite locally free equivalence
relation is finite. -/
instance isFinite_affineCoequalizerπ : IsFinite (p₁.affineCoequalizerπ p₂) :=
  (isKernelPair_and p₁ p₂).2.1

/-- The projection to the quotient of an affine scheme by a finite locally free equivalence
relation is flat. -/
instance flat_affineCoequalizerπ : Flat (p₁.affineCoequalizerπ p₂) :=
  (isKernelPair_and p₁ p₂).2.2.1

/-- The projection to the quotient of an affine scheme by a finite locally free equivalence
relation is surjective. -/
instance surjective_affineCoequalizerπ : Surjective (p₁.affineCoequalizerπ p₂) :=
  (isKernelPair_and p₁ p₂).2.2.2.1

/-- The projection to the quotient of an affine scheme by a finite locally free equivalence
relation is locally of finite presentation. -/
instance locallyOfFinitePresentation_affineCoequalizerπ :
    LocallyOfFinitePresentation (p₁.affineCoequalizerπ p₂) :=
  (isKernelPair_and p₁ p₂).2.2.2.2

/-- **SGA 3, Exposé V, Théorème 4.1, affine case, for schemes.** If `p₁ p₂ : R ⟶ X` is an
equivalence relation of schemes with `X` affine and `p₁` finite locally free, then the projection
`X ⟶ X/R` to the affine coequalizer is the coequalizer of `p₁` and `p₂` in schemes. -/
noncomputable def isColimitAffineCoequalizerCofork :
    IsColimit (Cofork.ofπ _ (p₁.affineCoequalizer_condition p₂)) :=
  (EffectiveEpi.getStruct _).isColimitCoforkOfIsPullback (p₁.isKernelPair_affineCoequalizerπ p₂)

/-- **The fppf quotient sheaf.** If `p₁ p₂ : R ⟶ X` is an equivalence relation of schemes with `X`
affine and `p₁` finite locally free, then under the Yoneda embedding into fppf sheaves, the
projection `X ⟶ X/R` to the affine coequalizer is the coequalizer of `p₁` and `p₂`. Thus `X/R`
represents the fppf quotient sheaf of `X` by `R`. -/
noncomputable def isColimitFppfYonedaAffineCoequalizerCofork :
    IsColimit (Cofork.ofπ (Scheme.fppfTopology.yoneda.map (p₁.affineCoequalizerπ p₂))
        (by rw [← Functor.map_comp, affineCoequalizer_condition, Functor.map_comp]) :
      Cofork (Scheme.fppfTopology.yoneda.map p₁) (Scheme.fppfTopology.yoneda.map p₂)) :=
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology (p₁.isKernelPair_affineCoequalizerπ p₂)
    (Precoverage.generate_mem_toGrothendieck (singleton_mem_fppfPrecoverage _))

end Quotient

end AlgebraicGeometry.Scheme.Hom
