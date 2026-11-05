/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.FiniteNormal.Basic
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Normal
import TauCeti.RingTheory.CohenMacaulay.Normal
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Finite normal models of covers of a punctured spectrum

Over a Noetherian normal local domain of dimension at least two, every finite étale cover of
the punctured spectrum is the restriction of the spectrum of its sections algebra. This algebra
is finite, torsion free, normal, and étale away from the closed fibre. Together with full
faithfulness of restriction, this gives the anti-equivalence between finite étale covers of the
punctured spectrum and finite normal torsion-free algebras étale away from the closed point.

The sections algebra is normal by the Hartogs criterion in
`TauCeti.AlgebraicGeometry.Spec.isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt`:
its restriction to the puncture recovers the original cover, so restriction on sections is an
isomorphism, and it is étale over the normal base at every point of that open subset.
The natural comparison with Mathlib's `AlgebraicGeometry.algΓ` uses the counits of
`Over.mapPullbackAdj` and `AlgebraicGeometry.algΓAlgSpecAdjunction`.

Torsion freeness excludes factors supported on the closed fibre, such as the residue-field
factor of `A × κ(A)`; without it the anti-equivalence would be false.

## References

* [The Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9),
  with the additional torsion-freeness hypothesis on the finite normal algebras.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing Opposite

universe u

namespace TauCeti.IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] [IsIntegrallyClosed A]

open TauCeti.AlgebraicGeometry.Spec in
/-- The sections of a finite étale cover of the punctured spectrum of a Noetherian normal local
domain of dimension at least two form a finite normal torsion-free algebra, étale away from the
closed fibre. Normality means that every prime localization is an integrally closed domain. -/
theorem finiteNormalPuncturedEtale_sections (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
    finiteNormalPuncturedEtale A (CommAlgCat.of A Γ(V.obj.left, ⊤)) := by
  let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
  let := φ.hom.toAlgebra
  have hdepth := two_le_depth_of_isIntegrallyClosed hdim
  have := finite_sections A hdepth V
  have := isTorsionFree_sections A V
  have : Algebra.FinitePresentation A Γ(V.obj.left, ⊤) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have het := isEtaleAt_sections A hdepth V
  refine (finiteNormalPuncturedEtale_iff A _).mpr ⟨inferInstance, inferInstance, ?_, het⟩
  let g := Spec.map (CommRingCat.ofHom (algebraMap A Γ(V.obj.left, ⊤)))
  let U := puncturedSpectrum A
  let W := g ⁻¹ᵁ U
  have hpb := isPullback_puncturedSpectrum_toSpecΓ A hdepth V.obj.hom
  let e := hpb.isoIsPullback _ _ (isPullback_morphismRestrict g U)
  -- The isomorphism from the cover to `W` identifies `W.ι` with the canonical map to its
  -- spectrum of sections, which is always an isomorphism on global functions.
  have he : e.hom ≫ W.ι = V.obj.left.toSpecΓ := hpb.isoIsPullback_hom_snd _ _ _
  have hΓ : IsIso (e.hom ≫ W.ι).appTop := by
    rw [he, Scheme.toSpecΓ_appTop]
    infer_instance
  have : IsIso e.hom.appTop := Scheme.Γ.map_isIso e.hom.op
  have : IsIso W.ι.appTop := by
    rw [Scheme.Hom.comp_appTop] at hΓ
    exact IsIso.of_isIso_comp_right _ e.hom.appTop
  intro q _
  refine isDomain_and_isIntegrallyClosed_localization_atPrime_of_isEtaleAt W
      (fun p hp ↦ het p.asIdeal ((mem_preimage_puncturedSpectrum_iff A p).mp hp)) ?_ q
  have hW := (ConcreteCategory.isIso_iff_bijective (W.ι.appTop ≫ W.topIso.hom)).mp inferInstance
  have heq : W.ι.appTop ≫ W.topIso.hom =
      (Spec (.of Γ(V.obj.left, ⊤))).presheaf.map W.leTop.op := by
    -- The middle object is sections on the restricted scheme, hence on the image open.
    -- `erw` lets functoriality recognize that identification.
    erw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    congr 1
  rwa [heq] at hW

/-- Every finite étale cover of the punctured spectrum of a Noetherian normal local domain of
dimension at least two is the restriction of a finite normal torsion-free algebra. The algebra
can be chosen to be the ring of sections of the given cover. -/
@[stacks 0BM9 "essential surjectivity, with torsion-free finite normal algebras"]
theorem exists_restrictPuncturedSpec_sections_iso (hdim : 2 ≤ ringKrullDim A)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    letI := (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop).hom).toAlgebra
    ∃ h : finiteNormalPuncturedEtale A (CommAlgCat.of A Γ(V.obj.left, ⊤)),
      Nonempty ((restrictPuncturedSpec A).obj
        (op ⟨CommAlgCat.of A Γ(V.obj.left, ⊤), h⟩) ≅ V) := by
  let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
  let := φ.hom.toAlgebra
  refine ⟨finiteNormalPuncturedEtale_sections A hdim V, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  rw [restrictPuncturedSpec_obj_obj]
  let hpb := (isPullback_puncturedSpectrum_toSpecΓ A
    (two_le_depth_of_isIntegrallyClosed hdim) V.obj.hom).flip
  exact Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd

/-- Restriction from finite normal torsion-free algebras étale away from the closed point is
essentially surjective onto finite étale covers of the punctured spectrum. -/
theorem restrictPuncturedSpec_essSurj (hdim : 2 ≤ ringKrullDim A) :
    (restrictPuncturedSpec A).EssSurj where
  mem_essImage V := by
    let φ := (Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop
    let := φ.hom.toAlgebra
    obtain ⟨h, e⟩ := exists_restrictPuncturedSpec_sections_iso A hdim V
    exact ⟨op ⟨CommAlgCat.of A Γ(V.obj.left, ⊤), h⟩, e⟩

/-- Finite étale covers of the punctured spectrum of a Noetherian normal local domain of
dimension at least two are anti-equivalent to finite normal torsion-free algebras étale away
from the closed point. The inverse functor takes spectra and restricts to the puncture. -/
@[stacks 0BM9 "with torsion-free finite normal algebras"]
def finiteNormalEquiv (hdim : 2 ≤ ringKrullDim A) :
    FiniteEtaleScheme (puncturedSpectrum A).toScheme ≌
      (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ := by
  let ff := restrictPuncturedSpec.fullyFaithful (A := A) hdim
  letI := ff.full
  letI := ff.faithful
  letI := restrictPuncturedSpec_essSurj A hdim
  letI : (restrictPuncturedSpec A).IsEquivalence := {}
  exact (restrictPuncturedSpec A).asEquivalence.symm

/-- The inverse of the finite-normal anti-equivalence is restriction of the spectrum. -/
@[simp]
theorem finiteNormalEquiv_inverse (hdim : 2 ≤ ringKrullDim A) :
    (finiteNormalEquiv A hdim).inverse = restrictPuncturedSpec A :=
  (rfl)

/-- The sections of the restricted spectrum of a finite normal torsion-free algebra recover
that algebra, naturally in algebra homomorphisms. -/
def restrictPuncturedSpecCompSectionsIso (hdim : 2 ≤ ringKrullDim A) :
    restrictPuncturedSpec A ⋙ (finiteEtaleSchemeProperty _).ι ⋙
      Over.map (puncturedSpectrum A).ι ⋙ algΓ (.of A) ≅
        (finiteNormalPuncturedEtale A).ι.op := by
  let F := (finiteNormalPuncturedEtale A).ι.op ⋙ algSpec (.of A)
  let τ := Functor.whiskerRight
    (Functor.whiskerLeft F (Over.mapPullbackAdj (puncturedSpectrum A).ι).counit) (algΓ (.of A))
  have hτ (B : (FiniteNormalPuncturedEtaleAlg A)ᵒᵖ) : IsIso (τ.app B) := by
    obtain ⟨_, _, hn, -⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.unop.property
    have hΓ := isIso_appTop_pullback_fst_puncturedSpectrum A hdim (B := B.unop.obj)
      fun q _ ↦ hn q
    have hbij := (ConcreteCategory.isIso_iff_bijective _).mp hΓ
    have : IsIso (τ.app B).unop :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    exact (isIso_unop_iff _).mp this
  letI := hτ
  letI : IsIso τ := NatIso.isIso_of_isIso_app τ
  let eτ := asIso τ
  letI := algSpec.instFull (R := .of A)
  letI := algSpec.instFaithful (R := .of A)
  letI : IsIso (algΓAlgSpecAdjunction (.of A)).counit :=
    (algΓAlgSpecAdjunction (.of A)).counit_isIso_of_R_fully_faithful
  exact eτ ≪≫ Functor.isoWhiskerLeft _ (asIso (algΓAlgSpecAdjunction (.of A)).counit)

/-- After forgetting the normal-algebra conditions, the forward functor of the anti-equivalence
is naturally isomorphic to global sections with its canonical base-algebra structure.
The naturality equations identify its action on every morphism with pullback of sections. -/
def finiteNormalEquivFunctorCompInclusionIso (hdim : 2 ≤ ringKrullDim A) :
    (finiteNormalEquiv A hdim).functor ⋙ (finiteNormalPuncturedEtale A).ι.op ≅
      (finiteEtaleSchemeProperty _).ι ⋙ Over.map (puncturedSpectrum A).ι ⋙ algΓ (.of A) :=
  Iso.inverseCompIso (G := (finiteNormalEquiv A hdim).symm)
    (restrictPuncturedSpecCompSectionsIso A hdim).symm

end TauCeti.IsLocalRing
