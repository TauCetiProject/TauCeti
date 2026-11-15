/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.UniversalSubgroup

/-!
# Fibres of the universal subgroup with their inclusions

Let `N` be a point of the Hopf-ideal locus over an `R`-algebra `A`. The fibre of the universal
family over its classifying map is already identified with `Spec ((A ⊗[R] H) ⧸ N)`. Here we
identify the inclusion of that fibre: it is the quotient closed immersion into
`Spec (A ⊗[R] H)`. Thus the identification retains the closed subscheme, rather than only
its abstract scheme over `Spec A`.

`isPullback_universalSubgroup_arrow` gives the cartesian square for the actual representative
arrow of `universalSubgroup`. The ambient base-change square is
`isPullback_toSchemeHopfIdealLocusGrp`. Both squares hold for every algebra `A`, with no
flatness or reducedness hypothesis.

The construction uses the universal-family fibre comparison
`isPullback_schemeHopfIdealLocusFamilyHom` and the two projections of the universal inclusion.
The affine ambient square is Mathlib's spectrum of the tensor-product pushout.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), §2.1, for closed subgroups
  as Hopf-ideal quotients.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite

namespace Module.Grassmannian

variable {R A H : Type u} [CommRing R] [CommRing A] [CommRing H]
  [Algebra R A] [HopfAlgebra R H] {k : ℕ}
  (N : G(k, A ⊗[R] H; A)) (hN : N.hopfIdealLocus = ⊥)

/-- The map from `Spec (A ⊗[R] H)` into the ambient group scheme of the universal subgroup,
over the point of the Hopf-ideal locus classifying `N`. Its components are the projection
to `Spec H` and the classifying map after projection to `Spec A`. -/
noncomputable def toSchemeHopfIdealLocusGrp :
    Spec (.of (A ⊗[R] H)) ⟶ (schemeHopfIdealLocusGrp R H k).X.left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : H →ₐ[R] A ⊗[R] H).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫
      (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).1) <| by
    rw [Category.assoc, (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).2]
    exact (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R A H)).w.symm

/-- The projection to `Spec H` of the ambient fibre map is induced by `h ↦ 1 ⊗ h`. -/
@[simp, reassoc]
theorem toSchemeHopfIdealLocusGrp_fst :
    toSchemeHopfIdealLocusGrp N hN ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : H →ₐ[R] A ⊗[R] H).toRingHom) :=
  pullback.lift_fst _ _ _

/-- The ambient fibre map lies over the classifying point of `N`. -/
@[simp, reassoc]
theorem toSchemeHopfIdealLocusGrp_snd :
    toSchemeHopfIdealLocusGrp N hN ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) ≫
        (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).1 :=
  pullback.lift_snd _ _ _

/-- The ambient group scheme pulled back along the point classifying `N` has underlying
scheme `Spec (A ⊗[R] H)`, with its usual projection to `Spec A`. -/
theorem isPullback_toSchemeHopfIdealLocusGrp :
    IsPullback (toSchemeHopfIdealLocusGrp N hN)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k))
      (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).1 := by
  refine IsPullback.of_right ?_ (toSchemeHopfIdealLocusGrp_snd N hN)
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      ((schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k))
  rw [toSchemeHopfIdealLocusGrp_fst,
    (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).2]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R A H)).flip

/-- The fibre map into the universal family intertwines its closed immersion into the
ambient group scheme with the quotient map by `N`. -/
@[reassoc (attr := simp)]
theorem toSchemeHopfIdealLocusFamily_toGrp :
    toSchemeHopfIdealLocusFamily N hN ≫ (schemeHopfIdealLocusFamilyToGrp R H k).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (R := A ⊗[R] H) (N.hopfIdeal hN))) ≫
        toSchemeHopfIdealLocusGrp N hN := by
  apply pullback.hom_ext (f := Spec.map (CommRingCat.ofHom (algebraMap R H)))
    (g := (schemeHopfIdealLocus R H k).subschemeι ≫ toSpec R H k)
  -- The ambient group wrapper must reduce to its pullback presentation for projection rewriting.
  · erw [Category.assoc, Category.assoc, schemeHopfIdealLocusFamilyToGrp_left_fst,
      toSchemeHopfIdealLocusFamily_ι_subschemeι_assoc, toPullbackHom_snd,
      toSchemeHopfIdealLocusGrp_fst]
    rfl
  · erw [Category.assoc, Category.assoc, schemeHopfIdealLocusFamilyToGrp_left_snd,
      toSchemeHopfIdealLocusFamily_schemeHopfIdealLocusFamilyHom, toSchemeHopfIdealLocusGrp_snd]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The inclusion of the fibre is cut out by `N`; the square has vertical closed immersions. -/
private theorem isPullback_schemeHopfIdealLocusFamilyToGrp :
    IsPullback (toSchemeHopfIdealLocusFamily N hN)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (R := A ⊗[R] H) (N.hopfIdeal hN))))
      (schemeHopfIdealLocusFamilyToGrp R H k).left (toSchemeHopfIdealLocusGrp N hN) := by
  refine IsPullback.of_bot ?_ (toSchemeHopfIdealLocusFamily_toGrp N hN)
    (isPullback_toSchemeHopfIdealLocusGrp N hN)
  rw [schemeHopfIdealLocusFamilyToGrp_left_snd]
  convert (isPullback_schemeHopfIdealLocusFamilyHom N hN) using 1
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The map from the quotient Hopf spectrum at `N` to the universal subgroup. It is the fibre
map into the universal family, read through the canonical identification of that family with
the representative of the closed subgroup. -/
noncomputable def toUniversalSubgroup :
    Spec (.of ((A ⊗[R] H) ⧸ N.hopfIdeal hN)) ⟶
      ((universalSubgroup R H k).1 : Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.left :=
  toSchemeHopfIdealLocusFamily N hN ≫ (universalSubgroupIso R H k).inv.hom.hom.left

/-- The map into the universal subgroup respects the closed-subgroup inclusion: on the fibre
it is the quotient closed immersion defined by `N`. -/
@[reassoc (attr := simp)]
theorem toUniversalSubgroup_arrow :
    toUniversalSubgroup N hN ≫ (universalSubgroup R H k).1.arrow.hom.hom.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (R := A ⊗[R] H) (N.hopfIdeal hN))) ≫
        toSchemeHopfIdealLocusGrp N hN := by
  have h := congrArg (fun f ↦ f.hom.hom.left) (universalSubgroupIso_inv_arrow (R := R)
    (H := H) (k := k))
  simp only [Grp.comp_hom_hom, Over.comp_left, Grp.homMk_hom_hom] at h
  rw [toUniversalSubgroup, Category.assoc, h, toSchemeHopfIdealLocusFamily_toGrp]

/-- The map into the universal subgroup lies over the point classifying `N`. -/
@[reassoc (attr := simp)]
theorem toUniversalSubgroup_structureMap :
    toUniversalSubgroup N hN ≫
        ((universalSubgroup R H k).1 : Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap A ((A ⊗[R] H) ⧸ N.hopfIdeal hN))) ≫
        (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).1 := by
  rw [toUniversalSubgroup, Category.assoc, Over.w]
  exact toSchemeHopfIdealLocusFamily_schemeHopfIdealLocusFamilyHom N hN

/-- The fibre of the universal closed-subgroup inclusion along the ambient base change
classifying `N` is exactly the quotient closed immersion
`Spec ((A ⊗[R] H) ⧸ N) ⟶ Spec (A ⊗[R] H)`. -/
theorem isPullback_universalSubgroup_arrow :
    IsPullback (toUniversalSubgroup N hN)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (R := A ⊗[R] H) (N.hopfIdeal hN))))
      (universalSubgroup R H k).1.arrow.hom.hom.left (toSchemeHopfIdealLocusGrp N hN) := by
  let e := (Grp.forget _ ⋙ Over.forget _).mapIso (universalSubgroupIso R H k)
  have h := congrArg (fun f ↦ f.hom.hom.left) (universalSubgroupIso_inv_arrow (R := R)
    (H := H) (k := k))
  simp only [Grp.comp_hom_hom, Over.comp_left, Grp.homMk_hom_hom] at h
  exact (isPullback_schemeHopfIdealLocusFamilyToGrp N hN).of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    (by rfl) (by simp)
    h.symm (by simp)

/-- The underlying scheme of the universal subgroup pulls back along the point classifying
`N` to the quotient Hopf spectrum, with its standard structure map to `Spec A`. -/
theorem isPullback_universalSubgroup :
    IsPullback (toUniversalSubgroup N hN)
      (Spec.map (CommRingCat.ofHom (algebraMap A ((A ⊗[R] H) ⧸ N.hopfIdeal hN))))
      ((universalSubgroup R H k).1 : Grp (Over (schemeHopfIdealLocus R H k).subscheme)).X.hom
      (schemeHopfIdealLocusHomEquiv R H k A ⟨N, hN⟩).1 := by
  let e := (Grp.forget _ ⋙ Over.forget _).mapIso (universalSubgroupIso R H k)
  exact (isPullback_schemeHopfIdealLocusFamilyHom N hN).of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    (by rfl) (by simp) ((universalSubgroupIso R H k).inv.hom.hom.w.symm) (by simp)

end Module.Grassmannian
