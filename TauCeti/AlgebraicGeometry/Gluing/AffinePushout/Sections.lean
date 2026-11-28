/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.Pullback

import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import TauCeti.Algebra.Category.Ring.Pullback
import TauCeti.AlgebraicGeometry.Gluing.AffinePushout.Basic
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.RingTheory.Localization.Pullback

/-!
# Sections of the affine Ferrand square

The two public results describe the actual section maps induced by the projections from a
ring fiber product and the maps to their common target:

* `RingHom.isPullback_SpecMap_pullback_sections_basicOpen` gives the pullback square on each
  principal open, using `Scheme.Hom.appLE` for its four section maps.
* `RingHom.isPullback_SpecMap_pullback_sections` gives the pullback square on every open and
  its inverse images. Its right overlap map uses `Scheme.Hom.appLE` to identify the two
  equal inverse-image opens over the common ring.

Both statements apply to arbitrary ring maps. The principal-open result describes sections
on the standard affine basis. The arbitrary-open result identifies sections over any open
with pairs of sections whose restrictions agree on its inverse image in `Spec C`.

See [Ferrand, *Conducteur, descente et pincement*][ferrand], Theorem 5.1, and the
localization argument in the Stacks Project, [Lemma 15.5.3][stacks-01Z8].

[ferrand]: https://www.numdam.org/articles/10.24033/bsmf.2455/
[stacks-01Z8]: https://stacks.math.columbia.edu/tag/01Z8
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace RingHom

variable {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
variable (p : B →+* C) (q : D →+* C)

/-- On a principal open of the spectrum of a ring fiber product, the actual section-ring
maps form a pullback square. -/
theorem isPullback_SpecMap_pullback_sections_basicOpen (r : p.pullback q) :
    IsPullback
      ((Spec.map (CommRingCat.ofHom (p.pullbackFst q))).appLE
        (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (p.pullbackFst q r))
        (by rw [SpecMap_preimage_basicOpen]; exact le_rfl))
      ((Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).appLE
        (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (p.pullbackSnd q r))
        (by rw [SpecMap_preimage_basicOpen]; exact le_rfl))
      ((Spec.map (CommRingCat.ofHom p)).appLE
        (PrimeSpectrum.basicOpen (p.pullbackFst q r))
        (PrimeSpectrum.basicOpen (p (p.pullbackFst q r)))
        (by rw [SpecMap_preimage_basicOpen]; exact le_rfl))
      ((Spec.map (CommRingCat.ofHom q)).appLE
        (PrimeSpectrum.basicOpen (p.pullbackSnd q r))
        (PrimeSpectrum.basicOpen (p (p.pullbackFst q r))) (by
          rw [SpecMap_preimage_basicOpen]
          exact le_of_eq (congrArg PrimeSpectrum.basicOpen r.property))) := by
  -- Present the section rings as structure-sheaf objects so their canonical instances match.
  refine (isPullback_pullback p q).localizationAway
    (A' := (Spec.structureSheaf (p.pullback q)).obj.obj (Opposite.op (PrimeSpectrum.basicOpen r)))
    (B' := (Spec.structureSheaf B).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen (p.pullbackFst q r))))
    (C' := (Spec.structureSheaf D).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen (p.pullbackSnd q r))))
    (D' := (Spec.structureSheaf C).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen (p (p.pullbackFst q r)))))
    r ?_ ?_ ?_ ?_
  · exact Spec.map_appLE_basicOpen_algebraMap _ _ _ rfl _
  · exact Spec.map_appLE_basicOpen_algebraMap _ _ _ rfl _
  · exact Spec.map_appLE_basicOpen_algebraMap _ _ _ rfl _
  · exact Spec.map_appLE_basicOpen_algebraMap (CommRingCat.ofHom q) _ _ r.property.symm _

private def overlapSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj
    ((TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom p)).base).obj
      (Spec (CommRingCat.of C)).sheaf)

private def leftSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj (Spec (CommRingCat.of B)).sheaf

private def rightSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).obj (Spec (CommRingCat.of D)).sheaf

private def rightOverlapMap : p.rightSheaf q ⟶ p.overlapSheaf q :=
  (p.commSq_SpecMap_pullback q).rightSheafMap

private def leftMap : (Spec (CommRingCat.of (p.pullback q))).sheaf ⟶ p.leftSheaf q :=
  ⟨(Spec.map (CommRingCat.ofHom (p.pullbackFst q))).c⟩

private def rightMap : (Spec (CommRingCat.of (p.pullback q))).sheaf ⟶ p.rightSheaf q :=
  ⟨(Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).c⟩

private def overlapMorphism : (Spec (CommRingCat.of B)).sheaf ⟶
    (TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom p)).base).obj
      (Spec (CommRingCat.of C)).sheaf := ⟨(Spec.map (CommRingCat.ofHom p)).c⟩

private def leftOverlapMap : p.leftSheaf q ⟶ p.overlapSheaf q :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).map (overlapMorphism p)

-- These component equations isolate the pushforward and sheaf wrappers.
private theorem leftMap_app (V : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    (p.leftMap q).hom.app (Opposite.op V) =
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).app V := rfl

private theorem rightMap_app (V : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    (p.rightMap q).hom.app (Opposite.op V) =
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).app V := rfl

private theorem leftOverlapMap_app (V : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    (p.leftOverlapMap q).hom.app (Opposite.op V) = (Spec.map (CommRingCat.ofHom p)).app
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ V) := rfl

private theorem rightOverlapMap_app (V : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    (p.rightOverlapMap q).hom.app (Opposite.op V) =
      (Spec.map (CommRingCat.ofHom q)).appLE
        (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ V)
        (Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
          (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ V))
        ((p.commSq_SpecMap_pullback q).preimage_preimage_eq V).le :=
  (p.commSq_SpecMap_pullback q).rightSheafMap_app V

private theorem sheafSquare_comm :
    p.leftMap q ≫ p.leftOverlapMap q = p.rightMap q ≫ p.rightOverlapMap q := by
  refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext ?_)
  funext V
  rw [TopCat.Sheaf.comp_app, TopCat.Sheaf.comp_app]
  have h := (p.commSq_SpecMap_pullback q).app_comp_app_eq_app_comp_appLE V.unop
  simp only [← leftMap_app, ← rightMap_app, ← leftOverlapMap_app,
    ← rightOverlapMap_app, Opposite.op_unop] at h
  exact h

private theorem isPullback_sections_basicOpen_preimage (x : p.pullback q) :
    let V : (Spec (CommRingCat.of (p.pullback q))).Opens := PrimeSpectrum.basicOpen x
    let f := Spec.map (CommRingCat.ofHom (p.pullbackFst q))
    let g := Spec.map (CommRingCat.ofHom (p.pullbackSnd q))
    let i := Spec.map (CommRingCat.ofHom p)
    let j := Spec.map (CommRingCat.ofHom q)
    IsPullback (f.app V) (g.app V) (i.app (f ⁻¹ᵁ V))
      (j.appLE (g ⁻¹ᵁ V) (i ⁻¹ᵁ (f ⁻¹ᵁ V))
        ((p.commSq_SpecMap_pullback q).preimage_preimage_eq V).le) := by
  intro V f g i j
  -- Quantify the inclusions so rewriting opens transports every dependent section map.
  let P (U : (Spec (CommRingCat.of B)).Opens) (W : (Spec (CommRingCat.of D)).Opens)
      (T : (Spec (CommRingCat.of C)).Opens) :=
    ∀ (hf : U ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) (hi : T ≤ i ⁻¹ᵁ U) (hj : T ≤ j ⁻¹ᵁ W),
      IsPullback (f.appLE V U hf) (g.appLE V W hg) (i.appLE U T hi) (j.appLE W T hj)
  have hB : f ⁻¹ᵁ V = PrimeSpectrum.basicOpen (p.pullbackFst q x) :=
    SpecMap_preimage_basicOpen _ _
  have hD : g ⁻¹ᵁ V = PrimeSpectrum.basicOpen (p.pullbackSnd q x) :=
    SpecMap_preimage_basicOpen _ _
  have hC : i ⁻¹ᵁ (f ⁻¹ᵁ V) = PrimeSpectrum.basicOpen (p (p.pullbackFst q x)) :=
    (congrArg (fun W ↦ i ⁻¹ᵁ W) hB).trans (SpecMap_preimage_basicOpen _ _)
  have h : P (f ⁻¹ᵁ V) (g ⁻¹ᵁ V) (i ⁻¹ᵁ (f ⁻¹ᵁ V)) := by
    rw [hC, hB, hD]
    intro _ _ _ _
    exact p.isPullback_SpecMap_pullback_sections_basicOpen q x
  rw [Scheme.Hom.app_eq_appLE f, Scheme.Hom.app_eq_appLE g, Scheme.Hom.app_eq_appLE i]
  exact h le_rfl le_rfl le_rfl ((p.commSq_SpecMap_pullback q).preimage_preimage_eq V).le

private theorem isPullback_sheafSquare :
    IsPullback (p.leftMap q) (p.rightMap q) (p.leftOverlapMap q) (p.rightOverlapMap q) := by
  let V (x : p.pullback q) : (Spec (CommRingCat.of (p.pullback q))).Opens :=
    PrimeSpectrum.basicOpen x
  let E (x : p.pullback q) :=
    TopCat.Sheaf.forget CommRingCat (Spec (CommRingCat.of (p.pullback q))) ⋙
      (evaluation (Opens (Spec (CommRingCat.of (p.pullback q))))ᵒᵖ CommRingCat).obj
        (Opposite.op (V x))
  have hE : JointlyReflectIsomorphisms E :=
    ⟨fun φ _ ↦ TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
      (fun x ↦ (inferInstance : IsIso ((E x).map φ)))⟩
  have (x : p.pullback q) : PreservesLimitsOfShape WalkingCospan (E x) := by
    have : PreservesLimitsOfShape WalkingCospan
        ((evaluation (Opens (Spec (CommRingCat.of (p.pullback q))))ᵒᵖ CommRingCat).obj
          (Opposite.op (V x))) := inferInstance
    infer_instance
  refine .of_isLimit (hE.jointlyReflectsLimit
    (c := PullbackCone.mk (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)) ?_)
  intro x
  refine (PullbackCone.isLimitMapConeEquiv _ (E x)).symm ?_
  have h : IsPullback ((E x).map (p.leftMap q)) ((E x).map (p.rightMap q))
      ((E x).map (p.leftOverlapMap q)) ((E x).map (p.rightOverlapMap q)) := by
    -- Forgetting the sheaf and evaluating at `V x` takes a morphism to its `.hom.app` component.
    change IsPullback ((p.leftMap q).hom.app _) ((p.rightMap q).hom.app _)
      ((p.leftOverlapMap q).hom.app _) ((p.rightOverlapMap q).hom.app _)
    rw [leftMap_app, rightMap_app, leftOverlapMap_app, rightOverlapMap_app]
    exact p.isPullback_sections_basicOpen_preimage q x
  exact h.isLimit

/-- For every open `U` of `Spec (B ×_C D)`, the section square on `U` and its inverse
images in `Spec B`, `Spec D`, and `Spec C` is a pullback. No surjectivity assumption is needed. -/
theorem isPullback_SpecMap_pullback_sections
    (U : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    IsPullback
      ((Spec.map (CommRingCat.ofHom (p.pullbackFst q))).app U)
      ((Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).app U)
      ((Spec.map (CommRingCat.ofHom p)).app
        (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U))
      ((Spec.map (CommRingCat.ofHom q)).appLE
        (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U)
        (Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
          (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U))
        (by exact ((p.commSq_SpecMap_pullback q).preimage_preimage_eq U).le)) := by
  have h : IsPullback ((p.leftMap q).hom.app (Opposite.op U))
      ((p.rightMap q).hom.app (Opposite.op U))
      ((p.leftOverlapMap q).hom.app (Opposite.op U))
      ((p.rightOverlapMap q).hom.app (Opposite.op U)) :=
    ((isPullback_sheafSquare p q).map (TopCat.Sheaf.forget CommRingCat _)).app (Opposite.op U)
  rw [leftMap_app, rightMap_app, leftOverlapMap_app, rightOverlapMap_app] at h
  exact h

end RingHom
