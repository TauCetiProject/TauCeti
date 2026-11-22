/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.Pullback

import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Gluing.AffinePushout.Basic
import TauCeti.AlgebraicGeometry.Restrict
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
  have h : IsPullback (CommRingCat.ofHom (p.pullbackFst q))
      (CommRingCat.ofHom (p.pullbackSnd q)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) :=
    .of_isLimit (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom p) (CommRingCat.ofHom q))
  -- Present the section rings as structure-sheaf objects so their canonical instances match.
  refine h.localizationAway
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

private theorem spec_pullback_base_comm :
    (Spec.map (CommRingCat.ofHom q)).base ≫
        (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base =
      (Spec.map (CommRingCat.ofHom p)).base ≫
        (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base := by
  exact congrArg (fun f : Spec (CommRingCat.of C) ⟶
    Spec (CommRingCat.of (p.pullback q)) => f.base) (p.commSq_SpecMap_pullback q).w.symm

private def leftSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj (Spec (CommRingCat.of B)).sheaf

private def rightSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).obj (Spec (CommRingCat.of D)).sheaf

private def rightOverlapHom :
    (TopCat.Presheaf.pushforward _
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).obj
      (Spec (CommRingCat.of D)).presheaf ⟶
    (TopCat.Presheaf.pushforward _
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj
      ((TopCat.Presheaf.pushforward _ (Spec.map (CommRingCat.ofHom p)).base).obj
        (Spec (CommRingCat.of C)).presheaf) :=
  (TopCat.Presheaf.pushforward _
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).map
      (Spec.map (CommRingCat.ofHom q)).c ≫
    (TopCat.Presheaf.Pushforward.comp
      (Spec.map (CommRingCat.ofHom q)).base
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base
      (Spec (CommRingCat.of C)).presheaf).inv ≫
    (TopCat.Presheaf.pushforwardEq
      (spec_pullback_base_comm p q)
      (Spec (CommRingCat.of C)).presheaf).hom ≫
    (TopCat.Presheaf.Pushforward.comp
      (Spec.map (CommRingCat.ofHom p)).base
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base
      (Spec (CommRingCat.of C)).presheaf).hom

private def rightOverlapMap : p.rightSheaf q ⟶ p.overlapSheaf q :=
  ⟨p.rightOverlapHom q⟩

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
        ((p.commSq_SpecMap_pullback q).preimage_preimage_eq V).le := by
  -- Evaluate the underlying presheaf morphism to use the pushforward component lemmas.
  change (p.rightOverlapHom q).app (Opposite.op V) = _
  simp only [rightOverlapHom, TopCat.Presheaf.comp_app,
    TopCat.Presheaf.Pushforward.comp_inv_app, TopCat.Presheaf.Pushforward.comp_hom_app,
    TopCat.Presheaf.pushforwardEq_hom_app, TopCat.Presheaf.pushforward_map_app']
  -- Present these components on the scheme section rings to match the appLE laws.
  change (Spec.map (CommRingCat.ofHom q)).app
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ V) ≫ 𝟙 _ ≫
    (Spec (CommRingCat.of C)).presheaf.map
      (homOfLE ((p.commSq_SpecMap_pullback q).preimage_preimage_eq V).le).op ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

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
  let l := p.leftOverlapMap q
  let r := p.rightOverlapMap q
  let t : (Spec (CommRingCat.of (p.pullback q))).sheaf ⟶ Limits.pullback l r :=
    pullback.lift (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)
  have ht : IsIso t := by
    -- Mathlib's `TopCat.Sheaf.isIso_iff_isIso_basis` lets us check the comparison
    -- isomorphism on the basic-open basis.
    apply TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    intro x
    let V : (Spec (CommRingCat.of (p.pullback q))).Opens := PrimeSpectrum.basicOpen x
    let E := TopCat.Sheaf.forget CommRingCat (Spec (CommRingCat.of (p.pullback q))) ⋙
      (evaluation (Opens (Spec (CommRingCat.of (p.pullback q))))ᵒᵖ CommRingCat).obj (Opposite.op V)
    -- Evaluation identifies the sheaf morphisms with their section-ring components.
    have hEval {F G : TopCat.Sheaf CommRingCat
        (Spec (CommRingCat.of (p.pullback q)))} (f : F ⟶ G) :
        E.map f = f.hom.app (Opposite.op V) := rfl
    have h₂ : IsPullback (E.map (p.leftMap q)) (E.map (p.rightMap q))
        (E.map l) (E.map r) := by
      simp only [hEval, l, r, leftMap_app, rightMap_app,
        leftOverlapMap_app, rightOverlapMap_app]
      exact p.isPullback_sections_basicOpen_preimage q x
    -- Record evaluation's limit preservation at the chosen open before composing functors.
    have : PreservesLimitsOfShape WalkingCospan
        ((evaluation (Opens (Spec (CommRingCat.of (p.pullback q))))ᵒᵖ CommRingCat).obj
          (Opposite.op V)) := inferInstance
    have : IsIso (pullbackComparison E l r) := inferInstance
    have ht_map : E.map t ≫ pullbackComparison E l r =
        pullback.lift (E.map (p.leftMap q)) (E.map (p.rightMap q))
          (by simpa only [l, r, ← E.map_comp] using congrArg E.map (sheafSquare_comm p q)) :=
      map_lift_pullbackComparison E l r (sheafSquare_comm p q)
    have ht_comp : IsIso (E.map t ≫ pullbackComparison E l r) := by
      rw [ht_map]
      exact (pullbackIsPullback (E.map l) (E.map r)).nonempty_isLimit_iff_isIso_lift.mp
        ⟨h₂.isLimit⟩
    exact (isIso_comp_right_iff (E.map t) (pullbackComparison E l r)).mp ht_comp
  refine .of_iso_pullback ⟨sheafSquare_comm p q⟩ (asIso t) ?_ ?_
  · exact pullback.lift_fst (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)
  · exact pullback.lift_snd (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)

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
