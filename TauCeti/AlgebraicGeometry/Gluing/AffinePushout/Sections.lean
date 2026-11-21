/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.RingTheory.Localization.Pullback

/-!
# Sections of the affine Ferrand square

The structure sheaf of the spectrum of a fiber product is the fiber product of the
pushed-forward structure sheaves. This needs neither surjectivity nor finiteness: the
principal-open calculation is localization of a ring pullback. The ring square is recognized
by `CommRingCat.pullbackConeIsLimit`, and `StructureSheaf.IsLocalization.to_basicOpen`
identifies its principal-open sections with localizations. The passage to all opens uses
`TopCat.Sheaf.isIso_iff_isIso_basis` to the canonical lift to the sheaf pullback.

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
theorem isPullback_spec_pullback_basicOpen (r : p.pullback q) :
    IsPullback
      ((Spec.map (CommRingCat.ofHom (p.pullbackFst q))).appLE
        (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (p.pullbackFst q r)) le_rfl)
      ((Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).appLE
        (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen (p.pullbackSnd q r)) le_rfl)
      ((Spec.map (CommRingCat.ofHom p)).appLE
        (PrimeSpectrum.basicOpen (p.pullbackFst q r))
        (PrimeSpectrum.basicOpen (p (p.pullbackFst q r))) le_rfl)
      ((Spec.map (CommRingCat.ofHom q)).appLE
        (PrimeSpectrum.basicOpen (p.pullbackSnd q r))
        (PrimeSpectrum.basicOpen (p (p.pullbackFst q r))) (by
          rw [SpecMap_preimage_basicOpen]
          exact le_of_eq (congrArg PrimeSpectrum.basicOpen r.property))) := by
  have h : IsPullback (CommRingCat.ofHom (p.pullbackFst q))
      (CommRingCat.ofHom (p.pullbackSnd q)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) :=
    .of_isLimit (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom p) (CommRingCat.ofHom q))
  let : Algebra (p.pullback q) Γ(Spec (CommRingCat.of (p.pullback q)),
      PrimeSpectrum.basicOpen r) := StructureSheaf.openAlgebra _ _
  let : Algebra B Γ(Spec (CommRingCat.of B),
      PrimeSpectrum.basicOpen (p.pullbackFst q r)) := StructureSheaf.openAlgebra _ _
  let : Algebra D Γ(Spec (CommRingCat.of D),
      PrimeSpectrum.basicOpen (p.pullbackSnd q r)) := StructureSheaf.openAlgebra _ _
  let : Algebra C Γ(Spec (CommRingCat.of C),
      PrimeSpectrum.basicOpen (p (p.pullbackFst q r))) := StructureSheaf.openAlgebra _ _
  have : IsLocalization.Away r Γ(Spec (CommRingCat.of (p.pullback q)),
      PrimeSpectrum.basicOpen r) := StructureSheaf.IsLocalization.to_basicOpen _ _
  have : IsLocalization.Away (p.pullbackFst q r) Γ(Spec (CommRingCat.of B),
      PrimeSpectrum.basicOpen (p.pullbackFst q r)) := StructureSheaf.IsLocalization.to_basicOpen _ _
  have : IsLocalization.Away (p.pullbackSnd q r) Γ(Spec (CommRingCat.of D),
      PrimeSpectrum.basicOpen (p.pullbackSnd q r)) := StructureSheaf.IsLocalization.to_basicOpen _ _
  have : IsLocalization.Away (p (p.pullbackFst q r)) Γ(Spec (CommRingCat.of C),
      PrimeSpectrum.basicOpen (p (p.pullbackFst q r))) :=
    StructureSheaf.IsLocalization.to_basicOpen _ _
  refine h.localizationAway r ?_ ?_ ?_ ?_ <;>
    exact Spec.appLE_algebraMap _ _ _ _

private def overlapSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj
    ((TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom p)).base).obj
      (Spec (CommRingCat.of C)).sheaf)

private theorem spec_pullback_comm :
    Spec.map (CommRingCat.ofHom p) ≫ Spec.map (CommRingCat.ofHom (p.pullbackFst q)) =
      Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (p.pullback_comm_sq q))

private theorem overlap_preimage (U : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U) =
    Spec.map (CommRingCat.ofHom q) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, spec_pullback_comm]

private theorem overlap_le (U : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U) ≤
    Spec.map (CommRingCat.ofHom q) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U) :=
  le_of_eq (overlap_preimage p q U)

-- Compare both composites on the same source and target opens using `appLE`.
-- This makes the transport along `overlap_preimage` explicit.
private theorem spec_pullback_app_comm
    (U : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).app U ≫
        (Spec.map (CommRingCat.ofHom p)).app
          (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U) =
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).app U ≫
        (Spec.map (CommRingCat.ofHom q)).appLE
          (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U)
          (Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
            (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U))
          (overlap_le p q U) := by
  have h := Scheme.Hom.congr_appLE _ (spec_pullback_comm p q) U
    (Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U))
    (by rw [Scheme.Hom.comp_preimage])
    (by rw [Scheme.Hom.comp_preimage]; exact overlap_le p q U)
  simpa only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE_eq_app] using h

private def leftSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj (Spec (CommRingCat.of B)).sheaf

private def rightSheaf :
    TopCat.Sheaf CommRingCat.{u} (Spec (CommRingCat.of (p.pullback q))) :=
  (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).obj (Spec (CommRingCat.of D)).sheaf

private def rightOverlapMap : p.rightSheaf q ⟶ p.overlapSheaf q :=
  ⟨{ app := fun U ↦ (Spec.map (CommRingCat.ofHom q)).appLE
        (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U.unop)
        (Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
          (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U.unop))
        (p.overlap_le q U.unop)
     naturality := fun U V i ↦ by
       -- Pushforward restriction maps evaluate at the inverse-image opens.
       change (Spec (CommRingCat.of D)).presheaf.map _ ≫ _ =
         _ ≫ (Spec (CommRingCat.of C)).presheaf.map _
       rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
       rfl }⟩

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
        (overlap_le p q V) := rfl

private theorem sheafSquare_comm :
    p.leftMap q ≫ p.leftOverlapMap q = p.rightMap q ≫ p.rightOverlapMap q := by
  refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext ?_)
  funext V
  rw [TopCat.Sheaf.comp_app, TopCat.Sheaf.comp_app]
  change (p.leftMap q).hom.app (Opposite.op V.unop) ≫
      (p.leftOverlapMap q).hom.app (Opposite.op V.unop) =
    (p.rightMap q).hom.app (Opposite.op V.unop) ≫
      (p.rightOverlapMap q).hom.app (Opposite.op V.unop)
  rw [leftMap_app, rightMap_app, leftOverlapMap_app, rightOverlapMap_app]
  exact spec_pullback_app_comm p q V.unop

private theorem isPullback_sheafSquare :
    IsPullback (p.leftMap q) (p.rightMap q) (p.leftOverlapMap q) (p.rightOverlapMap q) := by
  let l := p.leftOverlapMap q
  let r := p.rightOverlapMap q
  let t : (Spec (CommRingCat.of (p.pullback q))).sheaf ⟶ Limits.pullback l r :=
    pullback.lift (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)
  have ht : IsIso t := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    intro x
    let V : (Spec (CommRingCat.of (p.pullback q))).Opens := PrimeSpectrum.basicOpen x
    let E := TopCat.Sheaf.forget CommRingCat (Spec (CommRingCat.of (p.pullback q))) ⋙
      (evaluation (Opens (Spec (CommRingCat.of (p.pullback q))))ᵒᵖ CommRingCat).obj (Opposite.op V)
    have h₁ := ((IsPullback.of_hasPullback l r).map
      (TopCat.Sheaf.forget CommRingCat _)).app (Opposite.op V)
    have h₂ : IsPullback (E.map (p.leftMap q)) (E.map (p.rightMap q))
        (E.map l) (E.map r) := by
      change IsPullback ((p.leftMap q).hom.app (Opposite.op V))
        ((p.rightMap q).hom.app (Opposite.op V))
        ((p.leftOverlapMap q).hom.app (Opposite.op V))
        ((p.rightOverlapMap q).hom.app (Opposite.op V))
      rw [leftMap_app, rightMap_app, leftOverlapMap_app, rightOverlapMap_app]
      exact p.isPullback_spec_pullback_basicOpen q x
    have he : E.map t = h₁.isLimit.lift h₂.cone := by
      apply h₁.hom_ext
      · change E.map t ≫ E.map (pullback.fst l r) = _
        rw [← E.map_comp, pullback.lift_fst]
        exact (PullbackCone.IsLimit.lift_fst h₁.isLimit _ _ h₂.w).symm
      · change E.map t ≫ E.map (pullback.snd l r) = _
        rw [← E.map_comp, pullback.lift_snd]
        exact (PullbackCone.IsLimit.lift_snd h₁.isLimit _ _ h₂.w).symm
    change IsIso (E.map t)
    rw [he]
    exact h₁.isLimit.nonempty_isLimit_iff_isIso_lift.mp ⟨h₂.isLimit⟩
  refine .of_iso_pullback ⟨sheafSquare_comm p q⟩ (asIso t) ?_ ?_
  · exact pullback.lift_fst (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)
  · exact pullback.lift_snd (p.leftMap q) (p.rightMap q) (sheafSquare_comm p q)

/-- For every open `U` of `Spec (B ×_C D)`, the section square on `U` and its inverse
images in `Spec B`, `Spec D`, and `Spec C` is a pullback. No surjectivity assumption is needed. -/
theorem isPullback_spec_pullback_sections
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
        (by exact overlap_le p q U)) := by
  have h : IsPullback ((p.leftMap q).hom.app (Opposite.op U))
      ((p.rightMap q).hom.app (Opposite.op U))
      ((p.leftOverlapMap q).hom.app (Opposite.op U))
      ((p.rightOverlapMap q).hom.app (Opposite.op U)) :=
    ((isPullback_sheafSquare p q).map (TopCat.Sheaf.forget CommRingCat _)).app (Opposite.op U)
  rw [leftMap_app, rightMap_app, leftOverlapMap_app, rightOverlapMap_app] at h
  exact h

end RingHom
