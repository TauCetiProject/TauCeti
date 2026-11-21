/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import TauCeti.RingTheory.FiberProduct.Localization

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.Functors

/-!
# Sections of the affine Ferrand square

The structure sheaf of the spectrum of a fiber product is the fiber product of the
pushed-forward structure sheaves. This needs neither surjectivity nor finiteness: the
principal-open calculation is localization of a ring pullback.

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

private theorem spec_appLE_algebraMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (U : (Spec R).Opens) (V : (Spec S).Opens) (e : V ≤ Spec.map f ⁻¹ᵁ U) (x : R) :
    (Spec.map f).appLE U V e (algebraMap R Γ(Spec R, U) x) =
      algebraMap S Γ(Spec S, V) (f x) := by
  have h : CommRingCat.ofHom (algebraMap R Γ(Spec R, U)) ≫ (Spec.map f).appLE U V e =
      f ≫ CommRingCat.ofHom (algebraMap S Γ(Spec S, V)) := by
    simp only [IsAffineOpen.algebraMap_Spec_obj, CommRingCat.ofHom_hom,
      Category.assoc, Scheme.Hom.map_appLE]
    dsimp [Scheme.Hom.appLE]
    exact (Scheme.ΓSpecIso_inv_naturality_assoc f _).symm
  exact ConcreteCategory.congr_hom h x

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
          change PrimeSpectrum.basicOpen (p (p.pullbackFst q r)) ≤
            PrimeSpectrum.basicOpen (q (p.pullbackSnd q r))
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
  refine CommRingCat.isPullback_of_away h r ?_ ?_ ?_ ?_ <;>
    exact spec_appLE_algebraMap _ _ _ _

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

private theorem overlap_le (U : (Spec (CommRingCat.of (p.pullback q))).Opens) :
    Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U) ≤
    Spec.map (CommRingCat.ofHom q) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U) := by
  exact le_of_eq (congrArg (fun f : Spec (CommRingCat.of C) ⟶
    Spec (CommRingCat.of (p.pullback q)) ↦ f ⁻¹ᵁ U) (spec_pullback_comm p q))

private def rightOverlapMap :
    (TopCat.Sheaf.pushforward _
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).obj
        (Spec (CommRingCat.of D)).sheaf ⟶ overlapSheaf p q :=
  ⟨{ app := fun U ↦ (Spec.map (CommRingCat.ofHom q)).appLE
        (Spec.map (CommRingCat.ofHom (p.pullbackSnd q)) ⁻¹ᵁ U.unop)
        (Spec.map (CommRingCat.ofHom p) ⁻¹ᵁ
          (Spec.map (CommRingCat.ofHom (p.pullbackFst q)) ⁻¹ᵁ U.unop))
        (p.overlap_le q U.unop)
     naturality := fun U V i ↦ by
       change (Spec (CommRingCat.of D)).presheaf.map _ ≫ _ =
         _ ≫ (Spec (CommRingCat.of C)).presheaf.map _
       rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
       rfl }⟩

/-- On every open of the affine fiber product, its structure-sheaf sections are the
pullback of the actual section rings of the three other affine schemes. -/
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
  let F := (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).obj (Spec (CommRingCat.of B)).sheaf
  let G := (TopCat.Sheaf.pushforward _
    (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).base).obj (Spec (CommRingCat.of D)).sheaf
  let f : (Spec (CommRingCat.of (p.pullback q))).sheaf ⟶ F :=
    ⟨(Spec.map (CommRingCat.ofHom (p.pullbackFst q))).c⟩
  let g : (Spec (CommRingCat.of (p.pullback q))).sheaf ⟶ G :=
    ⟨(Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).c⟩
  let l : F ⟶ p.overlapSheaf q :=
    (TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).base).map
      (show (Spec (CommRingCat.of B)).sheaf ⟶
        (TopCat.Sheaf.pushforward _ (Spec.map (CommRingCat.ofHom p)).base).obj
          (Spec (CommRingCat.of C)).sheaf from ⟨(Spec.map (CommRingCat.ofHom p)).c⟩)
  let r := p.rightOverlapMap q
  have hw : f ≫ l = g ≫ r := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext ?_)
    funext V
    change (Spec.map (CommRingCat.ofHom (p.pullbackFst q))).app V.unop ≫
      (Spec.map (CommRingCat.ofHom p)).app _ =
      (Spec.map (CommRingCat.ofHom (p.pullbackSnd q))).app _ ≫
        (Spec.map (CommRingCat.ofHom q)).appLE _ _ _
    simpa only [Scheme.Hom.comp_app, Scheme.Hom.appLE, Category.assoc] using!
      Scheme.Hom.congr_app (spec_pullback_comm p q) V.unop
  let t := pullback.lift f g hw
  have ht : IsIso t := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    intro x
    let E := TopCat.Sheaf.forget CommRingCat (Spec (CommRingCat.of (p.pullback q))) ⋙
      (evaluation (Opens (Spec (CommRingCat.of (p.pullback q))))ᵒᵖ CommRingCat).obj
        (Opposite.op (PrimeSpectrum.basicOpen x))
    have h₁ := ((IsPullback.of_hasPullback l r).map
      (TopCat.Sheaf.forget CommRingCat _)).app (Opposite.op (PrimeSpectrum.basicOpen x))
    have h₂ : IsPullback (E.map f) (E.map g) (E.map l) (E.map r) :=
      p.isPullback_spec_pullback_basicOpen q x
    let e := h₂.isoIsPullback _ _ h₁
    have he : E.map t = e.hom := by
      apply h₁.hom_ext
      · change E.map t ≫ E.map (pullback.fst l r) = e.hom ≫ _
        rw [← E.map_comp, pullback.lift_fst]
        exact (IsPullback.isoIsPullback_hom_fst _ _ h₂ h₁).symm
      · change E.map t ≫ E.map (pullback.snd l r) = e.hom ≫ _
        rw [← E.map_comp, pullback.lift_snd]
        exact (IsPullback.isoIsPullback_hom_snd _ _ h₂ h₁).symm
    change IsIso (E.map t)
    rw [he]
    exact e.isIso_hom
  have hs : IsPullback f g l r :=
    .of_iso_pullback ⟨hw⟩ (asIso t) (by simp [t]) (by simp [t])
  exact (hs.map (TopCat.Sheaf.forget CommRingCat _)).app (Opposite.op U)

end RingHom
