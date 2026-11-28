/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Over
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Scheme-theoretic images of group scheme homomorphisms

The scheme-theoretic image of a quasi-compact homomorphism of group schemes over `S` is a
closed subgroup scheme when the source and image are flat over `S`. In particular, the
flatness hypotheses hold over a field. The source-to-image map is a homomorphism, and the
underlying scheme factorization is Mathlib's `Scheme.Hom.toImage` followed by `Scheme.Hom.imageι`.

Flat base change preserves schematic dominance of the source-to-image map. Consequently its
fibre square over `S` is schematically dominant, allowing multiplication to descend to the
image through `TauCeti.GroupScheme.grpObjOfClosedImmersion`.

## References

* The Stacks Project, Lemma 33.24.3 (Tag 04Q1), for products of scheme-theoretic images over fields.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Over.Hom

universe u

variable {S : Scheme.{u}} {G H : Over S}

private lemma isSchemeTheoreticallyDominant_tensorHom_toImageOver (f : G ⟶ H)
    [QuasiCompact f.left] [Flat G.hom] [Flat f.imageOver.hom] :
    IsSchemeTheoreticallyDominant (f.toImageOver ⊗ₘ f.toImageOver).left := by
  let I := f.imageOver
  let p := f.toImageOver
  have : IsSchemeTheoreticallyDominant p.left := inferInstanceAs
    (IsSchemeTheoreticallyDominant f.toImageOver.left)
  have : QuasiCompact p.left := inferInstanceAs (QuasiCompact f.toImageOver.left)
  -- The two whiskerings are base changes along the corresponding projections.
  have hR : IsPullback (pullback.fst G.hom G.hom) (p ▷ G).left p.left
      (pullback.fst I.hom G.hom) := by
    refine IsPullback.of_bot ?_ (by simp only [I, Over.whiskerRight_left_fst])
      (.of_hasPullback _ _)
    simpa only [I, Over.whiskerRight_left_snd, Over.w] using
      IsPullback.of_hasPullback G.hom G.hom
  have hL : IsPullback (pullback.snd I.hom G.hom) (I ◁ p).left p.left
      (pullback.snd I.hom I.hom) := by
    refine IsPullback.of_bot ?_ (by simp only [I, Over.whiskerLeft_left_snd])
      (.flip <| .of_hasPullback _ _)
    simpa only [I, Over.whiskerLeft_left_fst, Over.w] using
      (IsPullback.of_hasPullback I.hom G.hom).flip
  have := IsSchemeTheoreticallyDominant.of_isPullback hR
  have := IsSchemeTheoreticallyDominant.of_isPullback hL
  rw [tensorHom_def, Over.comp_left]
  exact inferInstanceAs (IsSchemeTheoreticallyDominant ((p ▷ G).left ≫ (I ◁ p).left))

variable [GrpObj G] [GrpObj H]

private lemma imageιOver_ker_le_one (f : G ⟶ H) [IsMonHom f] :
    f.imageιOver.left.ker ≤ η[H].left.ker := by
  simpa only [imageιOver_left, Scheme.IdealSheafData.ker_subschemeι, ← IsMonHom.one_hom f,
    Over.comp_left] using η[G].left.le_ker_comp f.left

private lemma imageιOver_ker_le_mul (f : G ⟶ H) [IsMonHom f]
    [QuasiCompact f.left] [Flat G.hom] [Flat f.imageOver.hom] :
    f.imageιOver.left.ker ≤ ((f.imageιOver ⊗ₘ f.imageιOver) ≫ μ[H]).left.ker := by
  have := isSchemeTheoreticallyDominant_tensorHom_toImageOver f
  have h : (f.toImageOver ⊗ₘ f.toImageOver) ≫ (f.imageιOver ⊗ₘ f.imageιOver) ≫ μ[H] =
      μ[G] ≫ f := by
    simp only [← Category.assoc, tensorHom_comp_tensorHom, toImageOver_imageιOver,
      IsMonHom.mul_hom]
  have hker := congrArg (fun g : G ⊗ G ⟶ H ↦ g.left.ker) h
  simp only [Over.comp_left, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant] at hker
  simpa only [imageιOver_left, Scheme.IdealSheafData.ker_subschemeι, Over.comp_left, hker] using
    μ[G].left.le_ker_comp f.left

private lemma imageιOver_ker_le_inv (f : G ⟶ H) [IsMonHom f] [QuasiCompact f.left] :
    f.imageιOver.left.ker ≤ (f.imageιOver ≫ ι[H]).left.ker := by
  have h : f.toImageOver ≫ f.imageιOver ≫ ι[H] = ι[G] ≫ f := by
    rw [toImageOver_imageιOver_assoc, GrpObj.inv_hom]
  have hker := congrArg (fun g : G ⟶ H ↦ g.left.ker) h
  simp only [Over.comp_left, imageιOver_left,
    Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant] at hker
  simpa only [imageιOver_left, Scheme.IdealSheafData.ker_subschemeι, Over.comp_left, hker] using
    ι[G].left.le_ker_comp f.left

variable (f : G ⟶ H) [IsMonHom f] [QuasiCompact f.left] [Flat G.hom] [Flat f.imageOver.hom]

/-- The scheme-theoretic image of a quasi-compact homomorphism carries the induced group
structure if the source and image are flat over the base. -/
@[no_expose]
noncomputable instance grpObjImageOver : GrpObj f.imageOver := by
  exact TauCeti.GroupScheme.grpObjOfClosedImmersion f.imageιOver (imageιOver_ker_le_one f)
    (imageιOver_ker_le_mul f) (imageιOver_ker_le_inv f)

/-- The closed immersion from the scheme-theoretic image into the target preserves the
group operations. -/
instance isMonHom_imageιOver : IsMonHom f.imageιOver := by
  exact TauCeti.GroupScheme.isMonHom_grpObjOfClosedImmersion f.imageιOver (imageιOver_ker_le_one f)
    (imageιOver_ker_le_mul f) (imageιOver_ker_le_inv f)

/-- The canonical map to the scheme-theoretic image preserves the group operations. -/
instance isMonHom_toImageOver : IsMonHom f.toImageOver := by
  have : Mono f.imageιOver := Over.mono_of_mono_left f.imageιOver
  refine ⟨(cancel_mono f.imageιOver).mp (by simp), (cancel_mono f.imageιOver).mp ?_⟩
  simp only [Category.assoc, toImageOver_imageιOver, IsMonHom.mul_hom]
  rw [← Category.assoc, tensorHom_comp_tensorHom, toImageOver_imageιOver]

end CategoryTheory.Over.Hom
