/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# Factoring through immersions after a schematic cover

A morphism factors through an immersion if it does so after precomposition with a
surjective, scheme-theoretically dominant morphism. Surjectivity detects containment in
the open part of the immersion; schematic dominance detects the equations of its closed
part. No flatness or reducedness is required.

This allows equivariant morphisms to restrict to locally closed scheme-theoretic images,
including images with nonreduced scheme structure.

The file also records that immersions are stable under composition with open immersions
on either side (`AlgebraicGeometry.IsImmersion.respectsLeft_isOpenImmersion`,
`AlgebraicGeometry.IsImmersion.respectsRight_isOpenImmersion`). The second one is the
hypothesis of Mathlib's `AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`, which
checks that a morphism is an immersion over opens covering its range.

The construction uses Mathlib's `Scheme.Hom.liftCoborder`, `IsOpenImmersion.lift`,
`IsClosedImmersion.lift`, and the ideal-sheaf formula `Scheme.Hom.ker_comp`, through
`Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant`.

For a quasi-compact immersion `i`, the ideal sheaf of the closed immersion `i.liftCoborder` into
the open `i.coborderRange` is the restriction of the ideal sheaf `ker i`
(`Scheme.Hom.ker_liftCoborder`).
-/

public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {W X Y Z : Scheme.{u}}

/-- A factorization through an immersion exists uniquely if it exists after a
surjective, scheme-theoretically dominant morphism. -/
theorem existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (i : Z ⟶ Y) [IsImmersion i] (g : X ⟶ Y)
    (p : W ⟶ X) [Surjective p] [IsSchemeTheoreticallyDominant p]
    (a : W ⟶ Z) (h : a ≫ i = p ≫ g) : ∃! l : X ⟶ Z, l ≫ i = g := by
  have hrange : Set.range g ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := p.surjective x
    exact ⟨a w, congrArg (fun f : W ⟶ Y ↦ f w) h⟩
  have hopen : Set.range i ⊆ Set.range i.coborderRange.ι := by
    rw [Scheme.Opens.range_ι]
    exact subset_coborder
  let gU := IsOpenImmersion.lift i.coborderRange.ι g (hrange.trans hopen)
  have hgU : gU ≫ i.coborderRange.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hU : a ≫ i.liftCoborder = p ≫ gU := by
    rw [← cancel_mono i.coborderRange.ι]
    simpa only [Category.assoc, i.liftCoborder_ι, hgU] using h
  have hker : i.liftCoborder.ker ≤ gU.ker := by
    calc
      i.liftCoborder.ker ≤ (a ≫ i.liftCoborder).ker := a.le_ker_comp _
      _ = (p ≫ gU).ker := congrArg Scheme.Hom.ker hU
      _ = gU.ker := p.ker_comp_of_isSchemeTheoreticallyDominant gU
  let l := IsClosedImmersion.lift i.liftCoborder gU hker
  have hl : l ≫ i = g := by
    calc
      l ≫ i = l ≫ i.liftCoborder ≫ i.coborderRange.ι := by rw [i.liftCoborder_ι]
      _ = gU ≫ i.coborderRange.ι := by rw [← Category.assoc, IsClosedImmersion.lift_fac]
      _ = g := hgU
  exact ⟨l, hl, fun l' hl' ↦ (cancel_mono i).mp (hl'.trans hl.symm)⟩

/-- For a quasi-compact immersion `i : Z ⟶ Y`, the ideal sheaf of the closed immersion
`i.liftCoborder` of `Z` into the open `i.coborderRange` is the restriction of `ker i` to that open.
For a closed immersion, `i.coborderRange` is all of `Y`. -/
theorem ker_liftCoborder (i : Z ⟶ Y) [IsImmersion i] [QuasiCompact i] :
    i.liftCoborder.ker = i.ker.comap i.coborderRange.ι := by
  -- `i.liftCoborder` is the base change of the closed immersion `i.imageι` along the open.
  rw [← (IsImmersion.isPullback_toImage_liftCoborder i).flip.isoPullback_hom_fst,
    ker_comp_of_isIso, IdealSheafData.ker_fst_of_isClosedImmersion, imageι,
    IdealSheafData.ker_subschemeι]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- Immersions are stable under precomposition with open immersions. -/
instance IsImmersion.respectsLeft_isOpenImmersion :
    MorphismProperty.RespectsLeft @IsImmersion @IsOpenImmersion where
  precomp _ hi _ hf := by have := hi; have := hf; infer_instance

/-- Immersions are stable under postcomposition with open immersions. -/
instance IsImmersion.respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp _ hi _ hf := by have := hi; have := hf; infer_instance

end AlgebraicGeometry

/-- The inverse image of an affine open along an immersion is affine if that open is contained
in the immersion's coborder. -/
theorem AlgebraicGeometry.IsAffineOpen.preimage_of_isImmersion
    {X Y : AlgebraicGeometry.Scheme} {U : Y.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion f] (hU' : U ≤ f.coborderRange) :
    AlgebraicGeometry.IsAffineOpen (f ⁻¹ᵁ U) := by
  have hA := hU.preimage_of_isOpenImmersion f.coborderRange.ι
    (by simpa only [AlgebraicGeometry.Scheme.Opens.opensRange_ι] using hU')
  rw [← f.liftCoborder_ι, AlgebraicGeometry.Scheme.Hom.comp_preimage]
  exact hA.preimage f.liftCoborder

/-- An immersion transfers a finite affine neighbourhood contained in its coborder from the
 target. The source neighbourhood can be chosen inside a prescribed open. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_isImmersion
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion f]
    {s : Set X} {W : X.Opens} (hs : s.Finite) (hsW : s ⊆ W)
    (hY : ∃ V : Y.Opens, AlgebraicGeometry.IsAffineOpen V ∧
      f '' s ⊆ V ∧ V ≤ f.coborderRange) :
    ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W := by
  obtain ⟨V, hV, hsV, hVc⟩ := hY
  have hpre := hV.preimage_of_isImmersion f hVc
  have hsPre : s ⊆ f ⁻¹ᵁ V := fun x hx ↦ f.mem_preimage.mpr
    (hsV (Set.mem_image_of_mem f hx))
  obtain ⟨r, hsr, hrW⟩ := hpre.exists_basicOpen_superset_le hs hsPre hsW
  exact ⟨X.basicOpen r, hpre.basicOpen r, hsr, hrW⟩
