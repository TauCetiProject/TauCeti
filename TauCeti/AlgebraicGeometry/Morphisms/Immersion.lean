/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Factoring through immersions after a schematic cover

A morphism factors through an immersion if it does so after precomposition with a
surjective, scheme-theoretically dominant morphism. Surjectivity detects containment in
the open part of the immersion; schematic dominance detects the equations of its closed
part. No flatness or reducedness is required.

This allows equivariant morphisms to restrict to locally closed scheme-theoretic images,
including images with nonreduced scheme structure.

The construction uses Mathlib's `Scheme.Hom.liftCoborder`, `IsOpenImmersion.lift`,
`IsClosedImmersion.lift`, and the ideal-sheaf formula `Scheme.Hom.ker_comp`.
-/

public section

open CategoryTheory

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
      _ = gU.ker := by rw [ker_comp, p.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  let l := IsClosedImmersion.lift i.liftCoborder gU hker
  have hl : l ≫ i = g := by
    calc
      l ≫ i = l ≫ i.liftCoborder ≫ i.coborderRange.ι := by rw [i.liftCoborder_ι]
      _ = gU ≫ i.coborderRange.ι := by rw [← Category.assoc, IsClosedImmersion.lift_fac]
      _ = g := hgU
  exact ⟨l, hl, fun l' hl' ↦ (cancel_mono i).mp (hl'.trans hl.symm)⟩

end AlgebraicGeometry.Scheme.Hom
