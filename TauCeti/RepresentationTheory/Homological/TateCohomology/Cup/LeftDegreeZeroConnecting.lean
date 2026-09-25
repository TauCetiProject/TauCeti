/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.ZeroLeft

/-!
# Connecting maps and the left degree-zero Tate cup product

Cup product with a degree-zero class in the first factor commutes with the connecting map of a
short exact sequence in the second factor. The result supplies the compatibility needed to
construct cup products in further bidegrees by dimension shifting.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Cup product with a degree-zero class in the first factor commutes with the connecting map
in the second factor, provided tensoring the short exact sequence with that first factor
preserves exactness. This is the left-factor/braided analogue of `δ_cupH0`. -/
theorem δ_cup0H (M : Rep k G) {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (hMS : (S.map (tensorLeft M)).ShortExact) (n : ℤ)
    (x : tateCohomology M 0) (y : tateCohomology S.X₃ n) :
    _root_.TateCohomology.δ hMS n (cup0H M S.X₃ n x y) =
      cup0H M S.X₁ (n + 1) x (_root_.TateCohomology.δ hS n y) := by
  induction x using H0_induction_on with
  | h x =>
    let F : S ⟶ S.map (tensorLeft M) :=
      { τ₁ := Rep.tensorInvariant S.X₁ x ≫ (β_ S.X₁ M).hom
        τ₂ := Rep.tensorInvariant S.X₂ x ≫ (β_ S.X₂ M).hom
        τ₃ := Rep.tensorInvariant S.X₃ x ≫ (β_ S.X₃ M).hom
        comm₁₂ := by
          dsimp
          rw [Category.assoc, ← BraidedCategory.braiding_naturality_left S.f M,
            ← Category.assoc, ← Rep.hom_comp_tensorInvariant, Category.assoc]
        comm₂₃ := by
          dsimp
          rw [Category.assoc, ← BraidedCategory.braiding_naturality_left S.g M,
            ← Category.assoc, ← Rep.hom_comp_tensorInvariant, Category.assoc] }
    rw [cup0H_H0π, cup0H_H0π, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
    exact congrArg (fun φ ↦ φ y) (_root_.TateCohomology.δ_naturality hS hMS F n).symm

end TauCeti.TateCohomology
