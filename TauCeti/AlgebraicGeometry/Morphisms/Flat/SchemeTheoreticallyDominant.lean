/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic

/-!
# Flat surjective morphisms are scheme-theoretically dominant

A flat surjective morphism is scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_flat_of_surjective`), and so are all its base
changes (`AlgebraicGeometry.IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective`). The
proof is stalkwise: a flat local homomorphism of stalks is faithfully flat, and extension of ideals
along a faithfully flat ring map is injective.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **A flat surjective morphism is scheme-theoretically dominant**: its scheme-theoretic image is
the whole target. -/
instance IsSchemeTheoreticallyDominant.of_flat_of_surjective (f : X ⟶ Y) [Flat f]
    [Surjective f] : IsSchemeTheoreticallyDominant f where
  ker_eq_bot := by
    -- `f.ker` and `⊥` have the same inverse image along `f`, and at each point the extension of
    -- stalk ideals along the faithfully flat stalk map of `f` is injective.
    refine le_bot_iff.mp (Scheme.IdealSheafData.le_iff_forall_stalkIdeal_le.mpr fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := f.surjective x
    let _ := (f.stalkMap y).hom.toAlgebra
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f y)) (X.presheaf.stalk y) :=
      f.faithfullyFlat_stalkMap y (Flat.stalkMap f y)
    have hy := congr(Scheme.IdealSheafData.stalkIdeal
      $(f.comap_ker_self.trans (Scheme.IdealSheafData.comap_bot f).symm) y)
    rw [Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap] at hy
    exact (Ideal.map_injective_of_faithfullyFlat (B := X.presheaf.stalk y) hy).le

/-- **Flat surjective morphisms are universally scheme-theoretically dominant**, since flatness and
surjectivity are stable under base change. -/
theorem IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective (f : X ⟶ Y) [Flat f]
    [Surjective f] : MorphismProperty.universally @IsSchemeTheoreticallyDominant f :=
  fun _ _ _ _ f' (h : IsPullback f' _ _ f) ↦
    have : Flat f' := MorphismProperty.of_isPullback h.flip ‹_›
    have : Surjective f' := MorphismProperty.of_isPullback h.flip ‹_›
    inferInstance

end AlgebraicGeometry
