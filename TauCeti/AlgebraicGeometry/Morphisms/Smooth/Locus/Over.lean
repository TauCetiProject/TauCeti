/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
public import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Base change of smooth-locus projections

`Scheme.Hom.isIso_pullback_map_smoothLocus` identifies the projection from the smooth locus
of a composite over an open where the first map is an isomorphism and the second is smooth.
It uses the smooth-locus criterion and `Over.Hom.isIso_pullback_map_iff_of_isOpenImmersion`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The projection from the smooth locus of `p ≫ f` to the source of `f` over `S` is an
isomorphism after base change to an open where `p` is an isomorphism and `f` is smooth. -/
theorem isIso_pullback_map_smoothLocus {η Y X S : Scheme} (p : Y ⟶ X) {f : X ⟶ S}
    [LocallyOfFinitePresentation (p ≫ f)] (j : η ⟶ S) [IsOpenImmersion j]
    (hf : Smooth (f ∣_ j.opensRange)) (hp : IsIso (p ∣_ f ⁻¹ᵁ j.opensRange)) :
    IsIso ((Over.pullback j).map
      (Over.homMk ((p ≫ f).smoothLocus.ι ≫ p) (Category.assoc _ _ _) :
        Over.mk ((p ≫ f).smoothLocus.ι ≫ p ≫ f) ⟶ Over.mk f)) := by
  have hres : Smooth ((p ≫ f) ∣_ j.opensRange) := by
    rw [morphismRestrict_comp]
    exact inferInstanceAs (Smooth ((p ∣_ f ⁻¹ᵁ j.opensRange) ≫ (f ∣_ j.opensRange)))
  have hU : p ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange) ≤ (p ≫ f).smoothLocus := by
    rw [← Scheme.Hom.comp_preimage, ← (p ≫ f).smooth_ι_comp_iff_le_smoothLocus,
      ← morphismRestrict_ι]
    infer_instance
  have hleft : (Over.homMk ((p ≫ f).smoothLocus.ι ≫ p) (Category.assoc _ _ _) :
      Over.mk ((p ≫ f).smoothLocus.ι ≫ p ≫ f) ⟶ Over.mk f).left =
        (p ≫ f).smoothLocus.ι ≫ p := Over.homMk_left _ _
  rw [Over.Hom.isIso_pullback_map_iff_of_isOpenImmersion, hleft]
  simp only [Over.mk_hom, morphismRestrict_comp]
  have hi : IsIso ((p ≫ f).smoothLocus.ι ∣_ p ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange)) :=
    (p ≫ f).smoothLocus.ι.isIso_morphismRestrict_of_le_opensRange
      (by rwa [Scheme.Opens.opensRange_ι])
  exact IsIso.comp_isIso' hi hp

end AlgebraicGeometry.Scheme.Hom
