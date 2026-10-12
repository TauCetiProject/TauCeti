/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.Augmentation
public import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup

/-!
# The augmentation connecting map in first group homology

The connecting map of the augmentation sequence sends the first-homology class of `g ⊗ a`
to the coinvariant class of `[g⁻¹] a - [1] a`. The same formula holds after restricting the
sequence to a subgroup. These formulas identify the connecting-map images of the classes
`g ⊗ a` in `H₀(G, I_G)` and `H₀(S, I_G)`, which is how the transfer on first homology is compared
with the group-theoretic transfer (Verlagerung) in
`TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Abelianization`.

## Main results

* `TauCeti.groupHomology.δ_mkH1OfIsTrivial`: the formula for the original sequence.
* `TauCeti.groupHomology.δ_res_mkH1OfIsTrivial`: the formula for the restricted sequence.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

universe u

open CategoryTheory Rep Finsupp

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G]

-- `δ₀_apply` needs the explicit endpoints of the augmentation sequence for elaboration.
private theorem shortExact_aug (k G : Type u) [CommRing k] [Group G] :
    (ShortComplex.mk (augmentationι k G) (augmentation k G)
      (augmentationι_comp_augmentation k G)).ShortExact :=
  augmentationSES_def k G ▸ augmentationSES_shortExact k G

/-- The augmentation connecting map sends `g ⊗ a` to the class of `[g⁻¹] a - [1] a`. -/
theorem δ_mkH1OfIsTrivial (g : G) (a : k) :
    δ (augmentationSES_def k G ▸ augmentationSES_shortExact k G) 1 0 rfl
        (mkH1OfIsTrivial (trivial k G k) (Additive.ofMul (Abelianization.of g)) a) =
      H0π (augmentationIdeal k G) (TauCeti.AugmentationIdeal.singleSub k G a g⁻¹) := by
  rw [mkH1OfIsTrivial_apply]
  exact δ₀_apply (shortExact_aug k G) _
    (single g (MonoidAlgebra.single 1 a))
    (by rw [cycles₁IsoOfIsTrivial_inv_apply]; simp)
    (TauCeti.AugmentationIdeal.singleSub k G a g⁻¹)
    (by rw [TauCeti.AugmentationIdeal.ι_singleSub, d₁₀_single]; simp)

/-- The restricted augmentation connecting map sends `s ⊗ a` to the class of
`[s⁻¹] a - [1] a`. The short exactness witness may be transported from
`Rep.augmentationSES_shortExact` through `Rep.augmentationSES_def`. -/
theorem δ_res_mkH1OfIsTrivial (S : Subgroup G)
    (hAug : (ShortComplex.mk (augmentationι k G) (augmentation k G)
      (augmentationι_comp_augmentation k G)).ShortExact) (s : S) (a : k) :
    δ ((shortExact_res S.subtype).2 hAug) 1 0 rfl
        (mkH1OfIsTrivial (res S.subtype (trivial k G k))
          (Additive.ofMul (Abelianization.of s)) a) =
      H0π (res S.subtype (augmentationIdeal k G))
        (TauCeti.AugmentationIdeal.singleSub k G a (s⁻¹ : S)) := by
  rw [mkH1OfIsTrivial_apply]
  exact δ₀_apply ((shortExact_res S.subtype).2 hAug) _
    (single s (MonoidAlgebra.single 1 a))
    (by rw [cycles₁IsoOfIsTrivial_inv_apply]; simp) _
    (by rw [d₁₀_single]; exact
      (TauCeti.AugmentationIdeal.ι_singleSub k G a _).trans (by simp))

end TauCeti.groupHomology
