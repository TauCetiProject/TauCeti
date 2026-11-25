/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Augmentation.Basic
public import TauCeti.RepresentationTheory.Semisimple.NonSemisimple

/-!
# The regular representation in modular characteristic is not semisimple

If the order of a finite group `G` is zero in the field `k`, the left regular representation of
`G` over `k` is not semisimple (`Representation.not_isSemisimpleRepresentation_leftRegular`). An
invariant complement `C` of the augmentation subrepresentation consists of invariant vectors, so it
lies in the invariant line spanned by `∑_g g`. The augmentation of `∑_g g` is the order of `G`,
which is zero, so `C` lies in the augmentation subrepresentation too. Then the augmentation
subrepresentation is everything, which it is not. This is the converse direction of Maschke's
theorem for the regular representation, and the reason
`TauCeti.isCompl_invariantLine_augmentationSubrepresentation_iff` needs `|G|` to be a unit.
-/

public section

namespace Representation

open TauCeti

variable {k G : Type*} [Field k] [Group G]

/-- **The regular representation in modular characteristic is not semisimple.** If the order of
a finite group `G` is zero in `k`, the left regular representation of `G` over `k` is not
semisimple. -/
theorem not_isSemisimpleRepresentation_leftRegular [Finite G] (hG : (Nat.card G : k) = 0) :
    ¬ (leftRegular k G).IsSemisimpleRepresentation := by
  intro
  have := Fintype.ofFinite G
  obtain ⟨C, hC⟩ := exists_isCompl (augmentationSubrepresentation k G G)
  -- Every vector of `C` is invariant, so `C` lies on the invariant line.
  have hline : C ≤ invariantLine k G G := fun c hc ↦ by
    have hinv (g : G) : leftRegular k G g c = c :=
      Subrepresentation.apply_eq_self_of_disjoint hC.disjoint hc (by
        rw [mem_augmentationSubrepresentation_iff, map_sub, sumCoords_basis_ofMulAction, sub_self])
    refine mem_invariantLine_iff.2 ⟨c.coeff 1, ?_⟩
    ext x
    simpa [coeff_permutationSum, coeff_ofMulAction] using
      (congrArg (fun y : MonoidAlgebra k G ↦ y.coeff 1) (hinv x⁻¹)).symm
  -- The augmentation of `∑_g g` is `|G| = 0`, so the invariant line lies in the augmentation.
  have haug : invariantLine k G G ≤ augmentationSubrepresentation k G G := fun v hv ↦ by
    obtain ⟨a, rfl⟩ := mem_invariantLine_iff.1 hv
    simp [← Nat.card_eq_fintype_card, hG]
  have hle := hline.trans haug
  have h1 : MonoidAlgebra.single (1 : G) (1 : k) ∈ augmentationSubrepresentation k G G :=
    (sup_eq_left.2 hle ▸ codisjoint_iff.1 hC.codisjoint) ▸ Subrepresentation.mem_top
  simp at h1

end Representation
