/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Augmentation.Basic
import TauCeti.RepresentationTheory.OfMulAction

/-!
# Permutation representations in modular characteristic are not semisimple

If a group `G` acts transitively on a finite nonempty set `X` whose cardinality is zero in the
field `k`, the permutation representation `k[X]` is not semisimple
(`Representation.not_isSemisimpleRepresentation_ofMulAction`). An invariant complement `C` of the
augmentation subrepresentation consists of invariant vectors, so by transitivity it lies in the
invariant line spanned by `∑_x x`. The augmentation of `∑_x x` is the cardinality of `X`, which is
zero, so `C` lies in the augmentation subrepresentation too. Then the augmentation
subrepresentation is everything, which it is not.

In particular, if the order of a finite group `G` is zero in `k`, the left regular representation
of `G` over `k` is not semisimple (`Representation.not_isSemisimpleRepresentation_leftRegular`).
This is the converse direction of Maschke's theorem for the regular representation, and the reason
`TauCeti.isCompl_invariantLine_augmentationSubrepresentation_iff` needs `|G|` to be a unit.
-/

public section

namespace Representation

open TauCeti

variable {k G : Type*} [Field k] [Group G]

/-- **Transitive permutation representations in modular characteristic are not semisimple.** If
`G` acts transitively on a finite nonempty set `X` whose cardinality is zero in `k`, the
permutation representation `k[X]` is not semisimple. -/
theorem not_isSemisimpleRepresentation_ofMulAction {X : Type*} [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite X] [Nonempty X] (hX : (Nat.card X : k) = 0) :
    ¬ (ofMulAction k G X).IsSemisimpleRepresentation := by
  intro
  have := Fintype.ofFinite X
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨C, hC⟩ := exists_isCompl (augmentationSubrepresentation k G X)
  -- Every vector of `C` is invariant, so by transitivity it lies on the invariant line.
  have hline : C ≤ invariantLine k G X := fun c hc ↦ by
    have hinv (g : G) : ofMulAction k G X g c = c :=
      Subrepresentation.apply_eq_self_of_disjoint hC.disjoint hc (by
        rw [mem_augmentationSubrepresentation_iff, map_sub, sumCoords_basis_ofMulAction, sub_self])
    refine mem_invariantLine_iff.2 ⟨c.coeff x₀, ?_⟩
    ext x
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ x
    simpa [coeff_permutationSum] using (coeff_smul_of_forall_ofMulAction_eq hinv g x₀).symm
  -- The augmentation of `∑_x x` is `|X| = 0`, so the invariant line lies in the augmentation.
  have haug : invariantLine k G X ≤ augmentationSubrepresentation k G X := fun v hv ↦ by
    obtain ⟨a, rfl⟩ := mem_invariantLine_iff.1 hv
    simp [← Nat.card_eq_fintype_card, hX]
  have htop : augmentationSubrepresentation k G X = ⊤ := by
    rw [← sup_eq_left.2 (hline.trans haug)]
    exact codisjoint_iff.1 hC.codisjoint
  have h1 : MonoidAlgebra.single x₀ (1 : k) ∈ augmentationSubrepresentation k G X :=
    htop ▸ Subrepresentation.mem_top
  simp at h1

/-- **The regular representation in modular characteristic is not semisimple.** If the order of
a finite group `G` is zero in `k`, the left regular representation of `G` over `k` is not
semisimple. -/
theorem not_isSemisimpleRepresentation_leftRegular [Finite G] (hG : (Nat.card G : k) = 0) :
    ¬ (leftRegular k G).IsSemisimpleRepresentation :=
  not_isSemisimpleRepresentation_ofMulAction hG

end Representation
