/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Quotient
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product

/-!
# Trivial solvable radicals of direct products

If two finite-type affine groups have trivial solvable radical, so does their direct product.
The groups themselves need not be smooth or connected. A connected normal smooth solvable
subgroup of the product has such an image in each factor, so both projection images are
trivial. The tensor-product universal property then makes the subgroup itself trivial.

This is the radical calculation used to assemble semisimple groups from their factors.
It uses `HopfIdeal.IsSolvableRadicalCandidate.comap_of_injective` for the projection images
and retains the scheme-theoretic subgroup throughout.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 21.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The direct product of two finite-type affine groups with trivial solvable radical has
trivial solvable radical. No smoothness or connectedness of the ambient groups is required. -/
theorem solvableRadicalDefiningIdeal_tensorProduct_eq_augmentation
    (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : solvableRadicalDefiningIdeal H = HopfIdeal.augmentation k H)
    (hK : solvableRadicalDefiningIdeal K = HopfIdeal.augmentation k K) :
    solvableRadicalDefiningIdeal (tensorProduct H K) =
      HopfIdeal.augmentation k (tensorProduct H K) := by
  rw [solvableRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  -- Project the candidate subgroup to each factor and use triviality of their radicals.
  have hIH : I.comap (toBialgHom (includeLeft H K)) = HopfIdeal.augmentation k H :=
    (solvableRadicalDefiningIdeal_eq_augmentation_iff H).mp hH _
      (hI.comap_of_injective (includeLeft H K).hom (includeLeft_injective H K))
  have hIK : I.comap (toBialgHom (includeRight H K)) = HopfIdeal.augmentation k K :=
    (solvableRadicalDefiningIdeal_eq_augmentation_iff K).mp hK _
      (hI.comap_of_injective (includeRight H K).hom (includeRight_injective H K))
  exact I.eq_augmentation_of_comap_includeLeft_of_comap_includeRight hIH hIK

end TauCeti.FiniteTypeCommHopfAlgCat
