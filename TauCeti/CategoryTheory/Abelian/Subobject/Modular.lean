/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.ModularLattice
public import TauCeti.CategoryTheory.Abelian.ImageSubobject

/-!
# The subobject lattice of an object of an abelian category is modular

For subobjects `A ≤ K` and `B` of an object of an abelian category, `(A ⊔ B) ⊓ K ≤ A ⊔ (B ⊓ K)`:
the lattice of subobjects is modular. This is the lattice-theoretic input to the theory of length
of objects: in a modular lattice Krull dimension is additive on intervals
(`Order.krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc`).

## Main results

* `CategoryTheory.Subobject.isModularLattice`: the subobjects of an object of an abelian
  category form a modular lattice.

## Implementation notes

The modular law is proved by element chasing up to refinements
(`Mathlib.CategoryTheory.Abelian.Refinements`). A morphism factoring through `A ⊔ B`, which is the
image of `A ⨿ B ⟶ X` (`CategoryTheory.Subobject.sup_eq_imageSubobject`), is, after precomposition
with an epimorphism, a sum `a + b` of morphisms factoring through `A` and `B`. If it also factors
through `K ≥ A`, then so does `b`, and the sum factors through `A ⊔ (B ⊓ K)`. The epimorphism is
removed by `CategoryTheory.Subobject.factors_epi_comp_iff`.

## References

* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer (1998), Chapter VIII,
  for element chasing in abelian categories.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- **The subobjects of an object of an abelian category form a modular lattice.** -/
instance isModularLattice : IsModularLattice (Subobject X) where
  sup_inf_le_assoc_of_le {A} B {K} hAK := by
    refine le_of_factors ?_
    have hK : K.Factors ((A ⊔ B) ⊓ K).arrow := inf_arrow_factors_right _ _
    obtain ⟨T, π, _, y, hy⟩ := (imageSubobject_factors_iff_up_to_refinements
      (coprod.desc A.arrow B.arrow) ((A ⊔ B) ⊓ K).arrow).1
        (by rw [← sup_eq_imageSubobject]; exact inf_arrow_factors_left _ _)
    -- Up to the refinement `π`, the inclusion is a sum of a part in `A` and a part in `B`.
    have hsplit : π ≫ ((A ⊔ B) ⊓ K).arrow =
        y ≫ coprod.desc A.arrow 0 + y ≫ coprod.desc 0 B.arrow := by
      rw [hy, ← Preadditive.comp_add]
      congr 1
      ext <;> simp
    have hA : A.Factors (y ≫ coprod.desc A.arrow 0) := by
      simpa [coprod.desc_comp] using factors_comp_arrow (P := A) (y ≫ coprod.desc (𝟙 _) 0)
    have hB : B.Factors (y ≫ coprod.desc 0 B.arrow) := by
      simpa [coprod.desc_comp] using factors_comp_arrow (P := B) (y ≫ coprod.desc 0 (𝟙 _))
    -- The part in `B` lies in `K`, since the whole and the part in `A ≤ K` do.
    have hBK : K.Factors (y ≫ coprod.desc 0 B.arrow) := factors_right_of_factors_add _ _
      (hsplit ▸ factors_of_factors_right π hK) (factors_of_le _ hAK hA)
    rw [← factors_epi_comp_iff _ π, hsplit]
    exact factors_add _ _ (sup_factors_of_factors_left hA)
      (sup_factors_of_factors_right ((inf_factors _).2 ⟨hB, hBK⟩))

end CategoryTheory.Subobject
