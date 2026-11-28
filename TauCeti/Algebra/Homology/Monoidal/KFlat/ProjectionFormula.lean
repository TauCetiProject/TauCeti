/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Tensor.ProjectionFormula
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic
import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Preservation of K-flatness from a projection formula

Let `G : C ⥤ D` preserve zero morphisms and let `L : D ⥤ C` be faithful, exact and additive
between abelian monoidal categories with biadditive tensors. Assume both categories admit
total tensor products for every pair of integer cochain complexes.
If `L (G X ⊗ Y) ≅ X ⊗ L Y` naturally and `L` preserves the diagonal coproducts, then
applying `G` degreewise preserves K-flat complexes.

Exactness is expressed by `L.PreservesHomology`; preservation of finite limits and finite
colimits by the additive functor `L` supplies this instance. A splitting `L ⋙ G ≅ 𝟭 D`
supplies faithfulness of `L`. Thus restriction with exact extension by zero is an application
once its projection formula and diagonal-coproduct preservation are established; neither an
adjunction nor a monoidal structure on either functor is needed.

## References

* Stacks Project, Lemma 21.17.4 (Tag 0E8K), using the projection formula of
  Lemma 18.27.9 (Tag 0E8I).
-/

public section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ K E : CochainComplex C ℤ, HasTensor K E]
  [∀ K E : CochainComplex D ℤ, HasTensor K E]

/-- A zero-morphism-preserving functor preserves K-flat cochain complexes if it admits a
projection formula with a faithful additive functor `L` preserving homology and the diagonal
coproducts. Both abelian categories must have biadditive tensors and total tensors for every
pair of integer cochain complexes. Only `L` needs to preserve homology. -/
theorem isKFlat_mapHomologicalComplex_obj_of_projectionFormula
    (G : C ⥤ D) (L : D ⥤ C) [G.PreservesZeroMorphisms] [L.Additive]
    [L.PreservesHomology] [L.Faithful]
    (e : G.prod (𝟭 D) ⋙ tensor D ⋙ L ≅ (𝟭 C).prod L ⋙ tensor C)
    (K : CochainComplex C ℤ) [K.IsKFlat]
    [∀ (E : CochainComplex D ℤ) (n : ℤ), PreservesColimit (Discrete.functor
      (fun pq : { pq : ℤ × ℤ // pq.1 + pq.2 = n } ↦
        G.obj (K.X pq.val.1) ⊗ E.X pq.val.2)) L] :
    CochainComplex.IsKFlat ((G.mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [CochainComplex.isKFlat_iff]
  intro E hE
  have hLE : ((L.mapHomologicalComplex (.up ℤ)).obj E).Acyclic := fun n ↦
    (L.mapHomologicalComplex_obj_exactAt_iff E n).2 ((hE n).map L)
  have hT := CochainComplex.IsKFlat.acyclic_tensor (K := K) _ hLE
  have hLT : ((L.mapHomologicalComplex (.up ℤ)).obj
      (tensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E)).Acyclic := fun n ↦
    ExactAt.of_iso (hT n) (L.projectionFormulaHomologicalComplexIso G e K E).symm
  exact fun n ↦ ((tensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) E).sc n
    |>.exact_map_iff_of_faithful L).1
      ((L.mapHomologicalComplex_obj_exactAt_iff _ n).1 (hLT n))

end CategoryTheory.Functor
