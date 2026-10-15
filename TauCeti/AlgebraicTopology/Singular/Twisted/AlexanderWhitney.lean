/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialObject.AlexanderWhitney
public import TauCeti.AlgebraicTopology.Singular.Twisted.Tensor

/-!
# The Alexander–Whitney diagonal with local coefficients

The singular chains twisted by a tensor product of local systems map to the tensor product of
their twisted chain complexes. The diagonal sends a simplex to the sum of its front and back
faces. The coefficients in each factor are transported from the initial vertex of the original
simplex to the initial vertex of the corresponding face; in the back factor this is transport
along the edge from vertex zero to the cut vertex.

The construction composes `twistedChainsTensorDiagonal` with
`CategoryTheory.SimplicialObject.alexanderWhitney`, the Alexander–Whitney map of simplicial
objects. It is natural in both local systems and in the
space, with the canonical tensor comparison for pullback. It supplies the diagonal for cup
products of cochains with dual local coefficients. The ring and coefficient fibres share a
universe, as required by the monoidal structure on `ModuleCat`; the space may live in a smaller
universe.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.2 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open scoped Simplicial

universe v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] {X Y : TopCat.{v}}
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R X)

/-- The Alexander–Whitney diagonal of twisted singular chains, from chains with coefficients
in `L ⊗ K` to the tensor product of the chains with coefficients in `L` and in `K`. -/
def twistedAlexanderWhitneyDiagonal :
    (L ⊗ K).twistedChainComplex ⟶ L.twistedChainComplex ⊗ K.twistedChainComplex :=
  (twistedChainComplexIsoAlternatingFaceMapComplex (L ⊗ K)).hom ≫
    (alternatingFaceMapComplex _).map (twistedChainsTensorDiagonal L K) ≫
      SimplicialObject.alexanderWhitney (twistedChains L) (twistedChains K) ≫
        ((twistedChainComplexIsoAlternatingFaceMapComplex L).inv ⊗ₘ
          (twistedChainComplexIsoAlternatingFaceMapComplex K).inv)

/-- The twisted diagonal, expressed in the alternating-face presentations of its factors. -/
@[reassoc]
private lemma twistedAlexanderWhitneyDiagonal_comp_comparison :
    twistedAlexanderWhitneyDiagonal L K ≫
        ((twistedChainComplexIsoAlternatingFaceMapComplex L).hom ⊗ₘ
          (twistedChainComplexIsoAlternatingFaceMapComplex K).hom) =
      (twistedChainComplexIsoAlternatingFaceMapComplex (L ⊗ K)).hom ≫
        (alternatingFaceMapComplex _).map (twistedChainsTensorDiagonal L K) ≫
          SimplicialObject.alexanderWhitney (twistedChains L) (twistedChains K) := by
  simp [twistedAlexanderWhitneyDiagonal]

/-- On a simplex summand, the twisted diagonal is the sum of front and back faces, with the
coefficient transport to each face's initial vertex. -/
@[reassoc]
lemma ιTwistedChainComplex_twistedAlexanderWhitneyDiagonal_f (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChainComplex (L ⊗ K) n σ ≫ (twistedAlexanderWhitneyDiagonal L K).f n =
      ∑ p : Fin (n + 1),
        ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
              ιTwistedChainComplex L p
                ((TopCat.toSSet.obj X).map
                  (SimplexCategory.subinterval 0 p (by omega)).op σ)) ⊗ₘ
          (K.map (vertexTransport (SimplexCategory.subinterval p (n - p) (by omega)).op σ) ≫
              ιTwistedChainComplex K (n - p)
                ((TopCat.toSSet.obj X).map
                  (SimplexCategory.subinterval p (n - p) (by omega)).op σ))) ≫
          HomologicalComplex.ιTensorObj L.twistedChainComplex K.twistedChainComplex
            p (n - p) n (by omega) := by
  apply (cancel_mono (((twistedChainComplexIsoAlternatingFaceMapComplex L).hom ⊗ₘ
    (twistedChainComplexIsoAlternatingFaceMapComplex K).hom).f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f,
    twistedAlexanderWhitneyDiagonal_comp_comparison]
  simp only [HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f]
  rw [ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f_assoc,
    ιTwistedChains_twistedChainsTensorDiagonal_app_assoc,
    SimplicialObject.alexanderWhitney_f]
  dsimp only [Monoidal.tensorObj_obj]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  rw [Category.assoc, tensorHom_comp_tensorHom_assoc, ιTwistedChains_map,
    ιTwistedChains_map]
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc,
    ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f]

variable {L K} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- Changing both local coefficient systems commutes with their twisted diagonal. -/
@[reassoc]
lemma twistedAlexanderWhitneyDiagonal_naturality (η : L ⟶ L') (θ : K ⟶ K') :
    twistedChainComplexCoefficientMap (η ⊗ₘ θ) ≫ twistedAlexanderWhitneyDiagonal L' K' =
      twistedAlexanderWhitneyDiagonal L K ≫
        (twistedChainComplexCoefficientMap η ⊗ₘ twistedChainComplexCoefficientMap θ) := by
  apply (cancel_mono ((twistedChainComplexIsoAlternatingFaceMapComplex L').hom ⊗ₘ
    (twistedChainComplexIsoAlternatingFaceMapComplex K').hom)).1
  simp only [Category.assoc, twistedAlexanderWhitneyDiagonal_comp_comparison,
    twistedChainComplexIsoAlternatingFaceMapComplex_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc, twistedChainsTensorDiagonal_naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [SimplicialObject.alexanderWhitney_naturality]
  simp only [tensorHom_comp_tensorHom,
    twistedChainComplexIsoAlternatingFaceMapComplex_hom_naturality]
  simp only [← tensorHom_comp_tensorHom,
    twistedAlexanderWhitneyDiagonal_comp_comparison_assoc]

section Space

variable (f : X ⟶ Y) (L K : LocalCoefficientSystem.{max v w, v, max v w} R Y)

/-- Pullback along a continuous map commutes with the twisted diagonal, after the canonical
identification between the pullback of a tensor product and the tensor product of pullbacks. -/
@[reassoc]
lemma twistedAlexanderWhitneyDiagonal_space_naturality :
    twistedChainComplexMap f (L ⊗ K) ≫ twistedAlexanderWhitneyDiagonal L K =
      twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).hom ≫
        twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K) ≫
          (twistedChainComplexMap f L ⊗ₘ twistedChainComplexMap f K) := by
  apply (cancel_mono ((twistedChainComplexIsoAlternatingFaceMapComplex L).hom ⊗ₘ
    (twistedChainComplexIsoAlternatingFaceMapComplex K).hom)).1
  simp only [Category.assoc, twistedAlexanderWhitneyDiagonal_comp_comparison,
    twistedChainComplexIsoAlternatingFaceMapComplex_hom_space_naturality_assoc]
  rw [← Functor.map_comp_assoc, twistedChainsTensorDiagonal_space_naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [SimplicialObject.alexanderWhitney_naturality]
  simp only [tensorHom_comp_tensorHom,
    twistedChainComplexIsoAlternatingFaceMapComplex_hom_space_naturality]
  simp only [← tensorHom_comp_tensorHom,
    twistedAlexanderWhitneyDiagonal_comp_comparison_assoc,
    twistedChainComplexIsoAlternatingFaceMapComplex_hom_naturality_assoc]

end Space

end TauCeti.LocalCoefficientSystem
