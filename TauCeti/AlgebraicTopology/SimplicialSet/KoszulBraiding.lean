/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KoszulBraiding
public import TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber

/-!
# The Alexander–Whitney map and the interchange of factors

For simplicial sets `K` and `L`, the Alexander–Whitney map
`C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)` followed by the Koszul braiding
`C(K; R) ⊗ C(L; S) ⟶ C(L; S) ⊗ C(K; R)`, which is `x ⊗ y ↦ (-1)^(p * q) y ⊗ x` in bidegree
`(p, q)`, is chain homotopic to the map that first swaps the factors of `K × L` and of `R ⊗ S` and
then applies the Alexander–Whitney map of `L × K`
(`SSet.alexanderWhitneyKoszulBraidingHomotopy`).  The two maps are not equal: the first sends a
simplex to a sum of front faces of its `K`-component tensored with back faces of its
`L`-component, the second the other way around.

This is the chain-level input for the graded commutativity of cup products.  The proof is by
acyclic models (`SSet.prodChainComplexHomotopy`): after composing with the shuffle map of `L × K`
and the swap back to `K × L`, the first map agrees in degree zero with the coefficient braiding
`R ⊗ S ⟶ S ⊗ R`, and the shuffle map is a right homotopy inverse of the Alexander–Whitney map
(`SSet.shuffleAlexanderWhitneyHomotopy`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, Theorem 3.11, for graded commutativity of the
  cup product.
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

/-- The Alexander–Whitney map of `K × L`, followed by the Koszul braiding, the shuffle map of
`L × K` and the swap back to `K × L`. -/
private def alexanderWhitneyKoszulBraidingShuffle :
    (K ⊗ L).chainComplex (R ⊗ S) ⟶ (K ⊗ L).chainComplex (S ⊗ R) :=
  alexanderWhitney K L R S ≫
    TauCeti.NatChainComplex.koszulBraidingHom (K.chainComplex R) (L.chainComplex S) ≫
      shuffle L K S R ≫ chainComplexMap (β_ L K).hom (S ⊗ R)

variable {K L} in
private lemma alexanderWhitneyKoszulBraidingShuffle_naturality {K' L' : SSet.{w}} (f : K ⟶ K')
    (g : L ⟶ L') :
    chainComplexMap (f ⊗ₘ g) (R ⊗ S) ≫ alexanderWhitneyKoszulBraidingShuffle K' L' R S =
      alexanderWhitneyKoszulBraidingShuffle K L R S ≫ chainComplexMap (f ⊗ₘ g) (S ⊗ R) := by
  -- `⊗ₘ` of chain complexes is `HomologicalComplex.tensorHom` by definition
  have hκ : (chainComplexMap f R ⊗ₘ chainComplexMap g S) ≫
      TauCeti.NatChainComplex.koszulBraidingHom (K'.chainComplex R) (L'.chainComplex S) =
        TauCeti.NatChainComplex.koszulBraidingHom (K.chainComplex R) (L.chainComplex S) ≫
          (chainComplexMap g S ⊗ₘ chainComplexMap f R) :=
    TauCeti.NatChainComplex.koszulBraidingHom_naturality _ _ _ _
  simp only [alexanderWhitneyKoszulBraidingShuffle, alexanderWhitney_naturality_assoc,
    reassoc_of% hκ, shuffle_naturality_assoc, Category.assoc, ← Functor.map_comp,
    BraidedCategory.braiding_naturality]

/-- In degree zero, `alexanderWhitneyKoszulBraidingShuffle` is the coefficient braiding: a vertex
`(x, y)` goes to `x ⊗ y`, then to `y ⊗ x` with the braided coefficients, then to the vertex
`(y, x)` of `L × K` and back to `(x, y)`. -/
private lemma alexanderWhitneyKoszulBraidingShuffle_f_zero :
    (alexanderWhitneyKoszulBraidingShuffle K L R S).f 0 =
      (((chainComplexFunctor C).map (β_ R S).hom).app (K ⊗ L)).f 0 := by
  ext x
  rw [alexanderWhitneyKoszulBraidingShuffle, comp_f, comp_f, comp_f,
    ιChainComplex_alexanderWhitney_f_assoc, Fin.sum_univ_one,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f]
  simp only [Fin.val_zero, Nat.sub_zero, TauCeti.SimplexCategory.subinterval_zero_eq_id, op_id,
    Functor.map_id_apply, Category.assoc,
    TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f_assoc, mul_zero, pow_zero, one_smul,
    BraidedCategory.braiding_naturality_assoc,
    reassoc_of% ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero]
  -- the swap sends the vertex `(x.2, x.1)` of `L × K` to `(x.1, x.2) = x`, by definition
  exact congrArg _ (ι_chainComplexMap_f (L ⊗ K) (K ⊗ L) (β_ L K).hom (S ⊗ R) (n := 0) (x.2, x.1))

/-- **The Alexander–Whitney map commutes with the interchange of factors up to homotopy**: the
Alexander–Whitney map `C(K × L; R ⊗ S) ⟶ C(K; R) ⊗ C(L; S)` followed by the Koszul braiding,
`x ⊗ y ↦ (-1)^(p * q) y ⊗ x` in bidegree `(p, q)`, is chain homotopic to the coefficient braiding
`R ⊗ S ⟶ S ⊗ R` followed by the swap `K × L ⟶ L × K` and the Alexander–Whitney map of `L × K`. -/
def alexanderWhitneyKoszulBraidingHomotopy :
    Homotopy (alexanderWhitney K L R S ≫
        TauCeti.NatChainComplex.koszulBraidingHom (K.chainComplex R) (L.chainComplex S))
      (((chainComplexFunctor C).map (β_ R S).hom).app (K ⊗ L) ≫
        chainComplexMap (β_ K L).hom (S ⊗ R) ≫ alexanderWhitney L K S R) :=
  (Homotopy.ofEq (Category.comp_id _).symm).trans <|
    ((shuffleAlexanderWhitneyHomotopy L K S R).symm.compLeft _).trans <|
      -- inserting the swap `L × K ⟶ K × L` and its inverse
      (Homotopy.ofEq (by
        rw [alexanderWhitneyKoszulBraidingShuffle, Category.assoc, Category.assoc, Category.assoc,
          Category.assoc, ← Functor.map_comp_assoc, SymmetricCategory.symmetry,
          CategoryTheory.Functor.map_id, Category.id_comp])).trans <|
        (prodChainComplexHomotopy (fun K L ↦ alexanderWhitneyKoszulBraidingShuffle K L R S)
          (fun K L ↦ ((chainComplexFunctor C).map (β_ R S).hom).app (K ⊗ L))
          (fun _ _ _ _ f g ↦ alexanderWhitneyKoszulBraidingShuffle_naturality R S f g)
          (fun _ _ _ _ f g ↦ ((chainComplexFunctor C).map (β_ R S).hom).naturality (f ⊗ₘ g))
          (fun K L ↦ alexanderWhitneyKoszulBraidingShuffle_f_zero K L R S) K L).compRight _

end SSet
