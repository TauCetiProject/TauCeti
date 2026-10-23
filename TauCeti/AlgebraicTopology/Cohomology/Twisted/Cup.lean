/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cup
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.AlexanderWhitney

/-!
# Cup products with dual local coefficients

For local systems `L` and `K` of modules over a commutative ring `R`, the twisted cochains
used here are `Hom(C_*(X; L), M)` and `Hom(C_*(X; K), N)`: the cochain coefficient systems are
the duals of the chain coefficient systems, with values in `M` and `N`. A pairing
`μ : M ⊗ N ⟶ P` gives a cup product with target `Hom(C_*(X; L ⊗ K), P)`, by evaluating the
two cochains on the front and back faces of each simplex and pairing their values. The
back-face coefficient is transported from vertex zero to the cut vertex.

The construction applies `TauCeti.ChainComplex.cup` to `twistedAlexanderWhitneyDiagonal`.
The product is
`R`-bilinear and natural in the coefficient systems and under continuous maps, retaining the
canonical tensor comparison between pulled-back local systems. The ring and coefficient fibres
share a universe, as required by the monoidal structure on `ModuleCat`; the space may live in a
smaller universe.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.2 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped Simplicial

universe v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] {X Y : TopCat.{v}}
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R X)
  {M N P : ModuleCat.{max v w} R} (μ : M ⊗ N ⟶ P)

/-- On a simplex, the cochain cup product evaluates the front and back faces, transporting
the coefficients to their initial vertices before evaluation. -/
lemma ιTwistedChainComplex_cupCochain (p q n : ℕ) (h : p + q = n)
    (φ : L.twistedChainComplex.X p ⟶ M) (ψ : K.twistedChainComplex.X q ⟶ N)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChainComplex (L ⊗ K) n σ ≫
        TauCeti.ChainComplex.cupCochain R (twistedAlexanderWhitneyDiagonal L K)
          μ p q n h φ ψ =
      ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
          ιTwistedChainComplex L p
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
        (K.map (vertexTransport (SimplexCategory.subinterval p q (by omega)).op σ) ≫
          ιTwistedChainComplex K q
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫
        μ := by
  subst h
  -- The tensor cochain kills every bidegree except `(p, q)`. State the surviving term for
  -- an arbitrary equal back degree: rewriting `p + q - p` directly gives an ill-typed motive
  -- because both the subinterval bound and the tensor-summand equality depend on that degree.
  have key : ∀ (j : ℕ) (hj : j = q) (hj' : p + j ≤ p + q) (hj'' : p + j = p + q),
      ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
          ιTwistedChainComplex L p
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ)) ⊗ₘ
        (K.map (vertexTransport (SimplexCategory.subinterval p j hj').op σ) ≫
          ιTwistedChainComplex K j
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p j hj').op σ))) ≫
          ιTensorObj L.twistedChainComplex K.twistedChainComplex p j (p + q) hj'' ≫
            TauCeti.ChainComplex.tensorCochain μ φ ψ (p + q) =
        ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
            ιTwistedChainComplex L p
              ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
          (K.map (vertexTransport (SimplexCategory.subinterval p q (by omega)).op σ) ≫
            ιTwistedChainComplex K q
              ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫
          μ := by
    rintro _ rfl _ _
    rw [TauCeti.ChainComplex.ιTensorObj_tensorCochain, tensorHom_comp_tensorHom_assoc]
    simp only [Category.assoc]
  rw [TauCeti.ChainComplex.cupCochain_apply,
    ιTwistedChainComplex_twistedAlexanderWhitneyDiagonal_f_assoc]
  dsimp only [Monoidal.tensorObj_obj]
  rw [Preadditive.sum_comp, Finset.sum_eq_single ⟨p, by omega⟩]
  · simp only [Category.assoc]
    exact key (p + q - p) (by omega) _ _
  · rintro i - hi
    rw [Category.assoc, TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_left _ _ _ _
      (fun h ↦ hi (Fin.ext h)), comp_zero]
  · simp

/-- The cup product of twisted cohomology classes, with dual chain coefficient systems and
the pairing `μ` of their values. -/
def twistedCup (p q n : ℕ) (h : p + q = n) :
    L.twistedCohomology R M p →ₗ[R] K.twistedCohomology R N q →ₗ[R]
      (L ⊗ K).twistedCohomology R P n :=
  TauCeti.ChainComplex.cup R (twistedAlexanderWhitneyDiagonal L K) μ p q n h

/-- The cup product of classes of twisted cocycles is represented by their cochain cup product. -/
@[simp]
lemma twistedCup_homologyπ (p q n : ℕ) (h : p + q = n)
    (a : (L.twistedCochainComplex R M).cycles p)
    (b : (K.twistedCochainComplex R N).cycles q) :
    twistedCup L K μ p q n h ((L.twistedCochainComplex R M).homologyπ p a)
        ((K.twistedCochainComplex R N).homologyπ q b) =
      ((L ⊗ K).twistedCochainComplex R P).homologyπ n
        (TauCeti.ChainComplex.cupCycles R (twistedAlexanderWhitneyDiagonal L K)
          μ p q n h a b) :=
  TauCeti.ChainComplex.cup_homologyπ _ _ _ _ _ _ _ _

variable {L K} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- Cup products commute with coefficient-system morphisms, contravariantly as do twisted
cochains. -/
lemma twistedCup_coefficient_naturality (η : L ⟶ L') (θ : K ⟶ K')
    (p q n : ℕ) (h : p + q = n)
    (a : L'.twistedCohomology R M p) (b : K'.twistedCohomology R N q) :
    twistedCup L K μ p q n h (twistedCohomologyCoefficientMap R M η p a)
        (twistedCohomologyCoefficientMap R N θ q b) =
      twistedCohomologyCoefficientMap R P (η ⊗ₘ θ) n
        (twistedCup L' K' μ p q n h a b) :=
  TauCeti.ChainComplex.cup_naturality _ μ _ _ _ _
    (twistedAlexanderWhitneyDiagonal_naturality η θ) p q n h a b

section Space

variable (f : X ⟶ Y) (L K : LocalCoefficientSystem.{max v w, v, max v w} R Y)

/-- Pulling back the cup product is cupping the pulled-back classes, after the canonical
comparison between the pullback of a tensor product and the tensor product of pullbacks. -/
lemma twistedCup_space_naturality (p q n : ℕ) (h : p + q = n)
    (a : L.twistedCohomology R M p) (b : K.twistedCohomology R N q) :
    twistedCup ((pullback f.hom).obj L) ((pullback f.hom).obj K) μ p q n h
        (twistedCohomologyMap R M f L p a) (twistedCohomologyMap R N f K q b) =
      twistedCohomologyCoefficientMap R P (pullbackTensorIso f.hom L K).inv n
        (twistedCohomologyMap R P f (L ⊗ K) n (twistedCup L K μ p q n h a b)) := by
  have hD : (twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K)) ≫ twistedAlexanderWhitneyDiagonal L K =
        twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K) ≫
          (twistedChainComplexMap f L ⊗ₘ twistedChainComplexMap f K) := by
    rw [Category.assoc, twistedAlexanderWhitneyDiagonal_space_naturality]
    simp [← Category.assoc, ← twistedChainComplexCoefficientMap_comp]
  have hcup := TauCeti.ChainComplex.cup_naturality
    (twistedAlexanderWhitneyDiagonal L K) μ
    (twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K))
    _ (twistedChainComplexMap f L) (twistedChainComplexMap f K) hD p q n h a b
  have hc :
      ((TauCeti.ChainComplex.linearYonedaFunctor R P).map
        (twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).inv ≫
          twistedChainComplexMap f (L ⊗ K)).op :
        (L ⊗ K).twistedCochainComplex R P ⟶
          (((pullback f.hom).obj L) ⊗ ((pullback f.hom).obj K)).twistedCochainComplex R P) =
        twistedCochainComplexMap R P f (L ⊗ K) ≫
          twistedCochainComplexCoefficientMap R P (pullbackTensorIso f.hom L K).inv := by
    rw [op_comp]
    exact Functor.map_comp _ _ _
  have hh := (congrArg (fun t ↦ HomologicalComplex.homologyMap t n) hc).trans
    (HomologicalComplex.homologyMap_comp _ _ n)
  exact hcup.trans (congrArg (fun t ↦ t (twistedCup L K μ p q n h a b)) hh)

end Space

end TauCeti.LocalCoefficientSystem
