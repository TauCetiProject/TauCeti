/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Homotopy

/-!
# Subdivision and its homotopy on small singular chains

Barycentric subdivision and its prism operator preserve chains subordinate to any family of
subsets: every simplex they produce factors through the original singular simplex. This file
restricts both operators to the small-chain complex and proves the homotopy formula there.
Thus subdivision induces the identity on small-chain homology as well as ordinary homology.
This is needed when replacing a bounding chain by a sufficiently fine subdivision while
keeping the correction to its already-small boundary inside the small-chain complex.

The restricted operators commute with the inclusion and with maps of covered spaces.
No openness or covering hypothesis is needed for these preservation statements.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, steps (2) and (4).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology

universe w v u

namespace TauCeti

open AffineChain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)

-- The chain inclusion is the coproduct map induced by an injective map of simplices.
local instance (n : ℕ) :
    Mono ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n) :=
  inferInstanceAs (Mono ((sigmaConst.obj R).map
    ((X.smallSingularSubcomplex U).ι.app (Opposite.op ⦋n⦌))))

/-- Barycentric subdivision restricted to small singular chains in degree `n`. -/
def smallSingularSubdivisionX (n : ℕ) :
    ((X.smallSingularSubcomplex U : SSet).chainComplex R).X n ⟶
      ((X.smallSingularSubcomplex U : SSet).chainComplex R).X n :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex U : SSet).isColimitChainComplexXCofan R n)
    fun σ ↦ smallSingularChain R U σ n (subdivision _ n (simplex n))

@[reassoc (attr := simp)]
lemma ιChainComplex_smallSingularSubdivisionX {n : ℕ}
    (σ : (X.smallSingularSubcomplex U : SSet) _⦋n⦌) :
    (X.smallSingularSubcomplex U : SSet).ιChainComplex σ ≫ smallSingularSubdivisionX R U n =
      smallSingularChain R U σ n (subdivision _ n (simplex n)) :=
  Cofan.IsColimit.fac _ _ σ

/-- Inclusion intertwines the restricted and ordinary subdivision operators. -/
@[reassoc (attr := simp)]
lemma smallSingularSubdivisionX_ι (n : ℕ) :
    smallSingularSubdivisionX R U n ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n =
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n ≫
        singularSubdivisionX R X n := by
  ext σ
  simp [singularChain_subdivision_simplex]

/-- Barycentric subdivision as an endomorphism of the small-chain complex. -/
def smallSingularSubdivisionChainMap :
    (X.smallSingularSubcomplex U : SSet).chainComplex R ⟶
      (X.smallSingularSubcomplex U : SSet).chainComplex R where
  f n := smallSingularSubdivisionX R U n
  comm' i j hij := by
    apply (cancel_mono ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f j)).1
    simp only [Category.assoc, ← HomologicalComplex.Hom.comm,
      ← HomologicalComplex.Hom.comm_assoc, smallSingularSubdivisionX_ι_assoc,
      smallSingularSubdivisionX_ι]
    simpa only [singularSubdivisionChainMap_f, Category.assoc] using
      congrArg ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f i ≫ ·)
        ((singularSubdivisionChainMap R X).comm i j)

@[simp]
lemma smallSingularSubdivisionChainMap_f (n : ℕ) :
    (smallSingularSubdivisionChainMap R U).f n = smallSingularSubdivisionX R U n := (rfl)

/-- The restricted chain map commutes with the inclusion of small chains. -/
@[reassoc (attr := simp)]
lemma smallSingularSubdivisionChainMap_ι :
    smallSingularSubdivisionChainMap R U ≫
        SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R =
      SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫
        singularSubdivisionChainMap R X := by
  ext n : 1
  simp

/-- The prism operator of subdivision restricted to small singular chains. -/
def smallSingularPrismX (n : ℕ) :
    ((X.smallSingularSubcomplex U : SSet).chainComplex R).X n ⟶
      ((X.smallSingularSubcomplex U : SSet).chainComplex R).X (n + 1) :=
  Cofan.IsColimit.desc ((X.smallSingularSubcomplex U : SSet).isColimitChainComplexXCofan R n)
    fun σ ↦ smallSingularChain R U σ (n + 1) (prismModel n)

@[reassoc (attr := simp)]
lemma ιChainComplex_smallSingularPrismX {n : ℕ}
    (σ : (X.smallSingularSubcomplex U : SSet) _⦋n⦌) :
    (X.smallSingularSubcomplex U : SSet).ιChainComplex σ ≫ smallSingularPrismX R U n =
      smallSingularChain R U σ (n + 1) (prismModel n) :=
  Cofan.IsColimit.fac _ _ σ

/-- Inclusion intertwines the restricted and ordinary prism operators. -/
@[reassoc (attr := simp)]
lemma smallSingularPrismX_ι (n : ℕ) :
    smallSingularPrismX R U n ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f (n + 1) =
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n ≫ singularPrismX R X n := by
  ext σ
  simp

@[simp]
lemma smallSingularPrismX_zero : smallSingularPrismX R U 0 = 0 := by
  ext σ
  simp

@[simp]
lemma smallSingularSubdivisionX_zero : smallSingularSubdivisionX R U 0 = 𝟙 _ := by
  apply (cancel_mono ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f 0)).1
  simp

/-- The prism homotopy formula holds inside the small-chain complex. -/
lemma smallSingularPrismX_boundary_add_boundary_smallSingularPrismX (n : ℕ) :
    ((X.smallSingularSubcomplex U : SSet).chainComplex R).d (n + 1) n ≫
        smallSingularPrismX R U n + smallSingularPrismX R U (n + 1) ≫
        ((X.smallSingularSubcomplex U : SSet).chainComplex R).d (n + 2) (n + 1) =
      𝟙 _ - smallSingularSubdivisionX R U (n + 1) := by
  apply (cancel_mono ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f (n + 1))).1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc,
    ← HomologicalComplex.Hom.comm, ← HomologicalComplex.Hom.comm_assoc,
    smallSingularPrismX_ι_assoc, smallSingularPrismX_ι,
    smallSingularSubdivisionX_ι, Category.id_comp]
  simpa only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id, Category.assoc] using
    congrArg ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f (n + 1) ≫ ·)
      (singularPrismX_boundary_add_boundary_singularPrismX R X n)

/-- Subdivision of small singular chains is chain homotopic to their identity map. -/
def smallSingularSubdivisionHomotopy : Homotopy (𝟙 _) (smallSingularSubdivisionChainMap R U) where
  hom i j := if h : i + 1 = j then smallSingularPrismX R U i ≫ eqToHom (by rw [h]) else 0
  zero i j hij := by
    rw [ComplexShape.down_Rel] at hij
    simp [hij]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp [smallSingularPrismX_boundary_add_boundary_smallSingularPrismX]

@[simp]
lemma smallSingularSubdivisionHomotopy_hom (n : ℕ) :
    (smallSingularSubdivisionHomotopy R U).hom n (n + 1) = smallSingularPrismX R U n := by
  simp [smallSingularSubdivisionHomotopy]

variable {κ : Type*} {Y : TopCat.{w}} (V : κ → Set Y)
  (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))

/-- The restricted subdivision commutes with maps carrying cover members into cover members. -/
@[reassoc]
lemma smallSingularSubdivisionChainMap_naturality :
    SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R ≫
        smallSingularSubdivisionChainMap R V =
      smallSingularSubdivisionChainMap R U ≫
        SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R := by
  have hι : SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R ≫
      SSet.chainComplexMap (Y.smallSingularSubcomplex V).ι R =
      SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) R := by
    simp only [← Functor.map_comp, TopCat.smallSingularSubcomplexMap_ι]
  have : Mono (SSet.chainComplexMap (Y.smallSingularSubcomplex V).ι R) :=
    HomologicalComplex.mono_of_mono_f _ inferInstance
  apply (cancel_mono (SSet.chainComplexMap (Y.smallSingularSubcomplex V).ι R)).1
  simp only [Category.assoc, smallSingularSubdivisionChainMap_ι, hι, reassoc_of% hι,
    smallSingularSubdivisionChainMap_ι_assoc]
  -- Express the singular-chain functor through its defining simplicial-chain functor.
  simpa [singularChainComplexFunctor] using
    congrArg (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫ ·)
      ((singularSubdivision R).naturality f)

/-- The restricted prism commutes with maps carrying cover members into cover members. -/
@[reassoc]
lemma smallSingularPrismX_naturality (n : ℕ) :
    (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R).f n ≫
        smallSingularPrismX R V n =
      smallSingularPrismX R U n ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R).f (n + 1) := by
  have hι (k : ℕ) : (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R).f k ≫
      (SSet.chainComplexMap (Y.smallSingularSubcomplex V).ι R).f k =
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f k ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k := by
    simp only [← HomologicalComplex.comp_f, ← Functor.map_comp,
      TopCat.smallSingularSubcomplexMap_ι]
  apply (cancel_mono ((SSet.chainComplexMap (Y.smallSingularSubcomplex V).ι R).f (n + 1))).1
  simp only [Category.assoc, smallSingularPrismX_ι, hι, reassoc_of% hι n,
    smallSingularPrismX_ι_assoc]
  exact congrArg ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n ≫ ·)
    (singularPrismX_naturality R X f n)

/-- Subdivision acts as the identity on small-chain homology. -/
@[simp]
lemma homologyMap_smallSingularSubdivisionChainMap [CategoryWithHomology C] (n : ℕ) :
    HomologicalComplex.homologyMap (smallSingularSubdivisionChainMap R U) n = 𝟙 _ := by
  rw [← (smallSingularSubdivisionHomotopy R U).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

end TauCeti
