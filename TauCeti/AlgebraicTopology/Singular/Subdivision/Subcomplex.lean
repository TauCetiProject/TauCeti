/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
import TauCeti.Algebra.Homology.Homotopy

/-!
# Subdivision and its homotopy on affinely stable subcomplexes of singular chains

A subcomplex `S` of the singular simplicial set of a space `X` is *affinely stable*
(`SSet.Subcomplex.IsAffineStable`) when the composite `σ ∘ A` of any of its simplices `σ : Δᵐ → X`
with an affine map `A : Δᵏ → Δᵐ` of standard simplices is again a simplex of `S`. Barycentric
subdivision and its prism operator send a singular simplex `σ` to a combination of simplices
`σ ∘ A` with `A` affine, so on an affinely stable subcomplex both operators restrict to the chains
`(S : SSet).chainComplex R` of `S`. This file builds the restricted operators and proves the
prism formula there, so that subdivision is chain homotopic to the identity on the chains of `S`
and acts as the identity on their homology.

The chains subordinate to a family of subsets (`TopCat.smallSingularSubcomplex`) form an affinely
stable subcomplex, and so do the smooth singular simplices of a manifold
(`TauCeti.smoothSingularSubcomplex`). Both are needed: the small-chain theorem replaces a chain by
a fine subdivision of it, and the comparison of smooth with continuous singular chains needs the
same operators on smooth chains.

## Main definitions and results

* `SSet.Subcomplex.IsAffineStable`: the subcomplex is closed under precomposition with affine
  maps of standard simplices. Intersections of affinely stable subcomplexes are affinely stable.
* `TauCeti.AffineChain.subcomplexChain`: push affine chains of `Δᵐ` forward along a simplex of an
  affinely stable subcomplex, with values in the chains of the subcomplex.
* `TauCeti.subcomplexSubdivisionChainMap`: barycentric subdivision as a chain endomorphism of the
  chains of an affinely stable subcomplex, compatible with the inclusion into singular chains.
* `TauCeti.subcomplexSubdivisionChainMap_pow_f_ι`: iterated subdivision is compatible with the
  inclusion into singular chains.
* `TauCeti.subcomplexSubdivisionHomotopy`: the prism operator as a chain homotopy from the identity
  to subdivision on those chains.
* `TauCeti.homologyMap_subcomplexSubdivisionChainMap`: subdivision induces the identity on their
  homology.
* `TauCeti.subcomplexSubdivisionChainMap_naturality`, `TauCeti.subcomplexPrismX_naturality`: both
  operators commute with maps of subcomplexes lying over continuous maps.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, steps (2) and (4).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology Opposite

universe w v u

namespace SSet.Subcomplex

variable {X : TopCat.{w}}

/-- A subcomplex of the singular simplicial set of a space is *affinely stable* when the composite
of any of its simplices `σ : Δᵐ → X` with an affine map `Δᵏ → Δᵐ` of standard simplices, given by
its vertices `v`, is again a simplex of the subcomplex. -/
class IsAffineStable (S : (TopCat.toSSet.obj X).Subcomplex) : Prop where
  /-- Precomposing a simplex of the subcomplex with an affine map gives a simplex of the
  subcomplex. -/
  comp_affineMapMk_mem {m k : ℕ} {σ : TopCat.toSSet.obj X _⦋m⦌} (hσ : σ ∈ S.obj (op ⦋m⦌))
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) :
    (X.toSSetObjEquiv _).symm ((X.toSSetObjEquiv _ σ).comp (StdSimplex.continuousAffineMapMk v)) ∈
      S.obj (op ⦋k⦌)

/-- The intersection of two affinely stable subcomplexes is affinely stable. -/
instance (S T : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable] [T.IsAffineStable] :
    (S ⊓ T).IsAffineStable where
  comp_affineMapMk_mem hσ v :=
    ⟨IsAffineStable.comp_affineMapMk_mem hσ.1 v, IsAffineStable.comp_affineMapMk_mem hσ.2 v⟩

end SSet.Subcomplex

namespace TauCeti

open AffineChain SSet.Subcomplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} (S : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable]

namespace AffineChain

/-- Push an affine chain of `Δᵐ` forward along a simplex `σ` of an affinely stable subcomplex `S`,
with values in the chains of `S`: a vertex tuple `v` is sent to the summand of the simplex
`σ ∘ StdSimplex.continuousAffineMapMk v` of `S`. -/
def subcomplexChain {m : ℕ} (σ : (S : SSet) _⦋m⦌) (k : ℕ) :
    ((Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) →ₗ[ℤ]
      (R ⟶ ((S : SSet).chainComplex R).X k) :=
  Finsupp.linearCombination ℤ fun v ↦ (S : SSet).ιChainComplex
    ⟨(X.toSSetObjEquiv _).symm
      ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)),
      IsAffineStable.comp_affineMapMk_mem σ.property v⟩

@[simp]
lemma subcomplexChain_single {m k : ℕ} (σ : (S : SSet) _⦋m⦌)
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) (a : ℤ) :
    subcomplexChain R S σ k (Finsupp.single v a) = a • (S : SSet).ιChainComplex
      ⟨(X.toSSetObjEquiv _).symm
        ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)),
        IsAffineStable.comp_affineMapMk_mem σ.property v⟩ := by
  simp [subcomplexChain]

/-- Pushing forward inside an affinely stable subcomplex agrees with the ordinary push-forward
after inclusion into singular chains. -/
@[reassoc (attr := simp)]
lemma subcomplexChain_ι {m k : ℕ} (σ : (S : SSet) _⦋m⦌)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    subcomplexChain R S σ k c ≫ (SSet.chainComplexMap S.ι R).f k =
      singularChain R (X.toSSetObjEquiv _ σ.val) k c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Preadditive.add_comp, hc, hd]
  | single v a => simp [SSet.ι_chainComplexMap_f]

end AffineChain

/-- Barycentric subdivision restricted to the chains of an affinely stable subcomplex, in
degree `n`. -/
def subcomplexSubdivisionX (n : ℕ) :
    ((S : SSet).chainComplex R).X n ⟶ ((S : SSet).chainComplex R).X n :=
  Cofan.IsColimit.desc ((S : SSet).isColimitChainComplexXCofan R n)
    fun σ ↦ subcomplexChain R S σ n (subdivision _ n (simplex n))

@[reassoc (attr := simp)]
lemma ιChainComplex_subcomplexSubdivisionX {n : ℕ} (σ : (S : SSet) _⦋n⦌) :
    (S : SSet).ιChainComplex σ ≫ subcomplexSubdivisionX R S n =
      subcomplexChain R S σ n (subdivision _ n (simplex n)) :=
  Cofan.IsColimit.fac _ _ σ

/-- Inclusion intertwines the restricted and ordinary subdivision operators. -/
@[reassoc (attr := simp)]
lemma subcomplexSubdivisionX_ι (n : ℕ) :
    subcomplexSubdivisionX R S n ≫ (SSet.chainComplexMap S.ι R).f n =
      (SSet.chainComplexMap S.ι R).f n ≫ singularSubdivisionX R X n := by
  ext σ
  simp [singularChain_subdivision_simplex, SSet.ι_chainComplexMap_f_assoc]

@[simp]
lemma subcomplexSubdivisionX_zero : subcomplexSubdivisionX R S 0 = 𝟙 _ := by
  apply (cancel_mono ((SSet.chainComplexMap S.ι R).f 0)).1
  simp

/-- Barycentric subdivision as a chain endomorphism of the chains of an affinely stable
subcomplex. -/
def subcomplexSubdivisionChainMap : (S : SSet).chainComplex R ⟶ (S : SSet).chainComplex R where
  f n := subcomplexSubdivisionX R S n
  comm' i j _ := by
    apply (cancel_mono ((SSet.chainComplexMap S.ι R).f j)).1
    simp only [Category.assoc, ← HomologicalComplex.Hom.comm,
      ← HomologicalComplex.Hom.comm_assoc, subcomplexSubdivisionX_ι_assoc,
      subcomplexSubdivisionX_ι]
    simpa only [singularSubdivisionChainMap_f, Category.assoc] using
      congrArg ((SSet.chainComplexMap S.ι R).f i ≫ ·) ((singularSubdivisionChainMap R X).comm i j)

@[simp]
lemma subcomplexSubdivisionChainMap_f (n : ℕ) :
    (subcomplexSubdivisionChainMap R S).f n = subcomplexSubdivisionX R S n := (rfl)

/-- The restricted subdivision commutes with the inclusion into singular chains. -/
@[reassoc (attr := simp)]
lemma subcomplexSubdivisionChainMap_ι :
    subcomplexSubdivisionChainMap R S ≫ SSet.chainComplexMap S.ι R =
      SSet.chainComplexMap S.ι R ≫ singularSubdivisionChainMap R X := by
  ext n : 1
  simp

/-- Iterated restricted subdivision commutes with the inclusion into singular chains. -/
@[reassoc]
lemma subcomplexSubdivisionChainMap_pow_f_ι (m n : ℕ) :
    (End.of (subcomplexSubdivisionChainMap R S) ^ m).asHom.f n ≫
        (SSet.chainComplexMap S.ι R).f n =
      (SSet.chainComplexMap S.ι R).f n ≫
        (End.of (singularSubdivisionChainMap R X) ^ m).asHom.f n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [HomologicalComplex.pow_f_succ, HomologicalComplex.pow_f_succ, Category.assoc,
      subcomplexSubdivisionChainMap_f, subcomplexSubdivisionX_ι, reassoc_of% ih,
      singularSubdivisionChainMap_f]

/-- The prism operator of barycentric subdivision restricted to the chains of an affinely stable
subcomplex. -/
def subcomplexPrismX (n : ℕ) :
    ((S : SSet).chainComplex R).X n ⟶ ((S : SSet).chainComplex R).X (n + 1) :=
  Cofan.IsColimit.desc ((S : SSet).isColimitChainComplexXCofan R n)
    fun σ ↦ subcomplexChain R S σ (n + 1) (prismModel n)

@[reassoc (attr := simp)]
lemma ιChainComplex_subcomplexPrismX {n : ℕ} (σ : (S : SSet) _⦋n⦌) :
    (S : SSet).ιChainComplex σ ≫ subcomplexPrismX R S n =
      subcomplexChain R S σ (n + 1) (prismModel n) :=
  Cofan.IsColimit.fac _ _ σ

/-- Inclusion intertwines the restricted and ordinary prism operators. -/
@[reassoc (attr := simp)]
lemma subcomplexPrismX_ι (n : ℕ) :
    subcomplexPrismX R S n ≫ (SSet.chainComplexMap S.ι R).f (n + 1) =
      (SSet.chainComplexMap S.ι R).f n ≫ singularPrismX R X n := by
  ext σ
  simp [SSet.ι_chainComplexMap_f_assoc]

@[simp]
lemma subcomplexPrismX_zero : subcomplexPrismX R S 0 = 0 := by
  ext σ
  simp

/-- The prism homotopy formula holds on the chains of an affinely stable subcomplex. -/
lemma subcomplexPrismX_boundary_add_boundary_subcomplexPrismX (n : ℕ) :
    ((S : SSet).chainComplex R).d (n + 1) n ≫ subcomplexPrismX R S n +
        subcomplexPrismX R S (n + 1) ≫ ((S : SSet).chainComplex R).d (n + 2) (n + 1) =
      𝟙 _ - subcomplexSubdivisionX R S (n + 1) := by
  apply (cancel_mono ((SSet.chainComplexMap S.ι R).f (n + 1))).1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc,
    ← HomologicalComplex.Hom.comm, ← HomologicalComplex.Hom.comm_assoc,
    subcomplexPrismX_ι_assoc, subcomplexPrismX_ι, subcomplexSubdivisionX_ι, Category.id_comp]
  simpa only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id, Category.assoc] using
    congrArg ((SSet.chainComplexMap S.ι R).f (n + 1) ≫ ·)
      (singularPrismX_boundary_add_boundary_singularPrismX R X n)

/-- Subdivision of the chains of an affinely stable subcomplex is chain homotopic to the
identity, through the prism operator. -/
def subcomplexSubdivisionHomotopy : Homotopy (𝟙 _) (subcomplexSubdivisionChainMap R S) :=
  Homotopy.equivSubZero.symm <| Homotopy.mkChainComplex _ (subcomplexPrismX R S) (by simp)
    fun n ↦ by simp [subcomplexPrismX_boundary_add_boundary_subcomplexPrismX]

@[simp]
lemma subcomplexSubdivisionHomotopy_hom (n : ℕ) :
    (subcomplexSubdivisionHomotopy R S).hom n (n + 1) = subcomplexPrismX R S n :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-- Subdivision acts as the identity on the homology of the chains of an affinely stable
subcomplex. -/
@[simp]
lemma homologyMap_subcomplexSubdivisionChainMap [CategoryWithHomology C] (n : ℕ) :
    HomologicalComplex.homologyMap (subcomplexSubdivisionChainMap R S) n = 𝟙 _ := by
  rw [← (subcomplexSubdivisionHomotopy R S).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

variable {Y : TopCat.{w}} (T : (TopCat.toSSet.obj Y).Subcomplex) [T.IsAffineStable]
  (f : X ⟶ Y) (g : (S : SSet) ⟶ (T : SSet)) (hg : g ≫ T.ι = S.ι ≫ TopCat.toSSet.map f)
include hg

/-- The restricted subdivision commutes with a map of affinely stable subcomplexes lying over a
continuous map of spaces. -/
@[reassoc]
lemma subcomplexSubdivisionChainMap_naturality :
    SSet.chainComplexMap g R ≫ subcomplexSubdivisionChainMap R T =
      subcomplexSubdivisionChainMap R S ≫ SSet.chainComplexMap g R := by
  have hι : SSet.chainComplexMap g R ≫ SSet.chainComplexMap T.ι R =
      SSet.chainComplexMap S.ι R ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
    simp only [← Functor.map_comp, hg]
  apply (cancel_mono (SSet.chainComplexMap T.ι R)).1
  simp only [Category.assoc, subcomplexSubdivisionChainMap_ι, hι, reassoc_of% hι,
    subcomplexSubdivisionChainMap_ι_assoc]
  -- Express the singular-chain functor through its defining simplicial-chain functor.
  simpa [singularChainComplexFunctor] using
    congrArg (SSet.chainComplexMap S.ι R ≫ ·) ((singularSubdivision R).naturality f)

/-- The restricted prism operator commutes with a map of affinely stable subcomplexes lying over a
continuous map of spaces. -/
@[reassoc]
lemma subcomplexPrismX_naturality (n : ℕ) :
    (SSet.chainComplexMap g R).f n ≫ subcomplexPrismX R T n =
      subcomplexPrismX R S n ≫ (SSet.chainComplexMap g R).f (n + 1) := by
  have hι (k : ℕ) : (SSet.chainComplexMap g R).f k ≫ (SSet.chainComplexMap T.ι R).f k =
      (SSet.chainComplexMap S.ι R).f k ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k := by
    simp only [← HomologicalComplex.comp_f, ← Functor.map_comp, hg]
  apply (cancel_mono ((SSet.chainComplexMap T.ι R).f (n + 1))).1
  simp only [Category.assoc, subcomplexPrismX_ι, hι, reassoc_of% hι n, subcomplexPrismX_ι_assoc]
  exact congrArg ((SSet.chainComplexMap S.ι R).f n ≫ ·) (singularPrismX_naturality R X f n)

end TauCeti
