/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.TopologicalSimplex

/-!
# Singular chains with local coefficients

A local coefficient system `L` on a space `X` is a functor from its fundamental groupoid to
modules, so it assigns a module to every point and a transport isomorphism to every path class.
Twisting the singular chain complex by `L` replaces the free module on the singular `n`-simplices
by the coproduct, over singular `n`-simplices `σ`, of the fibre of `L` at the initial vertex of
`σ`.  Reindexing a simplex moves its initial vertex inside the simplex, so the structure maps of
the resulting simplicial module also transport the coefficients along the image of a path joining
the old initial vertex to the new one.

The topological simplex is simply connected, so that path class, and hence the transport, is
determined by its endpoints alone.  This is what makes the simplicial identities hold: a
composite of transports is again the transport between its endpoints, and the boundary of a
twisted chain complex therefore squares to zero for the same formal reason as in the untwisted
case.

For a constant system the twisting is trivial and the construction returns Mathlib's singular
chain complex, while a continuous map `f : X ⟶ Y` induces a chain map from the chains of `X`
twisted by the system pulled back along `f`.

## Main declarations

* `TauCeti.LocalCoefficientSystem.twistedChains`: the simplicial module of twisted chains, and
  `twistedChainComplex`, `twistedHomology` for its alternating face map complex and homology.
* `TauCeti.LocalCoefficientSystem.twistedChainsFunctor`: twisted chains as a functor of the
  coefficient system, with `twistedChainComplexCoefficientMap` and
  `twistedHomologyCoefficientMap` for the induced maps of complexes and of homology, together
  with their identity and composition laws.
* `TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso`: for a constant system, twisted
  homology is ordinary singular homology, naturally in the module of coefficients.
* `TauCeti.LocalCoefficientSystem.twistedChainComplexMap`: the chain map induced by a continuous
  map, and `twistedHomologyMap` the resulting map on twisted homology, together with their
  identity and composition laws.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {m n p : SimplexCategoryᵒᵖ}

/-- The initial vertex of a singular simplex, as an object of the fundamental groupoid. -/
-- This is an `abbrev` so that the coefficient module attached to a simplex stays transparent to
-- unification.
abbrev initialVertex (σ : (TopCat.toSSet.obj X).obj n) : FundamentalGroupoid X :=
  ⟨TopCat.simplexMap σ (toTopInitialVertex n.unop)⟩

/-- The morphism of the fundamental groupoid of `X` obtained by running a singular simplex along
the unique path class between two points of its simplex. -/
def pathTransport (σ : (TopCat.toSSet.obj X).obj n) (z w : toTop.{v}.obj n.unop) :
    (⟨TopCat.simplexMap σ z⟩ : FundamentalGroupoid X) ⟶ ⟨TopCat.simplexMap σ w⟩ :=
  (FundamentalGroupoid.map (TopCat.simplexMap σ)).map
    (default : (⟨z⟩ : FundamentalGroupoid (toTop.{v}.obj n.unop)) ⟶ ⟨w⟩)

/-- Transport inside a simplex from a point to itself is the identity. -/
@[simp]
lemma pathTransport_self (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) :
    pathTransport σ z z = 𝟙 _ :=
  FundamentalGroupoid.map_default_self _ _

/-- Transports inside a simplex compose: running from `z` to `w` and then from `w` to `y` is
running from `z` to `y`. -/
@[reassoc (attr := simp)]
lemma pathTransport_comp (σ : (TopCat.toSSet.obj X).obj n)
    (z w y : toTop.{v}.obj n.unop) :
    pathTransport σ z w ≫ pathTransport σ w y = pathTransport σ z y :=
  FundamentalGroupoid.map_default_comp _ _ _ _

/-- Transport inside a simplex may be moved along an equality of its target point. -/
@[reassoc]
lemma pathTransport_eqToHom (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop)
    {w w' : toTop.{v}.obj n.unop} (h : w = w') :
    pathTransport σ z w ≫
        eqToHom (congrArg (fun y ↦ (⟨TopCat.simplexMap σ y⟩ : FundamentalGroupoid X)) h) =
      pathTransport σ z w' := by
  subst h
  simp

/-- Transport inside a reindexed simplex is transport inside the original simplex, between the
images of the two points under the reindexing. -/
lemma pathTransport_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m)
    (z w : toTop.{v}.obj n.unop) :
    pathTransport ((TopCat.toSSet.obj X).map α σ) z w =
      pathTransport σ (toTop.map α.unop z) (toTop.map α.unop w) := by
  have h : ((FundamentalGroupoid.map (toTop.map α.unop).hom).map
        (default : (⟨z⟩ : FundamentalGroupoid (toTop.{v}.obj n.unop)) ⟶ ⟨w⟩) :
      (⟨toTop.map α.unop z⟩ : FundamentalGroupoid (toTop.{v}.obj m.unop)) ⟶
        ⟨toTop.map α.unop w⟩) = default := Subsingleton.elim _ _
  exact (FundamentalGroupoid.map_comp_map _ _ _).trans (congrArg _ h)

/-- Pushing a singular simplex forward along a continuous map carries transport inside it to
transport inside the image simplex. -/
lemma map_pathTransport (f : X ⟶ Y) (σ : (TopCat.toSSet.obj X).obj n)
    (z w : toTop.{v}.obj n.unop) :
    (FundamentalGroupoid.map f.hom).map (pathTransport σ z w) =
      pathTransport ((TopCat.toSSet.map f).app n σ) z w :=
  (FundamentalGroupoid.map_comp_map _ _ _).symm

section Chains

variable (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The transport from the initial vertex of a singular `m`-simplex `σ` to the initial vertex of
the singular `n`-simplex obtained from `σ` by reindexing along `α`. -/
def vertexTransport (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    initialVertex σ ⟶ initialVertex ((TopCat.toSSet.obj X).map α σ) :=
  pathTransport σ (toTopInitialVertex m.unop) (toTop.map α.unop (toTopInitialVertex n.unop))

/-- Reindexing along an identity does not move the initial vertex, so the transport it induces is
the canonical identification of the two coefficient modules. -/
lemma vertexTransport_id (σ : (TopCat.toSSet.obj X).obj n) :
    vertexTransport (𝟙 n) σ = eqToHom (by simp) := by
  have hz : toTopInitialVertex n.unop =
      toTop.{v}.map (𝟙 n).unop (toTopInitialVertex n.unop) := by
    rw [unop_id, CategoryTheory.Functor.map_id]
    rfl
  simp only [vertexTransport, ← pathTransport_eqToHom σ (toTopInitialVertex n.unop) hz,
    pathTransport_self, Category.id_comp]
  -- Both sides are now `eqToHom` between the same two objects; proof irrelevance finishes.
  rfl

/-- Reindexing along a composite induces the composite of the two vertex transports, up to the
canonical identification of the two resulting simplices. -/
lemma vertexTransport_comp (α : m ⟶ n) (β : n ⟶ p)
    (σ : (TopCat.toSSet.obj X).obj m) :
    vertexTransport α σ ≫ vertexTransport β ((TopCat.toSSet.obj X).map α σ) =
      vertexTransport (α ≫ β) σ ≫ eqToHom (by simp) := by
  have hz : toTop.{v}.map (α ≫ β).unop (toTopInitialVertex p.unop) =
      toTop.{v}.map α.unop (toTop.{v}.map β.unop (toTopInitialVertex p.unop)) := by
    rw [unop_comp, CategoryTheory.Functor.map_comp]
    rfl
  simp only [vertexTransport, pathTransport_map]
  exact (pathTransport_comp σ _ _ _).trans
    (pathTransport_eqToHom σ (toTopInitialVertex m.unop) hz).symm

/-- The simplicial object of singular chains of `X` twisted by the local coefficient system `L`.
In degree `n` it is the coproduct, over the singular `n`-simplices `σ` of `X`, of the fibre of
`L` at the initial vertex of `σ`; a reindexing acts on the summands by transport along the
initial vertices. -/
def twistedChains : SimplicialObject (ModuleCat.{max v w} R) where
  obj n := ∐ fun σ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex σ)
  map {m n} α := Sigma.desc fun σ ↦ L.map (vertexTransport α σ) ≫
    Sigma.ι (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex τ))
      ((TopCat.toSSet.obj X).map α σ)
  map_id n := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have hσ : σ = (TopCat.toSSet.obj X).map (𝟙 n) σ := by simp
    rw [Sigma.ι_desc, Category.comp_id, vertexTransport_id, eqToHom_map]
    exact Sigma.eqToHom_comp_ι
      (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex τ)) hσ
  map_comp {m n p} α β := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have hσ : (TopCat.toSSet.obj X).map (α ≫ β) σ =
        (TopCat.toSSet.obj X).map β ((TopCat.toSSet.obj X).map α σ) := by simp
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc,
      ← Category.assoc, ← L.map_comp, vertexTransport_comp, L.map_comp, Category.assoc,
      eqToHom_map]
    exact congrArg (L.map (vertexTransport (α ≫ β) σ) ≫ ·)
      (Sigma.eqToHom_comp_ι (fun τ : (TopCat.toSSet.obj X).obj p ↦ L.obj (initialVertex τ))
        hσ).symm

/-- The inclusion into twisted chains of the coefficient module attached to a singular simplex. -/
def ιTwistedChains (σ : (TopCat.toSSet.obj X).obj n) :
    L.obj (initialVertex σ) ⟶ (twistedChains L).obj n :=
  Sigma.ι (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex τ)) σ

/-- Two maps out of a module of twisted chains agree as soon as they agree on every summand. -/
@[ext]
lemma twistedChains_hom_ext {A : ModuleCat.{max v w} R} {f g : (twistedChains L).obj n ⟶ A}
    (h : ∀ σ, ιTwistedChains L σ ≫ f = ιTwistedChains L σ ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- A structure map of twisted chains sends the summand of a simplex `σ` into the summand of the
reindexed simplex, after transporting the coefficients along the initial vertices. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    ιTwistedChains L σ ≫ (twistedChains L).map α =
      L.map (vertexTransport α σ) ≫ ιTwistedChains L ((TopCat.toSSet.obj X).map α σ) :=
  Sigma.ι_desc _ _

/-- The chain complex of singular chains of `X` twisted by the local coefficient system `L`. -/
-- The body must stay exposed: without it the degree-`k` term of the complex is opaque, so the
-- boundary formula `ιTwistedChains_twistedChainComplex_d` cannot even be stated.
@[expose]
def twistedChainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (twistedChains L)

/-- The boundary of the twisted chain complex sends the summand of a singular `(k + 1)`-simplex
`σ` to the alternating sum of the summands of the faces of `σ`, the coefficients being transported
from the initial vertex of `σ` to the initial vertex of each face. -/
@[reassoc]
lemma ιTwistedChains_twistedChainComplex_d (k : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    ιTwistedChains L σ ≫ (twistedChainComplex L).d (k + 1) k =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (L.map (vertexTransport (SimplexCategory.δ i).op σ) ≫
          ιTwistedChains L ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ)) := by
  simp [twistedChainComplex, SimplicialObject.δ, Preadditive.comp_sum]

/-- Singular homology of `X` with coefficients in the local coefficient system `L`. -/
def twistedHomology (k : ℕ) : ModuleCat.{max v w} R := (twistedChainComplex L).homology k

end Chains

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X}

/-- The map on twisted chains in a single degree induced by a morphism of local coefficient
systems. -/
def twistedChainsCoefficientApp (η : L ⟶ K) (n : SimplexCategoryᵒᵖ) :
    (twistedChains L).obj n ⟶ (twistedChains K).obj n :=
  Sigma.desc fun σ ↦ η.app (initialVertex σ) ≫ ιTwistedChains K σ

/-- A morphism of local coefficient systems acts on the summand of a simplex `σ` through its
component at the initial vertex of `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsCoefficientApp (η : L ⟶ K) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains L σ ≫ twistedChainsCoefficientApp η n =
      η.app (initialVertex σ) ≫ ιTwistedChains K σ :=
  Sigma.ι_desc _ _

/-- The morphism of twisted chains induced by a morphism of local coefficient systems. -/
def twistedChainsCoefficientMap (η : L ⟶ K) : twistedChains L ⟶ twistedChains K where
  app := twistedChainsCoefficientApp η
  naturality _ _ _ := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp

/-- In each degree, the morphism of twisted chains induced by a morphism of local coefficient
systems is the corresponding map of coproducts. -/
@[simp]
lemma twistedChainsCoefficientMap_app (η : L ⟶ K) (n : SimplexCategoryᵒᵖ) :
    (twistedChainsCoefficientMap η).app n = twistedChainsCoefficientApp η n := by rfl

variable (R X) in
/-- Twisted singular chains as a functor of the local coefficient system. -/
def twistedChainsFunctor :
    LocalCoefficientSystem.{u, v, max v w} R X ⥤ SimplicialObject (ModuleCat.{max v w} R) where
  obj L := twistedChains L
  map η := twistedChainsCoefficientMap η
  map_id L := by
    refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
    simp
  map_comp η θ := by
    refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
    simp

/-- The identity morphism of a coefficient system induces the identity of twisted chains. -/
@[simp]
lemma twistedChainsCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainsCoefficientMap (𝟙 L) = 𝟙 (twistedChains L) :=
  (twistedChainsFunctor R X).map_id L

/-- A composite of morphisms of coefficient systems induces the composite of the two induced
morphisms of twisted chains. -/
@[simp, reassoc]
lemma twistedChainsCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    twistedChainsCoefficientMap (η ≫ θ) =
      twistedChainsCoefficientMap η ≫ twistedChainsCoefficientMap θ :=
  (twistedChainsFunctor R X).map_comp η θ

/-- The morphism of twisted chain complexes induced by a morphism of local coefficient systems. -/
def twistedChainComplexCoefficientMap (η : L ⟶ K) :
    twistedChainComplex L ⟶ twistedChainComplex K :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (twistedChainsCoefficientMap η)

/-- The identity morphism of a coefficient system induces the identity of twisted chain
complexes. -/
@[simp]
lemma twistedChainComplexCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainComplexCoefficientMap (𝟙 L) = 𝟙 (twistedChainComplex L) :=
  (congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
    (twistedChainsCoefficientMap_id L)).trans (CategoryTheory.Functor.map_id _ _)

/-- A composite of morphisms of coefficient systems induces the composite of the two induced
morphisms of twisted chain complexes. -/
@[simp, reassoc]
lemma twistedChainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    twistedChainComplexCoefficientMap (η ≫ θ) =
      twistedChainComplexCoefficientMap η ≫ twistedChainComplexCoefficientMap θ :=
  (congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
    (twistedChainsCoefficientMap_comp η θ)).trans (CategoryTheory.Functor.map_comp _ _ _)

/-- The map on twisted homology induced by a morphism of local coefficient systems. -/
def twistedHomologyCoefficientMap (η : L ⟶ K) (k : ℕ) :
    twistedHomology L k ⟶ twistedHomology K k :=
  (HomologicalComplex.homologyFunctor _ _ k).map (twistedChainComplexCoefficientMap η)

/-- The identity morphism of a coefficient system induces the identity of twisted homology. -/
@[simp]
lemma twistedHomologyCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    twistedHomologyCoefficientMap (𝟙 L) k = 𝟙 (twistedHomology L k) :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
    (twistedChainComplexCoefficientMap_id L)).trans (CategoryTheory.Functor.map_id _ _)

/-- A composite of morphisms of coefficient systems induces the composite of the two induced maps
of twisted homology. -/
@[simp, reassoc]
lemma twistedHomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (k : ℕ) :
    twistedHomologyCoefficientMap (η ≫ θ) k =
      twistedHomologyCoefficientMap η k ≫ twistedHomologyCoefficientMap θ k :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
    (twistedChainComplexCoefficientMap_comp η θ)).trans (CategoryTheory.Functor.map_comp _ _ _)

end Coefficients

section Constant

variable (X) in
/-- For a constant local coefficient system, twisted chains are the ordinary singular chains. -/
def twistedChainsConstantIso (M : ModuleCat.{max v w} R) :
    twistedChains ((constantFunctor X).obj M) ≅
      TopCat.toSSet.obj X ⋙ (sigmaConst.{v}).obj M :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro m n α
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    -- A constant system transports by the identity, so both structure maps are the reindexing
    -- `Sigma.desc fun σ ↦ Sigma.ι _ (α · σ)` of the summands, and `rfl` identifies them.
    simp only [Iso.refl_hom, twistedChains, Functor.comp_map, sigmaConst]
    rfl)

variable (X) in
/-- The comparison of twisted chains with ordinary singular chains is natural in the coefficient
module: a morphism of modules acts on the twisted side through the constant systems it induces,
and on the singular side summandwise. -/
lemma twistedChainsConstantIso_hom_naturality {M N : ModuleCat.{max v w} R} (φ : M ⟶ N) :
    twistedChainsCoefficientMap ((constantFunctor X).map φ) ≫
        (twistedChainsConstantIso X N).hom =
      (twistedChainsConstantIso X M).hom ≫
        Functor.whiskerLeft (TopCat.toSSet.obj X) ((sigmaConst.{v}).map φ) :=
  -- In each degree the comparison is the identity, so both sides act on the summand of a simplex
  -- through the component of `φ` at that summand.
  NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦
    Eq.trans (ιTwistedChains_twistedChainsCoefficientApp ((constantFunctor X).map φ) n σ)
      (Sigma.ι_map (f := fun _ : (TopCat.toSSet.obj X).obj n ↦ M)
        (g := fun _ : (TopCat.toSSet.obj X).obj n ↦ N) (fun _ ↦ φ) σ).symm)

variable (X) in
/-- For a constant local coefficient system, the twisted chain complex is the ordinary singular
chain complex with coefficients in the same module. -/
def twistedChainComplexConstantIso (M : ModuleCat.{max v w} R) :
    twistedChainComplex ((constantFunctor X).obj M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj M).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (twistedChainsConstantIso X M)

variable (X) in
/-- The comparison of the twisted chain complex with the ordinary singular chain complex is
natural in the coefficient module. -/
lemma twistedChainComplexConstantIso_hom_naturality {M N : ModuleCat.{max v w} R} (φ : M ⟶ N) :
    twistedChainComplexCoefficientMap ((constantFunctor X).map φ) ≫
        (twistedChainComplexConstantIso X N).hom =
      (twistedChainComplexConstantIso X M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).map φ).app X :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _).symm.trans
    ((congrArg (fun ψ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map ψ)
      (twistedChainsConstantIso_hom_naturality X φ)).trans
      ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _))

variable (X) in
/-- For a constant local coefficient system, twisted homology is ordinary singular homology. -/
def twistedHomologyConstantIso (M : ModuleCat.{max v w} R) (k : ℕ) :
    twistedHomology ((constantFunctor X).obj M) k ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max v w} R) k).obj M).obj X :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (twistedChainComplexConstantIso X M)

variable (X) in
/-- The comparison of twisted homology with ordinary singular homology is natural in the
coefficient module. -/
lemma twistedHomologyConstantIso_hom_naturality {M N : ModuleCat.{max v w} R} (φ : M ⟶ N)
    (k : ℕ) :
    twistedHomologyCoefficientMap ((constantFunctor X).map φ) k ≫
        (twistedHomologyConstantIso X N k).hom =
      (twistedHomologyConstantIso X M k).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max v w} R) k).map φ).app X :=
  ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _).symm.trans
    ((congrArg (fun ψ ↦ (HomologicalComplex.homologyFunctor _ _ k).map ψ)
      (twistedChainComplexConstantIso_hom_naturality X φ)).trans
      ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _))

end Constant

section Map

variable {Y : TopCat.{v}} (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- The map on twisted chains in a single degree induced by a continuous map: a singular simplex
of `X` is sent to its image in `Y`.  The coefficient modules agree because the initial vertex of
the image simplex is the image of the initial vertex. -/
def twistedChainsMapApp (n : SimplexCategoryᵒᵖ) :
    (twistedChains ((pullback f.hom).obj L)).obj n ⟶ (twistedChains L).obj n :=
  Sigma.desc fun σ ↦ ιTwistedChains L ((TopCat.toSSet.map f).app n σ)

/-- A continuous map sends the summand of a simplex `σ` of `X` identically onto the summand of its
image simplex in `Y`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsMapApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains ((pullback f.hom).obj L) σ ≫ twistedChainsMapApp f L n =
      ιTwistedChains L ((TopCat.toSSet.map f).app n σ) :=
  Sigma.ι_desc _ _

/-- The morphism of twisted chains induced by a continuous map, from the chains twisted by the
pullback system to the chains twisted by `L`. -/
def twistedChainsMap : twistedChains ((pullback f.hom).obj L) ⟶ twistedChains L where
  app := twistedChainsMapApp f L
  naturality {m n} α := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    rw [← Category.assoc, ιTwistedChains_map, Category.assoc,
      ιTwistedChains_twistedChainsMapApp, ← Category.assoc,
      ιTwistedChains_twistedChainsMapApp]
    refine Eq.trans ?_ (ιTwistedChains_map L α ((TopCat.toSSet.map f).app m σ)).symm
    exact congrArg (· ≫ ιTwistedChains L ((TopCat.toSSet.obj Y).map α
        ((TopCat.toSSet.map f).app m σ)))
      (congrArg L.map (map_pathTransport f σ (toTopInitialVertex m.unop)
        (toTop.map α.unop (toTopInitialVertex n.unop))))

/-- In each degree, the morphism of twisted chains induced by a continuous map is the
corresponding map of coproducts. -/
@[simp]
lemma twistedChainsMap_app (n : SimplexCategoryᵒᵖ) :
    (twistedChainsMap f L).app n = twistedChainsMapApp f L n := by rfl

/-- The morphism of twisted chain complexes induced by a continuous map. -/
def twistedChainComplexMap :
    twistedChainComplex ((pullback f.hom).obj L) ⟶ twistedChainComplex L :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (twistedChainsMap f L)

/-- The map on twisted homology induced by a continuous map, from the homology of `X` twisted by
the pullback system to the homology of `Y` twisted by `L`. -/
def twistedHomologyMap (k : ℕ) :
    twistedHomology ((pullback f.hom).obj L) k ⟶ twistedHomology L k :=
  (HomologicalComplex.homologyFunctor _ _ k).map (twistedChainComplexMap f L)

end Map

section MapComp

variable {Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The identity map induces on twisted chains the map coming from the identification of a
coefficient system with its pullback along the identity. -/
lemma twistedChainsMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainsMap (𝟙 X) L = twistedChainsCoefficientMap ((pullbackIdIso X).hom.app L) := by
  refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
  refine (ιTwistedChains_twistedChainsMapApp (𝟙 X) L n σ).trans ?_
  refine Eq.trans ?_
    (ιTwistedChains_twistedChainsCoefficientApp ((pullbackIdIso X).hom.app L) n σ).symm
  rw [pullbackIdIso_hom_app_app]
  exact (Category.id_comp (ιTwistedChains L σ)).symm

/-- A composite of continuous maps induces on twisted chains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated pullback. -/
lemma twistedChainsMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) :
    twistedChainsMap (f ≫ g) L =
      twistedChainsCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) ≫
        twistedChainsMap f ((pullback g.hom).obj L) ≫ twistedChainsMap g L := by
  refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
  refine (ιTwistedChains_twistedChainsMapApp (f ≫ g) L n σ).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsCoefficientApp_assoc
    ((pullbackCompIso f.hom g.hom).hom.app L) n σ _).symm
  rw [pullbackCompIso_hom_app_app]
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact ((ιTwistedChains_twistedChainsMapApp_assoc f ((pullback g.hom).obj L) n σ
    (twistedChainsMapApp g L n)).trans
    (ιTwistedChains_twistedChainsMapApp g L n ((TopCat.toSSet.map f).app n σ))).symm

/-- The chain-complex form of `twistedChainsMap_id`. -/
lemma twistedChainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainComplexMap (𝟙 X) L =
      twistedChainComplexCoefficientMap ((pullbackIdIso X).hom.app L) :=
  congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
    (twistedChainsMap_id L)

/-- The chain-complex form of `twistedChainsMap_comp`. -/
lemma twistedChainComplexMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) :
    twistedChainComplexMap (f ≫ g) L =
      twistedChainComplexCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) ≫
        twistedChainComplexMap f ((pullback g.hom).obj L) ≫ twistedChainComplexMap g L :=
  (congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
      (twistedChainsMap_comp f g L)).trans
    (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl)

/-- The homology form of `twistedChainsMap_id`. -/
lemma twistedHomologyMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    twistedHomologyMap (𝟙 X) L k =
      twistedHomologyCoefficientMap ((pullbackIdIso X).hom.app L) k :=
  congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
    (twistedChainComplexMap_id L)

/-- The homology form of `twistedChainsMap_comp`. -/
lemma twistedHomologyMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) (k : ℕ) :
    twistedHomologyMap (f ≫ g) L k =
      twistedHomologyCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) k ≫
        twistedHomologyMap f ((pullback g.hom).obj L) k ≫ twistedHomologyMap g L k :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
      (twistedChainComplexMap_comp f g L)).trans
    (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl)

end MapComp

end LocalCoefficientSystem

end TauCeti
